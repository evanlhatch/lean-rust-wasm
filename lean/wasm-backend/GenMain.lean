import Lean
import Lean.Compiler.LCNF
import CodegenCore
import SchemaLang
import SchemaLang.Meta.Reflect
import WasmBackend
import WasmBackend.Check
import Oracle

/-!
# WasmBackend.GenMain — the LCNF → WAT artifact writer

The `leanir` pattern: import the manifest's modules' oleans, re-run the
LCNF pipeline (the impure-phase LCNF — Perceus RC included — is NOT
persisted in oleans), read the final `Decl`s from `impureExt`, emit WAT.

Pipeline: this exe writes `target/demo.wat` + `demo-world.wit` (+ the
observability manifest); the oracle manifest is `lake exe oracle`
(OracleMain.lean — the row universe lives in the Oracle library);
the justfile drives `wasm-tools parse -g` → binary, the component
wrap, and the differential smoke.

The COMPILE-SET + the world = the PROJECT MANIFEST (`project.json`
beside this exe) + the attribute registries — no hand-list:

- the manifest = the MODULES (`spec-modules` = the `@[schema]` surface;
  `impl-modules` = the `@[guest_std]`/`@[guest]` impls) — the exe loads
  their union (extensions replayed);
- the guest MARKS = the decls (the `CodegenCore.GuestGate` registry —
  a def joins when `@[guest]`/`@[guest_std]` checked it at elaboration;
  `targetDeclsOf` folds them, minus the std INTRINSICS whose bodies are
  never compiled — the backend maps those NAMES to runtime primitives);
- the SCHEMA registry's func items whose `body` is a compile root = the
  exports (`worldExportsOf`).

The internals (`area`/`applyAll` — unregistered but compiled helpers)
ride the same mark. A new project's manifest (template/project.json) is
its only authoring surface here — the demo's hand-listed `targetDecls`
is gone.
-/

open Lean

/-! ## The project manifest (project.json)

JSON (Lean's `Json.parse` — no dependency; TOML would need a parser).
Two keys, both arrays of module names:

```json
{
  "spec-modules": ["DemoFn"],
  "impl-modules": ["DemoFn", "GuestlangStd"]
}
```

`spec-modules` — the `@[schema]` authoring modules (the schema
registry's rows). `impl-modules` — the `@[guest_std]`/`@[guest]` impl
modules (the compiled surface). The exe loads the union (deduped); the
marks inside decide what compiles and what exports.
-/

structure ProjectManifest where
  specModules : Array Name
  implModules : Array Name

/-- Read one module-list key out of the manifest JSON. -/
def manifestModules (j : Json) (key : String) : Except String (Array Name) := do
  let v ← j.getObjVal? key
  (← v.getArr?).mapM fun e => do pure (← e.getStr?).toName

/-- Load + parse `project.json` (the exe's package dir is the cwd). -/
def loadProjectManifest (path : System.FilePath) : IO ProjectManifest := do
  let txt ← IO.FS.readFile path
  match Lean.Json.parse txt with
  | .error e => throw (IO.userError s!"{path}: {e}")
  | .ok j =>
    match (manifestModules j "spec-modules").bind fun spec =>
        (manifestModules j "impl-modules").map fun impl =>
          ({ specModules := spec, implModules := impl } : ProjectManifest) with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"{path}: {e}")

/-- The manifest's fold: the compile roots = the guest-marked decls
    (the `CodegenCore.GuestGate` registry, replayed from the loaded
    oleans), minus the std INTRINSICS (`strlen`/`strcat` — the backend
    maps the NAMES to the runtime primitives; the bodies are never
    compiled). The manifest's modules bound the loaded world; the marks
    pick the decls; this fold is the rest. Dedup: a def marked both
    `@[guest]` and `@[guest_std]` joins once. -/
def targetDeclsOf (env : Environment) : Array Name :=
  (CodegenCore.GuestGate.guestMarkedDecls env).eraseDups.toArray.filter
    fun n => (WasmBackend.stdOp? n).isNone

/-- Run the LCNF pipeline + emit the module, in CoreM. Returns the
    runtime-spliced WAT body WITHOUT the GENERATED header — the header
    is the driver's prepend (`watEmitter` + `runEmitters`, W7.12); this
    function's result joins the `WasmGenSpec` as spec data. -/
def emitModuleWasm (targetDecls : Array Name) : CoreM String := do
  Lean.Compiler.LCNF.main targetDecls {}
  -- Closure constants + lambdas: `_closed`/`_lam` decls (holding the
  -- paps) are generated IN-PROCESS by the re-run — never in the imported
  -- env. Include every impure decl UNDER a target's namespace.
  let mut names := targetDecls
  let all ← Lean.Compiler.LCNF.getLocalImpureDecls
  let internal := all.filter fun n =>
    let s := n.toString
    s.contains "." && targetDecls.any fun t => s.startsWith (t.toString ++ ".")
  names := names ++ internal
  let mut decls2 : List (Lean.Compiler.LCNF.Decl .impure) := []
  for n in names do
    if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
      decls2 := d :: decls2
  decls2 := decls2.reverse
  -- Debug dump: the final LCNF per decl (the compiler line's x-ray).
  for d in decls2 do
    let fmt ← Lean.Compiler.LCNF.ppDecl' d .impure
    IO.eprintln s!"--- {d.name}\n{fmt}"
  let wireNameOf (n : Name) : String :=
    CodegenCore.Emit.kebab n.getString!
  let exportTargets := targetDecls.toList.map fun n => (wireNameOf n, n)
  -- which targets return a STRING (the canonical ABI's post-return
  -- (ptr,len) convention): from the ORIGINAL def type — the LCNF type is
  -- erased to `obj` for every object result, Shape and String alike
  let env ← getEnv
  let stringResult? (n : Name) : Bool :=
    match env.find? n with
    | some (.defnInfo di) =>
        let rec peel (e : Expr) : Expr :=
          match e with | .forallE _ _ b _ => peel b | _ => e
        match peel di.type with
        | .const c _ => c == `String
        | _ => false
    | _ => false
  let res : Except String (String × WasmBackend.S) :=
    StateT.run (WasmBackend.emitModule decls2 exportTargets stringResult?) {}
  match res with
  | .ok (wat, st) =>
    -- splice the hand-written runtime (pooled allocator + Perceus RC)
    -- into the module body: single module, no imports. The splice
    -- marker sits AFTER the async task-intrinsic imports (the core-wasm
    -- section order: imports first) and before the memory.
    let rt ← IO.FS.readFile "runtime.wat"
    -- the migration's progress metric: the `Instr.raw` count (the
    -- honest ledger lives in WasmBackend.lean's header)
    IO.println s!"wasm-backend: {st.rawCount} raw instrs (the Wat.Instr.raw ledger)"
    pure (wat.replace "  ;;RUNTIME-SPLICE\n" (rt ++ "\n"))
  | .error e => throwError e

/-! ## The component world (the SSOT for demo-world.wit)

The world file the component embed consumes is EMITTED, not
hand-maintained — the hand-written copy was the last contract surface
with no writer (the one-writer doctrine). The table is CURATED (not
folded from `targetDecls`): object-parameterized functions (`area` over
`Shape`, `applyAll` over closures) have no flat component
representation yet — they join the world when the canonical ABI
flattens them (strings/objects), and the KEPT list is the honest
surface of what the component actually exports.
-/

/-- One folded world export: (wire name, rendered params, WIT return
    type, async?). Reducible — the emitters + the guard destructure it
    directly. -/
abbrev WorldExport := String × List String × String × Bool

/-- The COMPILED world's exports, FOLDED from the schema registry (the
    6.5.1 `body` seam): a fn is exported iff it is BOTH compiled
    (`targetDecls`) AND registered (`@[schema_fn]` — the registration
    is the export marker; `area`/`applyAll`/… are compiled but
    unregistered = internal). The SIGNATURE comes from the item, never
    hand-copied: the params = the registered names + `tyWit` types; the
    async-ness = the `Async.Future` marker (the registered ret =
    `.future`); `delivery = stream` surfaces the impl's list element as
    the stream's item type (`stream<u64>`, `stream<user>`). -/
def worldExportsOf (env : Environment) (targetDecls : Array Name) : List WorldExport :=
  let items := SchemaLang.Meta.registeredItems env
  targetDecls.toList.filterMap fun n =>
    match items.find? fun (_, it) =>
      match it with
      | .func sig => sig.body == n
      | _ => false with
    | some (_, .func sig) =>
        let nm := CodegenCore.Emit.kebab n.getString!
        let params := sig.params.map fun (p, t) =>
          CodegenCore.Emit.kebab p ++ ": " ++ SchemaLang.Emit.Wit.tyWit t
        let (isAsync, ret) := match sig.ret with
          | .future a =>
              let r := match a with
                | .list e => if sig.sem.delivery == (.stream : SchemaLang.Delivery)
                  then s!"stream<{SchemaLang.Emit.Wit.tyWit e}>"
                  else SchemaLang.Emit.Wit.tyWit a
                | a => SchemaLang.Emit.Wit.tyWit a
              (true, r)
          | ret => (false, SchemaLang.Emit.Wit.tyWit ret)
        some (nm, params, ret, isAsync)
    | _ => none

/-- The oracle's fn names — DERIVED from `Oracle.rowUniverse` (the
    library is the single source; kebab, as the JSON spells them). The
    drift surface 3.4 pins: an oracle row for a fn the world does not
    export is a differential row with no component export to run it
    against. -/
def oracleFns : List String := (rowUniverse.map (·.1)).eraseDups

-- 3.4: every oracle fn IS a world export (the component contract covers
-- everything the differential manifest exercises).


/-- The world document (doubleSlash comments; the driver prepends the
    header). The FUNC LINES = the folded exports (the registry is the
    authority); the demo-types interface stays the hand mirror of the
    schema's User/OrderError (the drift surface = the differential
    duel, which decodes through the HOST's generated types). -/
def worldWitOf (worldExports : List WorldExport) : String :=
  "package guestlang:demo;\n\n"
    ++ "interface demo-types {\n"
    ++ "  record user {\n    id: u64,\n    name: string,\n    email: string,\n    tags: list<string>,\n  }\n"
    ++ "  variant order-error {\n    empty-cart,\n    invalid-item(u64),\n    insufficient-funds(f64),\n  }\n"
    ++ "}\n\nworld demo {\n"
    ++ "  use demo-types.{user, order-error};\n"
    ++ String.intercalate "\n"
      (worldExports.map fun (name, params, ret, isAsync) =>
        let kw := if isAsync then "async " else ""
        s!"    export {name}: {kw}func({String.intercalate ", " params}) -> {ret};")
    ++ "\n}\n"

/-! ## The COMPILED world — the gateway's compilable subset

`get-user` is the first SCHEMA function the backend compiles: option +
record + strings + list<string> through the canonical ABI. The world
`use`s the gateway's types (one type authority — the record is the
SSOT's user, not a structural copy). `watch-orders` (async) + `db`
(resource) join when the async ABI + resources land — the compiled
world is the HONEST surface of what's compiled, and the compiled
component embeds IT.
-/

/-! ## The Emitter spine (W7.12)

The three artifacts this exe writes (`target/demo.wat`,
`demo-world.wit`, `../../src/observability_generated.rs`) are
`CodegenCore.Emit.Emitter` instances over `WasmGenSpec` — declared
outputs, header discipline, one write path (`runEmitters`). The spec
is NOT `List Item`: the wat emitter's input is the LCNF re-run's
RESULT — the LCNF emit is monadic (CoreM + the runtime.wat read), so
it stays in the DRIVER and the pure `Emitter.run` receives the
already-emitted, already-spliced body as spec data.

The instances live HERE (the exe), not in a WasmBackend lib module:
the lib is deliberately CodegenCore-only (lakefile note 2.1 — the
SchemaLang mathlib closure stays out of the backend's modules), the
lib's `globs` enumerate modules explicitly, and the spec is assembled
from exe-side data (the registry fold + the compiled module).

FOLLOW-UP (next wave, NOT this order): the forge jobs manifest
(`SchemaLang.Emit.Registry.forgeJobs`) does NOT cover these outputs —
they are not schema-lang emitters, so `jobsCoverEmitters` cannot see
them. Registering wasm-backend's emitters with forge is a cross-package
registry change; until it lands, these artifacts ride the
`wasm-compile` recipe's own byte-tie (the committed observability
surface + the wasm-tools validate) instead of `forge gen --check`.
-/

/-- The wasm-gen spec: exactly what the three emitters need, assembled
    by the driver. `watBody` = the compiled module's WAT,
    runtime-spliced, headerless; `worldExports` = the registry fold
    (`worldExportsOf`). -/
structure WasmGenSpec where
  watBody : String
  worldExports : List WorldExport

/-- The observability manifest body (headerless — the driver prepends):
    the spans = spec data, emitted from the SAME fold as the world (one
    writer). The host's call path spans exactly what this table declares
    — an unregistered fn = no span (the coverage = the registry by
    construction). -/
def observabilityRsOf (worldExports : List WorldExport) : String :=
  let spanRows := worldExports.map fun (name, params, ret, isAsync) =>
    let fields := params.map fun p =>
      let sp := p.splitOn ": "
      "(\"" ++ sp.head! ++ "\", \"" ++ sp.getLast! ++ "\")"
    let del := if isAsync && ret.startsWith "stream<" then "stream" else "once"
    "    SpanSpec { name: \"" ++ name ++ "\", delivery: \"" ++ del
      ++ "\", fields: &[" ++ String.intercalate ", " fields ++ "] }"
  String.join
    ( [ "/// One observed export: the span name + its fields + the delivery\n"
      , "/// contract (`once` = one result value; `stream` = incremental).\n"
      , "pub struct SpanSpec {\n"
      , "    pub name: &'static str,\n"
      , "    pub delivery: &'static str,\n"
      , "    pub fields: &'static [(&'static str, &'static str)],\n"
      , "}\n\n"
      , "/// The observed surface = the world's exports, in fold order.\n"
      , "pub const SPANS: &[SpanSpec] = &[\n"
      ]
      ++ spanRows.map (· ++ ",\n")
      ++ ["];\n"] )

/-- The compiled module (`target/demo.wat`). `watBody` carries the
    LCNF re-run's result; the emitter only wraps it with the path (the
    header is the driver's prepend). -/
def watEmitter : CodegenCore.Emit.Emitter WasmGenSpec where
  name := "wat"
  style := .wat
  specSource := "DemoFn.lean"
  outputs := ["target/demo.wat"]
  run spec := [{ path := "target/demo.wat", contents := spec.watBody }]

/-- The component world (`demo-world.wit` — `./`-prefixed so the shared
    write path's parent-dir computation names a real directory). -/
def worldWitEmitter : CodegenCore.Emit.Emitter WasmGenSpec where
  name := "world-wit"
  style := .doubleSlash
  specSource := "the schema registry (the @[schema_fn] items — the fold)"
  outputs := ["./demo-world.wit"]
  run spec := [{ path := "./demo-world.wit", contents := worldWitOf spec.worldExports }]

/-- THE OBSERVABILITY MANIFEST (the fast-observe seam): the spans =
    spec data, emitted from the SAME fold as the world (one writer). -/
def observabilityEmitter : CodegenCore.Emit.Emitter WasmGenSpec where
  name := "observability"
  style := .doubleSlash
  specSource := "the world fold (worldExportsOf)"
  outputs := ["../../src/observability_generated.rs"]
  run spec :=
    [{ path := "../../src/observability_generated.rs"
       contents := observabilityRsOf spec.worldExports }]

/-- The registry. Order = write order (wat, wit, observability — the
    pre-W7.12 driver's order). -/
def wasmEmitters : List (CodegenCore.Emit.Emitter WasmGenSpec) :=
  [watEmitter, worldWitEmitter, observabilityEmitter]


unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  -- the guest IMPLS (lean/std, schema-typed functions) are the point
  -- of this exe; they need the schema types (Demo — via GuestlangStd's
  -- import) and the std ops.
  let manifest ← loadProjectManifest "project.json"
  -- the manifest = the modules: load the deduped union, extensions
  -- replayed (the schema + guest-mark registries come back populated).
  let mods := (manifest.specModules ++ manifest.implModules).toList.eraseDups
  let env ← Lean.importModules (mods.toArray.map ({ module := · })) (opts := {}) (loadExts := true)
  let ctx : Core.Context := { fileName := "<wasm-gen>", fileMap := default }
  let state : Core.State := { env := env }
  -- the manifest's fold: the marks = the decls (no hand-list)
  let targetDecls := targetDeclsOf env
  -- the LCNF re-run + the runtime splice stay in the DRIVER (monadic);
  -- the wat emitter receives the RESULT as spec data.
  let (watBody, _) ← (emitModuleWasm targetDecls).toIO ctx state
  -- the folded world: the registry is the export authority. The guard
  -- (3.4): the oracle's rows must cover fns the world actually exports
  -- — checked BEFORE any artifact write (the emitters run after).
  let worldExports := worldExportsOf env targetDecls
  for f in oracleFns do
    unless worldExports.any fun (w, _, _, _) => w == f do
      -- the closed-world suggestion (CodegenCore.didYouMean — the
      -- every-error-path engine, reachable core-only from HERE): the
      -- misspell candidate lists the world's ACTUAL exports.
      let cands := CodegenCore.didYouMean f (worldExports.map fun (w, _, _, _) => w)
      let hint := if cands.isEmpty then ""
        else s!" — did you mean: {String.intercalate ", " cands}?"
      throw (IO.userError s!"oracle fn `{f}` is not a world export{hint}")
  -- the emit fold: assemble the spec, write via the Emit discipline
  -- (`runEmitters`: header prepend + createParentDirs + write — the
  -- shared driver tail). The generation metadata (the clock + git) is
  -- the driver's IO; the emitters stay pure.
  let spec : WasmGenSpec := { watBody, worldExports }
  let witBody := worldWitOf worldExports
  CodegenCore.Emit.runEmitters "wasm-backend" (wasmEmitters.map (·, spec))
    fun e _ =>
      -- the wat header's metadata is content-free (0 items, hash 0 —
      -- the LCNF result is not registry data); the wit + observability
      -- headers carry the fold's size + the world document's content
      -- hash (the drift check strips the 2-line header, so the
      -- wall-clock is byte-tie-safe).
      if e.name == "wat" then CodegenCore.Emit.genMeta 0 0
      else CodegenCore.Emit.genMeta worldExports.length witBody.hash
  IO.println "wrote target/demo.wat + demo-world.wit (the oracle: lake exe oracle)"
