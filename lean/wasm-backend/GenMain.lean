import Lean
import Lean.Compiler.LCNF
import CodegenCore
import SchemaLang
import SchemaLang.Meta.Reflect
import WasmBackend
import WasmBackend.Check

/-!
# WasmBackend.GenMain — the LCNF → WAT artifact writer

The `leanir` pattern: import the manifest's modules' oleans, re-run the
LCNF pipeline (the impure-phase LCNF — Perceus RC included — is NOT
persisted in oleans), read the final `Decl`s from `impureExt`, emit WAT.

Pipeline: this exe writes `target/demo.wat` (+ the differential oracle
program); the justfile drives `wasm-tools parse -g` → binary, the
component wrap, and the differential smoke.

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

/-- Run the LCNF pipeline + emit the module, in CoreM. -/
def emitModuleWasm (targetDecls : Array Name) (gm : CodegenCore.Emit.GenMeta) : CoreM String := do
  Lean.Compiler.LCNF.main targetDecls {}
  let mut decls : List (Lean.Compiler.LCNF.Decl .impure) := []
  for n in targetDecls do
    if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
      decls := d :: decls
  decls := decls.reverse
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
    -- WAT line comments are `;;` — CommentStyle.wat (2.10).
    let hdr := CodegenCore.Emit.header .wat "wasm-backend" "DemoFn.lean" gm
    -- the migration's progress metric: the `Instr.raw` count (the
    -- honest ledger lives in WasmBackend.lean's header)
    IO.println s!"wasm-backend: {st.rawCount} raw instrs (the Wat.Instr.raw ledger)"
    pure (hdr ++ (wat.replace "  ;;RUNTIME-SPLICE\n" (rt ++ "\n")))
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

/-- The COMPILED world's exports, FOLDED from the schema registry (the
    6.5.1 `body` seam): a fn is exported iff it is BOTH compiled
    (`targetDecls`) AND registered (`@[schema_fn]` — the registration
    is the export marker; `area`/`applyAll`/… are compiled but
    unregistered = internal). The SIGNATURE comes from the item, never
    hand-copied: the params = the registered names + `tyWit` types; the
    async-ness = the `Async.Future` marker (the registered ret =
    `.future`); `delivery = stream` surfaces the impl's list element as
    the stream's item type (`stream<u64>`, `stream<user>`). -/
def worldExportsOf (env : Environment) (targetDecls : Array Name) : List (String × List String × String × Bool) :=
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

/-- The oracle's fn names — mirrors `oracleSrc`'s `rows`/`resultOf`
    (kebab, as the JSON spells them). The drift surface 3.4 pins: an
    oracle row for a fn the world does not export is a differential row
    with no component export to run it against. -/
def oracleFns : List String :=
  ["double", "is-big", "adder", "double-area", "run-paps", "total", "pick", "str-len-demo", "greet", "get-user", "watch-counts", "watch-users", "user-valid", "user-complete", "order-error-valid"]

-- 3.4: every oracle fn IS a world export (the component contract covers
-- everything the differential manifest exercises).


/-- The world document (doubleSlash comments; the driver prepends the
    header). The FUNC LINES = the folded exports (the registry is the
    authority); the demo-types interface stays the hand mirror of the
    schema's User/OrderError (the drift surface = the differential
    duel, which decodes through the HOST's generated types). -/
def worldWitOf (worldExports : List (String × List String × String × Bool)) : String :=
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

/-- The DIFFERENTIAL ORACLE program: calls the real Lean functions over
generated inputs and prints the manifest as JSON. The Lean semantics is
the authority; the Rust diff test replays this against the emitted wasm.
(String VALUES go through `Lean.Json.str`/`compress` — proper escaping;
the row skeleton stays hand-spelled: `Json.mkObj` sorts keys and
`compress` strips spaces, so neither may touch the manifest's bytes.) -/
def oracleSrc : String := "
import Lean
import DemoFn
import GuestlangStd

def u64s : List UInt64 :=
  ((List.range 20).map (fun i => (i * 7 + 3) % 100)).map (fun n => n.toUInt64)

-- THE FUZZ SUPPLEMENT: a deterministic LCG drives RANDOM scalar rows —
-- the authority stays LEAN (the expected = resultOf's evals on the
-- random args); the engines must agree on inputs the fixed grid never
-- visits (the overflow wraps: UInt64 arithmetic is wrapping — the
-- random args cross the wrap boundary the grid avoids).
def lcg : UInt64 → UInt64 := fun s => s * 6364136223846793005 + 1442695040888963407

def fuzzRows : Nat → UInt64 → List (String × List String)
  | 0, _ => []
  | n+1, seed =>
      let s1 := lcg seed
      let s2 := lcg s1
      let s3 := lcg s2
      let s4 := lcg s3
      let row := match s1 % 7 with
        | 0 => (\"double\", [toString (s2 % 1000)])
        | 1 => (\"is-big\", [toString (s2 % 1000)])
        | 2 => (\"adder\", [toString (s2 % 1000), toString (s3 % 1000)])
        | 3 => (\"double-area\", [toString (s2 % 100)])
        | 4 => (\"run-paps\", [toString (s2 % 1000)])
        | 5 => (\"total\", [toString (s2 % 100), toString (s3 % 100), toString (s4 % 100)])
        | _ => (\"pick\", [if s2 % 2 == 0 then \"1\" else \"0\", toString (s3 % 100), toString (s4 % 100)])
      row :: fuzzRows n s4

def rows : List (String × List String) :=
  (u64s.map fun a => (\"double\", [toString a]))
  ++ (u64s.map fun a => (\"is-big\", [toString a]))
  ++ (u64s.map fun a => (\"adder\", [toString a, toString (a + 3)]))
  ++ (u64s.map fun a => (\"double-area\", [toString a]))
  ++ (u64s.map fun a => (\"run-paps\", [toString a]))
  ++ ((List.range 20).map fun i =>
    (\"total\", [toString (i * 3), toString (i + 1), toString (i * 2)]))
  ++ (u64s.map fun a => (\"pick\", [if a % 2 == 0 then \"1\" else \"0\", toString a, toString (a + 1)]))
  ++ (u64s.map fun a => (\"str-len-demo\", [toString a]))
  ++ (u64s.map fun a => (\"greet\", [toString a]))
  ++ (u64s.map fun a => (\"get-user\", [toString a]))
  ++ (u64s.map fun a => (\"watch-counts\", [toString a]))
  ++ (u64s.map fun a => (\"watch-users\", [toString a]))
  -- the VALIDATOR's duel: the row args = the record's FIELD VALUES FLAT
  -- (id, name, email, tags comma-joined) — the wasm_diff arg-builder
  -- constructs the Val::Record from them. THE INVALID ROW (id = 0) is
  -- the point: the validator must REFUSE it (the negative control —
  -- Lean says false, the wasm must agree).
  ++ [(\"user-valid\", [\"0\", \"zero\", \"0@g.dev\", \"a\"])]
  ++ (u64s.map fun a => (\"user-valid\", [toString a, \"first\", \"1@g.dev\", \"a\"]))
  -- the VARIANT validator's duel: the args = [discr, payload] — the
  -- canonical-ABI flat form (the discr = the WIT case order:
  -- empty-cart=0, invalid-item=1, insufficient-funds=2; the payload
  -- rides the joined i64 slot — u64 raw, f64 bits). The empty-cart row
  -- is the documented NEGATIVE (the validator refuses the
  -- no-information report); invalid-item(0) is the sentinel negative;
  -- the f64 arm's payload is unread (GuestImpl.orderErrorValid) — the
  -- row pins the CONSTANT arm, not a Float compare.
  ++ [(\"order-error-valid\", [\"0\", \"0\"])]
  ++ [(\"order-error-valid\", [\"1\", \"0\"])]
  ++ [(\"order-error-valid\", [\"1\", \"5\"])]
  ++ [(\"order-error-valid\", [\"2\", \"1.5\"])]
  -- the RICHER record validator's duel: the same flat-record arg form
  -- as user-valid — each gate (id, strlen, tags-count) gets its
  -- negative; the map rows are the positives. (The empty-LIST gate has
  -- no row: the flat-string convention cannot express the empty list —
  -- \"\" splits to [\"\"], one element, BOTH sides agree.)
  ++ [(\"user-complete\", [\"0\", \"zero\", \"0@g.dev\", \"a\"])]
  ++ [(\"user-complete\", [\"1\", \"ab\", \"1@g.dev\", \"a\"])]
  ++ (u64s.map fun a => (\"user-complete\", [toString a, \"first\", \"1@g.dev\", \"a,b\"]))

def resultOf (fn : String) (args : List String) : String :=
  match fn, args with
  | \"double\", [a] => toString (double a.toNat!.toUInt64)
  | \"is-big\", [a] => if isBig a.toNat!.toUInt64 then \"1\" else \"0\"
  | \"adder\", [a, b] => toString (adder a.toNat!.toUInt64 b.toNat!.toUInt64)
  | \"double-area\", [a] => toString (doubleArea a.toNat!.toUInt64)
  | \"run-paps\", [a] => toString (runPaps a.toNat!.toUInt64)
  | \"total\", [a, b, c] => toString (total a.toNat!.toUInt64 b.toNat!.toUInt64 c.toNat!.toUInt64)
  | \"pick\", [b, a, x] => toString (pick (b == \"1\") a.toNat!.toUInt64 x.toNat!.toUInt64)
  | \"str-len-demo\", [a] => toString (GuestImpl.strLenDemo a.toNat!.toUInt64)
  | \"greet\", [a] => GuestImpl.greet a.toNat!.toUInt64
  | \"get-user\", [a] => match GuestImpl.getUser a.toNat!.toUInt64 with
    | none => \"none\"
    | some u =>
      let tagS := String.intercalate \",\" (u.tags.map (fun t => t))
      s!\"some(\\{ id={u.id}, name={u.name}, email={u.email}, tags=({tagS}) })\"
  -- the stream's expected = the COLLECTED list (the host reads the
  -- stream to completion; the ser form = the list's)
  | \"watch-counts\", [_a] => \"(42,43)\"
  -- the validator: the args = the FLAT field values (see the rows);
  -- the bool result = the ser convention (1/0 — ser_val's Val::Bool form)
  | \"user-valid\", [id, name, email, tags] =>
    if (GuestImpl.userValid { id := id.toNat!.toUInt64, name := name, email := email, tags := tags.splitOn \",\" }) then \"1\" else \"0\"
  -- the variant validator: the discr → the Lean ctor; the payload only
  -- READ for invalid-item (the f64 arm ignores it — see the impl)
  | \"order-error-valid\", [d, p] =>
    let e : OrderError :=
      match d with
      | \"0\" => .emptyCart
      | \"1\" => .invalidItem p.toNat!.toUInt64
      | _ => .insufficientFunds 1.5
    if GuestImpl.orderErrorValid e then \"1\" else \"0\"
  -- the richer record validator: the same flat-record args as user-valid
  | \"user-complete\", [id, name, email, tags] =>
    if (GuestImpl.userComplete { id := id.toNat!.toUInt64, name := name, email := email, tags := tags.splitOn \",\" }) then \"1\" else \"0\"
  | \"watch-users\", [a] =>
    -- the ser_val's forms: the list = the comma-NO-space joins; the
    -- record = \"{ k=v, ... }\" with the comma-space joins
    let parts := (GuestImpl.watchUsers 0).map fun u =>
      let tagS := String.intercalate \",\" (u.tags.map (fun t => t))
      s!\"\\{ id={u.id}, name={u.name}, email={u.email}, tags=({tagS}) }\"
    let ser := String.intercalate \",\" parts
    s!\"({ser})\"
  | _, _ => \"?\"

def jsonRow (fn : String) (args : List String) (expected : String) : String :=
  -- values via Lean.Json (compress = core's escaping); the skeleton
  -- keeps the manifest's byte format (`mkObj` sorts keys — forbidden
  -- here).
  \"{\" ++ \"\\\"fn\\\": \" ++ (Lean.Json.str fn).compress ++ \", \\\"args\\\": [\" ++
    String.intercalate \",\" (args.map fun a => (Lean.Json.str a).compress) ++
    \"], \\\"expected\\\": \" ++ (Lean.Json.str expected).compress ++ \"}\"

def main : IO Unit := do
  let mut out := \"[\"
  let mut first := true
  for (fn, args) in (rows ++ fuzzRows 200 0x5EED) do
    let expected := resultOf fn args
    if !first then out := out ++ \",\"
    first := false
    out := out ++ jsonRow fn args expected
  out := out ++ \"]\"
  IO.println out
"

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  -- 2.1 was 'DemoFn only' (mathlib cost) — OBSOLETE: the guest IMPLS
  -- (lean/std, schema-typed functions) are now the point of this exe;
  -- they need the schema types (Demo — via GuestlangStd's import) and
  -- the std ops. The mathlib-in-closure cost is the product now.
  let manifest ← loadProjectManifest "project.json"
  -- the manifest = the modules: load the deduped union, extensions
  -- replayed (the schema + guest-mark registries come back populated).
  let mods := (manifest.specModules ++ manifest.implModules).toList.eraseDups
  let env ← Lean.importModules (mods.toArray.map ({ module := · })) (opts := {}) (loadExts := true)
  let ctx : Core.Context := { fileName := "<wasm-gen>", fileMap := default }
  let state : Core.State := { env := env }
  -- the generation metadata FIRST (the wat's header rides the splice)
  let preMeta ← CodegenCore.Emit.genMeta 0 0
  -- the manifest's fold: the marks = the decls (no hand-list)
  let targetDecls := targetDeclsOf env
  let (wat, _) ← (emitModuleWasm targetDecls preMeta).toIO ctx state
  IO.FS.createDirAll "target"
  IO.FS.writeFile "target/demo.wat" wat
  IO.FS.writeFile "target/oracle.lean" oracleSrc
  -- the folded world: the registry is the export authority. The guard
  -- (3.4) moved here from the top level: the oracle's rows must cover
  -- fns the world actually exports.
  let worldExports := worldExportsOf env targetDecls
  for f in oracleFns do
    unless worldExports.any fun (w, _, _, _) => w == f do
      throw (IO.userError s!"oracle fn `{f}` is not a world export")
  -- the generation metadata (the clock + git; the drift check strips
  -- the header, so the wall-clock is byte-tie-safe)
  let gm ← CodegenCore.Emit.genMeta worldExports.length
    (worldWitOf worldExports).hash
  let witHdr := CodegenCore.Emit.header .doubleSlash "wasm-backend"
    "the schema registry (the @[schema_fn] items — the fold)" gm
  IO.FS.writeFile "demo-world.wit" (witHdr ++ worldWitOf worldExports)
  -- THE OBSERVABILITY MANIFEST (the fast-observe seam): the spans =
  -- spec data, emitted from the SAME fold as the world (one writer).
  -- The host's call path spans exactly what this table declares — an
  -- unregistered fn = no span (the coverage = the registry by
  -- construction).
  let spanRows := worldExports.map fun (name, params, ret, isAsync) =>
    let fields := params.map fun p =>
      let sp := p.splitOn ": "
      "(\"" ++ sp.head! ++ "\", \"" ++ sp.getLast! ++ "\")"
    let del := if isAsync && ret.startsWith "stream<" then "stream" else "once"
    "    SpanSpec { name: \"" ++ name ++ "\", delivery: \"" ++ del
      ++ "\", fields: &[" ++ String.intercalate ", " fields ++ "] }"
  let obs := String.join
    ( [ CodegenCore.Emit.header .doubleSlash "wasm-backend"
          "the world fold (worldExportsOf)" gm
      , "/// One observed export: the span name + its fields + the delivery\n"
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
  IO.FS.writeFile "../../src/observability_generated.rs" obs
  IO.println "wrote target/demo.wat + target/oracle.lean + demo-world.wit"
