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
    oleans), minus the std INTRINSICS (`strlen`/`strcat`/`streq` —
    `GuestlangStd.Intrinsic.ofName?` maps their names, plus the string
    `==` spellings (`String.decEq` — the W9.6 gap-3 lowering), to the
    closed universe's ctors; the backend emits the ctors'
    `runtimeName` primitives, the bodies are never compiled). The
    manifest's modules bound the loaded world; the marks pick the
    decls; this fold is the rest. Dedup: a def marked both `@[guest]`
    and `@[guest_std]` joins once. -/
def targetDeclsOf (env : Environment) : Array Name :=
  (CodegenCore.GuestGate.guestMarkedDecls env).eraseDups.toArray.filter
    fun n => (GuestlangStd.Intrinsic.ofName? n).isNone

/-- The compile-set ROOT name of a pipeline-created worker/shim decl:
    `<root>._redArg` (the erasure worker), `<root>_boxed` (the pap
    shim), `<root>_closed` (the closure constant) — the ROOT is what
    joins the compile set; the pipeline creates the workers for it. -/
private def rootNameOf (n : Lean.Name) : Lean.Name :=
  match n with
  | .str p s =>
      if s == "_redArg" || s == "_boxed" || s == "_closed" then p else n
  | n => n

/-- The LCNF x-ray (the W9.6 guest-compat audit's tool): render one
    `LetValue` as its construct name — the diagnostic names the EXACT
    construct the backend cannot lower, per decl, with the code path
    to it. -/
private def ctorNameOf : Lean.Compiler.LCNF.LetValue .impure → String := fun v =>
  match v with
  | .lit (.nat _) => "nat-lit" | .lit _ => "lit"
  | .erased => "erased"
  | .proj _ _ _ _ => "proj"
  | .const n _ _ _ => s!"const {n}"
  | .fvar _ _ => "fvar"
  | .ctor i _ => s!"ctor {i.name}"
  | .oproj _ _ _ => "oproj"
  | .sproj _ _ _ _ => "sproj"
  | .box t _ _ => s!"box {t}"
  | .unbox _ _ => "unbox"
  | .uproj .. => "uproj"
  | .fap .. => "fap"
  | .pap .. => "pap"
  | .reset .. => "reset"
  | .reuse .. => "reuse"
  | .isShared .. => "isShared"

/-- The W9.6 audit diagnostic: report every target decl whose final
    LCNF carries a construct the backend does not lower — Perceus
    reset/reuse/isShared (no guest lowering) or Nat literals (GMP —
    banned in the guest). The walk is IO-recursive over the jp/cases
    structure; the printed path (`@/case/let/let/jpK`) locates the
    construct. Kept on every wasm-gen run: a marked decl the backend
    cannot compile fails LOUD here, before any artifact is written. -/
private partial def reportUnsupportedLCNF (decls2Names : NameSet) (d : Lean.Compiler.LCNF.Decl .impure) : IO Unit := do
  let debugTrace := false
  let rec walk (path : String) (c : Lean.Compiler.LCNF.Code .impure) : IO Bool := do
    match c with
    | .let decl k =>
        let here : Bool :=
          match decl.value with
          | .reset .. => true
          | .reuse .. => true
          | .isShared .. => true
          -- the bounded-Nat surface (WasmBackend.lean's header note) is
          -- LOWERED now: Nat.lit (cap-pinned) + the Nat countdown
          -- binops + the checker-scoped spec-BEq are supported — not
          -- diagnostics. An UNSUPPORTED Nat construct (ctor-case
          -- dispatch, succ/mul/…) arrives as an unknown-callee fap or
          -- an emitter throw below.
          | .fap fn args =>
              -- unknown callees: not a binop, not an intrinsic, not a
              -- spec-BEq product (inline-lowered, checker-scoped), not
              -- an inline-Nat fap (extern primitives — inline-lowered,
              -- no callee decl), and not a decl the backend emits (an
              -- undefined wasm call)
              (WasmBackend.binop? fn).isNone
                && (GuestlangStd.Intrinsic.ofName? fn).isNone
                && !WasmBackend.isSpecBEqName fn
                && !WasmBackend.inlineNatFap? fn args.size
                && !decls2Names.contains fn
          | _ => false
        let _ : Unit ←
          if here then
            IO.eprintln s!"wasm-gen: UNSUPPORTED-LCNF {d.name} @{path}: {ctorNameOf decl.value}"
          else
            pure ()
        let rest ← walk (path ++ "/let") k
        pure (here || rest)
    | .jp fd k =>
        let a ← walk (path ++ "/jp") fd.value
        let b ← walk (path ++ "/jpK") k
        pure (a || b)
    | .cases cs =>
        let mut any := false
        if debugTrace then
          IO.eprintln s!"WALK {d.name} @{path}: cases {cs.typeName} ({cs.alts.size} alts)"
        else pure ()
        for a in cs.alts do
          let bad ← match a with
            | .ctorAlt _ c => walk (path ++ "/case") c
            | .default c => walk (path ++ "/caseD") c
            | .alt _ _ _ _ => pure false
          any := any || bad
        pure any
    | _ => pure false
  if let .code c := d.value then
    let _ ← walk "" c
    pure ()

/-- The undefined-callee CLOSURE COMPLETION (the audit's gap-4 fix,
    general form): scan the local decls' final LCNF for fap callees the
    emitter cannot resolve (not a binop, not an intrinsic, not a
    spec-BEq product, not itself local) and — when the callee EXISTS in
    the env as compilable code — add it to the compile set and re-run
    the pipeline. This is how the checker's core-List helpers join
    (`List.get?Internal._redArg` etc. are created ONLY when their ROOT
    is a target; the checker's LCNF calls them, so the roots must
    compile). Fixpoint-bounded (8 rounds); a callee that stays
    undefined is the diagnostic's job (below), never a silent call. -/
private partial def fapCalleesOf : Lean.Compiler.LCNF.Code .impure → NameSet
  | .let decl k =>
      let here : NameSet :=
        match decl.value with
        | .fap fn args =>
            -- the inline-Nat surface: no callee exists — never chased
            if WasmBackend.inlineNatFap? fn args.size then {} else ({} : NameSet).insert fn
        -- the PAP callee too (the W9.6 decode lane): a first-class fn
        -- value (`decList? decWStep?`) lowers to `pap <root>_boxed` —
        -- the emitter's trampoline CALLS that name, so the `_boxed`
        -- shim must exist: chase the name, and the root-name map below
        -- strips the shim suffix to the ROOT whose compilation creates
        -- the shim as a local decl
        | .pap fn args =>
            if WasmBackend.inlineNatFap? fn args.size then {} else ({} : NameSet).insert fn
        | _ => {}
      (fapCalleesOf k).union here
  | .jp fd k => (fapCalleesOf fd.value).union (fapCalleesOf k)
  | .fun fd k _ => (fapCalleesOf fd.value).union (fapCalleesOf k)
  | .cases c =>
      c.alts.foldl (fun acc a => acc.union
        (match a with
          | .ctorAlt _ code => fapCalleesOf code
          | .default code => fapCalleesOf code
          | .alt _ _ _ h => absurd h (by simp))) {}
  | .sset _ _ _ _ _ k => fapCalleesOf k
  | .inc _ _ _ _ k => fapCalleesOf k
  | .dec _ _ _ _ _ k => fapCalleesOf k
  | .del _ k => fapCalleesOf k
  | .unreach _ | .return _ | .jmp ..
  | .oset .. | .uset .. | .setTag .. => {}

/-- The undefined callees across the local decls (the emitter's
    resolution surface: binop / intrinsic / spec-BEq / local = defined). -/
private def collectUndefinedCallees (decls : List (Lean.Compiler.LCNF.Decl .impure)) : NameSet :=
  let defined : NameSet :=
    decls.foldl (fun s d => s.insert d.name) {}
  decls.foldl (fun acc d =>
    match d.value with
    | .code c =>
        let callees := fapCalleesOf c
        callees.toList.foldl (fun acc' n =>
          if (WasmBackend.binop? n).isNone
              && (GuestlangStd.Intrinsic.ofName? n).isNone
              && !WasmBackend.isSpecBEqName n
              && !defined.contains n then
            acc'.insert n
          else acc') acc
    | .extern .. => acc) {}

/-! ## The LCNF re-run + emission -/

/-- Run the LCNF pipeline + emit the module, in CoreM. Returns the
    runtime-spliced WAT body WITHOUT the GENERATED header — the header
    is the driver's prepend (`watEmitter` + `runEmitters`, W7.12); this
    function's result joins the `WasmGenSpec` as spec data. -/
def emitModuleWasm (targetDecls : Array Name) : CoreM String := do
  -- THE CLOSURE COMPLETION FIXPOINT (see collectUndefinedCallees): each
  -- round runs the pipeline, scans the local decls for undefined fap
  -- callees, and re-runs with them added (their roots exist in the env;
  -- the workers the pipeline creates for them are the point). Bounded
  -- at 8 rounds — the checker's closure needs 1; the bound is the
  -- loud-failure guard (a 9th round would mean a cycle the emitter
  -- cannot close, and the diagnostic names the stragglers).
  let env ← getEnv
  let mut targets := targetDecls
  for _round in [0:8] do
    Lean.Compiler.LCNF.main targets {}
    let all ← Lean.Compiler.LCNF.getLocalImpureDecls
    let mut localDecls : List (Lean.Compiler.LCNF.Decl .impure) := []
    for n in all do
      if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
        localDecls := d :: localDecls
    let missing := collectUndefinedCallees localDecls
    if missing.isEmpty then
      break
    let addable := missing.toArray.filter fun n =>
      -- the ERASURE WORKER naming: `<root>._redArg` — the worker is
      -- created only when its ROOT compiles, so the ROOT is what joins
      -- the compile set (the worker itself is never an env constant)
      -- — and the SHIM naming `<root>_boxed` (the pap callee: same
      -- rule; also `_closed`). The root itself must be a def in the env.
      match env.find? (rootNameOf n) with
      | some (.defnInfo _) => true
      | _ => false
    if addable.isEmpty then
      -- none of the missing callees is compilable — the diagnostic
      -- below names them (undefined wasm calls), the emitter throws
      break
    let roots := addable.map rootNameOf
    targets := (targets ++ roots).toList.eraseDups.toArray
  Lean.Compiler.LCNF.main targets {}
  -- The re-run's LOCAL impure decls (never in the imported env):
  -- `_closed`/`_lam` closure constants, `_boxed` shims, `_redArg`
  -- workers, and the SPECIALIZATION PRODUCTS the spec pass names by
  -- their SOURCE type (`Option.instBEq.beq._at_.<target>.spec_0` — the
  -- W9.6 audit's gap 4). Include EVERY one: the local decl set IS the
  -- targets' closure (reachability, computed by the re-run itself) —
  -- the old under-a-target-namespace filter was the bug (a
  -- specialization product's name carries its source TYPE, so no
  -- namespace test can catch it; it emitted as an undefined wasm
  -- call). The intrinsics' names are still lowered as primitives, not
  -- calls — `ofName?` mapping inside the fap emitter.
  let mut names := targets
  let all ← Lean.Compiler.LCNF.getLocalImpureDecls
  names := (names ++ all).toList.eraseDups.toArray
  let mut decls2 : List (Lean.Compiler.LCNF.Decl .impure) := []
  for n in names do
    if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
      decls2 := d :: decls2
  decls2 := decls2.reverse
  -- Debug dump: the final LCNF per decl (the compiler line's x-ray).
  let decls2Names : Lean.NameSet := decls2.foldl (fun s d => s.insert d.name) {}
  for d in decls2 do
    reportUnsupportedLCNF decls2Names d
  for d in decls2 do
    let fmt ← Lean.Compiler.LCNF.ppDecl' d .impure
    IO.eprintln s!"--- {d.name}\n{fmt}"
  let wireNameOf (n : Name) : String :=
    CodegenCore.Emit.kebab n.getString!
  -- the EXPORT surface = the GUEST MARKS only (the original
  -- targetDecls) — the closure fixpoint's added roots (the core-List
  -- workers, the extern Nat primitives) are COMPILED but never
  -- exported: an extern target's adapter calls a no-result stub (the
  -- Nat.decEq_abi validate failure), and the extra exports would
  -- grow the component surface past the wit's item count (17 — the
  -- W9.6 witness export's).
  -- W9.6: the WIT-registered fn OWNS its wire name. A marked
  -- non-registered decl kebabing to the same name loses its core
  -- export — the case: the W9.5 seam `WitnessCheck.verifyWitness`
  -- (its params are not Ty-representable — the audit: unexportable at
  -- ANY fixing) vs the demo's export wrapper `DemoFn.verifyWitness`
  -- (the registered @[schema_fn]) — both kebab to `verify-witness`,
  -- and the duplicate core export failed the module encode.
  let exportTargets :=
    let registeredBodies : List Name :=
      (SchemaLang.Meta.registeredItems env).filterMap fun (_, it) =>
        match it with | .func sig => some sig.body | _ => none
    let isRegistered (n : Name) : Bool := registeredBodies.contains n
    let claimedWires : List String :=
      (targetDecls.toList.filter isRegistered).map wireNameOf
    let keepTarget (n : Name) : Bool :=
      if claimedWires.contains (wireNameOf n) then isRegistered n else true
    (targetDecls.toList.filter keepTarget).map fun n => (wireNameOf n, n)
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
  -- The LCNF re-run happens IN THIS PROCESS (the impure phase is not
  -- persisted in oleans) — disable Perceus reuse instrumentation: the
  -- emitter cannot lower reset/reuse/isShared joins (the
  -- UNSUPPORTED-LCNF diagnostic). Runtime optimization only; the
  -- emitted wasm is semantics-identical (RC correctness never relies
  -- on reuse).
  let env ← Lean.importModules (mods.toArray.map ({ module := · }))
    (opts := (default : Lean.Options).setBool `compiler.reuse false) (loadExts := true)
  let ctx : Core.Context := { fileName := "<wasm-gen>", fileMap := default
                              options := (default : Lean.Options).setBool `compiler.reuse false }
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
