/-
# ComponentTests.ImportFixture — the import discipline's fixture

The component lane's FIFTH fixture (the externs' OTHER half): the
guest whose export CALLS an IMPORTED function — the IR's `extern`
ctor carrying the WASM-IMPORT resolution (`ExternResolution.import`
— the two-level core wire name `mod.name`), the world's import row
(`Wit.World.imports` — the D2/WIT disciplines' consumption), the
component's import section + the canon LOWERS + the shim core
instance, and the host's provision (`func_wrap` — the linker
discipline). The full vertical:

    the guest IR (the declared trust boundary's import face)
      → the core module (the wasm import, imports-first index space)
      → the component (the world's import row, byte-tied)
      → the host's provision (the linker's func_wrap; the value
        crosses the boundary)
      → the goldens agree (the three-way: the Lean executor's
        provision row ≡ the component's execution ≡ the wasmtime run)

Why hand-built (the fault fixture's precedent, one lane over): the
guest's import call is the boundary's OWN shape — the toy-frontend
face (the hand-written IR is the conformance evidence that the IR
alone is the whole contract; the LCNF frontend's extern reading is
the frontend's lane, not this fixture's).

The teeth (each a PURE fact here, asserted in `ComponentTests.Main`):
- the undeclared/skewed import refuses at GENERATION
  (`checkImports`: importDrift / importSigDrift / importUnclaimed —
  an unprovisioned import never becomes an artifact);
- the unprovisioned model run answers `.unmodeled` (the honest
  ledger — never a wrong answer);
- the provision's type tooth: a provision whose answer's type drifts
  from the declared row never enters the caller's stack (the
  executor's runtime check);
- the instantiate-time refusals are the HOST's
  (`crates/mandate-host`'s import lane: the missing provision and
  the signature skew refuse there, typed).

The five questions (notes/v3/01-core.md): the fixture is data — the
answers live at the consumers (`Guest.lowerFuncs`'s import
face, `Guest.Component.checkImports`/`encodeComponent`, the host's
import lane).
-/

import Guest
import Guest.Component
import Wit
import Wit.World
import WasmCore.Instr
import WasmCore.Module
import WasmCore.Exec
import WasmCore.Validate

open WasmCore

namespace ComponentTests.ImportFixture

/-- THE IMPORT WORLD: `import host-add: func(a: u64, b: u64) ->
    u64;` + `export add64: func(a: u64, b: u64) -> u64;` — the
    guest's export calls the imported function (the boundary's
    two-sided contract, one world). -/
def importWorld : Wit.World :=
  { name := "guest"
  , imports :=
      [.func { name := "host-add"
             , params := [{ name := "a", ty := .atom .u64 }
                        , { name := "b", ty := .atom .u64 }]
             , result := some (.atom .u64) }]
  , exports :=
      [.func { name := "add64"
             , params := [{ name := "a", ty := .atom .u64 }
                        , { name := "b", ty := .atom .u64 }]
             , result := some (.atom .u64) }] }

/-- The import-resolved extern: the DECLARED trust boundary's import
    face (the contract rides the ctor as data; the resolution names
    the core wire row `host.host-add` — the mod groups the instantiate
    args, the name is the WIT row + the core import's ONE name). -/
def hostAddDecl : Guest.IR.Decl :=
  { name := "host-add"
  , params := [("a", .u64), ("b", .u64)]
  , resultTy := .u64
  , value := .extern
      { params := [.u64, .u64], result := .u64, effect := .pure
      , note := "the host's provision answers the addition (the trust \
                 note: pure, total, a + b)"
      , resolution := .import "host" "host-add" } }

/-- The guest's export: `add64` calls the imported function through
    the call lane (the sib index is the import's — the wasm
    imports-first function-index space) and returns its value. -/
def add64Decl : Guest.IR.Decl :=
  { name := "add64"
  , params := [("a", .u64), ("b", .u64)]
  , resultTy := .u64
  , value := .let_ { var := "r", ty := .u64
                    , value := .call "host-add"
                        #[.var "a", .var "b"] }
             (.ret "r") }

/-- THE IMPORT FIXTURE's core module (the lowering's import face):
    ONE core import (`host.host-add`, the declared type), ONE local
    function (`add64` at the shifted absolute index 1 — the imports
    take 0..k-1). -/
def importModule : Except Guest.LowerError WasmCore.Module :=
  Guest.lowerFuncs [hostAddDecl, add64Decl]

/-- THE MODEL'S PROVISION (the executor's extern-call semantics): the
    import's provision row is the closed op the model's host answers
    with (`i64add` — the ONE op table's row, `semOp i64add [b, a] =
    a + b`), set at the model run — mirroring the host's
    `func_wrap(|a, b| a + b)`, the wire carries none of it. -/
def modelModule : Except Guest.LowerError WasmCore.Module :=
  importModule.map (fun m =>
    { m with imports := m.imports.map (fun i => { i with impl := some .i64add }) })

/-- THE MODEL RUN: the guest's `add64` (absolute function index 1 —
    the import takes 0) on the args (head = TOP = the last param). -/
def modelRun (fuel : Nat) (a b : UInt64) : WasmCore.Outcome :=
  match modelModule with
  | .ok m => runFunc m 1 [.i64 b, .i64 a] fuel
  | .error _ => .unmodeled

/-- THE UNPROVISIONED MODEL RUN (the honesty face): no provision row
    — the executor's ledger answers `.unmodeled`, never a wrong
    answer. -/
def bareModule : Except Guest.LowerError WasmCore.Module := importModule

def bareRun (fuel : Nat) (a b : UInt64) : WasmCore.Outcome :=
  match bareModule with
  | .ok m => runFunc m 1 [.i64 b, .i64 a] fuel
  | .error _ => .unmodeled

/-- THE IMPORT SPEC: the lowered core module + the world it must
    match (the emission's skew checks — BOTH faces — run at
    generation). -/
def importSpec : Except Guest.LowerError Guest.Component.Spec :=
  importModule.map (fun m => { core := m, world := importWorld })

/-- The CONCRETE spec (the writer's value face): the fixture's
    lowering succeeding is itself a pinned test (`Main` asserts the
    `isOk`); the drift face is the loud panic — test code only, the
    driver's IO face never runs free. -/
def importSpecOk : Guest.Component.Spec :=
  match importSpec with
  | .ok s => s
  | .error e => panic! s!"ImportFixture: the fixture lowering drifted: {e.render}"

/-! ## The teeth (the negative controls, pure data) -/

/-- THE UNDECLARED IMPORT: the world names an import the module does
    not carry (`host-nope`, beside the claimed `host-add` — the
    module's own import stays claimed) — `importDrift` at
    generation. -/
def driftSpec : Except Guest.LowerError Guest.Component.Spec :=
  importModule.map (fun m =>
    { core := m
    , world := { name := "guest"
               , imports :=
                   [.func { name := "host-nope"
                          , params := [{ name := "a", ty := .atom .u64 }]
                          , result := some (.atom .u64) }]
                   ++ importWorld.imports
               , exports := importWorld.exports } })

/-- THE SKEWED IMPORT: the world's import row declares `bool` (the
    `i32` flattening) where the module's import — and the declared
    contract — rides `u64` (the `i64` flattening) — `importSigDrift`
    at generation (the skew discipline's import face; a SCALAR skew —
    the string/adapter-face skew is the `importAdapters` row's, the
    fixture's named boundary). -/
def skewSpec : Except Guest.LowerError Guest.Component.Spec :=
  importModule.map (fun m =>
    { core := m
    , world := { name := "guest"
               , imports :=
                   [.func { name := "host-add"
                          , params := [{ name := "a", ty := .atom .bool }
                                    , { name := "b", ty := .atom .u64 }]
                          , result := some (.atom .u64) }]
               , exports := importWorld.exports } })

/-- THE UNPROVISIONED COMPONENT: the module imports `host.host-add`
    but the world declares NO imports — `importUnclaimed` at
    generation (an artifact with an unprovisionable import is never
    written). -/
def unclaimedSpec : Except Guest.LowerError Guest.Component.Spec :=
  importModule.map (fun m =>
    { core := m
    , world := { name := "guest"
               , imports := []
               , exports := importWorld.exports } })

end ComponentTests.ImportFixture
