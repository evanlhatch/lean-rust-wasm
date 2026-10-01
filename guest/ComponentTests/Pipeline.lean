/-
ComponentTests.Pipeline — the component lane's driver pipeline, ONE
copy (the `Guest.Component.regen` discipline: the writer and the gate
share the ONE pipeline — a gate that re-encodes it would tie two
encodings, not the artifact to the spec).

Consumers (the only two):
- `componentgen` (ComponentGenMain.lean) — the WRITER side (`just
  componentgen`): the LCNF re-run + the emit spine's write face.
- `Gates.GenCheck` — the CHECK side (`gates gen-check`): the same
  pipeline's products tied against the committed artifacts.

`loadCoreModule` is the fixture import + the impure-phase LCNF re-run +
the lowering (the ComponentGenMain/ComponentTests.Main pattern: the
impure phase is not persisted in oleans, so every consumer re-runs it —
deterministic, which is what the byte-tie certifies). `scalarSpec`,
`stringSpec` and `edgeSpec` are the three lanes' spec constructions
(the scalar lane's core module is the LCNF re-run's product; the
string lane's module is the hand-built adapter-face fixture — pure
data, no LCNF; the edge lane's module is the edgepython frontend's
pure product — `ComponentTests.EdgeFixture`).

The five questions (notes/v3/01-core.md): none of its own — the shared
pipeline over Guest.Component's regen (the answers live there).
Gate row: none — the gen-check row CONSUMES this; the writer exe is
its write face.
-/
import Guest
import Guest.Component
import ComponentTests.Fixture
import ComponentTests.StringFixture
import ComponentTests.EdgeFixture
import ComponentTests.FaultFixture
import ComponentTests.WitFixture
import ComponentTests.ImportFixture

open Guest

/-- The fixture import + the LCNF re-run + the lowering (the driver's
    one product; the ComponentGenMain pattern). -/
unsafe def ComponentTests.Pipeline.loadCoreModule :
    IO (Except String WasmCore.Module) := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.searchPathRef.set (".lake/build/lib/lean" :: (← Lean.searchPathRef.get))
  try
    let env ← Lean.importModules #[{ module := `ComponentTests.Fixture }]
      (opts := Guest.lcnfOptions) (loadExts := true)
    match ← Guest.readDecl? env `add64 with
    | .error e => return .error s!"readDecl: {e}"
    | .ok d =>
      match Guest.compile [d] with
      | .error e => return .error s!"lower: {e.render}"
      | .ok m => return .ok m
  catch e =>
    return .error s!"importModules failed: {toString e}"

/-- The SCALAR lane's spec: the lowered core module (the pipeline's
    product) over the fixture world (`ComponentTests.Fixture.
    componentWorld` — the SSOT the emission is checked against). -/
def ComponentTests.Pipeline.scalarSpec (core : WasmCore.Module) :
    Guest.Component.Spec :=
  { core := core, world := componentWorld }

/-- The STRING lane's spec: the hand-built adapter-face module (pure
    data, no LCNF re-run — `ComponentTests.StringFixture`). -/
def ComponentTests.Pipeline.stringSpec : Guest.Component.Spec :=
  { core := ComponentTests.StringFixture.stringModule
  , world := ComponentTests.StringFixture.lengthWorld }

/-- The STRING lane's emission rows — the writer's write path
    (`stringComponentEmitter`; `Guest.Component.regen` is the SCALAR
    emitter's regen: its rows for a string spec name the scalar paths,
    which is why the writer checks through `regen` but WRITES through
    this emitter — the gate reads the same faces). -/
def ComponentTests.Pipeline.stringRows (s : Guest.Component.Spec) :
    List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile :=
  (Guest.Component.stringComponentEmitter.run s,
   (Guest.Component.stringComponentEmitter.runBinary).getD (fun _ => []) s)

/-- The EDGE lane's spec: the edgepython frontend's parity set
    (`ComponentTests.EdgeFixture.edgeSpec` — the pure frontend's
    product, no LCNF re-run; Pipeline re-exports it as the ONE spec
    face the writer/gate/tests name). -/
def ComponentTests.Pipeline.edgeSpec : Guest.Component.Spec :=
  ComponentTests.EdgeFixture.edgeSpec

/-- The EDGE lane's emission rows — the writer's write path
    (`edgeComponentEmitter`; the stringRows discipline: the writer
    checks through `regen` but WRITES through this emitter). -/
def ComponentTests.Pipeline.edgeRows (s : Guest.Component.Spec) :
    List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile :=
  (Guest.Component.edgeComponentEmitter.run s,
   (Guest.Component.edgeComponentEmitter.runBinary).getD (fun _ => []) s)

/-- The FAULT lane's spec: the hand-built heap-return module + the
    typed-refusal world (`ComponentTests.FaultFixture.faultSpec` —
    pure data, no LCNF re-run; the D6 port's result-channel face). -/
def ComponentTests.Pipeline.faultSpec : Guest.Component.Spec :=
  ComponentTests.FaultFixture.faultSpec

/-- The FAULT lane's emission rows — the writer's write path
    (`faultComponentEmitter`; the edgeRows discipline). -/
def ComponentTests.Pipeline.faultRows (s : Guest.Component.Spec) :
    List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile :=
  (Guest.Component.faultComponentEmitter.run s,
   (Guest.Component.faultComponentEmitter.runBinary).getD (fun _ => []) s)

/-- The WITNESS lane's spec: the hand-built checker module + the
    typed-refusal world (`ComponentTests.WitFixture.witGateSpec` —
    pure data, no LCNF re-run; the host-gating lane's
    `witness-gate : func(...) -> result<_, u64>` face). -/
def ComponentTests.Pipeline.witSpec : Guest.Component.Spec :=
  ComponentTests.WitFixture.witGateSpec

/-- The WITNESS lane's emission rows — the writer's write path
    (`witComponentEmitter`; the faultRows discipline). -/
def ComponentTests.Pipeline.witRows (s : Guest.Component.Spec) :
    List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile :=
  (Guest.Component.witComponentEmitter.run s,
   (Guest.Component.witComponentEmitter.runBinary).getD (fun _ => []) s)

/-- The IMPORT lane's spec: the hand-built import fixture (the guest's
    `add64` calling the imported `host-add` — `ComponentTests.
    ImportFixture.importSpecOk`, pure data, no LCNF re-run; the
    externs' OTHER half: the world's import row + the core module's
    wasm import + the host's provision). -/
def ComponentTests.Pipeline.importSpec : Guest.Component.Spec :=
  ComponentTests.ImportFixture.importSpecOk

/-- The IMPORT lane's emission rows — the writer's write path
    (`importComponentEmitter`; the witRows discipline). -/
def ComponentTests.Pipeline.importRows (s : Guest.Component.Spec) :
    List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile :=
  (Guest.Component.importComponentEmitter.run s,
   (Guest.Component.importComponentEmitter.runBinary).getD (fun _ => []) s)
