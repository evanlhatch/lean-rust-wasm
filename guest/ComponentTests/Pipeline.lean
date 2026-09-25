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
deterministic, which is what the byte-tie certifies). `scalarSpec` and
`stringSpec` are the two lanes' spec constructions (the scalar lane's
core module is the pipeline's product; the string lane's module is the
hand-built adapter-face fixture — pure data, no LCNF).

The five questions (notes/v3/01-core.md): none of its own — the shared
pipeline over Guest.Component's regen (the answers live there).
Gate row: none — the gen-check row CONSUMES this; the writer exe is
its write face.
-/
import Guest
import Guest.Component
import ComponentTests.Fixture
import ComponentTests.StringFixture

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
      match Guest.lowerFunc d with
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
