/-
ComponentGenMain — the `componentgen` exe: the component lane's
byte-tie writer side, MANIFEST-DRIVEN (the legacy WasmGenMain's P1
discipline ported fresh — `Guest.GenMain`).

    lake exe componentgen

THE MANIFEST DISCIPLINE: the driver's authoring surface is
`Guest.Gen.mandate` — the project manifest as a DECLARED value (the
world's name + the impl modules). The compile set + the world DERIVE
from the registered project surface, never a hand list:

- the env extensions REPLAY (`Guest.Gen.loadEnv` — importModules with
  `loadExts := true`): the `LintKit.GuestGate` guest-mark registry
  comes back populated from the oleans;
- the compile set = the marks bounded by the manifest's modules
  (`Guest.Gen.compileSetOf`) — a new `@[guest]` def joins by the
  registration alone;
- the world = the honest ABI surface of the compile set
  (`Guest.Gen.surfaceOf`): every marked def whose type maps into the
  component lane's `Wit.Scalar` universe exports under its own name
  (the core export's name — the world and the module agree by
  construction); a marked def outside the map is compiled but
  world-EXCLUDED and REPORTED (the honest surface).

PIPELINE: the derived surface → ONE LCNF re-run over the compile set
(`Guest.Gen.readTargets?` — the impure phase is not persisted in
oleans) → `Guest.compile` (the derived core module) →
`Guest.Component.regen` (the world/component SKEW CHECK runs at
generation — a drift refuses loudly, nothing written) → the emit
spine:

- the TEXT lane: the world text (`Render.worldFile`'s render face →
  `gen/component-slice.wit`, its 2-line GENERATED header inline);
- the BINARY lane: the component bytes (`componentEmitter`'s row →
  `gen/component-slice.wasm`) PLUS the `.hdr` sidecar carrying the
  same 2-line GENERATED header in text.

The STRING lane (the adapter-face fixture —
`ComponentTests.StringFixture.stringModule`, pure data, no LCNF, no
guest marks: the string runtime is `@[guest]`-banned) rides the same
writer unchanged: it is the adapter face's fixture, not a registered
surface — its world stays hand-built until the std lane registers.
The EDGE lane (the edgepython frontend's parity set —
`ComponentTests.EdgeFixture.edgeSpec`, the pure frontend's product,
no LCNF re-run) rides the same writer the same way: the second
frontend's component face, wasmtime-executed through the host's edge
lane. The FAULT lane (`ComponentTests.FaultFixture` — the D6 port's
typed-refusal channel) and the WITNESS lane
(`ComponentTests.WitFixture` — the host-gating lane's checker
component, `witness-gate`) ride it the same way: hand-built
fixture specs, the writer checks each through its `regen` and writes
through the lane's own emitter.

THE OBSERVABILITY DISCIPLINE, honest minimal: the derived surface
(compile set, world exports, compiled-but-unexported) is PRINTED at
generation — not emitted as a file. The legacy's
`observability_generated.rs` had a Rust host consumer; this tree has
none, and a generated file with no consumer breaks the leftover rule
(the file emitter lands with its consumer — Gates.Audit's noted row).

The LCNF re-run needs the unsafe IO (the importModules + the compiler
pipeline — the GuestTests.Main pattern; the interpreter is on in the
lakefile row). The PIPELINE is ComponentTests.Pipeline's ONE copy for
the gate's check side (the regen discipline: a gate that re-encoded
the writer would tie two encodings, not the artifact to the spec).

Gate row: none — this exe is the component lane's WRITER side (the
CHECK side is `gates gen-check`'s component loop + the committed
byte-tie pins in ComponentTests).
-/
import Guest
import Guest.GenMain
import ComponentTests.Pipeline
import ComponentTests.StringFixture

open Guest

/-- The name list's display face (the report's join). -/
def nameList (ns : List Lean.Name) : String :=
  String.intercalate ", " (ns.map (·.toString))

/-- One lane's regen-or-refuse: the skew check rides `regen` — a drift
    refuses loudly, nothing written (the writer's per-lane face). -/
unsafe def regenLane (tag : String) (s : Guest.Component.Spec) :
    IO (Option String) :=
  match Guest.Component.regen s with
  | .error e => do
      IO.eprintln s!"componentgen: {tag} REGEN FAILED — {e}"
      return none
  | .ok _ => return some "ok"

unsafe def main : IO UInt32 := do
  let m := Guest.Gen.mandate
  match ← Guest.Gen.loadEnv m with
  | .error e =>
    IO.eprintln s!"componentgen: {e}"
    return 1
  | .ok env =>
    -- the manifest's fold: the marks = the decls (no hand-list)
    let targets := Guest.Gen.compileSetOf env m
    if targets.isEmpty then
      IO.eprintln "componentgen: the manifest's compile set is EMPTY — \
        no `@[guest]`/`@[guest_std]` mark in the manifest's modules \
        (the registration IS the surface; a hand list is not an option)"
      return 1
    match Guest.Gen.surfaceOf env m targets with
    | .error e =>
      IO.eprintln s!"componentgen: {e}"
      return 1
    | .ok surf =>
      -- the honest report (the observability discipline's minimal)
      let exportNames := String.intercalate ", " (surf.world.exports.map (·.name))
      IO.println s!"componentgen: manifest [{nameList m.implModules}] → \
        compile set [{nameList targets.toList}]; world `{m.world}` exports \
        [{exportNames}]; compiled-but-unexported (outside the component ABI) \
        [{nameList surf.excluded}]"
      match ← Guest.Gen.readTargets? env targets with
      | .error e =>
        IO.eprintln s!"componentgen: {e}"
        return 1
      | .ok decls =>
        match Guest.compile decls with
        | .error e =>
          IO.eprintln s!"componentgen: LOWER FAILED — {e.render}"
          return 1
        | .ok core => do
          -- the scalar lane's spec: the LCNF re-run's product
          let spec : Guest.Component.Spec := { core := core, world := surf.world }
          -- the five lanes' regens (the skew check rides each; the
          -- first refusal aborts the writer, nothing written)
          let lanes : List (String × Guest.Component.Spec) :=
            [("SCALAR", spec)
            , ("STRING", ComponentTests.Pipeline.stringSpec)
            , ("EDGE", ComponentTests.Pipeline.edgeSpec)
            , ("FAULT", ComponentTests.Pipeline.faultSpec)
            , ("WITNESS", ComponentTests.Pipeline.witSpec)]
          let mut ok := true
          for (tag, s) in lanes do
            let r ← regenLane tag s
            ok := ok && r.isSome
          if !ok then return 1
          -- All five lanes through the emit spine (the regens' checks
          -- already ran; the emitters re-run their pure folds).
          let _textRows ← Kit.Emit.runEmitters "componentgen"
            [(Guest.Component.componentEmitter, spec)
            ,(Guest.Component.stringComponentEmitter, ComponentTests.Pipeline.stringSpec)
            ,(Guest.Component.edgeComponentEmitter, ComponentTests.Pipeline.edgeSpec)
            ,(Guest.Component.faultComponentEmitter, ComponentTests.Pipeline.faultSpec)
            ,(Guest.Component.witComponentEmitter, ComponentTests.Pipeline.witSpec)]
            (fun _ f => pure { items := 1, contentHash := f.contents.hash })
          let _binRows ← Kit.Emit.runBinaryEmitters "componentgen"
            [(Guest.Component.componentEmitter, spec)
            ,(Guest.Component.stringComponentEmitter, ComponentTests.Pipeline.stringSpec)
            ,(Guest.Component.edgeComponentEmitter, ComponentTests.Pipeline.edgeSpec)
            ,(Guest.Component.faultComponentEmitter, ComponentTests.Pipeline.faultSpec)
            ,(Guest.Component.witComponentEmitter, ComponentTests.Pipeline.witSpec)]
            (fun _ f =>
              pure { items := 1, contentHash := Kit.Emit.bytesHash f.contents })
          IO.println s!"componentgen: the component slices' world texts + \
            component bytes (+ sidecars) written"
          return 0
