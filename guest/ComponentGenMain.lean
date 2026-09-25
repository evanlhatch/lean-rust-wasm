/-
ComponentGenMain — the `componentgen` exe: the component lane's
byte-tie writer side.

    lake exe componentgen

Runs `Guest.Component.regen` over the component spec — the lowered
core module (the LCNF re-run of `ComponentTests.Fixture.add64` — the
guest function IS compiled here, in-process) + the world — and writes
the component slice's artifacts through the Kit.Emit spine:

- the TEXT lane: the world text (`Render.worldFile`'s render face →
  `gen/component-slice.wit`, its 2-line GENERATED header inline);
- the BINARY lane: the component bytes (`componentEmitter`'s row →
  `gen/component-slice.wasm`) PLUS the `.hdr` sidecar carrying the
  same 2-line GENERATED header in text.

SKEW CHECK AT GENERATION: `regen` runs `Guest.Component.check` FIRST —
a world/component skew (a missing export, a signature drift, a
non-scalar type) is a generation failure (the rendered Diag on
stderr, exit 1), never an artifact. Nothing is written on refusal.

The LCNF re-run needs the unsafe IO (the importModules + the
compiler pipeline — the GuestTests.Main pattern; the interpreter is
on in the lakefile row). The PIPELINE is ComponentTests.Pipeline's
ONE copy — shared with the gen-check gate (the regen discipline: a
gate that re-encoded the writer would tie two encodings, not the
artifact to the spec).

The five questions (notes/v3/01-core.md): none of its own — the IO
shell over `Guest.Component.regen` (the answers live in
Guest.Component). Gate row: none — this exe is the component lane's
WRITER side (the CHECK side is `gates gen-check`'s component loop,
consuming the same Pipeline).
-/
import Guest
import ComponentTests.Pipeline

open Guest

unsafe def main : IO UInt32 := do
  match ← ComponentTests.Pipeline.loadCoreModule with
  | .error e =>
    IO.eprintln s!"componentgen: PIPELINE FAILED — {e}"
    return 1
  | .ok core => do
    -- the string lane's fixture: pure data, no LCNF re-run
    -- (ComponentTests.Pipeline.stringSpec)
    match Guest.Component.regen (ComponentTests.Pipeline.scalarSpec core) with
    | .error e =>
      IO.eprintln s!"componentgen: REGEN FAILED — {e}"
      return 1
    | .ok _ =>
      match Guest.Component.regen ComponentTests.Pipeline.stringSpec with
      | .error e =>
        IO.eprintln s!"componentgen: STRING REGEN FAILED — {e}"
        return 1
      | .ok _ => do
        -- Both lanes through the emit spine (the regen's check already
        -- ran; the emitters re-run their pure folds).
        let _textRows ← Kit.Emit.runEmitters "componentgen"
          [(Guest.Component.componentEmitter, ComponentTests.Pipeline.scalarSpec core)
          ,(Guest.Component.stringComponentEmitter, ComponentTests.Pipeline.stringSpec)]
          (fun _ f => pure { items := 1, contentHash := f.contents.hash })
        let _binRows ← Kit.Emit.runBinaryEmitters "componentgen"
          [(Guest.Component.componentEmitter, ComponentTests.Pipeline.scalarSpec core)
          ,(Guest.Component.stringComponentEmitter, ComponentTests.Pipeline.stringSpec)]
          (fun _ f =>
            pure { items := 1, contentHash := Kit.Emit.bytesHash f.contents })
        IO.println s!"componentgen: the component slices' world texts + \
          component bytes (+ sidecars) written"
        return 0
