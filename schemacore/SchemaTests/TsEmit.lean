/- # SchemaTests.TsEmit — the TypeScript target's spine-discipline pins

The SECOND `Spine.CodeTarget` row's teeth (notes/design-forward-surface.md
§1's landing): the TS artifact rides the spine — the pins hold the
SPINE's discipline, not a second emitter's:

1. THE FACE-DECLARATION GATE: both real targets declare every face
   their record templates place (`spineFacesOk`); a target row that
   names a face it does not declare REFUSES — the emitter's run is
   EMPTY (the WIT lane's refusal-face precedent; the byte-tie's catch).
   THE NEGATIVE CONTROL (mandatory, 15-patterns #5): a broken target
   literal — `faceNames` carrying a face absent from `faces` — has NO
   artifact.
2. THE TS OUTPUT'S SHAPE PINS: the emitted artifact carries the
   interface + the JSON codec fns + the builder face + the two-faces
   honesty note (the canonical wire stays SchemaCore.Codec's bytes).
3. THE GOLDEN CHANNEL: `SchemaCore.Goldens.ts_artifact` is the
   kernel-side tie (emitter = committed golden); the live link is the
   goldens teeth. These pins are the runtime face over the same regen.

Evidence, not architecture — the five-question block lives in the
modules under test (SchemaCore.Emit.Spine / SchemaCore.Emit.Ts).
-/

import TestingKit.Harness
import SchemaCore
import SchemaCore.Goldens
import SchemaTests.Events

open SchemaCore TestingKit

/-! ## The fixtures -/

/-- The broken target: the record template places a face the target's
    table does not declare (the face-declaration gate's negative
    control — the TS row minus its builder face declaration). -/
def brokenTsTarget : SchemaCore.Emit.Spine.CodeTarget :=
  { SchemaCore.Emit.Ts.tsTarget with faces := [] }

/-! ## The suite -/

def tsEmitSpec : Spec :=
  Spec.ofList "the TS target's spine discipline: face gate, shape pins"
    (fun _ => do
      -- THE FACE-DECLARATION GATE (positive): both real targets
      -- declare every face their templates place.
      assert (SchemaCore.Emit.Spine.spineFacesOk
          SchemaCore.Emit.Rust.rustTarget)
        "the Rust target's face declarations drifted"
      assert (SchemaCore.Emit.Spine.spineFacesOk SchemaCore.Emit.Ts.tsTarget)
        "the TS target's face declarations drifted"
      -- THE ARTIFACT: the TS emitter over the pinned registry (the
      -- goldens teeth tie this registry to the live registration) —
      -- ONE file, the declared output path.
      let files := SchemaCore.Emit.Ts.tsEmitter.run Goldens.sliceReg
      assert (files.map (·.path) == ["gen/schema-slice.ts"])
        "the TS emitter's output set drifted"
      match files.head? with
      | none => assert false "the TS artifact must exist"
      | some f => do
        let body := f.contents
        -- THE SHAPE PINS: the universe faces + the record faces.
        assert (body.contains "export interface Example")
          "the record's TS interface is absent"
        assert (body.contains "export interface ExampleEx")
          "the second record's TS interface is absent"
        assert (body.contains "export function encodeExample")
          "the encode face is absent"
        assert (body.contains "export function decodeExample")
          "the decode face is absent"
        assert (body.contains "export class ExampleBuilder")
          "the builder face is absent (a target row missing a face \
            renders nothing — the face gate's positive arm)"
        -- THE TWO-FACES HONESTY: the canonical wire is the codec's.
        assert (body.contains "SchemaCore.Codec")
          "the JSON face's honesty note is absent (the wire of record)"
        -- the closed universe's TS faces
        assert (body.contains "export type Profile")
          "the closed enums' TS faces are absent"
        assert (body.contains "export type KeyString")
          "the branded key materials are absent"
      -- THE SPINE'S ONE-WRITER AUDIT (data level, 12 §3): the three
      -- renderings' outputs are pairwise disjoint.
      assert (Kit.Emit.outputsDisjoint
          [SchemaCore.witEmitter, SchemaCore.Emit.Rust.rustEmitter,
           SchemaCore.Emit.Ts.tsEmitter] = true)
        "the emitters' declared outputs collided")
    [ ("a target row missing a face still renders the artifact",
        fun _ =>
          -- THE SABOTAGE (must FAIL): the broken row's run is EMPTY —
          -- the face-declaration gate REFUSES (a face named but not
          -- declared is no artifact, never a partial render). The
          -- assertion claims the sabotaged world emitted anyway; the
          -- sweep catching this false claim IS the gate's tooth.
          assert (!(SchemaCore.Emit.Spine.spineEmitter brokenTsTarget
              |>.run Goldens.sliceReg).isEmpty)
            "control fired: the face-declaration gate refused the \
              broken row — never a partial render")
    , ("the broken target's face gate passes",
        fun _ =>
          -- THE SABOTAGE (must FAIL): the broken row's gate verdict is
          -- FALSE — asserting it true trips the vacuity wire if the
          -- gate's check ever stops distinguishing.
          assert (SchemaCore.Emit.Spine.spineFacesOk brokenTsTarget)
            "control fired: the broken row's gate verdict is false — \
              the refusal is the gate's, not the run's accident") ]
    4 42
