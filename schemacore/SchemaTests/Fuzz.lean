/-
# SchemaTests.Fuzz — the fuzz face's pins (the C3 lane's Lean side)

The fuzz emitter's shape pins + the mandatory negative controls (the
landed discipline: positive pins + the must-fail controls, 15-patterns
#5). The generated ARTIFACTS' bytes are byte-tied by `gates gen-check`
(the ONE tie per artifact — the dual's/duel's rule); this suite pins
the lane's STRUCTURE to the live pinned registry (`Goldens.sliceReg`):

- the emitter declares exactly the two artifacts (the one-writer face
  the ownership gate folds);
- the generated Arbitrary face carries EVERY registered record's impl
  (the fold's coverage — a registry row without an impl is a missing
  consumer, caught here);
- the TAPE GOLDEN is the LCG recurrence's own output (an INDEPENDENT
  re-derivation through `TestingKit.lcg`'s raw step — the cross-
  language tie's producer face, pinned against the function it feeds).

Evidence, not architecture — the five-question block lives in
SchemaCore.Emit.Fuzz.
-/

import TestingKit.Harness
import SchemaCore
import SchemaCore.Emit
import SchemaCore.Emit.Fuzz
import SchemaCore.Goldens

open SchemaCore TestingKit

namespace SchemaTests.Fuzz

/-! ## The suite -/

/-- The corrupted golden (the first control's claim): the byte list
    with its head replaced — must NOT equal the real golden. -/
def corruptedGolden : List UInt64 := 255 :: SchemaCore.Emit.Fuzz.tapeGoldenBytes.drop 1

def fuzzEmitSpec : Spec :=
  Spec.ofList "the fuzz face: the generated Arbitrary + the tape tie"
    (fun _ => do
      -- the emitter declares exactly the two artifacts (the ownership
      -- gate's real-emitter set folds this declaration)
      assert (SchemaCore.Emit.Fuzz.fuzzGenEmitter.outputs ==
          ["crates/schema-generated/tests/fuzz_gen.rs",
           "crates/schema-generated/tests/fuzz_properties.rs"])
        "the fuzz emitter's declared outputs drifted"
      -- the generated Arbitrary face carries EVERY registered record's
      -- impl — the fold's coverage (a registry row's record renders as
      -- `impl Arbitrary for <Pascal>`; the spelling is pascalName's)
      let body := SchemaCore.Emit.Fuzz.fuzzGenBody SchemaCore.Goldens.sliceReg
      assert (SchemaCore.Goldens.sliceReg.items.all fun item =>
        body.contains ("impl Arbitrary for "
          ++ SchemaCore.Emit.Rust.pascalName item.name))
        "a registry record's Arbitrary impl is missing from the generated face"
      -- THE TAPE TIE, BOUNDS ROW (runtime face): the golden's first
      -- bound is the NINTH step's `(>> 16) % 7` — the bytes' eight
      -- steps leave the tape, the bounds continue THAT stream (the
      -- golden test's replay order). The kernel does not reduce the
      -- nine-deep step chain (the byte row's `rfl` below reduces; this
      -- one does not), so the pin rides the spec's runtime assert.
      assert (SchemaCore.Emit.Fuzz.tapeGoldenBelows.head! ==
        ((TestingKit.lcg (TestingKit.Tape.advance
            (TestingKit.Tape.ofSeed SchemaCore.Emit.Fuzz.tapeGoldenSeed) 8).state
          >>> 16) % 7).toNat)
        "the tape tie drifted: the golden bound is not the continuation's first draw")
    [("a corrupted golden matches the tie",
        fun _ =>
          assert (corruptedGolden == SchemaCore.Emit.Fuzz.tapeGoldenBytes)
            "control fired: the corrupted golden matched — the tie is vacuous")
    , ("the generated face is empty",
        fun _ =>
          assert (SchemaCore.Emit.Fuzz.fuzzGenBody SchemaCore.Goldens.sliceReg == "")
            "control fired: an empty body passed — the coverage pin is vacuous")
    , ("the golden plan lost its draws",
        fun _ =>
          assert (SchemaCore.Emit.Fuzz.tapeGoldenBytes.length < 8
            && SchemaCore.Emit.Fuzz.tapeGoldenBelows.length < 8)
            "control fired: a short plan passed — the draw plan's pin is vacuous") ]
    4 42

/-- THE TAPE TIE (the golden's producer face, pinned independently of
    the drawers): the golden's first byte IS the raw recurrence's
    first step's top byte — `TestingKit.lcg` applied to the pinned
    seed, shifted (the byte drawer's shape), computed here through the
    recurrence ITSELF, not through `Tape.byte`. -/
example : SchemaCore.Emit.Fuzz.tapeGoldenBytes.head! =
  (TestingKit.lcg SchemaCore.Emit.Fuzz.tapeGoldenSeed >>> 56) := rfl

/-- The cross-emitter one-writer audit over the fuzz row (the
    ownership discipline, data level — the Rust lane's pins' shape). -/
example : Kit.Emit.outputsDisjoint
    [SchemaCore.witEmitter, SchemaCore.Emit.Rust.rustEmitter,
     SchemaCore.Emit.Fuzz.fuzzGenEmitter] = true := by decide

end SchemaTests.Fuzz
