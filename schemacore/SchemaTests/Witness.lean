/-
# SchemaTests.Witness — the witness lane's suites

The witness lane's teeth (15-patterns #5): the checker's
acceptance/refusal matrix over the CheckSlice fixture (the tampered
witness refuses; a false claim has NO witness), the guestVerified
discharge's discipline (the tier's first consumer — the discharge
fires exactly on checker acceptance, the mis-wire is visible data),
and the codec's round trips + refusals (append-form, the version
gate). Every law itself is theorem-backed in SchemaCore.Witness; the
runtime rows pin the VALUES.

The five questions: root = the witness lane's value-level evidence;
carrier = TestingKit's Spec (the negatives subtype); spine reading =
none; ladder rung = tested agreement rows over proved laws (the
theorem face is the authority; these pins are its regression surface);
gate row = SchemaTests' witness suites + the axiom report
(SchemaTests.Axioms pins the checker's cone).

-/

import TestingKit.Harness
import Kit.Obligation
import SchemaCore.Witness
import SchemaCore.WitnessGen
import SchemaCore.Emit.Witness
import SchemaCore.CheckSlice

open Kit SchemaCore TestingKit

/-! ## The fixtures (the witnesses — hand-built, which is the point:
     the producer is untrusted; only accepting ones certify) -/

/-- The good row (the check lane's fixture — count = 3). -/
def wRow : RowVals exampleCheckFields := goodRow

/-- The passing atomic witness: count > 0. -/
def wCount : Witness exampleCheckFields :=
  { label := "count-positive", claim := .u64GtLit "count" 0
    proof := .verdict true, fuel := 1 }

/-- The TAMPERED sibling: the record flipped — the checker must
    refuse (the record is verified, never trusted). -/
def wCountTampered : Witness exampleCheckFields :=
  { wCount with proof := .verdict false }

/-- The compound witness: count > 0 ∧ ¬(count = 0) — both children
    certified down the tree. -/
def wCompound : Witness exampleCheckFields :=
  { label := "count-compound"
    claim := .and (.u64GtLit "count" 0) (.not (.u64EqLit "count" 0))
    proof := .conj (.verdict true) (.neg (.verdict false))
    fuel := 2 }

/-- The disjunction witness: the LEFT disjunct is false at the fixture
    row (count = 3 ≠ 0), so the chosen side MUST be the right one —
    the wrong choice refuses. -/
def wDisj : Witness exampleCheckFields :=
  { label := "count-disj"
    claim := .or (.u64EqLit "count" 0) (.u64GtLit "count" 1)
    proof := .disj false (.verdict true)
    fuel := 2 }

/-- The disjunction's WRONG choice (the false left side certified). -/
def wDisjWrong : Witness exampleCheckFields :=
  { wDisj with proof := .disj true (.verdict true) }

/-- The FALSE claim: count = 0 at the good row — NO witness can
    certify it (the refusal is theorem-backed:
    `Witness.check_false_refuses`). -/
def wFalse : Witness exampleCheckFields :=
  { label := "count-zero", claim := .u64EqLit "count" 0
    proof := .verdict true, fuel := 1 }

/-- The SHAPE mismatch: an atomic claim with a conjunction proof term
    — not evidence, refusal (the calculus's catch-all). -/
def wShape : Witness exampleCheckFields :=
  { label := "shape-mismatch", claim := .lit true
    proof := .conj (.verdict true) (.verdict true), fuel := 2 }

/-- The claim's bytes (the codec pins' comparison face — Pred carries
    no BEq; the encoding is the value's faithful image, append-form
    law proved). -/
def predBytes (p : Pred exampleCheckFields) : List UInt8 := encPred p

/-! ## The producer (the lane's missing half — the producer→checker
     round + the completeness/teeth) -/

/-- The produced compound witness (the producer→checker round's
    Lean-side artifact: generated + self-checked at the pinned fuel). -/
def producedCompound : Option (Witness exampleCheckFields) :=
  WitnessGen.selfChecked? "count-compound"
    (.and (.u64GtLit "count" 0) (.not (.u64EqLit "count" 0))) wRow

/-- The producer suite: generation is complete for true claims (every
    seeded spec produces; the produced witness CHECKS at its pinned
    fuel AND at any larger cap — the mono transport's runtime face),
    the false claim has NO shipped certificate, and the emit face's
    seeded bytes decode back (the wire's round trip over the PRODUCED
    bytes, not hand-built ones). -/
def witnessProducerSpec : Spec :=
  Spec.ofList "the witness producer: completeness, the round, the refusal"
    (fun _ =>
      -- every seeded spec produces (the emit face's registry is
      -- renderable — the run path's self-check passed)
      let allSeeded :=
        SchemaCore.Emit.Witness.seedSpecs.all
          (fun s => (SchemaCore.Emit.Witness.produce? s).isSome)
      -- the producer→checker round: the produced witness checks at
      -- its pinned fuel, at 100× the cap (mono's runtime face), and
      -- its fuel IS the pinned one (needed × 4)
      let round :=
        match producedCompound with
        | some w =>
            w.checks wRow
              && (checkWitness 100 w.claim w.proof wRow)
              && (w.fuel == WitnessGen.fuelPinned w.claim)
        | none => false
      -- the false claim's refusal (the producer NEVER ships it —
      -- theorem-backed: `selfChecked?_none_of_check_false`)
      let refuses := (WitnessGen.selfChecked? "count-zero"
        (Pred.u64EqLit "count" 0) wRow).isNone
      -- the PRODUCED bytes round-trip (the wire over the generated
      -- artifact — the duel's accept-vector source)
      let wire :=
        match decWitness? (fs := exampleCheckFields) 1
            (SchemaCore.Emit.Witness.seedBytes
              SchemaCore.Emit.Witness.seedHead ++ []) with
        | some (w, rest) =>
            rest == []
              && (w.label == SchemaCore.Emit.Witness.seedHead.label)
              && (w.checks wRow)
        | none => false
      assert (allSeeded && round && refuses && wire)
        "the witness producer drifted")
    (([ ("the producer emits for a false claim",
        fun _ =>
          assert ((WitnessGen.selfChecked? "count-zero"
              (Pred.u64EqLit "count" 0) wRow).isSome)
            "control fired: a false claim has NO shipped certificate — the self-check refuses")
    , ("the refusal vectors decode-and-accept",
        fun _ =>
          -- the tampered record: the claim is TRUE at the row, so the
          -- decode succeeds — and the CHECKER must refuse the flipped
          -- record (the duel's refusal vector is a checker refusal,
          -- not a decode refusal)
          match decWitness? (fs := exampleCheckFields) 1
              (SchemaCore.Emit.Witness.refuseTamperedRecord ++ []) with
          | some (w, rest) =>
              assert (rest == [] && w.checks wRow)
                "control fired: the flipped record must be REFUSED by the checker — the record is verified, never trusted"
          | none => .error "control: the tampered bytes must decode")
    , ("the producer's checked prop is sound-only",
        fun _ =>
          assert ((WitnessGen.producerChecked "x"
              (Pred.u64GtLit "count" 0 : Pred exampleCheckFields)).isComplete
            = false)
            "control fired: the flags moved — the producer's face is the complete one") ]
     : List (String × (Tape → CheckResult))))
    4 42

/-- The duel's coverage pin (the kernel's face): the duel's expectations
    cover exactly the emitted vectors. -/
example : Kit.Duel.expectsCovered SchemaCore.Emit.Witness.witnessDuel = true := rfl

/-! ## The suites -/

/-- The checker's acceptance/refusal matrix + the duel rows. -/
def witnessCheckerSpec : Spec :=
  Spec.ofList "the witness checker: acceptance, refusal, the duel"
    (fun _ => assert (
      -- the honest witnesses are accepted (fuel exactly as shipped)
      (wCount.checks wRow)
        && (wCompound.checks wRow)
        && (wDisj.checks wRow)
      -- monotonicity's runtime face: a larger cap never flips an
      -- acceptance (the theorem `checkWitness_mono` is the authority)
        && (checkWitness 10 wCount.claim wCount.proof wRow)
      -- the refusal matrix: EVERY tampered/mismatched/false shape
        && (!wCountTampered.checks wRow)
        && (!wDisjWrong.checks wRow)
        && (!wFalse.checks wRow)
        && (!wShape.checks wRow)
        && (checkWitness 0 wCount.claim wCount.proof wRow == false)
      -- THE DUEL TIE (the runtime rows over the proved laws): an
      -- accepted witness certifies the claim's own check; the false
      -- claim's check is false, and the refusal follows
        && (wCount.claim.check wRow)
        && (wFalse.claim.check wRow == false))
      "the witness checker's acceptance/refusal matrix drifted")
    [ ("the tampered record still certifies",
        fun _ => assert (wCountTampered.checks wRow)
          "control fired: the record must be VERIFIED, never trusted")
    , ("fuel 0 accepts",
        fun _ => assert (checkWitness 0 wCount.claim wCount.proof wRow)
          "control fired: exhaustion IS refusal — the cap is the \
            semantics, never a trap")
    , ("the false claim's witness is accepted",
        fun _ => assert (wFalse.checks wRow)
          "control fired: a false claim has NO witness — the refusal \
            is theorem-backed")
    , ("a shape-mismatched proof term is accepted",
        fun _ => assert (wShape.checks wRow)
          "control fired: a proof term that does not fit the claim is \
            not evidence")
    , ("the disjunction's wrong choice is accepted",
        fun _ => assert (wDisjWrong.checks wRow)
          "control fired: the chosen side must be the TRUE one") ]
    4 42

/-- The guestVerified discharge's discipline — the tier's first
    consumer, live. -/
def witnessObligationSpec : Spec :=
  Spec.ofList "the guestVerified discharge: tier, evidence, soundness"
    (fun _ => do
      -- the obligation row: the computed tier, the claim as the index
      assert (((wCount.obligation wRow).tier) == Tier.guestVerified)
        "witness.obligationTier"
      -- the discharge FIRES exactly on checker acceptance — the
      -- guestWitness evidence is the artifact + the checker's verdict
      match wCount.discharge wRow "gen/witness/wcount.bin" "count-positive" with
      | some (.guestWitness a r) =>
          assert ((a == "gen/witness/wcount.bin") && (r == "count-positive"))
            "witness.dischargeEvidence"
      | _ => .error "witness.dischargeFired"
      -- the tampered witness REFUSES (none — the loud gap, never a
      -- fabricated evidence)
      assert ((wCountTampered.discharge wRow "a" "r").isNone)
        "witness.dischargeRefuses"
      -- the Discharged row CONSTRUCTS (the tier match is decided)
      let _ : Discharged (List String) (wCount.claim.Sat wRow) :=
        { obligation := wCount.obligation wRow
          evidence := .guestWitness "gen/witness/wcount.bin" "count-positive"
          tierOK := rfl }
      pure ())
    [ ("the tampered witness discharges",
        fun _ =>
          assert ((wCountTampered.discharge wRow "a" "r").isSome)
            "control fired: a refused witness must NOT mint evidence")
    , ("the mis-wire is invisible",
        fun _ =>
          assert (¬(Kit.tierMismatch (wCount.obligation wRow)
            (Kit.Evidence.decided true)))
            "control fired: a decided evidence against guestVerified \
              IS a mis-wire — the data check must see it") ]
    4 42

/-- The codec: append-form round trips over the witness data, the
    version gate, the refusal matrix. -/
def witnessCodecSpec : Spec :=
  Spec.ofList "the witness codec: round trips, the version gate, refusals"
    (fun _ =>
      -- the append-form law, live: any suffix rides through
      let rt (suffix : List UInt8) : Bool :=
        match decWitness? (fs := exampleCheckFields) 1
            (encWitness 1 wCount ++ suffix) with
        | some (w, rest) =>
            rest == suffix
              && (w.label == wCount.label)
              && (w.fuel == wCount.fuel)
              && (w.proof == wCount.proof)
              && (predBytes w.claim == predBytes wCount.claim)
        | none => false
      -- the atomic decoders' kernel pins (Pred has no BEq — the match
      -- IS the comparison)
      let rtP : Bool :=
        match decPred? (fs := []) (encPred (fs := []) (.lit true)) with
        | some (.lit b, []) => b
        | _ => false
      let ok : Bool :=
        rt [] && rt [9] && rt [0, 1] && rtP
          && (decWProof? (encWProof (.verdict true)) == some (.verdict true, []))
      -- the refusal matrix: truncation, unknown tag, wrong version
          && ((decWitness? (fs := exampleCheckFields) 1 [1]).isNone)
          && ((decWProof? [9]).isNone)
          && ((decWitness? (fs := exampleCheckFields) 2
                (encWitness 1 wCount ++ [])).isNone)
      assert ok "the witness codec drifted")
    [ ("the wrong version decodes",
        fun _ =>
          assert ((decWitness? (fs := exampleCheckFields) 2
            (encWitness 1 wCount ++ [])).isSome)
            "control fired: the version gate must refuse a mismatch")
    , ("a truncated witness decodes",
        fun _ =>
          assert ((decWitness? (fs := exampleCheckFields) 1 [1]).isSome)
            "control fired: truncation must refuse, never zero-parse")
    , ("an unknown tag decodes",
        fun _ => assert ((decWProof? [9]).isSome)
          "control fired: an unknown tag must refuse")
    , ("the round trip drops the proof",
        fun _ =>
          match decWitness? (fs := exampleCheckFields) 1
              (encWitness 1 wCount ++ []) with
          | some (w, _) => assert (w.proof == WProof.verdict false)
            "control fired: the proof term must survive the wire"
          | none => .error "control: the round trip itself broke") ]
    4 42
