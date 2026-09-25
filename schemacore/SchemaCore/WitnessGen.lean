/-
# SchemaCore.WitnessGen — the witness lane's PRODUCER face

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/04-verification.md §3 (THE certificate
pattern's producer half: from a TRUE claim, GENERATE the certificate —
the producer is untrusted by construction, because every consumer is
the checker: `selfChecked?` re-verifies the generated term in-process
and the downstream verifier re-verifies again); notes/v3/15-patterns.md
#3 (the pattern's canonical instance IS the witness lane — this module
completes the producer→checker→discharge flow the checker half,
`SchemaCore.Witness`, landed). Mined: `legacy/lean/schema-lang/
SchemaLang/Emit/Witness.lean` (the proof-term generation
`proofFor`/`generateWitness`, the self-check wired into the run path,
the pinned fuel `consumed × 4`, the completeness theorems) — ported
FRESH over the landed substrate.

THE PRODUCER'S SHAPE: `proofFor` walks the claim (a `Pred fs` — the
check lane's OWN fragment, no parallel claim table) and emits the
proof term the claim's shape demands:

- an ATOMIC claim records its computed verdict (`.verdict (p.check
  row)` — the record is a CLAIM: the checker re-fires the check and
  the two must AGREE, the tamper tooth);
- `and` certifies both children (the terms compose structurally);
- `or` records the CHOSEN side — the side whose own check fired true
  (when both sides fire false, no claim-matched term exists:
  `proofFor` refuses, `none`);
- `not` emits the refutation record (`.neg (.verdict false)`) — the
  checker verifies the inner check ACTUALLY fired false (soundness
  rides `Pred.check_complete`'s contrapositive through
  `checkWitness_sound`).

THE SELF-CHECK (the order's core rule, the legacy's verbatim): an
emitter that emits an unchecked witness is a bug. `selfChecked?` runs
the freshly generated certificate through the LANDED checker at its
pinned fuel; a refusal is `none` — the emit face
(`SchemaCore.Emit.Witness`) renders rows only from `some`.

THE FUEL (the legacy owner decision, `consumed × 4`): `fuelNeeded`
counts exactly what the checker consumes on an accepting run (one unit
per claim node walked: `and` walks both children, `or` the chosen
side, `not` stops at the refutation record — the checker's `not` arm
fires the inner check in ONE step); `fuelPinned` multiplies by 4.
Host and consumer agree BY CONSTRUCTION (the fuel ships in the
certificate), and the headroom can never flip a verdict —
`checkWitness_mono` transports acceptance to any larger cap.

THE COMPLETENESS HONESTY (the module's deliverable): for a claim in
the supported fragment that HOLDS, the producer finds a witness, and
the witness PASSES the checker at its pinned fuel:

    p.check row = true → ∃ pr, proofFor p row = some pr
                         ∧ checkWitness (fuelPinned p) p pr row = true

stated at the fragment's size (the fragment is `Pred`'s; `check` is
COMPLETE over it by the proved bridge `Pred.check_iff`, so the check
face IS the denotation face — `selfChecked?_of_sat` states the same
theorem at `p.Sat row`). The boundary, named: this is completeness OF
THE PRODUCER at ITS pinned fuel — the bare checker stays sound-only
(a true claim under an under-sized cap refuses; `Witness.
witnessChecked.complete?` is `.missing` and stays so). The producer's
face closes the gap AT THE PRODUCER: `producerChecked` mounts the
generated-and-self-checked verdict as a `Kit.CheckedProp` whose
completeness is `.proved` — the first `.proved` rung on this lane.

The trust story: `selfChecked?`-shipped certificates are sound by the
CHECKER's theorem (`Witness.checks_sound` — no new trust base); the
producer adds only completeness, and completeness is a THEOREM, not a
promise.

Core-only (imports SchemaCore.Witness — the cone rule).
-/

import SchemaCore.Witness

namespace SchemaCore

/-! ## The fuel accounting -/

/-- The fuel the checker CONSUMES on an accepting run over a generated
    proof: one unit per claim node walked (`and` walks both children,
    `or` the chosen side — the bound is the max, the walk is one side —
    `not` stops at the refutation record's one-step check). -/
def WitnessGen.fuelNeeded : Pred fs → Nat
  | .lit _ => 1
  | .u64EqLit _ _ => 1
  | .u64GtLit _ _ => 1
  | .u64Eq _ _ => 1
  | .strEqLit _ _ => 1
  | .and p q => 1 + WitnessGen.fuelNeeded p + WitnessGen.fuelNeeded q
  | .or p q => 1 + max (WitnessGen.fuelNeeded p) (WitnessGen.fuelNeeded q)
  | .not _ => 1

/-- The SHIPPED fuel: `needed × 4` (the legacy owner decision 2 —
    host and consumer agree by construction, the fuel ships in the
    certificate, and a legitimately expensive witness is a
    claim-shape finding, never a retry; the headroom can never flip a
    verdict — `checkWitness_mono`). -/
def WitnessGen.fuelPinned (p : Pred fs) : Nat := WitnessGen.fuelNeeded p * 4

/-! ## Generation: the claim-matched proof term -/

/-- The proof term the claim's shape demands. `none` = no
    claim-matched term exists (an `or` whose both sides check false —
    whichever side the record chose, the checker refuses: the chosen
    side's own verdict is false, the other side's shape mismatches.
    There is no honest term to ship). The producer is untrusted: every
    recorded verdict is a CLAIM the checker re-fires. -/
def WitnessGen.proofFor : (p : Pred fs) → RowVals fs → Option WProof
  | .lit b, _ => some (.verdict b)
  | .u64EqLit n v, row =>
      some (.verdict (Pred.check (.u64EqLit n v) row))
  | .u64GtLit n v, row =>
      some (.verdict (Pred.check (.u64GtLit n v) row))
  | .u64Eq a b, row =>
      some (.verdict (Pred.check (.u64Eq a b) row))
  | .strEqLit n s, row =>
      some (.verdict (Pred.check (.strEqLit n s) row))
  | .and p q, row =>
      (WitnessGen.proofFor p row).bind fun pp =>
        (WitnessGen.proofFor q row).map fun pq => .conj pp pq
  | .or p q, row =>
      if p.check row then
        (WitnessGen.proofFor p row).map fun pp => .disj true pp
      else
        (WitnessGen.proofFor q row).map fun pq => .disj false pq
  | .not _, _ => some (.neg (.verdict false))

/-! ## The completeness half (the two theorems, in dependency order) -/

/-- GENERATION FINDS A TERM for a true claim: a claim whose check
    fires true has a claim-matched proof term (the `or`'s choice is
    forced by the disjunction's check: some side fired). -/
theorem WitnessGen.proofFor_isSome_of_check {fs : List Field} :
    ∀ (p : Pred fs) (row : RowVals fs), p.check row = true →
      ∃ pr, WitnessGen.proofFor p row = some pr := by
  intro p
  induction p with
  | lit b => intro row _; exact ⟨_, rfl⟩
  | u64EqLit n v => intro row _; exact ⟨_, rfl⟩
  | u64GtLit n v => intro row _; exact ⟨_, rfl⟩
  | u64Eq a b => intro row _; exact ⟨_, rfl⟩
  | strEqLit n s => intro row _; exact ⟨_, rfl⟩
  | and p q ihp ihq =>
      intro row hc
      simp only [Pred.check, Bool.and_eq_true] at hc
      obtain ⟨pp, hpp⟩ := ihp row hc.1
      obtain ⟨pq, hpq⟩ := ihq row hc.2
      exact ⟨WProof.conj pp pq, by
        simp only [WitnessGen.proofFor, hpp, hpq, Option.bind_some,
          Option.map_some]⟩
  | or p q ihp ihq =>
      intro row hc
      simp only [Pred.check, Bool.or_eq_true] at hc
      rcases hc with hc | hc
      · -- the LEFT side fired: the record chooses it
        obtain ⟨pp, hpp⟩ := ihp row hc
        exact ⟨WProof.disj true pp, by
          simp only [WitnessGen.proofFor, if_pos hc, hpp, Option.map_some]⟩
      · -- the RIGHT side fired: split on the left's verdict for the
        -- if's branch (the true-left case re-uses the left side's term)
        cases hleft : p.check row with
        | true =>
            obtain ⟨pp, hpp⟩ := ihp row hleft
            exact ⟨WProof.disj true pp, by
              simp only [WitnessGen.proofFor, if_pos hleft, hpp,
                Option.map_some]⟩
        | false =>
            obtain ⟨pq, hpq⟩ := ihq row hc
            exact ⟨WProof.disj false pq, by
              simp only [WitnessGen.proofFor,
                if_neg (show ¬(p.check row = true) from by rw [hleft]; simp),
                hpq, Option.map_some]⟩
  | not p _ => intro row _; exact ⟨WProof.neg (WProof.verdict false), rfl⟩

/-- A generated atomic verdict ACCEPTS at the pinned fuel: the record
    is the computed check, so the checker's agreement arm fires. -/
theorem WitnessGen.accept_verdict {fs : List Field} (p : Pred fs)
    (row : RowVals fs) (hc : p.check row = true) :
    checkWitness (WitnessGen.fuelPinned p) p (.verdict true) row = true := by
  have h1 : 0 < WitnessGen.fuelPinned p := by
    cases p <;>
      simp only [WitnessGen.fuelPinned, WitnessGen.fuelNeeded] <;> omega
  obtain ⟨f, hf⟩ : ∃ f, WitnessGen.fuelPinned p = f + 1 :=
    ⟨WitnessGen.fuelPinned p - 1, by omega⟩
  rw [hf]
  simp only [checkWitness, hc, Bool.and_self]

/-- GENERATION IS COMPLETE FOR TRUE CLAIMS (the acceptance half): a
    claim whose check fires true has a claim-matched proof term, and
    the term ACCEPTS at the pinned fuel (the fuel transports ride
    `checkWitness_mono` — the headroom is provably enough). -/
theorem WitnessGen.proofFor_accept {fs : List Field} :
    ∀ (p : Pred fs) (row : RowVals fs) (pr : WProof),
      WitnessGen.proofFor p row = some pr → p.check row = true →
      checkWitness (WitnessGen.fuelPinned p) p pr row = true := by
  intro p
  induction p with
  | lit b =>
      intro row pr hpr hc
      simp only [WitnessGen.proofFor] at hpr
      cases hpr
      rw [show WitnessGen.fuelPinned (.lit b) = 3 + 1 from by
        simp [WitnessGen.fuelPinned, WitnessGen.fuelNeeded]]
      simp only [checkWitness, Pred.check] at hc ⊢
      simp [hc]
  | u64EqLit n v =>
      intro row pr hpr hc
      simp only [WitnessGen.proofFor] at hpr
      cases hpr
      rw [hc]
      exact WitnessGen.accept_verdict _ row hc
  | u64GtLit n v =>
      intro row pr hpr hc
      simp only [WitnessGen.proofFor] at hpr
      cases hpr
      rw [hc]
      exact WitnessGen.accept_verdict _ row hc
  | u64Eq a b =>
      intro row pr hpr hc
      simp only [WitnessGen.proofFor] at hpr
      cases hpr
      rw [hc]
      exact WitnessGen.accept_verdict _ row hc
  | strEqLit n s =>
      intro row pr hpr hc
      simp only [WitnessGen.proofFor] at hpr
      cases hpr
      rw [hc]
      exact WitnessGen.accept_verdict _ row hc
  | and p q ihp ihq =>
      intro row pr hpr hc
      simp only [Pred.check, Bool.and_eq_true] at hc
      obtain ⟨pp, hpp⟩ := WitnessGen.proofFor_isSome_of_check p row hc.1
      obtain ⟨pq, hpq⟩ := WitnessGen.proofFor_isSome_of_check q row hc.2
      simp only [WitnessGen.proofFor, hpp, hpq, Option.bind_some,
        Option.map_some] at hpr
      cases hpr
      obtain ⟨F, hF⟩ : ∃ F, WitnessGen.fuelPinned (.and p q) = F + 1 :=
        ⟨4 * (1 + WitnessGen.fuelNeeded p + WitnessGen.fuelNeeded q) - 1,
          by simp only [WitnessGen.fuelPinned, WitnessGen.fuelNeeded]; omega⟩
      have hle1 : WitnessGen.fuelPinned p ≤ F := by
        have := hF
        simp only [WitnessGen.fuelPinned, WitnessGen.fuelNeeded] at this ⊢
        omega
      have hle2 : WitnessGen.fuelPinned q ≤ F := by
        have := hF
        simp only [WitnessGen.fuelPinned, WitnessGen.fuelNeeded] at this ⊢
        omega
      rw [hF]
      simp only [checkWitness, Bool.and_eq_true]
      exact ⟨checkWitness_mono p pp row hle1 (ihp row pp hpp hc.1),
             checkWitness_mono q pq row hle2 (ihq row pq hpq hc.2)⟩
  | or p q ihp ihq =>
      intro row pr hpr hc
      -- the or-check's arm IS the Bool disjunction (definitional)
      cases hleft : p.check row with
      | true =>
          -- the LEFT side fired: the record chose it
          obtain ⟨pp, hpp⟩ := WitnessGen.proofFor_isSome_of_check p row hleft
          simp only [WitnessGen.proofFor, if_pos hleft, hpp,
            Option.map_some] at hpr
          cases hpr
          obtain ⟨F, hF⟩ : ∃ F, WitnessGen.fuelPinned (.or p q) = F + 1 :=
            ⟨4 * (1 + max (WitnessGen.fuelNeeded p)
                    (WitnessGen.fuelNeeded q)) - 1,
              by simp only [WitnessGen.fuelPinned, WitnessGen.fuelNeeded]; omega⟩
          have hle1 : WitnessGen.fuelPinned p ≤ F := by
            have := hF
            simp only [WitnessGen.fuelPinned, WitnessGen.fuelNeeded] at this ⊢
            omega
          rw [hF, checkWitness]
          exact checkWitness_mono p pp row hle1 (ihp row pp hpp hleft)
      | false =>
          -- the left side refused: the or's check forces the RIGHT side
          simp only [Pred.check, Bool.or_eq_true] at hc
          rcases hc with hc | hc
          · exact absurd hc (by rw [hleft]; simp)
          obtain ⟨pq, hpq⟩ := WitnessGen.proofFor_isSome_of_check q row hc
          simp only [WitnessGen.proofFor,
            if_neg (show ¬(p.check row = true) from by rw [hleft]; simp),
            hpq, Option.map_some] at hpr
          cases hpr
          obtain ⟨F, hF⟩ : ∃ F, WitnessGen.fuelPinned (.or p q) = F + 1 :=
            ⟨4 * (1 + max (WitnessGen.fuelNeeded p)
                    (WitnessGen.fuelNeeded q)) - 1,
              by simp only [WitnessGen.fuelPinned, WitnessGen.fuelNeeded]; omega⟩
          have hle2 : WitnessGen.fuelPinned q ≤ F := by
            have := hF
            simp only [WitnessGen.fuelPinned, WitnessGen.fuelNeeded] at this ⊢
            omega
          rw [hF, checkWitness]
          exact checkWitness_mono q pq row hle2 (ihq row pq hpq hc)
  | not p _ =>
      intro row pr hpr hc
      -- hc : the negation's check fired — the inner check did NOT
      have hfalse : p.check row = false := by
        simp only [Pred.check, Bool.not_eq_true'] at hc
        exact hc
      simp only [WitnessGen.proofFor] at hpr
      cases hpr
      rw [show WitnessGen.fuelPinned (.not p) = 3 + 1 from by
        simp [WitnessGen.fuelPinned, WitnessGen.fuelNeeded]]
      simp only [checkWitness, hfalse, Bool.not_false]

/-! ## The certificate assembly (the untrusted producer's artifact) -/

/-- The certificate assembly: the claim-matched proof term + the pinned
    fuel + the label, as the landed `Witness` artifact. UNCHECKED —
    the self-check is `selfChecked?`'s, and the emit face consumes
    only `selfChecked?` (this function exists separately so the tests'
    doctored-generator control can exhibit exactly what skipping the
    check would ship). -/
def WitnessGen.generateWitness (label : String) (p : Pred fs)
    (row : RowVals fs) : Option (Witness fs) :=
  (WitnessGen.proofFor p row).map fun proof =>
    { label := label, claim := p, proof := proof
      fuel := WitnessGen.fuelPinned p }

/-- THE SELF-CHECK (the order's core rule): generation is complete
    only when the freshly generated certificate passes the LANDED
    checker in-process at its pinned fuel over the row. `none` =
    emission failure (the emit face refuses to render — loud). -/
def WitnessGen.selfChecked? (label : String) (p : Pred fs)
    (row : RowVals fs) : Option (Witness fs) :=
  match WitnessGen.generateWitness label p row with
  | none => none
  | some w => if w.checks row then some w else none

/-- The self-check's match shape (the theorems' one unfolding). -/
theorem WitnessGen.selfChecked?_eq (label : String) (p : Pred fs)
    (row : RowVals fs) :
    WitnessGen.selfChecked? label p row =
      match WitnessGen.generateWitness label p row with
      | none => none
      | some w => if w.checks row then some w else none := rfl

/-! ## The producer's completeness (the honest statement) -/

/-- The generated witness, extracted: when the self-check accepts, the
    artifact is `some w` and `w` CHECKS at its shipped fuel (the
    checker ran in-process — the emit face renders only from this). -/
theorem WitnessGen.selfChecked?_checks {fs : List Field} (label : String)
    (p : Pred fs) (row : RowVals fs)
    (h : (WitnessGen.selfChecked? label p row).isSome = true) :
    ∃ w, WitnessGen.selfChecked? label p row = some w ∧ w.checks row = true := by
  rw [WitnessGen.selfChecked?_eq] at h ⊢
  cases hg : WitnessGen.generateWitness label p row with
  | none =>
      rw [hg] at h
      simp at h
  | some w =>
      rw [hg] at h
      by_cases hc : w.checks row = true
      · refine ⟨w, ?_, hc⟩
        simp [if_pos hc]
      · simp [if_neg hc] at h

/-- THE PRODUCER'S COMPLETENESS (the honest statement, at the fragment's
    size): for a claim in the supported fragment that HOLDS (`Sat` —
    the spec of record), the producer finds a certificate, and the
    certificate passed the checker at its pinned fuel (that is what
    `isSome` IS — the self-check's acceptance). -/
theorem WitnessGen.selfChecked?_of_sat {fs : List Field} (label : String)
    (p : Pred fs) (row : RowVals fs) (hs : p.Sat row) :
    (WitnessGen.selfChecked? label p row).isSome = true := by
  have hacc := WitnessGen.proofFor_isSome_of_check p row
    (p.check_complete row hs)
  obtain ⟨pr, hpr⟩ := hacc
  have hok := WitnessGen.proofFor_accept p row pr hpr (p.check_complete row hs)
  have hok' : Witness.checks ⟨label, p, pr, WitnessGen.fuelPinned p⟩ row = true := hok
  simp only [WitnessGen.selfChecked?_eq, WitnessGen.generateWitness, hpr,
    Option.map_some, if_pos hok']
  rfl

/-- The check-face spelling of the same theorem (the bridge makes the
    two faces coincide — one citation each). -/
theorem WitnessGen.selfChecked?_of_check_true {fs : List Field}
    (label : String) (p : Pred fs) (row : RowVals fs)
    (hc : p.check row = true) :
    (WitnessGen.selfChecked? label p row).isSome = true :=
  WitnessGen.selfChecked?_of_sat label p row (p.check_sound row hc)

/-! ## The producer's soundness (no new trust base) -/

/-- The shipped certificate's facts: the claim IS the spec's (the
    generator's image — the claim is the parameter, never a re-run),
    and the in-process check ran true (the self-check's gate). -/
theorem WitnessGen.selfChecked?_facts {fs : List Field} (label : String)
    (p : Pred fs) (row : RowVals fs) (w : Witness fs)
    (h : WitnessGen.selfChecked? label p row = some w) :
    w.claim = p ∧ w.checks row = true := by
  rw [WitnessGen.selfChecked?_eq, WitnessGen.generateWitness] at h
  cases hpr : WitnessGen.proofFor p row with
  | none =>
      simp only [hpr] at h
      simp at h
  | some pr =>
      simp only [hpr, Option.map_some] at h
      by_cases hc : Witness.checks
          { label := label, claim := p, proof := pr
            fuel := WitnessGen.fuelPinned p } row = true
      · simp only [if_pos hc, Option.some.injEq] at h
        rw [← h]
        exact ⟨rfl, hc⟩
      · rw [if_neg hc] at h
        simp at h

/-- THE PRODUCER'S SOUNDNESS: a shipped certificate's claim is TRUE —
    the self-check refuses exactly what the checker refuses, so the
    producer adds NO trust beyond the checker's theorem
    (`Witness.checks_sound`). -/
theorem WitnessGen.selfChecked?_sound {fs : List Field} (label : String)
    (p : Pred fs) (row : RowVals fs) (w : Witness fs)
    (h : WitnessGen.selfChecked? label p row = some w) : w.claim.Sat row := by
  obtain ⟨hclaim, hchk⟩ := WitnessGen.selfChecked?_facts label p row w h
  exact w.checks_sound row hchk

/-- THE FALSE-CLAIM REFUSAL: the producer NEVER emits a certificate for
    a claim whose check fires false (the self-check's gate — a shipped
    certificate would have to pass `checkWitness`, and the landed
    checker's acceptance implies the claim's check, theorem-backed). -/
theorem WitnessGen.selfChecked?_none_of_check_false {fs : List Field}
    (label : String) (p : Pred fs) (row : RowVals fs)
    (hc : p.check row = false) : WitnessGen.selfChecked? label p row = none := by
  rw [WitnessGen.selfChecked?_eq, WitnessGen.generateWitness]
  cases hpr : WitnessGen.proofFor p row with
  | none => rfl
  | some pr =>
      simp only [Option.map_some]
      rw [if_neg (fun (habs : Witness.checks ⟨label, p, pr,
          WitnessGen.fuelPinned p⟩ row = true) =>
        absurd (checkWitness_check_true habs)
          (by rw [hc]; simp))]

/-! ## The producer's CheckedProp (the lane's first `.proved` rung) -/

/-- The producer's check face over the row carrier: the
    generated-and-self-checked witness's verdict. -/
def WitnessGen.producerCheck (label : String) (p : Pred fs)
    (row : RowVals fs) : Bool :=
  match WitnessGen.selfChecked? label p row with
  | some w => w.checks row
  | none => false

/-- THE PRODUCER'S CHECKED PROP: the check lane's claim as a
    `Kit.CheckedProp` whose checker is the PRODUCER's face — sound by
    `selfChecked?_sound`, COMPLETE by `selfChecked?_of_sat` (the
    `.proved` rung). The honesty note stands: the BARE checker's
    `witnessChecked` stays sound-only (a true claim under an
    under-sized cap refuses); completeness holds OF THE PRODUCER at
    ITS pinned fuel — the producer finds the witness a true claim
    needs. -/
def WitnessGen.producerChecked (label : String) (p : Pred fs) :
    Kit.CheckedProp (RowVals fs) where
  P := fun row => p.Sat row
  check := WitnessGen.producerCheck label p
  sound := by
    intro row h
    simp only [WitnessGen.producerCheck] at h
    split at h
    · next w hw =>
        obtain ⟨hclaim, hchk⟩ := WitnessGen.selfChecked?_facts label p row w hw
        rw [← hclaim]
        exact w.checks_sound row hchk
    · exact absurd h (by simp)
  complete? := .proved (fun row hs => by
    obtain ⟨w, he, hc'⟩ := WitnessGen.selfChecked?_checks label p row
      (WitnessGen.selfChecked?_of_sat label p row hs)
    simp only [WitnessGen.producerCheck, he]
    exact hc')

/-- The loud flag, pinned: the producer's face IS complete (the
    checker's stays `false` — `Witness.witnessChecked_incomplete`; the
    two flags together are the lane's honest division). -/
theorem WitnessGen.producerChecked_complete (label : String) (p : Pred fs) :
    (WitnessGen.producerChecked label p).isComplete = true := rfl

end SchemaCore
