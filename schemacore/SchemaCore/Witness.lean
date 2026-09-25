/-
# SchemaCore.Witness — the witness lane (the certificate pattern's first lane)

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/04-verification.md §3 (THE certificate
pattern: an untrusted producer generates a candidate + certificate; a
small verified checker validates — no duplicate semantic authority), §2
(the `guestVerified` tier — the fifth discharge tier, whose
`guestWitness` evidence lived in kit/Kit/Obligation.lean with ZERO
consumers until this lane), notes/v3/10-sequencing.md Phase 10 (the
portable verifier), notes/v3/15-patterns.md #3 (the pattern's canonical
instance IS the witness lane). Mined: `legacy/lean/schema-lang/
SchemaLang/Witness.lean` + `WitnessCheck.lean` (the proof-term syntax,
the fuel-bounded total checker, `checkWitness_sound`'s conditional-on-
acceptance shape) — ported FRESH over the landed substrate.

THE CLAIM LANGUAGE (the honest minimal): the check lane's OWN fragment
— a claim IS a `Pred fs` (SchemaCore.Pred: the field predicates —
u64/string equalities and bounds — plus `and`/`or`/`not`). The
connection is deliberate: `Pred` already carries the spec of record
(`Pred.Sat`), the decidable checker (`Pred.check`), and the PROVED
bridge (`Pred.check_iff`) — the witness lane re-uses all three and
adds the CERTIFICATE half: the proof-term syntax the producer ships,
and the fuel-bounded checker that validates it. No parallel claim
table (15-patterns: never a parallel table).

THE PROOF TERMS (`WProof`): the recorded evidence down the claim's
tree — an atomic's recorded verdict (`verdict`), a conjunction's two
children (`conj`), a disjunction's CHOSEN side (`disj`), a negation's
refutation record (`neg` — the inner check's `false` verdict, which
soundness rides through `check_complete`'s contrapositive). The
producer is untrusted: any term can be shipped; only accepting ones
certify.

THE CHECKER (`checkWitness`): fuel-bounded, total. Fuel 0 REFUSES
(exhaustion is a verdict, never a trap — the `Sem.exec` discipline);
every acceptance path forces the claim's own check to fire `true`
somewhere, so soundness needs no fuel in the conclusion:

    checkWitness fuel claim proof row = true → claim.Sat row

Monotonicity (`checkWitness_mono`): acceptance survives any larger cap
— a witness the host sized stays accepted; an under-sized cap refuses,
loudly, forever (the "never retries with more fuel" policy).

THE guestVerified DISCHARGE (the tier's FIRST consumer): the
obligation row's claim index is the claim's denotation
(`w.claim.Sat row`) at tier `.guestVerified`; the discharge fires the
kit's `guestWitness` evidence EXACTLY when the checker accepts, and
`Witness.discharge_sound` closes the loop — the evidence certifies the
claim, riding `checkWitness_sound`. The trust story, honestly: the
Lean-side checker's soundness is THE theorem (no new trust base); the
GUEST-COMPILED checker's agreement with it is NOT yet proved — see the
compile-ability judgment below.

THE GUEST-COMPILED CHECKER (the honest state): the op surface is
judged in `WasmCore.WitnessFragment` (every claim-language operation
has a lowering row, `or` via the named de Morgan gap). The CARRIER is
the boundary: the checker walks `RowVals fs` — a GADT indexed by the
field list — and resolves fields BY NAME against it; Guest.Lower's
scalar fragment (the closed type map + the boxed-Nat object model)
has no dependent-index objects, so a GADT row walk is exactly the
refusal class that lane names loudly. The honest first cut is
therefore the Lean-side checker + the duel discipline below; the
guest-compiled checker is the NAMED FOLLOW-UP (the lowering lands
when the object model carries the row carrier — Guest lane's order).

THE DUEL DISCIPLINE: the checker vs the claim's own check, tied at the
theorem level (`checks_iff_check`: an accepted witness certifies the
claim's check-true; a false claim's check-false refuses any witness) —
and pinned as rows in SchemaTests (the acceptance/refusal teeth).

THE WIRE (the codec): the witness data over the append-form atoms —
label and claim and proof and fuel, one tag byte per ctor in
DECLARATION ORDER, the tree decoders DEPTH-CAPPED (a tree grammar is
prefix-free, not byte-structural; entry fuel = bytes + 1, one byte per
node minimum — the legacy discipline verbatim). Round trips are the
append-form law per family, composed once at `decWitness?_encWitness`.
The version prefix is checked BEFORE the payload — a wrong version
refuses loudly (`decWitness?_wrong_version`).

Deliberately OUT (each names its reason — the leftover rule): the
chain/migration rule (the legacy `WProp.chain` — the slice holds no
journal; the event lane's log is the consumer it lands with); the
`strlen` atom (Pred has no strlen — the check lane's exclusion
stands); witness GENERATION (the producer side is untrusted by
construction — the tests hand-build witnesses, which is the point);
the exact-image inversion (the legacy Witness lane shipped the
append-form law only — the refusal teeth ride the tests).

The five questions (notes/v3/01-core.md): root = the witness lane
(certificates as data over the slice's values); carrier = the
proof-term tree + the fuel-bounded judgment (a wrong acceptance
unprovable — the soundness type); spine reading = the certificate
pattern's producer→checker→discharge flow (the obligation row is the
lane's output); ladder rung = the soundness bridge is the small hand
kind, written once, cited by the discharge (04 §1's rung 6; the
checker's verdicts are Bool, the CLAIM's truth rides the proved
bridge); gate row = SchemaTests' witness suites + the axiom report.

Core-only (imports SchemaCore.Pred + Kit.Obligation + Kit.Varint —
the cone rule).
-/

import SchemaCore.Pred
import SchemaCore.Check
import SchemaCore.Codec
import Kit.Obligation
import Kit.Varint

namespace SchemaCore

open Kit.Varint

/-! ## The proof terms (the certificate's syntax) -/

/-- The proof-term syntax — the certificate the untrusted producer
    ships. One ctor per calculus rule: an atomic's recorded verdict, a
    conjunction's two children, a disjunction's chosen side, a
    negation's refutation record. No `DecidableEq` (the tree defeats
    the handler; `BEq` suffices for the tests' pins). -/
inductive WProof where
  /-- An atomic claim's recorded verdict (the legacy `byEval`). -/
  | verdict (b : Bool)
  /-- A conjunction's children, both certified. -/
  | conj (left right : WProof)
  /-- A disjunction's CHOSEN side: `chosen = true` certifies the left
      disjunct, `false` the right. -/
  | disj (chosen : Bool) (side : WProof)
  /-- A negation's refutation record: the inner check's `false`
      verdict (the checker verifies the inner check ACTUALLY fired
      false — soundness rides `check_complete`'s contrapositive). -/
  | neg (inner : WProof)
deriving Repr, BEq

/-! ## THE CHECKER — fuel-bounded, total -/

/-- THE JUDGMENT: fuel-bounded, total; fuel 0 is REFUSAL (the cap IS
    the semantics, never a trap). The calculus:

    - any claim + `verdict b`: accept iff the claim's OWN check fires
      true AND the record agrees (the record's tamper tooth);
    - `and` + `conj`: both children certified (one fuel unit down);
    - `or` + `disj`: the chosen side certified;
    - `not` + `neg (verdict false)`: the inner check actually fired
      false (the refutation record verified, not trusted);
    - EVERY mismatched shape refuses (the catch-all — a proof term
      that does not fit the claim is not evidence).

    Acceptance implies the claim's denotation — `checkWitness_sound`. -/
def checkWitness : (fuel : Nat) → Pred fs → WProof → RowVals fs → Bool
  | 0, _, _, _ => false
  | _ + 1, p, .verdict b, row => p.check row && b
  | fuel + 1, .and p q, .conj pp pq, row =>
      checkWitness fuel p pp row && checkWitness fuel q pq row
  | fuel + 1, .or _ q, .disj false pq, row => checkWitness fuel q pq row
  | fuel + 1, .or p _, .disj true pp, row => checkWitness fuel p pp row
  | _ + 1, .not p, .neg (.verdict false), row => !(p.check row)
  | _, _, _, _ => false

/-! ## THE INVERSION KIT — the mismatch grid paid once -/

/-- THE INVERSION KIT (pattern 18's face b): acceptance at a proof-term
    ctor forces the claim's matching shape and hands back the
    sub-checks' truths. Each lemma is one `cases p` over the checker's
    table — the mismatch cells die on the catch-all refusal (the
    semantics), the real cell reads the checker's equation. The grid
    lives HERE, once; `checkWitness_sound`/`checkWitness_mono` (and
    every future theorem over this checker) run their REAL arms only,
    citing these. -/
theorem checkWitness_conj_inv {fs : List Field} {fuel : Nat}
    {p : Pred fs} {pp pq : WProof} {row : RowVals fs}
    (h : checkWitness (fuel + 1) p (.conj pp pq) row = true) :
    ∃ a b, p = .and a b ∧ checkWitness fuel a pp row = true
                         ∧ checkWitness fuel b pq row = true := by
  cases p with
  | and a b =>
      simp only [checkWitness, Bool.and_eq_true] at h
      exact ⟨a, b, rfl, h.1, h.2⟩
  | _ => simp [checkWitness] at h

/-- The disjunction's inversion: acceptance forces the `or` shape and
    routes on the CHOSEN side (the certificate's `chosen` bit is the
    routing, verified not trusted). -/
theorem checkWitness_disj_inv {fs : List Field} {fuel : Nat}
    {p : Pred fs} {c : Bool} {side : WProof} {row : RowVals fs}
    (h : checkWitness (fuel + 1) p (.disj c side) row = true) :
    ∃ a q, p = .or a q ∧
      ((c = true ∧ checkWitness fuel a side row = true)
        ∨ (c = false ∧ checkWitness fuel q side row = true)) := by
  cases p with
  | or a q =>
      cases c with
      | false => exact ⟨a, q, rfl, Or.inr ⟨rfl, h⟩⟩
      | true => exact ⟨a, q, rfl, Or.inl ⟨rfl, h⟩⟩
  | _ => simp [checkWitness] at h

/-- The negation's inversion: acceptance forces the `not` shape AND
    the refutation record's exact face (`inner = verdict false`) AND
    the inner check's actual falsity — the record verified, not
    trusted. -/
theorem checkWitness_neg_inv {fs : List Field} {fuel : Nat}
    {p : Pred fs} {inner : WProof} {row : RowVals fs}
    (h : checkWitness (fuel + 1) p (.neg inner) row = true) :
    ∃ a, p = .not a ∧ inner = .verdict false ∧ a.check row = false := by
  cases p with
  | not a =>
      cases inner with
      | verdict b =>
          cases b with
          | false =>
              simp only [checkWitness, Bool.not_eq_true'] at h
              exact ⟨a, rfl, rfl, h⟩
          | true => simp [checkWitness] at h
      | _ => simp [checkWitness] at h
  | _ => simp [checkWitness] at h

/-! ## SOUNDNESS — acceptance implies the claim -/

/-- THE SOUNDNESS THEOREM (the lane's deliverable): an accepting check
    implies the claim's denotation — conditional on ACCEPTANCE, so
    fuel never appears in the conclusion. One induction on the cap;
    the atomic/refutation cases route through `Pred.check_sound` and
    `Pred.check_complete`'s contrapositive — the check lane's bridge,
    cited, never re-proved. -/
theorem checkWitness_sound {fs : List Field} :
    ∀ (fuel : Nat) (p : Pred fs) (pr : WProof) (row : RowVals fs),
      checkWitness fuel p pr row = true → p.Sat row := by
  intro fuel
  induction fuel with
  | zero => intro p pr row h; simp [checkWitness] at h
  | succ f ih =>
      intro p pr row h
      cases pr with
      | verdict b =>
          simp only [checkWitness, Bool.and_eq_true] at h
          exact p.check_sound row h.1
      -- the mismatch grid collapses to the catch-all arm: a proof term
      -- of the wrong shape decodes to `false` (the check's table), and
      -- a `false = true` hypothesis closes any goal
      -- the real arms only — the mismatch grid rides the inversion
      -- kit (the grid paid once, above)
      | conj pp pq =>
          obtain ⟨a, b, rfl, h1, h2⟩ := checkWitness_conj_inv h
          exact ⟨ih a pp row h1, ih b pq row h2⟩
      | disj c side =>
          obtain ⟨a, q, rfl, hc | hc⟩ := checkWitness_disj_inv h
          · exact Or.inl (ih a side row hc.2)
          · exact Or.inr (ih q side row hc.2)
      | neg inner =>
          obtain ⟨a, rfl, rfl, hfalse⟩ := checkWitness_neg_inv h
          -- the refutation record VERIFIED: the inner check fired
          -- false; completeness' contrapositive
          exact fun hsat =>
            absurd (a.check_complete row hsat) (by rw [hfalse]; decide)

/-- The soundness's acceptance-side reading, in the shape the tests
    pin: an accepted witness certifies the claim's own check — the
    DUEL TIE (soundness + completeness composed, one citation each). -/
theorem checkWitness_check_true {fs : List Field} {fuel : Nat}
    {p : Pred fs} {pr : WProof} {row : RowVals fs}
    (h : checkWitness fuel p pr row = true) : p.check row = true :=
  p.check_complete row (checkWitness_sound fuel p pr row h)

/-! ## The fuel discipline -/

/-- Exhaustion IS refusal: fuel 0 rejects every claim/proof pair. -/
theorem checkWitness_zero {fs : List Field} (p : Pred fs) (pr : WProof)
    (row : RowVals fs) : checkWitness 0 p pr row = false := rfl

/-- Acceptance is monotone in the cap: a witness the host sized stays
    accepted at any larger cap (an under-sized cap refuses loudly, and
    the refusal is stable — never a wrong acceptance at ANY cap). -/
theorem checkWitness_mono {fs : List Field} :
    ∀ (p : Pred fs) (pr : WProof) (row : RowVals fs) {fuel fuel' : Nat},
      fuel ≤ fuel' → checkWitness fuel p pr row = true →
      checkWitness fuel' p pr row = true := by
  intro p pr row fuel
  induction fuel generalizing p pr row with
  | zero =>
      intro fuel' _ h
      simp [checkWitness] at h
  | succ f ih =>
      intro fuel' hle h
      cases fuel' with
      | zero => exact absurd hle (Nat.not_succ_le_zero f)
      | succ f' =>
          cases pr with
          | verdict b => exact h
          -- the mismatch grid collapses to the catch-all arm (as in
          -- `checkWitness_sound`)
          -- the real arms only (the inversion kit, as in soundness)
          | conj pp pq =>
              obtain ⟨a, b, rfl, h1, h2⟩ := checkWitness_conj_inv h
              simp only [checkWitness, Bool.and_eq_true]
              exact ⟨ih a pp row (Nat.succ_le_succ_iff.mp hle) h1,
                     ih b pq row (Nat.succ_le_succ_iff.mp hle) h2⟩
          | disj c side =>
              obtain ⟨a, q, rfl, hc | hc⟩ := checkWitness_disj_inv h
              · simp only [hc.1, checkWitness]
                exact ih a side row (Nat.succ_le_succ_iff.mp hle) hc.2
              · simp only [hc.1, checkWitness]
                exact ih q side row (Nat.succ_le_succ_iff.mp hle) hc.2
          | neg inner =>
              obtain ⟨a, rfl, rfl, _⟩ := checkWitness_neg_inv h
              exact h

/-! ## The certificate (the untrusted producer's artifact) -/

/-- THE CERTIFICATE (04 §3's shape): the claim, the proof term, and
    the checker's step cap (fuel is PART of the artifact — host and
    consumer agree by construction; a low cap refuses, it never
    lies). The claim rides the field list as the index — a witness for
    another schema's rows cannot be applied (the check lane's GADT
    discipline). -/
structure Witness (fs : List Field) where
  label : String
  claim : Pred fs
  proof : WProof
  fuel : Nat

/-- The checker at the certificate's own shipped cap. -/
def Witness.checks (w : Witness fs) (row : RowVals fs) : Bool :=
  checkWitness w.fuel w.claim w.proof row

/-- SOUNDNESS at the artifact level: an accepted certificate certifies
    the claim's denotation over the row (cites `checkWitness_sound`
    — never a re-proof). -/
theorem Witness.checks_sound (w : Witness fs) (row : RowVals fs)
    (h : w.checks row = true) : w.claim.Sat row :=
  checkWitness_sound w.fuel w.claim w.proof row h

/-- THE DUEL TIE (the theorem face): an accepted certificate certifies
    the claim's own check — soundness + completeness composed, one
    citation each. The duel's tested rows live in SchemaTests. -/
theorem Witness.checks_iff_check (w : Witness fs) (row : RowVals fs)
    (h : w.checks row = true) : w.claim.check row = true :=
  w.claim.check_complete row (w.checks_sound row h)

/-- The duel's negative face: a claim whose own check fires false
    refuses EVERY certificate (the contrapositive of the tie — a false
    claim has no witness, and the refusal is theorem-backed). -/
theorem Witness.check_false_refuses (w : Witness fs) (row : RowVals fs)
    (h : w.claim.check row = false) : w.checks row = false := by
  cases hc : w.checks row with
  | false => rfl
  | true => exact absurd (w.checks_iff_check row hc) (by rw [h]; decide)

/-! ## The guestVerified discharge (the tier's FIRST consumer) -/

/-- THE OBLIGATION ROW (15-patterns #4): the certificate's checkable
    fact as data — the label, the COMPUTED tier (`guestVerified`: the
    discharge's backend is the witness checker), the payload (the
    claim's read fields — the scope, the check lane's payload
    discipline), the provenance — and THE CLAIM AS THE TYPE INDEX:
    the row is `Obligation _ (w.claim.Sat row)`, so a discharge of
    this row can never prove a different proposition (the mis-wire
    rule's deepest promotion). -/
def Witness.obligation (w : Witness fs) (row : RowVals fs) :
    Kit.Obligation (List String) (w.claim.Sat row) :=
  { label := w.label
    tier := .guestVerified
    payload := w.claim.reads
    provenance := `SchemaCore.Witness }

/-- THE guestVerified DISCHARGE — the fifth tier's FIRST consumer (the
    `guestWitness` evidence in kit/Kit/Obligation.lean had zero
    consumers until this lane). Gated on the checker's acceptance: the
    witness artifact + the checker's acceptance IS the evidence —
    `none` is the loud gap (a refused witness or a mis-set tier; the
    backend refuses, it does not fabricate evidence). `artifact` is
    the byte-tied witness file; `ref` the obligation's label inside
    it (the kit evidence ctor's contract). -/
def Witness.discharge (w : Witness fs) (row : RowVals fs)
    (artifact ref : String) : Option Kit.Evidence :=
  if w.checks row then some (.guestWitness artifact ref) else none

/-- THE DISCHARGE'S SOUNDNESS: the `guestWitness` evidence certifies
    the obligation's OWN claim — the conclusion is the index
    (`w.claim.Sat row`), riding `checkWitness_sound`. The trust story,
    honestly stated: the Lean-side checker's soundness is this theorem
    (no new trust base); the guest-compiled checker's AGREEMENT with
    it is the named follow-up (see the module header's compile-ability
    judgment). -/
theorem Witness.discharge_sound (w : Witness fs) (row : RowVals fs)
    (artifact ref : String)
    (h : w.discharge row artifact ref = some (.guestWitness artifact ref)) :
    w.claim.Sat row := by
  simp only [discharge] at h
  split at h
  · next hc => exact w.checks_sound row hc
  · simp at h

/-- The discharge's completeness is DELIBERATELY absent: a true claim
    may have no shipped certificate (a low fuel cap or a missing proof
    term refuses) — the loud-missing `CheckedProp` below makes the
    gap DATA, not a comment (04 §2's honesty discipline). -/
def Witness.witnessChecked (w : Witness fs) : Kit.CheckedProp (RowVals fs) where
  P := fun row => w.claim.Sat row
  check := w.checks
  sound := w.checks_sound
  complete? := .missing

/-- The loud flag, pinned: this lane is sound-only. -/
theorem Witness.witnessChecked_incomplete (w : Witness fs) :
    w.witnessChecked.isComplete = false := rfl

/-! ## The wire — the append-form codec over the witness data

One tag byte per ctor in DECLARATION ORDER (the EnumWire rule's
reading: reordering is wire-breaking); children via the append-form
combinators; the tree decoders DEPTH-CAPPED (a tree grammar is
prefix-free, not byte-structural — fuel 0 is `none`, never a trap;
entry fuel = bytes + 1, one byte per node minimum). Round trips are
the append-form law per family (15-patterns #2), composed once at
`decWitness?_encWitness`. -/

/-! ### The claim's wire (`Pred fs` — fs-polymorphic: the tree does
     not branch on the field list) -/

/-- The claim's node depth (the decode-fuel need: one unit per node). -/
def Pred.depth : Pred fs → Nat
  | .lit _ => 1
  | .u64EqLit _ _ => 1
  | .u64GtLit _ _ => 1
  | .u64Eq _ _ => 1
  | .strEqLit _ _ => 1
  | .and p q => max p.depth q.depth + 1
  | .or p q => max p.depth q.depth + 1
  | .not p => p.depth + 1

/-- The claim's encoder. Tags 0..7 in `Pred`'s ctor order: lit,
    u64EqLit, u64GtLit, u64Eq, strEqLit, and, or, not. -/
def encPred : Pred fs → List UInt8
  | .lit b => 0 :: encBool b
  | .u64EqLit n v => 1 :: encList encChar n.toList ++ encVarNat v.toNat
  | .u64GtLit n v => 2 :: encList encChar n.toList ++ encVarNat v.toNat
  | .u64Eq a b => 3 :: encList encChar a.toList ++ encList encChar b.toList
  | .strEqLit n s => 4 :: encList encChar n.toList ++ encList encChar s.toList
  | .and p q => 5 :: encPred p ++ encPred q
  | .or p q => 6 :: encPred p ++ encPred q
  | .not p => 7 :: encPred p

/-- The claim's depth-capped decoder. Unknown tags, truncation, and
    fuel exhaustion refuse (`none`) — loud, never a silent misparse. -/
def decPredF? : (fuel : Nat) → List UInt8 → Option (Pred fs × List UInt8)
  | 0, _ => none
  | fuel + 1, bs =>
      match decByte? bs with
      | some (0, r) => (decBool? r).map fun (b, r') => (.lit b, r')
      | some (1, r) =>
          (decStringraw? r).bind fun (n, r1) =>
          (decU64raw? r1).map fun (v, r2) => (.u64EqLit n v, r2)
      | some (2, r) =>
          (decStringraw? r).bind fun (n, r1) =>
          (decU64raw? r1).map fun (v, r2) => (.u64GtLit n v, r2)
      | some (3, r) =>
          (decStringraw? r).bind fun (a, r1) =>
          (decStringraw? r1).map fun (b, r2) => (.u64Eq a b, r2)
      | some (4, r) =>
          (decStringraw? r).bind fun (n, r1) =>
          (decStringraw? r1).map fun (s, r2) => (.strEqLit n s, r2)
      | some (5, r) =>
          (decPredF? fuel r).bind fun (p, r1) =>
          (decPredF? fuel r1).map fun (q, r2) => (.and p q, r2)
      | some (6, r) =>
          (decPredF? fuel r).bind fun (p, r1) =>
          (decPredF? fuel r1).map fun (q, r2) => (.or p q, r2)
      | some (7, r) => (decPredF? fuel r).map fun (p, r') => (.not p, r')
      | _ => none

/-- THE CLAIM'S ROUND TRIP at depth, append form. -/
theorem decPredF_encPred_append (p : Pred fs) :
    ∀ (rest : List UInt8) (fuel : Nat), p.depth ≤ fuel →
      decPredF? fuel (encPred p ++ rest) = some (p, rest) := by
  induction p with
  | lit b =>
      intro rest fuel h
      have hf : 0 < fuel := by
        simp only [Pred.depth] at h; omega
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encPred, List.cons_append, decPredF?, decByte?_cons,
        decBool?_encBool_append, Option.map_some]
  | u64EqLit n v =>
      intro rest fuel h
      have hf : 0 < fuel := by
        simp only [Pred.depth] at h; omega
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encPred, List.cons_append, List.append_assoc, decPredF?,
        decByte?_cons, decStringraw?_append, decU64raw?_append,
        Option.bind_some, Option.map_some]
  | u64GtLit n v =>
      intro rest fuel h
      have hf : 0 < fuel := by
        simp only [Pred.depth] at h; omega
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encPred, List.cons_append, List.append_assoc, decPredF?,
        decByte?_cons, decStringraw?_append, decU64raw?_append,
        Option.bind_some, Option.map_some]
  | u64Eq a b =>
      intro rest fuel h
      have hf : 0 < fuel := by
        simp only [Pred.depth] at h; omega
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encPred, List.cons_append, List.append_assoc, decPredF?,
        decByte?_cons, decStringraw?_append, Option.bind_some, Option.map_some]
  | strEqLit n s =>
      intro rest fuel h
      have hf : 0 < fuel := by
        simp only [Pred.depth] at h; omega
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encPred, List.cons_append, List.append_assoc, decPredF?,
        decByte?_cons, decStringraw?_append, Option.bind_some, Option.map_some]
  | and p q ihp ihq =>
      intro rest fuel h
      simp only [Pred.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hp : p.depth ≤ f := by omega
      have hq : q.depth ≤ f := by omega
      simp only [encPred, List.cons_append, List.append_assoc, decPredF?,
        decByte?_cons]
      rw [ihp (encPred q ++ rest) f hp]
      simp only [Option.bind_some]
      rw [ihq rest f hq]
      simp
  | or p q ihp ihq =>
      intro rest fuel h
      simp only [Pred.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hp : p.depth ≤ f := by omega
      have hq : q.depth ≤ f := by omega
      simp only [encPred, List.cons_append, List.append_assoc, decPredF?,
        decByte?_cons]
      rw [ihp (encPred q ++ rest) f hp]
      simp only [Option.bind_some]
      rw [ihq rest f hq]
      simp
  | not p ihp =>
      intro rest fuel h
      simp only [Pred.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hp : p.depth ≤ f := by omega
      simp only [encPred, List.cons_append, decPredF?, decByte?_cons]
      rw [ihp rest f hp]
      simp

/-- Every claim node emits at least one byte (its tag), so the entry
    fuel `bytes + 1` always covers the depth. -/
theorem Pred.depth_le_length_enc (p : Pred fs) : p.depth ≤ (encPred p).length := by
  induction p with
  | lit b =>
      show 1 ≤ (encPred (.lit b)).length
      rw [show encPred (.lit b) = 0 :: encBool b from rfl, List.length_cons]
      omega
  | u64EqLit n v =>
      show 1 ≤ (encPred (.u64EqLit n v)).length
      rw [show encPred (.u64EqLit n v)
            = 1 :: (encList encChar n.toList ++ encVarNat v.toNat) from rfl,
        List.length_cons, List.length_append]
      omega
  | u64GtLit n v =>
      show 1 ≤ (encPred (.u64GtLit n v)).length
      rw [show encPred (.u64GtLit n v)
            = 2 :: (encList encChar n.toList ++ encVarNat v.toNat) from rfl,
        List.length_cons, List.length_append]
      omega
  | u64Eq a b =>
      show 1 ≤ (encPred (.u64Eq a b)).length
      rw [show encPred (.u64Eq a b)
            = 3 :: (encList encChar a.toList ++ encList encChar b.toList) from rfl,
        List.length_cons, List.length_append]
      omega
  | strEqLit n s =>
      show 1 ≤ (encPred (.strEqLit n s)).length
      rw [show encPred (.strEqLit n s)
            = 4 :: (encList encChar n.toList ++ encList encChar s.toList) from rfl,
        List.length_cons, List.length_append]
      omega
  | and p q ihp ihq =>
      show max p.depth q.depth + 1 ≤ (encPred (.and p q)).length
      rw [show encPred (.and p q) = 5 :: (encPred p ++ encPred q) from rfl,
        List.length_cons, List.length_append]
      omega
  | or p q ihp ihq =>
      show max p.depth q.depth + 1 ≤ (encPred (.or p q)).length
      rw [show encPred (.or p q) = 6 :: (encPred p ++ encPred q) from rfl,
        List.length_cons, List.length_append]
      omega
  | not p ihp =>
      show p.depth + 1 ≤ (encPred (.not p)).length
      rw [show encPred (.not p) = 7 :: encPred p from rfl, List.length_cons]
      omega

/-- The claim's entry-point decoder. -/
def decPred? (bs : List UInt8) : Option (Pred fs × List UInt8) :=
  decPredF? (bs.length + 1) bs

/-- THE CLAIM'S ROUND TRIP at the entry point, append form. -/
theorem decPred_encPred_append (p : Pred fs) (rest : List UInt8) :
    decPred? (encPred p ++ rest) = some (p, rest) := by
  show decPredF? ((encPred p ++ rest).length + 1) _ = _
  apply decPredF_encPred_append
  have h := p.depth_le_length_enc
  simp [List.length_append]; omega

/-! ### The proof terms' wire -/

/-- The proof term's node depth (the decode-fuel need). -/
def WProof.depth : WProof → Nat
  | .verdict _ => 1
  | .conj a b => max a.depth b.depth + 1
  | .disj _ a => a.depth + 1
  | .neg a => a.depth + 1

/-- The proof term's encoder. Tags 0..3 in `WProof`'s ctor order:
    verdict, conj, disj, neg. -/
def encWProof : WProof → List UInt8
  | .verdict b => 0 :: encBool b
  | .conj a b => 1 :: encWProof a ++ encWProof b
  | .disj c a => 2 :: encBool c ++ encWProof a
  | .neg a => 3 :: encWProof a

/-- The proof term's depth-capped decoder. -/
def decWProofF? : (fuel : Nat) → List UInt8 → Option (WProof × List UInt8)
  | 0, _ => none
  | fuel + 1, bs =>
      match decByte? bs with
      | some (0, r) => (decBool? r).map fun (b, r') => (.verdict b, r')
      | some (1, r) =>
          (decWProofF? fuel r).bind fun (a, r1) =>
          (decWProofF? fuel r1).map fun (b, r2) => (.conj a b, r2)
      | some (2, r) =>
          (decBool? r).bind fun (c, r1) =>
          (decWProofF? fuel r1).map fun (a, r2) => (.disj c a, r2)
      | some (3, r) => (decWProofF? fuel r).map fun (a, r') => (.neg a, r')
      | _ => none

/-- THE PROOF TERM'S ROUND TRIP at depth, append form. -/
theorem decWProofF_encWProof_append (p : WProof) :
    ∀ (rest : List UInt8) (fuel : Nat), p.depth ≤ fuel →
      decWProofF? fuel (encWProof p ++ rest) = some (p, rest) := by
  induction p with
  | verdict b =>
      intro rest fuel h
      have hf : 0 < fuel := by
        simp only [WProof.depth] at h; omega
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encWProof, List.cons_append, decWProofF?, decByte?_cons,
        decBool?_encBool_append, Option.map_some]
  | conj a b iha ihb =>
      intro rest fuel h
      simp only [WProof.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have ha : a.depth ≤ f := by omega
      have hb : b.depth ≤ f := by omega
      simp only [encWProof, List.cons_append, List.append_assoc, decWProofF?,
        decByte?_cons]
      rw [iha (encWProof b ++ rest) f ha]
      simp only [Option.bind_some]
      rw [ihb rest f hb]
      simp
  | disj c a iha =>
      intro rest fuel h
      simp only [WProof.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have ha : a.depth ≤ f := by omega
      simp only [encWProof, List.cons_append, List.append_assoc, decWProofF?,
        decByte?_cons, decBool?_encBool_append, Option.bind_some]
      rw [iha rest f ha]
      simp
  | neg a iha =>
      intro rest fuel h
      simp only [WProof.depth] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have ha : a.depth ≤ f := by omega
      simp only [encWProof, List.cons_append, decWProofF?, decByte?_cons]
      rw [iha rest f ha]
      simp

/-- Every proof node emits at least one byte (its tag), so the entry
    fuel `bytes + 1` always covers the depth. -/
theorem WProof.depth_le_length_enc (p : WProof) : p.depth ≤ (encWProof p).length := by
  induction p with
  | verdict b =>
      show 1 ≤ (encWProof (.verdict b)).length
      rw [show encWProof (.verdict b) = 0 :: encBool b from rfl, List.length_cons]
      omega
  | conj a b iha ihb =>
      show max a.depth b.depth + 1 ≤ (encWProof (.conj a b)).length
      rw [show encWProof (.conj a b) = 1 :: (encWProof a ++ encWProof b) from rfl,
        List.length_cons, List.length_append]
      omega
  | disj c a iha =>
      show a.depth + 1 ≤ (encWProof (.disj c a)).length
      rw [show encWProof (.disj c a) = 2 :: (encBool c ++ encWProof a) from rfl,
        List.length_cons, List.length_append]
      omega
  | neg a iha =>
      show a.depth + 1 ≤ (encWProof (.neg a)).length
      rw [show encWProof (.neg a) = 3 :: encWProof a from rfl, List.length_cons]
      omega

/-- The proof term's entry-point decoder. -/
def decWProof? (bs : List UInt8) : Option (WProof × List UInt8) :=
  decWProofF? (bs.length + 1) bs

/-- THE PROOF TERM'S ROUND TRIP at the entry point, append form. -/
theorem decWProof_encWProof_append (p : WProof) (rest : List UInt8) :
    decWProof? (encWProof p ++ rest) = some (p, rest) := by
  show decWProofF? ((encWProof p ++ rest).length + 1) _ = _
  apply decWProofF_encWProof_append
  have h := p.depth_le_length_enc
  simp [List.length_append]; omega

/-! ### The certificate's wire -/

/-- The witness encoding: the version prefix + the payload
    `label ++ claim ++ proof ++ fuel`. The version is checked BEFORE
    the payload (a wrong version refuses loudly — the tamper tooth). -/
def encWitness (version : Nat) (w : Witness fs) : List UInt8 :=
  encVarNat version ++ encList encChar w.label.toList ++ encPred w.claim ++
    encWProof w.proof ++ encVarNat w.fuel

/-- The whole-form decode: the version gate, then the payload's four
    fields; truncation and trailing garbage refuse (the payload ends
    exactly at the fuel varint — append-form all the way down). -/
def decWitness? (version : Nat) (bs : List UInt8) : Option (Witness fs × List UInt8) :=
  (decVarNat? bs).bind fun (v, r1) =>
    if v = version then
      (decStringraw? r1).bind fun (label, r2) =>
      (decPred? r2).bind fun (claim, r3) =>
      (decWProof? r3).bind fun (proof, r4) =>
      (decVarNat? r4).map fun (fuel, r5) =>
        (⟨label, claim, proof, fuel⟩, r5)
    else none

/-- THE WITNESS ROUND TRIP (the assembled law): every field's
    append-form lemma composed once. -/
theorem decWitness?_encWitness (version : Nat) (w : Witness fs) (rest : List UInt8) :
    decWitness? version (encWitness version w ++ rest) = some (w, rest) := by
  obtain ⟨label, claim, proof, fuel⟩ := w
  simp only [encWitness, List.append_assoc, decWitness?,
    decVarNat?_encVarNat_append, if_true, decStringraw?_append,
    decPred_encPred_append, decWProof_encWProof_append, Option.bind_some,
    Option.map_some]

/-- THE VERSION GATE (the tamper tooth, theorem-backed): a decoder at
    any other version refuses — the wire's consumers pin their version,
    and a mismatch is a refusal, never a silent misparse. -/
theorem decWitness?_wrong_version (version : Nat) (w : Witness fs) (rest : List UInt8) :
    decWitness? (fs := fs) (version + 1) (encWitness version w ++ rest) = none := by
  simp only [encWitness, List.append_assoc, decWitness?,
    decVarNat?_encVarNat_append, Option.bind_some,
    if_neg (show ¬ ((version : Nat) = version + 1) from by omega)]

/-! ## The coverage pins (the wire reduces — kernel-visible) -/

-- the atomic claim's bytes: tag + bool
example : encPred (fs := []) (.lit true) = [0, 1] := rfl
-- the u64 claim's bytes: tag + the varint column name + the varint value
example : encPred (fs := []) (.u64EqLit "n" 300) = [1, 1, 110, 0xAC, 0x02] := rfl
-- the proof term's bytes: tag + bool
example : encWProof (.verdict false) = [0, 0] := rfl
-- a compound claim round-trips at the entry point, append form
example : decPred? (fs := [])
    (encPred (fs := []) (.and (.lit true) (.lit false)) ++ [9])
    = some (.and (.lit true) (.lit false), [9]) := by
  simp [decPred_encPred_append]
-- a truncated tree refuses (the depth cap bites before the lie)
example : decWProof? [1] = none := rfl
-- an unknown tag refuses
example : decWProof? [9] = none := rfl
-- the wrong version refuses (the theorem, at the kernel)
example : decWitness? (fs := []) 1
    (encWitness (fs := []) 0 ⟨"", .lit true, .verdict true, 1⟩ ++ []) = none :=
  decWitness?_wrong_version 0 ⟨"", .lit true, .verdict true, 1⟩ []
