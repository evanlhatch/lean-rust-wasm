/-
# SchemaLang.WitnessCheck — the guest proof checker + its soundness (W9.2)

The fifth tier's checker (notes/design-guest-verified.md §2.2–2.4): a
fuel-bounded, total function over W9.1's proof-term syntax (`WProof`),
checking the v1 calculus — VExpr-`.bool` invariants (`valid`), raw-u64
equalities (`eqU`), and the migration-chain rule (`chain`) — ONLY those
(owner decision 4). The heart is `checkWitness_sound`:

    checkWitness fuel claim proof fs row log = true → WHolds claim row log

— acceptance implies the claim's denotation, conditional on acceptance
(the doc's honest shape: fuel exhaustion = REFUSAL, §7.3, so soundness
never mentions fuel). The fuel discipline is pinned separately
(`checkWitness_mono`: acceptance is monotone in the cap — the
substrait `parseType_mono` / wasm-backend fuel-insensitive precedent).

## Deviations from the design doc (each with its reason)

1. **`RowValsP` lands HERE, not in W9.1** (the doc §2.3 marked it
   "proposed here, defined in W9.1"; W9.1 shipped data + codec only).
   It is defined at its consumer, EXTENDED with the chain lane's log
   segment: the doc's sketch signature (`checkWitness fuel claim proof
   RowValsP`) has no log, but the chain rule is meaningless without the
   journal the guest holds (§4: "the guest walks the log it already
   has"). `RowValsP` = the decoded field list + the row being certified
   + the log segment AT THE SAME field list.
2. **Fuel is a node+STEP cap, decremented per chain step** (the doc's
   "step cap", §2.3/§7.3): the rule node costs 1, each checked chain
   step costs 1. The mirror EVALUATORS are fuel-free — total structural
   functions (§2.2 rule 1: fuel is instrumentation over a total
   semantics; exhaustion is a verdict, never a trap — the `Sem.exec`
   discipline). v1 acceptance needs `fuel ≥ 1 + steps.length`.
3. **Per-step chain proofs are `byValidEval` EXACTLY.** The doc's rule 3
   recurses the full judgment per step ("each ps[i] certifies
   preservation across steps[i]"), but the per-step claim is always
   `.valid inv` — whose ONLY matching proof ctor is `byValidEval` — so
   the generic recursion collapses to an inline check with no
   expressiveness lost and no mutual recursion to justify. A richer
   per-step claim form is a NEW calculus rule (owner decision 4).
4. **`WHolds.chain` means: the invariant holds of the initial row AND
   of the log row at every referenced offset.** The "preservation
   across the migration" reading (old row satisfies inv → migrated row
   satisfies inv) is the CONSUMER's composition (W9.5's apply-gate over
   the replay fold), not a checker rule — the v1 proof atoms can only
   certify evaluation facts.

## The guest discipline

`lookupU64?`/`lookupString?`/`evalWU64?`/`evalWBool?`/`checkSteps`/
`checkWitness`/`checkWitnessArtifact` were `@[guest_std]`-marked at
landing; the marks are REMOVED pending the backend wave
(notes/w9-6-guest-checker-audit.md's gap list: Nat-literal lowering,
fap, string intrinsics) — the marks put the checker in wasm-gen's
compile set, and the backend cannot lower it yet. The gate
mount (CodegenCore.GuestGate), not the census lint: elaboration fails
if the closure leaves the guestlang-std surface. The constants used:
match-only Nat (zero/succ fuel patterns, `Nat.beq` on lengths — Nat
ARITHMETIC stays banned), String BEq (std-legal), UInt64 ops, List
walks, and `string_len` — the ONE strlen definition, whose compiled
callers resolve to the spliced runtime primitive (the evalRaw
precedent; Validate.lean's header).

## The semantic grounding (design §2.4's "stated against Denotes/evalV")

`WHolds` is stated against the MIRROR's own evaluators (the witness's
semantic function — the guest has no GADT to denote into). The tie to
the compiled reading is proved separately: `WUMirror`/`WBMirror`
relate a mirror term to the `VExpr` it reflects, and
`evalWU64?_eq_evalU`/`evalWBool?_eq_evalB` prove the readings agree
UNDER FIELD-NAME UNIQUENESS (name-based lookup ≡ path-based
extraction — the `(fs.map Field.name).Nodup` hypothesis is exactly
`universeCheck`'s uniqueness clause; the WellFormed link).
`WHolds.valid_iff_validates` is the bridge the consumer cites: a
checked `valid` witness ⟺ the compiled `validates` accepts.

Completeness: `complete? := .missing`, LOUD (the doc's v1 call — a low
shipped fuel rejects true claims; the gate is one-directional by
design, not by accident).

W9.5 additions (the consumer half): `verifyWitness` — THE function
boundary the consumption side calls (design §4 step 3); W9.6 swaps the
callee for the wasm-compiled checker and every call site survives
untouched — with its soundness-cited wrapper `verifyWitness_sound`;
and the fuel-classifier lemmas (`fuelNeed`, `checkSteps_fuel_sufficient`,
`checkWitness_fuel_sufficient`, `checkSteps_eq_false_of_fuel_lt`,
`checkWitness_eq_false_of_fuel_lt`) that make the apply-gate's two
refusal classes EXACT: below `fuelNeed` the check always refuses
(exhaustion = refusal, §7.3), at/above it the verdict is fuel-free
(the "never retries with more fuel" policy is a theorem, not a
comment).

Deliberate exclusions: the fifth tier's Kit/Invariant wiring (W9.3),
witness GENERATION (W9.4), the wasm compile (W9.6 — if the checker's
closure trips a backend `unsupported`, that is a BACKEND finding; this
module does not shrink the calculus to fit it).
-/

module

public import SchemaLang.Witness
public import SchemaLang.Validate
public import CodegenCore.GuestGate

@[expose] public section

namespace SchemaLang.WitnessCheck

open SchemaLang.Witness

/-! ## The mirror evaluators (the guest lane — `@[guest_std]`-gated)

Name-based field lookup over the decoded row (the wire carries NAMES;
the guest resolves them against the record's decoded field list). The
box match is `match h : f.ty with` + `h ▸ v` — matching `Value f.ty`
at an ABSTRACT `f.ty` does not elaborate (the index is a variable),
and splitting the tag in the LHS pattern makes the catch-all's
equation CONDITIONAL (a negative HEq side condition simp cannot
discharge); the equality-refined scrutinee compiles to ONE clean
equation (verified against the equation lemmas). The cast is
proof-irrelevant — identity at runtime. First-hit on duplicate names,
and a wrong-typed name-hit is `none`, not a skip — loud; the tie
theorems carry the uniqueness hypothesis (the header). -/

/-- The first `u64` field named `n`, unboxed. -/
def lookupU64? (n : String) : (fs : List Field) → RowVals fs → Option UInt64
  | [], _ => none
  | f :: fs, .cons v vs =>
      if f.name == n then
        match h : f.ty with
        | .u64 => some (match h ▸ v with | .u64 x => x)
        | _ => none
      else lookupU64? n fs vs

/-- The first `string` field named `n` (the `strlenCol` operand). -/
def lookupString? (n : String) : (fs : List Field) → RowVals fs → Option String
  | [], _ => none
  | f :: fs, .cons v vs =>
      if f.name == n then
        match h : f.ty with
        | .string => some (match h ▸ v with | .string s => s)
        | _ => none
      else lookupString? n fs vs

/-- The mirror's u64 reading — one-for-one with the `.u64`-valued
    fragment of `evalRaw`: literal, u64 column, string column's raw
    length via `string_len` (THE one definition — W6.10's dedup). -/
def evalWU64? : WU64 → (fs : List Field) → RowVals fs → Option UInt64
  | .lit v, _, _ => some v
  | .col n, fs, row => lookupU64? n fs row
  | .strlenCol n, fs, row => (lookupString? n fs row).map string_len

/-- The mirror's bool reading — the 0/1 u64, arm-for-arm `evalRaw`'s
    `.bool` slice (`gt`/`eq` via `boolToU64`, `and` = the 0/1
    multiplication, `not` = `1 - x`). Any unresolved operand is `none`
    — refusal, not the 0-analog: the CHECKER is not the validator's
    totalized reading, it is a gate. -/
def evalWBool? : WBoolExpr → (fs : List Field) → RowVals fs → Option UInt64
  | .gt a b, fs, row =>
      match evalWU64? a fs row, evalWU64? b fs row with
      | some x, some y => some (boolToU64 (x > y))
      | _, _ => none
  | .eq a b, fs, row =>
      match evalWU64? a fs row, evalWU64? b fs row with
      | some x, some y => some (boolToU64 (x == y))
      | _, _ => none
  | .and a b, fs, row =>
      match evalWBool? a fs row, evalWBool? b fs row with
      | some x, some y => some (x * y)
      | _, _ => none
  | .not a, fs, row =>
      match evalWBool? a fs row with
      | some x => some (1 - x)
      | none => none

/-! ## The checker (design §2.2–2.3) -/

/-- One chain step's proof verdict (hoisted so the walker's soundness
    proof destructs a FLAT def, not a nested match): v1's per-step claim
    is always `.valid inv`, whose only proof ctor is `byValidEval`
    (deviation 3) — anything else refuses. -/
def checkStepProof (p : WProof) (inv : WBoolExpr) (fs : List Field)
    (row : RowVals fs) : Bool :=
  match p with
  | .byValidEval => evalWBool? inv fs row == some 1
  | _ => false

/-- The chain lane's per-step walk: one fuel unit per step (the header's
    deviation 2), each step's offset dereferenced against the guest-held
    log. Length mismatch, out-of-range offset, wrong proof shape, out of
    fuel — all `false`: refusal is total. -/
def checkSteps : (fuel : Nat) → List WStep → List WProof → WBoolExpr →
    (fs : List Field) → List (RowVals fs) → Bool
  | _, [], [], _, _, _ => true
  | fuel + 1, s :: ss, p :: ps, inv, fs, log =>
      (match log[s.offset]? with
       | none => false
       | some r => checkStepProof p inv fs r) &&
        checkSteps fuel ss ps inv fs log
  | _, _, _, _, _, _ => false

/-- THE JUDGMENT (design §2.2's one judgment form). Structural on the
    fuel with the proof-shape dispatch at each rule:

    - `evalValid`: `valid e` accepts `byValidEval` when the row fold
      evaluates to 1 (the `validates` reading, computed guest-side).
    - `evalEq`: `eqU a b` accepts `byEval v` when both sides evaluate
      to `v` (the evaluators are TOTAL — "returns v within the cap" is
      instrumentation, §2.2 rule 1).
    - `chain`: `chain steps inv` accepts `steps ps` when the lengths
      match, the invariant holds of the initial row, and each step
      checks against the log (deviation 4's semantics).

    Fuel 0 is refusal (the cap IS the semantics, §7.3 — never a trap). -/
def checkWitness : (fuel : Nat) → WProp → WProof →
    (fs : List Field) → RowVals fs → List (RowVals fs) → Bool
  | 0, _, _, _, _, _ => false
  | _ + 1, .valid e, .byValidEval, fs, row, _ =>
      evalWBool? e fs row == some 1
  | _ + 1, .eqU a b, .byEval v, fs, row, _ =>
      (evalWU64? a fs row == some v) && (evalWU64? b fs row == some v)
  | fuel + 1, .chain steps inv, .steps ps, fs, row, log =>
      (steps.length == ps.length) && (evalWBool? inv fs row == some 1) &&
        checkSteps fuel steps ps inv fs log
  | _, _, _, _, _, _ => false

/-- The decoded context (design §2.3's `RowValsP` — landed here, see the
    header's deviation 1): the record's decoded field list, the row the
    claim is certified against, and the chain lane's log segment at the
    SAME list (offsets into it are meaningless across schemas). -/
structure RowValsP where
  fs : List Field
  row : RowVals fs
  log : List (RowVals fs)

/-- The artifact-level entry (the §4 consumer flow's check): fuel,
    claim and proof from the certificate itself — fuel is PART of the
    artifact (§7.3), so host and guest agree by construction. -/
def checkWitnessArtifact (w : Witness) (ctx : RowValsP) : Bool :=
  checkWitness w.fuel w.claim w.proof ctx.fs ctx.row ctx.log

/-! ## The reasoning authority (design §2.4 — the Wf.lean template) -/

/-- THE CLAIM'S MEANING: the denotation a checked witness certifies.
    Proof-agnostic (the proof term is evidence, not content); stated
    against the mirror's evaluators (the witness's semantic function),
    with the `evalV`/`validates` grounding proved below as the tie. -/
inductive WHolds {fs : List Field} : WProp → RowVals fs → List (RowVals fs) → Prop where
  /-- `valid e`: the row's fold evaluates to 1. -/
  | valid {e : WBoolExpr} {row : RowVals fs} {log : List (RowVals fs)} :
      evalWBool? e fs row = some 1 → WHolds (.valid e) row log
  /-- `eqU a b`: both sides evaluate, to the same value. -/
  | eqU {a b : WU64} {v : UInt64} {row : RowVals fs} {log : List (RowVals fs)} :
      evalWU64? a fs row = some v → evalWU64? b fs row = some v →
      WHolds (.eqU a b) row log
  /-- `chain steps inv`: the invariant holds of the initial row AND of
      the log row at every referenced offset (deviation 4). -/
  | chain {steps : List WStep} {inv : WBoolExpr} {row : RowVals fs}
      {log : List (RowVals fs)} :
      evalWBool? inv fs row = some 1 →
      (∀ s, s ∈ steps → ∃ r, log[s.offset]? = some r ∧ evalWBool? inv fs r = some 1) →
      WHolds (.chain steps inv) row log

/-! ## Soundness (the deliverable) -/

/-- An accepting step proof certifies the invariant's fold at the
    step's row (the wrong proof shapes refuse, definitionally). -/
theorem checkStepProof_eq_true {fs : List Field} {p : WProof} {inv : WBoolExpr}
    {row : RowVals fs} (h : checkStepProof p inv fs row = true) :
    evalWBool? inv fs row = some 1 := by
  cases p with
  | byEval v => simp [checkStepProof] at h
  | byValidEval => simp only [checkStepProof] at h; exact beq_iff_eq.mp h
  | steps qs => simp [checkStepProof] at h

/-- The per-step walk's soundness: acceptance at any fuel implies every
    referenced offset resolves and the invariant holds there. -/
theorem checkSteps_sound {fs : List Field} (steps : List WStep) :
    ∀ (fuel : Nat) (ps : List WProof) (inv : WBoolExpr) (log : List (RowVals fs)),
      checkSteps fuel steps ps inv fs log = true →
      ∀ s, s ∈ steps → ∃ r, log[s.offset]? = some r ∧ evalWBool? inv fs r = some 1 := by
  induction steps with
  | nil => intro fuel ps inv log h s hs; cases hs
  | cons st sts ih =>
      intro fuel ps inv log h s hs
      cases ps with
      | nil => simp [checkSteps] at h
      | cons p ps' =>
          cases fuel with
          | zero => simp [checkSteps] at h
          | succ f =>
              simp only [checkSteps] at h
              rw [Bool.and_eq_true] at h
              obtain ⟨hstep, hrest⟩ := h
              cases hs with
              | head =>
                  split at hstep
                  · simp at hstep
                  · rename_i r hget
                    exact ⟨r, hget, checkStepProof_eq_true hstep⟩
              | tail _ hs' => exact ih f ps' inv log hrest s hs'

/-- THE SOUNDNESS THEOREM (design §2.4): an accepting check implies the
    claim's denotation — conditional on ACCEPTANCE, so fuel never
    appears in the conclusion (the honest shape; §7.3's exhaustion =
    refusal is the `false` direction, pinned in Tests). -/
theorem checkWitness_sound {fs : List Field} (fuel : Nat) (claim : WProp) (proof : WProof)
    (row : RowVals fs) (log : List (RowVals fs))
    (h : checkWitness fuel claim proof fs row log = true) :
    WHolds claim row log := by
  cases fuel with
  | zero => cases claim <;> cases proof <;> simp [checkWitness] at h
  | succ f =>
      cases claim with
      | valid e =>
          cases proof with
          | byEval v => simp [checkWitness] at h
          | byValidEval =>
              simp only [checkWitness] at h
              exact WHolds.valid (beq_iff_eq.mp h)
          | steps ps => simp [checkWitness] at h
      | eqU a b =>
          cases proof with
          | byEval v =>
              simp only [checkWitness] at h
              rw [Bool.and_eq_true] at h
              exact WHolds.eqU (beq_iff_eq.mp h.1) (beq_iff_eq.mp h.2)
          | byValidEval => simp [checkWitness] at h
          | steps ps => simp [checkWitness] at h
      | chain steps inv =>
          cases proof with
          | byEval v => simp [checkWitness] at h
          | byValidEval => simp [checkWitness] at h
          | steps ps =>
              simp only [checkWitness] at h
              rw [Bool.and_eq_true, Bool.and_eq_true] at h
              obtain ⟨⟨_hlen, hinit⟩, hsteps⟩ := h
              exact WHolds.chain (beq_iff_eq.mp hinit)
                (checkSteps_sound steps f ps inv log hsteps)

/-- The artifact-level form (the order's headline): checking the
    certificate at its own shipped fuel implies the claim's
    denotation over the decoded context. -/
theorem checkWitnessArtifact_sound (w : Witness) (ctx : RowValsP)
    (h : checkWitnessArtifact w ctx = true) : WHolds w.claim ctx.row ctx.log :=
  checkWitness_sound w.fuel w.claim w.proof ctx.row ctx.log h

/-! ## The fuel discipline (the substrait `parseType_mono` precedent) -/

/-- Exhaustion IS refusal: fuel 0 rejects every claim/proof pair. -/
theorem checkWitness_zero {fs : List Field} (claim : WProp) (proof : WProof)
    (row : RowVals fs) (log : List (RowVals fs)) :
    checkWitness 0 claim proof fs row log = false := by
  cases claim <;> cases proof <;> simp [checkWitness]

/-- The per-step walk is monotone in the cap. -/
theorem checkSteps_mono {fs : List Field} (steps : List WStep) :
    ∀ {fuel fuel' : Nat} (ps : List WProof) (inv : WBoolExpr)
      (log : List (RowVals fs)),
      fuel ≤ fuel' → checkSteps fuel steps ps inv fs log = true →
      checkSteps fuel' steps ps inv fs log = true := by
  induction steps with
  | nil =>
      intro fuel fuel' ps inv log hle h
      cases ps with
      | nil => simp [checkSteps]
      | cons p ps' => simp [checkSteps] at h
  | cons st sts ih =>
      intro fuel fuel' ps inv log hle h
      cases ps with
      | nil => simp [checkSteps] at h
      | cons p ps' =>
          cases fuel with
          | zero => simp [checkSteps] at h
          | succ f =>
              cases fuel' with
              | zero => exact absurd hle (Nat.not_succ_le_zero f)
              | succ f' =>
                  have hle' : f ≤ f' := Nat.succ_le_succ_iff.mp hle
                  simp only [checkSteps] at h ⊢
                  rw [Bool.and_eq_true] at h ⊢
                  obtain ⟨hstep, hrest⟩ := h
                  exact ⟨hstep, ih ps' inv log hle' hrest⟩

/-- Acceptance is monotone in the fuel cap: a witness the host sized
    (§7.3's `consumed × 4`) stays accepted at any larger cap — the two
    runs (host self-check, guest check) can never disagree on fuel
    GROWTH, only on a cap set too low (which refuses, loudly). -/
theorem checkWitness_mono {fs : List Field} {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (claim : WProp) (proof : WProof) (row : RowVals fs) (log : List (RowVals fs))
    (h : checkWitness fuel claim proof fs row log = true) :
    checkWitness fuel' claim proof fs row log = true := by
  cases fuel with
  | zero => cases claim <;> cases proof <;> simp [checkWitness] at h
  | succ f =>
      cases fuel' with
      | zero => exact absurd hle (Nat.not_succ_le_zero f)
      | succ f' =>
          have hle' : f ≤ f' := Nat.succ_le_succ_iff.mp hle
          cases claim with
          | valid e =>
              cases proof with
              | byEval v => simp [checkWitness] at h
              | byValidEval => simp only [checkWitness] at h ⊢; exact h
              | steps ps => simp [checkWitness] at h
          | eqU a b =>
              cases proof with
              | byEval v => simp only [checkWitness] at h ⊢; exact h
              | byValidEval => simp [checkWitness] at h
              | steps ps => simp [checkWitness] at h
          | chain steps inv =>
              cases proof with
              | byEval v => simp [checkWitness] at h
              | byValidEval => simp [checkWitness] at h
              | steps ps =>
                  simp only [checkWitness] at h ⊢
                  rw [Bool.and_eq_true, Bool.and_eq_true] at h ⊢
                  obtain ⟨⟨hlen, hinit⟩, hsteps⟩ := h
                  exact ⟨⟨hlen, hinit⟩, checkSteps_mono steps ps inv log hle' hsteps⟩

/-! ## The CheckedProp pack (the canon row — gaps LOUD) -/

/-- The witness lane as the canon's `CheckedProp` (design §2.4): sound
    by `checkWitness_sound`, completeness LOUD-missing — a low shipped
    fuel rejects true claims (the deliberate one-directional gate; the
    two-constructor escape makes the gap data, not a comment). -/
def witnessChecked : CodegenCore.CheckedProp (RowValsP × WProp × WProof × Nat) where
  P := fun ⟨ctx, claim, _, _⟩ => WHolds claim ctx.row ctx.log
  check := fun ⟨ctx, claim, proof, fuel⟩ =>
    checkWitness fuel claim proof ctx.fs ctx.row ctx.log
  sound := fun ⟨ctx, claim, proof, fuel⟩ h =>
    checkWitness_sound fuel claim proof ctx.row ctx.log h
  complete? := .missing

/-- The loud flag, pinned: this lane is sound-only. -/
theorem witnessChecked_incomplete : witnessChecked.isComplete = false := rfl

/-! ## The semantic tie to the compiled reading (design §2.4)

The mirror reflects a `VExpr` when field names resolve to paths; under
name uniqueness the name-based guest reading IS the path-based
compiled reading. -/

/-- The `WU64` mirror relation: a wire-level u64 term and the `VExpr`
    it reflects (the column's `ColPath` is the resolution evidence).
    (`strlenCol`, not `strlen`: the token `strlen` is registered by
    Validate.lean's scoped `vexpr` syntax and does not parse as a
    cases-alternative identifier inside `namespace SchemaLang`.) -/
inductive WUMirror {fs : List Field} : WU64 → VExpr fs .u64 → Prop where
  | lit (v : UInt64) : WUMirror (.lit v) (.lit v)
  | col (n : String) (p : ColPath n .u64 fs) : WUMirror (.col n) (.col n p)
  | strlenCol (n : String) (p : ColPath n .string fs) :
      WUMirror (.strlenCol n) (.strlen (.col n p))

/-- The `WBoolExpr` mirror relation, ctor-for-ctor. -/
inductive WBMirror {fs : List Field} : WBoolExpr → VExpr fs .bool → Prop where
  | gt {a b : WU64} {a' b' : VExpr fs .u64} :
      WUMirror a a' → WUMirror b b' → WBMirror (.gt a b) (.gt a' b')
  | eq {a b : WU64} {a' b' : VExpr fs .u64} :
      WUMirror a a' → WUMirror b b' → WBMirror (.eq a b) (.eq a' b')
  | and {a b : WBoolExpr} {a' b' : VExpr fs .bool} :
      WBMirror a a' → WBMirror b b' → WBMirror (.and a b) (.and a' b')
  | not {a : WBoolExpr} {a' : VExpr fs .bool} :
      WBMirror a a' → WBMirror (.not a) (.not a')

/-- A path's field name occurs in the schema's name list. -/
theorem colPath_mem_name {n : String} {t : Ty} {fs : List Field}
    (p : ColPath n t fs) : n ∈ fs.map Field.name := by
  induction p with
  | here => exact List.mem_cons_self
  | there p ih => exact List.mem_cons_of_mem _ ih

/-- Under name uniqueness, the name-based u64 lookup IS the path walk. -/
theorem lookupU64?_eq_of_colPath {fs : List Field} {n : String}
    (p : ColPath n .u64 fs) :
    (fs.map Field.name).Nodup → ∀ (row : RowVals fs),
      ∃ x, p.get row = .u64 x ∧ lookupU64? n fs row = some x := by
  induction p with
  | here =>
      intro _hnd row
      cases row with
      | cons v vs =>
          cases v with
          | u64 x => exact ⟨x, rfl, by simp [lookupU64?]⟩
  | @there f fs' p ih =>
      intro hnd row
      cases row with
      | cons v vs =>
          rw [List.map_cons] at hnd
          obtain ⟨hne, hnd'⟩ := List.nodup_cons.mp hnd
          have hmem : n ∈ fs'.map Field.name := colPath_mem_name p
          obtain ⟨fn, ft⟩ := f
          have hbeq : (fn == n) = false :=
            beq_false_of_ne (fun h => hne (h.symm ▸ hmem))
          obtain ⟨x, hget, hlook⟩ := ih hnd' vs
          refine ⟨x, hget, ?_⟩
          cases ft <;> simp [lookupU64?, hbeq, hlook]

/-- Under name uniqueness, the name-based string lookup IS the path
    walk. -/
theorem lookupString?_eq_of_colPath {fs : List Field} {n : String}
    (p : ColPath n .string fs) :
    (fs.map Field.name).Nodup → ∀ (row : RowVals fs),
      ∃ s, p.get row = .string s ∧ lookupString? n fs row = some s := by
  induction p with
  | here =>
      intro _hnd row
      cases row with
      | cons v vs =>
          cases v with
          | string s => exact ⟨s, rfl, by simp [lookupString?]⟩
  | @there f fs' p ih =>
      intro hnd row
      cases row with
      | cons v vs =>
          rw [List.map_cons] at hnd
          obtain ⟨hne, hnd'⟩ := List.nodup_cons.mp hnd
          have hmem : n ∈ fs'.map Field.name := colPath_mem_name p
          obtain ⟨fn, ft⟩ := f
          have hbeq : (fn == n) = false :=
            beq_false_of_ne (fun h => hne (h.symm ▸ hmem))
          obtain ⟨s, hget, hlook⟩ := ih hnd' vs
          refine ⟨s, hget, ?_⟩
          cases ft <;> simp [lookupString?, hbeq, hlook]

/-- `evalU` is `evalRaw` at the `.u64` slice (the specializations are
    definitionally transparent). -/
theorem evalU_eq_evalRaw {s : List Field} (e : VExpr s .u64) (row : RowVals s) :
    evalU e row = evalRaw e row := rfl

/-- `evalB` is `evalRaw` at the `.bool` slice. -/
theorem evalB_eq_evalRaw {s : List Field} (e : VExpr s .bool) (row : RowVals s) :
    evalB e row = evalRaw e row := rfl

/-- THE u64 TIE: a mirrored term's guest reading is the compiled
    reading, lifted through `some`. -/
theorem evalWU64?_eq_evalU {fs : List Field} {u : WU64} {e : VExpr fs .u64}
    (hm : WUMirror u e) (hnd : (fs.map Field.name).Nodup) (row : RowVals fs) :
    evalWU64? u fs row = some (evalU e row) := by
  cases hm with
  | lit v => rfl
  | col n p =>
      obtain ⟨x, hget, hlook⟩ := lookupU64?_eq_of_colPath p hnd row
      have hev : evalU (.col n p) row = x := by
        rw [evalU_eq_evalRaw]
        simp only [evalRaw]
        rw [hget]
      rw [show evalWU64? (.col n) fs row = lookupU64? n fs row from rfl, hlook, hev]
  | strlenCol n p =>
      obtain ⟨s, hget, hlook⟩ := lookupString?_eq_of_colPath p hnd row
      have hev : evalU (.strlen (.col n p)) row = string_len s := by
        rw [evalU_eq_evalRaw]
        simp only [evalRaw]
        rw [hget]
      rw [show evalWU64? (.strlenCol n) fs row =
            (lookupString? n fs row).map string_len from rfl, hlook]
      show some (string_len s) = some (evalU (.strlen (.col n p)) row)
      rw [hev]

/-- THE bool TIE: the mirror's 0/1 reading is the compiled `evalB`. -/
theorem evalWBool?_eq_evalB {fs : List Field} {w : WBoolExpr} {e : VExpr fs .bool}
    (hm : WBMirror w e) (hnd : (fs.map Field.name).Nodup) (row : RowVals fs) :
    evalWBool? w fs row = some (evalB e row) := by
  induction hm with
  | gt ha hb =>
      simp only [evalWBool?, evalRaw, evalB_eq_evalRaw, evalU_eq_evalRaw,
        evalWU64?_eq_evalU ha hnd row, evalWU64?_eq_evalU hb hnd row]
  | eq ha hb =>
      simp only [evalWBool?, evalRaw, evalB_eq_evalRaw, evalU_eq_evalRaw,
        evalWU64?_eq_evalU ha hnd row, evalWU64?_eq_evalU hb hnd row]
  | and ha hb iha ihb =>
      simp only [evalWBool?, evalRaw, evalB_eq_evalRaw, iha, ihb]
  | not ha iha =>
      simp only [evalWBool?, evalRaw, evalB_eq_evalRaw, iha]

/-- THE BRIDGE the consumer cites (design §2.4's "stated against
    Denotes/evalV"): under field-name uniqueness (the WellFormed
    condition), a mirrored `valid` claim holds of the row iff the
    compiled `validates` accepts the VExpr it mirrors. -/
theorem WHolds.valid_iff_validates {fs : List Field} {w : WBoolExpr} {e : VExpr fs .bool}
    (hm : WBMirror w e) (hnd : (fs.map Field.name).Nodup)
    (row : RowVals fs) (log : List (RowVals fs)) :
    WHolds (.valid w) row log ↔ validates e row = true := by
  constructor
  · intro h
    cases h with
    | valid he =>
        have h1 : evalB e row = 1 := by
          rw [evalWBool?_eq_evalB hm hnd row] at he
          exact Option.some.inj he
        exact beq_iff_eq.mpr h1
  · intro h
    have h1 : evalB e row = 1 := beq_iff_eq.mp h
    exact WHolds.valid (by rw [evalWBool?_eq_evalB hm hnd row, h1])

/-- The `eqU` grounding: a mirrored equality claim holds iff the
    compiled u64 readings agree. -/
theorem WHolds.eqU_iff_evalU {fs : List Field} {a b : WU64} {a' b' : VExpr fs .u64}
    (ha : WUMirror a a') (hb : WUMirror b b') (hnd : (fs.map Field.name).Nodup)
    (row : RowVals fs) (log : List (RowVals fs)) :
    WHolds (.eqU a b) row log ↔ evalU a' row = evalU b' row := by
  constructor
  · intro h
    cases h with
    | eqU h1 h2 =>
        rw [evalWU64?_eq_evalU ha hnd row] at h1
        rw [evalWU64?_eq_evalU hb hnd row] at h2
        exact (Option.some.inj h1).trans (Option.some.inj h2).symm
  · intro h
    exact WHolds.eqU (v := evalU a' row)
      (by rw [evalWU64?_eq_evalU ha hnd row])
      (by rw [evalWU64?_eq_evalU hb hnd row, h])

/-- The chain grounding (the W9.5 apply-gate's bridge shape): a checked
    chain certifies the compiled invariant at the initial row AND at
    every referenced log row. -/
theorem WHolds.chain_validates {fs : List Field} {steps : List WStep} {inv : WBoolExpr}
    {e : VExpr fs .bool} (hm : WBMirror inv e) (hnd : (fs.map Field.name).Nodup)
    {row : RowVals fs} {log : List (RowVals fs)}
    (h : WHolds (.chain steps inv) row log) :
    validates e row = true ∧
      ∀ s, s ∈ steps → ∃ r, log[s.offset]? = some r ∧ validates e r = true := by
  cases h with
  | chain hinit hsteps =>
      refine ⟨?_, fun s hs => ?_⟩
      · exact (WHolds.valid_iff_validates hm hnd row log).mp (WHolds.valid hinit)
      · obtain ⟨r, hget, hr⟩ := hsteps s hs
        exact ⟨r, hget, (WHolds.valid_iff_validates hm hnd r log).mp (WHolds.valid hr)⟩

/-! ## The W9.5 seam (the W9.6 mount point) -/

/-- THE SEAM (design-guest-verified §4 step 3): the witness verdict as
    ONE function boundary — certificate + decoded context in, verdict
    out. Today the callee is the interpreted `checkWitnessArtifact`;
    W9.6 swaps in the wasm-compiled checker, and every consumption-side
    call site (the W9.5 apply-gate `EventSourced.replayMigrated?`, the
    ledger dogfood's discharge) names THIS function, so the swap
    touches one definition and the oracle duel pins guest verdict ≡
    interpreted verdict. `@[guest_std]`-gated like the checker it
    wraps: the seam's closure is exactly the checker's. -/
def verifyWitness (w : Witness) (ctx : RowValsP) : Bool :=
  checkWitnessArtifact w ctx

/-- The seam's soundness-cited wrapper: an accepting verdict IS the
    claim's denotation (cites `checkWitnessArtifact_sound`). W9.6's
    compiled callee owes the SAME statement — the duel's theorem-side
    pin. -/
theorem verifyWitness_sound (w : Witness) (ctx : RowValsP)
    (h : verifyWitness w ctx = true) : WHolds w.claim ctx.row ctx.log :=
  checkWitnessArtifact_sound w ctx h

/-! ## The fuel classifier (the apply-gate's refusal classes, made exact) -/

/-- The checker's structural fuel minimum (deviation 2's cost model:
    one unit per rule node, plus one per chain step). The consumption
    side reads it to classify a refusal: below the minimum the check
    ALWAYS refuses (`checkWitness_eq_false_of_fuel_lt`); at or above it
    the verdict is fuel-free (`checkWitness_fuel_sufficient`).
    (`Emit.Witness.fuelConsumed` is the same function at the host's
    emission lane — same cost model, two named sites; the byte-tied
    artifact carries `consumed × 4`.) -/
def fuelNeed : WProp → Nat
  | .chain steps _ => steps.length + 1
  | _ => 1

/-- The per-step walk is fuel-free once the cap covers the steps. -/
theorem checkSteps_fuel_sufficient {fs : List Field} (steps : List WStep) :
    ∀ {fuel fuel' : Nat} (ps : List WProof) (inv : WBoolExpr)
      (log : List (RowVals fs)),
      steps.length ≤ fuel → steps.length ≤ fuel' →
      checkSteps fuel steps ps inv fs log = checkSteps fuel' steps ps inv fs log := by
  induction steps with
  | nil => intro fuel fuel' ps inv log _ _; cases ps <;> simp [checkSteps]
  | cons s ss ih =>
      intro fuel fuel' ps inv log hf hf'
      cases ps with
      | nil => simp [checkSteps]
      | cons p ps' =>
          have hf1 : 1 ≤ fuel := by
            have h := hf; simp only [List.length_cons] at h; omega
          have hf2 : 1 ≤ fuel' := by
            have h := hf'; simp only [List.length_cons] at h; omega
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
          have h1 : ss.length ≤ f := by
            have h := hf; simp only [List.length_cons] at h; omega
          have h2 : ss.length ≤ f' := by
            have h := hf'; simp only [List.length_cons] at h; omega
          simp only [checkSteps]
          rw [ih ps' inv log h1 h2]

/-- The verdict is FUEL-FREE at any cap at or above the structural
    minimum — the §7.3 "the guest never retries with more fuel" policy
    as a theorem: no larger cap could change the verdict, so a refusal
    at sufficient fuel is a divergence, permanently. -/
theorem checkWitness_fuel_sufficient {fs : List Field} (claim : WProp) :
    ∀ {fuel fuel' : Nat} (proof : WProof) (row : RowVals fs)
      (log : List (RowVals fs)),
      fuelNeed claim ≤ fuel → fuelNeed claim ≤ fuel' →
      checkWitness fuel claim proof fs row log =
        checkWitness fuel' claim proof fs row log := by
  cases claim with
  | valid e =>
      intro fuel fuel' proof row log hf hf'
      have hf1 : 1 ≤ fuel := hf
      have hf2 : 1 ≤ fuel' := hf'
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
      cases proof <;> simp [checkWitness]
  | eqU a b =>
      intro fuel fuel' proof row log hf hf'
      have hf1 : 1 ≤ fuel := hf
      have hf2 : 1 ≤ fuel' := hf'
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
      cases proof <;> simp [checkWitness]
  | chain steps inv =>
      intro fuel fuel' proof row log hf hf'
      have h1 : steps.length + 1 ≤ fuel := hf
      have h2 : steps.length + 1 ≤ fuel' := hf'
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
      cases proof with
      | byEval v => simp [checkWitness]
      | byValidEval => simp [checkWitness]
      | steps ps =>
          have h1' : steps.length ≤ f := by omega
          have h2' : steps.length ≤ f' := by omega
          simp only [checkWitness]
          rw [checkSteps_fuel_sufficient steps ps inv log h1' h2']

/-- The walk refuses when the cap cannot cover the remaining steps. -/
theorem checkSteps_eq_false_of_fuel_lt {fs : List Field} (steps : List WStep) :
    ∀ {fuel : Nat} (ps : List WProof) (inv : WBoolExpr) (log : List (RowVals fs)),
      fuel < steps.length → steps.length = ps.length →
      checkSteps fuel steps ps inv fs log = false := by
  induction steps with
  | nil => intro fuel ps inv log hlt _; simp at hlt
  | cons s ss ih =>
      intro fuel ps inv log hlt hlen
      cases ps with
      | nil => simp at hlen
      | cons p ps' =>
          cases fuel with
          | zero => simp [checkSteps]
          | succ f =>
              have hlt' : f < ss.length := by
                have h := hlt; simp only [List.length_cons] at h; omega
              have hlen' : ss.length = ps'.length := by
                have h := hlen; simp only [List.length_cons] at h; omega
              simp only [checkSteps]
              rw [ih ps' inv log hlt' hlen']
              simp

/-- Below the structural minimum the check ALWAYS refuses — fuel
    exhaustion is its own refusal class, never confusable with
    divergence (the apply-gate's classifier is exact, both directions). -/
theorem checkWitness_eq_false_of_fuel_lt {fs : List Field} (claim : WProp) :
    ∀ {fuel : Nat} (proof : WProof) (row : RowVals fs) (log : List (RowVals fs)),
      fuel < fuelNeed claim → checkWitness fuel claim proof fs row log = false := by
  cases claim with
  | valid e =>
      intro fuel proof row log hlt
      have h0 : fuel = 0 := by have h : fuel < 1 := hlt; omega
      subst h0; cases proof <;> simp [checkWitness]
  | eqU a b =>
      intro fuel proof row log hlt
      have h0 : fuel = 0 := by have h : fuel < 1 := hlt; omega
      subst h0; cases proof <;> simp [checkWitness]
  | chain steps inv =>
      intro fuel proof row log hlt
      have hle : fuel ≤ steps.length := by
        have h : fuel < steps.length + 1 := hlt; omega
      cases fuel with
      | zero => cases proof <;> simp [checkWitness]
      | succ f =>
          cases proof with
          | byEval v => simp [checkWitness]
          | byValidEval => simp [checkWitness]
          | steps ps =>
              have hf : f < steps.length := by omega
              simp only [checkWitness]
              by_cases hlen : (steps.length == ps.length) = true
              · rw [hlen]
                simp only [Bool.true_and]
                rw [checkSteps_eq_false_of_fuel_lt steps ps inv log hf
                  (beq_iff_eq.mp hlen)]
                simp
              · have hne : (steps.length == ps.length) = false :=
                  Bool.eq_false_iff.mpr hlen
                simp [hne]

end SchemaLang.WitnessCheck

end -- @[expose] public section
