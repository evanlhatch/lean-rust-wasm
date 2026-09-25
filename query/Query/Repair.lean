/-
# Query.Repair — the repair discipline's seed: the candidate checked
against the specification

Owned by: the explanations-lane agent (the mandate tree, `query/`).
Driving decisions: notes/v3/02-data-plane.md §11 (explanations are
query semantics: WHICH CHANGE REPAIRS THE CONSTRAINT → a candidate
repair checked against the specification) + notes/v3/03-bidirectional.md
§7-8 (the delta is the accepted net change; a proposal's check is the
violation relation's emptiness) — consumed read-only over the violation
lane's landed surfaces (`SchemaCore.Violate`'s fixture, the update
lane's shared `RowDelta` substrate).

What lands here (the honest minimal, at the violation lane's fixture):

- `Violation.repair?` — THE CANDIDATE REPAIR: one named keyed delta
  per violation kind, riding the update lane's `RowDelta`/`applyRowDelta`
  substrate (no parallel change carrier). The duplicate-id violation
  has NO single-delta candidate — which row wins is a POLICY choice,
  not a derivation — the honest `none`, rendered loudly.
- `Db.applyRepair` — the candidate applied through the keyed
  applicator.
- `repairVerdict` — THE SPECIFICATION'S OWN DECISION: the residual
  violations of the repaired world (the state invariant's violation
  query re-run — never a bespoke "fixed" flag). Residuals are data.
- The bridges: `repairVerdict_clean_iff_valid` (a clean verdict IS the
  state invariant, through `valid_iff` — pattern #1's one-lemma cite)
  and the targeted-resolution theorems (the credited account is no
  longer a negative-balance violation; the removed transfer no longer
  dangles).

Deliberate exclusions (the leftover rule, each names its reason): the
duplicate-id candidate (a policy, not a derivation — the honest none
above); multi-repair composition (a world with several violations gets
each candidate's residual verdict from `repairVerdict` — composing
candidates into a plan has no consumer yet); repair MINIMALITY (the
candidate is A repair, not the minimal one — a minimality order needs
its own named semantics).

The five questions (notes/v3/01-core.md):
- **Root**: the data plane's explanation face (02 §11's repair
  question) over the violation lane's fixture.
- **Carrier grade**: the candidate is the update lane's OWN keyed
  delta — a mistyped repair is unconstructible (the GADT index).
- **Spine reading**: none — the seed rides the violation query and
  the keyed applicator.
- **Ladder rung**: hand theorems of the small kind — the targeted-
  resolution faces are positional computations (the GADT readers
  reduce); the clean-verdict bridge cites `valid_iff`.
- **Gate rows**: the axiom report + the repair suite in QueryTests
  (the worked candidates, the honest-none, the residual verdicts,
  the mandatory negative controls).

Core-only (imports SchemaCore.Violate — the cone rule; Query already
lives behind SchemaCore + ZSet).
-/

import SchemaCore.Violate

namespace Query

open SchemaCore

/-! ## The candidate repair's delta carrier -/

/-- The candidate repair's delta: the violated TABLE's own keyed delta
    (the update lane's shared `RowDelta` substrate — no parallel
    change carrier). -/
inductive RepairDelta where
  /-- A delta over the account table. -/
  | account : RowDelta accountFields → RepairDelta
  /-- A delta over the transfer table. -/
  | transfer : RowDelta transferFields → RepairDelta

/-! ## The positional facts the resolutions reduce through -/

/-- The credited row keeps its id. -/
theorem accId_withBal : ∀ (r : RowVals accountFields) (b : Int64),
    accId (withBal r b) = accId r
  | RowVals.cons (Value.u64 _) (RowVals.cons (Value.string _)
      (RowVals.cons (Value.i64 _) RowVals.nil)), _ => rfl

/-- The credited row's balance IS the new one. -/
theorem accBal_withBal : ∀ (r : RowVals accountFields) (b : Int64),
    accBal (withBal r b) = b
  | RowVals.cons (Value.u64 _) (RowVals.cons (Value.string _)
      (RowVals.cons (Value.i64 _) RowVals.nil)), _ => rfl

/-- The account's id projects (the key image, positionally). -/
theorem accId_image : ∀ (r : RowVals accountFields),
    RowVals.project? accountFields r "id" = some ⟨.u64, .u64 (accId r)⟩
  | RowVals.cons (Value.u64 _) (RowVals.cons (Value.string _)
      (RowVals.cons (Value.i64 _) RowVals.nil)) => rfl

/-- The transfer's tid projects (the key image, positionally). -/
theorem trTid_image : ∀ (t : RowVals transferFields),
    RowVals.project? transferFields t "tid" = some ⟨.u64, .u64 (trId t)⟩
  | RowVals.cons (Value.u64 _) (RowVals.cons (Value.u64 _)
      (RowVals.cons (Value.u64 _) (RowVals.cons (Value.u64 _) RowVals.nil))) => rfl

/-! ## The candidate per violation -/

/-- THE CANDIDATE REPAIR (02 §11: which change repairs the
    constraint): one named keyed delta per violation kind.

    - a negative balance → the account credited to zero;
    - a dangling endpoint → the transfer removed (keyed by `tid`);
    - a DUPLICATE id → NO candidate: which row wins is a policy
      choice, not a derivation — the honest `none`, rendered loudly. -/
def Violation.repair? : Violation → Option RepairDelta
  | .negative r => some (.account (.update (withBal r 0)))
  | .danglingSrc t => some (.transfer (.remove ⟨.u64, .u64 (trId t)⟩))
  | .danglingDst t => some (.transfer (.remove ⟨.u64, .u64 (trId t)⟩))
  | .dupId _ => none

/-- The candidate applied, through the update lane's keyed applicator
    (read-only consumption — no second table semantics). -/
def Db.applyRepair (db : Db) : RepairDelta → Db
  | .account d => { db with accounts := applyRowDelta "id" d db.accounts }
  | .transfer d => { db with transfers := applyRowDelta "tid" d db.transfers }

/-- THE REPAIR'S VERDICT — the specification's own decision: the
    residual violations of the repaired world (the state invariant's
    violation query re-run). Residuals are DATA, never hidden. -/
def repairVerdict (db : Db) (v : Violation) : Option (List Violation) :=
  (Violation.repair? v).map (fun d => violations (Db.applyRepair db d))

/-! ## The bridges -/

/-- THE CLEAN-VERDICT BRIDGE (pattern #1, citing `valid_iff` — never a
    second state-invariant theorem): the repaired world's verdict is
    clean iff the repaired world is VALID. -/
theorem repairVerdict_clean_iff_valid (db : Db) (v : Violation)
    (d : RepairDelta) (hv : Violation.repair? v = some d) :
    repairVerdict db v = some [] ↔ Valid (Db.applyRepair db d) := by
  unfold repairVerdict
  rw [hv]
  simp only [Option.map_some, Option.some.injEq]
  exact (valid_iff _).symm

/-- THE TARGETED RESOLUTION, credit face: the credited account is no
    longer A negative-balance violation — the candidate repairs the
    constraint it answered (the WORLD's verdict is `repairVerdict`,
    with residuals as data). -/
theorem applyRepair_credit_targeted (db : Db) (r : RowVals accountFields) :
    Violation.negative r
      ∉ violations (Db.applyRepair db (.account (.update (withBal r 0)))) := by
  intro hmem
  simp only [Db.applyRepair, violations, List.mem_append] at hmem
  rcases hmem with ((h | h) | h) | h
  · exact absurd h (by simp)
  · obtain ⟨x, hx, he⟩ := List.mem_map.mp h
    have hxr : x = r := Violation.negative.inj he
    rw [hxr] at hx
    rw [negativeAccounts, List.mem_filter] at hx
    obtain ⟨hmem2, hbal0⟩ := hx
    have hbal : decide (accBal r < 0) = true := hbal0
    rw [applyRowDelta] at hmem2
    rw [List.mem_map] at hmem2
    obtain ⟨old, hold, he2⟩ := hmem2
    -- the update arm's body, beta-reduced at `old`
    have hbody : (match RowVals.project? accountFields old "id" with
        | some a =>
            match RowVals.project? accountFields (withBal r 0) "id" with
            | some b => if FieldVal.beq a b then withBal r 0 else old
            | none => old
        | none => old) = r := he2
    have hproj0 : RowVals.project? accountFields (withBal r 0) "id"
        = some ⟨.u64, .u64 (accId r)⟩ := by
      rw [accId_image, accId_withBal]
    cases hp1 : RowVals.project? accountFields old "id" with
    | none =>
        simp only [hp1] at hbody
        -- hbody : old = r; but r's key projects — contradiction
        have hpo := hp1
        rw [hbody, accId_image] at hpo
        exact absurd hpo (by simp)
    | some a =>
        simp only [hp1, hproj0] at hbody
        -- hbody : (if beq a img then withBal r 0 else old) = r
        cases hb : FieldVal.beq a ⟨.u64, .u64 (accId r)⟩ with
        | false =>
            rw [hb, if_neg (by decide)] at hbody
            -- hbody : old = r; then a IS r's image — beq refl — contradiction
            have hpo := hp1
            rw [hbody, accId_image] at hpo
            have haa : ⟨.u64, .u64 (accId r)⟩ = a := Option.some.inj hpo
            rw [haa, FieldVal.beq_refl] at hb
            exact absurd hb (by decide)
        | true =>
            rw [hb, if_pos (by decide)] at hbody
            -- hbody : withBal r 0 = r; the credited balance is 0 — contradiction
            rw [← hbody, accBal_withBal] at hbal
            exact absurd hbal (by decide)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- THE TARGETED RESOLUTION, source-dangle face: the removed transfer
    no longer dangles on its `src`. -/
theorem applyRepair_danglingSrc_targeted (db : Db) (t : RowVals transferFields) :
    Violation.danglingSrc t
      ∉ violations (Db.applyRepair db (.transfer (.remove ⟨.u64, .u64 (trId t)⟩))) := by
  intro hmem
  simp only [Db.applyRepair, violations, List.mem_append] at hmem
  rcases hmem with ((h | h) | h) | h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · obtain ⟨x, hx, he⟩ := List.mem_map.mp h
    have hxr : x = t := Violation.danglingSrc.inj he
    rw [hxr] at hx
    rw [danglingSrc, applyRowDelta] at hx
    rw [List.mem_filter] at hx
    obtain ⟨hmem2, _⟩ := hx
    rw [List.mem_filter] at hmem2
    obtain ⟨_, hkeep⟩ := hmem2
    have hkeep' : (match RowVals.project? transferFields t "tid" with
        | some a => !FieldVal.beq a ⟨.u64, .u64 (trId t)⟩
        | none => true) = true := hkeep
    simp only [trTid_image, FieldVal.beq_refl, Bool.not_true] at hkeep'
    exact absurd hkeep' (by decide)
  · exact absurd h (by simp)

/-- THE TARGETED RESOLUTION, destination-dangle face. -/
theorem applyRepair_danglingDst_targeted (db : Db) (t : RowVals transferFields) :
    Violation.danglingDst t
      ∉ violations (Db.applyRepair db (.transfer (.remove ⟨.u64, .u64 (trId t)⟩))) := by
  intro hmem
  simp only [Db.applyRepair, violations, List.mem_append] at hmem
  rcases hmem with ((h | h) | h) | h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · obtain ⟨x, hx, he⟩ := List.mem_map.mp h
    have hxr : x = t := Violation.danglingDst.inj he
    rw [hxr] at hx
    rw [danglingDst, applyRowDelta] at hx
    rw [List.mem_filter] at hx
    obtain ⟨hmem2, _⟩ := hx
    rw [List.mem_filter] at hmem2
    obtain ⟨_, hkeep⟩ := hmem2
    have hkeep' : (match RowVals.project? transferFields t "tid" with
        | some a => !FieldVal.beq a ⟨.u64, .u64 (trId t)⟩
        | none => true) = true := hkeep
    simp only [trTid_image, FieldVal.beq_refl, Bool.not_true] at hkeep'
    exact absurd hkeep' (by decide)

end Query
