/-
# SchemaLang.TickCascade — the cascade's composition laws

The v1 tick's cascade = folding the registered updates (in registration
order) over the table's rows. The flatland schedule-equivalence claim
(GAPS A2, SPEC §7.4) is "frame order may differ; final state may not" —
THEOREMS HERE are that claim's seed, at the row level:

1. `ColPath.get_set_neutral` — a write to column `n₁` changes NO other
   column's read (the write locality).
2. `VExpr.evalV_set_neutral` / `evalRaw_set_neutral` — an expression
   whose reads avoid the written column evaluates the same before and
   after the write (the reads-congruence), boxed and raw. The raw one
   is ONE general-index theorem (W3.4: the `RawTy` index unblocks
   `induction`; the fixed-slice pair `evalU_set_neutral`/`evalBNeutral`
   — including the proof-carrying-def workaround — is retired). The
   hypothesis is data-derived from `UpdateItem.reads` (a fold, never
   hand-listed), so it is CHECKABLE at registration time — the derived
   reads earning their keep.
3. THE CASCADE IS A DELTA SYSTEM (W4.3): `cascadeSystem` instantiates
   `Dbsp.Effects.DeltaSystem` at state = the table's rows, locations =
   column names, mutations = packed updates (`Σ f, UpdateItem fs f`) —
   application IS `Change.patch`. The one contract
   (`disjoint_commutes`) is `cascade_two_commute` reached through the
   derived influence sets; the N-update order-freedom
   (`cascade_applySeq_perm`) is `applySeq_perm` read off the instance.
4. `cascade_two_commute` — two updates that don't interfere (neither
   reads the other's write) compose in either order: the cascade's
   order-freedom for the disjoint case ("frame order may differ; final
   state may not"). Kept at its four-point hypothesis set — the
   `NonInterfering` granularity, FINER than the class's symmetric
   influence-disjointness (shared READS are safe and legal there; the
   class is the conservative composable form).
5. `set_same_order_disagrees` — the NEGATIVE: same-column writes are
   order-DEPENDENT (later-wins, `set_commute_same`); an explicit
   kernel-checked get-observable witness. The duality is pinned at BOTH
   levels: disjoint = order-free, same-column = later-wins (the journal
   carries S0 exactly there).

Honest scope: v1's cascade is sequential single-table; the full
schedule-equivalence (stage-walker ≡ queue-cascade, Refine's relational
shape) needs these laws PLUS the row-shape certification — the growth
path is noted in notes/flatland-alignment.md §2.
-/

import SchemaLang.Update
import Dbsp.Effects

namespace SchemaLang

/-! ## The reads-membership simp family -/

@[simp] theorem VExpr.not_mem_reads_col {n m : String} {s : List Field} {t : Ty}
    {p : ColPath m t s} : n ∉ (VExpr.col m p).reads ↔ n ≠ m := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_lit {n : String} {s : List Field} (v : UInt64) :
    n ∉ (VExpr.lit v : VExpr s .u64).reads := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_gt {n : String} {s : List Field} (a b : VExpr s .u64) :
    n ∉ (VExpr.gt a b).reads ↔ n ∉ a.reads ∧ n ∉ b.reads := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_eq {n : String} {s : List Field} (a b : VExpr s .u64) :
    n ∉ (VExpr.eq a b).reads ↔ n ∉ a.reads ∧ n ∉ b.reads := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_and {n : String} {s : List Field} (a b : VExpr s .bool) :
    n ∉ (VExpr.and a b).reads ↔ n ∉ a.reads ∧ n ∉ b.reads := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_strlen {n : String} {s : List Field} (e : VExpr s .string) :
    n ∉ (VExpr.strlen e).reads ↔ n ∉ e.reads := by
  simp [VExpr.reads]

@[simp] theorem VExpr.not_mem_reads_not {n : String} {s : List Field} (e : VExpr s .bool) :
    n ∉ (VExpr.not e).reads ↔ n ∉ e.reads := by
  simp [VExpr.reads]

/-! ## Write locality -/

/-- A write to column `n₁` does not change ANY OTHER column's read. -/
theorem ColPath.get_set_neutral {n₁ n : String} {t₁ t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (p₁ : ColPath n₁ t₁ fs),
      n ≠ n₁ → ∀ (row : RowVals fs) (v : Value t₁),
        p.get (p₁.set row v) = p.get row := by
  intro fs
  induction fs with
  | nil => intro p _ _; cases p
  | cons f fs ih =>
      intro p p₁ hne row v
      cases p with
      | here =>
          cases p₁ with
          | here => exact absurd rfl hne
          | there p₁' => cases row; simp [ColPath.set, ColPath.get]
      | there p' =>
          cases p₁ with
          | here => cases row; simp [ColPath.set, ColPath.get]
          | there p₁' =>
              cases row with
              | cons a vs => simp only [ColPath.set]; exact ih p' p₁' hne vs v

/-- An expression whose reads avoid column `n₁` evaluates the same
    before and after a write to `n₁` (the reads-congruence). -/
theorem VExpr.evalV_set_neutral {fs : List Field} {n₁ : String} {t₁ : Ty} :
    ∀ {t : Ty} (e : VExpr fs t) (p₁ : ColPath n₁ t₁ fs) (_hne : n₁ ∉ e.reads)
      (row : RowVals fs) (v : Value t₁),
      evalV e (p₁.set row v) = evalV e row := by
  intro t e
  induction e with
  | col n p =>
      intro p₁ hne row v
      have hnn : n₁ ≠ n := by
        simpa using hne
      exact ColPath.get_set_neutral p p₁ hnn.symm row v
  | lit _ => intro _ _ _ _; rfl
  | gt a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp [evalV, iha p₁ ha row v, ihb p₁ hb row v]
  | eq a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp [evalV, iha p₁ ha row v, ihb p₁ hb row v]
  | and a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp [evalV, iha p₁ ha row v, ihb p₁ hb row v]
  | «strlen» e ih =>
      intro p₁ hne row v
      have he : n₁ ∉ e.reads := by
        simpa using hne
      simp [evalV, ih p₁ he row v]
  | not e ih =>
      intro p₁ hne row v
      have he : n₁ ∉ e.reads := by
        simpa using hne
      simp [evalV, ih p₁ he row v]

/-- The RAW evaluator's congruence, at the GENERAL index (W3.4): an
    expression whose reads avoid column `n₁` evaluates the same before
    and after a write to `n₁`. The general `t` index is what unblocks
    `induction` — the fixed-index `.bool` slice barred it, forcing the
    old proof-carrying-def workaround (`evalBNeutral`; retired, with
    `evalU_set_neutral`, into this ONE theorem). The `strlen` case's
    operand is a field ref (the only `.string`-typed shape), so it
    closes by `cases` + `get_set_neutral`, no induction hypothesis. -/
theorem VExpr.evalRaw_set_neutral {fs : List Field} {n₁ : String} {t₁ : Ty} :
    ∀ {t : Ty} (e : VExpr fs t) (p₁ : ColPath n₁ t₁ fs) (_hne : n₁ ∉ e.reads)
      (row : RowVals fs) (v : Value t₁),
      evalRaw e (p₁.set row v) = evalRaw e row := by
  intro t e
  induction e with
  | col n p =>
      intro p₁ hne row v
      have hnn : n₁ ≠ n := by
        simpa using hne
      have := ColPath.get_set_neutral p p₁ hnn.symm row v
      simp only [evalRaw, this]
  | lit _ => intro _ _ _ _; rfl
  | gt a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp only [evalRaw]
      rw [iha p₁ ha row v, ihb p₁ hb row v]
  | eq a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp only [evalRaw]
      rw [iha p₁ ha row v, ihb p₁ hb row v]
  | and a b iha ihb =>
      intro p₁ hne row v
      have ⟨ha, hb⟩ : n₁ ∉ a.reads ∧ n₁ ∉ b.reads := by
        simpa using hne
      simp only [evalRaw]
      rw [iha p₁ ha row v, ihb p₁ hb row v]
  | «strlen» e _ih =>
      intro p₁ hne row v
      -- the operand is a field ref (the only `.string` shape)
      cases e with
      | col n p =>
          have hnn : n₁ ≠ n := by
            simpa using hne
          have := ColPath.get_set_neutral p p₁ hnn.symm row v
          simp only [evalRaw, this]
  | not e ih =>
      intro p₁ hne row v
      have he : n₁ ∉ e.reads := by
        simpa using hne
      simp only [evalRaw]
      rw [ih p₁ he row v]

/-! ## The cascade -/

/-- DISJOINT cascade: two updates where NEITHER reads the other's
    written column compose in either order (the order-free composition
    law — "frame order may differ; final state may not", row level).
    The reads-congruence (evalB/evalV neutrality) handles the guards
    and values; `set_commute_disjoint` handles the writes. -/
theorem cascade_two_commute
    {fs : List Field} {f₁ f₂ : Field}
    (u₁ : UpdateItem fs f₁) (u₂ : UpdateItem fs f₂)
    (h₁g : f₂.name ∉ u₁.guard.reads) (h₁v : f₂.name ∉ u₁.value.reads)
    (h₂g : f₁.name ∉ u₂.guard.reads) (h₂v : f₁.name ∉ u₂.value.reads)
    (hne : f₁.name ≠ f₂.name)
    (rows : List (RowVals fs)) :
    (rows.map u₂.applyRow).map u₁.applyRow
      = (rows.map u₁.applyRow).map u₂.applyRow := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
      have hne' : f₂.name ≠ f₁.name := fun h => hne h.symm
      have g₁ : ∀ (row : RowVals fs),
          evalB u₁.guard (u₂.writePath.set row (evalV u₂.value r))
            = evalB u₁.guard row :=
        fun row => VExpr.evalRaw_set_neutral u₁.guard u₂.writePath h₁g row (evalV u₂.value r)
      have g₂ : ∀ (row : RowVals fs),
          evalB u₂.guard (u₁.writePath.set row (evalV u₁.value r))
            = evalB u₂.guard row :=
        fun row => VExpr.evalRaw_set_neutral u₂.guard u₁.writePath h₂g row (evalV u₁.value r)
      have v₁ : evalV u₁.value (u₂.writePath.set r (evalV u₂.value r))
          = evalV u₁.value r :=
        VExpr.evalV_set_neutral u₁.value u₂.writePath h₁v r (evalV u₂.value r)
      have v₂ : evalV u₂.value (u₁.writePath.set r (evalV u₁.value r))
          = evalV u₂.value r :=
        VExpr.evalV_set_neutral u₂.value u₁.writePath h₂v r (evalV u₁.value r)
      show (_ :: _) = (_ :: _)
      rw [ih]
      congr 1
      show u₁.applyRow (u₂.applyRow r) = u₂.applyRow (u₁.applyRow r)
      unfold UpdateItem.applyRow validates
      -- the guard verdicts are order-independent (the neutrality),
      -- made explicit per branch:
      by_cases hg₁ : (evalB u₁.guard r == 1) = true
      · by_cases hg₂ : (evalB u₂.guard r == 1) = true
        · -- both fire (in both orders — the guard neutrality): the
          -- writes commute (set_commute_disjoint)
          have c₁ : (evalB u₁.guard (u₂.writePath.set r (evalV u₂.value r)) == 1) = true := by
            rw [g₁ r]; exact hg₁
          have c₂ : (evalB u₂.guard (u₁.writePath.set r (evalV u₁.value r)) == 1) = true := by
            rw [g₂ r]; exact hg₂
          rw [if_pos hg₂, if_pos hg₁, if_pos c₁, if_pos c₂, v₁, v₂]
          exact ColPath.set_commute_disjoint u₂.writePath u₁.writePath hne' r
            (evalV u₂.value r) (evalV u₁.value r)
        · -- u₂ refuses (in both orders — the guard neutrality): the
          -- result is u₁'s write either way
          have nc₂ : ¬ ((evalB u₂.guard (u₁.writePath.set r (evalV u₁.value r)) == 1) = true) := by
            intro hh; rw [g₂ r] at hh; exact hg₂ hh
          rw [if_neg hg₂, if_pos hg₁, if_neg nc₂]
      · -- u₁ refuses in both orders: the result is u₂'s write or r
        have nc₁ : ¬ ((evalB u₁.guard (u₂.writePath.set r (evalV u₂.value r)) == 1) = true) := by
          intro hh; rw [g₁ r] at hh; exact hg₁ hh
        -- the INNER ifs collapse first (the outer conditions name the
        -- post-write rows only after the inner collapse)
        by_cases hg₂ : (evalB u₂.guard r == 1) = true
        · rw [if_neg hg₁, if_pos hg₂, if_neg nc₁]
        · rw [if_neg hg₂, if_neg hg₁, if_neg hg₂]

/-! ## The cascade IS a DeltaSystem (W4.3)

`Dbsp.Effects.DeltaSystem` (which extends `Change S Mut`) at: state =
the table's rows, locations = column names, mutations = packed updates.
The static influence of a packed update is reads ++ writes — write sets
ALONE cannot certify commutation, because `applyRow` READS the row: a
guard or value reading the other update's written column breaks
order-freedom (the guard-neutrality hypotheses of
`cascade_two_commute` exist exactly there). Influence-disjointness is
the conservative form — it also forbids SHARED reads, which are safe —
so `cascade_two_commute` keeps its finer four-point hypothesis set (the
`NonInterfering` granularity) and the instance's discharge EXTRACTS
those four facts from disjointness. -/

/-- The static influence of a packed update: every column whose change
    can alter the update's effect — the derived reads plus the written
    column (never hand-listed; `UpdateItem.reads`/`writes` are folds). -/
def cascadeInfluence {fs : List Field} (u : Σ f, UpdateItem fs f) : List String :=
  u.2.reads ++ u.2.writes

/-- Membership out of the influence set, unpacked to the row level: a
    column outside the influence is read by NEITHER expression and is
    not the written column. -/
theorem UpdateItem.not_mem_influence {fs : List Field} {f : Field}
    {u : UpdateItem fs f} {x : String}
    (h : x ∉ u.reads ++ u.writes) :
    x ∉ u.guard.reads ∧ x ∉ u.value.reads ∧ x ≠ f.name := by
  have hr : x ∉ u.reads := fun hx => h (List.mem_append_left _ hx)
  have hw : x ∉ u.writes := fun hx => h (List.mem_append_right _ hx)
  refine ⟨?_, ?_, ?_⟩
  · exact fun hx => hr (List.mem_eraseDups.mpr (List.mem_append_left _ hx))
  · exact fun hx => hr (List.mem_eraseDups.mpr (List.mem_append_right _ hx))
  · intro heq
    subst heq
    simp [UpdateItem.writes] at hw

-- the `warn.classDefReducibility` warning is silenced to say so (the
-- pointDeltaSystem precedent): the system is passed explicitly
-- (`cascadeSystem fs`), never found by instance search.
set_option warn.classDefReducibility false in
/-- THE INSTANCE: the row-table cascade is a delta system. Application
    IS patching (`UpdateItem.apply`); the ONE contract
    (`disjoint_commutes`) delegates to `cascade_two_commute` — the
    influence-disjointness premise unpacks to its four-point hypothesis
    set (`not_mem_influence`), never re-proved. -/
def cascadeSystem (fs : List Field) :
    Dbsp.DeltaSystem (List (RowVals fs)) String (Σ f, UpdateItem fs f) where
  patch rows u := u.2.apply rows
  valid _ _ := True
  writesOf := cascadeInfluence
  disjoint_commutes := by
    intro m₁ m₂ hd rows
    obtain ⟨f₁, u₁⟩ := m₁
    obtain ⟨f₂, u₂⟩ := m₂
    have hd' : Dbsp.LocDisjoint (u₁.reads ++ u₁.writes) (u₂.reads ++ u₂.writes) :=
      hd
    have hw₁ : f₁.name ∈ u₁.reads ++ u₁.writes :=
      List.mem_append_right _ (by simp [UpdateItem.writes])
    have hw₂ : f₂.name ∈ u₂.reads ++ u₂.writes :=
      List.mem_append_right _ (by simp [UpdateItem.writes])
    obtain ⟨h₁g, h₁v, -⟩ := UpdateItem.not_mem_influence (fun h => hd' h hw₂)
    obtain ⟨h₂g, h₂v, hne⟩ := UpdateItem.not_mem_influence (fun h => hd' hw₁ h)
    show (rows.map u₂.applyRow).map u₁.applyRow
      = (rows.map u₁.applyRow).map u₂.applyRow
    exact cascade_two_commute u₁ u₂ h₁g h₁v h₂g h₂v hne rows

/-- The class-vocabulary restatement: influence-disjoint packed updates
    commute — `disjoint_commutes` read off the instance. Thin BY
    DESIGN: the class site owns the proof. -/
theorem cascade_disj_commutes {fs : List Field} (u₁ u₂ : Σ f, UpdateItem fs f)
    (hd : Dbsp.LocDisjoint (cascadeInfluence u₁) (cascadeInfluence u₂))
    (rows : List (RowVals fs)) :
    (rows.map u₂.2.applyRow).map u₁.2.applyRow
      = (rows.map u₁.2.applyRow).map u₂.2.applyRow :=
  (cascadeSystem fs).disjoint_commutes u₁ u₂ hd rows

/-- N-update order-freedom: a pairwise influence-disjoint batch of
    packed updates computes the same final table under ANY ordering —
    `Dbsp.applySeq_perm` read off the instance (the permutation
    invariance of conflict-free batches, instantiated at the cascade). -/
theorem cascade_applySeq_perm {fs : List Field} {us₁ us₂ : List (Σ f, UpdateItem fs f)}
    (hp : us₁.Perm us₂)
    (hpair : us₁.Pairwise
      (fun a b => Dbsp.LocDisjoint (cascadeInfluence a) (cascadeInfluence b)))
    (rows : List (RowVals fs)) :
    Dbsp.applySeq (cascadeSystem fs) us₁ rows
      = Dbsp.applySeq (cascadeSystem fs) us₂ rows :=
  Dbsp.applySeq_perm hp hpair rows

/-- The NEGATIVE (the get-observable witness): same-column writes are
    ORDER-DEPENDENT — `set 0` then `set 5` reads 5; the other order
    reads 0. The journal's S0 policy exists exactly for this channel
    (later-wins; `set_commute_same` is its composition law). -/
theorem set_same_order_disagrees (row : RowVals [(⟨"id", Ty.u64⟩ : Field)])
    (p : ColPath "id" .u64 [(⟨"id", Ty.u64⟩ : Field)]) :
    p.get (p.set (p.set row (.u64 0)) (.u64 5))
      ≠ p.get (p.set row (.u64 0)) := by
  intro h
  cases p with
  | here => cases row; simp [ColPath.get, ColPath.set] at h
  | there p' => cases p'

end SchemaLang
