/-
# SchemaLang.TickCascade — the cascade's composition laws

The v1 tick's cascade = folding the registered updates (in registration
order) over the table's rows. The flatland schedule-equivalence claim
(GAPS A2, SPEC §7.4) is "frame order may differ; final state may not" —
THEOREMS HERE are that claim's seed, at the row level:

1. `ColPath.get_set_neutral` — a write to column `n₁` changes NO other
   column's read (the write locality).
2. `VExpr.evalV_set_neutral` / `evalU_set_neutral` / `evalBNeutral` —
   an expression whose reads avoid the written column evaluates the
   same before and after the write (the reads-congruence). The
   hypothesis is data-derived from `UpdateItem.reads` (a fold, never
   hand-listed), so it is CHECKABLE at registration time — the derived
   reads earning their keep. (evalB's is a PROOF-CARRYING DEF — the
   fixed-index `.bool` slice bars the `induction` tactic; the def
   recurses structurally, the `valueEqRefl` precedent.)
3. `cascade_two_commute` — two updates that don't interfere (neither
   reads the other's write) compose in either order: the cascade's
   order-freedom for the disjoint case ("frame order may differ; final
   state may not").
4. `set_same_order_disagrees` — the NEGATIVE: same-column writes are
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

namespace SchemaLang

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
      have hnn : n ≠ n₁ := fun h => hne (by
        show n₁ ∈ VExpr.reads (VExpr.col n p)
        simp only [VExpr.reads, List.mem_cons]
        exact Or.inl h.symm)
      exact ColPath.get_set_neutral p p₁ hnn row v
  | lit _ => intro _ _ _ _; rfl
  | gt a b iha ihb =>
      intro p₁ hne row v
      have ha : n₁ ∉ a.reads := fun h => hne (List.mem_append.2 (Or.inl h))
      have hb : n₁ ∉ b.reads := fun h => hne (List.mem_append.2 (Or.inr h))
      simp [evalV, iha p₁ ha row v, ihb p₁ hb row v]
  | eq a b iha ihb =>
      intro p₁ hne row v
      have ha : n₁ ∉ a.reads := fun h => hne (List.mem_append.2 (Or.inl h))
      have hb : n₁ ∉ b.reads := fun h => hne (List.mem_append.2 (Or.inr h))
      simp [evalV, iha p₁ ha row v, ihb p₁ hb row v]
  | and a b iha ihb =>
      intro p₁ hne row v
      have ha : n₁ ∉ a.reads := fun h => hne (List.mem_append.2 (Or.inl h))
      have hb : n₁ ∉ b.reads := fun h => hne (List.mem_append.2 (Or.inr h))
      simp [evalV, iha p₁ ha row v, ihb p₁ hb row v]
  | «strlen» e ih =>
      intro p₁ hne row v
      have he : n₁ ∉ e.reads := hne
      simp [evalV, ih p₁ he row v]
  | not e ih =>
      intro p₁ hne row v
      have he : n₁ ∉ e.reads := hne
      simp [evalV, ih p₁ he row v]

/-- The RAW u64 evaluator's congruence — the `.u64` slice admits
    lit/col/strlen ONLY (cases, no induction needed: no self-recursion). -/
theorem VExpr.evalU_set_neutral {fs : List Field} {n₁ : String} {t₁ : Ty} :
    ∀ (e : VExpr fs .u64) (p₁ : ColPath n₁ t₁ fs) (_hne : n₁ ∉ e.reads)
      (row : RowVals fs) (v : Value t₁),
      evalU e (p₁.set row v) = evalU e row := by
  intro e
  cases e with
  | lit _ => intro _ _ _ _; rfl
  | col n p =>
      intro p₁ hne row v
      have hnn : n ≠ n₁ := fun h => hne (by
        show n₁ ∈ VExpr.reads (VExpr.col n p)
        simp only [VExpr.reads, List.mem_cons]
        exact Or.inl h.symm)
      have := ColPath.get_set_neutral p p₁ hnn row v
      simp only [evalU, this]
  | «strlen» e =>
      intro p₁ hne row v
      -- the operand is a field ref (the only `.string` shape)
      cases e with
      | col n p =>
          have hnn : n ≠ n₁ := fun h => hne (by
            show n₁ ∈ VExpr.reads (VExpr.col n p)
            simp only [VExpr.reads, List.mem_cons]
            exact Or.inl h.symm)
          have := ColPath.get_set_neutral p p₁ hnn row v
          simp only [evalU, this]

/-- The raw BOOL evaluator's congruence — a PROOF-CARRYING DEF (the
    fixed-index `.bool` slice bars `induction`; `and` recurses
    structurally — the `valueEqRefl` precedent). -/
theorem VExpr.evalBNeutral {fs : List Field} {n₁ : String} {t₁ : Ty}
    (e : VExpr fs .bool) (p₁ : ColPath n₁ t₁ fs) (hne : n₁ ∉ e.reads) :
    ∀ (row : RowVals fs) (v : Value t₁),
      evalB e (p₁.set row v) = evalB e row := by
  cases e with
  | col n p =>
      intro row v
      have hnn : n ≠ n₁ := fun h => hne (by
        show n₁ ∈ VExpr.reads (VExpr.col n p)
        simp only [VExpr.reads, List.mem_cons]
        exact Or.inl h.symm)
      have := ColPath.get_set_neutral p p₁ hnn row v
      simp only [evalB, this]
  | gt a b =>
      intro row v
      have ha : n₁ ∉ a.reads := fun h => hne (List.mem_append.2 (Or.inl h))
      have hb : n₁ ∉ b.reads := fun h => hne (List.mem_append.2 (Or.inr h))
      simp only [evalB]
      rw [evalU_set_neutral a p₁ ha row v, evalU_set_neutral b p₁ hb row v]
  | eq a b =>
      intro row v
      have ha : n₁ ∉ a.reads := fun h => hne (List.mem_append.2 (Or.inl h))
      have hb : n₁ ∉ b.reads := fun h => hne (List.mem_append.2 (Or.inr h))
      simp only [evalB]
      rw [evalU_set_neutral a p₁ ha row v, evalU_set_neutral b p₁ hb row v]
  | and a b =>
      intro row v
      have ha : n₁ ∉ a.reads := fun h => hne (List.mem_append.2 (Or.inl h))
      have hb : n₁ ∉ b.reads := fun h => hne (List.mem_append.2 (Or.inr h))
      simp only [evalB]
      rw [evalBNeutral a p₁ ha row v, evalBNeutral b p₁ hb row v]
  | not e =>
      intro row v
      have he : n₁ ∉ e.reads := hne
      simp only [evalB]
      rw [evalBNeutral e p₁ he row v]

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
        fun row => VExpr.evalBNeutral u₁.guard u₂.writePath h₁g row (evalV u₂.value r)
      have g₂ : ∀ (row : RowVals fs),
          evalB u₂.guard (u₁.writePath.set row (evalV u₁.value r))
            = evalB u₂.guard row :=
        fun row => VExpr.evalBNeutral u₂.guard u₁.writePath h₂g row (evalV u₁.value r)
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
