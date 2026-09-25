/-
# ZSet.Basic — the canonical weighted-relation layer + the ℤ surface

Owned by: the ZSet agent (the mandate tree, `zset/`).

The five questions (notes/v3/01-core.md):
- **Root**: Change (01 §2) — the delta ladder's TOP rung: `ZSet` is the
  canonical `Kit.Change.Additive` instance (delta-as-state, the dbsp
  reading), the symmetry layer's carrier for signed multiplicities.
  ALSO the Universe × Change crossing (02 §4): `Weighted K Row` is the
  ONE relation semantics with a family of weights — Bool = membership,
  Nat = multiplicity, ℤ = deltas.
- **Carrier grade**: the CANONICAL-REP structure, not a quotient
  (06 §7c): a `Weighted K Row` IS its canonical sorted-association
  list, with the invariant in proof fields (`sorted`, `nonzero`). Two
  equal Weighteds are EQUAL — the canonicity theorem `weightOfW_inj`
  (equal weight functions force equal canonical reps) is this file's
  teeth, and it is what lets the wire/guest/decide layers carry
  `toListW` bytes as THE representation. A quotient would erase
  exactly that rep. `ZSet α` is the ℤ SPECIALIZATION — an abbrev for
  `Weighted Int α`, not a parallel rep (the review's consolidation:
  one machinery, the general layer; the group laws ride the Int
  instance's extra structure).
- **Spine reading**: none — this is the delta substrate the spine's
  lanes ride.
- **Ladder rung**: rung 6 — `Kit.Change.Additive (ZSet α) (ZSet α)`,
  every field discharged from the group laws (mined: the legacy dbsp's
  `Dbsp/ZSet.lean` Finsupp group, PORTED FRESH as core-only — the
  mathlib weight is exactly what did NOT come over).
- **Gate rows**: the axiom report (`gates axioms` — core-triple-or-
  nothing over the law theorems) + ZSetTests' pins.

The canonical-rep shape, and why (vs the quotient — 06 §7c): keys carry
a core-only strict total order (`CanonKey`); the representation is the
sorted, zero-free, key-nodup association list, PRODUCED by every
constructor (`fromListW` canonicalizes: insert-key + coalesce + drop
zeros). The laws are proved at the weight-function level
(`weight = weightOfW ∘ rep`) and lifted by `extW` — the quotient's
extensionality, bought with one canonicity theorem instead of
quotient soundness, so the rep stays first-class for the wire.

`WKind K` bundles EXACTLY what the generic theorems need — zero/add/
mul + the zero-test the canonicalizer consumes, with the add monoid
laws and the one distributivity the join-over-union laws use. NOT a
mathlib semiring (no `one`, no `mul_assoc`/`mul_comm`, core-only).

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Kit.Change
import Kit.Correspondence

/-! ## The key ordering (core-only, minimal) -/

namespace ZSet

/-- A core-only strict total order for the canonical form's sort.
    Minimal on purpose: irrefl + trans + trichotomy + decidability are
    exactly what `weightOfW_inj` (canonicity) and `insertKeyW_sorted`
    consume. Not core's `LT` — no global-instance diamonds, and no
    mathlib `LinearOrder`. -/
class CanonKey (α : Type) where
  lt : α → α → Prop
  decLt (a b : α) : Decidable (lt a b)
  irrefl : ∀ a : α, ¬ lt a a
  trans : ∀ a b c : α, lt a b → lt b c → lt a c
  trich : ∀ a b : α, lt a b ∨ a = b ∨ lt b a

/-- Route the class's decidability through the `if` machinery. -/
instance ckDecLt [ck : CanonKey α] (a b : α) : Decidable (ck.lt a b) := ck.decLt a b

instance canonKeyNat : CanonKey Nat where
  lt := Nat.lt
  decLt := Nat.decLt
  irrefl := Nat.lt_irrefl
  trans := @Nat.lt_trans
  trich := Nat.lt_trichotomy

instance canonKeyInt : CanonKey Int where
  lt := Int.lt
  decLt := Int.decLt
  irrefl := Int.lt_irrefl
  trans := @Int.lt_trans
  trich := Int.lt_trichotomy

instance canonKeyBool : CanonKey Bool where
  lt a b := a = false ∧ b = true
  decLt a b := inferInstanceAs (Decidable (a = false ∧ b = true))
  irrefl a := by
    intro h
    cases a with
    | false => exact absurd h.2 (by decide)
    | true => exact absurd h.1 (by decide)
  trans := by
    intro a b c ha hb
    obtain ⟨ha1, ha2⟩ := ha
    subst ha1
    subst ha2
    exact absurd hb.1 (by decide)
  trich := by
    intro a b
    cases a with
    | false =>
      cases b with
      | false => exact Or.inr (Or.inl rfl)
      | true => exact Or.inl ⟨rfl, rfl⟩
    | true =>
      cases b with
      | false => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      | true => exact Or.inr (Or.inl rfl)

/-- Lexicographic product order — rows are products more often than not. -/
instance canonKeyProd [ck1 : CanonKey α] [ck2 : CanonKey β]
    [DecidableEq α] [DecidableEq β] : CanonKey (α × β) where
  lt p q := ck1.lt p.1 q.1 ∨ (p.1 = q.1 ∧ ck2.lt p.2 q.2)
  decLt p q := inferInstanceAs (Decidable (ck1.lt p.1 q.1 ∨ (p.1 = q.1 ∧ ck2.lt p.2 q.2)))
  irrefl p := by
    obtain ⟨p1, p2⟩ := p
    intro h
    rcases h with h | ⟨h1, h2⟩
    · exact ck1.irrefl p1 h
    · exact ck2.irrefl p2 h2
  trans p q r := by
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    obtain ⟨r1, r2⟩ := r
    intro hp hq
    rcases hp with hp | ⟨hp1, hp2⟩
    · rcases hq with hq | ⟨hq1, hq2⟩
      · exact Or.inl (ck1.trans p1 q1 r1 hp hq)
      · rw [hq1] at hp
        exact Or.inl hp
    · rcases hq with hq | ⟨hq1, hq2⟩
      · rw [← hp1] at hq
        exact Or.inl hq
      · rw [hq1] at hp1
        exact Or.inr ⟨hp1, ck2.trans p2 q2 r2 hp2 hq2⟩
  trich p q := by
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    rcases ck1.trich p1 q1 with h | h | h
    · exact Or.inl (Or.inl h)
    · subst h
      rcases ck2.trich p2 q2 with h2 | h2 | h2
      · exact Or.inl (Or.inr ⟨rfl, h2⟩)
      · subst h2
        exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h2⟩))
    · exact Or.inr (Or.inr (Or.inl h))

/-! ## The weight kind (the fragment's operations, bundled) -/

/-- The weight kind: what a `K`-weighted relation's algebra must
    supply (02 §4). Minimal by the generic theorem's needs: add/zero
    (union), mul (join), the Bool zero-test (the canonicalizer's
    drop-zeros), the add-monoid laws + the one distributivity pair the
    join-over-union laws use, and the zero-test's spec + the coalesce
    law (what the canonicalizer's dropped-coalesce branch consumes:
    summing to zero makes the summands cancel against any third
    weight — true for ℤ by linearity, for Nat by order, for Bool by
    the or-table). Deliberately NOT a semiring: no `one`, no
    `mul_assoc`/`mul_comm` — the fragment never needed them. -/
class WKind (K : Type) where
  zero : K
  add : K → K → K
  mul : K → K → K
  isZero : K → Bool
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  mul_add : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  add_mul : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  mul_zero : ∀ a, mul zero a = zero
  isZero_zero : isZero zero = true
  isZero_true : ∀ w, isZero w = true → w = zero
  add_cancel : ∀ a b x, isZero (add a b) = true → add (add b x) a = x

theorem add_left_comm [wk : WKind K] (a b c : K) :
    wk.add a (wk.add b c) = wk.add b (wk.add a c) := by
  rw [← WKind.add_assoc, WKind.add_comm a b, WKind.add_assoc]

/-- The monoid-closing simp set: the WKind add laws, one tool call —
    the abstract replacement for `omega` over Int sums. -/
macro "wac" : tactic =>
  `(tactic| simp only [WKind.zero_add, WKind.add_zero, WKind.add_comm,
    add_left_comm, WKind.add_assoc])

/-- ℤ — the dbsp weights (signed multiplicities, the delta rung). -/
instance wkindInt : WKind Int where
  zero := 0
  add x y := x + y
  mul x y := x * y
  isZero w := decide (w = 0)
  zero_add := by intro a; omega
  add_zero := by intro a; omega
  add_comm := by intro a b; omega
  add_assoc := by intro a b c; omega
  mul_add := Int.add_mul
  add_mul := Int.mul_add
  mul_zero := Int.zero_mul
  isZero_zero := rfl
  isZero_true := by
    intro w h
    exact of_decide_eq_true h
  add_cancel := by
    intro a b x h
    have : a + b = 0 := of_decide_eq_true h
    omega

/-- Nat — multiplicities (bags). -/
instance wkindNat : WKind Nat where
  zero := 0
  add x y := x + y
  mul x y := x * y
  isZero w := decide (w = 0)
  zero_add := by intro a; omega
  add_zero := by intro a; omega
  add_comm := by intro a b; omega
  add_assoc := by intro a b c; omega
  mul_add := Nat.add_mul
  add_mul := Nat.mul_add
  mul_zero := Nat.zero_mul
  isZero_zero := rfl
  isZero_true := by
    intro w h
    exact of_decide_eq_true h
  add_cancel := by
    intro a b x h
    have : a + b = 0 := of_decide_eq_true h
    omega

/-- Bool — membership (sets): add = or, mul = and. -/
instance wkindBool : WKind Bool where
  zero := false
  add x y := x || y
  mul x y := x && y
  isZero b := !b
  zero_add := Bool.false_or
  add_zero := Bool.or_false
  add_comm := Bool.or_comm
  add_assoc := Bool.or_assoc
  mul_add := Bool.and_or_distrib_right
  add_mul := Bool.and_or_distrib_left
  mul_zero := Bool.false_and
  isZero_zero := by simp
  isZero_true := by
    intro b h
    simpa using h
  add_cancel := by
    intro a b x h
    have hh : a = false ∧ b = false := by simpa using h
    obtain ⟨ha, hb⟩ := hh
    subst ha
    subst hb
    simp

/-- Field unfoldings the Int-level proofs route through (the instance
    is a `where`-literal; these make the delta reduction nameable). -/
theorem wkindInt_zero : wkindInt.zero = 0 := rfl
theorem wkindInt_add (a b : Int) : wkindInt.add a b = a + b := rfl
theorem wkindInt_mul (a b : Int) : wkindInt.mul a b = a * b := rfl
theorem wkindInt_isZero (w : Int) : wkindInt.isZero w = decide (w = 0) := rfl

theorem wkindNat_zero : wkindNat.zero = 0 := rfl
theorem wkindNat_add (a b : Nat) : wkindNat.add a b = a + b := rfl
theorem wkindNat_mul (a b : Nat) : wkindNat.mul a b = a * b := rfl

theorem wkindBool_zero : wkindBool.zero = false := rfl
theorem wkindBool_add (a b : Bool) : wkindBool.add a b = (a || b) := rfl
theorem wkindBool_mul (a b : Bool) : wkindBool.mul a b = (a && b) := rfl

/-! ## The sortedness invariant (weight-agnostic) -/

/-- Strictly-sorted-by-key invariant over a `K`-weighted association
    list — the canonical form's order discipline (the invariant never
    looks at the weights). -/
inductive KeySortedW [ck : CanonKey α] : List (α × K) → Prop where
  | nil : KeySortedW []
  | cons (k : α) (w : K) (r : List (α × K))
      (hlt : ∀ q ∈ r, ck.lt k q.1) (hs : KeySortedW r) : KeySortedW ((k, w) :: r)

/-! ## The weight function over an association list -/

/-- The weight of key `a` in a `K`-weighted association list: the sum
    of the weights stored at `a`. The SEMANTICS of a rep — sortedness
    is representation, this is meaning. -/
def weightOfW [wk : WKind K] [DecidableEq α] :
    List (α × K) → α → K
  | [], _ => wk.zero
  | (k, w) :: r, a => if k = a then wk.add w (weightOfW r a) else weightOfW r a

theorem weightOfW_append [wk : WKind K] [DecidableEq α]
    (xs ys : List (α × K)) (a : α) :
    weightOfW (xs ++ ys) a = wk.add (weightOfW xs a) (weightOfW ys a) := by
  induction xs with
  | nil => simp only [List.nil_append, weightOfW, WKind.zero_add]
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.cons_append, weightOfW, ih]
    by_cases hka : k = a
    · rw [if_pos hka, if_pos hka]; wac
    · rw [if_neg hka, if_neg hka]

/-- Off-support reading: keys strictly greater than `a` contribute
    nothing. -/
theorem weightOfW_gt [wk : WKind K] [ck : CanonKey α] [DecidableEq α] (a : α) :
    ∀ l : List (α × K), (∀ p ∈ l, ck.lt a p.1) → weightOfW l a = wk.zero := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p r ih =>
    intro hall
    have h1 : ck.lt a p.1 := hall p (by simp)
    have hne : ¬ (p.1 = a) := by
      intro he
      subst he
      exact ck.irrefl _ h1
    simp only [weightOfW, if_neg hne]
    exact ih (fun q hq => hall q (by simp [hq]))

/-- The rep-entry weight IS the lookup weight (the canonical rep's
    single-entry-per-key discipline). -/
theorem weightOfW_entry [wk : WKind K] [ck : CanonKey α] [DecidableEq α] :
    ∀ (l : List (α × K)), KeySortedW l → ∀ p ∈ l, weightOfW l p.1 = p.2 := by
  intro l hsorted
  induction hsorted with
  | nil => intro p hp; simp at hp
  | cons k w r hlt hs ih =>
    intro p hp
    rcases List.mem_cons.mp hp with hp0 | hp0
    · subst hp0
      show weightOfW ((k, w) :: r) k = w
      have h1 : weightOfW ((k, w) :: r) k
          = if k = k then wk.add w (weightOfW r k) else weightOfW r k := rfl
      rw [h1, if_pos rfl, weightOfW_gt k r (fun q hq => hlt q hq), WKind.add_zero]
    · have hne : ¬ (k = p.1) := fun hh => ck.irrefl p.1 (hh ▸ hlt p hp0)
      simp only [weightOfW, if_neg hne]
      exact ih p hp0

/-- The Bool zero-test's negation, as an equation (the canonicalizer's
    kept-entry shape). -/
theorem false_of_not_eq_true {b : Bool} (h : ¬ (b = true)) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd rfl h

/-! ## The canonicalizer: insert-key (sort + coalesce + drop zeros) -/

/-- Sorted insert with coalescing, generalized over the weight kind:
    keeps the list strictly sorted by key, merges weights on equal
    keys, DROPS a key whose total weight is zero (the finite-support
    discipline — zero weight = absent). -/
def insertKeyW [wk : WKind K] [ck : CanonKey α] [DecidableEq α] (k : α) (w : K) :
    List (α × K) → List (α × K)
  | [] => if wk.isZero w = true then [] else [(k, w)]
  | (k', w') :: r =>
      if k' = k then
        if wk.isZero (wk.add w w') = true then r else (k, wk.add w w') :: r
      else if ck.lt k k' then
        if wk.isZero w = true then (k', w') :: r else (k, w) :: (k', w') :: r
      else (k', w') :: insertKeyW k w r

theorem mem_insertKeyW [wk : WKind K] [ck : CanonKey α] [DecidableEq α] (k : α) (w : K) :
    ∀ (l : List (α × K)) (q : α × K), q ∈ insertKeyW k w l → q.1 = k ∨ q ∈ l := by
  intro l
  induction l with
  | nil =>
    intro q hq
    by_cases hw : wk.isZero w = true
    · rw [insertKeyW, if_pos hw] at hq
      simp at hq
    · rw [insertKeyW, if_neg hw] at hq
      rcases List.mem_singleton.mp hq with rfl
      exact Or.inl rfl
  | cons p r ih =>
    obtain ⟨k', w'⟩ := p
    intro q hq
    rw [insertKeyW] at hq
    by_cases hkk : k' = k
    · rw [if_pos hkk] at hq
      by_cases hw0 : wk.isZero (wk.add w w') = true
      · rw [if_pos hw0] at hq
        exact Or.inr (List.mem_cons_of_mem _ hq)
      · rw [if_neg hw0] at hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem _ hq)
    · rw [if_neg hkk] at hq
      by_cases hlt : ck.lt k k'
      · rw [if_pos hlt] at hq
        by_cases hw : wk.isZero w = true
        · rw [if_pos hw] at hq
          exact Or.inr hq
        · rw [if_neg hw] at hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl rfl
          · exact Or.inr hq
      · rw [if_neg hlt] at hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inr (by simp)
        · rcases ih q hq with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

/-- THE WEIGHT LEMMA: inserting respects the weight semantics —
    everything routes through this. -/
theorem insertKeyW_weight [wk : WKind K] [ck : CanonKey α] [DecidableEq α] (k : α) (w : K) :
    ∀ (l : List (α × K)) (a : α),
      weightOfW (insertKeyW k w l) a
        = wk.add (weightOfW l a) (if k = a then w else wk.zero) := by
  intro l
  induction l with
  | nil =>
    intro a
    by_cases hw : wk.isZero w = true
    · rw [insertKeyW, if_pos hw, wk.isZero_true w hw]
      simp only [weightOfW, WKind.zero_add]
      split <;> rfl
    · rw [insertKeyW, if_neg hw]
      simp only [weightOfW, WKind.zero_add]
      by_cases hka : k = a
      · rw [if_pos hka, if_pos hka, WKind.add_zero]
      · rw [if_neg hka, if_neg hka]
  | cons p r ih =>
    obtain ⟨k', w'⟩ := p
    intro a
    by_cases hkk : k' = k
    · rw [insertKeyW, if_pos hkk]
      subst hkk
      by_cases hw0 : wk.isZero (wk.add w w') = true
      · rw [if_pos hw0]
        simp only [weightOfW]
        by_cases hka : k' = a
        · simp only [if_pos hka]
          exact (wk.add_cancel w w' _ hw0).symm
        · simp only [if_neg hka, WKind.add_zero]
      · rw [if_neg hw0]
        simp only [weightOfW]
        by_cases hka : k' = a
        · simp only [if_pos hka]; wac
        · simp only [if_neg hka, WKind.add_zero]
    · rw [insertKeyW, if_neg hkk]
      by_cases hlt : ck.lt k k'
      · rw [if_pos hlt]
        by_cases hw : wk.isZero w = true
        · rw [if_pos hw, wk.isZero_true w hw]
          simp only [weightOfW]
          by_cases hka : k = a
          · simp only [if_pos hka, WKind.add_zero]
          · simp only [if_neg hka, WKind.add_zero]
        · rw [if_neg hw]
          simp only [weightOfW]
          by_cases hka : k = a
          · simp only [if_pos hka]; wac
          · simp only [if_neg hka, WKind.add_zero]
      · rw [if_neg hlt]
        simp only [weightOfW, ih]
        by_cases h1 : k' = a
        · by_cases h2 : k = a
          · simp only [if_pos h1, if_pos h2]; wac
          · simp only [if_pos h1, if_neg h2]; wac
        · by_cases h2 : k = a
          · simp only [if_neg h1, if_pos h2]
          · simp only [if_neg h1, if_neg h2]

theorem insertKeyW_sorted [wk : WKind K] [ck : CanonKey α] [DecidableEq α] (k : α) (w : K) :
    ∀ (l : List (α × K)), KeySortedW l → KeySortedW (insertKeyW k w l) := by
  intro l hs
  induction hs with
  | nil =>
    by_cases hw : wk.isZero w = true
    · rw [insertKeyW, if_pos hw]
      exact KeySortedW.nil
    · rw [insertKeyW, if_neg hw]
      exact KeySortedW.cons k w [] (by simp) KeySortedW.nil
  | cons k' w' r hlt hs ih =>
    by_cases hkk : k' = k
    · rw [insertKeyW, if_pos hkk]
      by_cases hw0 : wk.isZero (wk.add w w') = true
      · rw [if_pos hw0]
        exact hs
      · rw [if_neg hw0]
        exact KeySortedW.cons k (wk.add w w') r (hkk ▸ hlt) hs
    · rw [insertKeyW, if_neg hkk]
      by_cases hltkk : ck.lt k k'
      · rw [if_pos hltkk]
        by_cases hw : wk.isZero w = true
        · rw [if_pos hw]
          exact KeySortedW.cons k' w' r hlt hs
        · rw [if_neg hw]
          refine KeySortedW.cons k w ((k', w') :: r) ?_ (KeySortedW.cons k' w' r hlt hs)
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hltkk
          · exact ck.trans k k' q.1 hltkk (hlt q hq)
      · rw [if_neg hltkk]
        refine KeySortedW.cons k' w' _ ?_ ih
        intro q hq
        rcases mem_insertKeyW k w r q hq with h | hq
        · have hq1 : q.1 = k := h
          rcases ck.trich k' q.1 with hh | hh | hh
          · exact hh
          · exact absurd (hq1 ▸ hh) hkk
          · exact absurd (hq1 ▸ hh) hltkk
        · exact hlt q hq

theorem insertKeyW_nonzero [wk : WKind K] [ck : CanonKey α] [DecidableEq α] (k : α) (w : K) :
    ∀ (l : List (α × K)), (∀ p ∈ l, wk.isZero p.2 = false) →
      ∀ q ∈ insertKeyW k w l, wk.isZero q.2 = false := by
  intro l
  induction l with
  | nil =>
    intro hn q hq
    by_cases hw : wk.isZero w = true
    · rw [insertKeyW, if_pos hw] at hq
      simp at hq
    · rw [insertKeyW, if_neg hw] at hq
      rcases List.mem_singleton.mp hq with rfl
      exact false_of_not_eq_true hw
  | cons p r ih =>
    obtain ⟨k', w'⟩ := p
    intro hn q hq
    have hr : ∀ x ∈ r, wk.isZero x.2 = false := fun x hx => hn x (by simp [hx])
    have hhead : wk.isZero (k', w').2 = false := hn (k', w') (by simp)
    rw [insertKeyW] at hq
    by_cases hkk : k' = k
    · rw [if_pos hkk] at hq
      by_cases hw0 : wk.isZero (wk.add w w') = true
      · rw [if_pos hw0] at hq
        exact hr q hq
      · rw [if_neg hw0] at hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact (Bool.eq_false_iff).mpr hw0
        · exact hr q hq
    · rw [if_neg hkk] at hq
      by_cases hlt : ck.lt k k'
      · rw [if_pos hlt] at hq
        by_cases hw : wk.isZero w = true
        · rw [if_pos hw] at hq
          rcases List.mem_cons.mp hq with hq0 | hq
          · subst hq0
            exact hhead
          · exact hr q hq
        · rw [if_neg hw] at hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact (Bool.eq_false_iff).mpr hw
          · rcases List.mem_cons.mp hq with hq1 | hq
            · subst hq1
              exact hhead
            · exact hr q hq
      · rw [if_neg hlt] at hq
        rcases List.mem_cons.mp hq with hq0 | hq
        · subst hq0
          exact hhead
        · exact ih hr q hq

/-! ## The canonical form of a raw list -/

/-- Canonicalize a raw list: insert every entry into the sorted
    zero-free form. THE canonical-rep producer. -/
def canonW [wk : WKind K] [ck : CanonKey α] [DecidableEq α] :
    List (α × K) → List (α × K)
  | [] => []
  | p :: r => insertKeyW p.1 p.2 (canonW r)

theorem canonW_weight [wk : WKind K] [ck : CanonKey α] [DecidableEq α]
    (l : List (α × K)) (a : α) :
    weightOfW (canonW l) a = weightOfW l a := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    rw [canonW, insertKeyW_weight, ih]
    simp only [weightOfW]
    by_cases hka : k = a
    · rw [if_pos hka, if_pos hka]; wac
    · rw [if_neg hka, if_neg hka]; wac

theorem canonW_sorted [wk : WKind K] [ck : CanonKey α] [DecidableEq α]
    (l : List (α × K)) : KeySortedW (canonW l) := by
  induction l with
  | nil => exact KeySortedW.nil
  | cons p r ih =>
    rw [canonW]
    exact insertKeyW_sorted p.1 p.2 (canonW r) ih

theorem canonW_nonzero [wk : WKind K] [ck : CanonKey α] [DecidableEq α]
    (l : List (α × K)) : ∀ p ∈ canonW l, wk.isZero p.2 = false := by
  induction l with
  | nil => intro p hp; simp [canonW] at hp
  | cons p r ih =>
    rw [canonW]
    exact insertKeyW_nonzero p.1 p.2 (canonW r) (fun q hq => ih q hq)

/-! ## The weighted relation — the canonical structure -/

/-- `Weighted K Row` — the finitely-supported mapping `Row → K` (02 §4):
    a CANONICAL finite-support `K`-weight over rows. The rep is the
    sorted zero-free association list — two equal Weighteds are EQUAL
    (`extW`); the invariant rides in proof fields, so a raw literal
    with a non-canonical rep does not typecheck. `ZSet α` (below) is
    the ℤ instance's specialization: an abbrev, not a parallel rep. -/
structure Weighted (K Row : Type) [wk : WKind K] [ck : CanonKey Row]
    [DecidableEq Row] where
  rep : List (Row × K)
  sorted : KeySortedW rep
  nonzero : ∀ p ∈ rep, wk.isZero p.2 = false

variable [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row]

/-- The weight lookup — the relation's meaning (02 §4: the
    finitely-supported mapping's value at a row; the membership/weight
    lookup of the data plane: `weightW m a ≠ zero` iff `a` is
    present). -/
def weightW (m : Weighted K Row) (a : Row) : K := weightOfW m.rep a

/-- The canonical rep as data — the wire/guest form (06 §7c). -/
def toListW (m : Weighted K Row) : List (Row × K) := m.rep

/-- Build from a raw association list — CANONICALIZES (sort + coalesce
    + drop zeros). Two differently-built equal Weighteds are BEq-equal
    because both land on the same canonical rep. -/
def fromListW (l : List (Row × K)) : Weighted K Row :=
  ⟨canonW l, canonW_sorted l, canonW_nonzero l⟩

/-! ## The canonicity theorem (this file's teeth) -/

/-- Equal weight functions force equal canonical reps — the two-reps
    lemma. Key step: strict sortedness + trichotomy pins the heads; no
    cancellation is consumed, because the compared reps' off-support
    weights are LITERALLY zero (the single-summand shape), so
    `add_zero` suffices. -/
theorem weightOfW_inj {l : List (Row × K)} (hl : KeySortedW l) :
    ∀ {l' : List (Row × K)}, KeySortedW l' →
      (∀ p ∈ l, wk.isZero p.2 = false) → (∀ p ∈ l', wk.isZero p.2 = false) →
      (∀ a, weightOfW l a = weightOfW l' a) → l = l' := by
  induction hl with
  | nil =>
    intro l' hl' _ hn' h
    cases hl' with
    | nil => rfl
    | cons k' w' r' hlt' hs' =>
      exfalso
      have h1 := h k'
      simp only [weightOfW] at h1
      simp at h1
      have h2 : weightOfW r' k' = wk.zero := weightOfW_gt k' r' hlt'
      rw [h2, WKind.add_zero] at h1
      have hz := hn' (k', w') (by simp)
      rw [h1.symm, WKind.isZero_zero] at hz
      exact Bool.noConfusion hz
  | cons k w r hlt hs IH =>
    intro l' hl' hn hn' h
    cases hl' with
    | nil =>
      exfalso
      have h1 := h k
      simp only [weightOfW] at h1
      simp at h1
      have h2 : weightOfW r k = wk.zero := weightOfW_gt k r hlt
      rw [h2, WKind.add_zero] at h1
      have hz := hn (k, w) (by simp)
      rw [h1, WKind.isZero_zero] at hz
      exact Bool.noConfusion hz
    | cons k' w' r' hlt' hs' =>
      have hrk : weightOfW r k = wk.zero := weightOfW_gt k r hlt
      have hr'k : weightOfW r' k' = wk.zero := weightOfW_gt k' r' hlt'
      have hkk : k = k' := by
        rcases ck.trich k k' with hlt0 | heq | hgt
        · exfalso
          have hne : ¬ (k' = k) := by
            intro hh
            rw [hh] at hlt0
            exact ck.irrefl k hlt0
          have h1 := h k
          simp only [weightOfW] at h1
          simp at h1
          rw [if_neg hne, hrk, WKind.add_zero] at h1
          have h3 : weightOfW r' k = wk.zero :=
            weightOfW_gt k r' (fun q hq => ck.trans k k' q.1 hlt0 (hlt' q hq))
          rw [h3] at h1
          have hz := hn (k, w) (by simp)
          rw [h1, WKind.isZero_zero] at hz
          exact Bool.noConfusion hz
        · exact heq
        · exfalso
          have hne : ¬ (k = k') := by
            intro hh
            rw [hh] at hgt
            exact ck.irrefl k' hgt
          have h1 := h k'
          simp only [weightOfW] at h1
          simp at h1
          rw [if_neg hne, hr'k, WKind.add_zero] at h1
          have h3 : weightOfW r k' = wk.zero :=
            weightOfW_gt k' r (fun q hq => ck.trans k' k q.1 hgt (hlt q hq))
          rw [h3] at h1
          have hz := hn' (k', w') (by simp)
          rw [h1.symm, WKind.isZero_zero] at hz
          exact Bool.noConfusion hz
      subst hkk
      have hww : w = w' := by
        have h1 := h k
        simp only [weightOfW] at h1
        simp at h1
        rw [hrk, hr'k, WKind.add_zero, WKind.add_zero] at h1
        exact h1
      have htail : r = r' := by
        refine IH hs' (fun p hp => hn p (by simp [hp]))
          (fun p hp => hn' p (by simp [hp])) ?_
        intro a
        by_cases hka : k = a
        · subst hka
          rw [weightOfW_gt k r (by intro q hq; exact hlt q hq),
              weightOfW_gt k r' (by intro q hq; exact hlt' q hq)]
        · have h1 := h a
          simp only [weightOfW] at h1
          rw [if_neg hka, if_neg hka] at h1
          exact h1
      rw [hww, htail]

/-- Extensionality: the weight function DETERMINES the weighted
    relation (funext-free — canonicity carries it). -/
theorem extW {m n : Weighted K Row} (h : ∀ a, weightW m a = weightW n a) : m = n := by
  obtain ⟨r, hs, hn⟩ := m
  obtain ⟨r', hs', hn'⟩ := n
  have h1 : r = r' := weightOfW_inj hs hs' hn hn' h
  subst h1
  rfl

/-! ## The operators + their weight-level laws (`_ok` = 02 §4's semantics) -/

/-- The empty relation: zero weight everywhere. -/
def zeroW : Weighted K Row := fromListW []

/-- The signed-free merge — UNION ADDS weights (02 §4). -/
def addW (m n : Weighted K Row) : Weighted K Row := fromListW (m.rep ++ n.rep)

/-- The singleton: one row, one weight. -/
def singleW (k : Row) (w : K) : Weighted K Row := fromListW [(k, w)]

theorem zeroW_ok (a : Row) : weightW zeroW a = wk.zero := rfl

theorem addW_ok (m n : Weighted K Row) (a : Row) :
    weightW (addW m n) a = wk.add (weightW m a) (weightW n a) := by
  simp only [addW, fromListW, weightW, canonW_weight, weightOfW_append]

theorem addW_comm (m n : Weighted K Row) : addW m n = addW n m :=
  extW fun a => by rw [addW_ok, addW_ok]; exact WKind.add_comm _ _

theorem addW_assoc (m n p : Weighted K Row) :
    addW (addW m n) p = addW m (addW n p) :=
  extW fun a => by rw [addW_ok, addW_ok, addW_ok, addW_ok]; exact WKind.add_assoc _ _ _

theorem singleW_ok (k : Row) (w : K) (a : Row) :
    weightW (singleW k w) a = if k = a then w else wk.zero := by
  simp only [singleW, fromListW, weightW, canonW_weight, weightOfW]
  by_cases hka : k = a
  · rw [if_pos hka, if_pos hka, WKind.add_zero]
  · rw [if_neg hka, if_neg hka]

omit ck in
/-- Scale every weight by `f` of its row (join's list shape). -/
def scaleByW (f : Row → K) : List (Row × K) → List (Row × K)
  | [] => []
  | p :: r => (p.1, wk.mul p.2 (f p.1)) :: scaleByW f r

omit ck in
theorem weightOfW_scale (f : Row → K) :
    ∀ (l : List (Row × K)) (a : Row),
      weightOfW (scaleByW f l) a = wk.mul (weightOfW l a) (f a) := by
  intro l
  induction l with
  | nil => intro _; simp only [scaleByW, weightOfW, WKind.mul_zero]
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    intro a
    simp only [scaleByW, weightOfW, ih]
    by_cases hka : k = a
    · subst hka
      rw [if_pos rfl, if_pos rfl, WKind.mul_add]
    · rw [if_neg hka, if_neg hka]

/-- The natural join over rows: JOIN MULTIPLIES weights (02 §4) —
    `weightW (joinW m n) a = weightW m a * weightW n a`. Nonlinear in
    the delta sense: its INCREMENTAL form needs the cross term (03 §9
    — `Δ(A⋈B) = ΔA⋈B + A⋈ΔB + ΔA⋈ΔB`), a Change-side law that does
    not live here. -/
def joinW (m n : Weighted K Row) : Weighted K Row :=
  fromListW (scaleByW (weightW n) m.rep)

theorem joinW_ok (m n : Weighted K Row) (a : Row) :
    weightW (joinW m n) a = wk.mul (weightW m a) (weightW n a) := by
  simp only [joinW, fromListW, weightW, canonW_weight, weightOfW_scale]

/-! ## Projection sums over preimages -/

/-- Relabel rows; keep weights. -/
def relabelW (g : Row → β) : List (Row × K) → List (β × K)
  | [] => []
  | p :: r => (g p.1, p.2) :: relabelW g r

omit [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row] in
theorem relabelW_append (g : Row → β) (xs ys : List (Row × K)) :
    relabelW g (xs ++ ys) = relabelW g xs ++ relabelW g ys := by
  induction xs with
  | nil => rfl
  | cons p r ih => simp only [relabelW, List.cons_append, ih]

omit [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row] in
/-- Insertion under a relabeling: the mirrored weight lemma — the
    projection's contributions follow the canonicalizer exactly. -/
theorem weightOfW_relabel_insertKeyW (g : Row → β) (k : Row) (w : K) (b : β)
    [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row]
    [CanonKey β] [DecidableEq β] :
    ∀ l, weightOfW (relabelW g (insertKeyW k w l)) b
      = wk.add (weightOfW (relabelW g l) b) (if g k = b then w else wk.zero) := by
  intro l
  induction l with
  | nil =>
    by_cases hw : wk.isZero w = true
    · rw [insertKeyW, if_pos hw, wk.isZero_true w hw]
      simp only [relabelW, weightOfW, WKind.zero_add]
      split <;> rfl
    · rw [insertKeyW, if_neg hw]
      simp only [relabelW, weightOfW, WKind.zero_add]
      by_cases hgb : g k = b
      · rw [if_pos hgb, if_pos hgb, WKind.add_zero]
      · rw [if_neg hgb, if_neg hgb]
  | cons p r ih =>
    obtain ⟨k', w'⟩ := p
    by_cases hkk : k' = k
    · rw [insertKeyW, if_pos hkk]
      subst hkk
      by_cases hw0 : wk.isZero (wk.add w w') = true
      · rw [if_pos hw0]
        simp only [relabelW, weightOfW]
        by_cases hgb : g k' = b
        · simp only [if_pos hgb]
          exact (wk.add_cancel w w' _ hw0).symm
        · simp only [if_neg hgb, WKind.add_zero]
      · rw [if_neg hw0]
        simp only [relabelW, weightOfW]
        by_cases hgb : g k' = b
        · simp only [if_pos hgb]; wac
        · simp only [if_neg hgb, WKind.add_zero]
    · rw [insertKeyW, if_neg hkk]
      by_cases hlt : ck.lt k k'
      · rw [if_pos hlt]
        by_cases hw : wk.isZero w = true
        · rw [if_pos hw, wk.isZero_true w hw]
          simp only [relabelW, weightOfW]
          by_cases hgb : g k = b
          · simp only [if_pos hgb, WKind.add_zero]
          · simp only [if_neg hgb, WKind.add_zero]
        · rw [if_neg hw]
          simp only [relabelW, weightOfW]
          by_cases hgb : g k = b
          · simp only [if_pos hgb]; wac
          · simp only [if_neg hgb, WKind.add_zero]
      · rw [if_neg hlt]
        simp only [relabelW, weightOfW, ih]
        by_cases h1 : g k' = b
        · by_cases h2 : g k = b
          · simp only [if_pos h1, if_pos h2]; wac
          · simp only [if_pos h1, if_neg h2]; wac
        · by_cases h2 : g k = b
          · simp only [if_neg h1, if_pos h2]
          · simp only [if_neg h1, if_neg h2]

omit [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row] in
/-- The canonicalizer preserves every relabeled weight — canon then
    relabel weighs like relabel then weigh. -/
theorem weightOfW_relabel_canonW (g : Row → β) (b : β)
    [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row]
    [CanonKey β] [DecidableEq β] :
    ∀ l : List (Row × K), weightOfW (relabelW g (canonW l)) b = weightOfW (relabelW g l) b := by
  intro l
  induction l with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    have hrel := weightOfW_relabel_insertKeyW g k w b (canonW r)
    rw [canonW, hrel, ih]
    simp only [relabelW, weightOfW]
    by_cases hgb : g k = b
    · rw [if_pos hgb, if_pos hgb]; wac
    · rw [if_neg hgb, if_neg hgb, WKind.add_zero]

omit ck [DecidableEq Row] in
/-- The relabeled weight IS the preimage sum (the fold). -/
theorem weightOfW_relabel_fold [CanonKey β] [DecidableEq β] (g : Row → β)
    (l : List (Row × K)) (b : β) :
    weightOfW (relabelW g l) b
      = l.foldr (fun p acc => if g p.1 = b then wk.add p.2 acc else acc) wk.zero := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    simp only [relabelW, weightOfW, List.foldr_cons]
    split <;> rw [ih] <;> rfl

omit [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row] in
/-- Projection along `g`: weightW (projectW g m) b = the sum of m's
    weights over the preimage of `b` RESTRICTED TO THE SUPPORT (02 §4's
    projection-sums; the finite-support discipline — rows off the
    support have zero weight and contribute nothing). This is dbsp's
    `map` / the SQL projection row of the fragment. -/
def projectW [CanonKey β] [DecidableEq β] (g : Row → β)
    (m : Weighted K Row) : Weighted K β :=
  fromListW (relabelW g m.rep)

omit ck [DecidableEq Row] in
/-- The preimage sum over the support — the projection's semantics. -/
def projectWeightW [CanonKey β] [DecidableEq β] (g : Row → β)
    (m : Weighted K Row) (b : β) : K :=
  m.rep.foldr (fun p acc => if g p.1 = b then wk.add p.2 acc else acc) wk.zero

theorem projectWeightW_eq [CanonKey β] [DecidableEq β] (g : Row → β)
    (m : Weighted K Row) (b : β) :
    projectWeightW g m b = weightOfW (relabelW g m.rep) b :=
  (weightOfW_relabel_fold g m.rep b).symm

theorem projectW_ok [CanonKey β] [DecidableEq β] (g : Row → β)
    (m : Weighted K Row) (b : β) :
    weightW (projectW g m) b = projectWeightW g m b := by
  simp only [projectW, fromListW, weightW, canonW_weight]
  rw [projectWeightW_eq]

/-! ## Filter restricts, multiplicities kept -/

/-- Filter: keep the rows satisfying `p`, weights unchanged (02 §4's
    selection). -/
def filterW (p : Row → Bool) (m : Weighted K Row) : Weighted K Row :=
  fromListW (m.rep.filter (fun e => p e.1))

theorem weightOfW_filter (p : Row → Bool) :
    ∀ (l : List (Row × K)), KeySortedW l → ∀ a : Row,
      weightOfW (l.filter (fun e => p e.1)) a
        = if p a then weightOfW l a else wk.zero := by
  intro l hsorted
  induction hsorted with
  | nil =>
    intro a
    simp only [List.filter_nil, weightOfW]
    split <;> rfl
  | cons k w r hlt hs ih =>
    intro a
    simp only [List.filter_cons]
    by_cases hpa : p k = true
    · rw [if_pos hpa]
      simp only [weightOfW, ih]
      by_cases hka : k = a
      · subst hka
        simp only [if_pos hpa]
      · simp only [if_neg hka]
    · rw [if_neg hpa]
      simp only [weightOfW, ih]
      by_cases hka : k = a
      · subst hka
        simp only [if_neg hpa]
      · simp only [if_neg hka]

theorem filterW_ok (p : Row → Bool) (m : Weighted K Row) (a : Row) :
    weightW (filterW p m) a = if p a then weightW m a else wk.zero := by
  simp only [filterW, fromListW, weightW, canonW_weight]
  exact weightOfW_filter p m.rep m.sorted a

/-! ## The linear family (`_linear`: the incrementalization licenses) -/

/-- Filter is linear: filtering a union is the union of the filters
    (the operator's own incremental form — no old state needed). -/
theorem filterW_add (p : Row → Bool) (m n : Weighted K Row) :
    filterW p (addW m n) = addW (filterW p m) (filterW p n) := by
  apply extW
  intro a
  simp only [filterW_ok, addW_ok]
  by_cases hpa : p a = true
  · simp only [if_pos hpa]
  · simp only [if_neg hpa, WKind.add_zero]

/-- Projection is linear: projecting a union is the union of the
    projections (the projection's homomorphism law over union-adds). -/
theorem projectW_add [CanonKey β] [DecidableEq β] (g : Row → β) (m n : Weighted K Row) :
    projectW g (addW m n) = addW (projectW g m) (projectW g n) := by
  apply extW
  intro b
  simp only [projectW_ok, addW_ok, projectWeightW_eq]
  rw [show (addW m n).rep = canonW (m.rep ++ n.rep) from rfl,
      weightOfW_relabel_canonW g b, relabelW_append, weightOfW_append]

/-- Join is BILINEAR over union (the `_linear` family's join mark):
    joining a union on the left is the union of the joins. The DELTA
    form needs the cross term (03 §9) — a Change-side law, not this
    file's. -/
theorem joinW_add_left (m n p : Weighted K Row) :
    joinW (addW m n) p = addW (joinW m p) (joinW n p) := by
  apply extW
  intro a
  simp only [joinW_ok, addW_ok]
  exact WKind.mul_add _ _ _

theorem joinW_add_right (m n p : Weighted K Row) :
    joinW m (addW n p) = addW (joinW m n) (joinW m p) := by
  apply extW
  intro a
  simp only [joinW_ok, addW_ok]
  exact WKind.add_mul _ _ _

/-! ## The ℤ surface: `ZSet α := Weighted Int α` (the thin specialization) -/

/-! The review's consolidation: ONE machinery — the general
    `Weighted K Row` layer above — with the ℤ surface as THIN
    specializations over it. The type is the specialization (an
    abbrev); every general law specializes definitionally; only the
    group laws (which need negation, more than `WKind` supplies) are
    stated at the Int level, riding the general carrier + the
    `wkindInt` instance's extra structure. No parallel rep. -/

variable [ck : CanonKey α] [DecidableEq α]

/-- The Z-set over `α`: the ℤ instance of the weighted-relation layer
    — `Weighted Int α` by definition. The delta ladder's top rung's
    canonical occupant (01 §2): signed multiplicities with the
    canonical-rep discipline inherited from the general layer. -/
abbrev ZSet (α : Type) [CanonKey α] [DecidableEq α] : Type := Weighted Int α

/-- The weight lookup — the Z-set's meaning (`weight m a ≠ 0` iff `a`
    is present). -/
abbrev weight (m : ZSet α) (a : α) : Int := weightW m a

/-- The canonical rep as data — the wire/guest form (06 §7c). -/
abbrev toList (m : ZSet α) : List (α × Int) := m.rep

/-- Build from a raw association list — CANONICALIZES (sort + coalesce
    + drop zeros). Two differently-built equal ZSets are BEq-equal
    because both land on the same canonical rep. -/
abbrev fromList (l : List (α × Int)) : ZSet α := fromListW l

/-- The empty Z-set: zero weight everywhere. -/
abbrev zero : ZSet α := zeroW

/-- The signed merge — the additive rung's operation. Commutative,
    associative, with `neg` as the inverse; NOT idempotent (03 §7:
    signed addition is not idempotent, net-zero ≠ nothing happened). -/
abbrev add (m n : ZSet α) : ZSet α := addW m n

/-- The inverse — rollback at the Z-set rung. Int-level (negation is
    the group structure `WKind` deliberately lacks). -/
abbrev neg (m : ZSet α) : ZSet α := fromListW (m.rep.map (fun p => (p.1, -p.2)))

/-- The natural join over keys: `weight (join m n) a = weight m a *
    weight n a` (02 §4's join-multiplies). The general `joinW` served
    directly — the specialization is definitional. Nonlinear by
    construction — its INCREMENTAL form needs the cross term (03 §9),
    a Change-side law, not this file's. -/
abbrev join (m n : ZSet α) : ZSet α := joinW m n

/-- Projection along `f` (02 §4's projection-sums over preimages).
    The general `projectW` served directly. -/
abbrev project [CanonKey β] [DecidableEq β] (f : α → β) (m : ZSet α) : ZSet β :=
  projectW f m

omit [ck : CanonKey α] [DecidableEq α] in
/-- The Int-level pointwise-negation lemma (the group's extra
    structure: `WKind` has no neg, so this rides the Int instance). -/
theorem weightOfW_neg [DecidableEq α] (l : List (α × Int)) (a : α) :
    weightOfW (l.map (fun p => (p.1, -p.2))) a = -weightOfW l a := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨k, w⟩ := p
    simp only [List.map_cons, weightOfW]
    split <;> simp only [ih, wkindInt_add] <;> omega

/-- Extensionality in the ℤ surface's `weight` form — the general
    `extW` served directly (the specialization is definitional). -/
theorem ext {m n : ZSet α} (h : ∀ a, weight m a = weight n a) : m = n := extW h

/-! ## The group laws (the Additive instance's fields) -/

theorem weight_zero (a : α) : weight zero a = 0 := rfl

theorem weight_add (m n : ZSet α) (a : α) :
    weight (add m n) a = weight m a + weight n a :=
  addW_ok m n a

theorem weight_neg (m : ZSet α) (a : α) : weight (neg m) a = -weight m a := by
  simp only [weight, neg, fromListW, weightW, canonW_weight, weightOfW_neg]

theorem zero_add (m : ZSet α) : add zero m = m :=
  ext fun a => by rw [weight_add, weight_zero]; omega

theorem add_zero (m : ZSet α) : add m zero = m :=
  ext fun a => by rw [weight_add, weight_zero]; omega

theorem add_comm (m n : ZSet α) : add m n = add n m :=
  ext fun a => by rw [weight_add, weight_add]; omega

theorem add_assoc (m n p : ZSet α) : add (add m n) p = add m (add n p) :=
  ext fun a => by rw [weight_add, weight_add, weight_add, weight_add]; omega

theorem add_neg (m : ZSet α) : add m (neg m) = zero :=
  ext fun a => by rw [weight_add, weight_neg, weight_zero]; omega

theorem neg_add (m : ZSet α) : add (neg m) m = zero :=
  ext fun a => by rw [weight_add, weight_neg, weight_zero]; omega

/-- The applied-cancel helper the `roundTrip` field needs. -/
theorem add_add_neg (m d : ZSet α) : add (add m d) (neg d) = m := by
  rw [add_assoc, add_neg, add_zero]

/-- Signed addition is NOT idempotent (03 §7) — the honest non-law:
    `add d d = zero` forces `d = zero`. -/
theorem add_self_eq_zero (d : ZSet α) (h : add d d = zero) : d = zero := by
  apply ext
  intro a
  have hw := weight_add d d a
  rw [h, weight_zero] at hw
  rw [weight_zero]
  omega

/-! ## Ergonomic instances + decidable equality -/

instance : Add (ZSet α) := ⟨add⟩
instance : Neg (ZSet α) := ⟨neg⟩

/-- Rep-level Bool equality (decides rep equality through the
    `DecidableEq`-routed decidables). -/
def repBEq [DecidableEq α] : List (α × Int) → List (α × Int) → Bool
  | [], [] => true
  | (k, w) :: r, (k', w') :: r' =>
      decide (k = k') && (decide (w = w') && repBEq r r')
  | _, _ => false

omit [ck : CanonKey α] [DecidableEq α] in
theorem repBEq_refl [DecidableEq α] : ∀ l : List (α × Int), repBEq l l = true
  | [] => rfl
  | (k, w) :: r => by simp [repBEq, repBEq_refl r]

omit [ck : CanonKey α] [DecidableEq α] in
theorem repBEq_eq [DecidableEq α] : ∀ {l l' : List (α × Int)}, repBEq l l' = true → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [repBEq] at h
  | _ :: _, [], h => by simp [repBEq] at h
  | (k, w) :: r, (k', w') :: r', h => by
      obtain ⟨h1, h23⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨h2, h3⟩ := Bool.and_eq_true_iff.mp h23
      have hk : k = k' := of_decide_eq_true h1
      have hw : w = w' := of_decide_eq_true h2
      subst hk
      subst hw
      exact congrArg (List.cons (k, w)) (repBEq_eq h3)

instance : BEq (ZSet α) := ⟨fun m n => repBEq m.rep n.rep⟩

/-- BEq is faithful: BEq-equal ZSets are equal (hence same weights). -/
theorem eq_of_beq {m n : ZSet α} (h : m == n) : m = n := by
  apply ext
  intro a
  show weightOfW m.rep a = weightOfW n.rep a
  rw [repBEq_eq h]

/-! ## The Kit.Change.Additive instance (the ladder's top rung) -/

/-- The delta-as-state application: a Z-set applies to a Z-set by
    signed merge, total (always `some`) — the degenerate honest Option,
    exactly like `Kit.intAdd`. -/
def zsetApply (s d : ZSet α) : Option (ZSet α) := some (add s d)

/-- The delta ladder's top rung's canonical occupant (01 §2, 02 §4):
    every lower rung's fields discharge from the group laws; the
    additive rung adds ONLY the commutativity + the compose-level
    inverse laws (no parallel `add` — the dupDefBodies lesson). -/
-- `Kit.Additive` is a structure, not a class — the instance is a def,
-- consumed explicitly like `Kit.intAdd`.
def zsetAdditive : Kit.Additive (ZSet α) (ZSet α) where
  apply := zsetApply
  compose := add
  assoc := add_assoc
  applyCompose := by
    intro s a b
    simp only [zsetApply, Option.bind_some, Option.some.injEq]
    exact (add_assoc s a b).symm
  nop := zero
  composeNopLeft := zero_add
  composeNopRight := add_zero
  applyNop := by
    intro s
    simp only [zsetApply, Option.some.injEq]
    exact add_zero s
  inv := neg
  roundTrip := by
    intro s d s' h
    have hs' : s' = add s d := by cases h; rfl
    subst hs'
    simp only [zsetApply, Option.some.injEq]
    exact add_add_neg s d
  Disjoint _ _ := True
  commute := by
    intro s a b _
    simp only [zsetApply, Option.bind_some, Option.some.injEq]
    rw [add_assoc, add_assoc, add_comm a b]
  composeComm := add_comm
  invLeft := neg_add
  invRight := add_neg
/-! ## THE GRADUATION (16-surface §5.1, 15-patterns #11): the canonical
    rep ≅ the weight function -/

/- The landed hard half: `weightOfW_inj` (canonicity — equal weight
    functions force equal canonical reps) + `extW`. The graduation
    assembles them into the correspondence VALUE between `Weighted K
    Row` and the finitely-supported weight functions.

    Carrier shape (the honest core-only finiteness): a finitely-
    supported weight function carries its canonical rep AS DATA — the
    rep IS the support's finiteness witness (sorted, zero-free, and
    weighing exactly the function). A Type-valued iso cannot eliminate
    a Prop: the pure `{f // finite support}` subtype would need the rep
    extracted from a Prop `∃`, so the witness rides in the type. The
    canonicity is what makes this carrier equivalent to the pure
    function reading: the rep is DETERMINED by the function
    (`weightOfW_inj`), so carrying it adds no information — the two
    round trips close by `rfl`/`funext`, never by choice. -/

/-- The finitely-supported weight function, with its canonical rep as
    the support's finiteness witness. -/
def FinSupFn (K Row : Type) [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row] : Type :=
  {fx : (Row → K) × List (Row × K) //
    KeySortedW fx.2 ∧ (∀ p ∈ fx.2, wk.isZero p.2 = false)
      ∧ ∀ a, weightOfW fx.2 a = fx.1 a}

/-- THE GRADUATION'S VALUE: the canonical reps ≅ the finitely-supported
    weight functions. `to` reads the weight function off the rep (the
    rep rides along as the support's witness); `inv` reassembles the
    `Weighted` from the carried rep — no canonicalization, no choice.
    `to_inv`'s function leg is the carried rep's own weight law;
    `inv_to` is structure-eta. The LOSSLESS claim — the function
    determines the rep — is `weightOfW_inj`/`extW`, pinned in the
    tests. -/
def weightFnIso {K Row : Type} [wk : WKind K] [ck : CanonKey Row] [DecidableEq Row] :
    Kit.Iso (Weighted K Row) (FinSupFn K Row) where
  to m := ⟨(weightW m, m.rep), m.sorted, m.nonzero, fun _ => rfl⟩
  inv fx := ⟨fx.1.2, fx.2.1, fx.2.2.1⟩
  to_inv fx := by
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · apply funext
      intro a
      show weightW (⟨fx.1.2, fx.2.1, fx.2.2.1⟩ : Weighted K Row) a = fx.1.1 a
      exact fx.2.2.2 a
    · rfl
  inv_to m := rfl

end ZSet
