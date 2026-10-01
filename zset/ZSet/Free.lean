/-
# ZSet.Free — THE UNIVERSAL PROPERTY (T3): the Z-set is the free abelian group

Owned by: the ZSet agent (the mandate tree, `zset/`).

The Z-set's capstone: `ZSet α` is the FREE abelian group on `α` — the
weight-preserving maps on the generators (assignments `α → M` into an
additive target) are in bijection with the homomorphisms out of
`ZSet α` (`homIso`, the ONE object), via the EXTENSION (`lift`): a
generator assignment extends UNIQUELY to a hom. The faithfulness half
(two homs agreeing on the generators are equal) rides the
canonical-rep discipline — `extW`, whose teeth are `weightOfW_inj`
(ZSet.Basic); the existence half is the signed fold over the canonical
rep.

THE CHANGE LADDER AS THE VARIETIES DISCIPLINE (comment-level tie; the
theorem below is the prize): the weight kinds are the VARIETIES of the
one weighted-relation semantics (02 §4) — `Bool` weights = sets (the
idempotent variety: `add` is `or`, `add d d = d`), `Nat` weights =
bags (the commutative-monoid variety), `Int` weights = abelian groups
(the delta rung, 03 §7's signed merges). Each rung of the Change
ladder (`Kit.Change`'s Applicable → … → Additive) admits exactly the
variety its algebra supports; the free-object universal property —
THE theorem here — lands at the TOP rung only, because freeness needs
inverses (a "free commutative monoid" statement would be a DIFFERENT
universal property, and the Nat-weighted layer carries its own, honest,
weaker lifts). Nothing is collapsed across the rungs.

The five questions:
- **Root**: Change (01 §2) — the top rung's universal property; the
  target `M` is any `Kit.Additive M M` carrier (the abelian-group rung
  consumed explicitly, never assumed as a mathlib class).
- **Carrier grade**: the extension rides the canonical rep (the rep IS
  the finite-support discipline); the faithfulness is `extW`/
  `weightOfW_inj` — no new representation, no quotient.
- **Spine reading**: none — a substrate theorem; the machine/observer
  lanes' delta faces instantiate it.
- **Ladder rung**: rung 6's capstone — the hom structure + the
  extension + the uniqueness (hand theorems over the canonical fold;
  the Int-action bookkeeping is the group-law rearrangement family of
  01 §7).
- **Gate rows**: the axiom report (the decl-count drift at the wave's
  commit) + ZSetTests' pins (positive + the mandatory negative
  control: a non-additive candidate fails the hom law).

Core-only: no mathlib, no Batteries (the cone rule).
-/
module

public import ZSet.Basic
@[expose] public section


namespace ZSet

variable {α : Type} [ck : CanonKey α] [DecidableEq α]

/-! ## The group bookkeeping (the target's Kit.Additive laws) -/

section GroupLaws

variable {M : Type} (g : Kit.Additive M M)

/-- The cancel-and-shift rearrangement (01 §7's small generic hand
    lemma; the machines' `Machines.compose_inv_cancel` is the same
    shape at its own carrier — re-proved here, since the zset cone
    cannot import machines). -/
theorem gCancel (x y : M) : g.compose (g.compose x y) (g.inv x) = y := by
  rw [g.composeComm (g.compose x y) (g.inv x), ← g.assoc, g.invLeft,
    g.composeNopLeft]

/-- Uniqueness of the inverse: anything composing with `x` to the
    no-op IS the inverse. -/
theorem eq_inv_of_compose_nop (y x : M) (h : g.compose y x = g.nop) :
    y = g.inv x := by
  rw [← g.composeNopRight y, ← g.invRight x, ← g.assoc, h, g.composeNopLeft]

/-- The inverse of a composite is the (commuted) composite of the
    inverses — the abelian group's anti-automorphism face. -/
theorem inv_compose (a b : M) :
    g.inv (g.compose a b) = g.compose (g.inv a) (g.inv b) := by
  symm
  exact eq_inv_of_compose_nop g (g.compose (g.inv a) (g.inv b)) (g.compose a b)
    (by rw [g.assoc, g.composeComm a b, ← g.assoc (g.inv b) b a, g.invLeft b,
      g.composeNopLeft a, g.invLeft a])

end GroupLaws

/-! ## The integer action on an additive target -/

section Action

variable {M : Type}

/-- The iterated compose: the n-fold sum's positive face, with the
    no-op as the zero iterate. -/
def iterCompose (g : Kit.Additive M M) : Nat → M → M
  | 0, _ => g.nop
  | k + 1, x => g.compose x (iterCompose g k x)

/-- The INTEGER ACTION: `w • x` — signed. A Z-set's weight `w` at a
    key carries to `w •` the generator's value; this is the scalar
    face the free abelian group's maps need. -/
def zAction (g : Kit.Additive M M) (w : Int) (x : M) : M :=
  match w with
  | Int.ofNat k => iterCompose g k x
  | Int.negSucc k => g.inv (iterCompose g (k + 1) x)

theorem iterCompose_succ (g : Kit.Additive M M) (k : Nat) (x : M) :
    iterCompose g (k + 1) x = g.compose x (iterCompose g k x) := rfl

theorem zAction_ofNat (g : Kit.Additive M M) (k : Nat) (x : M) :
    zAction g (Int.ofNat k) x = iterCompose g k x := rfl

theorem zAction_ofNat' (g : Kit.Additive M M) (k : Nat) (x : M) :
    zAction g (NatCast.natCast k) x = iterCompose g k x := rfl

theorem zAction_negSucc (g : Kit.Additive M M) (k : Nat) (x : M) :
    zAction g (Int.negSucc k) x = g.inv (iterCompose g (k + 1) x) := rfl

theorem zAction_zero (g : Kit.Additive M M) (x : M) :
    zAction g 0 x = g.nop := rfl

theorem zAction_one (g : Kit.Additive M M) (x : M) :
    zAction g 1 x = x := by
  show iterCompose g 1 x = x
  rw [iterCompose_succ g]
  exact g.composeNopRight x

/-- The iterates split over the added counts. -/
theorem iterCompose_add (g : Kit.Additive M M) (a b : Nat) (x : M) :
    iterCompose g (a + b) x
      = g.compose (iterCompose g a x) (iterCompose g b x) := by
  induction a with
  | zero =>
      rw [Nat.zero_add, show iterCompose g 0 x = g.nop from rfl,
        g.composeNopLeft]
  | succ a ih =>
      rw [show a + 1 + b = a + b + 1 from by omega, iterCompose_succ g, ih,
        iterCompose_succ g, g.assoc]

/-- THE INTEGER ACTION IS AN ACTION (the additive face):
    `(a + b) • x = a • x + b • x`. The mixed-sign cases are where the
    abelian structure earns its keep (cancellation + inverse
    uniqueness + the anti-automorphism). -/
theorem zAction_add (g : Kit.Additive M M) (a b : Int) (x : M) :
    zAction g (a + b) x = g.compose (zAction g a x) (zAction g b x) := by
  cases a with
  | ofNat m =>
      cases b with
      | ofNat n =>
          show iterCompose g (m + n) x
            = g.compose (iterCompose g m x) (iterCompose g n x)
          exact iterCompose_add g m n x
      | negSucc n =>
          -- ofNat m + negSucc n = subNatNat m (n + 1)
          show zAction g (Int.subNatNat m (n + 1)) x
            = g.compose (iterCompose g m x)
                (g.inv (iterCompose g (n + 1) x))
          rcases Nat.lt_or_ge m (n + 1) with hlt | hge
          · -- lands negative: subNatNat m (n+1) = negSucc (n - m)
            rw [Int.subNatNat_of_lt hlt]
            have hpred : Nat.pred ((n + 1) - m) = n - m := by
              have h1 : (n + 1) - m = (n - m) + 1 := by omega
              rw [h1, Nat.add_one, Nat.pred_succ]
            rw [hpred, zAction_negSucc]
            have hsplit : n + 1 = m + (n - m + 1) := by omega
            rw [hsplit, iterCompose_add g m (n - m + 1) x,
              inv_compose g (iterCompose g m x)
                (iterCompose g (n - m + 1) x), ← g.assoc, g.invRight,
              g.composeNopLeft]
          · -- lands positive: subNatNat m (n+1) = ofNat (m - (n+1))
            rw [Int.subNatNat_of_le hge, zAction_ofNat']
            have key : iterCompose g m x
                = g.compose (iterCompose g (n + 1) x)
                    (iterCompose g (m - (n + 1)) x) := by
              have hm : m = (n + 1) + (m - (n + 1)) := by omega
              conv => lhs; rw [hm]
              rw [iterCompose_add g]
            rw [key, gCancel g (iterCompose g (n + 1) x)
              (iterCompose g (m - (n + 1)) x)]
  | negSucc m =>
      cases b with
      | ofNat n =>
          -- negSucc m + ofNat n = subNatNat n (m + 1)
          show zAction g (Int.subNatNat n (m + 1)) x
            = g.compose (g.inv (iterCompose g (m + 1) x))
                (iterCompose g n x)
          rcases Nat.lt_or_ge n (m + 1) with hlt | hge
          · -- lands negative: subNatNat n (m+1) = negSucc (m - n)
            rw [Int.subNatNat_of_lt hlt]
            have hpred : Nat.pred ((m + 1) - n) = m - n := by
              have h1 : (m + 1) - n = (m - n) + 1 := by omega
              rw [h1, Nat.add_one, Nat.pred_succ]
            rw [hpred, zAction_negSucc]
            have hsplit : m + 1 = n + (m - n + 1) := by omega
            rw [hsplit, iterCompose_add g n (m - n + 1) x,
              inv_compose g (iterCompose g n x)
                (iterCompose g (m - n + 1) x),
              g.composeComm (g.inv (iterCompose g n x))
                (g.inv (iterCompose g (m - n + 1) x)), g.assoc,
              g.invLeft, g.composeNopRight]
          · -- lands positive: subNatNat n (m+1) = ofNat (n - (m+1))
            rw [Int.subNatNat_of_le hge, zAction_ofNat']
            have key : iterCompose g n x
                = g.compose (iterCompose g (m + 1) x)
                    (iterCompose g (n - (m + 1)) x) := by
              have hn : n = (m + 1) + (n - (m + 1)) := by omega
              conv => lhs; rw [hn]
              rw [iterCompose_add g]
            rw [key, ← g.assoc, g.invLeft, g.composeNopLeft]
      | negSucc n =>
          -- negSucc m + negSucc n = negSucc (m + n + 1)
          show zAction g (Int.negSucc (m + n + 1)) x
            = g.compose (g.inv (iterCompose g (m + 1) x))
                (g.inv (iterCompose g (n + 1) x))
          rw [zAction_negSucc]
          have hsplit : (m + 1) + (n + 1) = m + n + 1 + 1 := by omega
          rw [← hsplit, iterCompose_add g, inv_compose g]

end Action

/-! ## The canonical fold + the extension -/

section Lift

variable {M : Type}

omit ck [DecidableEq α] in
/-- The canonical fold: the signed sum over an association list —
    each entry contributes `zAction g w (f k)`, folded on the left of
    the accumulator. -/
def repFold (g : Kit.Additive M M) (f : α → M) (l : List (α × Int)) : M :=
  l.foldr (fun p acc => g.compose (zAction g p.2 (f p.1)) acc) g.nop

/-- The lift of a generator assignment: the canonical fold over the
    Z-set's rep. -/
def liftFun (g : Kit.Additive M M) (f : α → M) (m : ZSet α) : M :=
  repFold g f m.rep

omit ck [DecidableEq α] in
/-- The fold splits over appends (no commutativity needed — the foldr
    shape carries it). -/
theorem repFold_append (g : Kit.Additive M M) (f : α → M)
    (xs ys : List (α × Int)) :
    repFold g f (xs ++ ys) = g.compose (repFold g f xs) (repFold g f ys) := by
  induction xs with
  | nil => exact (g.composeNopLeft _).symm
  | cons p r ih =>
      show g.compose (zAction g p.2 (f p.1)) (repFold g f (r ++ ys))
        = g.compose (g.compose (zAction g p.2 (f p.1)) (repFold g f r))
            (repFold g f ys)
      rw [ih, g.assoc]

/-- THE FOLD LEMMA: the canonicalizer's every branch is fold-honest —
    inserting `(k, w)` shifts the fold by exactly `zAction g w (f k)`.
    This is where the abelian structure earns its keep: the REORDER
    branch (the insert lands after the head) needs `composeComm`. -/
theorem repFold_insertKeyW (g : Kit.Additive M M) (f : α → M) (k : α) (w : Int) :
    ∀ l : List (α × Int), repFold g f (insertKeyW k w l)
      = g.compose (zAction g w (f k)) (repFold g f l) := by
  intro l
  induction l with
  | nil =>
      rw [insertKeyW]
      by_cases h0 : w = 0
      · rw [if_pos (by rw [wkindInt_isZero, h0]; rfl), h0, zAction_zero g]
        exact (g.composeNopLeft _).symm
      · rw [if_neg (by rw [wkindInt_isZero, decide_eq_true_eq]; exact h0)]
        rfl
  | cons p r ih =>
      obtain ⟨k', w'⟩ := p
      rw [insertKeyW]
      by_cases hkk : k' = k
      · rw [if_pos hkk, hkk]
        by_cases hw0 : wkindInt.isZero (wkindInt.add w w') = true
        · have hsum0 : w + w' = 0 := of_decide_eq_true hw0
          rw [if_pos hw0]
          show repFold g f r
            = g.compose (zAction g w (f k))
                (g.compose (zAction g w' (f k)) (repFold g f r))
          rw [← g.assoc, ← zAction_add g, hsum0, zAction_zero g,
            g.composeNopLeft]
        · rw [if_neg hw0]
          show g.compose (zAction g (w + w') (f k)) (repFold g f r)
            = g.compose (zAction g w (f k))
                (g.compose (zAction g w' (f k)) (repFold g f r))
          rw [← g.assoc, ← zAction_add g]
      · rw [if_neg hkk]
        by_cases hlt : ck.lt k k'
        · rw [if_pos hlt]
          by_cases hw : wkindInt.isZero w = true
          · rw [if_pos hw]
            have h0 : w = 0 := of_decide_eq_true hw
            rw [h0, zAction_zero g, g.composeNopLeft]
          · rw [if_neg hw]
            rfl
        · rw [if_neg hlt]
          show g.compose (zAction g w' (f k'))
              (repFold g f (insertKeyW k w r))
            = g.compose (zAction g w (f k)) (repFold g f ((k', w') :: r))
          rw [ih, ← g.assoc, g.composeComm (zAction g w' (f k'))
            (zAction g w (f k)), g.assoc]
          rfl

/-- The canonical form is fold-invisible: the fold reads the WEIGHT
    function, not the list order (`canonW_weight`'s face at the
    fold). -/
theorem repFold_canonW (g : Kit.Additive M M) (f : α → M) (l : List (α × Int)) :
    repFold g f (canonW l) = repFold g f l := by
  induction l with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨k, w⟩ := p
      show repFold g f (insertKeyW k w (canonW r)) = repFold g f ((k, w) :: r)
      rw [repFold_insertKeyW, ih]
      rfl

/-! ## The canonical reps are the fold's fixed points -/

/-- Insert into a sorted zero-free list with all keys above `k`: the
    entry goes on the head (the canonical rep is the fold's fixed
    point — the canonicity discipline's small tooth). -/
theorem insertKeyW_self (k : α) (w : Int) (hw : wkindInt.isZero w = false) :
    ∀ l : List (α × Int), KeySortedW l → (∀ q ∈ l, wkindInt.isZero q.2 = false) →
      (∀ q ∈ l, ck.lt k q.1) → insertKeyW k w l = (k, w) :: l := by
  intro l hsorted
  induction hsorted with
  | nil => intro _ _; rw [insertKeyW, if_neg (Bool.eq_false_iff.mp hw)]
  | cons k' w' r hlt hs =>
      intro hnon hgt
      have hkk : ck.lt k k' := hgt (k', w') (by simp)
      have hne : ¬ (k' = k) := by
        intro he
        rw [he] at hkk
        exact ck.irrefl k hkk
      rw [insertKeyW, if_neg hne, if_pos hkk,
        if_neg (Bool.eq_false_iff.mp hw)]

/-- The canonicalizer fixes canonical reps (sorted + zero-free). -/
theorem canonW_self : ∀ l : List (α × Int), KeySortedW l →
    (∀ p ∈ l, wkindInt.isZero p.2 = false) → canonW l = l := by
  intro l hsorted
  induction hsorted with
  | nil => intro _; rfl
  | cons k w r hlt hs ih =>
      intro hnon
      rw [canonW, ih (fun q hq => hnon q (by simp [hq]))]
      exact insertKeyW_self k w (hnon (k, w) (by simp)) r hs
        (fun q hq => hnon q (by simp [hq])) hlt

/-! ## The homomorphisms out of the Z-set -/

/-- A homomorphism out of `ZSet α` into an additive target: preserves
    the no-op and the signed merge. (The single structure — no parallel
    `map` operations: the dupDefBodies lesson.) -/
structure Hom (α : Type) [ck : CanonKey α] [DecidableEq α] (M : Type) (g : Kit.Additive M M) where
  toFun : ZSet α → M
  map_zero : toFun zero = g.nop
  map_add : ∀ m n : ZSet α, toFun (add m n) = g.compose (toFun m) (toFun n)

section HomLaws

variable {M : Type} (g : Kit.Additive M M)

/-- Homs are determined by their underlying function (the law fields
    are Props — proof irrelevance carries the construction). -/
theorem Hom.ext {h₁ h₂ : Hom α M g}
    (h : ∀ m : ZSet α, h₁.toFun m = h₂.toFun m) : h₁ = h₂ := by
  cases h₁ with
  | mk f₁ z₁ a₁ =>
  cases h₂ with
  | mk f₂ z₂ a₂ =>
  have hf : f₁ = f₂ := funext h
  subst hf
  rfl

/-- Homs preserve the inverse (derived: the group laws force it —
    "inverses derived only where lawful", the Additive rung's own
    rule). -/
theorem Hom.map_neg (h : Hom α M g) (m : ZSet α) :
    h.toFun (neg m) = g.inv (h.toFun m) := by
  apply eq_inv_of_compose_nop g
  rw [← h.map_add (neg m) m, neg_add, h.map_zero]

/-! ## The iterated-add face (the generator's Nat face) -/

/-- The n-fold signed merge of `m` with itself (the positive
    multiples). -/
def iterAdd (m : ZSet α) : Nat → ZSet α
  | 0 => zero
  | n + 1 => add m (iterAdd m n)

/-- The weightW-headed singleton lemma (the fold-level proofs' face —
    `singleW_ok` is `weightW`-stated; the `weight` surface's lemmas do
    not pattern-match against `weightW` goals). -/
theorem singleW_weight (k : α) (w : Int) (a : α) :
    weightW (singleW k w) a = if k = a then w else 0 := singleW_ok k w a

/-- The weightW-headed negation lemma (`weight_neg`'s fold-level
    face). -/
theorem weightW_neg (m : ZSet α) (a : α) :
    weightW (neg m) a = -weightW m a := weight_neg m a

/-- The n-fold merge of the unit generator is the weight-n singleton
    (weights: `n` at `k`, else zero). -/
theorem singleW_iterAdd (k : α) (n : Nat) :
    iterAdd (singleW k 1) n = singleW k (Int.ofNat n) := by
  induction n with
  | zero =>
      apply extW
      intro a
      rw [singleW_weight]
      split <;> rfl
  | succ n ih =>
      rw [iterAdd, ih]
      apply extW
      intro a
      rw [addW_ok, singleW_weight, singleW_weight, singleW_weight,
        wkindInt_add, show Int.ofNat (n + 1) = Int.ofNat n + 1 from rfl]
      by_cases hka : k = a
      · rw [if_pos hka, if_pos hka, if_pos hka]
        omega
      · rw [if_neg hka, if_neg hka, if_neg hka]
        rfl

/-- Homs push the n-fold merge to the n-fold compose. -/
theorem Hom.iterAdd (h : Hom α M g) (n : Nat) (m : ZSet α) :
    h.toFun (iterAdd m n) = iterCompose g n (h.toFun m) := by
  induction n with
  | zero => exact h.map_zero
  | succ n ih =>
      show h.toFun (add m (ZSet.iterAdd m n))
        = iterCompose g (n + 1) (h.toFun m)
      rw [h.map_add, ih]
      exact (iterCompose_succ g n (h.toFun m)).symm

/-- THE GENERATOR LAW: every hom's value on a singleton is the integer
    action on its weight-1 value — a hom is WEIGHT-PRESERVING. -/
theorem Hom.singleW_zAction (h : Hom α M g) (k : α) (w : Int) :
    h.toFun (singleW k w) = zAction g w (h.toFun (singleW k 1)) := by
  cases w with
  | ofNat n =>
      rw [← singleW_iterAdd, h.iterAdd, zAction_ofNat g]
  | negSucc n =>
      have hsn : singleW k (Int.negSucc n)
          = neg (singleW k (Int.ofNat (n + 1))) := by
        apply extW
        intro a
        rw [weightW_neg, singleW_weight, singleW_weight,
          show Int.ofNat (n + 1) = Int.ofNat n + 1 from rfl]
        by_cases hka : k = a
        · rw [if_pos hka, if_pos hka]
          rfl
        · rw [if_neg hka, if_neg hka]
          rfl
      rw [hsn, h.map_neg, ← singleW_iterAdd, h.iterAdd, zAction_negSucc g]

/-! ## The raw-list reconstruction -/

/-- Two raw builds with the head entry split off agree in weight — the
    singleton-merge face of the canonicalizer (`canonW_weight`). -/
theorem fromListW_cons (k : α) (w : Int) (l : List (α × Int)) :
    fromListW ((k, w) :: l) = add (singleW k w) (fromListW l) := by
  apply extW
  intro a
  show weightW (fromListW ((k, w) :: l)) a
    = weightW (addW (singleW k w) (fromListW l)) a
  rw [addW_ok, singleW_weight,
    show weightW (fromListW ((k, w) :: l)) a
      = weightOfW (canonW ((k, w) :: l)) a from rfl,
    show weightW (fromListW l) a = weightOfW (canonW l) a from rfl,
    canonW_weight, canonW_weight]
  simp only [weightOfW, wkindInt_add]
  split <;> omega

/-- Every hom IS the canonical fold of its own generator restriction —
    the reconstruction lemma (the singleton law carries each entry;
    the induction is over the RAW list, the canonicalizer's honesty is
    `canonW_weight`). -/
theorem Hom.fold_lift (h : Hom α M g) :
    ∀ l : List (α × Int),
      h.toFun (fromListW l) = repFold g (fun k => h.toFun (singleW k 1)) l := by
  intro l
  induction l with
  | nil => exact h.map_zero
  | cons p r ih =>
      obtain ⟨k, w⟩ := p
      rw [fromListW_cons, h.map_add, Hom.singleW_zAction, ih]
      rfl

/-! ## THE EXTENSION -/

/-- **THE EXTENSION** (the universal property's existence half): a
    generator assignment `f : α → M` extends to a hom — the canonical
    fold. THE UNIVERSAL PROPERTY of the free abelian group (T3). -/
def lift (g : Kit.Additive M M) (f : α → M) : Hom α M g where
  toFun := liftFun g f
  map_zero := rfl
  map_add := by
    intro m n
    show repFold g f (add m n).rep
      = g.compose (repFold g f m.rep) (repFold g f n.rep)
    rw [show (add m n).rep
          = canonW ((m.rep : List (α × Int)) ++ n.rep) from rfl,
      repFold_canonW g f, repFold_append g f]

/-- THE WEIGHT PRESERVATION: the extension maps the weight-`w`
    singleton to `w • f k` — the generators' weights survive. -/
theorem lift_single (g : Kit.Additive M M) (f : α → M) (k : α) (w : Int) :
    (lift g f).toFun (singleW k w) = zAction g w (f k) := by
  show repFold g f (insertKeyW k w ([] : List (α × Int))) = zAction g w (f k)
  rw [repFold_insertKeyW g f]
  exact g.composeNopRight _

/-- Every hom IS the lift of its own generator restriction — the
    extension's UNIQUENESS at the function level. -/
theorem Hom.eq_lift (h : Hom α M g) :
    h.toFun = liftFun g (fun k => h.toFun (singleW k 1)) := by
  funext m
  have hrepx : fromListW (m.rep : List (α × Int)) = m := by
    simp only [fromListW, canonW_self m.rep m.sorted m.nonzero]
  rw [← hrepx, Hom.fold_lift (g := g) (h := h) m.rep]
  rw [show liftFun g (fun k => h.toFun (singleW k 1)) (fromListW (m.rep : List (α × Int)))
        = repFold g (fun k => h.toFun (singleW k 1))
            (canonW (m.rep : List (α × Int))) from rfl,
    repFold_canonW g (fun k => h.toFun (singleW k 1)) m.rep]

/-- **FAITHFULNESS** (the universal property's uniqueness half): two
    homs agreeing on the weight-1 generators are EQUAL. The
    canonical-rep discipline's `weightOfW_inj` (via `extW`) IS the
    faithfulness — the rep is determined by the weight function, so
    the hom is determined by the generators. -/
theorem Hom.ext_single (h₁ h₂ : Hom α M g)
    (h : ∀ k, h₁.toFun (singleW k 1) = h₂.toFun (singleW k 1)) : h₁ = h₂ := by
  refine Hom.ext (g := g) (h₁ := h₁) (h₂ := h₂) fun m => ?_
  rw [Hom.eq_lift (g := g) (h := h₁), Hom.eq_lift (g := g) (h := h₂),
    funext h]

end HomLaws

end Lift

/-! ## THE UNIVERSAL PROPERTY — the one object -/

/-- **THE UNIVERSAL PROPERTY** (T3): the homs out of `ZSet α` ≅ the
    generator assignments — `ZSet α` is the FREE abelian group on α.
    `to` restricts a hom to the weight-1 generators; `inv` is the
    extension (`lift`). `to_inv` is the weight preservation
    (`lift_single`); `inv_to` is the reconstruction (`Hom.eq_lift`,
    riding the canonical-rep discipline — `weightOfW_inj`'s
    faithfulness). -/
def homIso (g : Kit.Additive M M) : Kit.Iso (Hom α M g) (α → M) where
  to h := fun k => h.toFun (singleW k 1)
  inv f := lift g f
  to_inv f := funext fun k => by
    rw [lift_single, zAction_one]
  inv_to h := (Hom.ext (g := g) (h₁ := h)
    (h₂ := lift g fun k => h.toFun (singleW k 1))
    fun m => congrFun (Hom.eq_lift (g := g) (h := h)) m).symm

end ZSet

end -- public section
