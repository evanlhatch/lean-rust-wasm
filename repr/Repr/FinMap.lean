/-
# Repr.FinMap — the worked example: ONE abstract structure, TWO
# honestly different representations

The discipline's proof that it pays (the reviews' §2, steps 1-5 all
exercised):

1. **The simple mathematical spec**: the finitely-supported map as a
   PURE FUNCTION `Abs K V := K → Option V` — the zset discipline's
   face (the abstract carrier is the function, never a representation
   of it), with `insert`/`delete` as the token-indexed abstract steps.
2. **The efficient executable implementations**: TWO, honestly
   different —
   - `SortedAssoc`: the sorted (strictly ascending) association list —
     the canonical-rep discipline (ZSet's `Weighted` face); insert
     CANONICALIZES (insort), the invariant `Asc` rides the type as a
     proof field.
   - `RawAssoc`: the UNSORTED-with-duplicates list — the write log
     (insert appends, lookup reads the LAST binding); no canonical
     form is maintained, duplicates and order carry no meaning.
3. **The representation relation** (ONE relation shape for both):
   pointwise lookup agreement — `∀ k, lookup l k = a k`. The relation
   is LEFT-UNIQUE in the abstract argument (the concrete state
   determines the map) — the property `Repr.no_ignore_step`'s teeth
   consume.
4. **The operation-correctness theorems**: `lookupS_insort`,
   `lookupS_deleteS`, `lookupR_insertR`, `lookupR_deleteR` — each
   representation's steps proved to preserve the relation, pointwise,
   by induction.
5. **The generic client theorem exercised over both**: `sortedRep` and
   `rawRep` are `Repr.Represents` instances; `Repr.client_obs` comes
   FREE for each, and `client_cross` gives the cross-rep agreement
   (same program, same observation) with no new proof.

The non-iso honesty (the grade discipline): the two representations
are NOT isomorphic to the abstract map and not to each other.
- the SORTED rep earns the canonicity face: `canonicity` — two
  ascending lists with the same lookup function are THE SAME LIST —
  the abstraction is injective on the sorted rep (`toAbsS_inj`, the
  retraction-grade face; the `Kit.Retraction` structure itself is
  deliberately NOT claimed — the abstract side is ALL functions
  `K → Option V`, and only the finitely-supported ones have reps).
- the RAW rep earns the Abstraction grade ONLY: `raw_not_injective` —
  duplicates and order are meaning-free, so distinct raw lists
  represent the same map and NO inverse exists. `rawAbstraction`
  bundles it as a `Kit.Abstraction` (sound, deliberately not exact).

The construction gate's teeth, instantiated: `sorted_ignore_step` and
`raw_ignore_step` — a concrete step that ignores an operation cannot
bundle (`Repr.no_ignore_step`).

The five questions (notes/v3/01-core.md):
- root: Universe — the carriers are finite data; the abstract carrier
  is the function's initial-algebra reading; the Change face (the
  token program) rides `Repr.Represents`.
- carrier grade: the split the doctrine demands — sorted = canonicity
  (the retraction FACE, injectivity on the rep), raw = `Kit.Abstraction`
  (over, never exact). The Iso is claimed NOWHERE.
- spine reading: none — the lanes' finite-map-shaped states are the
  consumers.
- ladder rung: hand theorems of the small generic kind (01 §7) —
  the preservation lemmas are one induction each; the text-proof
  discipline is respected (the tokens are pairs, the char level is
  TextKit's, no string reductions).
- gate row: Repr's row in Gates.Packages' gated set; ReprTests.Axioms
  pins the laws' cones (core triple only).

Core-only: no mathlib, no Batteries (the cone rule). `MapKey` rides
`ZSet.CanonKey` — the key class landed ONCE, in the honest home (the
canonical-rep machinery that consumes it); `MapKey` extends it with
the one field the two-rep lane needs beyond the order (key decEq) and
Repr imports ZSet.Basic cone-legally (both C1 — the cone table's rows;
the old deliberate-parallel note was the consolidation debt, paid).
-/
module

public import Kit.Relation
public import Kit.Correspondence
public import ZSet.Basic
public import Repr.Basic
@[expose] public section


namespace Repr

/-! ## The keys (core-only decidable strict total order) -/

/-- The sorted rep's key class: ZSet.CanonKey (the order + its
    decidability — landed ONCE in the canonical-rep machinery) plus the
    one field the two-rep lane needs beyond the order: the KEY
    equality's decidability (the abstract steps' `if k = k'` route).
    The parent's order fields are inherited, never re-stated — the
    partial consolidation's whole point. -/
class MapKey (K : Type) extends ZSet.CanonKey K where
  decEq (a b : K) : Decidable (a = b)

/-- Route the class's equality decidability through the `if`
    machinery (the ONLY `Decidable (a = b)` instance the lane uses —
    no second route, no diamond). The ORDER fields route through the
    parent (`MapKey.toCanonKey.lt` at the use sites — Lean 4.33
    generates no projection constant for an `extends` field, and the
    flattened field name is not user-definable); the route is the
    citation, not a re-statement: the order's laws are CanonKey's,
    proved once in the canonical-rep machinery. -/
instance MapKey.decEqRoute [MapKey K] (a b : K) : Decidable (a = b) :=
  MapKey.decEq a b

instance mapKeyNat : MapKey Nat where
  toCanonKey := ZSet.canonKeyNat
  decEq := Nat.decEq

/-! ## 1. The simple mathematical spec: the finitely-supported map -/

/-- THE abstract carrier: the map as a pure function (the zset
    discipline's face — never a representation of itself). -/
def Abs (K V : Type) := K → Option V

/-- The empty map. -/
def Abs.empty (K V : Type) : Abs K V := fun _ => none

/-- The abstract insert. -/
def Abs.step [DecidableEq K] (k : K) (v : V) (m : Abs K V) : Abs K V :=
  fun k' => if k = k' then some v else m k'

/-- The abstract delete. -/
def Abs.del [DecidableEq K] (k : K) (m : Abs K V) : Abs K V :=
  fun k' => if k = k' then none else m k'

/-- THE operation tokens: the client interface's steps. -/
inductive Op (K V : Type) where
  | insert : K → V → Op K V
  | delete : K → Op K V
  deriving BEq

/-- The abstract step family. -/
def stepAbs [DecidableEq K] : Op K V → Abs K V → Abs K V
  | .insert k v, m => m.step k v
  | .delete k, m => m.del k

/-! ## 2a. The sorted representation (the canonical-rep discipline) -/

/-- Strictly ascending keys — sortedness AND key-nodup in ONE
    predicate (a repeated key would violate `lt`'s irreflexivity). -/
inductive Asc [MapKey K] : List (K × V) → Prop where
  | nil : Asc []
  | single (k : K) (v : V) : Asc [(k, v)]
  | cons {k1 : K} {v1 : V} {k2 : K} {v2 : V} {tl : List (K × V)}
      (hlt : MapKey.toCanonKey.lt k1 k2) (hrest : Asc ((k2, v2) :: tl)) :
      Asc ((k1, v1) :: (k2, v2) :: tl)

theorem Asc.head [MapKey K] {k1 : K} {v1 : V} {k2 : K} {v2 : V}
    {tl : List (K × V)} (h : Asc ((k1, v1) :: (k2, v2) :: tl)) :
    MapKey.toCanonKey.lt k1 k2 := by
  cases h with
  | cons hlt _ => exact hlt

theorem Asc.tail [MapKey K] {k1 : K} {v1 : V} {k2 : K} {v2 : V}
    {tl : List (K × V)} (h : Asc ((k1, v1) :: (k2, v2) :: tl)) :
    Asc ((k2, v2) :: tl) := by
  cases h with
  | cons _ hrest => exact hrest

/-- Replacing the head's VALUE preserves the invariant (only keys
    matter to `Asc`). -/
theorem Asc.replace_head [MapKey K] {k : K} {w w' : V}
    {tl : List (K × V)} (h : Asc ((k, w) :: tl)) : Asc ((k, w') :: tl) := by
  cases tl with
  | nil => exact Asc.single k w'
  | cons _ _ => exact Asc.cons (Asc.head h) (Asc.tail h)

/-- The sorted rep's carrier: the list + the invariant as a proof
    field (the ZSet.Weighted shape — the invariant in proof fields,
    not a quotient). -/
structure SortedAssoc (K V : Type) [MapKey K] where
  list : List (K × V)
  asc : Asc list

/-- The sorted rep's lookup: the linear scan (first binding wins —
    and `Asc` makes first = only). -/
def lookupS [MapKey K] : List (K × V) → K → Option V
  | [], _ => none
  | (k2, v2) :: tl, k => if k = k2 then some v2 else lookupS tl k

/-- The sorted rep's insert: CANONICALIZING (insort — the
    canonicalization differs from the raw rep's append; THE honest
    difference between the two representations). -/
def insort [MapKey K] (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | (k2, v2) :: tl =>
      if k = k2 then (k, v) :: tl
      else if MapKey.toCanonKey.lt k k2 then (k, v) :: (k2, v2) :: tl
      else (k2, v2) :: insort k v tl

/-- The sorted rep's delete. -/
def deleteS [MapKey K] (k : K) : List (K × V) → List (K × V)
  | [] => []
  | (k2, v2) :: tl => if k = k2 then tl else (k2, v2) :: deleteS k tl

/-! ### the invariant's machinery -/

theorem asc_tail [MapKey K] {k : K} {v : V} {t : List (K × V)}
    (h : Asc ((k, v) :: t)) : Asc t := by
  cases t with
  | nil => exact Asc.nil
  | cons _ _ => exact Asc.tail h

theorem lookupS_nil [MapKey K] {V : Type _} (k : K) :
    lookupS [] k = (none : Option V) := rfl

theorem lookupS_cons [MapKey K] (k2 : K) (v2 : V) (tl : List (K × V)) (k : K) :
    lookupS ((k2, v2) :: tl) k = if k = k2 then some v2 else lookupS tl k :=
  rfl

/-- A key strictly below every key present is absent. -/
theorem lookupS_absent [MapKey K] :
    ∀ (l : List (K × V)) (k : K), (∀ p : K × V, p ∈ l → MapKey.toCanonKey.lt k p.1) →
      lookupS l k = none := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons p tl ih =>
      obtain ⟨k3, v3⟩ := p
      intro k h
      have h3 : MapKey.toCanonKey.lt k k3 := h (k3, v3) (by simp)
      rw [lookupS_cons, if_neg (fun hEq => MapKey.toCanonKey.irrefl k3 (by
        rw [hEq] at h3; exact h3))]
      exact ih k (fun p' hp => h p' (List.mem_cons_of_mem _ hp))

/-- Every key in an ascending list's tail strictly exceeds the head. -/
theorem asc_mem_gt [MapKey K] :
    ∀ (tl : List (K × V)) (k2 : K) (v2 : V) (p : K × V),
      Asc ((k2, v2) :: tl) → p ∈ tl → MapKey.toCanonKey.lt k2 p.1 := by
  intro tl
  induction tl with
  | nil => intro k2 v2 p _ hmem; exact absurd hmem List.not_mem_nil
  | cons p3 tl3 ih =>
      intro k2 v2 p h hmem
      obtain ⟨k3, v3⟩ := p3
      rcases List.mem_cons.1 hmem with h5 | h5
      · rw [h5]; exact Asc.head h
      · exact MapKey.toCanonKey.trans k2 k3 p.1 (Asc.head h) (ih k3 v3 p (Asc.tail h) h5)

/-! ### the invariant's preservation -/

/-- Inserting a key STRICTLY GREATER than the head keeps the head in
    place (the insort induction's helper). -/
theorem insort_cons_gt [MapKey K] (k : K) (v : V) :
    ∀ (h : K) (w : V) (l : List (K × V)), MapKey.toCanonKey.lt h k →
      Asc ((h, w) :: l) → Asc ((h, w) :: insort k v l) := by
  intro h w l
  induction l generalizing h w with
  | nil => intro hlt _; rw [insort]; exact Asc.cons hlt (Asc.single k v)
  | cons p tl ih =>
      obtain ⟨k4, v4⟩ := p
      intro hlt hAsc
      rw [insort]
      split
      · next hEq =>   -- k = k4; result (k, v) :: tl
          rw [hEq] at hlt ⊢
          exact Asc.cons hlt (Asc.replace_head (Asc.tail hAsc))
      · next hEq =>   -- ¬(k = k4)
          split
          · next hlt2 =>   -- k < k4; result (k, v) :: (k4, v4) :: tl
              exact Asc.cons hlt (Asc.cons hlt2 (Asc.tail hAsc))
          · next hgt2 =>   -- k4 < k; result (k4, v4) :: insort k v tl
              have hgk4 : MapKey.toCanonKey.lt k4 k := by
                rcases MapKey.toCanonKey.trich k k4 with h5 | h5' | h5
                · exact absurd h5 hgt2
                · exact absurd h5' hEq
                · exact h5
              exact Asc.cons (Asc.head hAsc)
                (ih k4 v4 hgk4 (Asc.tail hAsc))

/-- Insert preserves the invariant. -/
theorem insort_asc [MapKey K] (k : K) (v : V) :
    ∀ l : List (K × V), Asc l → Asc (insort k v l) := by
  intro l
  induction l with
  | nil => intro _; exact Asc.single k v
  | cons p tl ih =>
      intro h
      obtain ⟨k2, v2⟩ := p
      rw [insort]
      split
      · next hEq =>   -- k = k2; goal : Asc ((k, v) :: tl)
          rw [hEq]
          exact Asc.replace_head h
      · next hEq =>   -- ¬(k = k2)
          split
          · next hlt =>   -- k < k2
              exact Asc.cons hlt h
          · next hgt =>   -- k2 < k (trichotomy through the two refusals)
              have hgk : MapKey.toCanonKey.lt k2 k := by
                rcases MapKey.toCanonKey.trich k k2 with h | h' | h
                · exact absurd h hgt
                · exact absurd h' hEq
                · exact h
              exact insort_cons_gt k v k2 v2 tl hgk h

/-- Deleting from an ascending list keeps ANY strictly-smaller head
    in place (the delete induction's helper). -/
theorem deleteS_under [MapKey K] (k : K) :
    ∀ (l : List (K × V)) (h2 : K) (w2 : V),
      Asc l → (∀ p : K × V, p ∈ l → MapKey.toCanonKey.lt h2 p.1) →
        Asc ((h2, w2) :: deleteS k l) := by
  intro l
  induction l with
  | nil => intro h2 w2 _ _; exact Asc.single h2 w2
  | cons p3 tl3 ih =>
      obtain ⟨k3, v3⟩ := p3
      intro h2 w2 hAsc hall
      rw [deleteS]
      split
      · next hEq =>   -- k = k3 : the result is JUST the tail (the head's
          -- binding is the only one deleted — the recursive call only
          -- happens in the else branch)
          cases tl3 with
          | nil => exact Asc.single h2 w2
          | cons p4 tl4 =>
              obtain ⟨k4, v4⟩ := p4
              exact Asc.cons (hall (k4, v4) (by simp)) (Asc.tail hAsc)
      · next hEq =>   -- k ≠ k3
          exact Asc.cons (hall (k3, v3) (by simp))
            (ih k3 v3 (asc_tail hAsc)
              (fun p hp => asc_mem_gt tl3 k3 v3 p hAsc hp))

/-- Delete preserves the invariant. -/
theorem deleteS_asc [MapKey K] (k : K) :
    ∀ l : List (K × V), Asc l → Asc (deleteS k l) := by
  intro l
  induction l with
  | nil => intro _; exact Asc.nil
  | cons p tl ih =>
      intro h
      obtain ⟨k2, v2⟩ := p
      rw [deleteS]
      split
      · next hEq =>   -- k = k2; goal : Asc tl
          exact asc_tail h
      · next hEq =>   -- ¬(k = k2); goal : Asc ((k2, v2) :: deleteS k tl)
          exact deleteS_under k tl k2 v2 (asc_tail h)
            (fun p hp => asc_mem_gt tl k2 v2 p h hp)

/-! ### 4. the operation-correctness theorems, sorted face -/

/-- THE sorted insert's correctness: the pointwise agreement with the
    abstract insert (step 4, sorted face). Holds for ARBITRARY lists —
    no invariant needed. -/
theorem lookupS_insort [MapKey K] (k : K) (v : V) :
    ∀ (l : List (K × V)) (k' : K),
      lookupS (insort k v l) k' = if k = k' then some v else lookupS l k' := by
  intro l
  induction l with
  | nil =>
      intro k'
      rw [insort, lookupS_cons]
      by_cases hEq : k = k'
      · rw [if_pos hEq.symm, if_pos hEq]
      · rw [if_neg (fun (h5 : k' = k) => hEq h5.symm), if_neg hEq]
  | cons p tl ih =>
      obtain ⟨k2, v2⟩ := p
      intro k'
      rw [insort]
      split
      · next hEq =>   -- k = k2
          rw [hEq, lookupS_cons, lookupS_cons]
          by_cases hk' : k' = k2
          · rw [if_pos hk', if_pos hk'.symm]
          · rw [if_neg hk', if_neg (fun (h5 : k2 = k') => hk' h5.symm),
              if_neg hk']
      · next hEq =>   -- ¬(k = k2)
          split
          · next hlt =>   -- k < k2
              rw [lookupS_cons, lookupS_cons]
              by_cases hk' : k' = k
              · rw [if_pos hk', if_pos hk'.symm]
              · rw [if_neg hk', if_neg (fun (h5 : k = k') => hk' h5.symm)]
          · next hgt =>   -- k2 < k
              have hgk : MapKey.toCanonKey.lt k2 k := by
                rcases MapKey.toCanonKey.trich k k2 with h | h' | h
                · exact absurd h hgt
                · exact absurd h' hEq
                · exact h
              simp only [lookupS_cons, lookupS_cons, ih k']
              by_cases hk2 : k' = k2
              · rw [if_pos hk2]
                by_cases hk' : k = k'
                · exact absurd (hk'.trans hk2) hEq
                · rw [if_neg hk', if_pos hk2]
              · rw [if_neg hk2]
                by_cases hk' : k = k'
                · rw [if_pos hk', if_pos hk']
                · rw [if_neg hk', if_neg hk', if_neg hk2]

/-- THE sorted delete's correctness: the pointwise agreement with the
    abstract delete (step 4, sorted face). Needs the invariant —
    delete removes THE binding, and `Asc` promises there is only one. -/
theorem lookupS_deleteS [MapKey K] (k : K) :
    ∀ (l : List (K × V)) (_ : Asc l) (k' : K),
      lookupS (deleteS k l) k' = if k = k' then none else lookupS l k' := by
  intro l
  induction l with
  | nil =>
      intro _ k'
      rw [deleteS, lookupS_nil]
      by_cases hEq : k = k'
      · rw [if_pos hEq]
      · rw [if_neg hEq]
  | cons p tl ih =>
      obtain ⟨k2, v2⟩ := p
      intro h k'
      rw [deleteS]
      split
      · next hEq =>   -- k = k2
          rw [hEq]
          by_cases hk2 : k2 = k'
          · rw [if_pos hk2, ← hk2]
            exact lookupS_absent tl k2
              (fun p5 hp5 => asc_mem_gt tl k2 v2 p5 h hp5)
          · rw [if_neg hk2, lookupS_cons,
              if_neg (fun (h5 : k' = k2) => hk2 h5.symm)]
      · next hEq =>   -- ¬(k = k2)
          rw [lookupS_cons, lookupS_cons]
          by_cases hk2 : k' = k2
          · rw [hk2, if_neg (fun (h5 : k = k2) => hEq h5)]
            simp
          · rw [if_neg hk2, ih (asc_tail h) k', if_neg hk2]

/-! ## 2b. The raw representation (unsorted, duplicates, last-wins) -/

/-- The raw rep's carrier: the plain pair list — unsorted, duplicates
    allowed (abbrev: the representation is the LIST, no wrapper). -/
abbrev RawAssoc (K V : Type) := List (K × V)

/-- The folded lookup from an arbitrary accumulator: the
    last-binding-wins discipline (a later binding of the key wins, an
    absent key keeps the accumulator) — the generalization the delete
    proofs consume. -/
def lookupFrom [DecidableEq K] (acc : Option V) (l : RawAssoc K V) (k : K) :
    Option V :=
  l.foldl (fun a p => if p.1 = k then some p.2 else a) acc

/-- The raw rep's lookup: the log read from the start, the LAST
    binding winning (the write log's semantics). -/
def lookupR [DecidableEq K] (l : RawAssoc K V) (k : K) : Option V :=
  lookupFrom none l k

/-- The raw rep's insert: APPEND (the write log — the canonicalization
    differs from the sorted rep's insort; THE honest difference). -/
def insertR [DecidableEq K] (k : K) (v : V) (l : RawAssoc K V) : RawAssoc K V :=
  l ++ [(k, v)]

/-- The raw rep's delete: remove EVERY binding of the key. -/
def deleteR [DecidableEq K] (k : K) : RawAssoc K V → RawAssoc K V
  | [] => []
  | (k2, v2) :: tl => if k2 = k then deleteR k tl else (k2, v2) :: deleteR k tl

/-- The raw rep's step family. -/
def rawStep [DecidableEq K] : Op K V → RawAssoc K V → RawAssoc K V
  | .insert k v, l => insertR k v l
  | .delete k, l => deleteR k l

theorem lookupFrom_cons [DecidableEq K] (acc : Option V) (p : K × V)
    (tl : RawAssoc K V) (k' : K) :
    lookupFrom acc (p :: tl) k' =
      lookupFrom (if p.1 = k' then some p.2 else acc) tl k' :=
  rfl

theorem lookupR_nil [DecidableEq K] {V : Type _} (k' : K) :
    lookupR [] k' = (none : Option V) := rfl

/-! ### 4. the operation-correctness theorems, raw face -/

/-- THE raw insert's correctness: appending the binding gives the
    abstract insert, pointwise (step 4, raw face). -/
theorem lookupR_insertR [DecidableEq K] (k : K) (v : V) (l : RawAssoc K V)
    (k' : K) :
    lookupR (insertR k v l) k' = if k = k' then some v else lookupR l k' := by
  have base : ∀ (l : RawAssoc K V) (acc : Option V) (k' : K),
      lookupFrom acc (l ++ [(k, v)]) k' =
        if k = k' then some v else lookupFrom acc l k' := by
    intro l
    induction l with
    | nil => intro acc k'; rfl
    | cons p tl ih =>
        obtain ⟨k2, v2⟩ := p
        intro acc k'
        rw [List.cons_append, lookupFrom_cons, ih, lookupFrom_cons]
  simp only [lookupR]
  exact base l none k'

/-- Deleting the key's bindings never disturbs a lookup of THAT key:
    the folded lookup holds its accumulator. -/
theorem lookupFrom_deleteR_self [DecidableEq K] (k : K) :
    ∀ (l : RawAssoc K V) (acc : Option V),
      lookupFrom acc (deleteR k l) k = acc := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p tl ih =>
      obtain ⟨k2, v2⟩ := p
      intro acc
      rw [deleteR]
      split
      · next hEq =>   -- k2 = k : the head's binding is the key's — dropped
          exact ih acc
      · next hEq =>   -- ¬(k2 = k) : head kept, accumulator unchanged
          rw [lookupFrom_cons, if_neg hEq, ih]

/-- Deleting the key's bindings never disturbs a lookup of any OTHER
    key. -/
theorem lookupFrom_deleteR_ne [DecidableEq K] (k k' : K) (hkk : k' ≠ k) :
    ∀ (l : RawAssoc K V) (acc : Option V),
      lookupFrom acc (deleteR k l) k' = lookupFrom acc l k' := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p tl ih =>
      obtain ⟨k2, v2⟩ := p
      intro acc
      rw [deleteR]
      split
      · next hEq =>   -- k2 = k : head dropped
          rw [ih, lookupFrom_cons,
            if_neg (fun h5 => hkk (h5.symm.trans hEq))]
      · next hEq =>   -- ¬(k2 = k) : head kept
          rw [lookupFrom_cons, ih, lookupFrom_cons]

/-- THE raw delete's correctness: removing every binding of the key
    gives the abstract delete, pointwise (step 4, raw face). -/
theorem lookupR_deleteR [DecidableEq K] (k : K) (l : RawAssoc K V) (k' : K) :
    lookupR (deleteR k l) k' = if k = k' then none else lookupR l k' := by
  simp only [lookupR]
  by_cases hEq : k = k'
  · rw [if_pos hEq, ← hEq, lookupFrom_deleteR_self k l none]
  · rw [if_neg hEq, lookupFrom_deleteR_ne k k' (fun h5 => hEq h5.symm) l none]

/-! ## 3. The representation relations + THE instances -/

/-- The pointwise-lookup relation is left-unique in the abstract
    argument — the concrete state determines the map (the property the
    construction gate's teeth consume). -/
theorem det_of_pointwise {K V : Type} {C : Type} (lk : C → K → Option V)
    (c : C) (a a' : K → Option V) (h1 : ∀ k, lk c k = a k)
    (h2 : ∀ k, lk c k = a' k) : a = a' :=
  funext fun k => (h1 k).symm.trans (h2 k)

/-- The sorted rep's relation: pointwise lookup agreement. -/
def RSorted [MapKey K] (c : SortedAssoc K V) (a : Abs K V) : Prop :=
  ∀ k, lookupS c.list k = a k

/-- The raw rep's relation: the SAME shape, the other carrier — one
    relation discipline, two representations. -/
def RRaw [DecidableEq K] (c : RawAssoc K V) (a : Abs K V) : Prop :=
  ∀ k, lookupR c k = a k

/-- The sorted rep's abstraction: the map the list determines. -/
def toAbsS [MapKey K] (s : SortedAssoc K V) : Abs K V := lookupS s.list

/-- The raw rep's abstraction. -/
def toAbsR [DecidableEq K] (l : RawAssoc K V) : Abs K V := lookupR l

/-- The sorted rep's step. -/
def sortedStep [MapKey K] : Op K V → SortedAssoc K V → SortedAssoc K V
  | .insert k v, s => ⟨insort k v s.list, insort_asc k v s.list s.asc⟩
  | .delete k, s => ⟨deleteS k s.list, deleteS_asc k s.list s.asc⟩

/-- THE sorted instance (the discipline's steps 1-4 bundled): the
    canonical-rep representation of the finite map. -/
def sortedRep [MapKey K] :
    Represents (Op K V) (Abs K V) (SortedAssoc K V) (Abs K V) where
  R := RSorted
  initA := Abs.empty K V
  stepA := stepAbs
  obsA := id
  initC := ⟨[], Asc.nil⟩
  stepC := sortedStep
  obsC := toAbsS
  pres_init := fun _ => rfl
  pres_step := by
    intro t c a h
    cases t with
    | insert k v =>
        intro k'
        show lookupS (insort k v c.list) k' = Abs.step k v a k'
        simp only [Abs.step]
        rw [lookupS_insort, h k']
    | delete k =>
        intro k'
        show lookupS (deleteS k c.list) k' = Abs.del k a k'
        simp only [Abs.del]
        rw [lookupS_deleteS k c.list c.asc k', h k']
  pres_obs := fun _ _ h => funext h

/-- THE raw instance: the unsorted-with-duplicates representation. -/
def rawRep [DecidableEq K] :
    Represents (Op K V) (Abs K V) (RawAssoc K V) (Abs K V) where
  R := RRaw
  initA := Abs.empty K V
  stepA := stepAbs
  obsA := id
  initC := []
  stepC := rawStep
  obsC := toAbsR
  pres_init := fun _ => rfl
  pres_step := by
    intro t c a h
    cases t with
    | insert k v =>
        intro k'
        show lookupR (insertR k v c) k' = Abs.step k v a k'
        simp only [Abs.step]
        rw [lookupR_insertR, h k']
    | delete k =>
        intro k'
        show lookupR (deleteR k c) k' = Abs.del k a k'
        simp only [Abs.del]
        rw [lookupR_deleteR, h k']
  pres_obs := fun _ _ h => funext h

/-! ## 5. The client theorem's instances -/

/-- The client theorem's CROSS-REP instance, free: the same program on
    both representations gives the same observation
    (`Repr.crossRep_obs` — the shared abstract interface matched
    definitionally). THE two representations' agreement, as a theorem.
    (`MapKey K` alone: the lane's single decidability route keeps the
    two reps' step families THE SAME function, definitionally.) -/
theorem client_cross [MapKey K] (p : List (Op K V)) :
    toAbsS (runC sortedRep p sortedRep.initC) =
      toAbsR (runC rawRep p rawRep.initC) :=
  crossRep_obs sortedRep rawRep rfl rfl rfl p

/-! ## The non-iso honesty (the grade discipline) -/

/-- THE canonicity theorem (the sorted rep's upgrade face): two
    ascending lists with the same lookup function are THE SAME LIST.
    The sorted rep's abstraction is injective — this is what the raw
    rep can never have (`raw_not_injective` is its exact negation's
    witness). -/
theorem canonicity [MapKey K] : ∀ (l1 l2 : List (K × V)),
    Asc l1 → Asc l2 → (∀ k, lookupS l1 k = lookupS l2 k) → l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 _ h2 h
      cases l2 with
      | nil => rfl
      | cons q t2 =>
          obtain ⟨k2, v2⟩ := q
          exfalso
          have hx := h k2
          rw [lookupS_nil, lookupS_cons, if_pos rfl] at hx
          simp at hx
  | cons p t1 ih =>
      intro l2 h1 h2 h
      obtain ⟨k1, v1⟩ := p
      cases l2 with
      | nil =>
          exfalso
          have hx := h k1
          rw [lookupS_cons, if_pos rfl, lookupS_nil] at hx
          simp at hx
      | cons q t2 =>
          obtain ⟨k2, v2⟩ := q
          have hkk : k1 = k2 := by
            rcases MapKey.toCanonKey.trich k1 k2 with hlt | heq | hgt
            · exfalso
              have hx := h k1
              rw [lookupS_cons, if_pos rfl, lookupS_cons,
                if_neg (fun hEq => MapKey.toCanonKey.irrefl k2 (by
                  rw [hEq] at hlt; exact hlt)),
                lookupS_absent t2 k1 (fun p5 hp5 =>
                  MapKey.toCanonKey.trans k1 k2 p5.1 hlt (asc_mem_gt t2 k2 v2 p5 h2 hp5))] at hx
              simp at hx
            · exact heq
            · exfalso
              have hx := h k2
              rw [lookupS_cons,
                if_neg (fun hEq => MapKey.toCanonKey.irrefl k1 (by
                  rw [hEq] at hgt; exact hgt)),
                lookupS_cons, if_pos rfl,
                lookupS_absent t1 k2 (fun p5 hp5 =>
                  MapKey.toCanonKey.trans k2 k1 p5.1 hgt (asc_mem_gt t1 k1 v1 p5 h1 hp5))] at hx
              simp at hx
          rw [hkk] at h1 h ⊢
          have hv : v1 = v2 := by
            have hx := h k2
            rw [lookupS_cons, if_pos rfl, lookupS_cons, if_pos rfl] at hx
            exact Option.some.inj hx
          have htail : ∀ k, lookupS t1 k = lookupS t2 k := by
            intro k
            by_cases hkEq : k = k2
            · rw [hkEq, lookupS_absent t1 k2
                (fun p5 hp5 => asc_mem_gt t1 k2 v1 p5 h1 hp5),
                lookupS_absent t2 k2
                (fun p5 hp5 => asc_mem_gt t2 k2 v2 p5 h2 hp5)]
            · have hx := h k
              rw [lookupS_cons, if_neg hkEq, lookupS_cons, if_neg hkEq] at hx
              exact hx
          rw [hv, ih t2 (asc_tail h1) (asc_tail h2) htail]

/-- The canonicity theorem at the rep level: the sorted rep's
    abstraction is injective (the retraction-grade face). -/
theorem toAbsS_inj [MapKey K] (s1 s2 : SortedAssoc K V)
    (h : toAbsS s1 = toAbsS s2) : s1 = s2 := by
  obtain ⟨l1, a1⟩ := s1
  obtain ⟨l2, a2⟩ := s2
  have h' : ∀ k, lookupS l1 k = lookupS l2 k := fun k => congrFun h k
  have hll := canonicity l1 l2 a1 a2 h'
  subst hll
  rfl

/-- THE non-iso honesty: the raw rep's abstraction is NOT injective —
    duplicates and order carry no meaning, so two DISTINCT raw lists
    represent the same map, and NO inverse exists. The raw rep is the
    Abstraction grade, never the Iso. -/
theorem raw_not_injective [DecidableEq K] (k : K) (v : V) :
    ∃ l1 l2 : RawAssoc K V, toAbsR l1 = toAbsR l2 ∧ l1 ≠ l2 := by
  refine ⟨[(k, v), (k, v)], [(k, v)], ?_, ?_⟩
  · have h1 : [(k, v), (k, v)] = insertR k v [(k, v)] := rfl
    have h2 : [(k, v)] = insertR k v [] := rfl
    simp only [toAbsR]
    funext k'
    rw [h1, lookupR_insertR, h2, lookupR_insertR, lookupR_nil]
    by_cases hEq : k = k' <;> simp [hEq]
  · intro hEq
    injection hEq with _ h2
    exact absurd h2 (List.cons_ne_nil _ _)

/-- The raw rep's honest grade, as the carrier's `Abstraction`
    structure: sound (every raw list determines its map), deliberately
    NOT exact (`raw_not_injective` — no inverse). -/
def rawAbstraction [DecidableEq K] : Kit.Abstraction (RawAssoc K V) (Abs K V) where
  abst := toAbsR
  conc b l := toAbsR l = b
  sound := fun _ => rfl

/-! ## The construction gate's teeth, instantiated -/

/-- The abstract insert's effect survives into the empty map — the
    observable the teeth's proof consumes. -/
theorem insert_effect_ne [DecidableEq K] (k : K) (v : V) :
    stepAbs (Op.insert k v) (Abs.empty K V) ≠ Abs.empty K V := by
  intro hEq
  have h5 : (if k = k then some v else (none : Option V)) = none :=
    congrFun hEq k
  rw [if_pos rfl] at h5
  simp at h5

/-- The construction gate's teeth, sorted face: a concrete step that
    IGNORES an operation cannot bundle with the abstract step — the
    insert's effect is observable through the left-unique relation
    (`Repr.no_ignore_step`). -/
theorem sorted_ignore_step [MapKey K] (k : K) (v : V) :
    ¬ ∃ r : Represents (Op K V) (Abs K V) (SortedAssoc K V) (Abs K V),
        r.R = RSorted ∧ r.stepC = (fun _ c => c) ∧ r.stepA = stepAbs :=
  no_ignore_step RSorted (fun _ c => c) stepAbs
    (fun c a a' h1 h2 => det_of_pointwise lookupS c.list a a' h1 h2)
    ⟨[], Asc.nil⟩ (Abs.empty K V) sortedRep.pres_init
    (Op.insert k v) (fun _ => rfl) (insert_effect_ne k v)

/-- The construction gate's teeth, raw face: same theorem, the other
    carrier — an implementation whose operations don't preserve the
    relation doesn't construct, at EITHER representation. -/
theorem raw_ignore_step [DecidableEq K] (k : K) (v : V) :
    ¬ ∃ r : Represents (Op K V) (Abs K V) (RawAssoc K V) (Abs K V),
        r.R = RRaw ∧ r.stepC = (fun _ c => c) ∧ r.stepA = stepAbs :=
  no_ignore_step RRaw (fun _ c => c) stepAbs
    (fun c a a' h1 h2 => det_of_pointwise lookupR c a a' h1 h2)
    [] (Abs.empty K V) rawRep.pres_init
    (Op.insert k v) (fun _ => rfl) (insert_effect_ne k v)

end Repr

end -- public section
