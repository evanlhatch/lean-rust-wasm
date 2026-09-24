/-
# Query.Basic — the query lane's row carrier: orderable schema rows

Owned by: the Query agent (the mandate tree, `query/`).

The query fragment (notes/v3/02-data-plane.md §2) evaluates weighted
relations whose rows are SCHEMA rows — `SchemaCore.RowVals fs`. The
canonical-rep machinery (`ZSet.Weighted K Row`) needs the row type to
carry a `CanonKey` (a core-only strict total order) + `DecidableEq`.
This file supplies exactly that, honestly:

- `Row.bytes` — the row's byte image, field by field, riding the ONE
  value codec (`SchemaCore.encVal`, read-only consumption — no second
  encoder). Injectivity (`Row.bytes_eq`) comes from the codec's
  append-form law (`decVal_encVal_append`, 15-patterns #2): the
  self-delimiting encoding determines each field value AND the rest.
- `lex8b` — bytewise lexicographic order over `List UInt8`, with the
  three CanonKey laws proved at the Nat level (`toNat` comparisons;
  `UInt8.toNat_inj` closes the equal branch).
- THE INSTANCES: `DecidableEq (RowVals fs)` + `CanonKey (RowVals fs)`.
  Any strict total order serves canonicalization — no structure is
  claimed beyond that (the wire never sees this order).

Also the two row shapes the fragment's result typing needs (02 §2-3):
`Row.append` (the equijoin's result row: the left schema ++ the right
schema — the result row type is COMPUTED) + `Row.at` (the positional
field read the projection's column data consumes). Both with their
injection laws.

Deliberate exclusions (02 §2's honest boundary, named): negation,
aggregation, universal conditions, ordering semantics — each needs
explicit additional semantics with named laws; none is smuggled in as
an order or a query operator. The `CanonKey` instance lives HERE, in
the lane that consumes it; promotion to schemacore is a deliberate
move for when a second consumer exists (the leftover rule).

The five questions (notes/v3/01-core.md):
- **Root**: Universe — data: the row carrier's orderable discipline.
- **Carrier grade**: the canonical-rep structure's requirement met
  (ZSet.Basic's `CanonKey`) — no new carrier of its own.
- **Spine reading**: none — the substrate the query fragment evaluates
  over.
- **Ladder rung**: hand theorems of the small kind (`bytes_eq` from
  the codec's append law; the lex laws by structural induction).
- **Gate rows**: the axiom report + QueryTests' pins (the byte image's
  injectivity exercised; the order's laws' negative controls).

Core-only (imports SchemaCore + ZSet.Basic — the cone rule; no
mathlib, no Batteries).
-/

import SchemaCore.RowVals
import SchemaCore.Codec
import ZSet.Basic

namespace Query

open SchemaCore

/-! ## The row's byte image -/

/-- The cons ctor's injection (the GADT's two data fields, the index
    already fixed by the caller's types). -/
theorem RowVals.cons_inj {f : Field} {fs : List Field}
    {v1 v2 : Value f.ty} {r1 r2 : RowVals fs}
    (h : RowVals.cons v1 r1 = RowVals.cons v2 r2) : v1 = v2 ∧ r1 = r2 := by
  injection h with _ _ a b
  exact ⟨a, b⟩

namespace Row

/-- The row's byte image: the ONE value codec (`SchemaCore.encVal`)
    applied field by field, schema order. The canonical-rep order's
    encoding — nothing more (the wire's row form is a later lane's
    business; this is the ORDER's encoding). -/
def bytes : (fs : List Field) → RowVals fs → List UInt8
  | [], .nil => []
  | f :: fs, .cons v vs => encVal f.ty v ++ bytes fs vs

/-- THE INJECTIVITY: equal byte images force equal rows — the codec's
    append-form law (`decVal_encVal_append`, 15-patterns #2) reading
    the fields back one at a time. -/
theorem bytes_eq : ∀ (fs : List Field) (r1 r2 : RowVals fs),
    bytes fs r1 = bytes fs r2 → r1 = r2 := by
  intro fs
  induction fs with
  | nil =>
      intro r1 r2 _; cases r1 <;> cases r2 <;> rfl
  | cons f fs' ih =>
      intro r1 r2 h
      cases r1 with
      | cons v1 rest1 =>
          cases r2 with
          | cons v2 rest2 =>
              have e1 : bytes (f :: fs') (RowVals.cons v1 rest1)
                  = encVal f.ty v1 ++ bytes fs' rest1 := rfl
              have e2 : bytes (f :: fs') (RowVals.cons v2 rest2)
                  = encVal f.ty v2 ++ bytes fs' rest2 := rfl
              rw [e1, e2] at h
              have d1 := decVal_encVal_append f.ty v1 (bytes fs' rest1)
              rw [h] at d1
              have d2 := decVal_encVal_append f.ty v2 (bytes fs' rest2)
              rw [d2] at d1
              injection Option.some.inj d1 with hv hrest
              rw [hv, ih rest2 rest1 hrest]

/-! ## The positional field read (the projection columns' reader) -/

/-- The `i`-th field value of a schema-aligned row — the projection's
    column reader (total: the index is in range by construction). -/
def field : (fs : List Field) → RowVals fs → (i : Fin fs.length) → Value fs[i.val].ty
  | _ :: _, .cons v _, ⟨0, _⟩ => v
  | _ :: _, .cons _ vs, ⟨n + 1, h⟩ =>
      field _ vs ⟨n, Nat.lt_of_succ_lt_succ h⟩

/-! ## The row concatenation (the equijoin's result row shape) -/

/-- The equijoin's result row: the left row's schema ++ the right row's
    schema — the result row TYPE is computed from the join (02 §2:
    conjunction = join; the combined row carries both sides). -/
def append : RowVals fs → RowVals gs → RowVals (fs ++ gs)
  | .nil, r => r
  | .cons v vs, r => .cons v (append vs r)

/-- The append's injectivity: the joined row determines BOTH sides
    (the schema lengths pin the split). -/
theorem append_inj : ∀ (fs gs : List Field) (l1 l2 : RowVals fs)
    (r1 r2 : RowVals gs), append l1 r1 = append l2 r2 → l1 = l2 ∧ r1 = r2 := by
  intro fs
  induction fs with
  | nil =>
      intro gs l1 l2 r1 r2 h
      cases l1 <;> cases l2
      · exact ⟨rfl, h⟩
  | cons f fs' ih =>
      intro gs l1 l2 r1 r2 h
      cases l1 with
      | cons v1 rest1 =>
          cases l2 with
          | cons v2 rest2 =>
              injection h with _ _ hv hrest
              subst hv
              obtain ⟨hl, hr⟩ := ih gs rest1 rest2 r1 r2 hrest
              exact ⟨by rw [hl], hr⟩

end Row

/-! ## The bytewise lexicographic order -/

/-- Bytewise lexicographic order over byte lists — the strict order
    the rows' canonical form sorts under (compared at the Nat level;
    `UInt8.toNat_inj` closes the equal-byte branch). -/
def lex8b : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a.toNat < b.toNat then true
      else if b.toNat < a.toNat then false
      else lex8b as bs

/-- The cons equation (the proofs' stepping stone). -/
theorem lex8b_cons (a : UInt8) (as : List UInt8) (b : UInt8) (bs : List UInt8) :
    lex8b (a :: as) (b :: bs) =
      (if a.toNat < b.toNat then true
       else if b.toNat < a.toNat then false else lex8b as bs) := rfl

/-- The true-head reading: a cons list is lex-less iff the head byte is
    smaller, or the heads are equal and the tails are. -/
theorem lex8b_cons_true {a b : UInt8} {as bs : List UInt8}
    (h : lex8b (a :: as) (b :: bs) = true) :
    a.toNat < b.toNat ∨ (a.toNat = b.toNat ∧ lex8b as bs = true) := by
  by_cases h1 : a.toNat < b.toNat
  · rw [lex8b_cons, if_pos h1] at h
    exact Or.inl h1
  · by_cases h2 : b.toNat < a.toNat
    · rw [lex8b_cons, if_neg h1, if_pos h2] at h
      exact absurd h (by simp)
    · rw [lex8b_cons, if_neg h1, if_neg h2] at h
      exact Or.inr ⟨by omega, h⟩

/-- Irreflexivity. -/
theorem lex8b_irrefl : ∀ l : List UInt8, lex8b l l = false
  | [] => rfl
  | a :: as => by
      rw [lex8b_cons, if_neg (show ¬ a.toNat < a.toNat by omega),
        if_neg (show ¬ a.toNat < a.toNat by omega)]
      exact lex8b_irrefl as

/-- Transitivity. -/
theorem lex8b_trans : ∀ (l1 : List UInt8) (l2 l3 : List UInt8),
    lex8b l1 l2 = true → lex8b l2 l3 = true → lex8b l1 l3 = true := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 l3 h1 h2
      cases l2 with
      | nil => rw [lex8b] at h1; simp at h1
      | cons b bs =>
          cases l3 with
          | nil => rw [lex8b] at h2; simp at h2
          | cons c cs => rfl
  | cons a as ih =>
      intro l2 l3 h1 h2
      cases l2 with
      | nil => rw [lex8b] at h1; simp at h1
      | cons b bs =>
          cases l3 with
          | nil => rw [lex8b] at h2; simp at h2
          | cons c cs =>
              rcases lex8b_cons_true h1 with hab | ⟨hab, h1'⟩
              · rcases lex8b_cons_true h2 with hbc | ⟨hbc, _⟩
                · rw [lex8b_cons, if_pos (by omega)]
                · rw [lex8b_cons, if_pos (by omega)]
              · rcases lex8b_cons_true h2 with hbc | ⟨hbc, h2'⟩
                · rw [lex8b_cons, if_pos (by omega)]
                · rw [lex8b_cons,
                    if_neg (show ¬ a.toNat < c.toNat by omega),
                    if_neg (show ¬ c.toNat < a.toNat by omega)]
                  exact ih bs cs h1' h2'

/-- Trichotomy (with the equality branch decided by the byte images'
    Nat comparison). -/
theorem lex8b_trich : ∀ (l1 : List UInt8) (l2 : List UInt8),
    lex8b l1 l2 = true ∨ l1 = l2 ∨ lex8b l2 l1 = true := by
  intro l1
  induction l1 with
  | nil =>
      intro l2
      cases l2 with
      | nil => exact Or.inr (Or.inl rfl)
      | cons b bs => exact Or.inl rfl
  | cons a as ih =>
      intro l2
      cases l2 with
      | nil => exact Or.inr (Or.inr rfl)
      | cons b bs =>
          rcases Nat.lt_trichotomy a.toNat b.toNat with h | h | h
          · exact Or.inl (by rw [lex8b_cons, if_pos h])
          · have hab : a = b := UInt8.toNat_inj.mp h
            subst hab
            rcases ih bs with h' | h' | h'
            · exact Or.inl (by
                rw [lex8b_cons,
                  if_neg (show ¬ (a : UInt8).toNat < a.toNat by omega),
                  if_neg (show ¬ a.toNat < (a : UInt8).toNat by omega)]
                exact h')
            · exact Or.inr (Or.inl (by rw [h']))
            · exact Or.inr (Or.inr (by
                rw [lex8b_cons,
                  if_neg (show ¬ (a : UInt8).toNat < a.toNat by omega),
                  if_neg (show ¬ a.toNat < (a : UInt8).toNat by omega)]
                exact h'))
          · exact Or.inr (Or.inr (by rw [lex8b_cons, if_pos h]))

/-! ## THE INSTANCES — schema rows are orderable keys -/

/-- Rows are compared by their byte images, lexicographically. Any
    strict total order serves the canonical form; this one is cheap and
    rides the ONE codec (no second encoder). -/
instance instDecidableEqRowVals (fs : List Field) : DecidableEq (RowVals fs) :=
  fun r1 r2 =>
    if h : Row.bytes fs r1 = Row.bytes fs r2 then
      isTrue (Row.bytes_eq fs r1 r2 h)
    else
      isFalse (fun he => h (by rw [he]))

instance instCanonKeyRowVals (fs : List Field) : ZSet.CanonKey (RowVals fs) where
  lt r1 r2 := lex8b (Row.bytes fs r1) (Row.bytes fs r2) = true
  decLt r1 r2 := inferInstanceAs (Decidable (lex8b (Row.bytes fs r1) (Row.bytes fs r2) = true))
  irrefl r := fun h => absurd h (by rw [lex8b_irrefl]; simp)
  trans r1 r2 r3 h1 h2 := lex8b_trans _ _ _ h1 h2
  trich r1 r2 := by
      rcases lex8b_trich (Row.bytes fs r1) (Row.bytes fs r2) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Row.bytes_eq fs r1 r2 h))
      · exact Or.inr (Or.inr h)

end Query
