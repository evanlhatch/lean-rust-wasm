/-
# SchemaLang.Lin — linearity by construction (the weighted-automata kernel)

A `Lin sem a b` is a list-homomorphism between schema types: it
respects concatenation, which is exactly the DBSP fragment that
incrementalizes (work proportional to the delta, never the collection).

The combinators each prove the law ONCE; composition in `Lin.comp`
preserves it — **a user composing from these combinators cannot build a
non-linear morphism**. Deciding linearity of arbitrary code is
undecidable; composing from linear primitives is undodgeable.

This is the weighted-automata fragment: ZSets are ℤ-weights, and the
recognizable (finite-state, linear-representation) part of the stream
space is exactly what composes here. Arbitrary per-element functions
are fine (map is linear for ANY element function — DBSP's map); what's
forbidden is stateful/cross-element structure, which must be built as
Machines instead (the "when" regime).
-/

import SchemaLang.Ty

namespace SchemaLang

/-- A linear morphism between schema types: a list-homomorphism. -/
structure Lin (sem : TySem) (a b : Ty) where
  fn : List (a.toType sem) → List (b.toType sem)
  linear : ∀ xs ys, fn (xs ++ ys) = fn xs ++ fn ys

/-- Identity: the empty circuit. -/
def Lin.idL (sem : TySem) (a : Ty) : Lin sem a a where
  fn xs := xs
  linear := by intros; simp

/-- Element map: linear for ANY element function (DBSP's `map`). -/
def Lin.map (sem : TySem) {a b : Ty} (f : a.toType sem → b.toType sem) :
    Lin sem a b where
  fn xs := xs.map f
  linear := by intros; simp [List.map_append]

/-- Predicate filter: drops elements (retraction is negation —
    `negL`-style combination is the group route; filter composes with
    map but not with aggregation). -/
def Lin.filter (sem : TySem) {a : Ty} (p : a.toType sem → Bool) : Lin sem a a where
  fn xs := xs.filter p
  linear := by intros; simp [List.filter_append]

/-- Concat-map: linear (flatten distributes over append). -/
def Lin.collect (sem : TySem) {a b : Ty} (f : a.toType sem → List (b.toType sem)) :
    Lin sem a b where
  fn xs := xs.flatMap f
  linear := by intros; simp [List.flatMap_append]

/-- Composition: closed under the category. -/
def Lin.comp (sem : TySem) {a b c : Ty} (g : Lin sem b c) (f : Lin sem a b) :
    Lin sem a c where
  fn xs := g.fn (f.fn xs)
  linear := by intros; rw [f.linear, g.linear]

end SchemaLang
