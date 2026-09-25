/-
# Kit.ListExtras — the generic List helpers the lanes kept re-rolling

THE DRY SWEEP'S FINDING: five modules hand-rolled the same generic
List lemmas — `SchemaCore.Update` (foldl commutation, nested
filterMap, the Perm appends, the beq twins), `SchemaCore.IncViolate`
(the filters' commutation), `SchemaCore.View` (the String beq twin's
consumer), `ZSet.Basic` (the Bool zero-test). This module is their ONE
home.

THE 06 §8 LOOKUP (what exists, checked against the v4.33.0 core
before anything landed here — the tree imports no Batteries):

- EXISTS in core, cited at the sites, NOT re-proved here:
  `beq_false_of_ne` (`a ≠ b → (a == b) = false`, with `LawfulBEq`) —
  replaces Update's `String.beq_false_of_ne'` +
  `FieldVal.beq_false_of_ne` twins; `Bool.eq_false_iff`
  (`b = false ↔ b ≠ true`) — replaces ZSet's `false_of_not_eq_true`;
  `List.foldl_append`; `List.filter_filter`; `List.filterMap_filterMap`.
- MISSING from core, landed HERE: `List.Perm` append-commutativity
  (core ships `Perm.append_left`/`append_right` only), pointwise
  `filterMap` congruence (core ships `filter_congr` only), the
  filters' COMMUTATION (core's `filter_filter` composes, never
  commutes), and the two fold-commutation shapes
  (`foldl_step_push`/`foldl_append_comm`).

Core-only (imports Init alone — the cone rule: Kit is C0 machinery;
every lane may import this).

The five questions (notes/v3/01-core.md):
- root: none — generic list combinatorics over core's List.
- carrier grade: none — the lemmas are the carrier's own laws.
- spine reading: none — substrate the lanes' proofs cite.
- ladder rung: n/a (proof support, no Change rung).
- gate row: the sites' gates ride unchanged (SchemaTests' pins cite
  the moved theorems by their new Kit.ListExtras names).
-/

namespace Kit.ListExtras

/-! ## The fold commutation shapes -/

/-- A step that commutes with every element of a fold pushes through
    the fold (the keyed delta's commutation kernel; Update's shape,
    landed once). -/
theorem foldl_step_push {α β : Type} {f : β → α → β}
    {s : List α} {c : α}
    (hc : ∀ c₂ ∈ s, ∀ b, f (f b c) c₂ = f (f b c₂) c) :
    ∀ b, s.foldl f (f b c) = f (s.foldl f b) c := by
  induction s with
  | nil => intro _; rfl
  | cons c₂ rest ih =>
      intro b
      simp only [List.foldl_cons]
      show rest.foldl f (f (f b c) c₂) = f (rest.foldl f (f b c₂)) c
      rw [hc c₂ (List.mem_cons_self) b]
      exact ih (fun c' hc' => hc c' (List.mem_cons_of_mem c₂ hc')) _

/-- Adjacent-block exchange for a fold of pairwise-commuting steps
    (Update's Law-3 shape, landed once). -/
theorem foldl_append_comm {α β : Type} {f : β → α → β}
    {s₁ s₂ : List α}
    (hc : ∀ c₁ ∈ s₁, ∀ c₂ ∈ s₂, ∀ b, f (f b c₁) c₂ = f (f b c₂) c₁) :
    ∀ b, (s₁ ++ s₂).foldl f b = (s₂ ++ s₁).foldl f b := by
  induction s₁ with
  | nil => intro b; simp
  | cons c₁ s₁' ih =>
      intro b
      simp only [List.cons_append, List.foldl_cons]
      rw [ih (fun x hx => hc x (List.mem_cons_of_mem c₁ hx)) (f b c₁)]
      show (s₂ ++ s₁').foldl f (f b c₁) = (s₂ ++ c₁ :: s₁').foldl f b
      rw [List.foldl_append, List.foldl_append]
      show s₁'.foldl f (s₂.foldl f (f b c₁))
        = s₁'.foldl f (f (s₂.foldl f b) c₁)
      rw [foldl_step_push (f := f) (s := s₂) (c := c₁)
        (fun c₂ hc₂ b' => hc c₁ (List.mem_cons_self) c₂ hc₂ b') b]

/-! ## The filterMap congruence -/

/-- Pointwise filterMap congruence (core ships `filter_congr` only). -/
theorem filterMap_congr {α β : Type} {f g : α → Option β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.filterMap_cons]
      rw [h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-! ## The filters' commutation -/

/-- The filters commute — core's `List.filter_filter` composes them
    into one conjunction filter; conjunct commutativity (Bool's
    `and_comm`) splits the two orders (IncViolate's
    `filter_filter_comm'`, landed once). -/
theorem filter_filter_comm {α : Type} (p q : α → Bool) (l : List α) :
    List.filter p (List.filter q l) = List.filter q (List.filter p l) := by
  rw [List.filter_filter, List.filter_filter,
    List.filter_congr (q := fun a => q a && p a)
      (fun a (_ : a ∈ l) => by cases p a <;> cases q a <;> rfl)]

/-! ## The Perm append shapes -/

/-- The cons-through-append shuffle (the append-comm step). -/
theorem permConsAppend {α : Type} (x : α) :
    ∀ (l₂ xs : List α), (x :: (l₂ ++ xs)).Perm (l₂ ++ x :: xs) := by
  intro l₂
  induction l₂ with
  | nil => intro _; exact List.Perm.refl _
  | cons y ys ih =>
      intro xs
      show (x :: y :: (ys ++ xs)).Perm (y :: (ys ++ x :: xs))
      exact (List.Perm.swap y x (ys ++ xs)).trans (List.Perm.cons y (ih xs))

/-- `l₁ ++ l₂ ~ l₂ ++ l₁` (core ships `Perm.append_left`/`append_right`
    but not append-commutativity). -/
theorem permAppendComm {α : Type} :
    ∀ (l₁ l₂ : List α), (l₁ ++ l₂).Perm (l₂ ++ l₁) := by
  intro l₁ l₂
  induction l₁ with
  | nil => rw [List.nil_append, List.append_nil]
  | cons x xs ih =>
      show (x :: (xs ++ l₂)).Perm (l₂ ++ x :: xs)
      exact (List.Perm.cons x ih).trans (permConsAppend x l₂ xs)

end Kit.ListExtras
