import LeanSubstrait.Emit.Text

/-!
# LeanSubstrait.Decode.ListExtra — `List.setLast` and friends

Core (v4.33) has no value-replacement "set the last element" on `List`.
Batteries has `Batteries.Data.List.modifyLast` (a function-applied, tail-recursive
variant), but this package is core-only (no Batteries in scope), and the
column-list inversion theorem in `Decode.lean` needs the value form. These
definitions and lemmas back `splitAppend_map_parseNamedCol`.
-/

namespace List

/-- Replace the last element of a list with `v`; the list is unchanged if it
    is empty. -/
def setLast : List α → α → List α
  | [], _ => []
  | [_], v => [v]
  | a :: b :: rest, v => a :: setLast (b :: rest) v

@[simp] theorem setLast_nil (v : α) : setLast [] v = [] := rfl
@[simp] theorem setLast_singleton (a v : α) : setLast [a] v = [v] := rfl
@[simp] theorem setLast_cons_cons (a b : α) (rest : List α) (v : α) :
    setLast (a :: b :: rest) v = a :: setLast (b :: rest) v := rfl

/-- `setLast` does not change the length. -/
@[simp] theorem length_setLast (xs : List α) (v : α) : (setLast xs v).length = xs.length := by
  induction xs with
  | nil => simp [setLast]
  | cons a rest ih =>
      cases rest with
      | nil => simp [setLast]
      | cons b rest' => simp [setLast, ih]

/-- `setLast` commutes with `map`. -/
@[simp] theorem setLast_map (xs : List α) (f : α → β) (v : α) :
    (setLast xs v).map f = setLast (xs.map f) (f v) := by
  induction xs with
  | nil => simp [setLast]
  | cons a rest ih =>
      cases rest with
      | nil => simp [setLast]
      | cons b rest' => simp [setLast, ih]

/-- The last element after `setLast` is `v`, for a nonempty list. -/
theorem getLast?_setLast_cons : ∀ (a : α) (rest : List α) (v : α),
    (setLast (a :: rest) v).getLast? = some v
  | a, [], v => by simp [setLast]
  | a, b :: rest, v => by
      rw [setLast_cons_cons]
      rw [getLast?_cons]
      rw [getLast?_setLast_cons b rest v]
      rfl

/-- The full `getLast?` reading of `setLast`: the empty list stays `none`,
    anything else becomes `v`. -/
theorem getLast?_setLast (xs : List α) (v : α) :
    (setLast xs v).getLast? = xs.getLast?.map (fun _ => v) := by
  cases xs with
  | nil => simp [setLast]
  | cons a rest => simp [getLast?_setLast_cons, getLast?_cons]

end List
