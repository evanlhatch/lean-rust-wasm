/-
# CodegenCore.Validation — the error-ACCUMULATING applicative

`Except` exits at the first error; `Validation` collects them ALL (both
sides of `seq` concatenate, a fold reports every element's failure in
order). There is deliberately NO `Monad` instance — bind cannot
accumulate (the continuation needs the value the error path lacks).
Ownership: the one copy of the accumulating-fold pattern. Exclusion: no
`Monad`, no `Alternative` (both would lie about accumulation).

Known conversion sites (the type + laws + tests shipped; converting
these is follow-up work):
- `SchemaLang.Meta.Reflect.checkStruct` / `checkInductive`
  (schema-lang Meta/Reflect.lean:145/192) — hand folds collecting diag
  lists per structure field / inductive ctor.
- `Item.universeCheck`'s `items.flatMap (Item.check known)`
  (schema-lang Item.lean:315) — already accumulating; gains the
  structured ok/errs reading.
- QLang's error-accumulating Query steps (qlang QLang/Query.lean).
-/
module

@[expose] public section

namespace CodegenCore

/-- A validation result: a value, or a NON-empty-by-convention list of
    errors (the convention is enforced by the combinators below, which
    only ever produce `errs` from a supplied error list — never `[]`). -/
inductive Validation (ε α : Type) where
  | ok : α → Validation ε α
  | errs : List ε → Validation ε α
  deriving BEq, Repr

namespace Validation

instance [Repr ε] [Repr α] : ToString (Validation ε α) where
  toString := fun v => toString (repr v)

/-- Functorial map: errors pass through untouched. -/
def map (f : α → β) : Validation ε α → Validation ε β
  | ok a => ok (f a)
  | errs e => errs e

/-- Applicative seq — THE accumulation point: both sides' errors
    concatenate, function side first (evaluation order preserved). -/
def seq (vf : Validation ε (α → β)) (vx : Unit → Validation ε α) : Validation ε β :=
  match vf, vx () with
  | ok f, ok a => ok (f a)
  | ok _, errs e => errs e
  | errs e, ok _ => errs e
  | errs e₁, errs e₂ => errs (e₁ ++ e₂)

instance : Functor (Validation ε) where
  map := map

instance : Applicative (Validation ε) where
  pure := ok
  seq := seq

/-- Prepend errors to a result, discarding the value if one is there
    (a value sitting next to accumulated errors is junk — the result of
    any fold that saw an error is `errs`). -/
def prependErrors (e : List ε) : Validation ε α → Validation ε α
  | ok _ => errs e
  | errs e' => errs (e ++ e')

/-- Error-accumulating monadic fold. While steps succeed the state folds
    left as usual; a failing step records its errors AND the fold
    continues from the last known state (the step's update is skipped) so
    later elements still report. Once ANY step fails the accumulated
    VALUE is meaningless — the result is `errs` — only the error list is
    meaningful. Errors concatenate in element order. -/
def foldlM (f : β → α → Validation ε β) : β → List α → Validation ε β
  | b, [] => ok b
  | b, x :: xs =>
    match f b x with
    | ok b' => foldlM f b' xs
    | errs e => prependErrors e (foldlM f b xs)

/-- Cons a head result onto an accumulated tail, concatenating errors
    (head's first — element order preserved). -/
def seqCons : Validation ε β → Validation ε (List β) → Validation ε (List β)
  | ok b, ok bs => ok (b :: bs)
  | ok _, errs e => errs e
  | errs e, ok _ => errs e
  | errs e₁, errs e₂ => errs (e₁ ++ e₂)

/-- Error-accumulating traverse: all-ok gives `ok` of the mapped list;
    any failures give `errs` of ALL of them, in list order. -/
def traverse (f : α → Validation ε β) : List α → Validation ε (List β)
  | [] => ok []
  | x :: xs => seqCons (f x) (traverse f xs)

/-- The error projection (`ok` has none). -/
def errors? : Validation ε α → List ε
  | ok _ => []
  | errs e => e

/-- Bridge back to the early-exit world (the whole error list as the
    payload). -/
def toExcept : Validation ε α → Except (List ε) α
  | ok a => .ok a
  | errs e => .error e

/-! ## Laws (small, proved — the accumulation contract) -/

/-- Ok-accumulation identity: folding pure-ok steps IS the plain fold. -/
theorem foldlM_ok {ε : Type} (g : β → α → β) (b : β) (xs : List α) :
    foldlM (fun b a => ok (g b a) : β → α → Validation ε β) b xs = ok (xs.foldl g b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => exact ih (g b x)

/-- Err-accumulation shape: when EVERY step fails with one error, the
    fold over a nonempty list is `errs` of exactly the element count in
    `List.replicate` — no error dropped, no early exit. (The empty fold
    is `ok`: no element, no error.) -/
theorem foldlM_errs (e : ε) :
    ∀ (b : β) (x : α) (xs : List α),
      foldlM (fun _ _ => errs [e] : β → α → Validation ε β) b (x :: xs) =
        errs (List.replicate (xs.length + 1) e) := by
  intro b x xs
  induction xs generalizing b x with
  | nil => rfl
  | cons y ys ih =>
    show prependErrors [e]
        (foldlM (fun _ _ => errs [e] : β → α → Validation ε β) b (y :: ys)) =
      errs (List.replicate (ys.length + 1 + 1) e)
    rw [ih b y]
    rfl

/-- Corollary: the error count equals the element count when every step
    fails — the anti-early-exit pin. -/
theorem foldlM_errs_length (e : ε) (b : β) (x : α) (xs : List α) :
    (foldlM (fun _ _ => errs [e] : β → α → Validation ε β) b (x :: xs)).errors?.length =
      (x :: xs).length := by
  rw [foldlM_errs e b x xs]
  simp only [errors?, List.length_replicate, List.length_cons]

/-- Traverse identity on pure-ok steps: `ok` of the plain map. -/
theorem traverse_ok {ε : Type} (g : α → β) :
    ∀ xs : List α, traverse (ε := ε) (fun a => ok (g a)) xs = ok (xs.map g)
  | [] => rfl
  | x :: xs => by
    show seqCons (ok (g x) : Validation ε β) (traverse (ε := ε) (fun a => ok (g a)) xs) =
      ok (g x :: List.map g xs)
    rw [traverse_ok g xs]
    rfl

end Validation

end CodegenCore
