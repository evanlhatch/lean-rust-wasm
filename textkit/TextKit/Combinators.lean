/-
# TextKit.Combinators — the total positioned combinator surface

The combinator lane over the error-carrying carrier `GParser`
(TextKit.Error): `<|>` (best-error by farthest position, order-stable),
the repetition family (`many`/`some`/`sepBy`), `optional`/`between`,
`lookAhead`-as-`peek`, and EXPLICIT backtracking via `save`/`jump`.

Totality (notes/v3/06-lean-rules.md §6, notes/v3/15-patterns.md #12):
- every combinator is a plain structural match over the cursor;
- `many` recurses STRUCTURALLY on a fuel `Nat` (no `termination_by` —
  wf-recursion is kernel-opaque and would kill the tests' reduction);
  the fuel is `remaining + 1`, which is exactly enough: each continued
  iteration consumes ≥ 1 character, and the zero-progress body's final
  attempt on the empty input rides the `+1`.
- SEMANTICS of `many`: stops at the body's first failure (swallowed —
  the standard parsec reading; the failure is not `many`'s failure) OR
  at a zero-progress success (the progress rule — a body that accepts
  the empty string cannot be repeated unboundedly; totality demands the
  stop, and the stop is the honest grammar-level `rep` progress
  condition of notes/v3/05-codegen.md §1 made operational).

Backtracking: parsers are BACKTRACKING BY DEFAULT — a failing parser
consumes nothing (its failure carries only the error), so alternation
never needs explicit rewind; `save`/`jump` exist for the cases where a
CONSUMING success must be un-done (the explicit, visible form).

The grammar layer (Phase 4) sits ON TOP of this carrier; nothing here
reaches into it. The plain `Parser` (TextKit.Basic) is bridged via
`recognize` (forget the error).

The five questions (notes/v3/01-core.md):
- root: Universe — total functions over the cursor (pure data).
- carrier grade: none of its own — rides GParser's ParseError lane;
`recognize` bridges down to the plain Parser.
- spine reading: none — the carrier the typed grammar layer (Phase 4)
sits on; nothing is read or emitted here.
- ladder rung: rung 1 — structural matches + explicit fuel; totality
by construction (no wf opacity).
- gate row: none yet — TextKit is outside Gates.Packages' gated set;
TextKitTests.Main pins the combinator behavior + negative controls.
-/

module

public import TextKit.Basic
public import TextKit.Error

@[expose] public section

namespace TextKit

/-! ## the GParser monad -/

namespace GParser

@[simp] def result (a : α) : GParser α := fun cur => .ok (a, cur)

@[simp] def bind {α β} (p : GParser α) (f : α → GParser β) : GParser β :=
  fun cur => match p cur with
    | .ok (a, cur') => f a cur'
    | .error e => .error e

instance : Monad GParser where
  pure := GParser.result
  bind := GParser.bind

/-- `do`-notation's `>>=` at an applied position (the instance glue). -/
@[simp] theorem bind_apply (p : GParser α) (f : α → GParser β) (cur : Cursor) :
    (p >>= f) cur = (GParser.bind p f) cur := by rfl

/-- `pure` at an applied position. -/
@[simp] theorem pure_apply (a : α) (cur : Cursor) :
    (pure a : GParser α) cur = .ok (a, cur) := rfl

end GParser

/-! ## the leaf scanners -/

/-- Consume one specific character; the expected-set names it. -/
def pchar (c : Char) : GParser Char := fun cur =>
  match cur.cs with
  | c' :: _ =>
      if c' = c then .ok (c, cur.adv)
      else .error (ParseError.base cur.off [s!"'{c}'"])
  | [] => .error (ParseError.base cur.off [s!"'{c}'"])

/-- Consume one character matching `p`; `name` is the expected-set entry
    (the head-predicate exclusion's positive face). -/
def satisfy (name : String) (p : Char → Bool) : GParser Char := fun cur =>
  match cur.cs with
  | c :: _ =>
      if p c then .ok (c, cur.adv)
      else .error (ParseError.base cur.off [name])
  | [] => .error (ParseError.base cur.off [name])

/-- Consume the literal `s` (the prefix kit's positive face). -/
def tok (s : String) : GParser String := fun cur =>
  if s.toList.isPrefixOf cur.cs then .ok (s, cur.advBy s.length)
  else .error (ParseError.base cur.off [s!"'{s}'"])

/-- Succeed only at end of input. -/
def eof : GParser Unit := fun cur =>
  match cur.cs with
  | [] => .ok ((), cur)
  | _ => .error (ParseError.base cur.off ["<end of input>"])

/-- Look at (but do not consume) the next character — `lookAhead`-as-peek
    on the atomic shape; NEVER fails. -/
@[simp] def peek : GParser (Option Char) := fun cur => .ok (cur.cs.head?, cur)

/-- Run `p`, then REWIND: the value survives, the cursor does not move.
    The general lookAhead (peek is its atomic special case). -/
def lookAhead (p : GParser α) : GParser α := fun cur =>
  match p cur with
  | .ok (a, _) => .ok (a, cur)
  | .error e => .error e

/-! ## explicit backtracking: save / jump -/

/-- Capture the current position (the explicit save point). -/
def save : GParser Cursor := fun cur => .ok (cur, cur)

/-- Jump back to a saved position — the explicit rewind (consumed input
    un-consumed; the byte offset rewinds with it). -/
def jump (tgt : Cursor) : GParser Unit := fun _ => .ok ((), tgt)

/-! ## alternation: best-error by farthest position -/

/-- Ordered choice: the left's success wins outright; on double failure
    the FARTHEST error wins, and at the same position the LEFT's error
    stands with the expected-sets unioned (order-stable:
    `ParseError.farther`). The `Alternative` instance puts it behind
    `<|>`. -/
def orElse (p q : GParser α) : GParser α := fun cur =>
  match p cur with
  | .ok r => .ok r
  | .error e =>
      match q cur with
      | .ok r => .ok r
      | .error e' => .error (ParseError.farther e e')

/-- The `Alternative` surface: `<|>` is the best-error choice above;
    `failure` reports an EMPTY expected-set at the current position
    (the honest unknown — a real grammar always labels through `label`). -/
def failureG : GParser α := fun cur =>
  .error (ParseError.base cur.off [])

instance : Alternative GParser where
  pure := GParser.result
  map f p := fun cur =>
    match p cur with
    | .ok (a, cur') => .ok (f a, cur')
    | .error e => .error e
  seq pf pa := fun cur =>
    match pf cur with
    | .error e => .error e
    | .ok (f, cur1) =>
        match pa () cur1 with
        | .error e => .error e
        | .ok (a, cur2) => .ok (f a, cur2)
  failure := failureG
  orElse := fun p q => orElse p (q ())

/-- Label a parser: on failure the label joins the envelope's context
    stack (prepended — outermost first, as a name-only `TextKit.Label`) and
    the valid-set becomes exactly the label (the label IS what the
    grammar wanted here); the message names it too (the envelope's
    curated-message rule). -/
def label (s : String) (p : GParser α) : GParser α := fun cur =>
  match p cur with
  | .error e =>
      .error { e with valid := [s], message := s!"expected {s}",
                      context := TextKit.Label.at s :: e.context }
  | .ok r => .ok r

/-- Fill the did-you-mean hook on failure (the field's consumer-side
    filler; the ENGINE's home is the kit, not this library). -/
def withSuggest (s : String) (p : GParser α) : GParser α := fun cur =>
  match p cur with
  | .error e => .error { e with suggest := some s }
  | .ok r => .ok r

/-! ## the repetition family (total, progress-guarded) -/

/-- The fuel-driven repetition engine (structural on the fuel — see the
    module header's totality note). -/
def manyGo (p : GParser α) : Nat → GParser (List α)
  | 0, cur => .ok ([], cur)
  | n+1, cur =>
      match p cur with
      | .error _ => .ok ([], cur)
      | .ok (a, cur') =>
          if cur'.cs.length < cur.cs.length then
            match manyGo p n cur' with
            | .ok (as, cur'') => .ok (a :: as, cur'')
            | .error e => .error e
          else .ok ([a], cur')

/-- Zero-or-more: the body's failure is swallowed (many succeeds with
    what it has); the body's zero-progress success stops the repetition
    (the progress rule — the module header's totality note). -/
def many (p : GParser α) : GParser (List α) := fun cur =>
  manyGo p (cur.cs.length + 1) cur

/-- One-or-more: the body's FIRST failure propagates (a `some` with
    nothing is a real failure, not an empty success). -/
def some (p : GParser α) : GParser (List α) := fun cur =>
  match p cur with
  | .error e => .error e
  | .ok (a, cur') =>
      match many p cur' with
      | .ok (as, cur'') => .ok (a :: as, cur'')
      | .error e => .error e

/-- `sep` then `p`, keeping only `p`'s value (the repetition glue). -/
def sepThen (sep : GParser β) (p : GParser α) : GParser α := fun cur =>
  match sep cur with
  | .error e => .error e
  | .ok (_, cur') => p cur'

/-- Zero-or-more `p` separated by `sep`: zero matches yield `[]`; else
    one match + the separated rest. A failed sep-then-body attempt gives
    the separator BACK (the swallowed failure rewinds to the attempt's
    start — the backtracking default, made visible in the pins). -/
def sepBy (p : GParser α) (sep : GParser β) : GParser (List α) := fun cur =>
  match p cur with
  | .error _ => .ok ([], cur)
  | .ok (a, cur') =>
      match many (sepThen sep p) cur' with
      | .ok (as, cur'') => .ok (a :: as, cur'')
      | .error e => .error e

/-- Zero-or-one: `p`'s success is `some`, `p`'s failure is `none`
    (swallowed — this combinator exists to swallow it). -/
def optional (p : GParser α) : GParser (Option α) := fun cur =>
  match p cur with
  | .error _ => .ok (none, cur)
  | .ok (a, cur') => .ok (Option.some a, cur')

/-- `openP`, then `p`, then `closeP`; only `p`'s value survives. -/
def between (openP : GParser β) (closeP : GParser γ) (p : GParser α) : GParser α := fun cur =>
  match openP cur with
  | .error e => .error e
  | .ok (_, cur1) =>
      match p cur1 with
      | .error e => .error e
      | .ok (a, cur2) =>
          match closeP cur2 with
          | .error e => .error e
          | .ok (_, cur3) => .ok (a, cur3)

/-! ## the bridges -/

/-- Top-level entry: run at offset 0; the final cursor's rest is the
    unconsumed input, and the error's position is absolute (the cursor
    carried the offset all along). -/
def runG (p : GParser α) (cs : List Char) : Except ParseError (α × List Char) :=
  match p ⟨0, cs⟩ with
  | .ok (a, cur) => Except.ok (a, cur.cs)
  | .error e => .error e

/-- Forget the error: the positioned lane viewed as the plain recognizer
    (the Basic monad's face — the bridge the plain-Parser consumers use). -/
def recognize (p : GParser α) : Parser α := fun cs =>
  match p ⟨0, cs⟩ with
  | .ok (a, cur) => Option.some (a, cur.cs)
  | .error _ => none

end TextKit

end -- @[expose] public section
