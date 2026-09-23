/-
# TextKit.Error — the structured parse error + the positioned lane

The doctrine's error shape (notes/v3/05-codegen.md §1): errors are
`ParseError` values — position + expected-set + label stack + did-you-mean
— never `none`. The plain `Parser` (TextKit.Basic) is a pure recognizer:
its `none` failures carry no position (the legacy Diag honesty note).
So the ERROR-CARRYING lane threads a cursor (offset + remaining input)
and reports `ParseError` on failure. The combinator surface
(TextKit.Combinators) lives on this lane; the plain `Parser` stays the
List-Char recognizer substrate.

Position semantics: `ParseError.pos` is the byte offset into the input at
the failure point, in the carrier's units (characters on this host
carrier). The GUEST variant is bytes+ids — a note, not a build: its
consumer does not exist yet, and nothing here precludes it (the fields
are plain data; a byte-offset guest error is the same shape re-keyed).

Guest-thinkability: every declaration here is first-order data over
`Nat`/`String`/`List Char` — no classes, no universes beyond `Type`,
nothing host-exclusive.

The did-you-mean hook: `ParseError.suggest` is a FIELD only — the
suggest ENGINE (edit-distance over the expected set, one engine, one
suffix — notes/v3/15-patterns.md #16) is the kit's home, not this
library's; a filler combinator lives in `TextKit.Combinators`.

The five questions (notes/v3/01-core.md):
- root: Universe — first-order error data (position + expected set +
label stack + suggestion field).
- carrier grade: none — `ParseError` is a value; the positioned lane
threads the cursor, it does not convert presentations.
- spine reading: none — the error vocabulary the combinator lane
speaks.
- ladder rung: rung 1 — no proof family; the guest-bytes variant is a
note, not a build.
- gate row: none yet — TextKit is outside Gates.Packages' gated set;
TextKitTests pins the position/expected behavior.
-/

module

@[expose] public section

namespace TextKit

/-! ## the cursor (the positioned lane's state) -/

/-- The parse cursor: the byte offset consumed so far + the unconsumed
    input. Position bookkeeping without re-measuring. -/
structure Cursor where
  /-- Characters consumed so far (the failure position's offset). -/
  off : Nat
  /-- The unconsumed input. -/
  cs : List Char
deriving Repr, BEq, Inhabited, DecidableEq

/-- A cursor advanced over one character. -/
def Cursor.adv (c : Cursor) : Cursor :=
  match c.cs with
  | _ :: rest => ⟨c.off + 1, rest⟩
  | [] => c

/-- A cursor advanced over a literal prefix (caller supplies the length). -/
def Cursor.advBy (c : Cursor) (n : Nat) : Cursor :=
  ⟨c.off + n, c.cs.drop n⟩

/-! ## the error shape -/

/-- The structured parse error: position (byte offset), the expected set
    at the failure point, the label stack (outermost first), and the
    did-you-mean hook (filled by the suggest engine's consumer). -/
structure ParseError where
  /-- The byte offset (carrier units) at the failure point. -/
  pos : Nat
  /-- What the grammar wanted here (the expected-set; a list, order =
      the grammar's declaration order — order-stable). -/
  expected : List String
  /-- The label stack, outermost first (the `context` the consumer
      surfaces: "while parsing X, inside Y"). -/
  context : List String
  /-- Did-you-mean hook: the engine's suggestion, when filled. -/
  suggest : Option String
deriving Repr, BEq, Inhabited, DecidableEq

/-- The BEST of two errors: the farther position wins; at the SAME
    position the expected-sets union (left's order first, then right's
    new entries — order-stable, the legacy `Diag.best` semantics), and
    the left's context + suggestion stand. Left-wins-on-ties keeps
    `<|>` deterministic under operand reordering of equals. -/
def ParseError.farther (a b : ParseError) : ParseError :=
  if a.pos > b.pos then a
  else if b.pos > a.pos then b
  else
    { a with
      expected := a.expected ++ (b.expected.filter (fun e => !(a.expected.contains e))) }

/-- The positioned parse result: the value + the final cursor, or the
    structured error. -/
abbrev ParseResult (α : Type) : Type := Except ParseError (α × Cursor)

/-- The positioned parser: total over the List Char core (a cursor is a
    byte offset + a `List Char`); errors are `ParseError` values. -/
abbrev GParser (α : Type) : Type := Cursor → ParseResult α

end TextKit

end -- @[expose] public section
