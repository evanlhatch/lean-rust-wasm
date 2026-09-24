/-
# TextKit.Error — the structured parse error + the positioned lane

The doctrine's error shape (notes/v3/05-codegen.md §1 + §4): errors are
`ParseError` values — the ONE diagnostic envelope WITH position — never
`none`. THE CONVERGED SHAPE (05 §4: "ParseError = a Diag with
position"): `ParseError extends TextKit.Diag` — the envelope's fields ARE
the parse error's (the E-code slot filled from the parse side via
`parseCode`, the expected set rides the envelope's `valid`, the
did-you-mean is the same `suggest` field, the label stack is the
envelope's `context : List Label`), and `pos` is the parse-specific
addition. No second envelope, no bridge at the boundary: every consumer
holding a `ParseError` holds a `Diag` (`ParseError.toDiag` is the
inheritance projection) and renders through `TextKit.Diag.toString`.

The plain `Parser` (TextKit.Basic) is a pure recognizer: its `none`
failures carry no position (the legacy Diag honesty note). So the
ERROR-CARRYING lane threads a cursor (offset + remaining input) and
reports `ParseError` on failure. The combinator surface
(TextKit.Combinators) lives on this lane; the plain `Parser` stays the
List-Char recognizer substrate.

Position semantics: `ParseError.pos` is the byte offset into the input at
the failure point, in the carrier's units (characters on this host
carrier). The GUEST variant is bytes+ids — a note, not a build: its
consumer does not exist yet, and nothing here precludes it (the fields
are plain data; a byte-offset guest error is the same shape re-keyed).

The did-you-mean hook: `ParseError.suggest` (the envelope's field) is a
FIELD only — the suggest ENGINE (edit-distance over the valid set, one
engine, one suffix — notes/v3/15-patterns.md #16) lives at
`TextKit.Suggest` (`TextKit.suggestFor`, the envelope's `closedWorld`
route); a filler combinator lives in `TextKit.Combinators`. The
envelope's discipline (`Diag.closedWorld` cannot skip the engine)
applies to closed-world parse failures at their construction sites.

The cone call (notes/v3/06-lean-rules.md §8 + the build boundary): the
envelope's home is `TextKit.Diag` — THIS root, the C0 module-system
substrate at the lowest point every diagnostic side imports. The
textkit→kit direction is build-impossible (a `module` file cannot
import a pre-`module` file — verified); the kit→textkit direction is
the proven one (Kit's own module files import TextKit.Basic), and Kit's
Diag re-exports these declarations under the `Kit` namespace,
interface-preserved. No module cycle: TextKit.{Suggest,Diag,Error}
import Lean/each other and nothing of Kit's. The guest-thinkability
note is unchanged: every field here is first-order data over
`Nat`/`String`/`List`.

The five questions (notes/v3/01-core.md):
- root: Universe — first-order error data (the envelope + position).
- carrier grade: none — `ParseError` is a value; the positioned lane
threads the cursor, it does not convert presentations.
- spine reading: none — the error vocabulary the combinator lane
speaks, in the ONE envelope all channels speak.
- ladder rung: rung 1 — no proof family; the guest-bytes variant is a
note, not a build.
- gate row: none yet — TextKit is outside Gates.Packages' gated set;
TextKitTests pins the position/valid behavior + the envelope
projection's rendering.
-/

module

public import TextKit.Diag

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

/-! ## the error shape (the ONE envelope, with position) -/

/-- The parse channel's E-code slot (filled from the parse side, per
    05 §4's one-code-space rule). A named constant, ALLOCATED from the
    PERSISTED registry (`notes/code-registry.txt` — the spec of record;
    codes never derive from enumeration position or import order). The
    code-registry gate's coverage scan ties this spelling to its
    allocated live row — a hand-strung code is a gate refusal. -/
def parseCode : ECode := ⟨"TK1001"⟩

/-- The structured parse error: the ONE diagnostic envelope
    (`TextKit.Diag` — code, message, context stack, got, valid space,
    did-you-mean, severity) WITH the parse-specific `pos`. The
    expected-set rides the envelope's `valid` (a list, order = the
    grammar's declaration order — order-stable); the label stack rides
    the envelope's `context` (outermost first, name-only labels); the
    did-you-mean rides the envelope's `suggest` (filled by the ONE
    engine's consumer — `TextKit.suggestFor` / the `closedWorld`
    constructor). -/
structure ParseError extends TextKit.Diag where
  /-- The byte offset (carrier units) at the failure point. -/
  pos : Nat
deriving Repr, BEq, Inhabited, DecidableEq

/-- The base parse error at `pos` wanting `expected` — the combinators'
    ONE construction path, so the envelope's fields cannot be skipped:
    the code slot from the parse side, the expected set → `valid`, the
    message naming the channel. Positional parse failures carry no
    single `got` (`got := none` — the envelope's honesty note for
    positional failures). -/
def ParseError.base (pos : Nat) (expected : List String) : ParseError :=
  { pos := pos
    code := parseCode
    message := "parse error"
    valid := expected }

/-- The BEST of two errors: the farther position wins; at the SAME
    position the valid-sets union (left's order first, then right's
    new entries — order-stable, the legacy `Diag.best` semantics), and
    the left's envelope fields (code, message, context, suggestion)
    stand. Left-wins-on-ties keeps `<|>` deterministic under operand
    reordering of equals. -/
def ParseError.farther (a b : ParseError) : ParseError :=
  if a.pos > b.pos then a
  else if b.pos > a.pos then b
  else
    { a with
      valid := a.valid ++ (b.valid.filter (fun e => !(a.valid.contains e))) }

/-- The positioned parse result: the value + the final cursor, or the
    structured error. -/
abbrev ParseResult (α : Type) : Type := Except ParseError (α × Cursor)

/-- The positioned parser: total over the List Char core (a cursor is a
    byte offset + a `List Char`); errors are `ParseError` values. -/
abbrev GParser (α : Type) : Type := Cursor → ParseResult α

end TextKit

end -- @[expose] public section
