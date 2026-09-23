/-
# TextKit.Basic — the total parser core

This order: TextKit, the FRESH core-only text foundation (no mathlib, no
Batteries). Carrier: `Parser α := List Char → Option (α × List Char)` —
an `abbrev` (reducible) so every entry keeps its plain-function signature
and the proofs reduce through the definitions directly (the abbrev rule,
notes/v3/06-lean-rules.md §3).

Deliberate exclusions:
- The escape/quoted-name kit of the legacy `TextKit.Basic`
  (`escape`/`unescape`/`name`/`scanName`/`scanQuotedRaw` and their
  inversions) is emitter-side content with no consumer in this tree;
  porting it now would violate the leftover rule. Its THEOREM CONTENT
  (the per-arm `escChars` factorization + the flatMap fold inversion)
  is the port source when its consumer lands.
- The typed bidirectional grammar layer (notes/v3/05-codegen.md §1) is
  Phase 4 — a separate order. The carrier stays List-Char based so that
  layer sits on top unchanged.

Mining provenance: the monad, the scanners, and the prefix kit are
theorem-content ports of `legacy/lean/TextKit/TextKit/Basic.lean`
(the `Parser` section, `isIdentChar`/`isIdentifier`, `scanIdent`,
`scanNat`, `startsWith`/`expect`). Bodies re-derived FRESH as direct
total definitions (no `where`-clause helpers — the equations ARE the
defs, so `rfl`/`simp` reduce through them without unfolding helpers).

TOTALITY: every definition here is a plain structural match (no
`termination_by`, no `partial`) — a total parser has no silent
divergence (notes/v3/15-patterns.md #12).

The five questions (notes/v3/01-core.md):
- root: Universe — total functions over `List Char` (pure data).
- carrier grade: none — a plain-function recognizer; the error-carrying
crossing is TextKit.Error's GParser lane.
- spine reading: none — the substrate the grammar layer (05 §1,
Phase 4) will sit on.
- ladder rung: rung 1 — direct total definitions; the equations ARE
the defs (no opaque `where` helpers).
- gate row: none yet — TextKit is outside Gates.Packages' gated set;
TextKitTests pins the scanners + the axiom cones.
-/

module

@[expose] public section

namespace TextKit

/-! ## the parser monad -/

/-- The rest-threading parser monad: over `List Char`, returning the value
    and the unconsumed rest. `Parser` is an `abbrev` (reducible), so every
    public entry keeps its plain `List Char → Option (α × List Char)`
    signature; the `do`-blocks live in `where`-clause helpers typed
    `… → Parser α` (the notation's monad inference needs the `Parser` head). -/
abbrev Parser (α : Type) : Type := List Char → Option (α × List Char)

namespace Parser

@[simp] def result (a : α) : Parser α := fun cs => some (a, cs)

@[simp] def bind {α β} (p : Parser α) (f : α → Parser β) : Parser β :=
  fun cs => match p cs with | none => none | some (a, rest) => f a rest

instance : Monad Parser where
  pure := Parser.result
  bind := Parser.bind

@[simp] def fail : Parser α := fun _ => none

/-- Look at (but do not consume) the next character. -/
@[simp] def peek : Parser Char :=
  fun cs => match cs with | c :: _ => some (c, cs) | [] => none

/-- The input as it stands (position capture). -/
@[simp] def rest : Parser (List Char) := fun cs => some (cs, cs)

/-- Rewind to an earlier captured position (position-reset jumps). -/
@[simp] def jump (tgt : List Char) : Parser Unit := fun _ => some ((), tgt)

/-- Consume one specific character. -/
@[simp] def consumeChar (c : Char) : Parser Unit :=
  fun cs => match cs with | c' :: rest => if c' == c then some ((), rest) else none | [] => none

/-- Consume the maximal prefix matching `p` — the leaf scanners' core. -/
@[simp] def takeWhile (p : Char → Bool) : Parser String :=
  fun cs => some (String.ofList (cs.takeWhile p), cs.dropWhile p)

/-- `do`-notation's `>>=` at an applied position reduces to the bind's
    `match` (the class-instance glue is otherwise opaque to `simp`). -/
@[simp] theorem bind_apply (p : Parser α) (f : α → Parser β) (cs : List Char) :
    (p >>= f) cs = (Parser.bind p f) cs := by rfl

/-- `pure` at an applied position (the instance glue unfolds here). -/
@[simp] theorem pure_apply (a : α) (cs : List Char) :
    (pure a : Parser α) cs = some (a, cs) := rfl

/-- `consumeChar` at a matching literal head. -/
@[simp] theorem consumeChar_self (c : Char) (rest : List Char) :
    consumeChar c (c :: rest) = some ((), rest) := by
  unfold consumeChar
  simp

end Parser

/-! ## the text primitives -/

/-- Is `c` a plain ASCII graphic-identifier character? -/
def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_'

/-- Is `s` a valid bare identifier (ASCII letter first, alnum/underscore after)? -/
def isIdentifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => c.isAlpha && rest.all isIdentChar

/-! ## the scanners (direct, equation-lemma-friendly) -/

/-- Scan a bare identifier: ASCII alpha head, then ident-chars. Returns
    the name and the unconsumed rest. NONE on a non-alpha head (the
    head-predicate exclusion is `Lemmas.scanIdent_none_of_not_alpha`). -/
def scanIdent (cs : List Char) : Option (String × List Char) :=
  match cs with
  | c :: _ =>
      if c.isAlpha then
        some (String.ofList (cs.takeWhile isIdentChar), cs.dropWhile isIdentChar)
      else none
  | [] => none

/-- Scan a decimal natural (one or more digits). NONE on zero digits. -/
def scanNat (cs : List Char) : Option (Nat × List Char) :=
  let ds := String.ofList (cs.takeWhile Char.isDigit)
  if ds = "" then none
  else
    some (ds.toList.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0,
      cs.dropWhile Char.isDigit)

/-! ## the prefix kit -/

/-- Is `p` a literal prefix of `cs`? -/
def startsWith (cs : List Char) (p : String) : Bool := p.toList.isPrefixOf cs

/-- Consume the literal prefix (NONE on a non-prefix). -/
def expect (p : String) (cs : List Char) : Option (List Char) :=
  if startsWith cs p then some (cs.drop p.length) else none

end TextKit

end -- @[expose] public section
