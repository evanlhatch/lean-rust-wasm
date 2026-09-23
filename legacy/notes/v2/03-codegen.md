# 03 — Generic text codegen: lexer, parser, printer (the executable spec)

ONE grammar value drives lexer + parser + printer + inversion + diagnostics.
"New text format" = one grammar table + zero hand parsers/printers/proofs.

## 0. Invariants

- **Total**: no `partial` in the text layer; structural recursion or
  `termination_by` with a size measure (the `Audit.go` pattern).
- **Proof-carrying**: well-definedness (`unambiguous`) and inversion
  (`parse∘emit`) are THEOREMS over the table, generated, never per-ctor.
- **Deterministic**: no sorts/hash iteration; best-error is monotone max-on-
  position, order-stable.
- **Guest-compilable**: one grammar, two carriers (host: positions + context;
  guest: bytes + Nat-free/match-only).
- **Curated errors**: every failure is a `ParseError` (03 §3) feeding Diag.

## 1. The grammar model (the concrete types)

```lean
namespace TextKit.Grammar

-- terminals carry a charset rule; sentence nodes carry the correspondence
inductive Lex (Tok : Type) where
  | token  (name : String) (text : String)            -- prefix-free literal
  | ident  (name : String) (first rest : Char → Bool)
  | number (name : String)
  | quoted (name : String) (esc : Char → Option Char) -- '…', "…" with escapes
  | punct  (name : String) (text : String)            -- single-char separators
  | ws     (sig : Bool) (p : Char → Bool)             -- significant? whitespace
  | comment (open close : String)                     -- line/block comments

inductive Node (Tok : Type) where
  | tok    (l : Lex Tok)
  | seq    (parts : List (Node Tok))        -- ordered sequence
  | alt    (choices : List (Node Tok))      -- ordered; FIRST fringe prefix-free
  | rep    (body : Node Tok) (sep : Option (Node Tok))
  | opt    (body : Node Tok)
  | label  (name : String) (body : Node Tok)   -- <?>-style error label
  | rel    (iso : CodegenCore.Iso (Packed Tok) R) (body : Node Tok)  -- payload pack
```

`Packed Tok` = the raw parse of a node (tokens/tree); `rel` declares the
correspondence between the raw parse and the node's semantic payload `R`
(the unparser/parser glue — the load-bearing piece).

```lean
structure Grammar (Tok R : Type) where
  root      : Node Tok
  lex       : List (Lex Tok)
  -- the well-definedness certificate lives in the literal:
  unambiguous : unambig root lex := by decide
  labels    : NameMap String  -- label id → human phrase (for Diag)
deriving Inhabited
```

`unambig` = prefix-freedom of token fringes at every `alt`, and no-left-corner
for `rel`/`rep` recursion — a decidable function over the finite table. An
ambiguous grammar literal FAILS TO ELABORATE (defaulted proof field).

## 2. The pipeline (three folds of one grammar value)

```
input text → [lex] → token stream → [parse] → ParseOutcome (α × rest × err?) 
                                   → [print] → output text
```

- **Lex** — a fold over `Grammar.lex`; positions via `Substring` on the host
  carrier (byte offsets into the ORIGINAL input), the guest carrier is
  `List UInt8` (the witness decode lane; match-only).
- **Parse** — recursive descent over the token stream; structural recursion
  over `Node`; total.
- **Print** — the inverse fold: `print : Payload → tokens → text`.
- **Inversion** — `parse (print x) = ok x`, generated (03 §5).

Section-shaped formats (manifests, snapshots, worlds, configs) declare a
SECTION grammar: `section → tokenize → parse` as one composition; section
markers are terminals, never magic strings in code.

## 3. ParseOutcome and ParseError (concrete)

```lean
structure Position where
  byte : Nat  ; line : Nat ; col : Nat
deriving Repr

structure ParseError where
  pos      : Position
  expected : List String      -- the expected set: terminals + labels at pos
  got      : String           -- offending slice (bounded, ≤80 chars)
  ctx      : List String      -- label stack, innermost first
  suggest  : Option String    -- did-you-mean fill (04)
  code     : String           -- the E-code row (04 §4)
deriving Repr, BEq

inductive ParseOutcome (α : Type) where
  | ok  (v : α) (rest : Toks) (score : Score)
  | err (e : ParseError)
```
`Score` = (maxPosition, labelSet, order) — the deterministic best-error key;
`<|>` keeps the higher score; ties break by more-specific labels then by order.

Guest carrier: `ParseErrorG` = pos-id + label-ids only; conversion at the
boundary (labels resolve by id via the registry).

## 4. The combinator surface (total)

```lean
def Parser (Tok α) := List Tok → ParseOutcome α
-- monad (pure/bind), fail, peek, rest, jump (the try-checkpoint primitive)
-- <|> (best-error), many, some, sepBy, sepBy1, optional, between, lookAhead
-- try p := save pos; p | jump-saved with relabeled error
```

- Build the surface over the fold-primitives; NO second execution model.
- `label <?> "phrase"` rewrites ctx/got without losing position.
- Backtracking is explicit (save/jump); nothing is implicit.

## 5. declare_inversion

```lean
declare_inversion <grammar>   -- command
```
Emits per node: the local inversion lemmas (`lexSelf`, `scanX_rev`,
`startsWith_self`, alt/seq/rep compositors) via family! templates, and the
headline: `theorem parse_emit (x : Payload) : parse (print x) = ok x`.
Requirement: every `seq`/`alt`/`rep` carries its unambiguity certificate so
inversion composes without ambiguity case analysis.

## 6. dsl! (the authoring surface generator)

```lean
dsl! <grammar> as <surfaceName>   -- command
```
Emits: the syntax category + term elaborator, the app_unexpanders
(delaborators printing values back to the DSL), and the printer (already the
grammar's print fold). Every future DSL gets surface + pretty-printer from one
spec; the hand-written unexpander family (the `[inv| …]` precedent) becomes
generated.

## 7. The recipe "add a format" (what an agent does)

1. Write `Grammar` (nodes + lex rows + labels + `rel` correspondences).
2. Compile — the `unambiguous` proof field fires or the grammar is fixed.
3. `declare_inversion` → parser + printer + inversion theorem.
4. `dsl!` where an authoring surface is wanted.
5. Add RoundTripSpec (golden) + corruption/negative rows as data.
6. Write the 06 recipe entry (new format = the grammar spec + golden rows).

## 8. TextKit layout (files this phase creates)

```
TextKit/TextKit/
  Grammar.lean  -- Node/Lex/Grammar + unambig + labels
  Lex.lean      -- lexer fold, Substring scanner
  Parse.lean    -- Parser/ParseOutcome/ParseError/Score + combinators
  Guest.lean    -- guest-thin adapter (bytes, ids)
  Inversion.lean-- declare_inversion + parse_emit
  Dsl.lean      -- dsl! + generated elaborators/unexpanders/printers
  Diag.lean     -- envelope shared with CodegenCore.Errors
  FormatLaws.lean
```

## 9. Acceptance gate (mechanical)

Re-express TWO existing formats as grammar values: (a) a sectioned text wire
(kernel: `snapshot` or the explain-text), (b) one manifest (`forgeJobs` or the
oracle manifest). Gate:

- emitted goldens byte-identical to today,
- `parse∘emit` is a GENERATED THEOREM (not a property test),
- corrupt/ambiguous inputs are REFUSED by the unambiguity+inversion data rows,
- curated `ParseError` messages name position + expected set + context + valid
  space (did-you-mean),
- elaboration time flat (07 §4 watch).

A new text format lands as: `Grammar` value + golden rows — no parser module,
no printer module, no proof family.
