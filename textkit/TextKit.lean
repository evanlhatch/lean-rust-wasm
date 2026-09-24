/-
# TextKit — the core-only text/parser foundation (FRESH, this tree)

Module map:
- `TextKit.Basic` — the `Parser` monad (List Char → Option), the
  text primitives (`isIdentChar`/`isIdentifier`), the scanners
  (`scanIdent`/`scanNat`/`startsWith`/`expect`), all direct total
  definitions (equation-lemma-friendly).
- `TextKit.Lemmas` — the inversion kit: `startsWith_self`/`expect_self`,
  the head-predicate exclusions, the bare-name inversion.
- `TextKit.Suggest` — the ONE did-you-mean engine (the ranked
  bounded edit distance + the one tree-wide suffix, as data) + the ONE
  diagnostic envelope `Diag` (05 §4's seven fields + `closedWorld`,
  the engine's route). Kit's Diag/Suggest re-export these (the
  interface-preserved shim) — the envelope has ONE home.
- `TextKit.Error` — `ParseError` = a `Diag` with position
  (`extends TextKit.Diag`: the expected set → `valid`, the label
  stack → `context`, the did-you-mean → `suggest`, the parse-side
  E-code slot) and the positioned lane (`Cursor`/`GParser`).
- `TextKit.Combinators` — the total positioned combinator surface:
  `<|>` (best-error by farthest position, order-stable),
  `many`/`some`/`sepBy`/`optional`/`between`/`lookAhead`-as-`peek`,
  explicit backtracking via `save`/`jump`.

NOT here (deliberate, see module headers): the escape/quoted-name kit
(no consumer yet) and the typed bidirectional grammar layer (Phase 4 —
it sits ON TOP of the List-Char carrier this library fixes).

The five questions (notes/v3/01-core.md): answered per submodule (the
map above); the umbrella answers none — import point. Gate row: none
yet — TextKit is not in Gates.Packages' gated set; TextKitTests.Axioms
pins the core triple over the headline lemmas.
-/

module

public import TextKit.Basic
public import TextKit.Lemmas
public import TextKit.Suggest
public import TextKit.Diag
public import TextKit.Error
public import TextKit.Combinators
