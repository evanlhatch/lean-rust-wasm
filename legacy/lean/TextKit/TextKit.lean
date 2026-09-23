/-
# TextKit — the core-only text/parser foundation

Lifted out of substrait (`Substrait.Decode.Basic` + `Substrait.Emit.Text`'s
four text primitives) so consumers below substrait can parse text without
depending on substrait. See `TextKit.Basic`'s header for the moved surface,
what stayed in substrait, and the re-export contract.

Module map:
- `TextKit.Basic` — the `Parser` monad, the text primitives
  (`isIdentChar`/`isIdentifier`/`escape`/`name`), the scanners
  (`scanIdent`/`scanQuotedRaw`/`scanName`/`scanNat`/`scanInt`/`startsWith`/
  `expect`), and the inversion-lemma kit (escape/unescape, quoted-name,
  bare-name, prefix). One module by design: the inversion proofs unfold the
  `where`-clause helper equation lemmas of the scanners — splitting them
  across modules buys nothing and risks the exposure surface.
- `TextKit.Grammar` — the grammar AS DATA: the closed token-stream
  `Grammar` value (tok/until/seq/alt/rep/rec), the byte-exact `emit`, the
  payload recognition `pOf`/`parseTokens` over the `Parser` monad, GWF +
  `checkGWF`, and the token-list inversion laws (`invert_core`,
  `invert_rep`, `invert_rep_behind_tok`). The gates' manifest parser
  consumes it (W-C1).
- `TextKit.Diag` — parse diagnostics: the `Diag` outcome, the
  failure-instrumented `DParser` lane, `labels`/`farthestFailure`, and
  `renderDiag` (the farthest-failure reporting the consumers surface).
- `TextKit.FormatLaws` — the byte-exact rendering laws for `Std.Format`:
  the provable hard-line rendering model (`renderGo`/`renderFmt`),
  rendering-level append associativity + the `joinSep`/`nest`-under-line
  laws, and the STRUCTURAL fmt-injectivity set (mirroring
  `SchemaLang.Emit.Wit`'s, name-for-name, for the later pure code motion).
-/

module

public import TextKit.Basic
public import TextKit.Grammar
public import TextKit.Diag
public import TextKit.FormatLaws
