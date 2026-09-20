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
-/

module

public import TextKit.Basic
