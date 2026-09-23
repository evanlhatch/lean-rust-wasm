/-
# Substrait.Decode.Basic — the parser core, re-homed onto TextKit

The substrait-AGNOSTIC parser machinery — the `Parser` monad, the scanners
(`scanIdent`/`scanQuotedRaw`/`scanName`/`scanNat`/`scanInt`/`startsWith`/
`expect`), the escape/unescape kit, and the WHOLE inversion-lemma set
(`unescape_escape`, `scanQuotedRaw_*`, `scanIdent_of_identifier`,
`scanName_*`, `expect_self`/`startsWith_self`) — LIVES in `TextKit.Basic`
now (core-only, below substrait; future consumers reach it without a
substrait dependency). The four text primitives the kit is proved over
(`isIdentChar`/`isIdentifier`/`escape`/`name`) moved there too, out of
`Emit.Text`.

This module is the compatibility re-export: every historical
`Substrait.Decode.*` name resolves to its TextKit home (the SAME constant —
`export`, not a copy), so downstream files and the axiom baseline are
unchanged modulo the alias. The behavior stays pinned by the goldens/sweeps
(byte-tie law: zero behavior change).

Never moved (grammar-specific, substrait's by construction): the token/name
tables — `Substrait.Grammar`'s urn/join/set/sort rows and every `*Tok`
constant — stay in `Substrait.Grammar`.
-/

module

public import Substrait.Emit.Text
public import TextKit

@[expose] public section

namespace Substrait.Decode

export TextKit (Parser
  Parser.result Parser.bind Parser.bind_apply Parser.fail Parser.peek Parser.rest
  Parser.jump Parser.consumeChar Parser.takeWhile Parser.pure_apply
  Parser.consumeChar_self
  scanIdent.scanIdentGo scanNat.scanNatGo scanName.scanNameGo
  escChars unescapeGo unescape
  scanIdent scanQuotedRaw scanName
  startsWith expect scanNat scanInt
  toString_char_toList escapeArm_eq escape_toList
  unescapeGo_escChars unescape_escape
  scanQuotedRaw_escChars scanQuotedRaw_escape
  scanIdent_of_identifier scanName_quoted scanName_name
  startsWith_self expect_self)

end Substrait.Decode

end
