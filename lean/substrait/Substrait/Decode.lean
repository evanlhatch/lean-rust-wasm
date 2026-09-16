/-
# Substrait.Decode — the text decoder (the emitter's inverse)

lean-v3 step 8 / D6: the parser shares the emitter's skeleton factorization
and `parse ∘ emit = id` is the theorem. Hand-rolled recursive descent over
`List Char` (D15) — structural prefix scanners for the leaves (proved) and
fuel-bounded recursion for the grammar layers (the project's fuel
discipline), rather than Parsec's `partial` combinators (proof-hostile).

Proved layer so far:
- `unescape_escape`: unescaping inverts `Emit.Text.escape`.
- `scanQuotedRaw_escChars`/`scanQuotedRaw_escape`: the raw quoted scanner
  recovers escape text (pairs never misread as the closing quote).
- `scanIdent_of_identifier`, `scanName_quoted`, `scanName_name`: the name
  inversion (`Emit.Text.name` scans back to the name, both branches).
- the TYPED wire decode: `decodeExpr`/`decodeArgs` + `decodeExpr_reEnc`/
  `decodeArgs_reEnc` (decode → lower recovers the wire term), and
  `decodeRel` + `decodeRel_reEnc` (the full `Typed.Rel` grammar: read /
  filter / project / aggregate / sort / fetch / join / set / write /
  extensionSingle; wire-side rejections for cross/extensionLeaf/
  extensionMulti).  `Rel.okS` is the hypothesis predicate (per-node
  recursion plus the decoded-schema pins the GADT demands — see its
  comment).

The full-plan round trip is executable-witnessed in Tests (decode-emit = id
on the golden plan; emit-decode byte-identical on the golden text).

Wire-decode notes (the rel layer):
- the mutual-block `Proto.Rel` defeats structural recursion, its derived
  `sizeOf` simproc disagrees with the instance funs, and `sizeOf` in a
  definition body hits an LCNF codegen failure — `decodeRel` is therefore
  well-founded on the actual `sizeOf` instance with hand-proved decreasing
  goals (`wf*_size`, from the instance funs, simproc-free);
- schema equality for the square/set checks uses `DecidableEq SType`
  (defined via `SType.eqAns` in `Schema.lean`);
- the master theorem compares at the WIRE level (decode → `relLower` = id):
  the decoded rel's projection names are placeholders (`""`) and its
  `FunctionSig.deterministic`/`sessionDependent` are re-derived defaults —
  both are erased by the wire, so the wire-level statement is the honest
  strongest form (the same convention as `decodeExpr_reEnc`).

Documented lossiness (the format, not the decoder): `RelCommon.direct` vs
absent emit kinds print identically (canonicalized to `none` on parse);
`advancedExtension` never prints; extension declarations print in
(anchor, kind) order; explicit-emit `Project`s (mapping baked into args)
are not invertible and rejected.


Module map (W5.3 phase 1 — pure code-motion split along the section
structure; this hub only imports):
- `Substrait.Decode.Basic` — the parser monad, escapes, name scanners,
  the prefix kit.
- `Substrait.Decode.Types` — `parseType`, the fuel lemmas, the type
  inversion ladder.
- `Substrait.Decode.Expr` — the literal/expression parsers and their
  inversion ladder.
- `Substrait.Decode.Rel` — the relation line-tree parsers and the
  line-shape pairings (`splitOnPipe_self`, `indentOf_indentUnits`,
  `drop_indentUnits`).
- `Substrait.Decode.Plan` — the plan driver, the parser-layer inversion
  theorems, and the W5.3-phase-2b line inversions (extension entries,
  version header, Root names).
- `Substrait.Decode.Typed` — the typed `decodeExpr`/`decodeArgs` and
  the expression re-encode theorem.
- `Substrait.Decode.TypedRel` — the size facts, the typed `decodeRel`,
  and the rel re-encode capstone.

W5.3 phase 2b: the LINE-SHAPE grammar (separators, keywords, section
markers, the indent rule, extension-block kinds, cast failure behaviors,
the binary sentinel) is single-sourced in `Substrait.Grammar` — every
`expect`/`startsWith` site here and every `++`-chain in `Emit.Text` names
the same constant. Resistant sites (char-level `match` patterns, the
`null`/`true`/`false` value words, `relWidth` vs `relWidthD`) are noted at
their definitions and in the `Substrait.Grammar` header.
-/
import Substrait.Decode.Basic
import Substrait.Decode.Types
import Substrait.Decode.Expr
import Substrait.Decode.Rel
import Substrait.Decode.Plan
import Substrait.Decode.Typed
import Substrait.Decode.TypedRel
