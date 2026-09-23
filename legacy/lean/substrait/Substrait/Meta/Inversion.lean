/-
# Substrait.Meta.Inversion — `declare_inversion`: RETIRED (W-C2)

**The recast (W-C2) retired this module's generative machinery.** The
urn/decl/version rows that `declare_inversion` inverted with generated
proof fragments are now `TextKit.Grammar` VALUES over one grammar per row
(`Substrait.Decode.RowG` + `Substrait.Decode.inv_*` in Decode.Plan.lean):
the generic inversion law `TextKit.Grammar.invert_core` re-derives the
round trip at the token layer (`RowG.urnLine_tokens` et al. — its FIRST
consumers), the emitter's row strings are the grammar's fold
(`RowG.*_emit`, drift-tied), and the old theorem names survive as the
keep-alive corollaries `inv_urnLine`/`inv_declLine`/`inv_versionLines`
(the parse-layer walks that read the field slots from the input stay hand
— a parser cannot instantiate a row grammar's token data; see the
section header in Decode.Plan.lean).

This module now exists ONLY as the command's syntax shell: the
`Substrait.Decode.Inversions` entries (which predate the recast and are
NOT this module's to edit) must keep PARSING — so every syntax category,
atom, and the command registration below stay — while the elaborator
generates NOTHING (the exact pattern `invcor` already used: accepted,
inert). The rows live in the grammar fold now; an entry here is a
lineage note, not a generator.

Core-only: `public import Lean` — the command's syntax needs the macro
machinery, nothing else.
-/

module

public import Lean

public meta section

namespace Substrait.Meta

open Lean Lean.Parser.Command Lean.Elab.Command

/-- A `line` segment (kept — the entries parse; nothing reads them). -/
declare_syntax_cat inversionSeg

syntax (name := invLit) "invlit " str : inversionSeg
syntax (name := invTok) "invtok " ident str : inversionSeg
syntax (name := invPfx) "invpfx" : inversionSeg
syntax (name := invDot) "invdot" : inversionSeg
syntax (name := invAnchor) "invanchor " ident : inversionSeg
syntax (name := invNum) "invnum " ident : inversionSeg
syntax (name := invName) "invname " ident : inversionSeg

/-- A resolution step (kept — the entries parse; nothing reads them). -/
declare_syntax_cat inversionStep

syntax (name := invReduce) "invreduce " term : inversionStep
syntax (name := invScan) "invscan " ident : inversionStep
syntax (name := invPeel) "invpeel " str : inversionStep
syntax (name := invExpect) "invexpect " ident : inversionStep
syntax (name := invFinish) "invfinish" : inversionStep
syntax (name := invTail) "invtail" : inversionStep

/-- The `cor <oldName>` block — RETIRED (accepted, generates nothing). -/
declare_syntax_cat inversionCor
syntax (name := invCor) "invcor " " := " ident : inversionCor

/-- The optional `proof := by …` bespoke tail — RETIRED (accepted, inert;
    the version row's presence conditional lives in `Decode.Plan`'s
    `inv_versionLines` now). -/
declare_syntax_cat inversionProof
syntax (name := invProof) "invproof " " := " term : inversionProof

/--
`declare_inversion <name> where …` — RETIRED by the W-C2 recast: the
command parses (so the pre-recast `Substrait.Decode.Inversions` entries
keep elaborating — the syntax shell stays registered) but generates
NOTHING. The row inversions are the grammar fold in
`Substrait.Decode.Plan` (`RowG` values + `invert_core` consumers +
the `inv_*` corollaries). See the module header.
-/
syntax (name := declareInversion)
  "declare_inversion " ident " where"
  " invparse " " := " term
  " invent " " := " term
  " invbinders " " := " bracketedBinder*
  " invresult " " := " term
  " invline " " := " "[" inversionSeg* "]"
  " invsteps " " := " "[" inversionStep* "]"
  optional(inversionCor) optional(inversionProof) : command

/-- The inert elaborator: the entry parses (the syntax shell above is
    registered), the elaborator generates NOTHING — the W-C2 recast owns
    the rows (see the module header; the kind check makes the body
    deliberately non-identical to the upstream no-op elaborators). -/
@[command_elab declareInversion]
def elabDeclareInversion : CommandElab := fun stx => do
  unless stx.isOfKind ``declareInversion do
    throwError "declare_inversion: syntax shell mismatch (retired)"

end Substrait.Meta

end -- public meta section
