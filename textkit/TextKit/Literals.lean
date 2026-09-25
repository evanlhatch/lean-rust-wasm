/-
# TextKit.Literals — the shared literal-toList rfl family

The cross-format literal tokens (notes/v3/15-patterns.md #12's
inversion-kit companion): every text format's proofs need `"c".toList`
= the cons spelling of its separators, and the SAME separators recur —
newline, space, comma, the parens — so the rfl family has ONE home
here instead of one copy per consumer (the Wit.Parse L_nl family, the
SchemaCore.Snapshot lcomma family, the Kit.CodeRegistry nl_list — the
third adopts on its next touch; kit/+ is another agent's zone).

Per-format literals (a format's own word and block spellings —
`"package "`, `"  record "`, `" {\n"`, …) are DOCTRINE and stay with
their format; only the shared singletons and their whitespace-run
composites land here.

The five questions (notes/v3/01-core.md):
- root: Universe — pure String/List-Char rfl facts, no imports.
- carrier grade: none — definitional equalities.
- spine reading: the literal face every format's render/parse
  round-trip rides.
- ladder rung: rfl (the house's one-per-literal discipline, hoisted).
- gate row: none — TextKit is outside Gates.Packages' gated set's
  special rows; TextKitTests pins the cone.
-/

module

@[expose] public section

namespace TextKit

/-! ## the shared singletons -/

/-- The newline (every LF-terminated line format). -/
theorem lit_nl : "\n".toList = ['\n'] := rfl

/-- The space (every space-separated format). -/
theorem lit_sp : " ".toList = [' '] := rfl

/-- The comma (every comma-separated format). -/
theorem lit_comma : ",".toList = [','] := rfl

/-- The open paren (the paren encodings: `option(u64)`, …). -/
theorem lit_lparen : "(".toList = ['('] := rfl

/-- The close paren. -/
theorem lit_rparen : ")".toList = [')'] := rfl

/-! ## the whitespace-run composites (built from the singletons) -/

/-- The four-space indent. -/
theorem lit_sp4 : "    ".toList = [' ', ' ', ' ', ' '] := rfl

/-- The newline + four-space indent (a continuation line's head). -/
theorem lit_nlsp4 : "\n    ".toList = '\n' :: "    ".toList := rfl

/-- The colon-space separator (`name: ty`). -/
theorem lit_colsp : ": ".toList = ':' :: " ".toList := rfl

end TextKit
