/-
LintKit.AxiomAllowlist — the env-linter form of the axiom sweep
(notes/v3/09-gates-ops.md §3's `lean-axioms` row; mined from
legacy/lean/LintKit/LintKit/AxiomAllowlist.lean).

For every theorem/def/opaque declared in a linted module, `collectAxioms`
and flag dependencies outside the allowlist: the core triple
(`propext`, `Classical.choice`, `Quot.sound`) plus the disclosed
`native_decide` trust base — matched by the rule the axiom gate uses: an
axiom name containing `_native.native_decide.` (the v4.33 shape), or its
`_native.bv_decide.` sibling (the same runner-checked certificate class).
A bare `axiom` declaration is flagged unless its own name is allowlisted.

This is the per-declaration upgrade over hand-maintained `#print axioms`
lists: coverage is every linted decl, not a remembered headline set.
Opt out per site with `@[nolint linter.guestlang.axiomAllowlist "reason"]`.

The option is declared at top level (see LintKit.Basic's header note),
via the `register_guestlang_linter` one-liner at the bottom.

The five questions (notes/v3/01-core.md):
- root: none — the gate machinery's trust-base row.
- carrier grade: none — the allowlist is a Bool predicate over axiom
names.
- spine reading: the interpretation stage of the axiom sweep (env →
findings); the gates consume it, never re-encode it.
- ladder rung: this linter IS 01 §7's disclosure mechanism — the
allowlist names the accepted axiom surface (core triple + disclosed
native_decide/bv_decide), nothing else.
- gate row: the axiom gate (Gates.Axioms) + the lintkit sweep.
-/
module

public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- The axiom allowlist: core triple + disclosed native_decide/bv_decide
trust bases. THE allowlist — the gates consume this, never re-encode it. -/
def isAllowedAxiom (n : Name) : Bool :=
  n == `propext || n == `Classical.choice || n == `Quot.sound ||
  -- the disclosed native_decide trust base + its bv_decide sibling
  -- (the same runner-checked certificate class: `Foo._native.bv_decide.ax_*`)
  ((toString n).splitOn "_native.native_decide.").length != 1 ||
  ((toString n).splitOn "_native.bv_decide.").length != 1

meta def axiomAllowlistTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  let some info := env.find? decl | return none
  match info with
  | .axiomInfo _ =>
    if isAllowedAxiom decl then return none
    return some m!"declaration is itself an axiom outside the allowlist \
      (propext, Classical.choice, Quot.sound, disclosed native_decide trust base). \
      Zero-sorry/zero-axiom is the gate (notes/v3/06-lean-rules.md)"
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
    let axioms ← collectAxioms decl
    let bad := axioms.filter fun a => !isAllowedAxiom a
    if bad.isEmpty then return none
    return some m!"depends on axioms outside the allowlist: {
      bad.toList} (allowed: propext, Classical.choice, Quot.sound, \
      *_native.native_decide.*)"
  | _ => return none

meta def axiomAllowlistLinter : EnvLinter where
  test := axiomAllowlistTest
  noErrorsFound := "no declarations depend on non-allowlisted axioms"
  errorsFound := "declarations depending on non-allowlisted axioms"

end LintKit

register_guestlang_linter linter.guestlang.axiomAllowlist LintKit.axiomAllowlistLinter
  "flag declarations depending on axioms outside the allowlist \
    (propext, Classical.choice, Quot.sound, disclosed native_decide trust base)"
