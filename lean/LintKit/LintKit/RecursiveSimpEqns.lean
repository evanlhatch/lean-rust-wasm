/-
LintKit.RecursiveSimpEqns — notes/lean-refactor-guide.md 6.2, doctrine §2:
"every recursive def ships `@[simp]` equation lemmas".

For each recursive def (`Lean.Meta.isRecursiveDefinition`) in a linted
module, the equation lemmas from `getEqnsFor?` must all be simp lemmas, or
the def itself must be simp-adjacent (tagged `@[simp]` directly — for a def
that registers via `toUnfold`/`toUnfoldThms` in the default simp set).

CAUTION (doctrine §8, substrait Decode): proofs that consume RAW equation
lemmas (`parseType.eq_*`) legitimately keep them out of simp to avoid simp
loops and term-shape churn. If the tree census shows that pattern dominates,
this linter ships default-OFF (option default flips to `false` below) and
runs only as an explicit census — the violation count is then reported, not
gated. Opt out per site:
`@[nolint linter.guestlang.recursiveSimpEqns "reason"]`.

The option is declared at top level (see LintKit.Basic's header note).
-/
module

public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

-- Default-OFF (2026-11 census): 83 violations across the tree (substrait
-- 64, Machines 7, dbsp 8, wasm-backend 4) and the dominant cluster is
-- DELIBERATE — doctrine §8: substrait's Decode proofs consume raw
-- equation lemmas (`parseType.eq_*`), and fuel-based runners
-- (`Machine.run`, …) keep equations out of simp to
-- avoid simp loops. Far past the "handful of nolint sites" bar for
-- default-on. Run explicitly as a census:
--   guestlang-lint --enable=linter.guestlang.recursiveSimpEqns <roots>

namespace LintKit

/-- Is `decl` a simp lemma (any polarity/inv) in the default simp set? -/
def isSimpLemma (decl : Name) : CoreM Bool := do
  let st ← Meta.getSimpTheorems
  return st.isLemma (.decl decl)
    || st.isLemma (.decl decl (post := false))
    || st.isLemma (.decl decl (inv := true))
    || st.isLemma (.decl decl (post := false) (inv := true))

/-- Is `decl` itself `@[simp]`-tagged (def-to-unfold, possibly with its
equation lemmas registered via `toUnfoldThms`)? -/
def isSimpDef (decl : Name) : CoreM Bool := do
  let st ← Meta.getSimpTheorems
  return st.isDeclToUnfold decl || st.toUnfoldThms.contains decl

meta def recursiveSimpEqnsTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  match env.find? decl with
  | some (.defnInfo _) => pure ()
  | _ => return none
  unless ← isRecursiveDefinition decl do return none
  if ← isSimpDef decl then return none
  let eqns? ← tryCatch (getEqnsFor? decl) fun _ => pure none
  match eqns? with
  | none =>
    return some m!"recursive definition has no equation lemmas available \
      (getEqnsFor? returned none) — consumers cannot rewrite by it"
  | some eqns =>
    let mut nonSimp : Array Name := #[]
    for e in eqns do
      unless ← isSimpLemma e do nonSimp := nonSimp.push e
    if nonSimp.isEmpty then return none
    return some m!"recursive definition's equation lemmas lack `@[simp]`: {
      nonSimp.toList} — either tag them (or the def) `@[simp]`, or opt out with \
      `@[nolint linter.guestlang.recursiveSimpEqns \"reason\"]` if simp must not \
      see these equations (simp loops / raw-equation proofs, doctrine §8)"

meta def recursiveSimpEqnsLinter : EnvLinter where
  test := recursiveSimpEqnsTest
  noErrorsFound := "every recursive definition ships `@[simp]` equation lemmas"
  errorsFound := "recursive definitions without `@[simp]` equation lemmas"

end LintKit

-- the census linter: registered default-OFF via `register_guestlang_linter`'s
-- `default_false` token (LintKit.Basic — the one-liner registration).
register_guestlang_linter linter.guestlang.recursiveSimpEqns
  LintKit.recursiveSimpEqnsLinter default_false
  "flag recursive definitions whose equation lemmas do not carry `@[simp]`"
