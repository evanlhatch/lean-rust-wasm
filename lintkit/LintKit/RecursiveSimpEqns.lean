/-
LintKit.RecursiveSimpEqns — "every recursive def ships `@[simp]` equation
lemmas" (mined from legacy/lean/LintKit/LintKit/RecursiveSimpEqns.lean).

For each recursive def (`Lean.Meta.isRecursiveDefinition`) in a linted
module, the equation lemmas from `getEqnsFor?` must all be simp lemmas, or
the def itself must be simp-adjacent (tagged `@[simp]` directly — for a def
that registers via `toUnfold`/`toUnfoldThms` in the default simp set).

CAUTION: the legacy asked `getEqnsFor?` — the equation GENERATOR — per
def. In this tree that call is a landmine: on some defs (e.g.
`TestingKit.Tape.advance`, a UInt64-LCG stepper) the generator aborts the
whole process with an UNCAUGHT `maxRecDepth` failure that escapes even
the runner's tryCatch. So this port never GENERATES equations: it reads
the default simp SET — the def is quiet iff it is simp-adjacent
(`isSimpDef`: tagged `@[simp]` directly, registered via `toUnfold`/
`toUnfoldThms`) or its well-known auto-eqn names (`decl.eq_1` …
`decl.eq_9`, `decl.eq_def`) are already simp lemmas. A recursive def
whose eqns exist but are simp-by-other-names is a false positive —
documented, and the census is a report, not a gate.

Default-OFF (the `default_false` token below): the census answers
"which recursive defs ship no simp equations" for every def of a
package; when the dominant cluster is the deliberate raw-equation-proof
pattern, the count is REPORTED, not gated:

  lake exe lintkit --enable=linter.guestlang.recursiveSimpEqns <roots>

Opt out per site: `@[nolint linter.guestlang.recursiveSimpEqns "reason"]`.

The five questions (notes/v3/01-core.md):
- root: none — the simp-discipline census.
- carrier grade: none — host machinery.
- spine reading: interpretation (env → findings).
- ladder rung: n/a.
- gate row: census only (default OFF) — the sweep reports, the gate does
  not consume.
-/
module

public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- Is `decl` itself `@[simp]`-tagged (def-to-unfold, possibly with its
equation lemmas registered via `toUnfoldThms`)? -/
def isSimpDef (decl : Name) : CoreM Bool := do
  let st ← Meta.getSimpTheorems
  return st.isDeclToUnfold decl || st.toUnfoldThms.contains decl

/-- The auto-generated equation-lemma names probed for simp membership
(no GENERATION — see the module header's landmine note). -/
def eqnNameProbe (decl : Name) : Array Name :=
  (Array.range 9).map (fun i => decl.append (.num `eq (i + 1)))
    |>.push (decl.append `eq_def)

meta def recursiveSimpEqnsTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  match env.find? decl with
  | some (.defnInfo _) => pure ()
  | _ => return none
  unless ← isRecursiveDefinition decl do return none
  if ← isSimpDef decl then return none
  let st ← Meta.getSimpTheorems
  if (eqnNameProbe decl).any (fun n => st.isLemma (.decl n)) then return none
  return some m!"recursive definition ships no `@[simp]` equation lemmas \
    (none of its auto-eqns `{decl}.eq_*` are in the default simp set) — \
    either tag them (or the def) `@[simp]`, or opt out with \
    `@[nolint linter.guestlang.recursiveSimpEqns \"reason\"]` if simp must not \
    see these equations (simp loops / raw-equation proofs)"

meta def recursiveSimpEqnsLinter : EnvLinter where
  test := recursiveSimpEqnsTest
  noErrorsFound := "every recursive definition ships `@[simp]` equation lemmas"
  errorsFound := "recursive definitions without `@[simp]` equation lemmas"

end LintKit

-- the census linter: registered default-OFF via the `default_false` token
-- (LintKit.Basic — the one-liner registration).
register_guestlang_linter linter.guestlang.recursiveSimpEqns
  LintKit.recursiveSimpEqnsLinter default_false
  "flag recursive definitions whose equation lemmas do not carry `@[simp]` \
    (census: default OFF — the sweep reports, the gate does not consume)"
