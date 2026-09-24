/-
LintKit.VerdictCtors — "verdicts are constructors, never strings or
collapsed booleans" (notes/v3/04 §6's error-quality/verdict discipline)
as an env-linter.

The compliant shapes in this tree: `SchemaCore.CheckVerdict` and
`Machines.Explore.Verdict` — enumerated inductive verdicts (checked/
failed, proved/refuted/unknown) carrying their evidence. The finding is
a def whose NAME names a verdict while its RESULT TYPE collapses to
`String` or `Bool`: a verdict-shaped name returning String encodes the
verdict as a parseable message (the consumer string-matches it — drift);
returning Bool merges the trichotomy (01-core §3: budget exhaustion is
UNKNOWN, never false).

Name heuristic: the result type is `String`/`Bool` (through leading
binders, like bareChecker's walk) and the def's name signals verdict-
ness — the LEAF starts with `verdict`/`outcome` (case-insensitive:
`verdictOf`, `outcomeFor`), or some name component ENDS with
`verdict`/`outcome` (`checkVerdict`, `CheckVerdict.ofRows`) — except the
rendering/projection verbs (`render`, `toString`, `show`, `print`,
`pretty`, `toBool`): a REAL verdict's renderer is legitimate
(`Verdict.render : Explore.Verdict → String` stays quiet — it renders an
enumerated verdict; it does not produce one).

Exemptions: test modules (the bareChecker precedent), `abbrev`s.
Opt out per site: `@[nolint linter.guestlang.verdictCtors "reason"]`.

The five questions (notes/v3/01-core.md):
- root: none — 04 §6's verdict discipline, mechanical.
- carrier grade: none — host machinery.
- spine reading: interpretation (env → findings) for the verdict class.
- ladder rung: n/a.
- gate row: the lintkit sweep over the gated roots.
-/
module

public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- Result-type test: `String` or `Bool` through leading binders. -/
def stringOrBoolResult : Expr → Bool
  | .forallE _ _ b _ => stringOrBoolResult b
  | .lam _ _ b _ => stringOrBoolResult b
  | e => e.isConstOf `String || e.isConstOf `Bool

/-- The rendering/projection/comparison verbs: a verdict's RENDERER or
equality machinery is legitimate (leaf names exempt from the verdict-
ness reading — `beq` covers the derived `instBEq…Verdict` instances). -/
def renderVerbs : List String :=
  ["render", "toString", "show", "print", "pretty", "toBool", "beq"]

/-- The verdict-ness name test: leaf starts with `verdict`/`outcome`
(case-insensitive), or a name component ends with one — minus the
rendering verbs. -/
def isVerdictShapedName (decl : Name) : Bool :=
  match decl with
  | .str _ leaf =>
      let low := leaf.toLower
      let verbs := renderVerbs
      if verbs.any (low == ·.toLower) then false
      else low.startsWith "verdict" || low.startsWith "outcome"
        || decl.components.any (fun c =>
          let s := c.toString.toLower
          s.endsWith "verdict" || s.endsWith "outcome")
  | _ => false

meta def verdictCtorsTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  let some (.defnInfo di) := env.find? decl | return none
  if ← isReducible decl then return none
  let some idx := env.getModuleIdxFor? decl | return none
  let mod := env.header.moduleNames[idx]!
  if (mod.toString.splitOn ".").contains "Tests" then return none
  unless isVerdictShapedName decl do return none
  unless stringOrBoolResult di.type do return none
  return some m!"collapsed verdict: `{decl}` is named like a verdict but \
    returns String/Bool — verdicts are constructors carrying their \
    evidence (an enumerated inductive, 04 §6: `CheckVerdict` / \
    `Explore.Verdict` are the compliant shapes); a String verdict is \
    parsed back by its consumers, a Bool verdict merges the honest \
    trichotomy; opt out with \
    `@[nolint linter.guestlang.verdictCtors \"reason\"]`"

meta def verdictCtorsLinter : EnvLinter where
  test := verdictCtorsTest
  noErrorsFound := "every verdict-shaped def returns an enumerated constructor"
  errorsFound := "collapsed verdicts (verdict-shaped names returning String/Bool)"

end LintKit

register_guestlang_linter linter.guestlang.verdictCtors LintKit.verdictCtorsLinter
  "flag defs named like verdicts (verdict*/outcome*/…Verdict) returning \
    String or Bool — verdicts are constructors, never strings/collapsed \
    booleans (04 §6)"
