/-
LintKit — the minimal linter engine (notes/v3/09-gates-ops.md §3's
`lean-lint` row). Umbrella: the `@[nolint]` attribute + the skip
discipline + the first three env-linters (axiom allowlist, package
namespace, duplicate def bodies incl. the upstream extension) + the
runner the `lintkit` exe drives. Core-only: no LSpec/mathlib, so any
package may import it.

The five questions (notes/v3/01-core.md): answered per submodule (the
imports below); the umbrella answers none — import point. Gate row:
LintKit IS a gated package (the axiom report sweeps its roots) and
the lintkit exe drives its linters over the gated roots.
-/
module

public import LintKit.Basic
public import LintKit.AxiomAllowlist
public import LintKit.PackageNamespace
public import LintKit.DupDefBodies
public import LintKit.Runner
