/-
LintKit — the minimal linter engine (notes/v3/09-gates-ops.md §3's
`lean-lint` row). Umbrella: the `@[nolint]` attribute + the skip
discipline + the env-linters (axiom allowlist, package namespace,
duplicate def bodies incl. the upstream extension, bare checker, verdict
constructors, recursive-simp census, guest ban + the `@[guest]`/
`@[guest_std]` gate) + the text lints (no-new-partial, nolint reason,
codec registration, did-you-mean) + the runner the `lintkit` exe drives.
Core-only: no LSpec/mathlib, so any package may import it.

The five questions (notes/v3/01-core.md): answered per submodule (the
imports below); the umbrella answers none — import point. Gate row:
LintKit IS a gated package (the axiom report sweeps its roots) and
the lintkit exe drives its linters over the gated roots.
-/
module

public import LintKit.Basic
public import LintKit.AxiomAllowlist
public import LintKit.Citations
public import LintKit.PackageNamespace
public import LintKit.DupDefBodies
public import LintKit.GuestGate
public import LintKit.DecideFirst
public import LintKit.Graduation
public import LintKit.ZeroCitation
public import LintKit.Runner
