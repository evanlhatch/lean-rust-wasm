/- LintKit — the guestlang custom linter layer (notes/lean-refactor-guide.md
   Phase 6). Umbrella: options + `@[nolint]` + the four env-linters + the
   pure text lints + the runner shared by the `guestlang-lint` exe and the
   self-tests. -/
module

public import LintKit.Basic
public import LintKit.DeclCheck
public import LintKit.GuestBan
public import LintKit.AxiomAllowlist
public import LintKit.RecursiveSimpEqns
public import LintKit.DupDefBodies
public import LintKit.PackageNamespace
public import LintKit.TextLints
public import LintKit.Runner
