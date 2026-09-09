/- LintKit — the guestlang custom linter layer (notes/lean-refactor-guide.md
   Phase 6). Umbrella: options + `@[nolint]` + the four env-linters + the
   pure text lints + the runner shared by the `guestlang-lint` exe and the
   self-tests. -/
import LintKit.Basic
import LintKit.AxiomAllowlist
import LintKit.RecursiveSimpEqns
import LintKit.DupDefBodies
import LintKit.PackageNamespace
import LintKit.TextLints
import LintKit.Runner
