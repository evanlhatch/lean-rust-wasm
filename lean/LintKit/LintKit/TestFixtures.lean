/- LintKit.TestFixtures — umbrella for the planted-violation fixture modules
   (the `LintKitFixtures` lean_lib root). NOT imported by `LintKit.lean`:
   the `just lean-lint` gate lints the `LintKit` root's import closure and
   must never see these. -/
import LintKit.TestFixtures.Violations
import LintKit.TestFixtures.Clean
import LintKit.TestFixtures.Cross
