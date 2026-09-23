/-
LintKit.TestFixtures.Cross — cross-module duplicate POSITIVE control for the
package-root-scoped dupDefBodies linter. `dupCrossB` lives in this module;
its twin `dupCrossA` is planted in `Violations.lean`. The pair shares the
package root `LintKit` but sits in DIFFERENT modules — the old per-module
clustering never saw it; the package-root scope must. (intra-module pairs
are still covered by `dupOne`/`dupTwo`.)
-/
import LintKit.Basic

namespace LintKit.TestFixtures.Cross

/-- Planted: cross-module duplicate of
`LintKit.TestFixtures.Violations.dupCrossA`. -/
def dupCrossB (x : Nat) : Nat := x + 99

end LintKit.TestFixtures.Cross
