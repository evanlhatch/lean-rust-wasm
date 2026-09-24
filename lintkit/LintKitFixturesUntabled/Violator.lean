/-/
LintKitFixturesUntabled.Violator — the cone linter's LOUD-GAP tooth.

The project root `LintKitFixturesUntabled` is deliberately NOT in the
cone table (`LintKit.Cone.coneOfRoot?`). The first cut's discipline
returned `#[]` for an untabled importer — a landed library that forgot
its table row passed the cone rule SILENTLY. The fixed linter routes an
untabled importer to `ConeVerdict.untabled` (a FINDING: "land its row
deliberately"), so this module must fire exactly the cone-gap finding in
LintKitTests.Main's teeth — never silently, never anything else.

The imports are deliberately all C0 and tabled: the ONLY planted finding
here is the untabled root itself (a single-purpose tooth).
-/
import LintKit.Cone

namespace LintKitFixturesUntabled.Violator

/-- A token decl: the module must elaborate (the fixture rides the
LintKitTestsLib build), and its content must trip nothing — the
untabled-root gap is the sole finding. -/
def planted : Nat := 0

end LintKitFixturesUntabled.Violator
