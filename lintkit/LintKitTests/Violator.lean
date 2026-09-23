/-
LintKitTests.Violator — the PLANTED cone violation (the cone linter's
positive control). This module's root `LintKitTests` is C0 in
`LintKit.coneOfRoot?`, but it imports `SchemaCore`, whose root is C1:
a cone-low module importing cone-high — notes/v3/06-lean-rules.md §8's
gate failure, fired by `LintKit.coneModuleTest` via the runner's
module-level pass.

Empty ON PURPOSE: an empty module can violate, which is exactly why the
cone linter is module-level, not per-declaration. This file imports
nothing else — the ONLY offence it can plant is the SchemaCore import.
Evidence, not architecture — the five-question block lives in the modules under test.
-/
import SchemaCore
