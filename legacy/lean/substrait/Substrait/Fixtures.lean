/-
# Substrait Test Fixtures

Shared schema definitions used across multiple test suites (SubstraitTests,
QLangTests).  Pure data — no TestKit dependency — so it lives in the
Substrait library itself.

Only the definitions genuinely shared are exported here.  Per-suite schemas
stay in their respective Tests/Main.lean.
-/

module

public import Substrait.Typed

@[expose] public section

open Substrait.Typed

/-- The units relation: health, regen — both nullable i32. -/
abbrev units : Schema :=
  [("health", .i32, true), ("regen", .i32, true)]

end -- @[expose] public section