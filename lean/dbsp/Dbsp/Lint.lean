/-
# Dbsp.Lint — the doctrine lint bundle

One import that turns on the project's lint set: mathlib's `flexible`
linter (no rigid tactics after a bare `simp` — the agent-proof fragility
class, lean/AGENTS.md trap 9 lineage) plus the style lints we opt into.
Imported by the leaf modules (Dbsp.Stream, Machines.Foundations,
Flatland.Value) so every downstream file elaborates with these registered.

The options themselves are set per-package in the lakefiles
(`weakLeanArgs`) so test files can override.
-/
import Mathlib.Tactic.Linter.FlexibleLinter
import Mathlib.Tactic.Linter.Style
