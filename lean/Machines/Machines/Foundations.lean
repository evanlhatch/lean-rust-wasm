/-
# Machines.Foundations — the correspondence-kit re-export

The correspondence kit (`Iso`/`PartialIso`/`CheckedProp`)
moved to `CodegenCore.Kit` (the kit needs zero
mathlib; this package has it). Re-exported below so the `Machines.` names
keep working for downstream. The two mathlib LINTER imports register the
package's lint config — they serve nothing in the kit itself.
-/

module

public import Mathlib.Tactic.Linter.FlexibleLinter
public import Mathlib.Tactic.Linter.Style
public import CodegenCore.Kit
-- The umbrella `public import Batteries` was deleted (hygiene batch):
-- the only Batteries-named entity this file uses is the `library_note`
-- command below, so the import is targeted at its home module.
public import Batteries.Util.LibraryNote

@[expose] public section

library_note machineAssemblePattern /--
  The veil Assemble pattern: a generated inductive for `Machine.Label` means
  proofs case-split and execution enumerate the SAME generated set of labels;
  they cannot drift. This is the two-projections core: Projection 1 (executable:
  `step?`, `run`) and Projection 2 (proof: `tr`) both consume the same labels,
  so execution and verification stay aligned.
-/

namespace Machines

/-- The kit's home is CodegenCore (core-only); the
    `Machines.` aliases keep every existing use compiling. `abbrev` (not
    `export` — core Lean 4 has no `export` command): reducible, so instance
    search and anonymous constructors see through them (the AGENTS.md
    abbrev rule). Dotted names do NOT unfold aliases, so the member names
    (`CheckedProp.ofComplete`, …) get their own one-line aliases. -/
abbrev Iso := CodegenCore.Iso
abbrev PartialIso := CodegenCore.PartialIso
abbrev CheckedProp := CodegenCore.CheckedProp
abbrev CheckedProp.ofComplete := @CodegenCore.CheckedProp.ofComplete
abbrev CheckedProp.check_iff := @CodegenCore.CheckedProp.check_iff
abbrev CheckedProp.isComplete := @CodegenCore.CheckedProp.isComplete

end Machines
