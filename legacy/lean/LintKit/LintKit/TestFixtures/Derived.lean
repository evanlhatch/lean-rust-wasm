/-
LintKit.TestFixtures.Derived — the `@[derived]` stamp fixture: a toy
generating command + its output, the +/− pair pinning the STRUCTURAL
exemption (LintKit.Basic's `hasDerived` skip in PackageNamespace's test):

* `List.stampedOk` — EMITTED by `emit_derived` (the schema_update shape: the
  command parks its output in a foreign namespace by construction) and
  stamped `@[derived]` — the packageNamespace linter must PASS it;
* `List.unstampedBad` — the twin WITHOUT the stamp — the linter must FLAG it.

Built (legal Lean) but never imported by the `LintKit` umbrella (the lint
gate never sees it); `LintKitTests.Main` importModules it with loadExts and
asserts the finding set.
-/
import LintKit.Basic

open Lean Elab Command

namespace LintKit.TestFixtures.Derived

/-- The toy generating command: `emit_derived <name>` emits `List.<name>`
    stamped `@[derived]` — the stamp comes from the EMITTING command, not a
    source-site opt-out (which a generated decl does not have). -/
syntax (name := emitDerived) "emit_derived " ident : command

-- The impl itself is generated-code infrastructure (meta machinery,
-- String-carrying), not guest code: the guestBan census's opt-out exercises
-- the nolint path on THAT linter too.
-- The impl itself is generated-code infrastructure (meta machinery,
-- String-carrying), not guest code: the guestBan census's opt-out exercises
-- the nolint path on THAT linter too. (One bracket: a stacked `@[nolint]`
-- after `@[command_elab]` does not parse — the nolint attr's `ident*` tail.)
@[command_elab LintKit.TestFixtures.Derived.emitDerived,
  nolint linter.guestlang.guestBan "fixture infra: the toy command's impl, not guest code"]
def emitDerivedImpl : Lean.Elab.Command.CommandElab :=
  fun stx => do
    let n := stx[1].getId
    Lean.Elab.Command.elabCommand
      (← `(@[derived] def $(mkIdent ((`List).str n.toString)) : Nat := 42))

emit_derived stampedOk

end LintKit.TestFixtures.Derived

/-- Planted (packageNamespace): UNSTAMPED helper parked in a core namespace —
the twin of `List.stampedOk`; the `@[derived]` skip's negative control.
Distinct body (the dupDefBodies cluster scan spans the package root). -/
def List.unstampedBad : Nat := 3
