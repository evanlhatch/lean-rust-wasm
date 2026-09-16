/-
# CodegenCore.AttrKit — `register_check_attribute`: the BOILERPLATE macro,
  plus `mountAsGate`: the GATE mount of the W7.13 decl-check shape
  (`LintKit.DeclCheck`) — one check, mountable as elab-time gate here or as
  env-lint via `LintKit.mountAsLinter`.
-/

import Lean
import LintKit.DeclCheck

open Lean
open Lean.Elab
open Lean.Elab.Command

namespace CodegenCore

/-- The GATE mount: run a `LintKit.DeclCheck` at elaboration; empty diags =
    pass, nonempty = a hard elab error (the joined diag messages). Side
    effects beyond the verdict (e.g. GuestGate's guest-mark registry write)
    belong in the attribute handler AFTER the mount passes — the pure check
    cannot carry them. Typical use, via `register_check_attribute`:
    `register_check_attribute \`foo : "..." := fun decl _stx _kind =>
      (mountAsGate myCheck decl : CoreM Unit)`. -/
def mountAsGate (check : LintKit.DeclCheck) (decl : Name) : CoreM Unit := do
  let env ← getEnv
  match check decl env with
  | [] => pure ()
  | ds => throwError (String.intercalate "\n" (ds.map (·.message)))

end CodegenCore

/-- `register_check_attribute name : "descr" := handler` → the full
    `initialize registerBuiltinAttribute { … }` block. -/
elab "register_check_attribute " name:term " : " descr:str " := " handler:term : command => do
  let cmd := (← `( initialize (registerBuiltinAttribute {
    name := $name
    descr := $descr
    applicationTime := .afterCompilation
    add := $handler
  }) )).raw
  elabCommand cmd