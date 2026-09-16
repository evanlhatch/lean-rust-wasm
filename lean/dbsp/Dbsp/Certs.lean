/-
# Dbsp.Certs — the certificate registry (lean-v3 §4.4's CI mechanism)

A compiled kernel's `cert` field names a theorem that justifies its
incrementalization; "certification drift = build error". This module is the
Lean-side mechanism: `@[cert]` marks a theorem citable, and
`#check_cert Name : Type` is the CI resolution — the name must be a
registered theorem whose type is defeq to the required shape.

    @[cert] theorem my_template_incremental ... := ...

    #check_cert my_template_incremental :
      ∀ (F : Operator a a), Strict F → ...

Core-only mechanism (environment extension + a command elaborator); no
mathlib needed beyond what Dbsp already has.
-/

module

public import Lean

open Lean Elab Command Term Meta

-- Elaboration-time only: env extension, attribute, and command
-- elaborators live in a `public meta section` (W5.4 module discipline).
public meta section

namespace Dbsp.Certs

/-- The registry: names of `@[cert]`-marked theorems. -/
initialize certExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `certs
    addImportedFn := fun ess => ess.foldl (init := #[]) fun acc es =>
      es.foldl (init := acc) fun acc e => if acc.contains e then acc else acc.push e
    addEntryFn := fun s e => s.push e
  }

/-- `@[cert]` — mark a theorem as citable by compiled artifacts. -/
initialize registerBuiltinAttribute {
  name := `cert
  descr := "mark a theorem as a citable certificate (lean-v3 §4.4)"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => do
    let env ← getEnv
    unless (env.find? decl).isSome do
      throwError "@[cert]: unknown declaration `{decl}`"
    -- NOTE (module system, W5.4): the theorem-kind check CANNOT live here.
    -- In a module, theorem bodies elaborate deferred, so at attribute
    -- application time a `theorem` is visible as an `axiomInfo`
    -- (observed: `.afterCompilation` and `.afterTypeChecking` both).
    -- Theorem-ness is enforced at `#check_cert` instead — the CI gate.
    modifyEnv (fun env => certExt.addEntry env decl)
}

/-- List every registered certificate. -/
elab "#print_certs" : command => do
  let certs := certExt.getState (← getEnv)
  logInfo (MessageData.joinSep (certs.toList.map (MessageData.ofConstName ·)) "\n")

/-- `#check_cert Name : Type` — resolve a cert citation: registered, a
    theorem, and of the required type (up to defeq). This is the CI check:
    a recipe wire field carries the name; this command pins the shape. -/
elab "#check_cert " n:ident " : " ty:term : command => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let env ← getEnv
    unless (certExt.getState env).contains name do
      throwError "`{name}` is not a registered certificate (missing @[cert])"
    let some ci := env.find? name | throwError "unknown constant `{name}`"
    unless ci.isTheorem do
      throwError "`{name}` is not a theorem — certs cite proofs"
    let expected ← elabType ty
    unless ← isDefEq ci.type expected do
      throwError m!"cert `{name}` has type{indentD m!"{ci.type}"}\nnot defeq to the required{indentD m!"{expected}"}"

end Dbsp.Certs

end -- public meta section
