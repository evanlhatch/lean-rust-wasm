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

import Lean

open Lean Elab Command Term Meta

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
    let some ci := env.find? decl
      | throwError "@[cert]: unknown declaration `{decl}`"
    unless ci.isTheorem do
      throwError "@[cert]: `{decl}` is not a theorem — certs cite proofs"
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
    let expected ← elabType ty
    unless ← isDefEq ci.type expected do
      throwError m!"cert `{name}` has type{indentD m!"{ci.type}"}\nnot defeq to the required{indentD m!"{expected}"}"

end Dbsp.Certs
