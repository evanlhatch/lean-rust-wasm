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

THE EVIDENCE-LANGUAGE TIE (C7): the mechanism is the resolution half of
`CodegenCore.Obligation.Evidence.citedProof` — an obligation discharged by
`.citedProof thm` claims exactly what `#check_cert` verifies about `thm`.
The resolution is ONE gate (`certGate`, shared by the `#check_cert`
elaborator and `citedProofResolves`, the obligation-side consumption);
see the section below. Kit stays core-only — the environment is an
elaboration-time value, so the gate lives here.

Core-only mechanism (environment extension + a command elaborator); no
mathlib needed beyond what Dbsp already has.
-/

module

public import Lean
public import CodegenCore.Kit -- `Obligation.Evidence.citedProof` (the tie)

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

/-! ## The evidence-language tie (C7) — one gate, two languages

`Obligation.Evidence.citedProof` (CodegenCore.Kit) NAMES the kernel
theorem that discharged an obligation; `#check_cert` VERIFIES such names.
The resolution is one gate shared by both languages — the guideline, not
threatened, is: an obligation whose discharge is `.citedProof thm` is
honest exactly when `thm` passes the Certs gate (`citedProofResolves` = the
"Certs test reads the obligation's citedProof" pattern — checkable as
data before emission). The shape half (`#check_cert`'s defeq pin against
the required type) stays at the cite site, where the required type
elaborates; `SchemaLang.checkCitation?` is the schema-lane's instance of
the same pattern over its stored predicates.

Kit stays core-only; the environment is an elaboration-time value, so
the gate lives HERE. -/

/-- THE cert-resolution gate (the registered + theorem half of
    `#check_cert`, shared with the evidence language): `none` = `n` is a
    registered `@[cert]` THEOREM in `env` (citable); `some msg` = the
    diagnostic, byte-identical to `#check_cert`'s own errors. -/
def certGate (env : Lean.Environment) (n : Lean.Name) : Option String := do
  unless (certExt.getState env).contains n do
    return s!"`{n}` is not a registered certificate (missing @[cert])"
  let some ci := env.find? n | return s!"unknown constant `{n}`"
  unless ci.isTheorem do
    return s!"`{n}` is not a theorem — certs cite proofs"
  none

/-- THE obligation-side consumption (the C7 data check): `.citedProof
    thm` evidence names the certificate that discharged its obligation;
    resolution = the shared Certs gate over `thm` (`true` = the citation
    resolves — registered, a theorem). Non-citedProof evidence carries no
    cert to resolve (`true` — this check speaks only for the cited-proof
    shape, the case whose honesty `#check_cert` can be asked about). -/
def citedProofResolves (env : Lean.Environment)
    (ev : CodegenCore.Obligation.Evidence) : Bool :=
  match ev with
  | .citedProof thm => (certGate env thm).isNone
  | _ => true

/-- List every registered certificate. -/
elab "#print_certs" : command => do
  let certs := certExt.getState (← getEnv)
  logInfo (MessageData.joinSep (certs.toList.map (MessageData.ofConstName ·)) "\n")

/-- `#check_cert Name : Type` — resolve a cert citation: registered, a
    theorem, and of the required type (up to defeq). This is the CI check:
    a recipe wire field carries the name; this command pins the shape.
    The registered/theorem half runs the SHARED `certGate` (the same
    resolution `citedProofResolves` reads — the C7 tie, one gate); the
    shape half (defeq against the required type) stays here, where the
    required type elaborates. -/
elab "#check_cert " n:ident " : " ty:term : command => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let env ← getEnv
    if let some d := certGate env name then
      throwError d
    let expected ← elabType ty
    let some ci := env.find? name | throwError "unknown constant `{name}`"
    unless ← isDefEq ci.type expected do
      throwError m!"cert `{name}` has type{indentD m!"{ci.type}"}\nnot defeq to the required{indentD m!"{expected}"}"

end Dbsp.Certs

end -- public meta section
