/-
# SchemaLang.Meta.Register.Invariants — the `schema_invariant` command

Extracted from `SchemaLang.Meta.Reflect` (pure code motion — every
declaration keeps its exact statement and name): the invariant registry
(`invariantItemExt`) and the `schema_invariant` command elaborator.
The typed-quotation helpers live in `Register.Quotes`.
-/
module

public import Lean
public import Qq
public import CodegenCore.AttrKit
public import CodegenCore
public meta import SchemaLang.Ty
public meta import SchemaLang.Item
public meta import SchemaLang.Invariant
public meta import SchemaLang.Update
public meta import SchemaLang.Keys
-- Update2 is mathlib-FREE by construction (the neutrality family moved
-- to Update.lean at W8.3 — TickCascade's `Dbsp.Effects` dependency
-- must NOT reach legacy `Meta.Reflect` consumers: the feature-flags
-- `Flag` collision lesson). Keep it that way: Update2 imports
-- Update/Keys/CodegenCore only.
public meta import SchemaLang.Update2
public meta import SchemaLang.Meta.Register.Core
public meta import SchemaLang.Meta.Register.Quotes

public meta section

namespace SchemaLang.Meta

open Lean
open Qq

/-! ## Invariants — `schema_invariant <name> for <Record> := <term>`

The invariant registry is a SEPARATE extension (`invariantItemExt`) —
`Item` is the closed boundary universe and cannot carry the VExpr
family. The command elaborates the author's term against
`VExpr <the record's real fields> .bool` — the fields looked up from
`schemaItemExt` at elab time, so an unknown record is a did-you-mean
error and a misspelled COLUMN is the `HasCol` instance failure. The
tier is COMPUTED here: an executable term alone registers
`boundaryCheck`; `proved <thm>` cites a theorem, RESOLVED at
registration (`SchemaLang.checkCitation?` — the `Dbsp.Certs.
#check_cert` pattern: missing, non-theorem, sorry-tainted, or
wrong-shape citations fail to elaborate). -/

/-- The invariant registry: append-only, replayed from oleans at import
    (the `CodegenCore.mkRegistryExt` semantics — a SEPARATE extension
    because `Item` is the closed boundary universe and cannot carry the
    VExpr family). -/
initialize invariantItemExt :
    SimplePersistentEnvExtension InvariantItem (List InvariantItem) ←
  CodegenCore.mkRegistryExt `invariantItemExt

/-- The registered invariant rows (the emission entry point). -/
def registeredInvariants (env : Environment) : List InvariantItem :=
  invariantItemExt.getState env

/-- Registered invariant names (dup detection). -/
def registeredInvariantNames (env : Environment) : List String :=
  (registeredInvariants env).map (·.name)

/-- The invariant's NAME may be an ident OR a string literal: the registry
names are kebab (`id-positive`) — the emitted Rust's fn suffix and the
emitted comment carry them verbatim — but a kebab word is not a Lean
ident. The string form is the authoring surface for those; the ident
form stays for Lean-friendly names.

`schema_invariant <name> for <Record> (proved <thm>)? := <term>` —
    elaborate the predicate against the registered record's fields,
    register the `InvariantItem` (tier computed per `tierOf`). -/
syntax (name := schemaInvariant) "schema_invariant " (ident <|> str)
  " for " ident (" proved " ident)? " := " term : command

open Lean Elab Command Term in
@[command_elab SchemaLang.Meta.schemaInvariant]
unsafe def elabSchemaInvariant : CommandElab := fun (stx : Syntax) => do
  -- the name: ident OR string literal (the kebab registry names are
  -- not Lean idents — see the syntax note above)
  let invName : String :=
    match stx[1]!.isStrLit? with
    | some s => s
    | none => stx[1]!.getId.toString
  let recId := stx[3]!.getId
  let proofName? : Option Name :=
    let opt : Syntax := stx[4]!
    if opt.isNone then none else some opt[1]!.getId
  let env ← getEnv
  -- the record: a registered `Item.record`, or a did-you-mean error
  -- over the registered RECORD names (variants/resources cannot take
  -- field-indexed invariants)
  let recordNames := (schemaItemExt.getState env).filterMap
    (fun (_, it) => match it with | .record n _ => some n | _ => none)
  let found? : Option (Name × Item) :=
    (schemaItemExt.getState env).find? (fun (ln, _) => ln == recId)
  let (recordName, fields) : String × List Field ←
    match found? with
    | some (_, .record n fields) => pure (n, fields)
    | _ =>
        let cands := CodegenCore.didYouMean recId.toString recordNames
        let hint := if cands.isEmpty then ""
          else s!" — did you mean: {String.intercalate ", " cands}?"
        throwError s!"schema_invariant `{invName}`: `{recId}` is not a registered record{hint}"
  if (registeredInvariantNames env).contains invName then
    throwError s!"schema_invariant `{invName}`: duplicate invariant name"
  -- the predicate: elaborated against `VExpr <fields> .bool`, then
  -- evaluated to the GADT value (the emitter compiles the VALUE)
  let (exprTerm, inv) : Expr × SchemaInvariant ← liftTermElabM do
    let fsList := fieldsToExpr fields
    let expectedFs : Q(Type) := q(List Field)
    let expected : Expr := vexprBoolTyQ fsList
    let e ← elabTerm stx[6]! (some expected)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasExprMVar then
      throwError s!"schema_invariant `{invName}`: unresolved metavariables in the predicate"
    let fsVal : List Field ← Meta.evalExpr (List Field) expectedFs fsList
    let ev : VExpr fsVal .bool ← Meta.evalExpr (VExpr fsVal .bool) expected e
    pure (e, { fields := fsVal, expr := ev })
  -- THE PROVED-TIER CITATION GATE (the wire — `SchemaLang.checkCitation?`,
  -- the `Dbsp.Certs.#check_cert` pattern): a `proved <thm>` citation must
  -- resolve HERE — missing, non-theorem, sorry-tainted, or wrong-shape
  -- citations are ELABORATION errors (the stored-but-unchecked hole is
  -- closed; formerly "resolution is CI's job later").
  if let some pn := proofName? then
    liftTermElabM do
      let env' ← getEnv
      let fsListE := fieldsToExpr fields
      match ← checkCitation? env' fsListE exprTerm pn with
      | some d => throwError s!"schema_invariant `{invName}`: {d}"
      | none => pure ()
  modifyEnv fun env =>
    invariantItemExt.addEntry env
      { name := invName, schemaRef := recordName, tier := tierOf proofName?
      , proofName := proofName?, inv := inv, exprTerm := exprTerm }


end SchemaLang.Meta

end -- public meta section
