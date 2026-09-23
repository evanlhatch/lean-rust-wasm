/-
# SchemaLang.Meta.Register.Schema — `@[schema]`: records + variants

Extracted from `SchemaLang.Meta.Reflect` (pure code motion — every
declaration keeps its exact statement and name): the Records and
Variants sections (pure checks + registration handlers) and the
`@[schema]` attribute itself.

S5 SEAM (the meta-toolkit follow-up — documented): this lane's
REGISTRY (`schemaItemExt`/`registeredItems`, the `Name × Item` pair —
the default `declare_registry_member` shape) lives in `Register.Core`
and is the EMITTED skeleton now (`declare_registry_member
schemaItemExt registeredItems : Item` — decls byte-identical, the
write path `registerSchemaItem` stays hand-written; see there). The
`@[schema]` ATTRIBUTE below stays HAND-ROLLED — a deliberate seam: it
is richer than the toolkit's form-(ii) builder shape
(`Name → CoreM <kind>`): (1) the optional `key.<field>` argument is
parsed from the ATTRIBUTE SYNTAX (`schemaKeyArgOfStx stx`) — the
toolkit's emitted mount passes `_stx`; (2) the structure/inductive
dispatch with the per-item checks (`checkStruct`/`checkInductive` —
the SchemaDiag diagnostics, the pinned messages); (3) the DUAL-
extension write: the item into `schemaItemExt` AND the declared key
into `keysExt` (`registerSchemaKeys` — which READS `schemaItemExt` at
registration, so the key write must come AFTER the item's, i.e. the
mount needs a post-registration hook, not a side effect in the
builder); (4) the wire-name dup gate lives IN the checks
(`SchemaDiag.dupName`), where the toolkit's `freshNameCheck` would
spell the rejection differently (the pinned messages). Migrating the
ATTRIBUTE needs a stx-threaded builder + a post-registration hook for
`registerSchemaKeys` — a toolkit v2, not a minimal parameterization;
the seam stands (the attribute below stays hand-rolled, behavior and
messages identical).
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
public meta import SchemaLang.Meta.Register.Provenance
public meta import SchemaLang.Meta.Register.Keys

public meta section

namespace SchemaLang.Meta

open Lean
open Qq

/-! ## Records — `@[schema]` on a structure -/

/-- Pure structural check: diagnostics or fields. NO monad — the
    generalization traps of CoreM do-blocks don't apply to a Sum. -/
def checkStruct (env : Environment) (declName : Name) :
    Sum (List SchemaDiag) (List Field) :=
  if !(Lean.isStructure env declName) then
    .inl [SchemaDiag.notAStructure declName.toString]
  else
    let fieldNames := Lean.getStructureFields env declName
    let ctor := Lean.getStructureCtor env declName
    match env.find? ctor.name with
    | none => .inl [SchemaDiag.noCtor declName.toString]
    | some (.ctorInfo ci) =>
      let tys := ctorArgTypes ci.type
      if tys.length != fieldNames.size then
        .inl [SchemaDiag.binderMismatch declName.toString]
      else
        let known := registeredNames env
        let step (acc : Sum (List SchemaDiag) (List Field)) (pair : Name × Expr) :=
          let (f, tE) := pair
          match acc with
          | .inl ds => .inl ds
          | .inr fields =>
            match checkSchemaIdent (s!"field of `{declName}`") f.toString with
            | ds@(_ :: _) => .inl ds
            | [] => match tyOfExpr? env tE with
              | some t => .inr (fields ++ [{ name := f.toString, ty := t }])
              | none => .inl [SchemaDiag.nonBoundaryType f.toString (toString tE)]
        let acc := (fieldNames.toList.zip tys).foldl step (.inr [])
        match acc with
        | .inl ds => .inl ds
        | .inr fields =>
          if known.contains (schemaNameOf declName) then
            .inl [SchemaDiag.dupName (schemaNameOf declName)]
          else .inr fields
    | _ => .inl [SchemaDiag.noCtor declName.toString]

/-- Register one reflected structure; returns the registered fields
    (the `@[schema key.<field>]` handler builds the `KeyDecl` from
    them — the registration-time read, no re-derivation). -/
def registerSchemaStruct (declName : Name) : CoreM (List Field) := do
  let env ← getEnv
  match checkStruct env declName with
  | .inl ds => throwError ("@[schema] `" ++ declName.toString ++ "`: "
      ++ String.intercalate "; " (ds.map SchemaDiag.render))
  | .inr fields => do
    registerSchemaItem declName (.record (schemaNameOf declName) fields)
    registerSchemaItemDoc declName
    pure fields

/-! ## Variants — `@[schema]` on a non-parameterized inductive -/

/-- Pure inductive check: diagnostics or variant cases. v1 limits:
    non-parameterized only, each ctor with at most ONE payload arg
    (the WIT variant-case shape). -/
def checkInductive (env : Environment) (declName : Name) :
    Sum (List SchemaDiag) (List VariantCase) :=
  match env.find? declName with
  | some (.inductInfo ii) =>
      if ii.numParams != 0 then
        .inl [SchemaDiag.binderMismatch declName.toString]
      else
        let known := registeredNames env
        let step (acc : Sum (List SchemaDiag) (List VariantCase))
            (ctor : Name) : Sum (List SchemaDiag) (List VariantCase) :=
          let caseName := ctorNameOf declName ctor
          match acc with
          | .inl ds => .inl ds
          | .inr cases =>
            match checkSchemaIdent (s!"case of `{declName}`") caseName with
            | ds@(_ :: _) => .inl ds
            | [] =>
              match env.find? ctor with
              | none => .inl [SchemaDiag.noCtor caseName]
              | some (.ctorInfo ci) =>
                  match ctorArgTypes ci.type with
                  | [] => .inr (cases ++ [(caseName, none)])
                  | [t] =>
                      match tyOfExpr? env t with
                      | some ty => .inr (cases ++ [(caseName, some ty)])
                      | none => .inl [SchemaDiag.nonBoundaryType caseName (toString t)]
                  | _ => .inl [SchemaDiag.multiPayload caseName]
              | _ => .inl [SchemaDiag.noCtor caseName]
        let acc := ii.ctors.foldl step (.inr [])
        match acc with
        | .inl ds => .inl ds
        | .inr cases =>
          if known.contains (schemaNameOf declName) then
            .inl [SchemaDiag.dupName (schemaNameOf declName)]
          else .inr cases
  | _ => .inl [SchemaDiag.noCtor declName.toString]

/-- Register one reflected inductive as a variant. -/
def registerSchemaVariant (declName : Name) : CoreM Unit := do
  let env ← getEnv
  match checkInductive env declName with
  | .inl ds => throwError ("@[schema] `" ++ declName.toString ++ "`: "
      ++ String.intercalate "; " (ds.map SchemaDiag.render))
  | .inr cases => do
    registerSchemaItem declName (.variant (schemaNameOf declName) cases)
    registerSchemaItemDoc declName

/- `@[schema]` — reflect a structure OR a non-parameterized inductive
    into the schema registry. The optional argument declares the
    record's PRIMARY KEY at registration time: `@[schema key.id]`
    (W8.2 — the one optional ident the `simple` attr parser admits,
    dot-joined, the `funcSemOfStx` precedent). The attribute-time
    declaration is what lanes running AT declaration time see
    (`@[schema key.code, event_sourced]` — the declared key WINS over
    the first-field convention, `Item.keyOfWith`); the `schema_keys`
    command (Meta.Keys) is the full surface (primary + foreign keys)
    for records whose consumers run later. The registration below
    stays HAND-ROLLED (the S5 seam — see the module header): richer
    than the toolkit's mount (the stx-carried `key.<field>` arg, the
    dual-extension write, the own diagnostics). -/
register_check_attribute `schema : "register a structure or inductive as a schema item (the boundary universe); optional arg `key.<field>` declares the primary key (W8.2)" := fun decl stx _kind => do
    let keyArg? ← match schemaKeyArgOfStx stx with
      | .ok k => pure k
      | .error msg => throwError msg
    let env ← getEnv
    if Lean.isStructure env decl then
      let fields ← registerSchemaStruct decl
      if let some keyField := keyArg? then
        let kd : KeyDecl :=
          { record := schemaNameOf decl, fields := fields
          , key := keyField, foreign := [] }
        registerSchemaKeys kd s!"@[schema key.{keyField}] `{decl}`"
    else
      match env.find? decl with
      | some (.inductInfo _) =>
        if keyArg?.isSome then
          throwError ("@[schema key.…] declares a PRIMARY KEY — records only "
            ++ s!"(`{decl}` is an inductive; a variant has no fields)")
        else
          registerSchemaVariant decl
      | _ => throwError ("@[schema] supports structures and inductives only: `"
        ++ decl.toString ++ "`")


end SchemaLang.Meta

end -- public meta section
