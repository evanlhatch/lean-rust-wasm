/-
# SchemaLang.Meta.Register.Funcs — `@[schema_fn]` + `@[schema_resource]`

Extracted from `SchemaLang.Meta.Reflect` (pure code motion — every
declaration keeps its exact statement and name): the Functions section
(signature-as-spec reification, the `FuncSem` attr-arg parse, the
`@[schema_fn]` attribute) and the Resources section (`@[schema_resource]`).
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

public meta section

namespace SchemaLang.Meta

open Lean
open Qq

/-! ## Functions — `@[schema_fn]` on a def -/

/-- One optional attr-arg node → its ident name (present = the node
    wraps the ident at `[0]`; absent = `null`). -/
def optArgIdent? (stx : Syntax) : Except String (Option String) :=
  if stx.isNone then .ok none
  else if stx[0]!.isIdent then .ok (some stx[0]!.getId.toString)
  else .error s!"unexpected @[schema_fn] argument: {stx}"

/-- Parse the optional `@[schema_fn]` semantic args into a `FuncSem`
    (6.5.1). The builtin `simple` attr parser admits ONE optional
    ident — a dedicated two-ident attr parser was tried and is
    SHADOWED (`simple` wins every parse it can consume; there is no
    fallback across attr parsers), so all axes travel in ONE ident,
    dot-separated: `@[schema_fn volatile]` (determinism only),
    `@[schema_fn strict]` (nullSem only), `@[schema_fn
    strict.volatile]` (both, either order), `@[schema_fn stream]`
    (delivery), `@[schema_fn strict.volatile.stream]` (all three).
    Each part names a NullSem, Determinism, or Delivery ctor; unknown
    names, duplicated axes, and >3 parts are LOUD errors enumerating
    the valid space. -/
def funcSemOfStx (stx : Syntax) : Except String FuncSem := do
  let step (acc : Option NullSem × Option Determinism × Option Delivery) (name : String)
      : Except String (Option NullSem × Option Determinism × Option Delivery) :=
    let (nullSem?, det?, del?) := acc
    match name with
    | "strict" | "propagate" | "custom" =>
        if nullSem?.isSome then
          .error s!"duplicate nullSem argument `{name}` — one of strict, propagate, custom"
        else
          .ok (NullSem.ofToken? name, det?, del?)
    | "pure" | "stable" | "volatile" =>
        if det?.isSome then
          .error s!"duplicate determinism argument `{name}` — one of pure, stable, volatile"
        else
          .ok (nullSem?, Determinism.ofToken? name, del?)
    | "stream" | "once" =>
        if del?.isSome then
          .error s!"duplicate delivery argument `{name}` — one of stream, once"
        else
          .ok (nullSem?, det?, Delivery.ofToken? name)
    | other =>
        .error (s!"unknown @[schema_fn] argument `{other}` — valid: "
          ++ "strict, propagate, custom (nullSem); pure, stable, volatile (determinism); "
          ++ "stream, once (delivery)")
  -- `simple` shape: [name ident, one optional arg]; .missing =
  -- programmatic application (no args)
  let opts := match stx with
    | .missing => []
    | _ => stx.getArgs.toList.drop 1
  match opts.mapM optArgIdent? with
  | .error e => .error e
  | .ok idents =>
    let parts := (idents.filterMap id).flatMap (String.splitOn · ".")
    if parts.length > 3 then
      .error s!"too many @[schema_fn] arguments ({parts.length}) — at most one nullSem, one determinism, one delivery"
    else
      let init : Option NullSem × Option Determinism × Option Delivery := (none, none, none)
      match parts.foldlM (fun (acc : Option NullSem × Option Determinism × Option Delivery) name =>
          step acc name) init with
      | .error e => .error e
      | .ok (nullSem?, det?, del?) =>
          .ok { nullSem := nullSem?.getD .propagate
              , determinism := det?.getD .pure
              , delivery := del?.getD .once }

/-- Walk a def's type: gather the EXPLICIT binder (param) types and the
    return type. The signature is the spec; the body is never read. -/
def funcSignature (env : Environment) (declName : Name) :
    Except String FuncSig := do
  let di ← match env.find? declName with
    | some (.defnInfo di) => pure di
    | _ => throw ("`" ++ declName.toString ++ "` is not a def")
  let rec go (acc : List (String × Ty)) (t : Expr) : Except String FuncSig :=
    match t with
    | .forallE name d b bi =>
        if bi.isExplicit then
          match tyOfExpr? env d with
          | some ty => go (acc ++ [(paramNameOf name, ty)]) b
          | none => throw s!"param `{name}` has non-boundary type: {d}"
        else go acc b
    | _ =>
        match tyOfExpr? env t with
        | some ret => pure { name := schemaNameOf declName, params := acc, ret := ret
                           , body := declName }
        | none => throw s!"return type not in the boundary fragment: {t}"
  go [] di.type

/-- Register one reflected function signature, with its semantic
    contract fields (6.5.1). -/
def registerSchemaFunc (declName : Name) (sem : FuncSem := {}) : CoreM Unit := do
  let env ← getEnv
  match funcSignature env declName with
  | .error msg => throwError ("@[schema_fn] `" ++ declName.toString ++ "`: " ++ msg)
  | .ok sig => do
    registerSchemaItem declName (.func { sig with sem })
    registerSchemaItemDoc declName

/- `@[schema_fn]` — reflect a function's SIGNATURE into the schema
    registry (params + return type; the body is not part of the spec).
    Optional ident args set the semantic fields (one ident, dot-joined
    for both axes — see `funcSemOfStx`): `@[schema_fn volatile]`,
    `@[schema_fn strict.volatile]`, … -/
register_check_attribute `schema_fn : "register a function signature as a schema func item" := fun decl stx _kind => do
    let sem ← match stx with
      | .missing => pure ({} : FuncSem)
      | _ => match funcSemOfStx stx with
        | .ok sem => pure sem
        | .error msg =>
            throwError ("@[schema_fn] `" ++ decl.toString ++ "`: " ++ msg)
    registerSchemaFunc decl sem

/-! ## Resources — `@[schema_resource]` on an opaque type -/

/-- Register one reflected resource (an opaque handle: the name is the
    schema content; there is nothing to check). -/
def registerSchemaResource (declName : Name) : CoreM Unit := do
  registerSchemaItem declName (.resource (schemaNameOf declName))
  registerSchemaItemDoc declName

/- `@[schema_resource]` — register an opaque handle type as a schema
    resource item (its method surface arrives as `func` items referencing
    it in their first param). -/
register_check_attribute `schema_resource : "register an opaque type as a schema resource item" := fun decl _stx _kind => (registerSchemaResource decl : CoreM Unit)


end SchemaLang.Meta

end -- public meta section
