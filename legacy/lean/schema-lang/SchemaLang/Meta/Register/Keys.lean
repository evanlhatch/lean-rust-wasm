/-
# SchemaLang.Meta.Register.Keys — the W8.2 declared-key registry

Extracted from `SchemaLang.Meta.Reflect` (pure code motion — every
declaration keeps its exact statement and name): the `schemaKeyExt`
extension, the `@[schema key.<field>]` attr-arg parse, and the SHARED
key-registration gate. The DATA, the WF lane, and the obligation view
live in `SchemaLang.Keys`; the `schema_keys` command in `Meta.Keys`.
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

public meta section

namespace SchemaLang.Meta

open Lean
open Qq

/-! ## Keys — the W8.2 declared-key registry

The key registry rides its OWN extension (the `invariantItemExt`
precedent — `Item` is the closed boundary universe and carries no key
metadata, so the emitters' `List Item` fold is untouched and the
byte-tie holds by construction). The DATA, the WF lane, and the
obligation view live in `SchemaLang.Keys`; the `schema_keys` command in
`Meta.Keys`. This section: the extension, the `@[schema key.<field>]
attr-arg parse, and the SHARED registration gate (the pure checker is
the single authority — one gate, two mount points). -/

/-- The key registry: record schema-name ↦ declared keys, append-only,
    replayed from oleans at import (the `CodegenCore.mkRegistryExt`
    semantics). -/
initialize schemaKeyExt :
    SimplePersistentEnvExtension KeyDecl (List KeyDecl) ←
  CodegenCore.mkRegistryExt `schemaKeyExt

/-- The registered key declarations from an environment (the
    Meta.EventSourced + Meta.Keys + tests entry point). -/
def registeredKeys (env : Environment) : List KeyDecl :=
  schemaKeyExt.getState env

/-- The registered key declaration for one record schema name, if any. -/
def registeredKeyDecl? (env : Environment) (record : String) : Option KeyDecl :=
  (registeredKeys env).find? (·.record == record)

/-- The optional `@[schema key.<field>]` argument (the `simple` attr
    parser's ONE optional ident, dot-split — the `funcSemOfStx`
    precedent). `none` = no primary key declared. -/
def schemaKeyArgOfStx (stx : Syntax) : Except String (Option String) := do
  let opts := match stx with
    | .missing => []
    | _ => stx.getArgs.toList.drop 1
  let mut args : List String := []
  for o in opts do
    if o.isNone then pure ()
    else if o[0]!.isIdent then args := args ++ [o[0]!.getId.toString]
    else throw s!"unexpected @[schema] argument: {o}"
  match args with
  | [] => .ok none
  | [arg] =>
      match String.splitOn arg "." with
      | ["key", field] => .ok (some field)
      | _ => throw (s!"unexpected @[schema] argument `{arg}` — valid: "
          ++ "`key.<field>` (the primary key, declared at registration; "
          ++ "foreign keys ride the `schema_keys` command)")
  | _ => throw "@[schema] takes at most one argument (`key.<field>`)"

/-- THE SHARED KEY-REGISTRATION GATE (the `checkStruct` pattern: the
    mount resolves names, the PURE checker judges): reject a duplicate
    declaration, then run `keyDeclsCheck` over the replayed registry
    PLUS the new declaration — every rejection mode (missing key
    field, non-scalar key, missing/keyless/mismatched target, stale
    fields, duplicate) fails ELABORATION with the rendered
    diagnostics. Mounted by the `@[schema key.<field>]` attr arg (this
    module) and the `schema_keys` command (Meta.Keys). -/
def registerSchemaKeys (kd : KeyDecl) (ctx : String) : CoreM Unit := do
  let env ← getEnv
  if ((registeredKeys env).map (·.record)).contains kd.record then
    throwError s!"{ctx}: {SchemaDiag.render (.dupKeyDecl kd.record)}"
  let items := (schemaItemExt.getState env).map (·.2)
  match keyDeclsCheck items (registeredKeys env ++ [kd]) with
  | [] => modifyEnv fun env => schemaKeyExt.addEntry env kd
  | ds => throwError s!"{ctx}: {SchemaDiag.renderList ds}"


end SchemaLang.Meta

end -- public meta section
