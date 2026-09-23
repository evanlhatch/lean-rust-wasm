/-
# SchemaLang.Meta.Keys — `schema_keys`: the key-declaration surface (W8.2)

The FULL authoring surface for declared keys (SchemaLang.Keys owns the
DATA + the WF lane + the obligation view; `Meta.Reflect` owns the
registry + the shared gate — the `invariantItemExt` precedent: a
SEPARATE extension because `Item` is the closed boundary universe and
carries no key metadata):

    schema_keys for User := primary id
    schema_keys for Order := primary id, userId → User

One declaration per record: the PRIMARY KEY (a field name; the field's
Ty must inject from `KeyTy` — the W8.1 scalar discipline) plus any
FOREIGN KEYS (`<field> → <TargetRecord>` — the target references via
its OWN declared primary key, so the target's keys must be registered
FIRST — the forward-reference rule, same as `.ty` refs).

The sibling surface is the `@[schema key.<field>]` attr arg
(Meta.Reflect): the primary key AT REGISTRATION TIME, for lanes that
read the registry AT declaration time — `@[schema key.code,
event_sourced]` makes the declared key WIN over the first-field
convention in the generated `esKey` (the `Item.keyOfWith` read). Use
the attr arg for the primary when `@[event_sourced]` must see it; use
this command otherwise (and always for foreign keys — a record gets
its keys from exactly ONE surface; the second write is the loud
`dupKeyDecl`).

THE GATE: the command resolves the record + the FK targets (Lean name
→ schema name, did-you-mean over the registered record names — the
`schema_invariant` pattern), builds the `KeyDecl`, and hands it to
`registerSchemaKeys` — the PURE checker (`keyDeclsCheck`,
SchemaLang.Keys) over the replayed registry as the elaboration gate.
A missing/non-scalar key field, a missing/keyless/mismatched target,
a stale field snapshot, or a duplicate declaration is an ELABORATION
error (the tightest tier).

Ownership: the keys lane's command half. Deliberate exclusions: no
emitter reads this registry (the byte-tie holds by construction);
composite keys (v1: single-field, the `Item.keyOf` convention's
granularity).
-/

module

public import Lean
public meta import SchemaLang.Meta.Reflect

public meta section

namespace SchemaLang.Meta

open Lean Elab Command

/-- `schema_keys for <Record> := primary <field> (, <field> → <Target>)*`
    — declare the record's primary key + foreign keys (the module
    header). Word tokens follow the `schema_update` minimality lesson
    (ONE word token — `primary`; the FK separator is punctuation, the
    FK arrow is `→`, never a common word — a `foreign` token would
    reserve the word and break `KeyDecl.foreign` field syntax). -/
syntax (name := schemaKeys) "schema_keys " "for " ident " := " "primary " ident
  (", " ident " → " ident)* : command

/-- Resolve a registered RECORD's (schema name, fields) from a Lean
    name, or a did-you-mean error over the registered record names
    (the `schema_invariant` pattern — variants/resources cannot take
    keys). -/
def resolveKeyRecord (cmd : String) (recId : Name) :
    CommandElabM (String × List Field) := do
  let env ← getEnv
  let recordNames := (schemaItemExt.getState env).filterMap
    (fun (_, it) => match it with | .record n _ => some n | _ => none)
  match (schemaItemExt.getState env).find? (fun (ln, _) => ln == recId) with
  | some (_, .record n fields) => pure (n, fields)
  | _ =>
      let cands := CodegenCore.didYouMean recId.toString recordNames
      let hint := if cands.isEmpty then ""
        else s!" — did you mean: {String.intercalate ", " cands}?"
      throwError s!"{cmd}: `{recId}` is not a registered record{hint}"

/-- The command elaborator: resolve names, build the `KeyDecl`, hand
    it to the SHARED gate (`registerSchemaKeys` — the pure checker is
    the single authority). -/
@[command_elab schemaKeys]
def elabSchemaKeys : CommandElab := fun stx => do
  let recId := stx[2]!.getId
  let keyId := stx[5]!.getId.toString
  let (recordName, fields) ← resolveKeyRecord "schema_keys" recId
  -- the FK targets: Lean name → schema name (did-you-mean over the
  -- registered record names; the type/field checks are the checker's)
  let fks ← stx[6]!.getArgs.mapM fun g => do
    let fieldName := g[1]!.getId.toString
    let targetId := g[3]!.getId
    let (targetName, _) ← resolveKeyRecord "schema_keys" targetId
    pure { field := fieldName, target := targetName : ForeignKey }
  let kd : KeyDecl :=
    { record := recordName, fields := fields, key := keyId
    , foreign := fks.toList }
  liftCoreM <| registerSchemaKeys kd s!"schema_keys for `{recId}`"

end SchemaLang.Meta
