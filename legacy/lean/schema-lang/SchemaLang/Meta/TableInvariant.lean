/-
# SchemaLang.Meta.TableInvariant — `schema_table_invariant` (W8.8)

The authoring surface for table-level invariants (SchemaLang.TableInvariant
owns the DATA + the executable check + the obligation view; this module
owns the registry + the command — the `invariantItemExt`/`schemaKeyExt`
precedent: a SEPARATE extension because `Item` is the closed boundary
universe and carries no invariant metadata, so the emitters' `List Item`
fold is untouched and the byte-tie holds BY CONSTRUCTION):

    schema_table_invariant "acct-ids-unique" for Acct := unique id
    schema_table_invariant "acct-conserves" for Acct := sum balance = 150
    schema_table_invariant "acct-bounded"   for Acct := count ≤ 4
    schema_table_invariant "acct-exact"     for Acct := count = 2

The name may be an ident OR a string literal (the kebab registry names
are not Lean idents — the `schema_invariant` note). FOUR syntax kinds
(one per aggregation shape — no infix `<|>` choice node: the
elaborators never read token positions of a collapsed choice).

THE GATE: the command resolves the record (the `schema_keys` pattern —
`resolveKeyRecord`, did-you-mean over the registered record names),
builds the `TableInvItem` with the record's LIVE field list as the
snapshot, and hands it to `registerTableInvariant` — the PURE checker
(`tableInvCheck`, SchemaLang.TableInvariant) over the replayed registry
as the elaboration gate. An unknown record, a missing/non-u64 `sum`
field, a missing `unique` field, or a duplicate name is an ELABORATION
error (the tightest tier).

Ownership: the table-invariant lane's command half. Deliberate
exclusions: no emitter reads this registry (the byte-tie holds by
construction); the tier's home is the DATA lane's `TableInvItem.tierOf`
(no per-registration tier syntax — the computed rung is the only honest
one v1 can serve, the module header's tier answer).
-/

module

public import Lean
public meta import SchemaLang.Meta.Reflect
public meta import SchemaLang.Meta.Keys
public meta import SchemaLang.TableInvariant

public meta section

namespace SchemaLang.Meta

open Lean Elab Command

/-- The table-invariant registry: append-only, replayed from oleans at
    import (the `CodegenCore.mkRegistryExt` semantics — a SEPARATE
    extension because `Item` is the closed boundary universe and cannot
    carry the aggregation data). -/
initialize tableInvariantExt :
    SimplePersistentEnvExtension TableInvItem (List TableInvItem) ←
  CodegenCore.mkRegistryExt `tableInvariantExt

/-- The registered table-invariant rows (the tests' entry point; the
    emission entry point when an emitter lane lands). -/
def registeredTableInvariants (env : Environment) : List TableInvItem :=
  tableInvariantExt.getState env

/-- THE SHARED REGISTRATION GATE (the `registerSchemaKeys` pattern: the
    mount resolves names, the PURE checker judges): run
    `tableInvCheck` over the replayed registry PLUS the new declaration
    — every rejection mode (unknown/non-record target, stale fields,
    missing or non-u64 aggregation field, duplicate name) fails
    ELABORATION with the checker's diagnostics. -/
def registerTableInvariant (ti : TableInvItem) (ctx : String) : CoreM Unit := do
  let env ← getEnv
  let items := (schemaItemExt.getState env).map (·.2)
  match tableInvCheck items (registeredTableInvariants env ++ [ti]) with
  | [] => modifyEnv fun env => tableInvariantExt.addEntry env ti
  | ds => throwError s!"{ctx}: {String.intercalate "; " ds}"

/-- `schema_table_invariant <name> for <Record> := unique <field>` —
    the field's images are all-distinct over the row-set (the row-set
    is a FUNCTION from the field to the row). -/
syntax (name := schemaTableInvUnique) "schema_table_invariant " (ident <|> str)
  " for " ident " := " "unique " ident : command

/-- `schema_table_invariant <name> for <Record> := sum <field> = <num>` —
    conservation: the u64 column's ℕ-exact sum is the target. -/
syntax (name := schemaTableInvSum) "schema_table_invariant " (ident <|> str)
  " for " ident " := " "sum " ident " = " num : command

/-- `schema_table_invariant <name> for <Record> := count ≤ <num>` —
    a cardinality bound. -/
syntax (name := schemaTableInvCountLe) "schema_table_invariant " (ident <|> str)
  " for " ident " := " "count " "≤" num : command

/-- `schema_table_invariant <name> for <Record> := count = <num>` —
    an exact cardinality. -/
syntax (name := schemaTableInvCountEq) "schema_table_invariant " (ident <|> str)
  " for " ident " := " "count " " = " num : command

/-- The shared elaborator body: resolve the record (did-you-mean over
    the registered record names), build the item with the record's
    LIVE fields as the snapshot, hand it to the gate. -/
def elabTableInvBody (stx : Syntax) (agg : TableAgg) : CommandElabM Unit := do
  let invName : String :=
    match stx[1]!.isStrLit? with
    | some s => s
    | none => stx[1]!.getId.toString
  let (recordName, fields) ← resolveKeyRecord "schema_table_invariant" stx[3]!.getId
  liftCoreM <| registerTableInvariant
    { name := invName, schemaRef := recordName, fields := fields, agg := agg }
    s!"schema_table_invariant `{invName}`"

@[command_elab schemaTableInvUnique]
def elabTableInvUnique : CommandElab := fun stx =>
  elabTableInvBody stx (.unique stx[6]!.getId.toString)

@[command_elab schemaTableInvSum]
def elabTableInvSum : CommandElab := fun stx => do
  let some n := stx[8]!.isNatLit?
    | throwError "schema_table_invariant: the `sum` target must be a numeric literal"
  elabTableInvBody stx (.sum stx[6]!.getId.toString n)

@[command_elab schemaTableInvCountLe]
def elabTableInvCountLe : CommandElab := fun stx => do
  let some n := stx[7]!.isNatLit?
    | throwError "schema_table_invariant: the `count` bound must be a numeric literal"
  elabTableInvBody stx (.countLe n)

@[command_elab schemaTableInvCountEq]
def elabTableInvCountEq : CommandElab := fun stx => do
  let some n := stx[7]!.isNatLit?
    | throwError "schema_table_invariant: the `count` bound must be a numeric literal"
  elabTableInvBody stx (.countEq n)

end SchemaLang.Meta
