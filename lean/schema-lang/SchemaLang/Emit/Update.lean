/-
# SchemaLang.Emit.Update — updates → Rust apply functions

The update registry (SchemaLang.Meta.Register.Updates's `update2ItemExt`,
authoring surface `schema_update`) is EMITTED here:
`../../generated/rust/updates_generated.rs` — one `pub fn apply_<name>(rows: &mut
Vec<<Record>>) ` per update (the guard + the single-column write,
compiled from the VExpr values), plus one `pub fn tick_<record>`
folding that record's updates in registration order (the tick's
cascade: single-pass, single-table — Update.lean's stage machine pins
the STAGE discipline, this file emits its row-transform half).

v1→v2 (the migration): the emitter consumes the v2 REGISTRY
(`ctx.updates2` = `update2ItemExt`). The v1 surface is dead; the
emission surface is the V1-SHAPED subset of the v2 rows — exactly ONE
SET clause, no insert/delete. Every pre-migration v1 row was the
singleton-SET image of the same registration's v2 row (the command
built both from one elaboration), so the emitted BYTES are unchanged
(the v1-shape gate reproduces the old row set); a multi-SET /
INSERT / DELETE row has no v1 emission and is skipped honestly.

The Item-AST discipline (Emit/Rust.lean): item shape goes through the
`CodegenCore.Emit.Rust.Item` nodes; string interpolation appears only
in leaf payloads (fn bodies — the audited concession). Names are
pre-mangled via `Emit.snake`/`rustIdent`/`pascal` — the AST never
case-converts.

Lowering (reuses Emit.Expr — the interface lowering, imported, NOT
copied):
- the guard via `Emit.Expr.boolRustI` at the `vexprLang` instance
  (the `evalB` discipline: raw u64 ops over the struct's fields;
  strlen = `.len()` on strings),
- the value via `valueRust` (below): u64 value exprs delegate to
  `Emit.Expr.u64RustI` (the interface's `HasU64` view); a
  `.col`-of-string value → `(<ref>).clone()` (string assignment —
  GADT-direct, justified below). ANY other shape → no emitted fn for
  that row + a comment (the honest-skip discipline).

The emitter contract (v2, Emit.Invariant's discipline): `run` takes
the FULL registry state (`Emit.GenCtx`) — the update lane reads
`ctx.updates2`, the ext-replayed `schema_update` rows. `SomeUpdate2`
carries the table's FIELDS but not the record REF (the GADT shape),
so the row's record name is re-derived at emission: the registered
record whose field list EQUALS the update's (`recNameOf?` — data,
first match in registry order; the driver's ctx carries the item
universe alongside). A row with no matching record is skipped
honestly (no emitted fn for an unnameable target).

Deliberate exclusions: `tick` fns are emitted only for records with at
least one LOWERABLE update (a record whose updates all skip honestly
gets no tick — a fn over an empty body would be a lie); `.ty`-ref
columns, list columns, and non-.col value shapes, and the non-v1 v2
row shapes (multi-SET/INSERT/DELETE), are not lowerable yet (additive
— extend `valueRust`, the universe stays closed).
-/

module

public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Update2
public import SchemaLang.ExprLang
public import SchemaLang.Emit.Expr
public import SchemaLang.Emit.GenCtx
public import SchemaLang.Emit.Rust
public import SchemaLang.Meta.Reflect

@[expose] public section

namespace SchemaLang.Emit.Update

open CodegenCore.Emit (pascal snake rustIdent)

/-! ## The value lowering (the guard rides Emit.Expr's `boolRustI`) -/

/-- The field-ref rendering (the emitted fn iterates `rows` by `&mut`
    — every field read is `r.<field>`). -/
def refOf : String → String := fun n => s!"r.{rustIdent n}"

/-- The WRITTEN VALUE's Rust text. u64 value exprs delegate to
    `Emit.Expr.u64RustI` (the interface's u64 view); a string value is
    the `.col`-ref shape ONLY (`VExpr` has no string literal) →
    `.clone()`; any other Ty — or any shape not representable — is
    `none` (the honest skip). -/
def valueRust : {fs : List Field} → {t : Ty} → VExpr fs t → Option String
  -- the u64 arm rides the interface (`HasU64.view`)
  | fs, .u64, e => some (Emit.Expr.u64RustI (vexprLang fs) refOf e)
  -- GADT-direct, JUSTIFIED: a string-typed WRITE value is a
  -- syntax-directed shape (`.col`-ref → `.clone()`) at the `.string`
  -- index — the interface's views cover `.u64`/`.bool` only; no
  -- `HasString` capability exists (one joins when a second consumer
  -- needs it — capabilities follow consumers)
  | _, .string, .col n _ => some s!"({refOf n}).clone()"
  | _, _, _ => none

/-! ## The module assembly -/

/-- The emitter's demo row: the record's registry name (the `Vec<<Record>>`
    target — `SomeUpdate2` does not carry it; `InvariantItem.schemaRef`'s
    role) + the registered v2 update. -/
structure DemoUpdate where
  recName : String
  u : SomeUpdate2

/-- The update's apply fn's Rust name (snake — Rust identifiers cannot
    carry the registry name's kebab; the `apply_<name>` shape). -/
def applyFnName (u : DemoUpdate) : String := s!"apply_{snake u.u.update.name}"

/-- The record's folding tick's Rust name. -/
def tickFnName (rec : String) : String := s!"tick_{snake rec}"

/-- The v2 row's singleton SET clause, when it has EXACTLY one — the
    v1-shape gate's spine (a list match on the indexed clause list;
    multi-SET rows are `none`). -/
def v1Clause? (u : SomeUpdate2) : Option (SetClause u.fields) :=
  match u.update.sets with
  | [c] => some c
  | _ => none

/-- THE V1-SHAPE GATE (the v1→v2 migration's emission subset): a v2
    row emits on the v1 surface iff it is the singleton-SET image —
    exactly ONE SET clause, no insert, no delete. Multi-SET/INSERT/
    DELETE rows have no v1 lowering (honest skip). -/
def v1Shape (u : SomeUpdate2) : Bool :=
  (v1Clause? u).isSome && u.update.insert?.isNone && !u.update.delete

/-- Is this update's value lowerable? (the honest-skip test — the v1
    shape AND the value lowering both apply) -/
def lowerable (u : DemoUpdate) : Bool :=
  match v1Clause? u.u with
  | some c => u.u.update.insert?.isNone && !u.u.update.delete
      && (valueRust c.value).isSome
  | none => false

/-- One update → the apply fn (or the honest-skip comment). The body is
    `Update2Item.apply`'s guarded row write (the v1 singleton-SET
    discipline) as a loop: the guard AND the value read the ORIGINAL
    row (batch semantics — no intra-update cascade); a refused row
    passes through untouched. -/
def applyFn (u : DemoUpdate) : List CodegenCore.Emit.Rust.Item :=
  match v1Clause? u.u with
  | none =>
      [ .comment (s!"update `{u.u.update.name}` on {u.recName}: not a v1-shaped "
          ++ "v2 row (multi-SET / INSERT / DELETE) — no v1 lowering, honest skip")
      ]
  | some c =>
      if u.u.update.insert?.isSome || u.u.update.delete then
        [ .comment (s!"update `{u.u.update.name}` on {u.recName}: not a v1-shaped "
            ++ "v2 row (multi-SET / INSERT / DELETE) — no v1 lowering, honest skip")
        ]
      else
        match valueRust c.value with
        | none =>
            [ .comment (s!"update `{u.u.update.name}` on {u.recName}: the value on `{c.field.name}` "
                ++ "has no Rust lowering — honest skip, no fn emitted")
            ]
        | some v =>
            let guardTxt :=
              Emit.Expr.boolRustI (vexprLang u.u.fields) refOf u.u.update.guard
            [ .comment s!"update `{u.u.update.name}` on {u.recName} — writes `{c.field.name}`"
            , .comment "  guard + value read the ORIGINAL row (UpdateItem.applyRow discipline)"
            , .fn s!"fn {applyFnName u}(rows: &mut Vec<{pascal u.recName}>)"
                ("for r in rows.iter_mut() { if " ++ guardTxt ++ " { r."
                  ++ rustIdent c.field.name ++ " = " ++ v ++ "; } }") ]

/-- One record → the tick fn (its lowerable updates in registration
    order — the cascade). Only called for records with ≥1 lowerable
    update (the header's exclusion). -/
def tickFn (ups : List DemoUpdate) (rec : String) : CodegenCore.Emit.Rust.Item :=
  let calls := ups.filter (fun u => u.recName == rec && lowerable u)
  .fn s!"fn {tickFnName rec}(rows: &mut Vec<{pascal rec}>)"
    (String.intercalate " " (calls.map (fun u => s!"{applyFnName u}(rows);")))

/-- The full module items (deterministic: registration order throughout);
    the shared `Emit.Rust.recordGroupedModule` skeleton at the update
    lane's four folds (no trailing test module — `none`). -/
def moduleItems (ups : List DemoUpdate) : List CodegenCore.Emit.Rust.Item :=
  let records := (ups.map (·.recName)).eraseDups
  Emit.Rust.recordGroupedModule
    [ "GENERATED from the schema_update registry (SchemaLang.Meta.updateItemExt) —"
    , "do not edit — regenerate (just gen). One apply fn per update (guard via"
    , "the evalB discipline), one tick fn per record (registration order). The"
    , "spec of record is UpdateItem.applyRow: guard AND value read the ORIGINAL"
    , "row; a refused row passes through untouched; the tick re-runs updates in"
    , "registration order (v1 cascade: single-pass, single-table)." ]
    records
    (ups.flatMap applyFn)
    (records.filterMap (fun rec =>
      if ups.any (fun u => u.recName == rec && lowerable u) then
        some (tickFn ups rec)
      else none))
    none

/-- The emitter's pure fold (the compile logic, fully testable). -/
def updateFiles (ups : List DemoUpdate) : List CodegenCore.Emit.GeneratedFile :=
  [ { path := "../../generated/rust/updates_generated.rs"
      contents := CodegenCore.Emit.Rust.renderModule (moduleItems ups) } ]

/-! ## The emitter -/

/-- The record name for a registered update: the registered RECORD
    whose field list equals the update's (the shape match — the
    registry's records carry the refs `SomeUpdate2` lacks). First match
    in registry order; `none` = unnameable target, the row is skipped
    honestly. Two records with identical field lists would collide —
    the demo registry has no such pair (the dup-name audit keeps the
    registry's RECORD names unique; identical SHAPES are legal but
    unnameable for the update lane — resolved by registry order). -/
def recNameOf? (items : List Item) (u : SomeUpdate2) : Option String :=
  match items with
  | [] => none
  | .record n fields :: rest =>
      if fields == u.fields then some n else recNameOf? rest u
  | _ :: rest => recNameOf? rest u

/-- The emitter's rows: the registered updates re-unified with their
    record's name (the emitter's internal row shape — `applyFn`/
    `tickFn` need the `Vec<<Record>>` target). Rows with no matching
    record are dropped (the honest skip). -/
def ctxRows (ctx : GenCtx) : List DemoUpdate :=
  ctx.updates2.filterMap fun u =>
    recNameOf? ctx.items u |>.map fun recName => { recName := recName, u := u }

/-- The update emitter: buf-plugin shape (name/style/specSource/
    declared outputs/pure run). The parent registry wires it into
    `SchemaLang.Emit.coreEmitters` (one line, the Registry lane's).
    The lane reads `ctx.updates2` — the replayed v2 registry, no
    committed mirror (the v2 contract).

    v1→v2 sweep — the emission subset: the lane emits the V1-SHAPED
    subset of the v2 rows (`v1Shape` — one SET clause, no
    insert/delete), byte-identical to the pre-migration v1 registry's
    content (the command built both from one elaboration). SEAM-KEPT:
    the lane's partiality (`recNameOf?`'s honest skip, `valueRust`'s
    none arms, the v1-shape gate) is reachable on a checked universe —
    the update registry's row-to-record linkage is NOT part of
    `WellFormed`, so no `CheckedUniverse` evidence discharges it; the
    honest skips stay, per the header. -/
def updateEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "update"
  style := .doubleSlash
  specSource := "SchemaLang.Meta.Reflect (update2ItemExt) — schema_update"
  outputs := ["../../generated/rust/updates_generated.rs"]
  run ctx := updateFiles (ctxRows ctx)

end SchemaLang.Emit.Update
