/-
# SchemaLang.Emit.Update — updates → Rust apply functions

The update registry (SchemaLang.Meta.Reflect's `updateItemExt`,
authoring surface `schema_update`) is EMITTED here:
`../../src/updates_generated.rs` — one `pub fn apply_<name>(rows: &mut
Vec<<Record>>) ` per update (the guard + the single-column write,
compiled from the VExpr values), plus one `pub fn tick_<record>`
folding that record's updates in registration order (the tick's
cascade, v1: single-pass, single-table — Update.lean's machine pins the
STAGE discipline, this file emits its row-transform half).

The Item-AST discipline (Emit/Rust.lean): item shape goes through the
`CodegenCore.Emit.Rust.Item` nodes; string interpolation appears only
in leaf payloads (fn bodies — the audited concession). Names are
pre-mangled via `Emit.snake`/`rustIdent`/`pascal` — the AST never
case-converts.

Lowering (reuses Emit.Expr — the interface lowering, imported, NOT
copied; W7.2 phase 2 — the phase-1 COMPAT spellings are gone):
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
`ctx.updates`, the ext-replayed `schema_update` rows. `SomeUpdate`
carries the table's FIELDS but not the record REF (the GADT shape),
so the row's record name is re-derived at emission: the registered
record whose field list EQUALS the update's (`recNameOf?` — data,
first match in registry order; the driver's ctx carries the item
universe alongside). A row with no matching record is skipped
honestly (no emitted fn for an unnameable target).

Deliberate exclusions: `tick` fns are emitted only for records with at
least one LOWERABLE update (a record whose updates all skip honestly
gets no tick — a fn over an empty body would be a lie); `.ty`-ref
columns, list columns, and non-.col value shapes are not lowerable yet
(additive — extend `valueRust`, the universe stays closed).

v1→v2 note (the demotion): this emitter reads the V1 registry
(`ctx.updates` = `updateItemExt` — the byte-tie pins
`updates_generated.rs` to these rows). Every v1 row is the
singleton-SET image of the same registration's v2 row
(`Update2Item` — one `SetClause`, no insert/delete; the command builds
both from one elaboration), so the emitted text is the v2 reading's
byte-identical projection: `UpdateItem.applyRow`'s guard-then-write
discipline IS `Update2.applySets` at one clause. Switching the source
to `update2ItemExt` is the named follow-up (moves `Emit.GenCtx.updates`
and the gates' `registeredUpdates` fold together; byte-tie
re-verification mandatory).
-/

module

public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Update
public import SchemaLang.ExprLang
public import SchemaLang.Emit.Expr
public import SchemaLang.Emit.GenCtx
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
    target — `SomeUpdate` does not carry it; `InvariantItem.schemaRef`'s
    role) + the registered update. -/
structure DemoUpdate where
  recName : String
  u : SomeUpdate

/-- The update's apply fn's Rust name (snake — Rust identifiers cannot
    carry the registry name's kebab; the `apply_<name>` shape). -/
def applyFnName (u : DemoUpdate) : String := s!"apply_{snake u.u.update.name}"

/-- The record's folding tick's Rust name. -/
def tickFnName (rec : String) : String := s!"tick_{snake rec}"

/-- Is this update's value lowerable? (the honest-skip test) -/
def lowerable (u : DemoUpdate) : Bool :=
  (valueRust u.u.update.value).isSome

/-- One update → the apply fn (or the honest-skip comment). The body is
    `UpdateItem.applyRow` as a loop: the guard AND the value read the
    ORIGINAL row (batch semantics — no intra-update cascade); a refused
    row passes through untouched. -/
def applyFn (u : DemoUpdate) : List CodegenCore.Emit.Rust.Item :=
  match valueRust u.u.update.value with
  | none =>
      [ .comment (s!"update `{u.u.update.name}` on {u.recName}: the value on `{u.u.field.name}` "
          ++ "has no Rust lowering — honest skip, no fn emitted")
      ]
  | some v =>
      let guardTxt :=
        Emit.Expr.boolRustI (vexprLang u.u.fields) refOf u.u.update.guard
      [ .comment s!"update `{u.u.update.name}` on {u.recName} — writes `{u.u.field.name}`"
      , .comment "  guard + value read the ORIGINAL row (UpdateItem.applyRow discipline)"
      , .fn s!"fn {applyFnName u}(rows: &mut Vec<{pascal u.recName}>)"
          ("for r in rows.iter_mut() { if " ++ guardTxt ++ " { r."
            ++ rustIdent u.u.field.name ++ " = " ++ v ++ "; } }") ]

/-- One record → the tick fn (its lowerable updates in registration
    order — the cascade). Only called for records with ≥1 lowerable
    update (the header's exclusion). -/
def tickFn (ups : List DemoUpdate) (rec : String) : CodegenCore.Emit.Rust.Item :=
  let calls := ups.filter (fun u => u.recName == rec && lowerable u)
  .fn s!"fn {tickFnName rec}(rows: &mut Vec<{pascal rec}>)"
    (String.intercalate " " (calls.map (fun u => s!"{applyFnName u}(rows);")))

/-- The full module items (deterministic: registration order throughout). -/
def moduleItems (ups : List DemoUpdate) : List CodegenCore.Emit.Rust.Item :=
  let records := (ups.map (·.recName)).eraseDups
  [.comment "GENERATED from the schema_update registry (SchemaLang.Meta.updateItemExt) —"
  , .comment "do not edit — regenerate (just gen). One apply fn per update (guard via"
  , .comment "the evalB discipline), one tick fn per record (registration order). The"
  , .comment "spec of record is UpdateItem.applyRow: guard AND value read the ORIGINAL"
  , .comment "row; a refused row passes through untouched; the tick re-runs updates in"
  , .comment "registration order (v1 cascade: single-pass, single-table)."
  , .raw "" ]
  ++ records.map (fun rec => .use_ s!"crate::schema_generated::{pascal rec}")
  ++ [.raw "" ]
  ++ ups.flatMap applyFn
  ++ [.raw "" ]
  ++ records.filterMap (fun rec =>
        if ups.any (fun u => u.recName == rec && lowerable u) then
          some (tickFn ups rec)
        else none)

/-- The emitter's pure fold (the compile logic, fully testable). -/
def updateFiles (ups : List DemoUpdate) : List CodegenCore.Emit.GeneratedFile :=
  [ { path := "../../src/updates_generated.rs"
      contents := CodegenCore.Emit.Rust.renderModule (moduleItems ups) } ]

/-! ## The emitter -/

/-- The record name for a registered update: the registered RECORD
    whose field list equals the update's (the shape match — the
    registry's records carry the refs `SomeUpdate` lacks). First match
    in registry order; `none` = unnameable target, the row is skipped
    honestly. Two records with identical field lists would collide —
    the demo registry has no such pair (the dup-name audit keeps the
    registry's RECORD names unique; identical SHAPES are legal but
    unnameable for the update lane — resolved by registry order). -/
def recNameOf? (items : List Item) (u : SomeUpdate) : Option String :=
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
  ctx.updates.filterMap fun u =>
    recNameOf? ctx.items u |>.map fun recName => { recName := recName, u := u }

/-- The update emitter: buf-plugin shape (name/style/specSource/
    declared outputs/pure run). The parent registry wires it into
    `SchemaLang.Emit.coreEmitters` (one line, the Registry lane's).
    The lane reads `ctx.updates` — the replayed registry, no committed
    mirror (the v2 contract). -/
def updateEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "update"
  style := .doubleSlash
  specSource := "SchemaLang.Meta.Reflect (updateItemExt) — schema_update"
  outputs := ["../../src/updates_generated.rs"]
  run ctx := updateFiles (ctxRows ctx)

end SchemaLang.Emit.Update
