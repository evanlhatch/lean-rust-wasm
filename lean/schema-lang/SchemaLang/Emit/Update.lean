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

Lowering (reuses Emit.Invariant — imported, NOT copied):
- the guard via `boolRust` (the `evalB` discipline: raw u64 ops over
  the struct's fields; strlen = `.len()` on strings),
- the value via `valueRust` (below): u64 value exprs delegate to
  `u64Rust`; a `.col`-of-string value → `(<ref>).clone()` (string
  assignment). ANY other shape → no emitted fn for that row + a
  comment (the honest-skip discipline).

The replay concession (v1, Emit.Invariant's discipline): emitters are
pure `List Item → List GeneratedFile` — no environment reaches `run`,
and `Item` cannot carry the VExpr family, so the emitter's input is
`demoUpdates` — the committed row list below, whose entries mirror
exactly what the Tests' `schema_update` registrations contain (the
Tests' run_cmd pins the mirror: names + derived reads/writes/
selfReading must equal the registry's). When the driver gains an
env-replay hook, `run` switches to `registeredUpdates` with no other
change.

Deliberate exclusions: `tick` fns are emitted only for records with at
least one LOWERABLE update (a record whose updates all skip honestly
gets no tick — a fn over an empty body would be a lie); `.ty`-ref
columns, list columns, and non-.col value shapes are not lowerable yet
(additive — extend `valueRust`, the universe stays closed).
-/

import CodegenCore
import SchemaLang.Item
import SchemaLang.Update
import SchemaLang.Emit.Invariant
import SchemaLang.Meta.Reflect

namespace SchemaLang.Emit.Update

open CodegenCore.Emit (pascal snake rustIdent)

/-! ## The value lowering (the guard rides Emit.Invariant's `boolRust`) -/

/-- The field-ref rendering (the emitted fn iterates `rows` by `&mut`
    — every field read is `r.<field>`). -/
def refOf : String → String := fun n => s!"r.{rustIdent n}"

/-- The WRITTEN VALUE's Rust text. u64 value exprs delegate to
    `Emit.Invariant.u64Rust` (the evalB discipline); a string value is
    the `.col`-ref shape ONLY (`VExpr` has no string literal) →
    `.clone()`; any other Ty — or any shape not representable — is
    `none` (the honest skip). -/
def valueRust : {fs : List Field} → {t : Ty} → VExpr fs t → Option String
  | _, .u64, e => some (SchemaLang.Emit.Invariant.u64Rust refOf e)
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
      let guardTxt := SchemaLang.Emit.Invariant.boolRust refOf u.u.update.guard
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

/-! ## The registered rows (the v1 replay concession — see the header) -/

/-- The User record, as the update lane sees it (the mirror of Demo's
    `@[schema] structure User` — the registered fields the
    `schema_update` command elaborated against). `abbrev` — the
    reducibility rule: the `HasCol` instance search must see through
    the list. -/
abbrev userFields : List Field :=
  [ { name := "id", ty := .u64 }
  , { name := "name", ty := .string }
  , { name := "email", ty := .string }
  , { name := "tags", ty := .list .string } ]

/-- The demo registry's update rows — the mirror of the Tests'
    `schema_update` registrations (the `demoInvariants` discipline; the
    Tests' run_cmd pins the mirror). `self_bump` is the SELF-READING
    row (the value reads the written column — nonlinear, the journal
    carries S0); its guard is the always-true idiom (`where` is
    required, `VExpr .bool` has no literal-true). -/
def demoUpdates : List DemoUpdate :=
  [ { recName := "User"
    , u := { fields := userFields, field := { name := "id", ty := .u64 }
           , update := { name := "reset_id"
                       , guard := .gt (.colOf "id") (.lit 100)
                       , value := .lit 0
                       , writePath := .here } } }
  , { recName := "User"
    , u := { fields := userFields, field := { name := "email", ty := .string }
           , update := { name := "echo_email"
                       , guard := .gt (.strlen (.colOf "name")) (.lit 3)
                       , value := .colOf "name"
                       , writePath := .there (.there .here) } } }
  , { recName := "User"
    , u := { fields := userFields, field := { name := "id", ty := .u64 }
           , update := { name := "self_bump"
                       , guard := .eq (.lit 0) (.lit 0)
                       , value := .colOf "id"
                       , writePath := .here } } } ]

/-- The update emitter: buf-plugin shape (name/style/specSource/
    declared outputs/pure run). The parent registry wires it into
    `SchemaLang.Emit.coreEmitters` (one line, the Registry lane's). -/
def updateEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "update"
  style := .doubleSlash
  specSource := "SchemaLang.Meta.Reflect (updateItemExt) — schema_update"
  outputs := ["../../src/updates_generated.rs"]
  run _ := updateFiles demoUpdates

end SchemaLang.Emit.Update
