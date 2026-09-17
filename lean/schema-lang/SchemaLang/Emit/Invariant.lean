/-
# SchemaLang.Emit.Invariant — invariants → Rust check functions

The invariant registry (SchemaLang.Meta.Reflect's `invariantItemExt`,
authoring surface `schema_invariant`) is EMITTED here:
`../../src/invariants_generated.rs` — one `pub fn check_<name>(v:
&<Record>) -> bool` per invariant, compiled from the VExpr value (the
`evalB` discipline: raw u64 ops over the struct's fields; strlen =
`.len()` on strings), plus one `validate_<record>` folding that
record's invariants with AND, plus a `#[cfg(test)]` module whose test
per invariant pins the LEAN-COMPUTED verdict on the all-default row
(a failing row must fail — the Rust CI replays it).

The Item-AST discipline (Emit/Rust.lean): item shape goes through the
`CodegenCore.Emit.Rust.Item` nodes; string interpolation appears only
in leaf payloads (fn bodies — the audited concession). Names are
pre-mangled via `Emit.snake`/`rustIdent`/`pascal` — the AST never
case-converts. The expression lowering (u64/bool → Rust text) lives in
`Emit.Expr` — the shared consumer module written against the
`ExprLang` interface (W7.2 phase 2; phase 1 housed it here).

The emitter contract (v2): `run` takes the FULL registry state
(`Emit.GenCtx`) — the invariant lane reads `ctx.invariants`, the
ext-replayed `schema_invariant` rows (the driver replays them from the
spec module's oleans; the spec of record is the byte-tied generated
artifact, and the demo's registrations live IN `Demo.lean` — spec data
belongs to the spec).

Deliberate exclusions: `proved` rows still emit their check fn (the
tier is enforcement INTENT — recorded in the comment; the emitted fn
is the boundary half of the ladder either way); `oracleCovered` rows
do not exist in the demo registry yet (the ctor is closed for when
they do).
-/

module

public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Invariant
public import SchemaLang.ExprLang
public import SchemaLang.Emit.Expr
public import SchemaLang.Emit.GenCtx
public import SchemaLang.Meta.Reflect

@[expose] public section

namespace SchemaLang.Emit.Invariant

open CodegenCore.Emit (pascal snake rustIdent)

/-! ## The default row — the Lean-computed test verdict

`defaultValue?`/`defaultRow?` MOVED to `SchemaLang.Validate` (W8.2 —
the keys lane's obligation claims needed them and this module imports
`Meta.Reflect`, so they had to live below the emit/meta split; the
`RowVals` home owns them). This section keeps the consumers. -/

/-- The invariant's verdict on the all-default row — the verdict the
    emitted `#[test]` pins (a false verdict = the failing row that must
    fail). -/
def defaultVerdict (it : InvariantItem) : Option Bool := do
  let row ← defaultRow? it.inv.fields
  -- the interface's validator projection (W7.2 phase 2) —
  -- `validatesI_vexpr` ties it to `validates`, so the pinned verdict's
  -- bytes are unchanged
  pure (validatesI (vexprLang it.inv.fields) it.inv.expr row)

/-! ## The Rust literal defaults (the test row's construction) -/

def rustDefault? : Ty → Option String
  | .bool => some "false"
  | .u8 => some "0u8" | .u16 => some "0u16"
  | .u32 => some "0u32" | .u64 => some "0u64"
  | .i8 => some "0i8" | .i16 => some "0i16"
  | .i32 => some "0i32" | .i64 => some "0i64"
  | .f32 => some "0.0f32" | .f64 => some "0.0f64"
  | .string => some "String::new()"
  | .bytes => some "Vec::new()"
  | .option _ => some "None"
  | .list _ => some "Vec::new()"
  -- the flat default: `Vec::new()` (empty = the zero-count flat form —
  -- the wire's dims list carries the shape, an empty Vec is the
  -- only self-contained literal consistent with any dims... the
  -- HONEST default: `none` — an empty Vec's shape is 0, not dims —
  -- a tensor field gets no emitted test literal (the .ty rule)).
  | .tensor _ _ => none
  -- map/set: `BTreeMap::new()`/`BTreeSet::new()` are self-contained
  -- but need the `std::collections` import in the emitted test module
  -- — not pinned today (no consumer), so the HONEST default: `none`
  -- (the tensor rule). v2 with the imports work.
  | .map _ _ | .set _ => none
  | .result _ _ | .future _ | .stream _ | .ty _ => none

/-! ## The module assembly -/

/-- The check fn's Rust name (snake — Rust identifiers cannot carry the
    registry name's kebab; the mission's `check_<name>` shape). -/
def checkFnName (it : InvariantItem) : String := s!"check_{snake it.name}"

/-- The record's folding validator's Rust name. -/
def validateFnName (rec : String) : String := s!"validate_{snake rec}"

/-- One invariant → the tier comment + the check fn. -/
def checkFn (it : InvariantItem) : List CodegenCore.Emit.Rust.Item :=
  let proofLine := match it.proofName with
    | some thm => s!" — proved via `{thm}` (citation resolved in CI)"
    | none => ""
  [ .comment s!"invariant `{it.name}` on {it.schemaRef} — tier: {it.tier.render}{proofLine}"
  , .fn s!"fn {checkFnName it}(v: &{pascal it.schemaRef}) -> bool"
      (Emit.Expr.boolRustI (vexprLang it.inv.fields)
        (fun n => s!"v.{rustIdent n}") it.inv.expr) ]

/-- One record → the folding validator (AND over its invariants). -/
def validateFn (invs : List InvariantItem) (rec : String) :
    CodegenCore.Emit.Rust.Item :=
  let ref : String → String := fun n => s!"v.{rustIdent n}"
  let body := String.intercalate " && "
    (invs.map fun it =>
      s!"({Emit.Expr.boolRustI (vexprLang it.inv.fields) ref it.inv.expr})")
  .fn s!"fn {validateFnName rec}(v: &{pascal rec}) -> bool"
    (if invs.isEmpty then "true" else body)

/-- One invariant → the `#[test]` pair (the Lean-computed default-row
    verdict, replayed in Rust CI). Skipped when any field lacks a
    literal default (`.ty` refs et al). -/
def testFn (it : InvariantItem) : Option (List CodegenCore.Emit.Rust.Item) := do
  let verdict ← defaultVerdict it
  let fields ← it.inv.fields.mapM fun f =>
    (rustDefault? f.ty).map fun d => s!"{rustIdent f.name}: {d}"
  let fieldsTxt := String.intercalate ", " fields
  let body := s!"let v = {pascal it.schemaRef} \{ {fieldsTxt} }; "
    ++ s!"assert_eq!({checkFnName it}(&v), {verdict});"
  some [ .raw "#[test]"
       , .fn s!"fn {checkFnName it}_default_row()" body ]

/-- The full module items (deterministic: registry order throughout). -/
def moduleItems (invs : List InvariantItem) : List CodegenCore.Emit.Rust.Item :=
  let records := (invs.map (·.schemaRef)).eraseDups
  [.comment "GENERATED from the schema_invariant registry (SchemaLang.Meta.invariantItemExt) —"
  , .comment "do not edit — regenerate (just gen). One check fn per invariant (the evalB"
  , .comment "discipline: raw u64 ops over the struct's fields; strlen = .len() on strings)."
  , .raw "" ]
  ++ records.map (fun rec => .use_ s!"crate::schema_generated::{pascal rec}")
  ++ [.raw "" ]
  ++ invs.flatMap checkFn
  ++ [.raw "" ]
  ++ records.map (fun rec => validateFn (invs.filter (·.schemaRef == rec)) rec)
  ++ [.raw "" ]
  ++ [ .raw "#[cfg(test)]"
     , .mod_ "invariant_tests"
         ([.raw "use super::*;"] ++ (invs.filterMap testFn).flatten) ]

/-- The emitter's pure fold (the compile logic, fully testable). -/
def invariantFiles (invs : List InvariantItem) : List CodegenCore.Emit.GeneratedFile :=
  [ { path := "../../src/invariants_generated.rs"
      contents := CodegenCore.Emit.Rust.renderModule (moduleItems invs) } ]

/-! ## The emitter -/

/-- The invariant emitter: buf-plugin shape (name/style/specSource/
    declared outputs/pure run). The parent registry wires it into
    `SchemaLang.Emit.coreEmitters`. The lane reads `ctx.invariants` —
    the replayed registry, no committed mirror (the v2 contract). -/
def invariantEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "invariant"
  style := .doubleSlash
  specSource := "SchemaLang.Meta.Reflect (invariantItemExt) — schema_invariant"
  outputs := ["../../src/invariants_generated.rs"]
  run ctx := invariantFiles ctx.invariants

end SchemaLang.Emit.Invariant
