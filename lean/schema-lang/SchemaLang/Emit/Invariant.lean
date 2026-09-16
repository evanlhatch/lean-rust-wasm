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
case-converts.

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

import CodegenCore
import SchemaLang.Item
import SchemaLang.Invariant
import SchemaLang.ExprLang
import SchemaLang.Emit.GenCtx
import SchemaLang.Meta.Reflect

namespace SchemaLang.Emit.Invariant

open CodegenCore.Emit (pascal snake rustIdent)

/-! ## The VExpr → Rust lowering (the evalB discipline), written ONCE
    against the ExprLang interface (W7.2) -/

/-- The u64 operand's Rust text — the EMISSION reading of the
    `U64Node` view: the name is the rendering key, the boxed
    projection the node carries is the evaluation readings' half
    (ignored here). `ref` renders a field ref (the record's struct
    field — `rustIdent`-mangled). -/
def u64RustI (L : ExprLang) [HasU64 L] (ref : L.Ident → String)
    (e : L.Expr .u64) : String :=
  match HasU64.view e with
  | .lit v => s!"{v}u64"
  | .col n _ => ref n
  | .strlenCol n _ => s!"({ref n}).len() as u64"

/-- The boolean's Rust text ALGEBRA (children arrive pre-folded to
    text — the fold owns the recursion). -/
def boolRustAlg {I R : Type} (ref : I → String) :
    BoolNode I R String String → String
  | .col n _ => s!"({ref n}) as u64 == 1"
  | .gt a b => s!"({a} > {b})"
  | .eq a b => s!"({a} == {b})"
  | .and a b => s!"({a} && {b})"
  | .not a => s!"(!({a}))"

/-- The boolean's Rust text: the fold at the emission algebras. -/
def boolRustI (L : ExprLang) [HasU64 L] [HasBool L] (ref : L.Ident → String)
    (e : L.Expr .bool) : String :=
  HasBool.fold (u64RustI L ref) (boolRustAlg ref) e

/-- COMPAT (W7.2 phase 1): the VExpr-specialized spellings Emit.Update
    still rides; its port is the next consumer step. Same signatures
    as the pre-interface defs. -/
def u64Rust (ref : String → String) {fs : List Field} (e : VExpr fs .u64) : String :=
  u64RustI (vexprLang fs) ref e

def boolRust (ref : String → String) {fs : List Field} (e : VExpr fs .bool) : String :=
  boolRustI (vexprLang fs) ref e

/-! ## The default row — the Lean-computed test verdict -/

/-- The default value per Ty (`none` = no literal: `.ty` refs have no
    `Value` ctor — a record with such a field gets no emitted test). -/
def defaultValue? : (t : Ty) → Option (Value t)
  | .bool => some (.bool false)
  | .u8 => some (.u8 0) | .u16 => some (.u16 0)
  | .u32 => some (.u32 0) | .u64 => some (.u64 0)
  | .i8 => some (.i8 0) | .i16 => some (.i16 0)
  | .i32 => some (.i32 0) | .i64 => some (.i64 0)
  | .f32 => some (.f32 0) | .f64 => some (.f64 0)
  | .string => some (.string "")
  | .bytes => some (.bytes [])
  | .option _ => some .none
  | .list _ => some (.list .nil)
  -- the zero-dims default only: `TVal.scalar` IS the 0-dim shape; a
  -- nonzero-dims tensor needs per-element literals (none available)
  | .tensor [] a => do let v ← defaultValue? a; some (Value.tensor (TVal.scalar v))
  | .tensor (_ :: _) _ => none
  | .result ok _ => do let v ← defaultValue? ok; some (.ok v)
  | .future a => do let v ← defaultValue? a; some (.future v)
  | .stream _ => some (.stream .nil)
  | .ty _ => none

/-- The all-default row for a field list (`none` = a field without a
    literal default). -/
def defaultRow? : (fs : List Field) → Option (RowVals fs)
  | [] => some .nil
  | f :: rest => do
      let v ← defaultValue? f.ty
      let rest' ← defaultRow? rest
      some (.cons v rest')

/-- The invariant's verdict on the all-default row — the verdict the
    emitted `#[test]` pins (a false verdict = the failing row that must
    fail). -/
def defaultVerdict (it : InvariantItem) : Option Bool := do
  let row ← defaultRow? it.inv.fields
  pure (validates it.inv.expr row)

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
      (boolRustI (vexprLang it.inv.fields) (fun n => s!"v.{rustIdent n}") it.inv.expr) ]

/-- One record → the folding validator (AND over its invariants). -/
def validateFn (invs : List InvariantItem) (rec : String) :
    CodegenCore.Emit.Rust.Item :=
  let ref : String → String := fun n => s!"v.{rustIdent n}"
  let body := String.intercalate " && "
    (invs.map fun it => s!"({boolRustI (vexprLang it.inv.fields) ref it.inv.expr})")
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
