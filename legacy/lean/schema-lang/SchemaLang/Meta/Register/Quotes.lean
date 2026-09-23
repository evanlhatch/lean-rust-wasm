/-
# SchemaLang.Meta.Register.Quotes — the typed-quotation helpers (Qq)

Extracted from `SchemaLang.Meta.Reflect` (pure code motion — every
declaration keeps its exact statement and name): the binder-discipline
`Q(_)` builders shared by the invariant and update commands.

v1→v2 (the migration): the v1 `UpdatePure`/`UpdateItem` quotation
helpers (`updatePureInstTyQ`/`updatePureInstPfQ`) were DELETED with
the v1 surface (Qq quotations resolve their constants at definition
time — a quotation naming a deleted constant fails to compile, so the
dead helpers had to go, not just go uncalled). The v2 pure-lock
helpers live with the command (`Meta.Register.Updates`'s
`update2PureInstTyQ`/`update2PureInstPfQ`).
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
public meta section

namespace SchemaLang.Meta

open Lean
open Qq

/-! ## Typed-quotation helpers (Qq)

Every `q(...)` quotation takes its runtime data as BINDERS, never
let-bound or inline `toExpr` antiquotes: Qq's unquoter unfolds
let-values/definitions before checking for the `Quoted` type, so only
binder-position `Q(_)` variables survive. The plain wrappers then fill
the binders with `toExpr` casts — sound because the `ToExpr` instances
emit literal denotations. -/

/-- `Ty` → its constructor tree as a TYPED quotation (the
    expected-type builder: the command elaborates the author's term
    against `VExpr <the record's real fields> .bool`). The `Q(Ty)`
    ascription is sound: `ToExpr Ty` emits the literal denotation.
    This IS the instance-driven adapter (the Expr-level core is the
    `ToExpr Ty` walk itself); the Term-level twin is
    `SchemaLang.Meta.tyTerm` in `Meta.Derive` (pinned to agree with
    this core by that module's drift-pin). -/
def tyToExpr (t : Ty) : Q(Ty) :=
  toExpr t

/-- One field → the `Field.mk` application (the binder-discipline
    quotation; see the section note). -/
def fieldToExprQ (n : Q(String)) (t : Q(Ty)) : Q(Field) :=
  q(Field.mk $n $t)

/-- One field → the `Field.mk` application (the GADT's index term),
    as a typed quotation. -/
def fieldToExpr (f : Field) : Q(Field) :=
  fieldToExprQ (toExpr f.name) (tyToExpr f.ty)

/-- The empty field list (the fold's seed; binder discipline). -/
def fieldsNilQ : Q(List Field) := q([])

/-- `cons` on the field-list literal (binder discipline). -/
def fieldsConsQ (f : Q(Field)) (fs : Q(List Field)) : Q(List Field) :=
  q($f :: $fs)

/-- The record's fields as a `List Field` literal term — the index the
    expected type carries, so the `HasCol` instance search walks the
    REAL schema (a misspelled column fails instance search). Pure Qq
    fold (was `Meta.mkListLit`). -/
def fieldsToExpr (fields : List Field) : Q(List Field) :=
  fields.foldr (fun f acc => fieldsConsQ (fieldToExpr f) acc) fieldsNilQ

/-- `VExpr <fields> .bool` as a type quotation. -/
def vexprBoolTyQ (fsList : Q(List Field)) : Q(Type) :=
  q(VExpr $fsList Ty.bool)

/-- `VExpr <fields> <ty>` as a type quotation. -/
def vexprTyQ (fsList : Q(List Field)) (t : Q(Ty)) : Q(Type) :=
  q(VExpr $fsList $t)

/-- `ColPath <name> <ty> <fields>` as a type quotation. -/
def colPathTyQ (fsList : Q(List Field)) (n : Q(String)) (t : Q(Ty)) : Q(Type) :=
  q(ColPath $n $t $fsList)

end SchemaLang.Meta

end -- public meta section
