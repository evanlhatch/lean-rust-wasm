/-
# Substrait.Typed.Rel

The schema-indexed relation family.

`Rel (inS outS : Schema)` is a well-typed plan fragment that takes rows of
schema `inS` and produces rows of schema `outS`.  Constructors:

- `read`       : a base table scan (schema-preserving)
- `filter`     : keep rows matching a boolean expression
- `project`    : compute new columns; output = input columns ++ new columns;
                 carries an optional `RelCommon.Emit` output mapping (the
                 column-replacing UPDATE shape — see
                 `crates/flatland-substrait/src/builders.rs::project_emit`).
                 With a mapping the *direct* output schema (input ++ new)
                 overstates the visible width; the mapping is metadata that
                 `ToProto`/`Emit.Text` honor, and no v0 rel consumes an
                 emit-mapped project's output, so the direct index is the
                 documented compromise.
- `aggregate`  : group + measure — output = grouping keys ++ measure columns
- `sort`, `fetch`, `set` (union), `write` (DML: op + table schema + input),
  `extensionSingle`

The language is a plain GADT rather than lean-linq's PHOAS `∀ ρ` bundle: our
binders are shallow (no comprehension spine), so a single typed term with
functions over it (`toProto`, `eval`) is the simpler fit.  This choice is
documented in the README.

Columns are referenced by name through `HasCol` (ordinals computed at
`toProto`).  Function calls embed their `FunctionSig`; wire anchors are
assigned at emission (see `Substrait.Typed.ToProto`).

Aggregate grouping keys and measure arguments use `AnyExpr s` (the
type-erased package) instead of a bare dependent sigma: Lean forbids
`Σ`/nested inductives with local-variable parameters under the GADT, and the
indexed `Args` spine is only meaningful when the accepted shape is a *signature*
argument list.
-/
import Substrait.Typed.Expr
import Substrait.Proto.Rel

namespace Substrait.Typed

/-- A projection in `Rel.project`: a named output column backed by an expression over the projection's input schema. -/
structure Projection (sc : Schema) where
  name : String
  dtype : SType
  nullable : Bool
  expr : Expr sc dtype nullable

/-- The output schema of a projection: input columns followed by the new columns. -/
def projectOut (p : Schema) (outs : List (Projection p)) : Schema :=
  p ++ outs.map (fun pr => (pr.name, pr.dtype, pr.nullable))

/-- An aggregate measure: a signature invocation over the aggregate input schema. -/
structure Measure (s : Schema) where
  sig : FunctionSig
  args : List (AnyExpr s)

/-- The schema of an aggregate's output: grouping keys then measure columns (both unnamed; the positions are the contract). -/
def aggregateOut (s : Schema) (grouping : List (AnyExpr s)) (measures : List (Measure s)) : Schema :=
  (grouping.map (fun ⟨t, n, _⟩ => ("", t, n))) ++
    measures.map (fun m => ("", m.sig.ret, m.sig.retNullable))

/-- A sort key: the column to order by (a resolved reference) plus its direction. -/
structure SortKey (s : Schema) where
  col : Column
  direction : Proto.SortDirection

/-- Construct a `SortKey` for a named column (instances search `HasCol s name t n`). -/
def sortKey {s : Schema} (name : String) (t : SType) (n : Bool) (direction : Proto.SortDirection)
    [h : HasCol s name t n] : SortKey s :=
  -- Use `h.index` directly: re-running instance search here would be stuck
  -- because the `Column` result type pins none of `s`/`t`/`n`.
  { col := { name := name, ordinal := h.index }, direction := direction }

/--
`Rel` — the schema-indexed relation family.  `Rel inS outS` takes rows of
`inS` and produces rows of `outS`.  Leaf relations preserve their schema
(`read`); each node's output schema is computed from its arguments
(`project` appends, `aggregate` returns grouping keys + measures, `join`
concatenates both sides).
-/
inductive Rel : Schema → Schema → Type where
  | read (table : String) (schema : Schema) : Rel schema schema

  | filter (input : Rel s s) (cond : Expr s .bool n) : Rel s s

  | project (input : Rel s p) (outs : List (Projection p))
            (emit : Option (List Nat)) : Rel s (projectOut p outs)

  | aggregate (aggInput : Rel s s) (grouping : List (AnyExpr s))
              (measures : List (Measure s)) : Rel s (aggregateOut s grouping measures)

  | sort (input : Rel s s) (orderBy : List (SortKey s)) : Rel s s

  | fetch (input : Rel s s) (limit offset : Option Nat) : Rel s s

  | join (left : Rel sl sl') (right : Rel sr sr')
         (cond : Expr (sl' ++ sr') .bool n)
         (joinType : Proto.JoinType) : Rel (sl ++ sr) (sl' ++ sr')

  | set (op : Proto.SetOp) (left : Rel s s') (right : Rel s s') : Rel s s'

  | write (op : String) (table : String) (tableSchema : Option Schema)
          (input : Rel s s') : Rel s s'

  | extensionSingle (detail : String) (input : Rel s s') : Rel s s'

end Substrait.Typed
