/-
# Substrait.Typed.Builder

A small fluent builder over `Rel`s — the authoring surface for the golden
plan in the Tests.

**Canonicalization at construction**: consecutive `.filter` calls fuse into a
single `Filter` rel whose conditions are ANDed (matching what a SQL planner
would produce — important for byte-identical goldens against the producer's
output).  Adjacent `.project` calls compose by construction (each project
extends the schema; a later project's expressions refer to the earlier one's
schema).  Because the typed layer represents each rel node explicitly,
fusion is the *only* canonicalization its authoring needs.

The builder tracks a single in/out schema pair; `.project` changes the output
schema, so the builder's type follows the pipeline.

`filter`/`sort`/`fetch`/`union` are **schema-preserving** (`Rel.filter` is a
schema-preserving wire node): on a `Builder inS outS` where `inS ≠ outS`
(e.g. after `.project`) a filter would need a schema equality the typed layer
refuses to invent, so those steps are typed `Builder inS inS`.  This is the
only shape the golden plan (and any filter-before-project pipeline) needs.
-/
import Substrait.Typed.Rel

namespace Substrait.Typed

/-- A fluent plan fragment: `Rel inS outS` plus pipeline sugar. -/
structure Builder (inS outS : Schema) where
  rel : Rel inS outS

namespace Builder

/-- Start from a table scan. -/
def read (table : String) (schema : Schema) : Builder schema schema :=
  { rel := .read table schema }

/--
Fuse a filter condition into a schema-preserving rel: a `.filter` node gets
its condition ANDed with the incoming condition (the fusion canonicalization);
anything else receives a fresh `.filter` wrap.  The schema is an explicit
parameter so the dependent indices refine cleanly (no `sorry`).
-/
def fuseFilter (s : Schema) (r : Rel s s) (n : Bool) (cond : Expr s .bool n) : Rel s s :=
  match r with
  | .filter inner c => Rel.filter inner (Expr.and c cond)
  | rel => Rel.filter rel cond

/--
`filter cond` — keep rows matching `cond`, fusing consecutive filters into
one `Filter` rel with ANDed conditions.  The condition comes **first** so the
pipeline sugar reads `builder |> Builder.filter cond` (the infix `|>` feeds the
builder into the trailing position).
-/
def filter (cond : Expr inS .bool n2) (b : Builder inS inS) : Builder inS inS :=
  { rel := fuseFilter inS b.rel n2 cond }

/-- `project outs` — compute new columns (output = input columns ++ new).  Like `filter`, the columns come first for the `|>` pipeline. -/
def project (outs : List (Projection s)) (b : Builder inS s) : Builder inS (projectOut s outs) :=
  { rel := .project b.rel outs none }

/-- `fetch limit offset` — apply limit/offset (schema-preserving). -/
def fetch (b : Builder inS inS) (limit offset : Option Nat) : Builder inS inS :=
  { rel := .fetch b.rel limit offset }

/-- `sort by` — order rows (schema-preserving). -/
def sort (b : Builder inS inS) (orderBy : List (SortKey inS)) : Builder inS inS :=
  { rel := .sort b.rel orderBy }

/-- Union with another same-shape fragment (schema-preserving). -/
def union (b : Builder inS inS) (other : Rel inS inS) : Builder inS inS :=
  { rel := .set .unionAll b.rel other }

/-- Lower to the underlying rel. -/
def toRel (b : Builder inS outS) : Rel inS outS := b.rel

end Builder

end Substrait.Typed
