/-
# QLang.Query

The fluent read-side pipeline: `table "units" |> filter (...) |> project [...]`.

Ported from the flatland lineage's `FlatlandDsl.Query`, plus the BUILDER'S
CANON carried over from `Substrait.Typed.Builder`:

- **Filter fusion at construction** — consecutive `.filter` steps fuse into a
  single `Filter` rel whose conditions are ANDed (matching what a SQL planner
  would produce; important for byte-identical goldens against a producer's
  output). The dynamic surface reuses `Builder.fuseFilter` — one copy of the
  canon.
- **The `|>` convention** — every step's data arguments come FIRST and the
  pipeline value is the LAST positional argument, so
  `q |> Query.filter cond |> Query.project outs` reads left-to-right.

`Query inS outS` holds a typed `Rel inS outS` plus a *validation log*.  Steps
are total (pipe-friendly), and each step's runtime validation (column exists,
function arity/argument types match the known signature) records an error
rather than aborting; `Query.checked` turns the log into an `Except String`
at the end, and `Query.toRel` exposes the underlying rel for consumers.

The schema is the pipeline's *type index*: `filter`/`project` compile their
expressions against that index viewed *as data* (schemas are `abbrev` values,
so `s : Schema` is simultaneously the type and the term to validate against).
`filter` is schema-preserving (`Query s s`); `project` appends compiled
columns: output schema = input ++ successful projections (matching Substrait
Project's additive shape).

Deliberate exclusions (see the package header): no `join` step (the typed
surface owns joins; a dynamic join needs a two-pipeline combinator — deferred
until a consumer needs it) and no write/DML steps (the dig's SKIP list).
-/
import Substrait.Typed
import QLang.Error
import QLang.Registry
import QLang.DExpr

namespace QLang

open Substrait.Typed

/-- A fluent pipeline: a typed rel plus collected validation errors. -/
structure Query (inS outS : Schema) where
  rel : Rel inS outS
  errors : List String

namespace Query

/-- Start from a table scan with an explicit schema (mirrors `Typed.Builder.read`). -/
def table (name : String) (schema : Schema) : Query schema schema :=
  { rel := Rel.read name schema, errors := [] }

/-- Start from the registry (`Except` — the table may not exist).  The result
is a dependent pair because the schema (hence the pipeline type) only exists
once the table is found. -/
def fromRegistry (reg : Registry) (name : String) : Except String (Σ s, Query s s) := do
  let t ← reg.find name
  pure (Sigma.mk t.schema (table t.name t.schema))

/-- `filter cond` — keep rows matching a boolean `DExpr`, compiling it against
the pipeline schema (schema-preserving, like `Typed.Builder.filter`).  The
canon: the compiled condition is FUSED into an existing trailing `Filter` node
(ANDed) rather than wrapped — `Builder.fuseFilter` is the single copy. -/
def filter (cond : DExpr) (q : Query s s) : Query s s :=
  match q with
  | { rel := r, errors := errs } =>
      match compile s cond with
      | .ok ⟨t, n, e⟩ =>
          match t with
          | .bool =>
              { rel := Builder.fuseFilter s r n e, errors := errs }
          | t =>
              { rel := r, errors := s!"filter condition must be boolean, got {repr t}" :: errs }
      | .error e =>
          { rel := r, errors := e :: errs }

/-- ONE compile pass over the projection list: each `DExpr` is compiled
exactly once, and the results are partitioned (input order preserved within
each side) into the successful projections and the validation errors.
`successes` and `failures` are projections of this fold — recompiling
separately doubled the work and made the error order depend on which list
was demanded first.  The partitioner is core's order-preserving
`List.partitionMap` (no `partitionResults` helper exists in core/TestKit). -/
def compileProjections (p : Schema) (outs : List (String × DExpr)) :
    List (Projection p) × List String :=
  outs.partitionMap (fun (nm, d) =>
    match compile p d with
    | .ok c => .inl { name := nm, dtype := c.t, nullable := c.n, expr := c.e }
    | .error e => .inr e)

/-- The *successful* projections of a `project` call (used for both the output
schema of the step and the rel it builds, so the type and the value agree). -/
def successes (p : Schema) (outs : List (String × DExpr)) : List (Projection p) :=
  (compileProjections p outs).1

/-- The validation errors of a `project` call (the failing projections). -/
def failures (p : Schema) (outs : List (String × DExpr)) : List String :=
  (compileProjections p outs).2

/-- `project outs` — append named columns (additive, like Substrait
`ProjectRel`); output schema = input ++ compiled columns.  A failing
projection is skipped and its error logged. -/
def project (outs : List (String × DExpr)) (q : Query inS p) :
    Query inS (projectOut p (successes p outs)) :=
  match q with
  | { rel := r, errors := errs } =>
      let ps := compileProjections p outs
      { rel := Rel.project r ps.1 none, errors := ps.2 ++ errs }

/-- `sort keys` — order rows by column NAME + direction; names resolve
against the pipeline schema at step time (schema-preserving). -/
def sort (keys : List (String × Substrait.Proto.SortDirection)) (q : Query s s) : Query s s :=
  match q with
  | { rel := r, errors := errs } =>
      match keys.mapM (fun (name, dir) =>
        colOrdinal s name |>.map (fun ord => ({ col := { name := name, ordinal := ord }, direction := dir } : SortKey s))) with
      | .ok ks => { rel := Rel.sort r ks, errors := errs }
      | .error e => { rel := r, errors := e :: errs }

/-- `fetch limit offset` — apply limit/offset (schema-preserving; nothing to
validate). -/
def fetch (limit offset : Option Nat) (q : Query s s) : Query s s :=
  match q with
  | { rel := r, errors := errs } => { rel := Rel.fetch r limit offset, errors := errs }

/-- The validation log as `Except` (first error wins display order). -/
def checked (q : Query inS outS) : Except String (Rel inS outS) :=
  match q.errors with
  | [] => pure q.rel
  | es => throw (String.intercalate "; " es.reverse)

/-- Run the pipeline and report the rel, failing on the first logged error. -/
def toRel (q : Query inS outS) : Except String (Rel inS outS) :=
  checked q

end Query

end QLang
