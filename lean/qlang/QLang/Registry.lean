/-
# QLang.Registry

The table registry for the dynamic surface. Ported from the flatland
lineage's `FlatlandDsl.Schema` (trimmed to what a query language needs —
no emit-mapping helpers, no `columnIndex`/`nameAt`: ordinals are resolved
inside `QLang.DExpr.compileCol`).

Column *names* resolve to *positional ordinals* (the Substrait `$n` field
references) at compile time; resolution failure is an `Except String` —
never a panic.
-/
import Substrait.Typed
import QLang.Error

namespace QLang

open Substrait.Typed

/-- A table's schema: table name + ordered columns. -/
structure TableSchema where
  name : String
  schema : Schema
deriving Repr, BEq, Inhabited

/-- `tableS "units" [("health", .i32, true), ...]` — a table-schema literal. -/
def tableS (name : String) (schema : Schema) : TableSchema :=
  { name := name, schema := schema }

/-- The table registry: `name → TableSchema`. -/
structure Registry where
  tables : List TableSchema
deriving Repr, BEq, Inhabited

namespace Registry

/-- The empty registry. -/
def empty : Registry := { tables := [] }

/-- Convenience: build a registry from a list of tables. -/
def ofTables (tables : List TableSchema) : Registry := { tables := tables }

/-- Add (or shadow) a table. -/
def add (r : Registry) (t : TableSchema) : Registry :=
  { r with tables := t :: r.tables }

/-- Look up a table by name.  Unknown table → `Except String` with the
    valid space enumerated + did-you-mean. -/
def find (r : Registry) (name : String) : Except String TableSchema :=
  match r.tables.find? (fun t => t.name == name) with
  | some t => pure t
  | none =>
      let known := r.tables.map (fun t => t.name)
      throw (QLangError.unknownTableMsg name known)

/-- The schema of a table (an `Except` since the table itself may be unknown). -/
def schema (r : Registry) (name : String) : Except String Schema := do
  let t ← r.find name
  pure t.schema

end Registry

end QLang
