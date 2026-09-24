/-
# SchemaCore.RowVals — the row layer: positional values + the name↔index iso

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/02-data-plane.md §1-3 (records are row
TYPES; the row is the runtime half of a record, indexed BY its schema —
a row for `["id","name"]` cannot hold the values of `["name","id"]`).

Provenance (mined, ported at slice size):
- `RowVals : List Field → Type` + `RowVals.project?` — from legacy
  `SchemaLang/Validate.lean` (the value-aligned row) and legacy
  `SchemaLang/Keys.lean` (the name-keyed projection, FIRST match wins).
- the name↔index correspondence `fieldIndexIso` — from legacy
  `CodegenCore/Kit.lean`'s `nodupNamesIso` (piece 4 of the W-iso batch):
  for a NODUP name list, `Fin n` is Iso the name subtype — position
  ↦ name, name ↦ its unique position. Keys are determinacy theorems
  (02 §3): the nodup hypothesis is what makes the position map
  injective; the iso STATES what a name-keyed walk DOES.

Deliberately OUT (no consumer yet — the leftover rule): the
`RowVals.cast` kit (its consumers are the existential wrappers of the
update/invariant lanes — none landed); the generated per-record bridge
harness (GenKit does not exist; the discipline is demonstrated on the
slice fixture in SchemaTests — the `@[row_bridge]` shape: `toRow`/
`ofRow` + both round-trip laws + the ONE `Kit.Iso`).

The five questions: root = Universe (data — the row carrier over the
field list); carrier = the GADT index (wrong-shape rows
unconstructible — the correspondence choice: a TRUE `Iso`, not a
partial one, because the domain already IS the well-formed rows);
spine reading = the record↔row crossing is a graded correspondence
(01 §4's Iso row); ladder rung = the projections/laws are structural
(`rfl`-reducible, kernel-visible); gate row = the axiom report +
SchemaTests' round-trip pins + negative controls.

Core-only (imports SchemaCore.Item + SchemaCore.Value — the cone rule).
-/

import SchemaCore.Item
import SchemaCore.Value

namespace SchemaCore

/-! ## The value-aligned row -/

/-- One `Value` per field of the schema, in schema order — the runtime
    half of a record, indexed BY the field list. -/
inductive RowVals : List Field → Type where
  | nil : RowVals []
  | cons : {f : Field} → {fs : List Field} → Value f.ty → RowVals fs →
      RowVals (f :: fs)

/-- A projected field value: the type index + the payload (the
    DATA-level twin of a typed path — registry rows are data; the
    existential is what a name-keyed walk returns). -/
structure FieldVal where
  ty : Ty
  val : Value ty

/-- The name-keyed field projection over a schema-aligned row (FIRST
    match wins — the legacy projection's reading). -/
def RowVals.project? : (fs : List Field) → RowVals fs → (n : String) →
    Option FieldVal
  | [], .nil, _ => none
  | f :: _, .cons v vs, n =>
      if f.name == n then some { ty := f.ty, val := v }
      else RowVals.project? _ vs n

/-- The projection's coverage pins (first-match + miss). -/
example : RowVals.project?
    [{ name := "a", ty := .u64 }, { name := "b", ty := .string }]
    (.cons (.u64 1) (.cons (.string "x") .nil)) "b"
    = some { ty := .string, val := .string "x" } := rfl
example : RowVals.project?
    [{ name := "a", ty := .u64 }]
    (.cons (.u64 1) .nil) "missing" = none := rfl

/-! ## The name↔index correspondence -/

/-- The name↔index iso: for a NODUP name list, the position and the
    name subtype are isomorphic — position i ↦ name i, name ↦ its
    unique position (mined: `CodegenCore.nodupNamesIso`). The nodup
    hypothesis is the DETERMINACY content (02 §3): without it the
    inverse is not a function. -/
def fieldIndexIso {names : List String} (hnd : names.Nodup) :
    Kit.Iso (Fin names.length) {n : String // n ∈ names} where
  to i := ⟨names[i.1]'i.2, List.getElem_mem i.2⟩
  inv n := ⟨names.idxOf n.1, List.idxOf_lt_length_of_mem n.2⟩
  to_inv n := Subtype.ext (List.getElem_idxOf (List.idxOf_lt_length_of_mem n.2))
  inv_to i := Fin.ext (by
    have hj := List.getElem_idxOf (List.idxOf_lt_length_of_mem
      (List.getElem_mem i.2))
    exact (List.getElem_inj hnd).mp hj)

end SchemaCore
