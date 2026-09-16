/-
# CodegenCore.CodedRegistry — a DataRegistry with position-derived codes (W7.4)

The CodedItem mixin: `DataRegistry` (name uniqueness IN THE TYPE) plus a
code space (`codePrefix`, `start`) whose codes come from
`CodegenCore.allocateCodes` over the items. Code collision-freedom is a
proof field with a `by decide` default, exactly like `nodup` — a coded
registry literal with colliding codes fails to ELABORATE; there is no
runtime rejection path because there is no illegal state.

Deliberately NO `insert`: codes are position-derived, so a mid-list
insertion would reallocate every later code. Coded registries grow by
append at the authoring layer (the attribute handlers append; the CI
byte-tie pins the emitted bytes).

First consumer: faults' E-code allocation (`E100 + position`).
-/

module

public import CodegenCore.DataRegistry
public import CodegenCore.Registry

@[expose] public section

namespace CodegenCore

/-- A named registry with allocated codes: name uniqueness from
    `DataRegistry.nodup`, code collision-freedom from `codesNodup` —
    both proof fields defaulted to `by decide`, so a concrete literal
    carries both invariants BY CONSTRUCTION. -/
structure CodedRegistry (α : Type) extends DataRegistry α where
  /-- The code prefix (`"E"` for failure modes). -/
  codePrefix : String
  /-- The first code's number; code of item `i` is `s!"{codePrefix}{start + i}"`. -/
  start : Nat
  /-- The allocated codes are distinct. Default discharged by `decide`
      over the concrete items; override with an explicit proof for
      non-concrete item lists. -/
  codesNodup : ((allocateCodes codePrefix start items).map (·.2)).Nodup := by decide

namespace CodedRegistry

/-- The allocated (item, code) pairs, in registration order. -/
def codes (reg : CodedRegistry α) : List (α × String) :=
  allocateCodes reg.codePrefix reg.start reg.items

/-- Code allocation preserves count — one code per item, always. -/
theorem codes_length (reg : CodedRegistry α) :
    reg.codes.length = reg.items.length :=
  allocateCodes_length reg.codePrefix reg.start reg.items

/-- Collision-freedom transported to `codes` (definitionally the raw
    allocation the proof field quantifies over). -/
theorem codes_nodup (reg : CodedRegistry α) :
    (reg.codes.map (·.2)).Nodup :=
  reg.codesNodup

end CodedRegistry

end CodegenCore
