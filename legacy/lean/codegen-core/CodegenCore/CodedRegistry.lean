/-
# CodegenCore.CodedRegistry — a DataRegistry with position-derived codes

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
public import CodegenCore.Kit

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

/-! ## The denseness upgrade (W-iso batch: positions ARE the items)

`allocateCodes` is position-derived — code `i` IS `s!"{codePrefix}{start + i}"`,
so the code space is DENSE (exactly `start … start + n - 1`, no gaps, no
hand-set codes) by construction. `denseCheck` is the executable check
that survives any hand-set-code regression (a concrete registry decides
it; first consumer: faults' `allocationChecks`). Under denseness the
code space indexes the items: the correspondence below upgrades to
`Iso (Fin n) α` exactly when the registry EXHAUSTS `α` (the enum case —
`finIso`); for a non-exhaustive α the honest form is the member subtype
(`membersIso`). -/

/-- Position injectivity: the position of `items[i]` IS `i` — the
    name-map is nodup (`reg.nodup`), so two positions naming the same
    item are one position. -/
theorem idxOf_getElem_inj [BEq α] [LawfulBEq α] (reg : CodedRegistry α)
    (i : Fin reg.items.length) : reg.items.idxOf reg.items[i.1] = i.1 := by
  have hmem : reg.items[i.1] ∈ reg.items := List.getElem_mem i.2
  have hj := List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)
  have hlen₁ : reg.items.idxOf reg.items[i.1]
      < (reg.items.map reg.nameOf).length := by
    rw [List.length_map]
    exact List.idxOf_lt_length_of_mem hmem
  have hlen₂ : i.1 < (reg.items.map reg.nameOf).length := by
    rw [List.length_map]
    exact i.2
  have hmap? : (reg.items.map reg.nameOf)[reg.items.idxOf reg.items[i.1]]?
      = (reg.items.map reg.nameOf)[i.1]? := by
    rw [List.getElem?_map, List.getElem?_map,
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem),
      List.getElem?_eq_getElem i.2, hj]
  exact (List.getElem?_inj hlen₁ reg.nodup).mp hmap?

/-- The executable denseness check: every allocated code, stripped of
    the prefix, parses to exactly `start + position`. -/
def denseCheck (reg : CodedRegistry α) : Bool :=
  reg.codes.zipIdx.all fun c =>
    (c.1.2.drop reg.codePrefix.length).toNat? == some (reg.start + c.2)

/-- Denseness BY CONSTRUCTION, at the writer: the code allocated at
    position `i` IS the position-derived string `s!"{pre}{start + i}"`
    — there is no hand-set code to drift (the `allocateCodes` module
    header's discipline, as a theorem). The string-parse roundtrip that
    would lift this to a symbolic `denseCheck … = true` needs a decimal
    parse lemma development (`Slice.toNat?` over `Nat.repr` digits) the
    checker's concrete `decide` pins don't — `denseCheck` stays the
    executable regression net over concrete registries (the faults
    allocation checks), this lemma the production fact. -/
theorem allocateCodes_code_eq {α : Type} (pre : String) (start : Nat)
    (items : List α) (i : Nat) (h : i < items.length) :
    (allocateCodes pre start items)[i]'(by simp [allocateCodes]; exact h)
      = (items[i], s!"{pre}{start + i}") := by
  simp [allocateCodes, List.getElem_map, List.getElem_zipIdx]

/-- Positions ↔ members: name uniqueness makes the position map
    injective, membership total. The `[BEq α]` is for `idxOf` (the
    inverse's lookup). -/
def membersIso [BEq α] [LawfulBEq α] (reg : CodedRegistry α) :
    Iso (Fin reg.items.length) {a // a ∈ reg.items} where
  to i := ⟨reg.items[i.1]'i.2, List.getElem_mem i.2⟩
  inv a := ⟨reg.items.idxOf a.1, List.idxOf_lt_length_of_mem a.2⟩
  to_inv a := Subtype.ext (List.getElem_idxOf (List.idxOf_lt_length_of_mem a.2))
  inv_to i := Fin.ext (idxOf_getElem_inj reg i)

/-- The dense/exhaustive upgrade: when EVERY `a : α` is registered (the
    enum case), the position correspondence is total on α — an honest
    `Iso (Fin n) α` (the `List.Nodup.getEquivOfForallMemList` shape).
    Fires only when `α` is exhausted by the registry; for a non-enum α
    (e.g. faults' payload-carrying `FailureModeItem`) the honest form is
    `membersIso`. -/
def finIso [BEq α] [LawfulBEq α] (reg : CodedRegistry α)
    (hex : ∀ a : α, a ∈ reg.items) : Iso (Fin reg.items.length) α where
  to i := reg.items[i.1]'i.2
  inv a := ⟨reg.items.idxOf a, List.idxOf_lt_length_of_mem (hex a)⟩
  to_inv a := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hex a))
  inv_to i := Fin.ext (idxOf_getElem_inj reg i)

end CodedRegistry

end CodegenCore
