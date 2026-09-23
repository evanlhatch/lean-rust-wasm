/-
# Faults.Item — the failure-mode item's pure data surface

Split from `Faults.Registry` at W10.1 (the one-fault unification's
module conversion): `Faults.Registry` is a `module` now, and the
module system's phase rule forbids a same-module `meta` declaration
from accessing a same-module non-meta one. The registry's env
extensions + attribute/commands are meta (the `declare_registry_member`
pattern — RegisterKit); the item structure + its pure helpers + the
kernel-checked obligation theorems must stay NON-meta (the theorem
proofs unfold them; the kernel cannot see through `meta`). One module
each side of the phase line: this one is the non-meta data surface,
`Faults.Registry` the meta machinery. Cross-module access is the
module-legal shape (the RegisterKit precedent: `Item` lives in
schema-lang, the meta ext-initialize consumes its derived instances).

Item shape (flatland base + the fields the emission contract requires):
- `name`     — registry identifier, mangled to the Rust variant
- `display`  — the `#[error("…")]` message (may interpolate payload
               fields, fast-observe format syntax)
- `category` — policy axis (see `Faults.Category`)
- `advice`   — the `#[advice]` attribute; the fix, in domain vocabulary
- `payload`  — structured fields, typed by the SCHEMA language's `Ty`
               (schema-lang is the type authority; no second universe)

Codes are NEVER hand-set: they derive from registry position via
`CodegenCore.allocateCodes`, surfaced through `CodedRegistry.codes` —
name uniqueness AND code collision-freedom are proof fields with
`by decide` defaults (W7.4's CodedItem mixin), so an illegal registry
literal fails to ELABORATE; there is no runtime rejection path.
-/

module

-- NOTE (W10.1): the import cone stops at the schema-lang SUBMODULES —
-- never the `SchemaLang` root, whose cone reaches back to `Demo`
-- (`SchemaLang.Emit.Witness` reads the demo witness registry) — Demo
-- imports this module (the fold's elaboration-order constraint), and
-- the cycle would be a build error.
public import CodegenCore
public import CodegenCore.CodedRegistry
public import SchemaLang.Ty
public import SchemaLang.Item
public import SchemaLang.Wf
public import Faults.Category

namespace Faults

open SchemaLang (Ty)

@[expose] public section

/-- A failure mode: spec data. -/
structure FailureModeItem where
  name : String
  display : String
  category : Category
  advice : String
  payload : List (String × Ty)
deriving Repr, BEq, Inhabited

/-- Payload type references resolve against `known` (the schema
    universe's type names; scalars need no universe). Uses the diagnostic
    authority (`Ty.check`) — one resolver, shared with SchemaLang. -/
def FailureModeItem.wellFormed (known : List String) (m : FailureModeItem) : Bool :=
  m.payload.all (fun (_, t) => (t.check known).isEmpty)

/-- The registry's diagnostic authority (wellFormed is the Bool
    projection; this NAMES the failure). Rides `Ty.check` — the ONE
    resolver shared with SchemaLang — whose `unknownRef` render carries
    the closed-world suggestion (`CodegenCore.didYouMean`, moved here-
    adjacent so every error path reaches it core-only). -/
def FailureModeItem.diagnose (known : List String) (m : FailureModeItem) :
    List String :=
  m.payload.flatMap fun (fname, t) =>
    (t.check known).map fun d => s!"`{m.name}` payload `{fname}`: {d}"

/-- The faults-local bridge, composed (the `universeWellFormed_iff`
    family's transport — the Wf lane's `tyCheck_eq_nil_iff` applied
    pointwise over the payload): the Bool projection's `true` means
    every payload type's references resolve against `known`. -/
theorem FailureModeItem.wellFormed_iff {known : List String}
    (m : FailureModeItem) :
    m.wellFormed known = true ↔
      ∀ (f : String × Ty), f ∈ m.payload → SchemaLang.TyRefsOk known f.2 := by
  simp only [FailureModeItem.wellFormed, List.all_eq_true, List.isEmpty_iff,
    SchemaLang.tyCheck_eq_nil_iff]

/-- The universe check: every mode well formed. Name uniqueness is the
    `DataRegistry.nodup` proof field — subsumed by the framework (W7.4),
    no longer a Bool check here. -/
def universeWellFormed (known : List String)
    (reg : CodegenCore.DataRegistry FailureModeItem) : Bool :=
  reg.items.all (fun m => m.wellFormed known)

/-- Code allocation preserves count — the kernel-checked obligation,
    now the framework's theorem (`CodedRegistry.codes_length`). Kept
    under the stable name: the axiom gate prints it. -/
theorem allocate_length (reg : CodegenCore.CodedRegistry FailureModeItem) :
    reg.codes.length = reg.items.length :=
  reg.codes_length

end -- public section
end Faults
