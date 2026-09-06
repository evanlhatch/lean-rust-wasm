/-
# Faults.Registry — the failure-mode registry (the one code allocator)

Lifted from flatland's `Codegen.Registry.FailureModeItem` and COMPLETED:
flatland's registry had no emitter (the fast-observe integration was
designed in TOOLKIT §11.1, never built). This package is that emitter.

Item shape (flatland base + the fields the emission contract requires):
- `name`     — registry identifier, mangled to the Rust variant
- `display`  — the `#[error("…")]` message (may interpolate payload
               fields, fast-observe format syntax)
- `category` — policy axis (see `Faults.Category`)
- `advice`   — the `#[advice]` attribute; the fix, in domain vocabulary
- `payload`  — structured fields, typed by the SCHEMA language's `Ty`
               (schema-lang is the type authority; no second universe)

Codes are NEVER hand-set: `allocate` derives them from registry position
via `CodegenCore.allocateCodes` — collision-free by construction, and
the proof obligation (count preservation) is checked in the kernel.

wellFormed: payload types resolve against the schema universe's type
names, names unique (Nodup).
-/

import CodegenCore
import SchemaLang
import Faults.Category

namespace Faults

open SchemaLang (Ty)

/-- A failure mode: spec data. -/
structure FailureModeItem where
  name : String
  display : String
  category : Category
  advice : String
  payload : List (String × Ty)
deriving Repr, BEq, Inhabited

/-- Payload type references resolve against `known` (the schema
    universe's type names; scalars need no universe). -/
def FailureModeItem.wellFormed (known : List String) (m : FailureModeItem) : Bool :=
  m.payload.all (fun (_, t) => t.wellFormed known)

/-- Failure-mode names are unique. -/
def namesUnique (items : List FailureModeItem) : Bool :=
  (items.map (·.name)).Nodup

/-- The universe check: every mode well formed, names unique. -/
def universeWellFormed (known : List String) (items : List FailureModeItem) : Bool :=
  items.all (fun m => m.wellFormed known) && namesUnique items

/-- Code allocation: `"E{n}"` from registry position, start 100.
    Append-only registry ⇒ stable codes (CI byte-tie enforces). -/
def allocate (items : List FailureModeItem) : List (FailureModeItem × String) :=
  CodegenCore.allocateCodes "E" 100 items

/-- Code allocation preserves count — kernel-checked obligation. -/
theorem allocate_length (items : List FailureModeItem) :
    (allocate items).length = items.length :=
  CodegenCore.allocateCodes_length "E" 100 items

end Faults
