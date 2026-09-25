/-
# Faults.Item — the failure-mode item's pure data surface

The faults lane's item (notes/v3/05-codegen.md §4 + notes/v3/12-construction.md
§8), mined from `legacy/lean/faults/Faults/{Item,Category}.lean` — the shape
ported, the allocation discipline REPLACED (the honest upgrade the v3 doctrine
demands): the legacy derived codes from registry POSITION
(`CodedRegistry.start`); here a fault's E-code ALLOCATES from the PERSISTED
registry (`Kit.CodeRegistry` — notes/code-registry.txt, the spec of record;
stable allocation, never position/import-derived). The item itself carries NO
code field — a hand-set code is unrepresentable where honest; the allocation
lives in `Faults.Alloc`, keyed by the fault's stable NAME.

- `name`     — registry identifier (mangled to the Rust variant by `Kit.pascal`)
- `display`  — the `#[error("…")]` message (may interpolate payload fields,
               thiserror's format syntax)
- `category` — the policy axis (`Faults.Category`)
- `advice`   — the fix, in domain vocabulary
- `payload`  — structured fields, typed by SchemaCore's CLOSED `Ty`
               (schemacore is the type authority, READ-ONLY here — no second
               universe; rendering routes through the ONE fold,
               `SchemaCore.tyRustPrim`)

Named exclusion (the leftover rule): the legacy's `.unsupported` category
does NOT port — its only role was the registration-time refusal (fast-observe
has no Unsupported variant), and this tree has no fast-observe consumer; the
honest size is the four expressible ctors. It returns with the fast-observe
integration (the named follow-up).

The slice's `Ty` is first-order (no named references), so the legacy's
`wellFormed`/`diagnose` resolution lane has no consumer here — the payload
types are total by construction. The lane's negative controls live at the
REGISTRATION (Kit.Lane's duplicate refusal) and the ALLOCATION (Faults.Alloc).

Core-only content (imports SchemaCore's closed universe — the cone rule).
Five questions (notes/v3/01-core.md):
- root: Universe — the fault rows as finite, name-keyed spec data.
- carrier grade: first-order over String/Category/List (String × Ty).
- spine reading: Registry (Faults.Registry's mount) → Interpretation
  (Faults.Emit's rendering) — the item is the spec half.
- ladder rung: rung 1 — plain data, every checkable fact a `decide`.
- gate row: FaultsTests (the pins + the mandatory negative controls).
-/

import SchemaCore.Ty

namespace Faults

open SchemaCore (Ty)

/-! ## the category — the policy axis -/

/-- The error taxonomy's policy axis (the legacy's observability rules as
    data): `fatal` poisons the world; `content` = fix the input, retrying
    unchanged fails; `transient` = retry with backoff; `invariant` = engine
    bug, never retry. The policy is DATA here and a METHOD in the generated
    Rust (`retryable()`), the display attribute driven from the same value —
    renderings, one source. -/
inductive Category where
  | fatal
  | content
  | transient
  | invariant
deriving Repr, BEq, DecidableEq, Inhabited

/-- The retry policy: `transient` is the ONLY retryable category — a
    `content` error means unchanged input fails again, and an `invariant`
    error means the engine is wrong. -/
def Category.retryable : Category → Bool
  | .transient => true
  | _ => false

/-- The Rust spelling (the generated `ErrorCategory` variant's name). -/
def Category.rustName : Category → String
  | .fatal => "Fatal"
  | .content => "Content"
  | .transient => "Transient"
  | .invariant => "Invariant"

/-! ## the item -/

/-- A failure mode: spec data. NO code field — the E-code allocates from the
    persisted registry at the allocation step (`Faults.Alloc`), keyed by the
    fault's name; a hand-set code is unrepresentable where honest. -/
structure FaultItem where
  /-- Registry identifier (unique — Kit.Lane's mount refuses duplicates). -/
  name : String
  /-- The `#[error("…")]` message (may interpolate payload field names). -/
  display : String
  /-- The policy axis. -/
  category : Category
  /-- The fix, in domain vocabulary (the generated `advice()`). -/
  advice : String
  /-- Structured fields, typed by the CLOSED `Ty` (schemacore's universe —
      no second type authority). -/
  payload : List (String × Ty)
deriving Repr, BEq, Inhabited

end Faults
