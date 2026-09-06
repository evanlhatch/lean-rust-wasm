/-
# Faults.Category — the error taxonomy's policy axis

Lifted from flatland's `Codegen.Registry.Category` (SPEC/TOOLKIT §11.1
doctrine: the failure-mode registry is the ONE code allocator across the
stack — an E-code means the same thing in an elaboration error and in a
production trace).

Semantics (flatland's observability rules as a type):
- `fatal`      — poisons the world; abort the process
- `content`    — user bug; fix the input, retrying unchanged will fail
- `transient`  — retry with backoff; unchanged input may succeed
- `invariant`  — engine bug; file a bug, never retry
- `unsupported`— feature/capability missing; degrade or fail fast

The policy is DATA here and a method in the generated Rust
(`retryable()`), with fast-observe's `category` attribute driven from
the same value — three renderings, one source.
-/

namespace Faults

inductive Category where
  | fatal | content | transient | invariant | unsupported
deriving Repr, BEq, DecidableEq, Inhabited

/-- The retry policy. `transient` is the ONLY retryable category —
    a `content` error means unchanged input will fail again, and an
    `invariant` error means the engine is wrong. -/
def Category.retryable : Category → Bool
  | .transient => true
  | _ => false

/-- The fast-observe attribute identifier (PascalCase). -/
def Category.rustName : Category → String
  | .fatal => "Fatal"
  | .content => "Content"
  | .transient => "Transient"
  | .invariant => "Invariant"
  | .unsupported => "Unsupported"

end Faults
