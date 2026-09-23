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

Boundary note: `unsupported` is currently UNEMITTABLE — fast-observe's
`ErrorCategory` has no Unsupported variant and its `Policy` no degrade
action, so a spec carrying `.unsupported` would fail rustc in the
CONSUMER, not at generation. The registry therefore rejects it at
registration (`registerFaultItem`, named diagnostic). Mapping it to an
expressible category (e.g. `Content` = fix-the-caller's-input) changes
policy semantics and is a deliberate decision, not emitter default —
until that decision lands, the ctor stays taxonomic-only (no spec may
use it).

MODULE (W10.1): this file is a `module` now — the variant-projection
fold's consumer (`Demo.lean`, the schema authoring surface) is itself
a module, and the module system refuses `module ← non-module` imports.
Everything here is public + exposed: the plain-file importers
(`Faults.Spec.*`, `Faults.Emit.*`, the tests) consumed the transitive
visibility the plain file used to provide, so the imports stay
`public` and the decls stay exposed (the structure/ctor transparency
the spec literals and the `evalConst` registration path need).
-/

module

namespace Faults

@[expose] public section

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
public def Category.rustName : Category → String
  | .fatal => "Fatal"
  | .content => "Content"
  | .transient => "Transient"
  | .invariant => "Invariant"
  | .unsupported => "Unsupported"

end -- public section
end Faults
