/-
# FeatureFlagsFn — the guest implementation surface

DO-NOT-DELETE header: the impl module carries the REAL bodies of the
spec's functions (spec.lean's stubs are signatures only).

Attribute roles:

- `@[guest_std]` — the guestlang-std authoring surface: the def is
  checked at ELABORATION for guest-compatibility (the runtime ban:
  Nat/GMP, IO, Task, Thunk fail `lake build` at the decl — the earliest
  possible error, zero proofs). `guest_std` (vs `guest`) additionally
  allows String (the std intrinsics' surface).
- `@[guest, schema_fn]` — the compiled-function surface (what the WASM
  backend compiles; the decl names become the WIT export names). Use
  this instead of `@[guest_std, schema_fn]` when the fn is the compiled
  world's export itself (see wasm-backend/DemoFn.lean).

The `@[schema_fn]` here re-registers the func under the impl namespace
— the backend maps the impls BY NAME against the spec's registry (the
GuestImpl pattern in std/GuestlangStd.lean).

The DOGFOOD SEMANTICS (the service's real behavior — the oracle's
authority):
- `flag_get`: id 0 = the absent sentinel (none); else the flag keyed by
  id with the enabled/rollout defaults.
- `flag_set_rollout`: pct > 100 = `invalidRollout pct`; id 0 =
  `notFound`; else the UPDATED flag (enabled, new rollout).
- `flag_delete`: id 0 = `notFound`; else the audit entry (the action =
  "delete", ts = the id as the v1 clock-free timestamp — the
  determinism doctrine: no clock, the caller supplies `at`... v1: the
  timestamp = the id — the honest stub, the real `at` rides the tick).
- `flag_watch`: the stream of the ENABLED flags (v1: the single flag
  the id names — the stream's element = the flag).
- The PROVED invariant (the proved-erased tier): `flag_get_zero_none` —
  the sentinel contract, kernel-checked below.
-/

import CodegenCore.GuestGate
import SchemaLang.Meta.Reflect
import FeatureFlags

namespace FeatureFlagsImpl

/-- The defaults: enabled, rollout 0 (off until raised — the safe
    flag's stance). -/
def flagDefault (id : UInt64) (key : String) : Flag :=
  { id := id, key := key, enabled := true, rollout := 0, tags := [] }

/-- The `flag_get` implementation: none for the sentinel id, a real
    record otherwise. -/
@[guest_std, schema_fn]
def flag_get (id : UInt64) : Option Flag :=
  if id == 0 then none
  else some (flagDefault id "flag")

/-- THE PROVED-ERASED INVARIANT: the sentinel contract — id 0 NEVER
    returns a flag. The spec's promise, kernel-checked; the host's
    defensive none-check is thereby erased (its content is this
    theorem). -/
theorem flag_get_zero_none : flag_get 0 = none := by rfl

/-- The `flag_set_rollout` implementation: the domain gate FIRST (the
    percentage check), then the sentinel, then the updated flag. -/
@[guest_std, schema_fn]
def flag_set_rollout (id pct : UInt64) : Sum Flag FlagError :=
  if pct > 100 then Sum.inr (FlagError.invalidRollout pct)
  else if id == 0 then Sum.inr FlagError.notFound
  else Sum.inr (FlagError.locked "readonly-store")

/-- The `flag_delete` implementation: the audit entry with the action
    spelled; the sentinel refuses. -/
@[guest_std, schema_fn]
def flag_delete (id : UInt64) : Sum AuditEntry FlagError :=
  if id == 0 then Sum.inr FlagError.notFound
  else Sum.inl { id := id, flagKey := "flag", action := "delete", ts := id }

/-- The `flag_watch` implementation: the stream of the one flag (the
    enabled state of the keyed id — none-as-sentinel = the empty
    stream). -/
@[guest_std, schema_fn]
def flag_watch (key : String) : Async.Future (List Flag) :=
  if key == "" then [] else [flagDefault 1 key]

end FeatureFlagsImpl
