/-
# LedgerFn — the guest implementation surface

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
-/

import CodegenCore.GuestGate
import SchemaLang.Meta.Reflect
import Ledger
import GuestlangStd.StrOps

namespace LedgerImpl

/-- The `ledger-get` implementation: none for the sentinel id, a real
    record otherwise (the GuestImpl pattern's minimal mirror). -/
@[guest_std, schema_fn]
def ledger_get (id : UInt64) : Option Ledger :=
  if id == 0 then none
  else some { id := id, label := "ledger", balance := 0, owner := "ledger-owner" }

/-- The `ledger-valid` validator: id ≠ 0 ∧ label nonempty. The hand-body
    (the VExpr's strlen-node = honestly skipped — see schema-lang's
    Validate.lean header); the duel = the authority. -/
@[guest_std, schema_fn]
def ledger_valid (a : Ledger) : Bool :=
  a.id > 0 && GuestlangStd.strlen a.label > 0

/-- The `deposit` implementation: the wrapping add (UInt64). -/
@[guest_std, schema_fn]
def deposit (balance amount : UInt64) : UInt64 :=
  balance + amount

end LedgerImpl
