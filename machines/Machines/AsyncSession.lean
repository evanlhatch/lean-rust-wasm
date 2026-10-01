/-
# Machines.AsyncSession — the WASI async-lift protocol AS a session (D4's named remainder)

Owned by: the sessions/boundary lane (`machines/`). Driving decisions:
notes/v3/08-capabilities.md §9 (protocols as dual-checked sessions) +
the legacy async-lift recipe (legacy/notes/wasm-backend-notes.md §
async-lift — the wit-bindgen 0.61 protocol dissected from wasmparser's
`check_asyncness`). What D2 landed in `wit/` is the TY-LEVEL
`stream<T>`/`future<T>` rows (`Wit.Render.ty_future`) — the FUNC-level
async row (`Wit.Func.async`) is D2's named remainder, so the WIT-side
session bridge (`Wit.Session`, named in `Wit.Compose`) stays named;
THIS module is the protocol's honest content on the Machines side: the
async-lift handshake declared ONCE as a session, both peers derived
from it, the duality checked — the runtime lane in
`mandate-host::wasi_async` enforces the same shape guest-side/Rust-side
(the fixture's callee delivers results by calling task-return then
returning the task handle — the recipe's (d)).

## What lands (the honest minimal)

- `AsyncWire` — the handshake's payload universe, instantiated from the
  recipe: `taskReturn v` (the flat result the callee delivers through
  its `[task-return]<fn>` import — the runtime face of the D2
  `future<u64>` row: the value the host AWAITS) + `taskHandle t` (the
  handle the lifted core body returns — 0 = sync-computable, done at
  the first poll).
- `guestAsyncExport` — the callee's protocol: SEND the flat result
  (task-return), then SEND the task handle, done. The states/transitions
  are the landed session machine's suffixes (named below).
- `hostConcurrentCall` — the host's protocol, DERIVED (the dual, never
  hand-written): receive the result, receive the handle. The guest's
  async export IS the host's concurrent-call dual — the recipe's two
  faces of one handshake, declared once.
- The duality check: the definitional `dual` pins + the `IsDualOf`
  instance (peer agreement as a TYPE — a hand-written peer whose
  directions do not flip fails definitional equality at elaboration).
- The teeth: a mis-shaped async export refuses — a callee that WAITS
  first (recv-first), a handle before the result, a wrong-direction
  move, a wrong VALUE on the wire (the future resolved to a different
  number), an over-talking peer at `done`. Every refusal is data
  (`sessionStep? = none`, the `offender` diagnostic names position +
  move).

The runtime face (`mandate-host::wasi_async`): the fixture component
exports `f : async func() -> u64` — the canonical-async lift, the
value crossing through task-return. That lane is the ENFORCEMENT face
of this protocol; the two land together (the same named remainder).

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Machines.Basic
import Machines.Session
import LintKit.Basic

namespace Machines.AsyncSession

open Machines.Session

/-! ## The async-lift wire payload universe -/

/-- One wire message of the async-lift handshake. The universe is
    CLOSED: a new message kind is a protocol act here, not a flag. -/
inductive AsyncWire where
  /-- The flat result the CALLEE delivers through its
      `[task-return]<fn>` import — the recipe's (d); the runtime face
      of the D2 `future<u64>` row (the value the host awaits). -/
  | taskReturn (v : Nat)
  /-- The task handle the lifted core body returns (`i32` flat; 0 =
      sync-computable — done at the first poll, the recipe's
      sync-computable-body discipline). -/
  | taskHandle (t : Nat)
deriving DecidableEq, Repr, BEq

open AsyncWire

/-! ## The two peers: the guest's async export, the host's concurrent call -/

/-- THE GUEST'S ASYNC EXPORT (the callee's pen): deliver the flat
    result through task-return, then return the task handle, done. -/
def guestAsyncExport : Session AsyncWire :=
  .send (taskReturn 42) (.send (taskHandle 0) .done)

/-- THE HOST'S CONCURRENT CALL (derived, never hand-written): receive
    the result, receive the handle. The dual of the guest's export —
    the recipe's two faces of ONE handshake. -/
def hostConcurrentCall : Session AsyncWire := Session.dual guestAsyncExport

/-- THE DUALITY CHECK (definitional): the host's concurrent call is
    exactly receive-result-then-receive-handle. -/
theorem hostDualGuest :
    hostConcurrentCall
      = .recv (taskReturn 42) (.recv (taskHandle 0) .done) := rfl

/-- The duality round trip at the handshake (the involution, cited). -/
theorem dualGuestHost :
    Session.dual guestAsyncExport = hostConcurrentCall := rfl

/-- Peer agreement as a TYPE: the host's concurrent call inhabits the
    dual-of relation over the guest's export, by construction. A
    hand-written peer that disagrees fails definitional equality at
    ELABORATION time (the mismatched handshake does not compile). -/
instance instHostDualGuest :
    Session.IsDualOf hostConcurrentCall guestAsyncExport := ⟨rfl⟩

/-- THE WIRE LAW (payloads): dual peers exchange the SAME values in
    the same order — pinned at the handshake. -/
theorem msgs_wire :
    Session.msgs hostConcurrentCall = [taskReturn 42, taskHandle 0] := rfl

/-- THE WIRE LAW (directions): the peers oppose pointwise (the general
    law `dirs_dual`, cited). -/
theorem dirs_wire :
    Session.dirs hostConcurrentCall
      = (Session.dirs guestAsyncExport).map Dir.flip :=
  Session.dirs_dual guestAsyncExport

/-! ## The session's states + transitions (the host's view) -/

/-- State 1: the call is outstanding — the host awaits the task-return. -/
def sAwaitResult : Session AsyncWire := hostConcurrentCall

/-- State 2: the result delivered — the host awaits the task handle. -/
def sAwaitHandle : Session AsyncWire := .recv (taskHandle 0) .done

/-- Transition 1: the future resolves — task-return delivers 42. -/
theorem step_result :
    sessionStep? sAwaitResult (.step .rcv (taskReturn 42)) = some sAwaitHandle := rfl

/-- Transition 2: the lifted body returns its handle (0 = done at the
    first poll) — the handshake completes. -/
theorem step_handle :
    sessionStep? sAwaitHandle (.step .rcv (taskHandle 0)) = some .done := rfl

/-- Terminal: `done` refuses every move (the general law, cited). -/
theorem done_terminal (mv : Session.Move AsyncWire) :
    sessionStep? (P := AsyncWire) .done mv = none := Session.doneRefused mv

/-! ## The conformance: both peers complete the handshake -/

/-- The guest's canonical tape runs its export protocol to `done` (the
    general law `follow_runs`, cited). -/
theorem guest_run_completes :
    sessionMachine.run guestAsyncExport (follow guestAsyncExport) = some .done :=
  Session.follow_runs guestAsyncExport

/-- The host's canonical tape runs its concurrent-call protocol to
    `done` — the awaited call completes. -/
theorem host_run_completes :
    sessionMachine.run hostConcurrentCall (follow hostConcurrentCall) = some .done :=
  Session.follow_runs hostConcurrentCall

/-! ## The teeth: the mis-shaped async export refuses -/

/-- A callee that WAITS first (a recv-rooted protocol) is not an async
    lift — the guest's export protocol refuses the receive move (the
    direction is the guest's to send). -/
theorem export_refuses_recv :
    sessionStep? guestAsyncExport (.step .rcv (taskReturn 42)) = none := rfl

/-- THE HOST refuses a handle before the result — the wire order is
    the protocol's (task-return precedes the return). -/
theorem host_refuses_handle_first :
    sessionStep? sAwaitResult (.step .rcv (taskHandle 0)) = none := rfl

/-- THE WIRE IS TYPED: a future that resolves to a DIFFERENT value is
    refused — the handshake's payload equality is checked. -/
theorem host_refuses_wrong_value (v : Nat) (h : ¬ v = 42) :
    sessionStep? sAwaitResult (.step .rcv (taskReturn v)) = none := by
  show sessionStep? (.recv (taskReturn 42) (.recv (taskHandle 0) .done))
      (.step .rcv (taskReturn v)) = none
  simp only [sessionStep?]
  split
  · rename_i heq
    simp only [AsyncWire.taskReturn.injEq] at heq
    omega
  · rfl

/-- THE MIS-SHAPED EXPORT, as a peer: a recv-first "async export" run
    against the GUEST tape (the callee's own expected moves) refuses —
    the shape of the protocol, not just one move, is the contract. -/
theorem misShaped_refused (misShaped : Session AsyncWire)
    (h : misShaped = .recv (taskReturn 42) .done) :
    sessionMachine.run misShaped (follow guestAsyncExport) = none := by
  rw [h]
  rfl

/-- THE NAMED DIAGNOSTIC: a drifted value (43 where the protocol pins
    42) is refused at position 0 with the offending move named. -/
theorem offender_drift :
    Session.offender hostConcurrentCall [.step .rcv (taskReturn 43)]
      = some (0, .step .rcv (taskReturn 43)) := rfl

end Machines.AsyncSession
