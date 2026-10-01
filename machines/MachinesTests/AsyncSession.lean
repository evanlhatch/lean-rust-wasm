/-
# MachinesTests.AsyncSession — the async-lift session's pins + the mandatory controls

The D4 async-lift handshake (legacy/notes/wasm-backend-notes.md §
async-lift, as a session): both peers derived from the ONE declared
protocol (`Machines.AsyncSession.guestAsyncExport` /
`hostConcurrentCall` — the host's is the dual, never hand-written),
the duality checked (the involution + the wire laws), both canonical
tapes pinned COMPLETING, and the mis-shaped-export teeth pinned as
data (recv-first callee, handle-before-result, wrong value, the
`offender` diagnostic). The elaboration tooth is the peer-agreement
TYPE: a peer whose directions do not flip fails definitional equality.

Negative controls (15-patterns #5): the drifted dual, the mis-shaped
export accepted, the diagnostic blinded. Axiom self-check: `#print
axioms` over the cited laws (the core triple at most).
-/

import Machines
import TestingKit.Spec
import TestingKit.Harness

namespace MachinesTests.AsyncSession

open Machines TestingKit
open Machines.AsyncSession
open Machines.AsyncSession.AsyncWire
open Machines.Session

/-! ## The handshake fixture -/

/-- The guest peer's VALUE, pinned: send the flat result (the
    task-return face of the awaited `future<u64>`), then the task
    handle. -/
theorem guestAsyncExport_pin :
    guestAsyncExport
      = .send (taskReturn 42) (.send (taskHandle 0) .done) := rfl

/-- THE HOST PEER, pinned: receive the result, receive the handle —
    the dual, derived definitionally. -/
theorem hostConcurrentCall_pin :
    hostConcurrentCall
      = .recv (taskReturn 42) (.recv (taskHandle 0) .done) := rfl

/-- THE DUALITY LAWS, cited at the handshake. -/
theorem duality_laws :
    Session.dual (Session.dual guestAsyncExport) = guestAsyncExport
      ∧ Session.msgs (Session.dual guestAsyncExport) = Session.msgs guestAsyncExport :=
  ⟨Session.dual_dual guestAsyncExport, Session.msgs_dual guestAsyncExport⟩

/-- Peer agreement as a TYPE, inhabited definitionally. -/
theorem peerAgreesAsync : IsDualOf hostConcurrentCall guestAsyncExport := ⟨rfl⟩

/- THE ELABORATION TOOTH: a hand-written peer whose directions do not
flip does NOT compile — the mismatched handshake fails definitional
equality at elaboration time. An `example` (never a named theorem): a
FAILED declaration commits with `sorryAx` (Lean's error recovery) —
the tooth stays, no sorry lands. (Block comment, not a docstring: a
docstring here would attach to the #guard_msgs command — the
parse-error trap in its docstring form.) -/
/-- error: Application type mismatch: The argument
  rfl
has type
  ?m.10 = ?m.10
but is expected to have type
  recv (taskReturn 42) done = guestAsyncExport.dual
in the application
  { agrees := rfl } -/
#guard_msgs in
example : IsDualOf (.recv (taskReturn 42) .done) guestAsyncExport := ⟨rfl⟩

/-! ## The states, transitions, conformance -/

/-- The canonical tapes, pinned in values. -/
theorem follow_pins :
    follow guestAsyncExport = [.step .snd (taskReturn 42), .step .snd (taskHandle 0)]
      ∧ follow hostConcurrentCall
        = [.step .rcv (taskReturn 42), .step .rcv (taskHandle 0)] :=
  ⟨rfl, rfl⟩

/-- BOTH canonical tapes complete: the guest's export answers, the
    host's concurrent call awaits and resolves (the general law
    `follow_runs`, cited). -/
theorem conformance :
    sessionMachine.run guestAsyncExport (follow guestAsyncExport) = some .done
      ∧ sessionMachine.run hostConcurrentCall (follow hostConcurrentCall) = some .done :=
  ⟨guest_run_completes, host_run_completes⟩

/-- The transitions, pinned (the future resolves; the handle lands). -/
theorem transition_pins :
    sessionStep? sAwaitResult (.step .rcv (taskReturn 42)) = some sAwaitHandle
      ∧ sessionStep? sAwaitHandle (.step .rcv (taskHandle 0)) = some .done :=
  ⟨step_result, step_handle⟩

/-! ## The teeth: the mis-shaped async export refuses -/

/-- The refusal battery, pinned as data: the wrong-direction move, the
    handle-before-result reorder, the wrong VALUE on the wire (43
    where the protocol pins 42), and the terminal's silence. -/
theorem refusals :
    sessionStep? guestAsyncExport (.step .rcv (taskReturn 42)) = none
      ∧ sessionStep? sAwaitResult (.step .rcv (taskHandle 0)) = none
      ∧ sessionStep? sAwaitResult (.step .rcv (taskReturn 43)) = none
      ∧ sessionStep? .done (.step .rcv (taskReturn 42)) = none :=
  ⟨export_refuses_recv, host_refuses_handle_first,
   host_refuses_wrong_value 43 (by decide), done_terminal _⟩

/-- The diagnostic: the drifted value is refused at position 0, the
    move named. -/
theorem offender_pin :
    offender hostConcurrentCall [.step .rcv (taskReturn 43)]
      = some (0, .step .rcv (taskReturn 43)) := rfl

/-! ## The axiom self-check (this lane's own pins) -/

/-- info: 'Machines.AsyncSession.hostDualGuest' does not depend on any axioms -/
#guard_msgs in
#print axioms Machines.AsyncSession.hostDualGuest

/-- info: 'Machines.AsyncSession.guest_run_completes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.AsyncSession.guest_run_completes

/-- info: 'Machines.AsyncSession.host_run_completes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.AsyncSession.host_run_completes

/-- info: 'Machines.AsyncSession.host_refuses_wrong_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.AsyncSession.host_refuses_wrong_value

/-! ## The suite -/

def specAsyncSession : Spec := Spec.ofList "async-lift-session"
  (fun _ => do
    assert (guestAsyncExport == .send (taskReturn 42) (.send (taskHandle 0) .done))
      "guest export protocol wrong"
    assert (hostConcurrentCall == .recv (taskReturn 42) (.recv (taskHandle 0) .done))
      "host concurrent-call protocol wrong (not the derived dual)"
    assert (Session.dual (Session.dual guestAsyncExport) == guestAsyncExport)
      "involution broken"
    assert (Session.msgs (Session.dual guestAsyncExport) == Session.msgs guestAsyncExport)
      "wire law (payloads) broken"
    assert (sessionMachine.run guestAsyncExport (follow guestAsyncExport) == some .done)
      "guest tape refused"
    assert (sessionMachine.run hostConcurrentCall (follow hostConcurrentCall) == some .done)
      "host tape refused"
    assert (sessionStep? sAwaitResult (.step .rcv (taskReturn 42)) == some sAwaitHandle)
      "task-return transition wrong"
    assert (sessionStep? sAwaitResult (.step .rcv (taskReturn 43)) == none)
      "wrong-value future accepted"
    assert (sessionStep? sAwaitResult (.step .rcv (taskHandle 0)) == none)
      "handle-before-result accepted"
    assert (sessionStep? guestAsyncExport (.step .rcv (taskReturn 42)) == none)
      "recv-first callee accepted")
  [ ("sabotage-dual-drifted", fun _ =>
      assert (hostConcurrentCall == .send (taskReturn 42) .done) "control"),
    ("sabotage-mis-shape-accepted", fun _ =>
      assert (sessionStep? sAwaitResult (.step .rcv (taskReturn 43))
        == some sAwaitHandle) "control"),
    ("sabotage-diagnostic-blinded", fun _ =>
      assert (offender hostConcurrentCall [.step .rcv (taskReturn 43)] == none)
        "control") ]
  1 49

/-! ## The stream's unbounded production: the coinductive face -/

def specAsyncStreamInf : Spec := Spec.ofList "stream-unbounded-production"
  (fun _ => do
    -- the producer's unbounded production, as data: 0, 1, 2, 3
    assert (List.map (producerCoal.states insPoll 0) [0, 1, 2, 3]
        == [0, 1, 2, 3]) "producer states wrong"
    -- the consumer's progress: every poll answered (all `some`)
    assert ((producerCoal.beh insPoll 0 0).isSome
        && (producerCoal.beh insPoll 0 3).isSome) "consumer progress wrong")
  [ ("sabotage-producer-blocks", fun _ =>
      -- the poll NEVER refuses — the unbounded production is the point
      assert (List.map (producerCoal.states insPoll 0) [0, 1] == [0, 0])
        "control"),
    ("sabotage-handshake-forever", fun _ =>
      -- the bounded handshake is NOT the unbounded face: the repeated
      -- task-return dies after one exchange (the protocol is finite)
      assert (sessionMachine.run guestAsyncExport
          (List.replicate 4 (.step .snd (taskReturn 42))) == some .done)
        "control") ]
  1 50

/-! ### The census: the stream-face theorems, cited -/

example : InfRun streamProducer insPoll 0 := infRun_producer
example : Fairness producerCoal insPoll 0 := fair_producer
example : InfRun streamProducer insPoll 0 := infRun_producer_of_fair
example : ∀ t, ∃ o, producerCoal.beh insPoll 0 t = some o :=
  consumer_progress
example : ¬ InfRun sessionMachine insRepeat guestAsyncExport :=
  noInfRun_bounded

/-! ### The axiom self-check -/

/-- info: 'Machines.AsyncSession.infRun_producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Machines.AsyncSession.infRun_producer

/-- info: 'Machines.AsyncSession.fair_producer' does not depend on any axioms -/
#guard_msgs in
#print axioms Machines.AsyncSession.fair_producer

/-- info: 'Machines.AsyncSession.noInfRun_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Machines.AsyncSession.noInfRun_bounded

end MachinesTests.AsyncSession
