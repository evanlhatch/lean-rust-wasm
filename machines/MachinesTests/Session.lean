/-
# MachinesTests.Session — the sessions lane's pins + the mandatory controls

The worked two-party protocol (08 §9's honest fixture): a
request/response exchange with a two-way choice at the end. Both peers
are PROJECTED from the one global protocol (never hand-written), the
duality is checked (the involution + the wire laws), a CONFORMING run
is pinned completing, and two VIOLATING runs (direction mismatch,
payload mismatch) are refused with the named diagnostic (`offender`:
WHICH move at WHICH position). The refinement (the delaying impl) is
cited, and its two faces are pinned in values.

Negative controls (15-patterns #5): the drifted dual, the violation
accepted, the diagnostic blinded — each sabotage the suite MUST catch.
The elaboration tooth is the peer-agreement-as-TYPE check: a
mismatched peer fails definitional equality at elaboration time.

Axiom self-check: the pins below (`#print axioms`) name the core
triple at most — the same discipline as MachinesTests.Axioms, kept in
this lane's own file.
-/

import Machines
import TestingKit.Spec
import TestingKit.Harness

open Machines Machines.Session TestingKit

/-! ## The worked two-party protocol -/

/-- The worked payload universe (the lane is generic; the fixture
    instantiates `P`). -/
inductive Pay where
  | req | ack | bye
deriving DecidableEq, Repr, BEq

open Pay

/-- The global protocol, from the CLIENT's pen: send a request, receive
    an acknowledgement, then EITHER send bye and end OR receive a second
    acknowledgement and end. Every grammar constructor exercised. -/
def gFix : Session Pay :=
  .send .req (.recv .ack (.choice (.send .bye .done) (.recv .ack .done)))

/-- The SERVER peer: PROJECTED from the global protocol (the duality
    discipline — declare once, both peers derived, never hand-written). -/
def serverFix : Session Pay := dual gFix

/-- The two VIOLATING tapes: a direction mismatch at the second move
    (the protocol expects the client to RECEIVE), and a payload
    mismatch (the protocol expects an acknowledgement, not a request). -/
def badDir : List (Session.Move Pay) :=
  [.step .snd .req, .step .snd .ack]

def badPay : List (Session.Move Pay) :=
  [.step .snd .req, .step .rcv .req]

/-! ## The duality + the projections (the laws, cited; the values, pinned) -/

/-- THE INVOLUTION at the fixture (the general law is
    `Session.dual_dual` — cited in the axiom pins below). -/
theorem dualDual_gFix : dual (dual gFix) = gFix := Session.dual_dual gFix

/-- The projected server's VALUE, pinned: every send became a receive of
    the same payload and vice versa; the choice dualized in place. -/
theorem serverFix_pin :
    serverFix = .recv .req (.send .ack (.choice (.recv .bye .done) (.send .ack .done))) := rfl

/-- The wire law at the fixture: the dual peers exchange the SAME
    payloads in the same order — pinned. -/
theorem msgs_gFix_pin : msgs gFix = [.req, .ack, .bye, .ack] := rfl

theorem msgsDual_gFix : msgs (dual gFix) = msgs gFix := msgs_dual gFix

/-- THE PROJECTION CORRECTNESS (the duality discipline's content): the
    projected peers are dual-compatible BY CONSTRUCTION — the theorem
    is definitional, so the choreography cannot drift from the wire. -/
theorem projDual_gFix : dual (projClient gFix) = projServer gFix := proj_dual gFix

/-- A projected server determines the global protocol (the involution's
    face at the projection). -/
theorem projServer_determined (g : Session Pay)
    (h : projServer g = projServer gFix) : g = gFix :=
  projServer_inj h

/-- Peer agreement as a TYPE: the projected peer inhabits `IsDualOf`
    definitionally (the only witness is the generic instance). -/
theorem peerAgrees : IsDualOf serverFix gFix := ⟨rfl⟩

/- THE ELABORATION TOOTH: a hand-written peer whose direction does not
    flip does NOT compile — the mismatched conversation fails
    definitional equality at elaboration time. An `example` (never a
    named theorem): a FAILED declaration commits with `sorryAx` (Lean's
    error recovery) — the tooth stays, no sorry lands. (Block comment:
    a docstring here would attach to the #guard_msgs command, not the
    theorem — the parse-error trap in its docstring form.) -/
/-- error: Application type mismatch: The argument
  rfl
has type
  ?m.9 = ?m.9
but is expected to have type
  send bye done = gFix.dual
in the application
  { agrees := rfl } -/
#guard_msgs in
example : IsDualOf (.send .bye .done) gFix := ⟨rfl⟩

/-! ## The session-as-machine: conformance teeth -/

/-- The canonical tape, pinned in values. -/
theorem follow_gFix_pin :
    follow gFix
      = [.step .snd .req, .step .rcv .ack, .pick true, .step .snd .bye] := rfl

/-- THE CONFORMING RUN (cited, never re-proved): a protocol-following
    run COMPLETES — a run that follows the protocol is a legal trace. -/
theorem conforming_gFix : sessionMachine.run gFix (follow gFix) = some .done :=
  follow_runs gFix

/-- THE REFUSAL (direction): the violating tape is refused — the
    refusal is data, never a silent self-loop. -/
theorem dirViolation_refused : sessionMachine.run gFix badDir = none := rfl

/-- THE REFUSAL (payload): the wire is typed — a mismatched payload is
    refused. -/
theorem payViolation_refused : sessionMachine.run gFix badPay = none := rfl

/-- THE NAMED DIAGNOSTIC (direction): the offender is the SECOND move —
    position 1, a send where the protocol expects a receive. -/
theorem offender_gFix_dir :
    offender gFix badDir = some (1, .step .snd .ack) := rfl

/-- THE NAMED DIAGNOSTIC (payload): position 1, a request where the
    protocol expects an acknowledgement. -/
theorem offender_gFix_pay :
    offender gFix badPay = some (1, .step .rcv .req) := rfl

/-- The truncated tape: non-conforming (the run did not reach `done`)
    but with NO offender — the tape ran out before any refusal. The
    diagnostic distinguishes wedging from truncation. -/
theorem truncated_gFix :
    sessionMachine.run gFix [.step .snd .req] ≠ some .done
    ∧ offender gFix [.step .snd .req] = none := ⟨by decide, rfl⟩

/-! ## The refinement: the delaying impl's two faces (cited + pinned) -/

/-- THE REFINEMENT, cited: the impl that performs the first exchange and
    then delays refines its protocol (rides the landed `Coalg.Refines`). -/
theorem impl_refines_protocol :
    Refines
      (⟨boundedImpl, nodeObs⟩ :
        Coalgebra (Bool × Session Pay) (Session.Move Pay) (Option (Dir × Pay)))
      (⟨mSpec, nodeObs⟩ :
        Coalgebra (Bool × Session Pay) (Session.Move Pay) (Option (Dir × Pay)))
      Holds :=
  bounded_refines (P := Pay)

/-- The impl's FRESH face, pinned: it fires the first exchange exactly
    when the protocol does. -/
theorem implFace_fresh :
    boundedImpl.step? (false, gFix) (.step .snd .req)
      = some (true, .recv .ack (.choice (.send .bye .done) (.recv .ack .done))) := rfl

/-- The impl's HOLDING face, pinned: after the first exchange it
    refuses everything — it may not speak when the protocol does not. -/
theorem implFace_holds :
    boundedImpl.step? (true, gFix) (.step .snd .req) = none := rfl

/-! ## The axiom self-check (this lane's own pins) -/

/-- info: 'Machines.Session.dual_dual' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Session.dual_dual

/-- info: 'Machines.Session.msgs_dual' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Session.msgs_dual

/-- info: 'Machines.Session.dirs_dual' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Session.dirs_dual

/-- info: 'Machines.Session.follow_runs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Session.follow_runs

/-- info: 'Machines.Session.taken_of_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Machines.Session.taken_of_run

/-- info: 'Machines.Session.bounded_refines' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Machines.Session.bounded_refines

/-- info: 'Machines.Session.proj_dual' does not depend on any axioms -/
#guard_msgs in
#print axioms Machines.Session.proj_dual

/-! ## The suite -/

def specSession : Spec := Spec.ofList "session-boundary"
  (fun _ => do
    assert (dual (dual gFix) == gFix) "involution wrong"
    assert (serverFix == .recv .req (.send .ack
      (.choice (.recv .bye .done) (.send .ack .done)))) "dual value wrong"
    assert (msgs (dual gFix) == msgs gFix) "wire law (payloads) wrong"
    assert (msgs gFix == [.req, .ack, .bye, .ack]) "msgs value wrong"
    assert (sessionMachine.run gFix (follow gFix) == some .done)
      "conforming run refused"
    assert (sessionMachine.run gFix badDir == none)
      "direction violation accepted"
    assert (sessionMachine.run gFix badPay == none)
      "payload violation accepted"
    assert (offender gFix badDir == some (1, .step .snd .ack))
      "diagnostic wrong (direction)"
    assert (offender gFix badPay == some (1, .step .rcv .req))
      "diagnostic wrong (payload)"
    assert (offender gFix [.step .snd .req] == none)
      "truncated tape misdiagnosed"
    assert (boundedImpl.step? (true, gFix) (.step .snd .req) == none)
      "holding impl fired")
  [ ("sabotage-dual-drift", fun _ =>
      assert (serverFix == gFix) "control"),
    ("sabotage-violation-accepted", fun _ =>
      assert (sessionMachine.run gFix badDir == some .done) "control"),
    ("sabotage-diagnostic-blind", fun _ =>
      assert (offender gFix badDir == none) "control") ]
  1 47
