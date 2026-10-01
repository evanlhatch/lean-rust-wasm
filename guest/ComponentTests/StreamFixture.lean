/-
# ComponentTests.StreamFixture — the stream lane's component face

The component lane's stream fixture: the D2 `stream<u64>` TY row's
RUNTIME face as a contract (the AsyncFixture precedent, one lane
over). The legacy evidence: the watch-counts/watch-users stream
exports (the zero-copy handle pass-through through the middleware —
`legacy/crates/splicer-mw/`; the items flow THROUGH the handle, in
order). The runtime face THIS fixture pins:
`crates/mandate-host`'s stream lane (`stream.rs` +
`tests/streams.rs`) — the host consumes a `stream<u64>` export with
the PULL discipline: the host reads the stream's items until the end.

THE HONEST BOUNDARY (named, never papered over): the fixture's
`make` export is a SYNC `func() -> stream<u64>` whose guest body
creates the stream and returns the readable half EMPTY (the
`stream.new` + `stream.drop-writable` intrinsics — a full sync
crossing). A guest PRODUCING items mid-body (suspending the write
until the consumer attaches, the legacy 1c) is the stack-switching /
async-lift CALLBACK discipline — NOT landed; the guest-side
production via the callback discipline is the honest current shape's
seam (`mandate-host::wasi_async`, the async-lift lane). The multi-item
face the runtime tests pin is the HOST-producer side of the SAME pull
discipline (wasmtime 47's `StreamProducer` for `Vec<u64>`: items
delivered in order, then end-of-stream) — plus the handle
pass-through export (`pass : func(stream<u64>) -> stream<u64>`, the
legacy middleware's zero-copy pass-through at the boundary).

The session's runtime face (leg 3's partner): the producer/consumer
discipline declared ONCE as a session — the guest's stream export
(item, item, item, end) — the host's drain DERIVED as the dual, the
duality checked; the wire's payload ORDER is the session's
guarantee, pinned (`msgs_wire`: [7, 8, 9, end] — the items cross in
order).

The five questions (notes/v3/01-core.md): the fixture is data (the
test lane's Universe face) — the answers live at the consumers
(`mandate-host`'s stream lane over the pinned row).
-/

import Wit
import Wit.World
import Wit.Parse
import Machines.Session
import TestingKit.Spec

namespace ComponentTests.StreamFixture

open Wit (Func Field Ty World Item)
open Machines.Session

/-! ## The deployed stream row (the Lean SSOT's contract face) -/

/-- THE PINNED STREAM ROW: `make : func() -> stream<u64>` — the D2
    `Ty.stream` row's runtime face at the fixture's shape (the SYNC
    export the host consumes with the pull discipline). -/
def makeStream : Func :=
  { name := "make"
  , params := []
  , result := some (.stream (.atom .u64))
  , async := false }

/-- THE STREAM WORLD (the contract the runtime face answers). -/
def streamWorld : World :=
  { name := "stream", imports := [], exports := [.func makeStream] }

/-- The world text (the render's face). -/
def worldText : String := Wit.Render.worldFile "mandate:stream" streamWorld

/-! ## The legs (pure, each consumed by the suite) -/

/-- LEG 1 (the render): the stream row's spelling is the sync
    `func()` returning `stream<u64>` — the D2 row's runtime-face
    text (the render law `Wit.Parse.ty_stream`'s image). -/
def legRender : Bool :=
  worldText.contains "export make: func() -> stream<u64>;"

/-- LEG 1b (the parse-back): the world text parses back and recovers
    the stream payload (a render whose image loses `stream<u64>`
    fails here). -/
def legParseBack : Bool :=
  match Wit.Parse.parseWorld (Wit.Render.world streamWorld) with
  | .ok q =>
      (q.val.exports.all (fun i =>
        match i with
        | .func f => f.name == "make"
            && f.result == some (.stream (.atom .u64))
            && !f.async
        | .iface _ => false)) == some true
  | .error _ => false

/-! ## The session's runtime face (the producer/consumer discipline) -/

/-- One wire message of the stream discipline. The universe is
    CLOSED: a new message kind is a protocol act here, not a flag. -/
inductive StreamWire where
  /-- One stream item crossing (the payload is the value). -/
  | item (v : Nat)
  /-- End of stream (the pull discipline's terminal). -/
  | endOfStream
deriving DecidableEq, Repr, BEq

open StreamWire

/-- THE GUEST'S STREAM EXPORT (the producer's pen): deliver the
    items IN ORDER, then the end-of-stream, done. The multi-item
    fixture [7, 8, 9] — the Rust face's golden list. -/
def guestStreamExport : Machines.Session StreamWire :=
  .send (item 7) (.send (item 8) (.send (item 9) (.send endOfStream .done)))

/-- THE HOST'S STREAM DRAIN (derived, never hand-written): receive
    the items in order, receive the end, done. The dual of the
    guest's export — the pull discipline's two faces of one session. -/
def hostStreamDrain : Machines.Session StreamWire := Machines.Session.dual guestStreamExport

/-- THE DUALITY CHECK (definitional): the host's drain is exactly
    receive-7-receive-8-receive-9-receive-end. -/
theorem hostDualGuest :
    hostStreamDrain
      = .recv (item 7) (.recv (item 8) (.recv (item 9) (.recv endOfStream .done)))
      := rfl

/-- Peer agreement as a TYPE: the host's drain inhabits the dual-of
    relation over the guest's export, by construction. -/
instance instHostDualGuest :
    IsDualOf hostStreamDrain guestStreamExport := ⟨rfl⟩

/-- THE WIRE LAW (the ORDER pin): dual peers exchange the SAME
    payloads in the same order — the items cross 7, 8, 9, then the
    end. A reordering breaks this at elaboration. -/
theorem msgs_wire :
    Machines.Session.msgs hostStreamDrain = [item 7, item 8, item 9, endOfStream] := rfl

/-- THE EMPTY STREAM: the guest's `make` face — the stream is created
    and the readable half returned with NO items (the sync crossing
    the runtime lane runs); the host's pull observes end immediately. -/
def guestStreamEmpty : Machines.Session StreamWire := .send endOfStream .done

/-- The empty stream's host face: receive-end-then-done (derived). -/
def hostDrainEmpty : Machines.Session StreamWire := dual guestStreamEmpty

/-- The empty stream's wire law: ONE message — the end. -/
theorem msgs_empty :
    Machines.Session.msgs hostDrainEmpty = [endOfStream] := rfl

/-! ## The conformance: both peers complete the pull -/

/-- The guest's canonical tape runs its export protocol to `done`
    (the general law `follow_runs`, cited). -/
theorem guest_run_completes :
    Machines.Session.sessionMachine.run guestStreamExport (Machines.Session.follow guestStreamExport) = some .done :=
  follow_runs guestStreamExport

/-- The host's canonical tape runs its drain protocol to `done` —
    the pulled stream drains completely. -/
theorem host_run_completes :
    Machines.Session.sessionMachine.run hostStreamDrain (Machines.Session.follow hostStreamDrain) = some .done :=
  follow_runs hostStreamDrain

/-- The empty stream's run completes (the pull observes only the end). -/
theorem empty_run_completes :
    Machines.Session.sessionMachine.run guestStreamEmpty (Machines.Session.follow guestStreamEmpty) = some .done :=
  follow_runs guestStreamEmpty

/-! ## The teeth: the mis-shaped stream refuses -/

/-- Transition 1: the first item crosses (7). -/
theorem step_first :
    Machines.Session.sessionStep? hostStreamDrain (.step .rcv (item 7))
      = some (.recv (item 8) (.recv (item 9) (.recv endOfStream .done))) := rfl

/-- THE HOST refuses an item OUT OF ORDER (8 where the protocol pins
    7) — the order is the session's guarantee, not a convention. -/
theorem host_refuses_out_of_order :
    Machines.Session.sessionStep? hostStreamDrain (.step .rcv (item 8)) = none := by
  show sessionStep?
    (.recv (item 7) (.recv (item 8) (.recv (item 9) (.recv endOfStream .done))))
    (.step .rcv (item 8)) = none
  simp only [sessionStep?]
  split
  · rename_i heq
    simp only [StreamWire.item.injEq] at heq
    omega
  · rfl

/-- THE WIRE IS TYPED: the end where an item is pinned refuses —
    the pull expects an item until the pinned items have crossed. -/
theorem host_refuses_end_first :
    Machines.Session.sessionStep? hostStreamDrain (.step .rcv endOfStream) = none := by
  show sessionStep?
    (.recv (item 7) (.recv (item 8) (.recv (item 9) (.recv endOfStream .done))))
    (.step .rcv endOfStream) = none
  rfl

/-- THE DIRECTION IS THE PRODUCER'S: a guest export that WAITS first
    (a recv-rooted "stream") is not a stream producer — the guest's
    protocol refuses the receive move. -/
theorem export_refuses_recv :
    Machines.Session.sessionStep? guestStreamExport (.step .rcv (item 7)) = none := rfl

/-- Terminal: after the end, EVERY move refuses (the general law
    `doneRefused`, cited) — the pull is over. -/
theorem done_terminal (mv : Machines.Session.Move StreamWire) :
    Machines.Session.sessionStep? (P := StreamWire) .done mv = none := doneRefused mv

/-- THE NAMED DIAGNOSTIC: a drifted item (8 where the protocol pins
    7) is refused at position 0 with the offending move named. -/
theorem offender_drift :
    Machines.Session.offender hostStreamDrain [.step .rcv (item 8)]
      = some (0, .step .rcv (item 8)) := rfl

/-! ## The VALUE tie to the runtime face -/

/-- THE STREAM GOLDEN (the shared literal): the multi-item face's
    items — the session model's `guestStreamExport` payloads and the
    Rust face's golden list (`tests/streams.rs`'s
    `the_multi_item_stream_crosses_in_order` pin). THREE values +
    the end, both faces. -/
def streamGolden : List Nat := [7, 8, 9]

/-- THE WIRE'S ITEM PAYLOADS ARE THE GOLDEN: the session's msgs
    drop the end marker onto the golden list — definitional, so a
    value or order drift fails at elaboration. -/
theorem wireItems :
    (Machines.Session.msgs hostStreamDrain).dropLast = streamGolden.map item := rfl

/-- The leg as data (the suite consumes the theorem's shape). -/
def legWireValue : Bool :=
  decide (show Bool from
    (show List StreamWire from (Machines.Session.msgs hostStreamDrain).dropLast)
      = streamGolden.map item)

/-! ## The suite (the Main driver consumes this) -/

def streamSpecs : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList "the stream lane: the make row — the render's \
      `func() -> stream<u64>` spelling, the parse-back's payload \
      survival, the producer/consumer session (the items cross in \
      order: 7, 8, 9, end), the duality, the empty stream, the value \
      tie to the Rust face's golden"
      (fun _ => do
        TestingKit.assert legRender
          "the world text must spell `export make: func() -> stream<u64>;`"
        TestingKit.assert legParseBack
          "the parse-back must recover the stream row (the payload survives)"
        TestingKit.assert legWireValue
          "the session's wire must carry the golden items in order \
           (7, 8, 9 — the Rust face's golden list)")
      [ ("control: the render pin is a LIE (demands the u64-scalar \
          spelling — caught)",
         fun _ => TestingKit.assert
           (worldText.contains "export make: func() -> u64;")
           "the control demands the scalar spelling to be present")
      , ("control: the value pin BROKEN (the golden 42 first) is caught",
         fun _ => TestingKit.assertEq "wrong"
           (match (show List StreamWire from
              (Machines.Session.msgs hostStreamDrain).dropLast) with
            | .item v :: _ => v
            | _ => 0) 42)
      ]
      (h := by simp) 1 73
  ]

end ComponentTests.StreamFixture
