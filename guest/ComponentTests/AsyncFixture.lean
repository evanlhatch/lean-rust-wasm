/-
# ComponentTests.AsyncFixture — the async lane's component face

The component lane's SIXTH fixture: the async host lane (D4's named
remainder — the async-lift protocol as a session). The Lean side
landed (`Machines.AsyncSession`: the handshake declared ONCE as a
session, both peers derived, the duality checked; `Wit.Func.async`: the
func-level async row; `Wit.Session`: the row ↔ tape bridge, the
parse-back landed with the async row); THIS fixture is the CONTRACT
face: the pinned async world row whose runtime face the host runs
(`crates/mandate-host`'s async lane — `wasi_async`, the fixture
component exporting `f : async func() -> u64`).

THE HONEST MINIMAL (the WitFixture precedent, one lane over): the
guest's async component is NOT emitted by `Guest.Component` (the
emission lane's world-check face is sync — the async emission is the
named next), so the fixture pins the CONTRACT (the world row + its
render + its parse-back + its tape) and the VALUE, and the wasmtime
face pins the runtime side at the same literals. The parity
discipline's shape:

- leg 1 (HERE, the contract face): the row's render spells
  `export await-future: async func() -> u64;` (the WIT spec's current
  shape — `Wit.Render.func`'s async prefix, confirmed against the
  legacy `splicer-mw.wit` fixture); the parse-back (`Wit.Parse`,
  landed WITH the async row) recovers the flag;
- leg 2 (HERE, the tape bridge): the row's export tape IS the lift's
  three moves (recv params — vacuous here — then the two SENDS:
  task-return, task handle; `Wit.Session.exportTape`'s async arm), and
  the import row's tape IS its dual (`import_dual_export` — the host's
  concurrent call, derived never hand-written);
- leg 3 (crates/mandate-host tests/wasi_async.rs, the runtime face):
  the async component RUNS through `instantiate_async` +
  `run_concurrent`'s Accessor discipline, and the future's value — the
  SAME `hostGolden` 42 pinned here — crosses typed (`TypedFunc<(),,
  (u64,)>`'s lift). The task intrinsics are runtime-provided (the
  canon trampolines; the source evidence in `wasi_async`'s module doc).

THE SESSION/RUNTIME AGREEMENT (the honest claim): the fixture's
`wireFirstValue` ties the session model's first payload
(`Machines.AsyncSession.hostConcurrentCall`'s `taskReturn 42`) to the
Rust golden's 42; what this pins is the VALUE + the MOVE ORDER at the
fixture — not a compiled-body correspondence theorem (the same honesty
the component lane's parity discipline uses: the fixture's body IS the
tape's face).

The teeth (the Machinery's own, cited not duplicated — the patterns
rule): the mis-shaped async export refuses (`Machines.AsyncSession`'s
refusal family — recv-first, handle-first, wrong value, over-talking);
the signature-level face (`Wit.Session.sync_async_tapes_ne`); the
RUST face's teeth (the asyncness mismatch refuses at compile; the
valve's default-deny on the async path) live in the wasi_async suite.

The five questions (notes/v3/01-core.md): the fixture is data (the
test lane's Universe face) — the answers live at the consumers
(`mandate-host`'s async lane over the pinned row).
-/

import Wit
import Wit.World
import Wit.Session
import Wit.Parse
import Machines.AsyncSession
import TestingKit.Spec

namespace ComponentTests.AsyncFixture

open Wit (Func Field Ty World Item)

/-! ## The deployed async row (the Lean SSOT's contract face) -/

/-- THE PINNED ASYNC ROW: `await-future : async func() -> u64` — the
    func-level async row (`Wit.Func.async`) at the fixture's shape,
    the D2 `future<u64>` row's contract face (the value the host
    awaits). -/
def awaitFuture : Func :=
  { name := "await-future"
  , params := []
  , result := some (.atom .u64)
  , async := true }

/-- THE ASYNC WORLD (the contract the runtime face answers). -/
def asyncWorld : World :=
  { name := "async", imports := [], exports := [.func awaitFuture] }

/-- The world text (the render's face). -/
def worldText : String := Wit.Render.worldFile "mandate:async" asyncWorld

/-! ## The legs (pure, each consumed by the suite) -/

/-- LEG 1 (the render): the async row's spelling is the `async `
    prefix before `func(` — the contract text the runtime face's
    export answers. -/
def legRender : Bool :=
  worldText.contains "export await-future: async func() -> u64;"

/-- LEG 1b (the parse-back, landed WITH the async row): the world
    text parses back and recovers the flag (the round trip's async
    pin — a render whose image drops the `async` bit fails here). -/
def legParseBack : Bool :=
  match Wit.Parse.parseWorld (Wit.Render.world asyncWorld) with
  | .ok q =>
      (q.val.exports.all (fun i =>
        match i with
        | .func f => f.name == "await-future" && f.async
            && f.result == some (.atom .u64)
        | .iface _ => false)) == some true
  | .error _ => false

/-- LEG 2 (the tape bridge): the async row's export tape IS the lift's
    three moves — recv the (vacuous) params, send task-return, send
    task handle. Kernel-checked (`decide` over the derived
    DecidableEq); `Wit.Session.exportTape`'s async arm. -/
def legTape : Bool :=
  decide ((show List Wit.Session.Move from Wit.Session.exportTape awaitFuture)
    = [Wit.Session.Move.recv .params,
       Wit.Session.Move.send .taskReturn,
       Wit.Session.Move.send .taskHandle])

/-- LEG 2b (the dual): the import row's tape IS the export's dual —
    the host's concurrent call, derived (`Wit.Session.
    import_dual_export`'s cited face at THIS row). -/
def legDual : Bool :=
  decide ((show List Wit.Session.Move from Wit.Session.importTape awaitFuture)
    = ((show List Wit.Session.Move from Wit.Session.exportTape awaitFuture)
      |>.map Wit.Session.Move.flip))

/-! ## The session model's VALUE tie (the Machines face) -/

/-- THE HOST GOLDEN (the shared literal): the future's value — the
    session model's `taskReturn 42` (`Machines.AsyncSession`) and the
    Rust face's golden answer (`tests/wasi_async.rs`'s
    `async_future_value_crosses` pin). ONE 42, both faces. -/
def hostGolden : Nat := 42

/-- THE WIRE'S FIRST PAYLOAD IS THE GOLDEN: the session model's
    concurrent call opens with `taskReturn 42` — definitional (the
    `msgs_wire` pin's reading), so a value drift fails at elaboration. -/
theorem wireFirstValue :
    match Machines.Session.msgs Machines.AsyncSession.hostConcurrentCall with
    | .taskReturn v :: _ => v = hostGolden
    | _ => False := rfl

/-- The leg as data (the suite consumes the theorem's shape; the
    kernel checked the equality). -/
def legWireValue : Bool :=
  decide (show Bool from
    match (show List Machines.AsyncSession.AsyncWire from
      Machines.Session.msgs Machines.AsyncSession.hostConcurrentCall) with
    | .taskReturn v :: _ => v = hostGolden
    | _ => False)

/-! ## The suite (the Main driver consumes this) -/

def asyncSpecs : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList "the async lane: the await-future row — the render's \
      `async func` spelling, the parse-back's flag survival, the tape \
      bridge (the lift's two sends over the vacuous params), the dual, \
      the session model's 42 = the Rust face's golden"
      (fun _ => do
        TestingKit.assert legRender
          "the world text must spell `export await-future: async func() -> u64;`"
        TestingKit.assert legParseBack
          "the parse-back must recover the async row (the flag survives)"
        TestingKit.assert legTape
          "the async export's tape must be recv-params, send-task-return, send-handle"
        TestingKit.assert legDual
          "the import row's tape must be the export's dual (the derived \
           concurrent call)"
        TestingKit.assert legWireValue
          "the session's wire must open with taskReturn 42 (the host golden)")
      [ ("control: the render pin is a LIE (demands the sync spelling — \
          caught)",
         fun _ => TestingKit.assert
           (worldText.contains "export await-future: func() -> u64;")
           "the control demands the sync spelling to be present")
      , ("control: the value pin BROKEN (the golden 999) is caught",
         fun _ => TestingKit.assertEq "wrong"
           (match Machines.Session.msgs Machines.AsyncSession.hostConcurrentCall with
            | .taskReturn v :: _ => v
            | _ => 0) 999)
      ]
      (h := by simp) 1 71
  ]

end ComponentTests.AsyncFixture
