/-
# SchemaLang.Session — payload-TYPED choreographies

`Machines.Session` owns the choreography MECHANISM generically over the
payload universe `P` (duality, lockstep, mid-protocol deadlock-freedom,
termination — proved once). This layer is the `P := Ty` instantiation:
the payload is the schema universe's `Ty` — the closed type universe the
WIT/Rust emitters own — so a choreography that names a payload the
schema doesn't define fails the universe check, and the wire names come
from the ONE renderer.

`TStep`/`TProtocol`/`tdual` are the generic `Machines.Session` defs at
`P := Ty` (no local re-defs — the duality facts come from one place).
The ONE remaining local fact is the bridge `tdual_toWire`: the typed
dual's WIRE view (`toWire`, via `Ty.witName` = `Emit.Wit.tyWit` — the
same text the WIT emitter puts on the wire) IS the wire dual of the
wire view. The payload-sequence agreement
(`typed_wire_payloads_agree`) then reduces to the generic
`Machines.Session.tdual_types` — no choreography fact is proved twice,
and the choreography cannot drift from the wire.

The instance is the gateway conversation with REAL Tys: `get-user`
(sends `u64`, receives `option<user>`), `watch-orders` (sends
`order-error`, receives `stream<user>`).
-/

import Machines.Session
import SchemaLang.Ty
import SchemaLang.Emit.Wit

namespace SchemaLang

/-- The WIRE NAME of a schema type: the same text the WIT emitter puts
    on the wire (`tyWit`). One renderer, two consumers — the
    choreography and the interface cannot drift. (Top-level in
    `SchemaLang` so the `Ty.` projection resolves — under `Session` it
    would nest as `Session.Ty.witName` and dot-notation would miss it.) -/
def Ty.witName (t : Ty) : String := Emit.Wit.tyWit t

namespace Session

open Machines.Session (Dir)

/-- A typed choreography step: direction × the payload's SCHEMA type —
    the generic `Machines.Session.TStep` at `P := Ty` (the closed
    universe — `.ty "user"` resolves or fails at elaboration via the
    universe check). -/
abbrev TStep := Machines.Session.TStep Ty

/-- A typed protocol — the generic `Machines.Session.TProtocol` at
    `P := Ty`. -/
abbrev TProtocol := Machines.Session.TProtocol Ty

/-- The typed dual — the generic `Machines.Session.tdual` at `P := Ty`
    (flip directions, keep the schema type). The duality facts
    (`tdual_dual`, `tdual_types`, `tdual_directions_oppose`,
    `tdual_payload_mirror`) are the generic theorems, instantiated. -/
abbrev tdual (p : TProtocol) : TProtocol := Machines.Session.tdual p

/-- The wire-level (string) view of a typed protocol — the
    `Machines.Session.TProtocol String` the generic duality theorems
    speak about at `P := String`. -/
def toWire (p : TProtocol) : Machines.Session.TProtocol String :=
  p.map fun (d, t) => (d, t.witName)

/-- THE BRIDGE: the wire view of the typed dual IS the wire dual of the
    wire view. Everything `Machines.Session` proves about the dual
    (mirror, lockstep, liveness) transfers to the typed layer through
    this — proved ONCE, generically, in Machines.Session. -/
theorem tdual_toWire (p : TProtocol) :
    toWire (tdual p) = Machines.Session.tdual (toWire p) := by
  induction p with
  | nil => rfl
  | cons s rest ih =>
      -- both sides are definitional cons compositions:
      -- LHS = toWire (tdual cons) = (flip d, wire t) :: toWire (tdual rest)
      -- RHS = tdual (toWire cons) = (flip d, wire t) :: tdual (toWire rest)
      show (s.1.flip, s.2.witName) :: toWire (Machines.Session.tdual rest)
        = (s.1.flip, s.2.witName) :: Machines.Session.tdual (toWire rest)
      rw [ih]

/-- The typed dual keeps the PAYLOAD SEQUENCE — the wire names agree
    position-for-position (the generic `Machines.Session.tdual_types`
    at `P := String`, via the bridge). -/
theorem typed_wire_payloads_agree (p : TProtocol) :
    (toWire (tdual p)).map (·.2) = (toWire p).map (·.2) := by
  rw [tdual_toWire]
  exact Machines.Session.tdual_types _

/-! ## The gateway instance, typed -/

/-- The gateway conversation with REAL schema types: `get-user` sends
    `u64`, receives `option<user>`; `watch-orders` sends `order-error`,
    receives the `stream<user>` change flow (the delta-shaped contract
    AS the choreography). A payload not in the schema universe fails
    `universeCheck`; the wire names come from the one renderer. -/
def gatewayTyped : TProtocol :=
  [ (.snd, .u64), (.rcv, .option (.ty "user"))
  , (.snd, .ty "order-error"), (.rcv, .stream (.ty "user")) ]

/-- The typed gateway duals through the bridge: the generic guarantees
    (lockstep, mirror, mid-protocol liveness) hold of the typed gateway
    conversation, proved ONCE in Machines.Session. -/
theorem gateway_typed_dual_wire :
    toWire (tdual gatewayTyped) = Machines.Session.tdual (toWire gatewayTyped) :=
  tdual_toWire gatewayTyped

end SchemaLang.Session
