/-
# SchemaLang.Session — payload-TYPED choreographies

`Machines.Session` certifies the choreography SHAPE (directions mirror
under dual; mid-protocol deadlock-freedom; termination) with payload
types as STRINGS. This layer upgrades the payload to the schema
universe's `Ty` — the closed type universe the WIT/Rust emitters own —
so a choreography that names a payload the schema doesn't define fails
the universe check, and the wire names come from the ONE renderer.

The bridge theorem (`tdual_toWire`) proves the typed layer's dual maps
to the string layer's dual through the wire rendering (`Ty.witName` =
`Emit.Wit.tyWit` — the same text the WIT emitter puts on the wire).
The payload-sequence agreement (`typed_wire_payloads_agree`) then
reduces to `Machines.Session.dual_map_payload` — no choreography fact
is proved twice, and the choreography cannot drift from the wire.

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

/-- A typed choreography step: direction × the payload's SCHEMA type
    (the closed universe — `.ty "user"` resolves or fails at
    elaboration via the universe check). -/
abbrev TStep := Dir × Ty

/-- A typed protocol. -/
abbrev TProtocol := List TStep

/-- The wire-level (string) view of a typed protocol — exactly the
    `Machines.Session.Protocol` the duality theorems speak about. -/
def toWire (p : TProtocol) : Machines.Session.Protocol :=
  p.map fun (d, t) => (d, t.witName)

/-- The typed dual: flip directions, keep the schema type. -/
def tdual (p : TProtocol) : TProtocol :=
  p.map fun (d, t) => (d.flip, t)

/-- THE BRIDGE: the wire view of the typed dual IS the wire dual of the
    wire view. Everything `Machines.Session` proves about the dual
    (mirror, lockstep, liveness) transfers to the typed layer through
    this — proved ONCE, at the string layer. -/
theorem tdual_toWire (p : TProtocol) :
    toWire (tdual p) = Machines.Session.dual (toWire p) := by
  induction p with
  | nil => rfl
  | cons s rest ih =>
      -- both sides are definitional cons compositions:
      -- LHS = toWire (tdual cons) = (flip d, wire t) :: toWire (tdual rest)
      -- RHS = dual (toWire cons) = (flip d, wire t) :: dual (toWire rest)
      show (s.1.flip, s.2.witName) :: toWire (tdual rest)
        = (s.1.flip, s.2.witName) :: Machines.Session.dual (toWire rest)
      rw [ih]

/-- The typed dual keeps the PAYLOAD SEQUENCE — the wire names agree
    position-for-position (the typed reading of
    `Machines.Session.dual_map_payload`, via the bridge). -/
theorem typed_wire_payloads_agree (p : TProtocol) :
    (toWire (tdual p)).map (·.2) = (toWire p).map (·.2) := by
  rw [tdual_toWire]
  exact Machines.Session.dual_map_payload _

/-- The typed dual's payload sequence IS the original's schema types
    (types survive dualing untouched). -/
theorem tdual_types (p : TProtocol) : (tdual p).map (·.2) = p.map (·.2) := by
  induction p with
  | nil => rfl
  | cons s rest ih => simp [tdual]

/-- Directions oppose pairwise: every send on one side is a receive on
    the other (the typed lockstep condition, executed form). -/
theorem typed_directions_oppose (p : TProtocol) :
    List.all (List.zip (p.map (·.1)) ((tdual p).map (·.1)))
      (fun x => x.1 != x.2) := by
  induction p with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | mk d t =>
          -- zip + all over a cons are definitional
          show ((d != d.flip) && List.all
            (List.zip (rest.map (·.1)) ((tdual rest).map (·.1)))
            (fun x => x.1 != x.2)) = true
          have h1 : (d != d.flip) = true := by cases d <;> rfl
          rw [h1]
          simp [ih]

/-! ## The gateway instance, typed -/

/-- The gateway conversation with REAL schema types: `get-user` sends
    `u64`, receives `option<user>`; `watch-orders` sends `order-error`,
    receives the `stream<user>` change flow (the delta-shaped contract
    AS the choreography). A payload not in the schema universe fails
    `universeCheck`; the wire names come from the one renderer. -/
def gatewayTyped : TProtocol :=
  [ (.snd, .u64), (.rcv, .option (.ty "user"))
  , (.snd, .ty "order-error"), (.rcv, .stream (.ty "user")) ]

/-- The typed gateway duals through the bridge: the string-layer
    guarantees (lockstep, mirror, mid-protocol liveness) hold of the
    typed gateway conversation, proved ONCE in Machines.Session. -/
theorem gateway_typed_dual_wire :
    toWire (tdual gatewayTyped) = Machines.Session.dual (toWire gatewayTyped) :=
  tdual_toWire gatewayTyped

end SchemaLang.Session
