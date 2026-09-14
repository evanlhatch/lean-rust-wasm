/-
# SchemaLang.OrderMachine — the order lifecycle as a machine

The demo domain's (Demo.lean: User/Order/OrderError) lifecycle discipline,
modeled as a Machines machine — the SECOND machine in the tree and the
first DOMAIN machine: the pipeline machine (Pipeline.lean) models the
TOOLING, this one models the SOFTWARE the spec authors ship.

Two projections, per Machines.Core (the Pipeline.lean pattern):
- executable: `orderMachine.step?` / `.run` — invalid sequences rejected,
- proof: `orderMachine.tr` + the theorems below.

Proved here:
- `lifecycle_rank_advances` / `lifecycle_rank_advances_tr` — every non-`reset` transition
  strictly increases the lifecycle rank (the lifecycle is a DAG whose
  only cycles pass through `reset`).
- `terminal_only_reset` — `delivered`/`cancelled` are TERMINAL: only
  `reset` leaves them (the lifecycle cannot silently reopen).
- `reject_*` — out-of-order and double-fire are observably rejected.
- `orderTableStep?_eq_step?` — the emitted Rust table IS the machine (the
  same discipline that governs the pipeline driver).

Consumption: `SchemaLang.Emit.Machine` folds `orderTrans` into Rust
(`src/order_machine_generated.rs`); steel-host's test replays the
lifecycle trace against the generated step fn. The battery
(`conformance`) sweeps the full state space; the pipelineDead machine
(Pipeline.lean) is the global non-vacuity control for the battery.

Deliberate exclusion: no effectful transition payloads (Machines v1 has
no output channel — see Machines/Core.lean); the machine is the
DISCIPLINE model, the data effects ride the schema funcs.
-/

import Machines.Dsl
import Machines.Testing
import SchemaLang.Item

open Machines.Dsl

namespace SchemaLang

/-! ## The lifecycle -/

/-- The order status: the machine's states (NOT a schema item — this is
    the lifecycle discipline, not wire data; the wire carries the order
    record, the host carries the status). `stray` is the state NO
    transition produces — the invariant excludes it, the battery
    enumerates it (non-vacuity: the machine PROVES the host can never
    synthesize it), the generated step rejects it. -/
inductive OrderStatus where
  | cart | placed | shipped | delivered | cancelled | stray
deriving Repr, BEq, DecidableEq, Inhabited

-- The machine. Terminal states (`delivered`/`cancelled`) reject every
-- event except `reset` (the recovery edge) — terminality is a THEOREM
-- below, not a convention. (plain comment: doc comments cannot precede
-- machine! — the custom command rejects them)
/-- Lifecycle rank: cart 0 → placed 1 → shipped 2 → delivered/
    cancelled 3. `cancelled` rides with `delivered` (both terminal);
    `stray` rides at 0 (unreachable — no transition targets it). -/
def OrderStatus.rank : OrderStatus → Nat
  | .cart => 0 | .placed => 1 | .shipped => 2
  | .delivered => 3 | .cancelled => 3 | .stray => 0

machine! orderMachine where
  State: OrderStatus
  Inv: fun s => s ≠ .stray
  rank: OrderStatus.rank rewind: reset
  event: place guard: (fun s => s = .cart) action: (fun _ _ => .placed)
  event: ship guard: (fun s => s = .placed) action: (fun _ _ => .shipped)
  event: deliver guard: (fun s => s = .shipped) action: (fun _ _ => .delivered)
  event: cancel guard: (fun s => s = .cart || s = .placed) action: (fun _ _ => .cancelled)
  event: reset guard: (fun _ => true) action: (fun _ _ => .cart)

instance : DecidablePred orderMachine.Inv := fun s =>
  match s with
  | .stray => isFalse (fun h => h rfl)
  | .cart => isTrue (fun h => OrderStatus.noConfusion h)
  | .placed => isTrue (fun h => OrderStatus.noConfusion h)
  | .shipped => isTrue (fun h => OrderStatus.noConfusion h)
  | .delivered => isTrue (fun h => OrderStatus.noConfusion h)
  | .cancelled => isTrue (fun h => OrderStatus.noConfusion h)

/-- The full state space for the conformance battery — the stray state
    included (that's the point: the invariant is FALSE on it, the
    non-vacuity check has something to see, and no transition reaches
    it). -/
def orderStates : List OrderStatus :=
  [.cart, .placed, .shipped, .delivered, .cancelled, .stray]

/-- The conformance battery: deadlock-freedom (reset is always
    enabled), guard coverage, invariant non-vacuity. -/
def orderConformance : List (String × TestKit.CheckResult) :=
  Machines.Testing.conformance orderMachine orderMachine.labels orderStates
    orderMachine.labels_complete

/-! ## The proved discipline -/

/-- Terminal states: only `reset` leaves them. A delivered order cannot
    be re-shipped; a cancelled order cannot be re-placed — silently
    reopening the lifecycle is IMPOSSIBLE, not forbidden. -/
theorem terminal_only_reset (s s' : OrderStatus) (l : orderMachine.Label)
    (htr : orderMachine.tr s l s')
    (hd : s = .delivered ∨ s = .cancelled) :
    l = .reset := by
  obtain ⟨w, hw⟩ := htr
  rcases hd with hd | hd <;> subst hd
  · cases l <;> simp [orderMachine, orderMachine.spec] at w ⊢
  · cases l <;> simp [orderMachine, orderMachine.spec] at w ⊢

/-- The happy path EXECUTES: place, ship, deliver. -/
theorem lifecycle_happy_path : orderMachine.run .cart [.place, .ship, .deliver]
    = some ([(.place, .placed), (.ship, .shipped), (.deliver, .delivered)], .delivered) :=
  rfl

/-- The cancel path EXECUTES from either open state. -/
theorem cancel_from_placed : orderMachine.run .cart [.place, .cancel]
    = some ([(.place, .placed), (.cancel, .cancelled)], .cancelled) :=
  rfl

/-- Out-of-order firing is REJECTED, observably. -/
theorem reject_ship_before_place : orderMachine.run .cart [.ship] = none := rfl

/-- Double-fire is REJECTED, observably (a placed order cannot be
    re-placed). -/
theorem reject_double_place : orderMachine.run .cart [.place, .place] = none := rfl

/-- The terminal state's step is `none` for every non-reset event (the
    executable reading of `terminal_only_reset`). -/
theorem delivered_step_none (l : orderMachine.Label)
    (hnr : l ≠ .reset) : orderMachine.step? .delivered l = none := by
  cases l <;> simp [orderMachine, orderMachine.spec] at hnr ⊢

/-! ## The emitted table — the driver's data

The transition DATA the emitter folds (`Emit.Machine.matchArms`
generates the Rust match from these rows). The DATA and the structural
`orderTableStep?` below are two readings of one machine — the theorem pins
the structural reading to the machine; the emitter's wildcard-check +
the Rust-side replay test guard the data reading.
-/

def orderTrans : List (orderMachine.Label × OrderStatus × OrderStatus) :=
  [ (.place, .cart, .placed)
  , (.ship, .placed, .shipped)
  , (.deliver, .shipped, .delivered)
  , (.cancel, .cart, .cancelled)
  , (.cancel, .placed, .cancelled)
  , (.reset, .cart, .cart)
  , (.reset, .placed, .cart)
  , (.reset, .shipped, .cart)
  , (.reset, .delivered, .cart)
  , (.reset, .cancelled, .cart)
  , (.reset, .stray, .cart) ]

/-- The structural reading (the theorem's subject). -/
def orderTableStep? : orderMachine.Label → OrderStatus → Option OrderStatus
  | .place, .cart => some .placed
  | .ship, .placed => some .shipped
  | .deliver, .shipped => some .delivered
  | .cancel, .cart => some .cancelled
  | .cancel, .placed => some .cancelled
  | .reset, _ => some .cart
  | _, _ => none

/-- The emitted table IS the machine. -/
theorem orderTableStep?_eq_step? (e : orderMachine.Label) (s : OrderStatus) :
    orderTableStep? e s = orderMachine.step? s e := by
  cases s <;> cases e <;>
    simp [orderTableStep?, orderMachine, orderMachine.spec]

end SchemaLang
