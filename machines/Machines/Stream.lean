/-
# Machines.Stream — streams: the shared currency of machines and deltas

Owned by: the machines agent (the mandate tree, `machines/`).
Driving decisions: notes/v3/01-core.md §2-3 (Change + TraceModel — this
is where the roots MEET: a stream of deltas differentiates a stream of
states) + the legacy's proven content (legacy/lean/dbsp/Dbsp/Stream.lean,
Dbsp/Linear.lean — `Stream`, the `D`/`I` pair, the first-entry
convention; mined for intent, ported FRESH as core-only: the legacy's
group structure came from mathlib's `AddCommGroup` Pi instances, which
the cone rule forbids — here the additive structure is the LANDED
`Kit.Additive` (Kit.Change's top rung), consumed explicitly, exactly
like `ZSet.zsetAdditive` and `Kit.intAdd`).

## The home judgment (recorded)

Streams are the shared currency of machines and deltas — the honest
home is one both import. `machines/` sits downstream of `Kit` (and may
import `ZSet`), so `Machines.Stream` is importable by every future
consumer of either root; nothing in `zset/` needs to import it back
(the Z-set's additive instance FEEDS this layer, as the tests pin via
`zsetAdditive`). The generic is `Kit.Additive A A` — the delta-as-state
reading (the dbsp rung): the SAME type carries states and net changes.

## The convention (stated honestly, as in the legacy)

`D` and `I` are a true bijection on the PLAIN stream type — no
`s (-1) = 0` subtype — because `D` carries the initial value in its
first entry: `(D s) 0 = s 0`. So `(D s)` reads as an EVENT-SOURCING
journal: entry 0 is the init snapshot, entry `t+1` is the net change
from `t` to `t+1`. `I` integrates from that first entry. The cost of
the convention: `D` is NOT linear-in-the-Delta sense at index 0 — it is
the honest price of totality, and the net-zero trichotomy (03 §7: the
journal is EVENTS, the delta is the NET change; net-zero ≠ nothing
happened) is exercised as the mandatory control in MachinesTests.

## The five questions

- **Root**: the Change ↔ TraceModel CROSSING (01-core §2-3) — `D`
  takes the behavior view (a state stream) to the change view (a delta
  stream); `I` goes back. Neither root alone: the bridge between them.
- **Carrier grade**: `Kit.Correspondence.Iso` (01-core §4, the ONE
  carrier) — the `dI` value packages both round trips as an Iso VALUE,
  not a bare theorem pair.
- **Spine reading**: none — a substrate both the machine bridges and
  the delta lanes ride.
- **Ladder rung**: the round-trip laws are hand theorems at the
  structure (rung 6 — one induction each over a group-law
  rearrangement; not kernel-decidable in general). The group
  rearrangement itself (`compose_inv_cancel`) is the small generic
  hand lemma 01-core §7 calls the best foundation.
- **Gate rows**: the axiom report pins in MachinesTests.Axioms.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Kit.Change
import Kit.Correspondence

namespace Machines

/-- A stream: a `Nat`-indexed sequence — the discrete-time carrier
    both the machine semantics and the delta semantics speak. -/
abbrev Stream (A : Type) := Nat → A

variable {A : Type}

/-! ## The differentiation / integration pair -/

/-- Differentiation: the consecutive differences, with the FIRST ENTRY
    carrying the initial value (`(D s) 0 = s 0`) — the journal
    convention. The additive structure is `Kit.Additive A A`
    (delta-as-state): `compose` is the group operation, `inv` the
    negation. -/
def D (g : Kit.Additive A A) (s : Stream A) : Stream A :=
  fun t => match t with
    | 0 => s 0
    | t + 1 => g.compose (s (t + 1)) (g.inv (s t))

/-- Integration: the cumulative fold from the first entry — the
    replay operator. -/
def I (g : Kit.Additive A A) (s : Stream A) : Stream A :=
  fun t => match t with
    | 0 => s 0
    | t + 1 => g.compose (I g s t) (s (t + 1))

@[simp] theorem D_zero (g : Kit.Additive A A) (s : Stream A) : D g s 0 = s 0 := rfl

@[simp] theorem D_succ (g : Kit.Additive A A) (s : Stream A) (t : Nat) :
    D g s (t + 1) = g.compose (s (t + 1)) (g.inv (s t)) := rfl

@[simp] theorem I_zero (g : Kit.Additive A A) (s : Stream A) : I g s 0 = s 0 := rfl

@[simp] theorem I_succ (g : Kit.Additive A A) (s : Stream A) (t : Nat) :
    I g s (t + 1) = g.compose (I g s t) (s (t + 1)) := rfl

/-! ## The round trips -/

/-- The one group rearrangement both directions need: adding `y` then
    cancelling `x` leaves `y` — assoc + comm + the inverse law. The
    small generic hand lemma (01-core §7). -/
theorem compose_inv_cancel (g : Kit.Additive A A) (x y : A) :
    g.compose (g.compose x y) (g.inv x) = y := by
  rw [g.composeComm (g.compose x y) (g.inv x), ← g.assoc, g.invLeft,
    g.composeNopLeft]

/-- `I ∘ D = id`: replaying the journal reconstructs the state stream
    (the event-sourcing law). -/
theorem I_D (g : Kit.Additive A A) (s : Stream A) : I g (D g s) = s := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [I_succ, D_succ, ih, ← g.assoc]
      exact compose_inv_cancel g (s t) (s (t + 1))

/-- `D ∘ I = id`: differentiating the integral recovers the changes. -/
theorem D_I (g : Kit.Additive A A) (s : Stream A) : D g (I g s) = s := by
  funext t
  induction t with
  | zero => rfl
  | succ t =>
      rw [D_succ, I_succ]
      exact compose_inv_cancel g (I g s t) (s (t + 1))

/-! ## THE dI ISO (01-core §4: the carrier, not a bare theorem pair) -/

/-- **THE D/I ISO**: integration and differentiation are a true
    bijection on streams, packaged as the correspondence kit's
    `Kit.Iso` (`to := I`, `inv := D`). Both directions are the LANDED
    laws above — nothing is re-proved here; the Iso VALUE is the
    carrier discipline (a crossing declares its grade, and Iso — both
    round trips — is exactly what the first-entry convention buys).
    The symmetric iso (swap `to`/`inv`) is the same structure; one
    direction is named. -/
def dI (g : Kit.Additive A A) : Kit.Iso (Stream A) (Stream A) :=
  Kit.Iso.mk (I g) (D g) (I_D g) (D_I g)

end Machines
