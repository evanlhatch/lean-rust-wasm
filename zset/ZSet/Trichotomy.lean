/-
# ZSet.Trichotomy — the command/delta/event trichotomy, as data (03 §7)

Owned by: the ZSet agent (the mandate tree, `zset/`).

The five questions (notes/v3/01-core.md):
- **Root**: Change (01 §2) — the delta ladder's operational half; the
  EVENT's causality reaches into TraceModel (01 §3: occurrence identity
  is a TraceModel concern carried ON the event, not collapsed into Δ).
- **Carrier grade**: plain data — the trichotomy must NOT collapse, so
  the three concepts get three DIFFERENT types, and the conflations are
  the tested negatives (ZSetTests).
- **Spine reading**: the journal is the spine's append-only event log
  shape (accumulate-then-read), at seed size.
- **Ladder rung**: n/a — types, not a Change instance (the DELTA rung
  is ZSet's own, one level down).
- **Gate rows**: the axiom report + the trichotomy's discipline pins
  in ZSetTests (net-zero ≠ nothing happened, at the data level).

## THE FORBIDDEN CONFLATIONS (03 §7 — each pinned in ZSetTests)

1. **net-zero ≠ nothing happened**: a DELTA that adds to zero is the
   SAME delta as `zero` (signed addition), but the EVENT LOG that
   produced it is NOT empty — the delta erases intermediate history,
   the log does not. Collapsing them deletes the audit trail.
2. **a COMMAND is not a DELTA**: a command is REQUESTED intent — it can
   fail (be refused at the transaction boundary) or no-op. Only the
   ACCEPTED net change is a delta. `Command.accept` here is the
   trivially-total acceptor; the refusing boundary (constraint checks,
   03 §8's violation relations) arrives with its first consumer.
3. **an EVENT is not its label/intent**: the same intent occurring
   twice is TWO events (`occId` — occurrence identity). Without it,
   replay/delivery cannot dedup (03 §7: signed addition commutes but is
   NOT idempotent — replay needs event identity or dedup).
4. **signed addition is not idempotent**: `add d d ≠ d` in general
   (pinned in ZSetTests via `add_self_eq_zero`). Treating a delta as a
   set (idempotent merge) silently drops legitimate doubling.

The journal stays causal; the Z-set is a PROJECTION of it.
-/

import ZSet.Basic

namespace ZSet

variable [ck : CanonKey α] [DecidableEq α]

/-- A COMMAND: requested intent — a raw, UN-canonicalized change
    request. Deliberately NOT a `ZSet`: the request's order and its
    intermediate sums are history the delta must not presuppose, and
    the command may be REFUSED (no delta at all) or no-op. -/
abbrev Command (α : Type) [CanonKey α] [DecidableEq α] : Type :=
  List (α × Int)

/-- The acceptor: requested intent → accepted net change. The seed's
    boundary is trivially total (ZSet addition cannot refuse); a real
    transaction refuses at the validity boundary (03 §7: signed deltas
    may transiently violate — validity is checked after the WHOLE
    atomic batch). Refusal paths land with the first transaction
    consumer (the leftover rule); the type stays honest by naming the
    boundary HERE, at the trichotomy's seam. -/
def Command.accept [CanonKey α] [DecidableEq α] (c : Command α) : ZSet α :=
  fromList c

/-- A DELTA: an accepted NET state change — the trichotomy's middle
    rung. It is a `ZSet`: signed addition commutes, `neg` rolls back,
    and it erases intermediate history (see the conflation pins). -/
abbrev Delta (α : Type) [CanonKey α] [DecidableEq α] : Type :=
  ZSet α

/-- An EVENT: a recorded OCCURRENCE — identity + the causal reference
    to the intent that occurred. `occId` is the occurrence identity:
    the same intent twice is two events. The delta of the event is the
    acceptor's output on its intent (a projection, never the event
    itself). -/
structure Event (α : Type) [CanonKey α] [DecidableEq α] where
  /-- Occurrence identity: distinguishes two occurrences of the same
      intent (an event is not its label — 01 §3). -/
  occId : Nat
  /-- The causal reference: which requested intent occurred. -/
  intent : Command α

omit [CanonKey α] [DecidableEq α] in
/-- Occurrence identity's teeth: different `occId`s are different
    events (the trichotomy's pin — no deriving-needed equality). -/
theorem Event.occId_ne {α : Type} {ick : CanonKey α} {ideq : DecidableEq α}
    {e1 e2 : Event α} (h : e1.occId ≠ e2.occId) : e1 ≠ e2 := by
  intro hh
  exact h (congrArg (fun e => e.occId) hh)

/-- The event's delta — a PROJECTION of the event (the log stays
    causal; the Z-set is its net). -/
def Event.net [CanonKey α] [DecidableEq α] (e : Event α) : Delta α :=
  e.intent.accept

end ZSet
