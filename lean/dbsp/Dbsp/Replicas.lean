/-
# Dbsp.Replicas — delta-CRDT convergence (the replication theorem)

The delta-shaped contracts (`Dbsp.ChangeSpec`) across replicas: each
replica holds a collection and applies deltas AS THEY ARRIVE. If delta
application is the abelian-group addition (patch = +, invert = -), then
replicas that RECEIVE THE SAME DELTAS converge — regardless of ORDER.
Convergence is not an algorithm here; it is the commutativity law of
the group (mathlib's, kernel-checked), applied to replica states.

The theorems:

- `applyDeltas_sum`: delta application IS the group sum — the bridge
  lemma every convergence fact reduces to.
- `two_replica_converge`: two replicas starting from the same state,
  receiving the same two deltas in OPPOSITE orders, end equal — the
  2-replica convergence core.
- `batch_order_irrelevant`: batches arriving in either order converge —
  the N-replica claim at batch granularity (a permutation of the same
  delta multiset sums identically).
- `retract_is_inverse`: a retraction (remove/undo) is the group
  inverse — delta-then-inverse restores the state. The rollback law
  `Machines.Rewind` executes for machine state; here for replica
  collections.

Deliberate scope: deltas are UNORDERED (a set), not causally
broadcast. Causal ordering is the transport's job (the wRPC layer);
the CRDT claim is exactly: ordering does not matter for convergence.
-/

import Dbsp.ZSet
import Mathlib.Tactic.Abel

namespace Dbsp.Replicas

open Dbsp

/-- A replica's state after applying deltas `δ₁ δ₂ …` (in arrival order)
    to the initial state `s`: the group SUM. Application IS addition —
    `ChangeSpec`'s canonical change structure (`patch s δ = s + δ`).
    Noncomputable: the theory-side ZSet (mathlib Finsupp quotients). -/
noncomputable def applyDeltas (s : ZSet A) (δs : List (ZSet A)) : ZSet A :=
  δs.foldr (· + ·) s

/-- Delta application is the group sum over the initial state — the
    bridge lemma: every convergence fact below reduces to the laws of
    `+` through this. -/
theorem applyDeltas_sum (s : ZSet A) (δs : List (ZSet A)) :
    applyDeltas s δs = s + δs.sum := by
  induction δs with
  | nil => simp [applyDeltas]
  | cons δ rest ih =>
      -- the reassociation δ + (s + Σ) = s + (δ + Σ) is abelian-group
      -- arithmetic — `abel` closes it (the group laws ARE the proof)
      simp only [applyDeltas, List.foldr_cons]
      rw [ih]
      abel

/-- THE 2-replica convergence core: same start, same deltas, opposite
    arrival orders — equal end states. This is the whole CRDT claim for
    two replicas; the group's commutativity does the work. -/
theorem two_replica_converge (s δ₁ δ₂ : ZSet A) :
    applyDeltas s [δ₁, δ₂] = applyDeltas s [δ₂, δ₁] := by
  rw [applyDeltas_sum, applyDeltas_sum]
  abel

/-- Batches arriving in either order converge: the N-replica claim at
    batch granularity. A permutation of the same delta multiset sums
    identically — the transport may reorder freely. -/
theorem batch_order_irrelevant (s : ZSet A) (δs δs' : List (ZSet A)) :
    applyDeltas s (δs ++ δs') = applyDeltas s (δs' ++ δs) := by
  rw [applyDeltas_sum, applyDeltas_sum, List.sum_append, List.sum_append]
  abel

/-- A retraction IS the group inverse: applying a delta then its
    inverse restores the original state — the rollback law
    (`Machines.Rewind` executes it for machine state; here for replica
    collections). -/
theorem retract_is_inverse (s : ZSet A) (δ : ZSet A) :
    applyDeltas (applyDeltas s [δ]) [-δ] = s := by
  rw [applyDeltas_sum, applyDeltas_sum] at *
  simp only [List.sum_cons, List.sum_nil, neg_add] at *
  abel

end Dbsp.Replicas
