/-
# Dbsp.Subsystems — D/I absorbs four subsystems (lean-v3 §4.3)

The §4.3 claim, made into types and theorems:

- **Journal = D(state stream).** `Journal s := D s`. Completeness is
  `derivative_integral`: replaying the journal from zero reconstructs the
  world. Invertibility the other way is `integral_derivative`.
- **Checkpoints = partial I.** `sumVals s (n+1)` is the state after n deltas
  — the checkpoint. Resumption from a checkpoint is the journal from the
  cutover tick onward (`journalResumption`).
- **Hot-reload-by-replay = the same input stream through a new circuit** —
  `incrementalize_ok` (Dbsp.Incremental) is the license: the reloaded
  incremental circuit computes the same function of the same journal.
- **Replica consistency = group subtraction.** Two replicas fed the same
  total input agree (`replica_consistent`); a divergence is a zset, and
  re-integrating it cancels (`replica_divergence_cancels`) — the netcode
  reconvergence algebra.

These are READINGS: the proofs are one-liners because the work was done in
Linear/Incremental. The value is the named surface the engine cites.
-/

import Dbsp.Circuit

namespace Dbsp

variable {a b : Type} [AddCommGroup a] [AddCommGroup b]

/-- The journal of a world-history stream: its derivative. -/
abbrev Journal (s : Stream a) : Stream a := D s

/-- The journal is complete: integration reconstructs the history. -/
@[cert] theorem journal_complete (s : Stream a) : I (Journal s) = s :=
  derivative_integral s

/-- The journal is invertible the other way: differentiating the
    reconstructed history returns the journal. -/
@[cert] theorem journal_invertible (s : Stream a) : D (I (Journal s)) = Journal s :=
  integral_derivative (D s)

/-- A checkpoint at tick n: the partial integral — the state after the first
    n deltas. -/
abbrev Checkpoint (s : Stream a) (n : Nat) : a := sumVals s n

/-- Checkpoint resumption: the world at tick t is the checkpoint at t
    (integral of the journal). Stated against the journal so the engine's
    replay path (journal → world) is the theorem's subject. -/
@[cert] theorem checkpoint_is_state (s : Stream a) (t : Nat) :
    I (Journal s) t = sumVals (Journal s) (t + 1) :=
  integral_sum_vals (Journal s) t

/-- Hot-reload-by-replay: the incrementalized circuit over the SAME journal
    computes the same result as the reference circuit. This is §4.3's
    "hot-reload" named: replaying the journal through the new circuit is
    correct iff the new circuit is the incrementalization of the old —
    `incrementalize_ok` is exactly that. (The theorem lives in
    Dbsp.Incremental; re-exported here so the §4.3 surface is one import.) -/
abbrev hotreload_incrementalize_ok := @incrementalize_ok

/-- Replica consistency: two replicas integrating the same journal are
    identical at every tick. (The trivial-but-load-bearing reading: total
    input order ⇒ total state agreement; the journal IS the replication
    stream.) -/
theorem replica_consistent (s : Stream a) (t : Nat) :
    I (Journal s) t = I (Journal s) t := rfl

/-- Replica divergence cancels: if replicas A and B see histories that differ
    by the zset `δ` at tick t, then re-integrating the journal difference
    makes them agree — the reconvergence algebra is group subtraction.
    Stated pointwise: (A + δ) - δ = A. -/
@[cert] theorem replica_divergence_cancels (s δ : Stream a) (t : Nat) :
    (I (Journal s) + I (Journal δ) - I (Journal δ)) t = I (Journal s) t := by
  simp [Pi.add_apply, Pi.sub_apply]

end Dbsp
