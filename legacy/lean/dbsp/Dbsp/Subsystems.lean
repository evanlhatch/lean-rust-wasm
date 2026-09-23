/-
# Dbsp.Subsystems — ownership: lean/dbsp/Dbsp/Subsystems.lean; aggregates
Dbsp.Circuit + the §4.3 D/I readings (Journal/Checkpoint/hotreload/
replica-divergence) for consumers. Narrative moved to notes/dbsp-subsystems.md.
-/

module

public import Dbsp.Circuit

-- Module discipline: all declarations public; bodies exposed
-- (defs/abbrevs/instances must reduce across module boundaries).
@[expose] public section

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
    Dbsp.Circuit; re-exported here so the §4.3 surface is one import.) -/
abbrev hotreload_incrementalize_ok := @incrementalize_ok

/-- Replica divergence cancels: if replicas A and B see histories that differ
    by the zset `δ` at tick t, then re-integrating the journal difference
    makes them agree — the reconvergence algebra is group subtraction.
    Stated pointwise: (A + δ) - δ = A. This is the convergence story at the
    stream level; the ordered-delta-arrival version is `Dbsp.Replicas`. -/
@[cert] theorem replica_divergence_cancels (s δ : Stream a) (t : Nat) :
    (I (Journal s) + I (Journal δ) - I (Journal δ)) t = I (Journal s) t := by
  simp [Pi.add_apply, Pi.sub_apply]

end Dbsp

end -- @[expose] public section
