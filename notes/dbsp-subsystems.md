# Dbsp.Subsystems — the §4.3 D/I readings (narrative, moved from the module)

Narrative for `lean/dbsp/Dbsp/Subsystems.lean`. The module stays an
import aggregator (public import of `Dbsp.Circuit` + the readings below
re-exported for consumers); this prose used to be the module's doc-comment
and moved here 2026-12 so the module carries only a stub header. Live
declarations still live in the module; the facts below are the READINGS
those declarations cite.

The §4.3 claim, made into types and theorems:

- **Journal = D(state stream).** `Journal s := D s`. Completeness is
  `derivative_integral`: replaying the journal from zero reconstructs the
  world. Invertibility the other way is `integral_derivative`.
- **Checkpoints = partial I.** `sumVals s (n+1)` is the state after n deltas
  — the checkpoint. Resumption from a checkpoint is the journal from the
  cutover tick onward (`checkpoint_is_state`, this module — the world at
  tick t is the checkpoint, the integral of the journal).
- **Hot-reload-by-replay = the same input stream through a new circuit** —
  `incrementalize_ok` (Dbsp.Circuit) is the license: the reloaded
  incremental circuit computes the same function of the same journal.
- **Replica consistency = group subtraction.** A divergence is a zset, and
  re-integrating it cancels (`replica_divergence_cancels`) — the netcode
  reconvergence algebra. (An earlier `replica_consistent` here was a
  syntactic-reflexivity theorem — `I (Journal s) t = I (Journal s) t` —
  deleted as vacuous, 2026-12 quality pass; the genuine convergence
  content — same deltas in any order — lives in `Dbsp.Replicas`,
  `two_replica_converge`/`batch_order_irrelevant`.)

These are READINGS: the proofs are one-liners because the work was done in
Linear/Incremental. The value is the named surface the engine cites.
