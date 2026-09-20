/-
# Dbsp.Determinism — the hash-chained event log (the replay-integrity spine)

The determinism-spine design (port-audit #9): a hash-chained event log
over an ABSTRACT `combine`, replayed by an ABSTRACT `step` — the
ledger-replay story at the level of its laws, with no concrete hash or
event type fixed (the consumers instantiate; theorems hold for all).

The complement to `Dbsp.Replicas`: THERE the claim was that delta
application is the abelian-group sum, so arrival ORDER cannot matter
(replicas converge). HERE order is the artifact — the event log is a
SEQUENCE (doctrine §8: protocols are sequences) — and the chain hash
binds it: each event's hash covers every event before it. The two
together are the replication story: deltas reorder freely under the
group law; the event chain pins the order the replay must see.

The theorems (all over ABSTRACT `step`/`combine` — no instance debt):

- `replay_append`: checkpoint + tail = full replay — the HOT-RELOAD
  law (reload replays the post-checkpoint tail from the snapshot
  state; it computes exactly the full-log replay).
- `chainHash_append`: the checkpoint hash seeds the tail's chain —
  the extension law that makes the hash a CONTENT ADDRESS for the
  whole prefix.
- `same_chain_same_spine`: equal logs give equal hashes AND equal
  replayed states — the same-chain ⇒ same-replay theorem. The replayed
  state is a function of the chain alone; `step` receives no ambient
  state, no clock, no host read (the type enforces the design).
- `hash_divergence_detects`: different chain hashes prove different
  chains — the tamper/divergence detection a replica's pinned
  (state, hash) checkpoint gives for free.

Deliberate scope: no injectivity claim for `combine` (hash COLLISION
means equal hashes do NOT prove equal chains — the module only claims
the sound direction, detection, never hash-equality-as-identity).
-/

module

public import Dbsp.Replicas

-- W5.4 module discipline: all declarations public; bodies exposed
-- (defs/abbrevs/instances must reduce across module boundaries).
@[expose] public section

namespace Dbsp.Determinism

variable {Event State : Type}

/-! ## The two folds (abbrevs over core's `List.foldl`)

The hand-rolled structural recursions are gone: `replay`/`chainHash` are
`abbrev`s over `List.foldl`, so the spine laws CITE the core lemmas
(`List.foldl_append`) instead of re-proving them by induction. -/

/-- Replay: fold the events LEFT through `step`, from the initial
    state. Pure — the determinism spine's design constraint is HERE:
    `step` sees only (state, event). -/
abbrev replay (step : State → Event → State) (s : State) :
    List Event → State :=
  List.foldl step s

/-- The chain hash: fold `combine` LEFT from the seed. The hash of
    position k covers events 0..k-1 — the ledger's tamper-evidence. -/
abbrev chainHash (combine : UInt64 → Event → UInt64) :
    UInt64 → List Event → UInt64 :=
  List.foldl combine

@[simp] theorem replay_nil (step : State → Event → State) (s : State) :
    replay step s [] = s := List.foldl_nil

@[simp] theorem replay_cons (step : State → Event → State) (s : State)
    (e : Event) (rest : List Event) :
    replay step s (e :: rest) = replay step (step s e) rest := List.foldl_cons

@[simp] theorem chainHash_nil (combine : UInt64 → Event → UInt64)
    (seed : UInt64) : chainHash combine seed [] = seed := List.foldl_nil

@[simp] theorem chainHash_cons (combine : UInt64 → Event → UInt64)
    (seed : UInt64) (e : Event) (rest : List Event) :
    chainHash combine seed (e :: rest) = chainHash combine (combine seed e) rest :=
  List.foldl_cons

/-! ## The spine laws -/

/-- THE HOT-RELOAD LAW: replaying the tail from the checkpoint state
    computes exactly the full-log replay. A reload replays only the
    post-checkpoint events and lands on the same state the original
    run reached. -/
theorem replay_append (step : State → Event → State) (s : State)
    (pre post : List Event) :
    replay step (replay step s pre) post = replay step s (pre ++ post) :=
  (List.foldl_append (f := step) (b := s) (l := pre) (l' := post)).symm

/-- THE CHAIN-EXTENSION LAW: the checkpoint hash seeds the tail's
    chain — `chainHash` of the whole log is computable from the
    checkpoint hash + the tail, without re-reading the prefix. -/
theorem chainHash_append (combine : UInt64 → Event → UInt64) (seed : UInt64)
    (pre post : List Event) :
    chainHash combine (chainHash combine seed pre) post
      = chainHash combine seed (pre ++ post) :=
  (List.foldl_append (f := combine) (b := seed) (l := pre) (l' := post)).symm

/-- THE DETERMINISM-SPINE THEOREM: equal chains give equal hashes AND
    equal replayed states — the replayed state is a function of the
    chain alone. Two replicas that receive the same event log and
    start from the same state agree on BOTH the state and the chain
    position — the agreement a checkpoint handshake verifies. -/
theorem same_chain_same_spine (combine : UInt64 → Event → UInt64)
    (seed : UInt64) (step : State → Event → State) (s : State)
    (log log' : List Event) (h : log = log') :
    chainHash combine seed log = chainHash combine seed log'
      ∧ replay step s log = replay step s log' := by simp [h]

/-- DIVERGENCE DETECTION: different chain hashes prove different
    chains — a replica pinning (state, hash) at a checkpoint detects
    any tampering or reordering of the log it received. The sound
    direction only: equal hashes do NOT prove equal chains (combine
    is not assumed injective — collisions are possible, never claimed
    away). -/
theorem hash_divergence_detects (combine : UInt64 → Event → UInt64)
    (seed : UInt64) (l l' : List Event)
    (h : chainHash combine seed l ≠ chainHash combine seed l') : l ≠ l' := by
  intro he
  exact h (he ▸ rfl)

end Dbsp.Determinism

end -- @[expose] public section
