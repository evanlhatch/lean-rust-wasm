# 16 — The surface: the two-idiom frontend + the strengthening program

The interface/implementation split, locked. Below the waterline: the
formal machinery (folds, carriers, engines, initiality). Above it:
inherited idioms only — we do not invent idioms; we inherit the two
most intuitive ones and let the obscure mathematics pay out implicitly.

## 1. The two conjugate vocabularies

The fusion bridges (journal = D∘run, replay = I∘journal — PROVED) mean
the stream idiom and the table idiom are two readings of one phenomenon.
The surface presents BOTH; the conjugacy is a theorem, not a metaphor.

**The snapshot idiom** (from SQL/spreadsheets — for STATE):

```lean sketch
table Orders { id : u64 key, customer : ref Customer, total : i64,
               state : OrderState }
forbid NegativeBalance where Account.balance < 0
query Pending := Orders where state = .pending
```

**The stream idiom** (from git/diffs/dbsp — for CHANGE):

```lean sketch
stream OrderEvents      -- the journal: occurrences + identity + order
delta  OrderChanges     -- the net signed bag (the Z-set)
view   Outstanding := integrate (Payments map signedAmount)
on change to Orders …   -- subscriptions are first-class
```

The bridges are NAMED surface constructs: a table IS `integrate` of its
deltas; the delta stream IS `differentiate` of the table; `on change`
is the derivative. One rule to learn — state is the integral of change;
change is the derivative of state — and incremental maintenance, audit,
subscriptions, and replay come IMPLICITLY (the theorems are already
landed underneath).

The honest boundary: streams are for change; unchanging state is not a
stream. "What IS the balance" (table) vs "what HAPPENED" (journal) vs
"what CHANGED" (delta) are three questions with three honest views, and
the toolkit guarantees the three agree (the trichotomy, 03 §7, as types).

## 2. The six-word vocabulary + the compile-to rule

The surface words: **table, key, ref, rule, state, event**. Every
surface construct names which machinery it compiles to, or it does not
exist (the acceptance test):

| Surface | Compiles to |
|---|---|
| `table` | the closed universe + the folds + derived codecs (the description layer) |
| `key`/`ref` | determinacy theorems driving API shape (02 §3) |
| `forbid` | the ℤ-weighted violation relation (∅ ⟺ valid) + the obligation row |
| `query` | the weighted-relation fragment; the weight is a LATER choice (Bool/Nat/ℤ/provenance) |
| `machine` | the machine! entourage + the conformance battery |
| `on`/`emit` | the event/journal lanes (the fusion bridges) |
| `view` | a materialized query (02 §10 — the maintenance equation) |

No surface construct ever exposes a fold, a carrier grade, or an engine.
The developer's mental model is relational+streams; the toolkit's
correctness is categorical; the bridge is the deriving machinery, and
the bridge's faithfulness is the relational engine's theorem.

## 3. The evidence entourage (the weakest-sufficient discipline)

Every declaration's evidence cone is GENERATED, and the generator's
first question is "does the type already carry it?":

1. in the type (unrepresentable) → NO artifact (construction IS the
   evidence — a generated proof of it is waste);
2. decidable over a closed space → the kernel proof (`decide`/`cases`),
   never a sweep;
3. unbounded → the LCG sweep + the mandatory controls + the
   validity-preserving shrinker;
4. behavioral → the duel rows (tested agreement, tier-honest).

The tier is COMPUTED from the evidence kind — the machinery cannot
mislabel. A generated proof whose statement is construction-guaranteed
is a lint finding (evidence redundancy), same discipline as dead code.

## 4. The strengthening program (the model's honest holes)

Ranked; each lands as its own order:

1. **The carrier-as-graph bridge** (cheap, immediate): every carrier
   value (Iso/Retraction/Codec) induces its graph `Rel`; the engine
   runs over graphs. ONE composition tower, the grades riding on top —
   kills the two parallel composition stories (carrier `trans` vs
   `Rel.comp`).
2. **The coalgebraic half** (the roof's other half): the TraceModel
   root has bisimulation-as-stream-equality but no FINALITY — the dual
   of initiality. Land: the unfold/corecursion discipline + the
   finality theorem (behavioral equality IS bisimilarity) + refinement
   between machines as the morphisms. This makes TraceModel as strong
   as Universe; it is the home of impl ≤ spec.
3. **The hyperproperty substrate** (the power jump): `Rel` lifted to
   PAIRS of executions (the product program) + the security observer
   (04 §4's vocabulary exists). Noninterference ("secret changes can't
   alter public outputs") and schedule-independence ("delivery order
   doesn't change the answer") become STATABLE — the properties other
   toolkits can't express.
4. **The description layer's functorial deepening**: `Descr` as a
   pattern functor's fixed point; every deriving handler a fold over
   the functor; one generic correctness theorem instead of per-handler
   proofs. Lands when the handlers multiply (they are landing).
5. **The semantic-profiles lane** (ACTIVATED — the game-engine product
   needs it): phantom-indexed scalar semantics — `Float Deterministic`
   (fixed-point/ordered; codec-legal) vs `Float Fast` (honest about the
   forfeited laws); `Money USD Cents`-shaped profiles erase at runtime.
   This resolves the no-floats exclusion HONESTLY rather than by
   avoidance.
6. **Typed contexts/substitutions** (de Bruijn discipline): the shared
   scoped-binding substrate for every language we build — lands WITH
   the first real language (qlang's retarget / the guest language);
   the leftover rule holds until then.

## 5. The cheap wins (formal-model perspective, unharvested)

1. **The graduation sweep**: five sites graduate to true `Iso` via
   `toImageIso` — the codec (values ≅ accepted bytes), the snapshot
   (registry ≅ canonical text), the machines (`Exec` ≅ runnable tapes —
   `exec_run`/`run_exec` already proved, assembly only), the WIT
   lossless fragment ≅ its image, the ZSet rep ≅ the weight function
   (`weightOfW_inj` is the hard half, landed). Plus the graduation LINT:
   a Retraction/Codec with a decidable image and no iso upgrade is
   strength-left-on-the-table.
2. **Free theorems from initiality, systematically**: any two
   presentations of one walk are equal by `foldTy_unique` with `rfl`
   hypotheses — every future "these two renderers agree" is free.
3. **Reflexivity-as-determinism**: `Kit.Relation`'s diagonal — every
   deterministic interpreter gets its determinism theorem free (landed;
   CITE it per interpreter instead of proving per-site).
4. **The observer-coarsening theorems**: forgetting observations
   preserves claims (the `Below` discipline) — every "the instrumented
   run agrees with the plain run" is an instance.
5. **The additive instance's free projections**: an `Additive` change
   IS unconditionally commuting (`bindComm` landed) — the parallel-
   scheduler discipline for disjoint writers is a citation, not a proof.
6. **The decide-first sweep**: hand scripts over closed finite spaces
   upgrade to kernel proofs (the lint is queued; the upgrades follow it).
7. **The conformance battery's free reach**: every `machine!` gains
   deadlock-freedom + guard-coverage + non-vacuity verdicts by
   construction — the liveness layer's bottom rung costs nothing per
   machine.
8. **The dissolution test**: any module whose theorems re-prove what a
   carrier/ladder/engine instance would give by citation is an audit
   finding — the re-audit loop each wave.

## 6. The game-engine activation (the proof the idioms generalize)

The readings that activated this doctrine (the product's shape):

- **ECS = the data plane, literally**: entities are keys, components
  are tables, systems are queries + updates; change detection IS
  incremental view maintenance; parallel scheduling IS the
  disjointness-commutativity theorem (proved, not hoped).
- **Rollback/replay = the fusion bridges** (landed): journal + D/I +
  event identity.
- **Save versioning = the migration lane**; **the asset pipeline = the
  provenance ledger** (demand sets are the rebuild graph);
  **animation/AI = machine! + the battery**; **frame budgets = the
  cost lane**; **broadphase = materialized queries** (02 §10).
- **The float tension** resolves via §4.5 (the profile lane), never via
  fake laws.

The doctrine's test stands: none of these is a vertical feature; each
is rows + instances of the landed machinery.
