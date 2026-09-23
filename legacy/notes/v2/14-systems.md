# 14 — The toolkit on its own substrate (circuits, machines, dbsp applied to US)

The theory is not just for the product — it is the operating system of THIS
toolkit. Where circuits, machines, and delta algebra apply to our own
generation/build/verify system, use them; never hand-roll a load-bearing
mechanism our own proved machinery already specifies.

## 1. The codegen pipeline as an incremental circuit (impact gating, made principled)

**Purpose.** The build is a pipeline of stages (reflect → check → emulate →
byte-tie → gate). Today every run re-verifies everything. But stages are
functions over the registry: the pipeline IS a `Ckt` — and impact-gated
rebuilds are INCREMENTALIZATION.

- Define the pipeline as a circuit: stage inputs = (registry snapshot, prior
  artifacts), stage outputs = artifacts/gates. `incrementalize_ok` says:
  running stages on deltas = differencing running them on states. The
  `--affected` filter (12 §5) is the delta input; the byte-tie is the
  difference-output check.
- Citation: the emitted driver's "what changed" answers cite
  `incrementalize_ok`-shaped facts for the stage graph — the impact analysis
  is a circuit fact, not a grep heuristic.
- Keep it honest: the stage graph is static and known — a fixed `Ckt` per
  package; only the delta set varies. No dynamic compilation.

**Files:** the pipeline module in the gates/forge driver becomes: stage table
(row: stage name, spec delta it consumes, artifacts it writes, its gate) +
`run` as the circuit fold + a `--affected` delta input. The byte-tie rows and
the provenance ledger (15) read the same table.

## 2. The spec as an event-sourced aggregate

**Purpose.** The One Universe (02 §4) is a STATE; the registry writes are
EVENTS. Make the management stack event-sourced like the product:

- Spec changes = deltas on the Universe value; the committed
  `universe.snapshot` = the INTEGRAL; the breaking diff = D applied to the
  snapshots; the breaking gate = `diffBetween` (13 §2) over spec states.
- Per-lane registration = `append`; replaying the registration log
  reconstructs the snapshot — the snapshot is a fold, never a hand file.
- Consequence: "what did the spec change between commits" is an algebraic
  delta, and migration derivation (13 §1) consumes it directly (the Change
  enum IS the breaking diff's output).

**Files:** Universe.lean gains the event log (`specLog : List SpecEvent`) and
the replay fold; the snapshot writer is the integral; the breaking gate diffs
via `diffBetween`.

## 3. Machinery in the runtime/host

- **Host lifecycle as a machine:** the component runtime's states
  (not-instantiated → instantiating → instantiated → failed) as a machine!
  with the generated battery; backpressure (the mpsc/semaphore contract rows
  already exist — wire them as the runtime's guard vocabulary).
- **Every driver as a machine:** `schema gen`, `gates`, `forge` are stage
  machines already; the sequencing phases themselves (11) are a machine over
  the build — the meta-machine can certify "phase order is respected".
- **CI = the machine** (07 §3): all gates are transitions; keep it that way
  and let model-checking (12 §3) certify the pipeline's own state space is
  reachable/terminating (the finite stage graph).

## 4. Strengthen the circuit model itself

- **Denotational data plane:** the Rel→Ckt lowering is the product edge;
  the honest gaps are KNOWN (aggregate's linear measure operator missing;
  sort/fetch out — top-k theory). State them in the model's header, an
  additive-ctor promise, not a silent hole.
- **Boolean/typed circuits for validators:** the VExpr compiled lane is
  already binary circuits; formalize it as the Ckt instantiation (the
  emitted validators cite the circuit typing, so a validator that can't be
  represented as a circuit fails construction, not at runtime).
- **CEGAR as circuit refinement:** model-checking's counterexample trace +
  the minimal-failing-universe (13 §4) compose into refinement: a failing
  gate refines its abstraction until the culprit is named. Name it CEGAR;
  use the term in code/commits where the loop is implemented.

## 5. Where NOT to apply the substrate (honesty)

- Don't force infinite/stateful semantics into the finite model-checker
  (12 §3 guard). Don't circuit-ify things that are genuinely sequential IO
  (the driver's shell work). The substrate applies to MECHANISMS with a
  dataflow or state shape — registries, stage graphs, lifecycles, protocols —
  not to arbitrary glue.

## Acceptance

- The `--affected` rebuild path is described by a stage table + circuit fold
  (not a custom loop); the full run and the affected run agree on the
  artifacts they share.
- The committed snapshot is provably the integral of the registration log
  (replay = snapshot, cited).
- The host lifecycle is a machine! with a generated battery; the pipeline is
  the machine (07 §3) and model-check certified over the finite stage graph.
