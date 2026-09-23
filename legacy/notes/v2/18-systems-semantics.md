# 18 — Systems semantics: trace sets, refinement, fairness, contracts

The TLA+/Dafny/Alloy gap-closer: the primitives that make it possible to say
"this SYSTEM is correct" not just "this machine is safe". Every capability
here is generated over finite structures, decide-backed, and consumed by the
batteries, the duels, and the gates — never re-derived per feature.

## 0. The property taxonomy (Alpern–Schneider, as the doctrine)

Every claimed property is classified, and the classification lives IN the
battery row data:

```lean
inductive PropertyKind where
  | safety    -- "nothing bad ever happens"  (nothing-bad: []-guarded)
  | liveness  -- "something good eventually happens"
  | fairness  -- "if a transition is enabled often enough, it fires"
  | refinement -- "system A behaves within system B"
  | contract -- "under assumption A, guarantee G holds on the boundary"
```

Rule: a battery/property row carries its kind; the taxonomy is enforced by the
kind's home (safety → machine invariants; liveness/fairness → trace props;
refinement → the refinement kit; contracts → boundary/function statements).

## 1. Trace sets and refinement (the TLA+ heart we were missing)

**Purpose.** A machine's BEHAVIOR is its trace set — the set of all runs
(interleavings, schedules, environments): the image of `step?` over all label
sequences from the initial states, extended by all environment schedules.

```lean
def TraceSet (m : Machine) : Set (List m.Label)  -- all finite runs from init

-- refinement = trace inclusion (and the CONTRACT of conformance):
def refines (a b : Machine) : Prop := TraceSet a ⊆ TraceSet b

-- different state spaces: refinement via a coupling/abstraction map
structure RefinementMap (m₁ m₂ : Machine) where
  -- the coupling invariant (spec vs impl)
  coupling : m₁.State → m₂.State → Prop
  forward/backward : each m₁ step maps to an m₂ (or m₂↦m₁) step under coupling
```

- For FINITE machines, `TraceSet` and `refines` are decidable/bounded: the
  predicate is generated, and the refinement battery is a `by decide`
  check over the enumerated space.
- The classic uses fall out as INSTANCES:
  - deterministic equivalence: bisimilarity ≅ equal trace sets (Fusion);
  - Compose (product): interleavings = the shuffle closure (language of the
    product);
  - Sim: the schedule CHOICE selects the trace; `Schedulable` ⇔ the set is
    nonempty;
  - spec vs impl: a hand impl refines the spec iff `TraceSet impl ⊆
    TraceSet spec` under the coupling map — the Dafny-style "code satisfies
    spec" question, but with generation making it checkable.
- The generator: `machine!`/`derive` emits the `traceSet`-bounded analysis +
  the refinement battery for two-machine compositions.

**Kit home:** Machines (`Trace`, → `Refinement`) — a new small theory module;
the finite versions ride ModelCheck (12 §3).

**Acceptance:** (i) two deterministic machines whose product admits both
orders have equal trace sets and refines-each-other battery green; (ii) a
hand impl (e.g., the guest body) under a coupling map passes
`refines impl spec` or the battery reports the discriminating trace.

**Guard:** finite spaces only for the decidable battery; infinite
state spaces → theorem territory (the refinement map is a hand theorem,
generated-incentive but not decide).

## 2. Fairness and stuttering (the temporal completion)

**Purpose.** TLA+ specs are meaningful because they are invariant under
STUTTERING steps and can express FAIRNESS.

- **Stuttering invariance**: adding a "do nothing" step changes no trace set
  (the stutter identity — every spec is stutter-closed). Generated battery:
  `TraceSet (with INSERTED stutter) = TraceSet` for any machine.
- **Fairness** (weak/strong, finite): a transition that is continuously (weak)
  or infinitely-often (strong) ENABLED eventually fires. Over the enumerated
  space this is a Boolean + decide battery per machine: "event `retire` is
  strongly fair: if enabled infinitely often, it fires."
- The generator: `machine!` emits the `stutter_closed` + `fairness` rows
  with the classification (18 §0).

**Acceptance:** the stutter battery is green for any machine; a machine with
an enabled-live transition that never fires FAILS its strong-fairness battery
loudly (it should — that is a real deadlock/livelock finding in the TLA+
reading).

**Guard:** finite spaces; fairness is a property row (data), never a faction
attached to a proof.

## 3. Assume/guarantee boundaries (open systems)

**Purpose.** A boundary to an environment is an A/G pair: the component
ASSUMES the environment's input contract and GUARANTEES its output contract.

```lean
structure AGBoundary (P Q : Type) where
  assume    : P → Prop    -- what the environment must provide (a Statement)
  guarantee : P → Q → Prop -- what the component promises (a Statement)

-- the composition rule: two components compose when G₁ ⇒ A₂ (per wire), and
-- the composed boundary's guarantee = the joined effect row (12 §1).
def composeAG (b₁ b₂) (h : b₁.guarantee ⇒ b₂.assume) : AGBoundary …
```

- Boundaries ARE the sessions (12 §7) + the effect rows (12 §1): the A/G is
  the semantic content of the wire; the session is its shape; the effect row
  is its side.
- Assumptions/guarantees are Statements: mounted as gates (at the boundary),
  checked by the duel (replay), and refused by the what-if inspector when the
  assumption is violated.

**Acceptance:** a guest fn's input contract is an assumption; a spy/what-if
run that violates the assumption is REFUSED with the E-code; two components
that compose by the rule share the guarantee verification.

**Guard:** A/G pairs are closed per boundary (the assumption is a
Statement in the archive — no free-form strings).

## 4. Function contracts (Dafny-style, made checkable)

**Purpose.** Structural (pre/post) on guest functions:

```lean
structure FnContract where
  fn        : Name
  requires  : Statement (input-tuple)  -- checked at the boundary
  ensures   : Statement (input-tuple → output)  -- checked on replay/duel
```

- `requires` mounts as a gate at the boundary (a violating call is refused,
  loud); `ensures` mounts on the duel (a replay that yields a violating
  output fails) and flows into the property battery rows.
- Contracts compose with the effect row: `requires`/`ensures` can mention
  read columns only (12 §1 discipline).

**Acceptance:** a fn whose contract is violated by a capacity-propagation
end-to-end (boundary refusal → duel verdict) is a red gate; a correct one
is green with the Classification rows (18 §0).

**Guard:** contracts are Statements (05 §1) — sound, closed evidence,
mounted; never free-form predicates on the wire.

## 5. The generator hooks (what an agent does)

- `machine!` entropy grows: states/`Trans` → + stutter-closed battery, +
  fairness rows, + (for a two-machine device) the refinement battery.
- `schema_fn` grows: `requires`/`ensures` rows (as Statements); the boundary
  mount + duel rows generated.
- `boundary`/provisional sessions grow: A/G pairs as data; compose rule
  checked at elaboration.
- The data-flow of the belt: the five capabilities keep their homes
  (17-foundation-contract §1), but machines/process add the sixth product:
  **behavior semantics** (trace set + refinement + fairness + stuttering)
  for any machine/process declaration — the "declare once, inherit six".

## 6. Acceptance gate (mechanical)

- Two-machine system: trace-set equality battery + the stutter battery green;
  a livelocked variant fails its strong-fairness row with the trace.
- Guest fn: boundary refuses a violates-`requires` call; the duel rows pin
  `ensures`; both flow with the Classification rows.
- Refinement (hand impl vs spec under a coupling map): battery green or the
  discriminating trace data.
- Every new property row carries its `PropertyKind` — a row without the
  classification is a review finding.

## Priority

Trace-set refinement (18 §1) is the missing TLA+ heart — sequence with the
machine work (Phase 3 stays; alternatively appears in Phase 8b "systems
semantics"). Fairness/stuttering (18 §2) and contracts (18 §4) are the
human-visible completions; A/G (18 §3) unifies boundaries/effects/sessions.
Classification (18 §0) is doctrine added at battery-generation time.
