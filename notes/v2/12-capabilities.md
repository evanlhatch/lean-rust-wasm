# 12 — The capabilities (concrete specs for the big additions)

Each capability here is specified to the point an agent can build its first
vertical slice: the types, the kit home, the generator hook, the acceptance
test, and the guards that keep it honest.

## 1. Effects: "what this code may touch" as type-level data

**Purpose.** Collapse the five scattered `reads`/`writes`/GuestBan/determinism/
purity axes into ONE closed lattice on functions, checked at elaboration, and
lowered to the WIT capability set. Composition joins effects; an over-
permissive composition fails to elaborate.

```lean
inductive Effect where
  | read  (name : String)          -- a schema column/resource read
  | write (name : String)          -- a schema column/resource write
  | guestCap (c : Capability)      -- a closed capability token (WIT)
  | hostIO                          -- host capabilities (non-guest)
deriving DecidableEq, BEq, cmp

-- the lattice: effects are a set; order = subset; join = union.
abbrev EffectSet := List Effect        -- canonical: sorted by cmp, dedup
def EffectSet.le (a b : EffectSet) : Prop := a ⊆ b
def EffectSet.join := union

structure CapabilityRow where
  fn       : Name
  effects  : EffectSet
  derived_from : Option Name   -- "reads/writes derived from the registry item"

-- the check: a function's declared effects are a SUPERSET of its body's
-- needed effects; composition = join; a violated bound fails to elaborate
-- (a defaulted proof field on the composition, or an instance gate).
class HasEffects (f : α → β) where
  effects : EffectSet
```

**Seed:** the update lane's derived `reads`/`writes`, `UpdatePure.volatileFree`,
`FuncSem.determinism`, and the GuestGate ban column. Design notes:

- The effect row for schema functions is DERIVED from the registry item
  (record field accesses known at registration) — never hand-written.
- The lattice stays CLOSED per app (a closed `Capability` inductive); the
  kernel cone stays open (new capabilities = new enum cases).
- Guest boundaries: the guest's allowed touches ARE its effect set; the
  dialect with the GuestBan column means the ban becomes one closed axis.
- WIT lowering: the world's capability set is the join of the exported
  functions' rows.

**Kit home:** schema-core (the lattice + derivation); the check lives in the
Statement kit (a `HasEffects`-certified composition is a Statement, mounts =
elaboration gate + WIT lowering + guest ban).

**Acceptance:** an update whose body reads a column its row doesn't declare
fails to elaborate; two composed functions' rows equal the join; the wasm
world's imports match the join of export rows; the GuestGate column is
re-expressed as an Effect case.

**Guard:** finite and closed (decidable lattice); derivation over hand tables.

## 2. Liveness: "something good eventually happens" (the machine row's second half)

**Purpose.** Machines prove safety only. Add generated trace predicates over
the enumerated finite machine: eventually / always-eventually / until —
discharged `by decide` over the reachable graph, with counterexample traces as
data.

```lean
inductive TraceProp where
  | eventually (P : State → Prop)
  | alwaysEventually (P : State → Prop)
  | until (P Q : State → Prop)

-- over the enumerated space: reachability is computable and finite
def reach (m : Machine) (init m.State) : List m.State  -- BFS, visited set

-- the decision: every reachable state (or the trace predicate) — decided
def evalTraceProp (m : Machine) (init : m.State) (tp : TraceProp) : Bool
```

**Generator hook:** `machine!` with the `states:` clause already emits the
enumeration + `Trans` table. Extend the entourage to emit a
`<m>_liveness` battery: rows `"eventually <target> from <state>"` +
`"always-eventually <…>"` where true, each a theorem by `by decide` over
`evalTraceProp`; where a property is FALSE the battery emits a
COUNTEREXAMPLE TRACE (the safe path + the failing state) as data (not a
failure you have to guess).

**Seed:** Convergent (termination variant — keep as the non-finite form),
Fusion bisimulation, `Machines.Testing.conformance`'s state space.

**Kit home:** Machines (`Trace` module) + `CodegenCore.ModelCheck` (below) is
the engine; the machine! entourage is the generator.

**Acceptance:** order/feature-flags/pipeline machines each land a generated
liveness battery; a deliberately-dead end machine's battery fails loudly with
the trace.

**Guard:** finite enumerations only (the `states:` clause); anything else is
theorem territory (Convergent variants).

## 3. Finite model-checking: exhaustive, decide-certified

**Purpose.** The conformance battery samples; model-checking EXHAUSTS. One
primitive: finite enumeration + transition + decidable property →
verified-certificate OR counterexample-trace. Consumed by every entity
machine, every grammar's `unambiguous` (once per reachable state set), every
op table's battery, the cascade's finite schedules.

```lean
namespace CodegenCore.ModelCheck

structure ModelCheck (σ l : Type) [BEq σ] where
  states : List σ
  init   : σ
  step   : σ → l → Option σ        -- total on the enumerated space
  labels : List l
  prop   : σ → Bool
  -- result:
  --   .verified cert : ∀ s ∈ reachable-board, prop s = true
  --   .counterexample (trace : List l) (bad : σ) : path from init → bad, ¬ prop bad
def run   (mc : ModelCheck σ l) (max : Nat) : Either bad path .
def certificate (mc) : Optional (proof-of-verify or trace)  -- decide-backed

-- the machine! generator: batteries become "every reachable state satisfies Inv"
-- via run over the enumerated table; grammars: unambiguous + reachability;
-- op tables: both-direction property batteries.
```

**Rules (keep it honest):**

- FINITE-ONLY. Model-checking applies where the space is enumerated. Do not
  extend to infinite (that is theorem/Convergent work).
- Certificates are decide-backed/generated; the verdict is a THEOREM per
  battery (e.g. "every reachable state of the order machine satisfies
  terminal_only_reset"), not a sampled pass.
- CI budget-bound: `max` bounds the board; the bound is data and the battery
  reports "board truncated" if hit (never a silent partial).

**Kit home:** `CodegenCore.ModelCheck` (C0 — core-only: finite sets, decide,
lists). The machine! entourage and the grammar `unambiguous` field are its
first consumers.

**Acceptance:** all three existing machines + one grammar land exhaustively-
verified batteries with certificates; a sabotaged machine/grammar produces a
counterexample trace that fails loud.

**Guard:** finite-only + budget-bound + certificate-only verdicts.

## 4. Shrinking (minimal counterexamples, the PBT closure)

**Purpose.** A failing sweep should report the MINIMAL counterexample, not the
first draw. `Spec` gains an optional shrink strategy; on failure the harness
walks the shrink lattice to a local minimum and ships the minimal case +
the shrink path.

```lean
structure Spec where
  name      : String
  prop      : (α : Type) → [Sampleable α] → (α → Bool)   -- or per-family
  shrink    : Option (α → List α) := none   -- smaller candidates
  negatives : List (String × (α → Bool))    -- must-FAIL controls; ≥2 by decide
  numInst   : Nat := 200
  seed      : Option Nat := some 0xD3C
-- result: pass | fail (minimalCounterexample, shrinkTrace) | vacuous
```

**Seed:** bolero's Rust-side TypeGenerator/shrink; Specimen's LCG discipline;
our current PropSpec.

**Kit home:** TestKit (`Shrink.lean`); generators provide the shrink strategy.

**Acceptance:** a deliberately failing suite reports the minimal case + the
shrink path; seeded replays byte-identical.

**Guard:** shrink is a strategy parameter (no global search); deterministic.

## 5. Impact-aware gating (the change-proportional dev loop)

**Purpose.** The gates re-verify everything (~50 min). Restore and wire the
changed-declaration analysis (gonzalgo): given the change set, compute the
affected modules/artifacts and run only their gates.

```lean
-- in the gates exe:
structure ChangeSet where
  modified  : List FilePath   -- from the VCS diff
  deleted   : List FilePath

def affectedModules (cs : ChangeSet) : List Name   -- import-closure walk
def affectedArtifacts (cs) : List (Emitter × Spec) -- artifacts whose spec/emitter changed
-- gates accept `--affected <file>` and run only impacted checks;
-- the full run remains the default for CI/main.
```

**Wiring:** gates exe subcommand flags; the justfile passes the change set; the
byte-tie runs only for affected artifacts; axiom/kernel checks run only for
affected roots. The full run stays as the release gate.

**Acceptance:** a one-line change in a spec module re-checks only that
package's artifacts in measurable time; the full run still passes.

**Guard:** correctness of the affected-set is the invariant — a change that
could affect X must include X (the analysis is conservative; never under-
reports).

## 6. The causal trail (observability as a shipped capability)

**Purpose.** From any failing verdict, walk the causal chain as DATA: which
spec row produced which artifact, which obligation attested it, which duel row
disagreed, with what category. Debugging becomes a query, not a session.

```lean
inductive CausalStep where
  | specRow      (lane : Lane) (row : String)          -- registry item
  | artifact     (path : String) (generated : Bool)    -- the generated file
  | oblig        (label : String) (tier : Tier) (evidence : Evidence)
  | gateVerdict  (gate : String) (status : Verdict)
  | duel         (row : oracleRowId) (divergence : Divergence)
structure Trail where
  steps : List CausalStep   -- spec → artifact → oblig → verdict → duel
```

**Seeds:** the oracle's `explain` (row → path → divergence), the E-code
registry, `SpanSpec`/spans, GatewayX. Extend: the artifact headers already
carry the spec-source + hash — the trail connects header → spec row → gate →
duel. The E-code is the trail's spine (04 §4).

**Kit home:** TestKit `Verdict` + a new `Trace` module in codegen-core (the
trail record + render); the oracle/gates emit trails, not just verdicts.

**Acceptance:** a sabotaged artifact produces a trail ending in the
divergence category + the responsible spec row; the E-code resolves in
Lean/Rust/wasm/gate logs identically.

**Guard:** trails are DATA (indices + ids), never free-form strings.

## 7. Session-typed boundaries (the guest boundary's contracts)

**Purpose.** The once/stream/async export contracts as session types; the
adapter generated from the session; runtime can't misread the wire because the
shape is typed.

```lean
-- extends Machines.Session over the boundary:
inductive BoundaryStep (P : Type) where | send (p : P) | recv (p : P)
abbrev Boundary (P) := List (BoundaryStep P)
-- once   : send(flat-result) end
-- stream : send(read) recv(items)* send(done)
-- async  : send(task) recv(callback)
-- the adapter is a fold of the boundary; the WIT shape falls out of it.
```

**Seed:** Machines.Session + IsDualOf, the adapter generator (WasmBackend's
schema-driven adapters), `FuncSem.delivery`.

**Kit home:** schema-core (the Boundary type + lowering) + wasm-core (the
adapter fold); complements Effect (the outer edge is the capability row).

**Acceptance:** each export's adapter is generated from its boundary; a wrong
boundary (once where stream is declared) fails construction.

**Guard:** boundaries are closed per app (a closed step set); the adapter is a
fold, not a hand shape.

## Priority note

Per the user's direction — build the FINITE MODEL-CHECKING + LIVENESS layer
into the outset (Phase 3 of 11), pair it with the machine! entourage, then the
observability slice (impact gating + causal trail) for the dev loop, then
Effects/Shrinking/Sessions in the type-driven stratum. Each is independently
gated; none waits on another except Effects-on-foundation.
