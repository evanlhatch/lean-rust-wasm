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

## 8. Contracts in the function types (the in-type pre/postcondition)

**Purpose.** The function's return TYPE carries the postcondition — a
dependent pair `{ r // P r }` — so a violated precondition or postcondition
fails to elaborate at the call site, host-side, with no runtime check. THE
key fact: Lean erases Prop content at codegen, so the guest artifact is
byte-unaffected (zero wire cost) — the contract is elaboration-time-only.

```lean sketch
-- the in-type form: the result exists only with its proof component
structure Contract (fs : List Field) where
  post : RowVals fs → Prop          -- Prop-only (the guard below)
  pre  : RowVals fs → Prop

def applyOp (op : ContractOp fs) (r : RowVals fs)
    (h : op.pre r) : { res // op.post res }   -- erases to the same bytes
```

**Seed:** the PrePost obligation lane (SchemaLang/PrePost.lean —
`FnContract`/`PrePostClaim`/`PrePostObligation`) + the guest's
proof-erasure boundary. Relationship: the in-type form is the STRONGER
reading for authoring surfaces that can carry it; the PrePost lane stays
for the surfaces that cannot.

**Kit home:** schema-core (the contract-carrying function types); the
discharge is a Statement row (same tier/evidence discipline as the lane).

**Acceptance:** an authoring surface that can carry the in-type form gains
it — a call site violating the precondition fails to elaborate with a
curated error; the guest bytes are UNCHANGED by adding the contract
(byte-tie green without regen).

**Guard:** contracts on guest-compiled paths must be Prop-only — no
computational content in the proof component (erasure is total; a
computational postcondition would break the byte-tie).

## 9. Version-indexed journals (replay-type-safety as structure)

**Purpose.** The journal is indexed by the schema version it replays
against; migration is the TYPED map between the indexed types, not a hand
upcaster that a schema change can silently strand.

```lean sketch
-- the journal carries its schema version in the type
inductive Journal : SchemaVersion → Type where
  | nil  (v : SchemaVersion) : Journal v
  | cons (r : Record v) (j : Journal v) : Journal v

-- migration = the typed map, one per breaking change (13 §1's
-- per-migration preservation obligation rides it)
def migrate (u : Journal v1) : Journal v2
```

**Seed:** SchemaLang/EventSourced.lean (the journal codecs:
`encJournal`/`decJournal?`) + SchemaLang/Migration.lean (`FieldMigration`,
`CompatVerdict`).

**Kit home:** schema-core (the version index + the typed map); consumed by
the data-plane lane (13 §1's migration obligations).

**Acceptance:** an old journal replays only against the matching version —
a mismatch is a type error, not a runtime check; a breaking change yields
the typed migration + its preservation obligation.

**Guard:** the journal's codecs stay on the canonical rep (16 §2's
discipline — journals are explicitly NOT quotiented there); the version
index is host-side only until the wire story is named.

## 10. Composite decidability (one `Decidable` for the whole judgment)

**Purpose.** A compound judgment (a declaration's whole legality) is ONE
decidable instance composed from the components' — so the site discharges
as ONE kernel decide, not a chain of per-part decides each paying kernel
entry.

```lean sketch
-- the components are decidable; the compound reuses them by composition:
instance : Decidable WholeLegality where
  decide := partA.decide && partB.decide && partC.decide
-- the construction site discharges ONCE:
def theDecl : Good := { … , legal := by decide }
```

**Seed:** the machine! entourage's per-component decides (Machines/Dsl.lean
— the generated `DecidablePred <m>.Inv` instance, the labels' `decide`).

**Kit home:** Statement (the compound legality is ONE Statement row; the
evidence is the single decide certificate).

**Acceptance:** a compound-legality site discharges via one `by decide`;
a wrong component fails instance search with A2's curated "why not".

**Guard:** the instance graph stays shallow (09 §1's
`synthInstance.maxHeartbeats` smell) — compose the parts, do not build a
lattice of instances.

## 11. Simproc-registered evaluators (evaluation goals close by `simp`)

**Purpose.** The lane evaluators (`evalV`/`evalRaw` + the codec decoders)
registered as simp procedures, so any proof's evaluation goal discharges
via `simp` — no per-theorem `simp only [...]` incantation restating the
evaluator's equations by hand.

```lean sketch
-- one registration per evaluator; afterwards a ground evaluation
closes by plain `simp` in any proof:
simproc registration for `evalV e row`  (the boxed reading)
simproc registration for `evalRaw e r`  (the 0/1-word reading)
simproc registration for `decVal? t bs` (the codec decoders)
```

**Seed:** SchemaLang/Validate.lean's evaluators (`evalV`, `evalRaw`) +
SchemaLang/CodecValue.lean's decoders (`decVal?`/`decodeValue`).

**Kit home:** schema-core (the registrations live beside the evaluators'
namespaces).

**Acceptance:** an evaluation goal over a ground expression closes by
`simp` alone in a proof that never names the evaluator's equations; the
readings-tie theorems (ExprLang) are unaffected.

**Guard:** simproc-written reductions are kernel-checked anyway — the
theorem stays the authority, the simproc is the accelerator (the axiom
gate covers it; a wrong simproc fails the build, never silently passes).

## 12. Traversable/Foldable for the container shapes (the effectful walk)

**Purpose.** The effectful walk over the value containers stated ONCE per
shape via `traverse` — the Validation-accumulating applicative composes,
so "decode every element, collect ALL errors" is a traverse, not a hand
fold per container.

```lean sketch
-- each container states the walk once (VList shown; VMap/RowVals the same):
def foldVList    {t : Ty} {β : Type} (f : β → Value t → β) (b : β)
    (vl : VList t) : β
def traverseVList {t : Ty} [Applicative F] (f : Value t → F (Value t))
    (vl : VList t) : F (VList t)
-- the consumer composes with Validation (error-ACCUMULATING, not Except's
-- first-error exit): a multi-error decode reports every bad element.
```

**Seed:** SchemaLang/CodecValue.lean's containers (`VList`/`VMap` + the
erase/rebuild pairs) + CodegenCore's `Validation` (the error-accumulating
applicative).

**Kit home:** schema-core (CodecValue's namespaces).

**Acceptance:** a multi-error decode collects ALL errors via one traverse;
the erase/rebuild round-trips (`listToVList_vListToList`, the VMap analog)
still hold.

**Guard:** instances must be law-respecting — the traversable laws stated
and discharged per the ladder. The GADT constraint is why these are hand
shapes, not derivings: nested `List (Value t)` inside the GADT is
kernel-forbidden (CodecValue's header).

## 13. Vector/Fin at the canonical ABI (arity mismatches unrepresentable)

**Purpose.** The guest boundary's flattened args as arity-indexed vectors —
`Vector WasmVal (arity f)` — so a call with the wrong arg count has NO
constructor (ladder rung 1), not a runtime size check at the seam.

```lean sketch
-- the boundary call: the vector's length IS the export's arity
def callExport (f : ExportName) (args : Vector WasmVal (arity f)) : …
-- flattening is the indexed fold; the flat index discipline is
-- SchemaLang's `flatIdxT` (Layout.lean).
```

**Seed:** SchemaLang/Layout.lean's `flatIdxT` + the wasm-backend's
schema-typed adapter generator (WasmBackend: `adapterShape?`/`shapeTys?` —
the R3 generator landed; no new hand shape per export).

**Kit home:** wasm-core (the boundary types); the adapter generator
consumes them.

**Acceptance:** a call with the wrong arg count fails to elaborate (never
at runtime); byte-tie — the WAT emission's bytes unchanged.

**Guard:** byte-tie — the WAT emission's bytes unchanged; the
vectorization is host-side typing only, no new wire shape.

## 14. Middleware (the ordered chain, effect-row-carrying)

**Purpose.** Cross-cutting app behavior as an ordered chain of transformers
`(In → IO Out) → (In → IO Out)`, each layer carrying an effect row (12 §1's
lattice — the layer's row JOINS the composition, never bypasses it). Chain
validity is mechanical: the declared precedences form a poset, and the poset
must have a linear extension — decidable over the finite registry; a cycle
fails to elaborate. The chain's effect row is the JOIN of the layers' rows —
computed, not written.

```lean
-- a middleware: a transformer + the effect row it adds (12 §1's rows)
structure Middleware (In Out : Type) where
  name       : String
  transform  : (In → IO Out) → (In → IO Out)
  effects    : EffectSet                 -- the row this layer adds
  before     : List String               -- precedence: this layer before these
  after      : List String

-- chain validity: the precedence poset has a linear extension (decidable
-- over the finite registry) — a cycle has no constructor at the site:
structure Chain (In Out : Type) where
  layers : List (Middleware In Out)
  linear : hasLinearExtension (layers.map (·.name)) := by decide

-- the chain's effect row is the JOIN of the layers' rows (computed):
def chainEffects (c : Chain In Out) : EffectSet :=
  c.layers.foldr (fun m acc => EffectSet.join m.effects acc) []
```

**Seed:** the splicer-mw fixture (`crates/splicer-mw` — the hand-ordered
chain this replaces) + the effect-row work (12 §1: `EffectSet`/`EffectSet.join`).

**Kit home:** schema-core (beside the Effect lattice — the chain's rows are
that lattice's data); the legality is a Statement row (mounts: the elaboration
gate on chain construction + the WIT capability lowering).

**Acceptance:** a chain whose precedence constraints cycle fails to elaborate
(the `linear` decide fires, cycle named); a chain's effect row equals the join
of its layers' rows, computed from the layers, not hand-declared; the composed
`(In → IO Out)` respects every layer's row bound.

**Guard:** chains are closed per app — a closed middleware registry; the
poset is COMPUTED from the declared precedences, never asserted; layers carry
rows, never raw IO.

**Instance of:** TraceModel (the precedence poset — linear extension is the
causal order's consistency check) + Universe (the effect rows) + Statement
(chain legality).

## 15. Dependency injection (the provider DAG, instantiation as the fold)

**Purpose.** Wiring as a provider DAG: each provider declares what it
provides and what it needs; instantiation IS the topological fold (the
cascade machinery — dbsp's fix, applied to construction). Legality = acyclic
+ every need satisfied — ONE Statement, discharged at construction; a cycle
refuses with the cycle named; a missing provider names the unsatisfied
requirement + the valid space (04 §2). NOTE for the tree: this is the
consumer the deleted `Machines.Foundations.Dag` was missing — the DI
container re-earns the DAG concept here (the leftover rule's redemption path,
01 §4).

```lean
-- a provider: the graph IS the rows, not a side table
structure Provider (α : Type) where
  provides : Name
  needs    : List Name
  build    : Needs (needs) → α     -- the row-typed dependency record

-- legality: acyclic + every need satisfied — ONE Statement over the rows:
structure DiGraph (ps : List Provider) where
  legal : (acyclic ps ∧ everyNeedSatisfied ps) := by decide

-- instantiation = the topological fold (the cascade machinery):
def resolve (ps : List Provider) (want : Name) : Either Diag α
```

**Seed:** the cascade machinery (dbsp's fix over the stage graph) + the
row-typed dependency record (`Needs (needs)` rides the Universe's row types).

**Kit home:** schema-core (the provider rows + the fold); legality is a
Statement row (mounts: construction gate + the curated cycle/missing
diagnostics).

**Acceptance:** a cyclic provider graph refuses with the cycle named (the
counterexample is the cycle path, data not prose); a missing provider names
the unsatisfied requirement + the valid space of providers that could fill it
(04 §2); a legal graph's instantiation order is the generated topological
fold, not a hand sequence.

**Guard:** providers are closed per app (a closed provider registry); the
fold is the ONLY instantiation path — no out-of-band construction.

**Instance of:** TraceModel (the DAG — the causal order over providers) +
Change (the topological fold / fix — the cascade machinery) + Statement
(graph legality).

## 16. Routing (the route table as a TextKit grammar)

**Purpose.** Routes are a TextKit GRAMMAR (03): a route table = a prefix
grammar over path segments; the router = the generated parser; "no two routes
match the same path" = the grammar's `unambiguous` certificate (03 §1) — an
ambiguous route table fails to elaborate, never 500s at runtime. Extraction =
the `rel` payload correspondences (the parse's raw tree ↔ the typed params);
404 = the curated ParseError with the valid space (04 §2).

```lean
-- segments are the terminals; params are typed at the boundary:
inductive RouteTok where
  | lit (s : String)
  | param (t : Ty)                 -- closed per app (A1)

-- the route table IS a Grammar value (03 §8's Grammar over RouteTok):
def routeGrammar (routes : List (PathPattern × Handler)) : Grammar RouteTok
-- the generated parser carries the certificate:
--   unambiguous : unambig routeGrammar := by decide
-- extraction: rel : Iso (Packed RouteTok) Params  (03's `rel` payload iso)
-- 404: the curated ParseError (position/expected/valid-space, 04 §2)
```

**Seed:** TextKit (03 §8: Grammar/Lex/Parse + the `unambiguous` field + the
`rel` correspondence machinery) + the WIT world's route-ish surfaces (the
path-shaped exports the adapter generator already sees).

**Kit home:** TextKit (the grammar values + generated parser); the route
table's handler typing rides the Universe's row types.

**Acceptance:** an ambiguous route table fails to elaborate (the
`unambiguous` field, defaulted decide — the ambiguity named as data); a
request's parse yields the handler + the typed params via the `rel` iso; a
no-match request renders the curated 404 with the valid space of patterns.

**Guard:** path grammars stay in the 03 discipline (total, no recovery — a
404 is a VALUE of the parse, not a thrown error).

**Instance of:** Universe (the route table) + Correspondence (the carrier —
the `rel` isos, the parse round-trip, the ambiguity certificate).

## 17. Transport semantics (delivery guarantees as data)

**Purpose.** Delivery guarantees as DATA per channel
(`atMostOnce | atLeastOnce | exactlyOnce`), and the guarantee's OBLIGATION
generated from the data: atLeastOnce ⇒ the consumer's handler is idempotent —
`apply (apply s m) m = apply s m` — decidable for finite handlers, so the
obligation rides the ladder (a defaulted decide; the counterexample is data).
An exactlyOnce claim never stands bare: it needs the journal/idempotency-key
row (the canon row: "a queue/mailbox = a stream + a cursor").

```lean
inductive Delivery where
  | atMostOnce | atLeastOnce | exactlyOnce    -- closed (A1)

structure Channel where
  delivery : Delivery
  journal  : Option JournalRow   -- exactlyOnce REQUIRES this (the guard)

-- the generated obligation: atLeastOnce ⇒ idempotent handler — decidable
-- for finite handlers, discharged at the handler's construction site:
class Idempotent (apply : State → Msg → State) where
  proof : ∀ s m, apply (apply s m) m = apply s m := by decide
```

**Seed:** the canon row "a queue/mailbox = a stream + a cursor; redelivery =
replay from cursor; at-least-once + idempotent consumer" (notes/canon.md) +
the session lane (12 §7's Boundary — the channel's shape) + `FuncSem.delivery`.

**Kit home:** schema-core (the `Delivery` enum + the obligation family); the
idempotence check is a Statement row (mounts: the handler's construction gate
+ the channel/config cross-check).

**Acceptance:** an at-least-once channel with a non-idempotent handler fails
to elaborate/discharge with the counterexample (the message `m` and state `s`
where double-apply diverges, as data); an exactlyOnce channel without a
journal row fails construction; an idempotent handler's decide discharges at
the site.

**Guard:** exactlyOnce claims need the journal/idempotency-key row (the canon
row) — never asserted bare; delivery enums are closed per app.

**Instance of:** TraceModel (the channel's ordering — delivery is a statement
about the trace set) + Statement/Obligation (the idempotence obligation rides
the ladder).

## 18. Caching/memoization (a hit equals recomputation)

**Purpose.** A cache = a table + an invalidation policy (both data);
correctness = `lookup c k = some v → compute k = v` — a hit equals
recomputation, stated once as a coherence obligation and discharged per the
ladder (decidable when the key space is bounded, oracleSwept otherwise). A
poisoned cache (a hit that disagrees with recomputation) is caught by the
obligation, not by a test.

```lean
structure Cache (K V : Type) where
  table       : K → Option V      -- the stored rows
  compute     : K → V             -- the authority (recomputation)
  invalidated : K → Bool          -- the policy, as data (closed per app)

-- the coherence obligation, discharged per the ladder:
def coherent (c : Cache K V) : Prop :=
  ∀ k v, c.table k = some v → v = c.compute k
-- bounded K: `by decide` over the enumerated space;
-- otherwise: oracleSwept (the sweep row is the evidence)
```

**Seed:** the Universe's row types (the table is a row-valued function) +
Statement/Obligation (the coherence row + the tier/evidence record) + the
negative-control discipline (TestKit's PropSpec — the poisoned-cache control
is a mandatory negative).

**Kit home:** schema-core (the Cache structure + the coherence obligation
family); the sweep/decide evidence is a Statement row.

**Acceptance:** a poisoned-cache negative control is caught (the coherence
obligation fails with the key + both values as the counterexample); the
coherence obligation discharges on the fixture (bounded keys, `by decide`);
an invalidation policy change re-discharges mechanically.

**Guard:** eviction/invalidation policies are data (closed per app — no
callback-shaped escape hatch); an unbounded key space must declare the
oracleSwept tier explicitly, never silently.

**Instance of:** Universe (the table + the policy) + Statement/Obligation
(the coherence obligation + its tier/evidence).

## 19. Configuration (schema record + the last-wins override monoid)

**Purpose.** A config = a schema record (the Universe's row types) + an
override monoid — later sources override earlier, per field, the LAST-wins
semilattice — so resolution order is the monoid fold, computed, never
hand-sequenced. Validation is NOT a parallel pass: it is the schema's own
WF/obligations (Statement rows); an invalid config renders the curated Diag
(04 §1).

```lean
-- the override monoid: last-wins per field, over the schema's rows
structure CfgLayer (fs : List Field) where
  vals : RowVals fs

def overrideLayer (old new : CfgLayer fs) : CfgLayer fs :=
  ⟨perField old.vals new.vals (fun _ _ n => n)⟩   -- LAST wins, per field

-- resolution = the monoid fold over the closed source list, in order:
def resolveCfg (fs : List Field) (sources : List (CfgLayer fs)) :
    RowVals fs :=
  sources.foldl overrideLayer (defaultRow fs)   -- DefaultVal seeds the base
```

**Seed:** the schema record machinery (the Universe's `RowVals fs` + the WF
obligations) + `DefaultVal` (SchemaLang.CodecValue — the base layer's seed
values).

**Kit home:** schema-core (the `CfgLayer` fold beside the row machinery); the
validation IS the schema's existing Statement rows (no parallel config-check
pass — R1).

**Acceptance:** a config's resolution order is the monoid fold — a test pins
the fold's output for a two-source override, byte-identical on replay; an
invalid config (a WF violation in the resolved row) renders the curated Diag
with the valid space (04 §2); a schema change re-derives the config's
obligations mechanically.

**Guard:** config sources are a closed list per app; the override monoid is
per-field LAST-wins — no merge callbacks, no side-table precedence.

**Instance of:** Universe (the schema record + the fold's rows).

## 20. Capacity (bounded Petri nets — the counted-shared-resource shape)

**Purpose.** The shape machines can't express: places hold token COUNTS
(pools, rate limiters, inventories), transitions consume/produce. The
machine row (Machines) is the one-token special case — say so in the
module header. For FINITE nets the three resource analyses are all
decidable: boundedness (does a marking stay bounded), deadlock (a
reachable marking with no enabled transition), conservation (tokens
preserved, weighted). The honest discipline: the reachable-marking
space is finite WHEN boundedness holds, so the check carries a bound —
an unbounded answer is LOUD (the 12 §3 budget discipline), never a
silent truncation.

```lean
structure Net where
  places      : List Nat                     -- initial token counts
  transitions : List (List Nat × List Nat)   -- (consume, produce),
                                             -- index-aligned with places
abbrev Marking := List Nat                   -- token counts per place
-- where statable, the bound is IN the type: the capacity is enforced
-- by construction, not by check
abbrev MarkingAt (caps : List Nat) := { m : Marking // m ≤ caps }

def enabled   (n : Net) (m : Marking) (t : Nat) : Bool  -- consume ≤ m
def fire      (n : Net) (m : Marking) (t : Nat) : Marking

-- the three analyses, decide-backed over the finite reachable space:
def bounded   (n : Net) (B : Nat) : Verdict
--   .yes | .no (violating marking) | .unboundedAt B (LOUD — the bound
--   was hit, the question did not terminate within budget)
def deadlock  (n : Net) : Option Marking   -- the counterexample marking, as data
def conserved (n : Net) (w : List Nat) : Bool   -- weighted token preservation
```

**Seed:** the canon row "floored stock / budget / quota = a
 canonically-ordered value with monus (nonneg BY CONSTRUCTION)"
(notes/canon.md) — a place's token count is that value; the machine row
(Machines) — the one-token special case, cited as such.

**Kit home:** Machines (beside the Trace module); the checks ride
`CodegenCore.ModelCheck` (12 §3 — the reachable-space walk is that
engine's run with the marking as state and each transition as a label).

**Acceptance:** a pool spec's capacity is never exceeded BY CONSTRUCTION
(the type of a marking enforces the bound where statable); a deadlocking
net yields the counterexample marking as data; an unbounded net's check
reports `unboundedAt B` loudly — never a silent partial.

**Guard:** FINITE nets only; the boundedness question must terminate
(budget-bounded, the 12 §3 discipline) — an unbounded net is a verdict,
not a hang.

**Instance of:** TraceModel (firings = events; the causal order over
them is the net's behavior) + Universe (the net is data).

## 21. The connector library (connectors as first-class — the Wright/Acme lesson)

**Purpose.** Connectors as FIRST-CLASS with protocol semantics: an
architecture is typed ports wired through lawful connectors, and the
connector-composition MISMATCHES — the protocol-level incompatibility
hiding in the wiring (Wright's deadlock-in-the-wiring) — are caught at
elaboration via the session duality check (Machines.Session's
`IsDualOf`/`tdual` machinery) + the effect rows (12 §1). Each kind
carries its protocol: rpc = a session; pubsub = a broadcast stream;
queue = a cursor'd stream (the canon row: "a queue/mailbox = a stream +
a cursor"); pipe = an unbuffered session; sharedMem = an effect row.

```lean
inductive ConnectorKind where
  | pipe | rpc | pubsub | queue | sharedMem    -- closed per app (A1)

structure Connector where
  kind     : ConnectorKind
  protocol : Machines.Session.Protocol     -- the duality check's subject
  effects  : EffectSet                     -- 12 §1's rows

-- an architecture = typed ports wired through LAWFUL connectors; the
-- composition check is duality + the effect-row join, both decidable,
-- so a mismatch fails to elaborate (never a runtime surprise):
structure LawfulWiring (producer consumer : Connector) where
  dual : Machines.Session.IsDualOf producer.protocol
           (Machines.Session.tdual consumer.protocol) := by decide
  fx   : consumer.effects ≤ producer.effects.join consumer.effects := by decide
```

**Seed:** Machines/Session.lean (`IsDualOf`, `tdual`, `tdual_dual` — the
duality machinery, proved once) + the session lane (12 §7's Boundary —
the connector's step shape) + the canon row "a queue/mailbox = a stream
+ a cursor" (notes/canon.md) + the effect rows (12 §1).

**Kit home:** schema-core (beside the Boundary types and the Effect
lattice); a wiring's legality is a Statement row (mounts: the
elaboration gate on wiring construction).

**Acceptance:** a miswired pair (a pipe wired to a queue's consumer
contract) fails to elaborate NAMING the protocol mismatch; a lawful
wiring's composed protocol passes duality (the decide discharges at the
site); the queue row's cursor is the stream replay discipline, not a
second mechanism.

**Guard:** connector kinds closed per app (A1); the composition check
is decidable (duality + effect-row joins) — no check that needs search.

**Instance of:** TraceModel (the connector's protocol is a trace shape —
sessions are the causal order over steps) + Correspondence (the wiring's
duality is the carrier's iso) + the Statement carrier (wiring legality).

## 22. Wires (format × delivery × protocol — every channel is one triple)

**Purpose.** A wire = format × delivery × protocol. The FORMAT is the
codec — a `PartialIso`, the correspondence carrier (the canon row: "a
codec = a `PartialIso`"). The DELIVERY is the transport semantics
(`atMostOnce | atLeastOnce | exactlyOnce` — 12 §17's `Delivery` data).
The PROTOCOL is the session — what flows when (the `Machines.Session`
row, canon Part 2). The connector library (12 §21) is the WIRING
discipline over ports; wires are its content.

**FFI IS A WIRE**: the synchronous in-process case — the C ABI encoding
is its format, call/return is its protocol, exactlyOnce by
construction. The lesson, named so it is not re-paid: the lean-ffi
crate died because it was a wire with no protocol and no consumer —
an undeclared channel is a finding (the guard below). Component-model
channels, WIT boundaries, and network transports are all wires with
different triples of the same three axes.

```lean
structure Wire where
  format   : PartialIso                      -- the codec: raw ↔ typed
  delivery : Delivery                        -- 12 §17's closed enum
  protocol : Machines.Session.Protocol       -- what flows when (the session row)

-- a channel exists iff its Wire row exists: the three axes are DECLARED
-- DATA, checked at the boundary (the format rides the codec's law, the
-- protocol rides duality, the delivery drives the obligation)
```

**Seed:** the canon rows (codec = PartialIso, W1.2; protocol =
Machines.Session, Part 2; queue = stream + cursor, Part 3) + 12 §17's
`Delivery` + 12 §21's `Connector` (the wire's consumer) + 12 §9's open
guard ("the version index is host-side only until the wire story is
named") — this section names it.

**Kit home:** schema-core (beside the Boundary types, the `Delivery`
enum, and the connector rows); a channel's declaration is a registry
row in the same universe the WIT world and span folds read.

**Acceptance:** the trio's instances cross-compose — a wire's format
rides `RoundTripSpec` (05 §2's deriving rows), its protocol rides the
session's duality check (`Machines.Session.IsDualOf`), its delivery
drives the idempotency obligation (12 §17: atLeastOnce ⇒ the handler's
idempotence decide; exactlyOnce ⇒ the journal row). A declared wire
composes all three mechanically; an undeclared channel — a side
channel, a hand-rolled socket, a second serialization — is a review
finding, not a feature.

**Guard:** the three axes are declared data (no anonymous channels);
delivery enums closed per app (A1); the format is always a PartialIso,
never a hand printer/parser pair (the canon row forbids the second
inversion theorem).

**Instance of:** Correspondence (the format is the carrier's
PartialIso) + TraceModel (the protocol is the session's trace shape) +
Statement (the wire's declaration is a row; the cross-composed
obligations ride the ladder).

## 23. Statecharts (hierarchy + orthogonal regions — promoted from Watch)

**Purpose.** The machine row's two-dimensional extension, promoted on
its trigger: hierarchy (nested states) + orthogonal regions (parallel
sub-machines with broadcast). The trigger that earns the promotion: the
first lifecycle that is honestly two-dimensional — states × regions —
in a product lane. A one-dimensional lifecycle stays a flat
`Machines.Machine` (the special case; say so in the header).

The formal content, two shapes:

- **A hierarchical machine** = a tree of machines with entry/exit
discipline: entering a node enters its initial child; exiting a node
runs the exit chain to the root. History, guards on entry/exit — all
tree discipline, not new theory.
- **Orthogonal regions** = the product machine: regions step in
parallel over the tuple of states; an event BROADCASTS — every region
that handles it steps, the rest stutter.

```lean sketch
-- hierarchy: a machine whose container is a tree of machines
inductive HierMachine where
  | leaf   (m : Machines.Machine)
  | node   (m : Machines.Machine) (children : List HierMachine)
-- entry/exit: node entry descends to the initial child; exit unwinds

-- orthogonality: the product machine over the regions, broadcast step
def regions (rs : List Machines.Machine) : Machines.Machine
-- state = the tuple of region states; step = the broadcast fold
```

**Seed:** `Machines.Machine` (the flat row — the leaf) +
`Machines.Session` (the broadcast/step ordering vocabulary) + 19's
denotation (machines denote into the TraceModel — the extension point).

**Kit home:** Machines (beside the Trace module); the hierarchical and
product shapes EXTEND the row's denotation, they are not a second
machine theory.

**Acceptance:** the first two-dimensional lifecycle lands as one
hierarchical machine with regions; the denotation extends into the
TraceModel (19), so liveness and finite model-checking (12 §2/§3) apply
over the flattened product unchanged; a flat machine's battery is
byte-identical (the flat row is the degenerate case).

**Guard:** promotion holds only while the trigger holds — if no
product lane carries a two-dimensional lifecycle, this stays a Watch
item (the leftover rule, 01 §4); the flat machine row remains the
default; hierarchy and regions are Machines extensions, never a
parallel statechart library.

**Instance of:** TraceModel (Machines' denotation extended — hierarchy
and regions denote into the same trace poset).

## Priority note

Per the user's direction — build the FINITE MODEL-CHECKING + LIVENESS layer
into the outset (Phase 3 of 11), pair it with the machine! entourage, then the
observability slice (impact gating + causal trail) for the dev loop, then
Effects/Shrinking/Sessions in the type-driven stratum. Each is independently
gated; none waits on another except Effects-on-foundation.

## Watch items

Named so nobody rediscovers them ad hoc; each carries a TRIGGER, not a
date. None has a consumer today — per the leftover rule (01 §4), they
wait for one.

- **Kahn process networks** — blocking-read FIFO determinism. Trigger:
  push-based async-concurrent dataflow. Kahn determinism = the
  confluence row's async cousin.
- **Morphic systems** (the dynamic-topology concept, named) — machines
  whose states are architectures: the machine's transition CREATES and
  tears down sub-machines. Trigger: a runtime-created/torn-down
  topology — tenants/pipelines spun up per deployment. Almost
  certainly out of this product's scope; WATCH, named here so nobody
  rediscovers it ad hoc. (Statecharts left this block — promoted to
  §23 on the two-dimensional-lifecycle trigger.)
