# PolyFun study — typed interaction, programs, machines — 2026-09-18

Source: /tmp/polyfun (shallow clone of Verified-zkEVM/PolyFun; Lean module
system, Mathlib + CSLib deps). 575 Lean files: `PolyFun/` (PFunctor,
IPFunctor, ITree, Interaction, Realizability, Control), `ToCslib/`
(upstream stagings), optional `ComplexityBackends/`, tests, and an
unusually complete `docs/guides/` layer. Method: direct reads of the
guides + the owning source files (line cites below are from the clone).
Companion to cedar-study.md (same format: what they do, verdict,
consumer, cost).

Context for every verdict: our Session lane is a LINEAR script
(`TProtocol P := List (Dir × P)`, payload never inspected, position =
state), dual-checked by `IsDualOf` at elaboration (`Machines/Session.lean`
header); our effects lane derives a two-move session from `EffectDecl`
(`SchemaLang/Commands.lean`); our guest logic is emitted RUST, not Lean
programs — the Lean side declares and checks, it does not run guests.
That last fact kills several otherwise-attractive borrows.

## 1. The indexed interface shape (IPFunctor)

**What they do.** `IPFunctor I J` is a three-field structure
`A : J → Type` (requests available at output index), `B : (j) → A j →
Type` (response family), `src : (j) → (a) → B j a → I` (which state each
child lives in) — `PolyFun/IPFunctor/Basic.lean:74-83`. The endomorphic
specialization `Endo I := IPFunctor I I` (`Basic.lean:92`) is where free
constructions live. Three free-tree flavors over it
(`docs/guides/ipfunctor.md`, comparison table): `IFreeM P X s`
(primitive, state-indexed leaf family — different branches may end at
different leaf states), `FreeM P s α` (constant family), and
`FreeM₂ P s t α` (`PolyFun/IPFunctor/Free/Indexed.lean:18` — every leaf
tagged with a proof `u = t`, so the POST-STATE is static). `FreeM₂` gets
a genuine Atkey indexed bind and a `LawfulIndexedMonad` instance
(`Control/Monad/Indexed.lean`); its own doc says session-typed protocols
are the canonical use. The final coalgebra `IM P i` (indexed M-tree with
a coherence invariant at every vertex, `IPFunctor/M.lean`) covers
infinite state-gated interaction.

**What it buys over our two-move sessions.** Our `TProtocol` fixes each
position's payload in advance; responses cannot depend on earlier
answers and the post-state is implicit (position = length). `IPFunctor`
buys exactly two things we lack: (a) requests/response TYPES gated by
protocol state (`B s a` reads the state), and (b) statically checked
post-state per program fragment (`FreeM₂`'s `u = t` leaves — a
wrong-final-state choreography is a type error, the same elaboration-time
refusal our `IsDualOf` gives for peers, but along the TIME axis).

**Verdict: WATCH.** No consumer — our canon already rules the shape
(Part 2: "a wizard / multi-step flow = a SEQUENCE (indexed monad /
session), NOT a machine") but no lane instantiates it; every live
protocol is the two-move command/event loop.

**Trigger:** the first ≥3-move or answer-dependent protocol (a wizard
row instantiation, or a choreography whose event type depends on the
command). **Minimal version then:** `Endo I` + `FreeM₂`-style
post-state marker + the `IndexedMonad` class — NOT the two-index general
layer (composition `Q ◃ P` needs distinct indices; we have no consumer
for functors between family categories). The general `I ≠ J` machinery,
lenses/charts/equivs, and `IM` stay un-borrowed. Estimated port cost at
trigger time: the `FreeM₂` core is ~1 file (indexed.lean is small); a
faithful minimal port with laws + negative controls is one work order.
Note their own limitation list (`docs/guides/ipfunctor.md`, end):
`FreeM₂.liftObj` doesn't exist (post-state varies with response) — plan
authoring in `FreeM` and convert when the post-state is known.

## 2. Model-correspondence machinery vs our Fusion bridges

**What they do.**
- `Implements` (`PFunctor/Dynamical/DynComputation.lean:819-821`):
  `∀ input, M.denote input = FreeM.toResumption (program input)` — the
  machine↔program bridge states the machine's denotation EQUALS the free
  program's behavior tree, with hidden-state types free to differ.
- `ObsEq.of_implements` (`DynComputation.lean:825-828`): two machines
  implementing the same program are observationally equivalent — the
  PROGRAM is the intermediary, so cross-state-type machine comparison
  never needs a relational simulation.
- `ImplementsWithin` (`Dynamical/DynComputation/Bounded.lean:792,
  799-800`): `Implements ∧ ∀ input, IsTotalRollBound k` — the termination
  BUDGET is a conjunct of the correctness predicate, not a separate
  certificate.
- ITree↔handler: `toITree_liftM_weakBisim` (`ITree/Free.lean:137-141`) —
  free-handler interpretation and ITree interpretation agree up to WEAK
  bisimulation, explicitly accounting for interpreter steps.
- The LTS spectrum (`Control/Bisimulation.lean:97-124`): strong ⊆ delay ⊆
  weak, each as simulation / state-pair / total-equivalence at three
  levels, with a cslib projection whose step-level correspondences are
  definitional — plus a naming rule page
  (`docs/guides/bisimulation.md`, end) pinning who may say "bisimulation".

**What we're missing.** Our `Machines.Fusion.bisim_iff_resp_streams`
(`Machines/Fusion.lean` header item 3) is the deterministic finite case,
stated as stream EQUALITY on shared types; its own header defers
cross-type machine pairs "until a relational-simulation order lands".
PolyFun's answer to that exact problem is shape (b) above: don't relate
the machines directly, relate both to a program. We have no `Implements`
analog — nothing says "this machine computes the same interaction as
this spec-program". We also attach termination separately
(`Convergent.run_length_bound`) rather than as a correctness conjunct
(their `ImplementsWithin` shape).

**Verdict: WATCH** (both shapes). **Trigger for `Implements`-as-shape:**
the first cross-type machine pair — the exact condition the Fusion
header names; the program-as-intermediary trick may dissolve the need
for a relational-simulation order entirely. **Trigger for
`ImplementsWithin`:** the first correctness statement about the pipeline
machine that needs its fuel bound IN the theorem (our canon's
"convergence/termination" row already carries both halves separately).
Port cost when triggered: low — these are predicate definitions + short
theorems over machinery we already have (`Machine`, `Convergent`), no
new library.

## 3. Handler independence — the honest need check

**What they do.** `Handler m q := (a : q.A) → m (q.B a)`
(`PFunctor/Handler.lean:31`) — a Kleisli section, one line. Programs
(`FreeM P α`) name requests; handlers choose answers; `liftM` interprets;
`mapTarget` retargets a handler along a monad morphism
(`Handler.lean:38-58`). The same program runs under any handler; VCVio's
`QueryImpl` is definitionally this type (README table).

**The honest need check.** The guest↔host loop (`Commands.lean`) is
where a swappable host would pay: one guest program, two hosts (the real
executor and the differential-oracle host simulation). But (a) the host
execution semantics and oracle host sim are DECLARED EXCLUSIONS in
Commands.lean's header ("no consumer yet; grows with the first one,
W8.10"), and (b) our guest logic is emitted Rust — there is no Lean-side
guest program to interpret under two handlers. The Lean side owns the
choreography declaration and its laws, which are already
host-symmetric by duality (`tdual_payload_mirror`). A Handler layer
today would formalize a program that doesn't exist.

**Verdict: WATCH.** **Trigger:** W8.10 lands a Lean-side host-execution
interpreter AND a second (oracle) host for the same command interface —
i.e. the moment two interpreters of one command stream actually exist.
Then the borrow is nearly free: the "handler" is a type synonym plus one
interpretation-commutes lemma; no library port. Until then: no consumer — skip.

## 4. Realizability / StepClass vs our fuel + obligation tiers

**What they do.** `StepClass` (`Realizability/StepClass.lean:68-77`):
`Str : Type → Type v` (representation DATA, not a proposition — "runs in
polynomial time" is a statement about encodings) + `Hom` (admissibility
Prop) + id/comp. Over it: `IsRealizableBy`/`IsRealizableWithin`
(existential machine + admissibility proofs, boundary a PARAMETER "never
an existential" — `docs/guides/realizability.md`); and the quantitative
layer `QuantitativeStepClass` (`Realizability/Quantitative.lean:62`) —
`Realizer` (executable evidence, `Type`-valued) + `size` + `cost` +
`admissible` erasing to `Hom`. Certificates: `RankedRunCertificate`
(`Quantitative/BoundedClosure.lean:53`) — a decreasing potential with an
EXPLICIT progress field so an empty allowed-answer relation cannot prove
termination vacuously; `RunsWithinUnder` splits the progress conjunct
for the same reason. A whole doc section ("What A Certificate Cannot
Fake") enumerates what a dishonest prover cannot do.

**Comparison with ours.** The honesty shapes are already parallel:
their `admissible`-erasing-to-`Hom` ≈ our `CheckedProp` (relation +
checker + sound); their boundary-as-parameter ≈ our `WitnessRef` pinning
the certificate + decoded context + artifact name (`Obligation.lean`
guestVerified arm); their "termination vacuity" guards ≈ our mandatory
negative controls; their loud-gap discipline ≈ our `discharge = none`
"armed but unfired" pattern. Their fuel handling ("fuel exhaustion =
REFUSAL, soundness never mentions fuel", `checkWitness_mono` monotonicity)
is exactly `WitnessCheck.lean`'s pinned shape — ours landed first as
doctrine, theirs confirms it.

**Verdict: SKIP** the machinery. Reason: `StepClass` exists to constrain
LEAN-SIDE machine implementations (their step maps); our implementations
live in emitted Rust, our Lean side declares and checks, and our cost
story is witness/obligation-tier shaped, not complexity-class shaped
(quantitative certificates in Lean would need a backend adequacy theorem
— their own "known gaps" admit the whole-program linking theorem is
open). **Watch trigger** (narrow): if we ever need to certify a cost
bound on emitted code IN Lean (e.g. a gas-metering lane), borrow the
`RankedRunCertificate` shape (decreasing potential + separate progress
conjunct) rather than the StepClass category.

## 5. FreeM ergonomics (do-notation over requests)

**What they do.** Three `@[doElem_elab]` override files
(`IPFunctor/Notation.lean`, `Notation/Indexed.lean`,
`Notation/Deterministic.lean`) make ordinary `do` blocks elaborate to
indexed free-monad trees, with statically tracked intermediate states
(`FreeM₂` flavor) and CUSTOM DIAGNOSTICS for state mismatches and
non-polymorphic remainders — the elaborator detects the monad head via
`whnf` at reducible transparency so plain-def aliases survive. This is
real machinery, toolchain-pinned, and their docs treat it as the
user-facing win of the whole indexed layer.

**Could our Commands lane borrow it?** The Commands lane's user surface
is schema DECLARATIONS (`EffectDecl`, `@[schema_command]` items), not
Lean programs — guests don't write Lean do-blocks. The only Lean-side
authoring surface we own is `machine!` (`Machines/Dsl.lean`), whose
users write guard/action terms, not request trees. The ergonomics only
become relevant when item 1's trigger fires (a genuine multi-step
protocol someone AUTHORS by hand in Lean).

**Verdict: WATCH** — rides item 1's trigger; never adopt the elaborator
overrides without the indexed layer they serve. At trigger time, port
cost is the dominant line item (elaborator overrides are
toolchain-coupled; budget a full work order and pin the toolchain check
they use — the `backward.do.legacy` caveat is in their docs).

## 6. The program-logic layer (WP/vcgen) vs our PrePost

**What they do.** A layered WP stack: `MAlgOrdered m l` (ordered monad
algebra over a complete lattice, with `wp`/`Triple` and the structural
rules, `Control/Monad/Algebra.lean`); per-operation specs `OpSpec P l`
with a syntactic `wpFold` and soundness `wpFold_le_wpVia`/`wpFold_eq_wpVia`
against any handler (`PFunctor/Free/WP.lean`); `@[spec]` lemmas
(`Spec.lift`, `Spec.liftBind`) letting core's `vcgen` decompose free
programs with uninterpreted operations (`PFunctor/Free/Do.lean` header);
demonic/angelic readings as SCOPED instances with an explicit warning
that a global instance would "race downstream registrations on
reducible unfoldings"; and a two-tier `Std.Do` quarantine enforced by
`scripts/check-modules.sh`. The full construct-coverage table is in
`docs/guides/program-logic.md`.

**vs our PrePost.** `SchemaLang/PrePost.lean` is an OBLIGATION ladder,
not a wp calculus: pre = caller boundary check (`CheckedProp`, exact
iff); post = tier computed from a citation, discharged by
`.citedProof`/`.decide`/witness, with `none` as the loud gap. There is no
Lean-side monadic program to compose postconditions over — wp's whole
value is compositional reasoning over program STRUCTURE, and our program
structure lives in Rust. Borrowing `MAlgOrdered`/`wpFold` would build a
calculus with no programs. Their engineering lessons (scoped-not-global
instances, quarantine fences, construct-coverage table) are real but
attach to a wp layer we don't have.

**Verdict: SKIP.** Reason: no Lean-side program surface; our postcondition
story rides the obligation ladder and proved preservation theorems
(`post_preserved_of_neutral`). **Named existing shelf row:** the canon's
"Dijkstra monads" entry (Part 5) is the correct flip condition ("the
guest lane wants fuel/capability contracts riding in action types") — a
WP layer, if ever, enters through that door, not this one.

## 7. Hygiene / discipline (CI axiom audit, docs structure)

**What they do.**
- **Axiom sweep** (`scripts/PolyFunAxiomSweep.lean`): whole-library
  kernel-level axiom census over compiled oleans — sees exactly what the
  kernel accepted, includes compiler auxiliaries (taint surfaces on the
  parent), records `native_decide`-minted axioms per owning declaration.
  Committed `axiom_baseline.json` is checked by `--check`; crucially
  `--update-baseline` REFUSES to write a nonempty baseline ("it cannot
  pre-authorize future taint"). The docstring enumerates the sweep's
  blind spots (structure-field defaults, `example`s, unimported files)
  and mandates pairing with an import-completeness gate.
- **`scripts/check-modules.sh`**: every file must declare `module`; the
  `Std.Do` quarantine enforced as an import-modifier allowlist per
  directory.
- **`scripts/check-docs-integrity.py`**: local md links + anchors
  resolve; Lean paths written as code in docs resolve; **Lean excerpts
  in docs must match marked regions of checked tutorial modules** (an
  excerpt-drift gate); every library/example/consumer module has a
  docstring. Wired into CI (`.github/workflows/ci.yml` runs
  `scripts/validate.sh --axioms`; separate `docs-integrity.yml`).

**Comparison with ours.** Our `just lean-axioms` (justfile:409) already
does the kernel axiom cone per gated package with an allowlist plus a
diff against committed `notes/axiom-report.md` — the same core pattern,
independently arrived at. `just gates` already runs an import-completeness
analog (`lean-proof-roots`). What we genuinely lack:
1. the excerpt-drift gate (our notes/ carry many Lean fences that can
   silently rot — cedar-study C3 adopted their GUIDE.md; this is the
   executable half of the same idea);
2. the refuse-nonempty-baseline discipline on re-baseline;
3. the written blind-spot list for our own axiom sweep.

**Verdict: ADOPT as patterns** (no PolyFun code ports — ours is a
different gate harness). Consumers: (1) excerpt-drift gate →
`notes/**` code fences, wired as a `just gates` recipe (consumer: every
notes doc with ```lean blocks; port cost: small — their
`check-docs-integrity.py` check #4 is ~100 lines of pattern); (2)+(3)
→ `Gates.Axioms` `--write` path and the justfile comment (trivial cost).
WATCH (not adopt): the module-mode lint — our W5.4 module migration is
the trigger; their `check-modules.sh` is the enforcement template.

## Prioritized borrow list

1. **ADOPT — docs excerpt-drift gate** (their `check-docs-integrity.py`
   check 4): Lean fences in `notes/` verified against real tree regions;
   wire into `just gates`. Consumer: every notes doc; cost: ~1 session.
2. **ADOPT (micro) — axiom-gate honesty details**: refuse nonempty
   re-baseline; document the kernel-sweep blind spots (structure-field
   defaults, `example`s, unimported files) next to the baseline rule.
   Consumer: `Gates.Axioms` / `just lean-axioms`. Cost: trivial.
3. **WATCH — `FreeM₂` indexed sessions** (item 1 + 5): trigger = first
   ≥3-move/answer-dependent protocol (canon wizard row); minimal version
   = `Endo I` + post-state marker + `IndexedMonad` + their do-notation
   pattern; budget one work order + one for the elaborator.
4. **WATCH — `Implements`/`ImplementsWithin` shapes** (item 2): trigger =
   first cross-type machine pair (Fusion header's named condition) — the
   program-as-intermediary may replace the deferred relational-simulation
   order; and the first correctness statement needing the fuel bound
   in-theorem. Cost when triggered: low.
5. **WATCH — Handler independence** (item 3): trigger = W8.10's Lean-side
   host interpreter + oracle host for one command interface; borrow is
   then a one-line type + one commutation lemma.
6. **SKIP — StepClass/quantitative realizability** (item 4): our
   implementations are Rust; the honesty shapes (fuel-as-refusal,
   boundary-pinned witnesses, vacuity guards, loud-gap discharge) are
   already ours; narrow re-entry via `RankedRunCertificate` if a
   Lean-side cost-certificate lane ever opens.
7. **SKIP — the WP/vcgen layer** (item 6): no Lean-side programs to
   compute over; the canon's Dijkstra-monad shelf row is the named door.
