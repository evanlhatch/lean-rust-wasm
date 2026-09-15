# Cohesion plan 2026-09-15 — fewer concepts, more Lean

Companion to `notes/code-review-2026-09-15.md` (the granular findings).
This doc is the concept-level pass: what the toolkit IS, the minimal
concept kernel, where dependent types/metaprogramming go harder, the
isomorphisms to make explicit, the proof-automation policy, and the
25% cut. Method: 7 parallel full-package surveys + direct reads;
inventory of every agreement theorem, registry, emitter, fuel site,
`partial def`; flatland docs (DOCTRINE/TOOLKIT/lean-v3/lean.md/
REBUILD-lean) read as the constitution.

## 0. The one-sentence answer

The repo already IS one pattern — **closed universe + total denotation +
correspondence proof + generated artifacts** — applied ~15 times by hand.
The move is to name that pattern once, make every instance an *instance*,
and delete the copies. Concept count drops; power per concept rises;
the proofs compose instead of accumulating.

Evidence the pattern is real (inventoried, non-test code):
~53 section/retraction theorems (codecs, text wire, enum wire),
~60 two-semantics agreements (exec vs relational, eval vs compiled),
10 data-is-function pins (table = step fn), ~16 optimizer/compiler
certificates, ~22 bridge/commutation theorems, plus ~20 NEGATIVE
controls (buggy twins that must disagree — a discipline almost nobody
has). Every one is an instance of THREE shapes — `Iso`,
`PartialIso`, `Denotes + ReprOp` — which exist in
`Machines/Foundations.lean:42-122` and have **zero non-test
instances**. The kit is written and unused; the theorems are written
and unconnected. That gap is the whole cohesion problem.

## 1. The minimal kernel — six concepts

Everything loadbearing in the tree is one of these:

| # | Concept | Shape | Canonical home (today) |
|---|---|---|---|
| 1 | **Universe** | Tarski: closed inductive codes + TOTAL `El : Code → Type` | `Ty`+`toType`, `VExpr`+`evalV`, `Wat.Op`+`Sem`, `Ckt`+`denote`, `PType` |
| 2 | **Correspondence** | `Iso` / `PartialIso` / `Denotes+ReprOp` (laws on the shape, not the instance) | Machines.Foundations (dead) |
| 3 | **Law class** | legality assembled by instance search (`Linear`, `Change`/`ChangeInversion`, `Determinism`, `NonInterfering`) | dbsp, scattered |
| 4 | **Machine** | guarded transitions, two projections, agreement by construction (`tr_iff_step?` proved ONCE, inherited by all) | Machines.Core |
| 5 | **Registry→Emitter** | env extension + pure `Emitter` + byte-tie + one-writer audit (the buf spine) | codegen-core |
| 6 | **Surface** | attributes + `declare_*` commands + macros; proofs generated, not written | Meta.Reflect, EnumWire, Dsl |

Everything else — TestKit's three Specs, LintKit's five linters,
GuestGate's bans, the oracle, the breaking gate — is a *combination*
of these six, and should be defined as such (§5).

The authoring story these six tell, end to end: a domain is a Universe
(1); its rules/updates/machines are data over it (4, via 6); legality
is synthesized by law classes (3); every crossing — wire, codegen,
theory↔exec, Lean-eval↔wasm-run — is a Correspondence (2); artifacts
are folds through the Registry-Emitter spine (5); the byte-tie and
differential duel are the CI shadow of (2).

## 2. Where dependent types go harder (ranked by leverage)

**D1. Kill synced-by-test evaluator families with finally-tagless.**
`VExpr` has THREE evaluators (`evalV` boxed, `evalU`/`evalB` raw,
Validate.lean:252/299/334) whose agreement is pinned by executed
tests, plus the `evalBNeutral` proof-carrying-def workaround
(TickCascade.lean:133-174) because the fixed `.bool` index bars
`induction`. The tagless move: author expressions against a
`class ExprLang (repr : Ty → Type)` (one method per ctor); the GADT
is the REIFY instance (codegen stays first-order, doctrine D8
honored); `evalV`/`evalU`/`evalB` are three instances of one term —
agreement by parametricity, the test pin graduates to construction.
If tagless feels too clever, the cheaper half: `RawTy : Ty → Type`
computed return type + one `evalRaw`, collapsing evalU/evalB and the
fixed-index workaround class (~50 lines + the tie becomes a theorem).
Same trick absorbs `VCase` (Validate.lean:499-513 — the same GADT
with a different leaf): one family parameterized by its leaf type.

**D2. Lengths/shapes into indices at the codec boundary.**
`buildOne?`/`buildSlices?` (CodecValue.lean:317-388) thread fuel +
parallel need-computation lemmas (`needS_le`, `needOne_le_len`) for
what is structural recursion on a length-indexed type. Take
`h : vs.length = flatLength t dims` as the index-level fuel: ~80
lines of bound-lemma plumbing disappear. General rule: where a def
carries `fuel` AND a proved exact measure exists, the measure wins.

**D3. Stack-typed instruction GADT in Sem (bounded, worth it).**
`Instr : List VTy → List VTy → Type` over `Sem.Instr` (NOT `Wat.Instr`
— WAT stays string-named for goldens): `checkStack` (94 lines)
becomes the derivation; `exec_typed`'s per-case checker-casing
(536-line theorem, Sem.lean:398-936) collapses to induction over the
derivation (~8-line flat cases); underflow unrepresentable. Honest
residue: memory bounds checks, fuel, and the after-`br` dead-tail
rule stay explicit — `typeSafety` does not become `rfl`. Bonus: the
result-typed frame version FIXES the documented typing gap
(Correct.lean:373-379). Net ~-350 lines and a proof that currently
re-cases the checker stops existing twice.

**D4. Proofs in constructor position at the registry boundary.**
`Emitter` gains `outputs_nodup : outputs.Nodup := by decide`
(one-writer becomes unconstructible, the audit test retires);
`allocateCodes` returns codes with `Nodup` in the type (faults'
`decide`-in-Tests collision check becomes structural);
`DiffSpec`'s ≥2-corruptions rule becomes a list-length field.
Pattern: every "checked in Tests" invariant adjacent to a structure
is a candidate `:= by decide` field.

**D5. `machine!` generates its whole entourage.** Today the macro
emits the machine; users hand-write the transition table + table=step
theorem + `DecidablePred Inv` — 3-4 verbatim copies each
(Pipeline.lean:78-90,130-174; OrderMachine.lean:75-86,118-169;
Update.lean:312-365; feature-flags Machine.lean:47-55,114-147). The
macro owns all the data: emit the table, the `tableStep?_eq_step?`
proof, the DecidablePred instance. Also: payload-carrying events
(`event send (v : α)`) — the gap that keeps all of Sync.lean
(~150 lines) off the macro. ~250 downstream lines deleted, one error
class gone, and "the emitted Rust is the machine" stops being
hand-re-proved per machine.

## 3. Where the functional power goes harder

**F1. Isomorphisms as objects, not theorem pairs.** Inventory:
`VList t ≃ List (Value t)` (one direction proved, CodecValue.lean:160);
`Option α ≃ Sum Unit α` (wire-identical: `encOpt` duplicates `encSum`'s
tag layout); `encListVList`/`encStreamVList` twin theorems (13-line
proofs differing in one ctor); `valOpt`/`optVal`/`valSum`/`sumVal`
adapter halves with no inverse lemmas; mangler round-trips
(`snake∘pascal`) asserted per-case in Tests. Move: each becomes one
`Iso`/`PartialIso` VALUE; the inverse lemmas prove once at the
structure; consumers cite the object. And `Substrait Typed↔Proto`:
define `WireImage` (the subtype of Proto.Rel in the typed image —
the `SqPred`/`PairPred` pinning predicates, Decode.lean:4956-4972,
become the type), then `toProtoWith`/`decodeRel` is a genuine
section/retraction pair, absorbing today's ad-hoc `okS` side
conditions.

**F2. Recursion schemes ONLY where a tree has ≥3 passes.**
Substrait's `Proto.Rel`/`Expression` have ~6 parallel passes (emit,
decode, eval, lower, anchor-assign, size) — the lean4-mlir
anti-pattern the repo's own D6 names. One `Rel.fold` (paramorphism:
emitters want the original subterm) + algebras. For `Ty` folds
(tyWit/tyRust/tySnapshot/lower/…): NO catamorphism — match arms are
already minimal; an algebra record restates 20 ctors per consumer,
net-zero. The real `Ty` duplication is the QUOTATION triple:
`tyToExpr` (Reflect.lean:419) / `tyTerm` (Derive.lean:52) / `ccTerm`
(Meta/Gen.lean:63) are one hand-written `ToExpr Ty` at three sites —
one `instance : ToExpr Ty` deletes ~45 lines and a drift class
(nothing forces the three to agree on a new ctor today).

**F3. The Grammar-as-data play (substrait's 25-35% cut).**
Grammar.lean already proves the pattern for 13 type-head ctors
(shared table + `prefix_unique` by `decide` + `lexCtor_self` ONE
lemma for all ctors). But literal/expr/rel grammars are hand code,
and the name tables drift in pairs (`joinTypeName` Emit/Text.lean:360
vs `joinTypeOfName` Decode.lean:2964 — three such pairs). Extend the
table to a grammar datatype (`tok/seq/alt/rec` + an explicit `Iso`
payload per node); emit and parse as folds; ONE master inversion
theorem under a decidable no-left-corner condition. Follow-set facts
become per-grammar `decide` obligations. Decode.lean 5583 → ~3400;
Emit/Text's hand tables die; the headline `parse∘emit` becomes
provable instead of property-tested.

**F4. One fold behind the harness.** TestKit: `PropSpec`/`DetSpec`/
`DiffSpec` are ONE concept (positive-must-pass + negative-must-fail,
vacuous louder than failing) at three carriers; verdict logic
triplicated (PropSpec.lean:47-54, DetSpec.lean:43-55,
DiffSpec.lean:83-97). One `Spec` structure with a `negatives` list;
DiffSpec's discipline becomes a length-≥2 field. `GateKit.byteTie`
has ZERO consumers (forge owns the byte-tie — justfile:227) — delete.

**F5. `abbrev`-first, compute-by-reduction.** The doctrine's 4.5 is
mostly followed; two violations found: `Determinism.lean`'s
`replay`/`chainHash` ARE `List.foldl` with hand-proved
`foldl_append` restatements (47-99, ~30 lines → 2 abbrevs + core
citations); `deltaChain` (LinearMachine.lean:147) same. Rule:
before proving ANY List/Option/Finset lemma, check core+mathlib —
flatland's review found ~20 hand-proved core duplicates under stale
"core has no X" comments; require the check cited.

## 4. Proof automation — the honest policy

Census (non-test): schema-lang proof core: simp 99, cases 124,
rfl 71, simp only 61, omega 35, **grind 0, aesop 0**. dbsp+Machines:
538 theorems, omega well-used, **aesop 0**, grind only inside
`machine_safety`. The `zset` simp set: tagged on lemmas
(ZSet.lean:104+), invoked at **zero** sites — populated-but-unused,
theater by the doctrine's own words.

The flatland doctrine said "no Aesop-heavy proofs — automation for
arithmetic, not structure." That stance is RIGHT for this repo and
worth keeping, sharpened: proofs here are *artifacts* — cited by
`#check_cert`, pinned by byte-ties, diffed in review. Proof search
rots silently under drift; generated proofs and reduction don't.
So the automation ladder for this toolkit:

1. **Generative first** (the repo's real automation edge):
   `declare_enum_wire` ships codec+4 theorems+negative control per
   enum; `machine!` discharges 88-92% of safety POs. Extend this
   family (D5, `declare_inversion` for the parser lemma twins,
   `deriving`-with-proofs for row codecs, one `ToExpr` instance).
   Every hand-written proof FAMILY is a macro that hasn't been
   written: `stream_cases` (funext;cases<;>simp ×9+ in dbsp),
   `nullability_split` (Decode's required/nullable twins, -350
   lines), `binop_case`/`frame_tail` (Sem.lean exec_typed, -140),
   `fuel_ge` (Correct.lean's 15-succ destructures).
2. **grind** — core in v4.33, zero new dep EVERYWHERE (the
   "schema-lang can't" assumption is wrong: grind needs no mathlib).
   Its niche: the propositional/`by_cases` matrices —
   `cascade_two_commute`'s guard matrix (TickCascade.lean:213-240),
   the membership `have`-blocks (TickCascade.lean:65-167, ~35
   lines), Subschema's `List.mem` inductions, Relational's `_pos`
   family (~26→14). And it should join `machine_safety`'s ladder —
   already does (Dsl.lean:78); extend the same ladder to
   `guard_omega`'s successor for Sync's hand-proofs.
3. **omega/bv_decide/decide**: omega already good (Convergent,
   Staging, StreamElim). `bv_decide` for UInt64 kernel contracts
   exists in proofkit.Binop — but nothing imports it; either move
   those theorems next to the wasm lowering they describe or admit
   the contract guards nothing and cut.
4. **Wire or strip simp sets**: `zset` gets invoked or untagged —
   no third state. Enable core's `unusedSimpArgs` linter tree-wide
   (free detector of hand-listed members).
5. **aesop**: allowed in dbsp/Machines (mathlib present) for LEAF
   goals — the `distinct` family, `map_inj_distinct_comm` (41-line
   Finset.sum_eq_single slog). Never for structure; never in
   cert-cited theorems (the cert gate wants stable, inspectable
   terms). Expected yield is small precisely because the families
   above are macro-shaped, not search-shaped.
6. **mathlib policy**: kernel packages stay core-only — codegen-core,
   substrait (public wire lib, D1), TestKit, LintKit, and the NEW
   kit home (§5, the correspondence shapes need zero mathlib —
   Foundations.lean imports only two mathlib LINTER modules, a
   bogus coupling). Everything above (schema-lang, wasm-backend,
   the app packages) already has mathlib in closure via Machines —
   use it narrowly (`Data.Finsupp`, order/lattice fixpoints,
   `Finset` sweeps), never `import Mathlib`.

Also: `Substring`/fuel cleanups — the fuel inventory shows most
`fuel` is fake partiality with a proved exact measure beside it
(`parseType` has `typeDepth` + monotonicity already proved,
Decode.lean:601-700; `decodeRel` is the in-repo WF exemplar,
:4789-4915). Convert fuel→`termination_by` where the measure is
structural; keep fuel only where it IS semantics (Sem.exec step
budget, cascade cap). `partial def` count: 18; every one is a
correctness-theorem blocker (Emit.Text's partials are why
`parse∘emit` is property-tested, not proved).

## 5. The cohesion moves (the actual refactors)

Ordered by leverage. Each is gate-checkable independently.

**M1. Liberate the kit.** Move `Iso`/`PartialIso`/`Denotes`/`ReprOp`/
`iterateBounded` out of Machines.Foundations into a core-only home
(codegen-core or a new `kit` package; drop the mathlib-linter
imports). Instantiate it: every codec ships a `PartialIso` value
(the append-form lemmas ARE the law, transported through `bind`);
edgepython's parity theorems become `ReprOp` squares; the mangler
laws become instances; `EnumWire` generates the `PartialIso` wrapper
per enum. Foundations' `Dag`/`iterateBounded` either get their
consumer (the cascade scheduler) or move to Tests. This converts
~145 hand-rolled agreement theorems into instances of three shapes —
and gives the tree a searchable, checkable answer to "what reads
agree here?"

**M2. One behavior substrate: dbsp+Machines made loadbearing.**
The canon rows, cashed:
- `Machines.Convergent.InfiniteRun (steps : Nat → S)` IS
  `Dbsp.Stream S` — type it as such (free, Machines already deps
  Dbsp); the D/I theorems then APPLY to machine runs.
- `RewindableMachine` = `ChangeInversion` + `action s h = patch s
  (deltaOf l s h)`: `rewind_suffix` becomes iterated
  `correct_invert`, and journal=`D`, rewind=group-subtraction stop
  being comment cross-refs.
- The cascade's `cascade_two_commute` (TickCascade.lean:179, 59
  hand lines) IS `DeltaSystem.disjoint_commutes` at
  `S := rows, Mut := UpdateItem, writesOf := UpdateItem.writes` —
  one instance + the row-level neutrality lemmas it already has,
  and N-update order-freedom (`applySeq_perm`) comes free. This is
  the template for "schema-lang INSTANTIATES dbsp instead of
  re-proving at row level."
- Delete the string Session layer (it's `P := String` with
  delegating one-liners; `tsession` projects payloads to `""` —
  payload-independent by construction, Session.lean:301). The typed
  layer becomes the only layer; schema-lang.Session's bridge
  theorems evaporate (~90 lines across two packages).
- Delete `ConvergentMachine` (zero consumers; `Convergent` wins).
- The differential oracle, named: it IS `Machines.Refine.RefinesFun`
  between Lean eval and wasm exec, discharged by testing — saying
  so buys the vocabulary (simulation, trace inclusion) for free.
- The product edge: `Ckt Func` → Rust emitter, `incrementalize_ok`
  cited BY NAME in the emitted header, `#check_cert` in CI —
  certification drift = build error. Substrait `Rel` → `Ckt`
  lowering: 7/10 ctors lower today against Relational's operators;
  `aggregate` needs one linear measure operator; `sort`/`fetch` are
  honestly out (no incremental top-k theory — say so, don't fake
  it). THIS is what makes dbsp earn its 3.6k lines.

**M3. Semantics attached to the op table (the edgepython lesson).**
Two wasm evaluators exist because `Wat.Op` is frozen and Sem is
lane-owned read-only; edgepython re-implemented the frame machine
with zero proofs (Eval.lean:131-175 ≈ Sem.lean:250-261). Fix: the
per-op semantics (stack transform + step) lives NEXT to `Wat.Op`;
Sem's theorems quantify over the table; a new op extends renderer +
checker + evaluator + theorem in one place — the closed-universe
rule (`Ty` extends every emitter, compiler-enforced) applied to
semantics. edgepython deletes its evaluator, parity-proves its
Python semantics against the shared one.

**M4. The authoring surface, derived not written.** The dogfood
packages prove the gaps (feature-flags is the audit): a user today
learns ~9 concepts and hand-writes ~7 derivable artifacts. Kill, in
order: (a) the spec/impl double signature — `@[implements Spec.foo]`
checks the body against the registry at elab; write the type ONCE;
(b) Async.Future/Stream — ONE copy in SchemaLang (the reifier's
name-match is the obstacle; a canonical home fixes it); (c)
structure-side derive to match `derive_variant_cases` — schema
abbrev, RowVals mirrors (`userSchema`, `flagSentinelRow`,
`userNameLenRow` are hand-copied field lists), `toVList`; (d) the
`set_option linter...false` ritual — framework-emitted decls exempt
by construction. Test: the template's spec+impl should shrink to
~half and every deleted line should be a concept the user no longer
learns.

**M5. Emitters: use the spine.** `Registry.pipelineRust`
(Emit/Registry.lean:120-167, ~48 lines) is a hand-inlined copy of
exactly what `Emit.Machine.moduleRust` generates generically — and
Registry already imports Emit.Machine. One call deletes ~60 lines.
Same class: wasm-backend's `worldWitOf` hand-mirrors the WIT that
`Emit.Wit.worldOf` folds (GenMain imports SchemaLang — the emitter
is IN SCOPE); `asyncFns` is a hand table beside the registry's
`FuncSem.delivery`; the oracle has two disagreeing sources
(`oracleSrc` string in GenMain vs `Oracle.lean` — regenerating
silently drops 130 Plausible rows; P0 fix). Extend the Rust `Item`
AST (inherent impl, match, attribute nodes) to reclaim the 72
`.raw` sites, or accept raw and stop pretending the AST covers
modules. Driver loop dedup: one `runEmitters` in codegen-core
(schema-lang/faults GenMains copy it).

**M6. Deletions (the concept-reduction half).**
- `Field.lean` (HasField duplicates HasCol; only consumer never
  uses it), `Vortex/DataFusion.lean` (32 lines, zero code — all
  comment; move verdict to notes), `Bridge.lean` (no consumer;
  fold its 60 real lines next to Vortex.Lower if the test earns
  it), `Subsystems.lean` (rename-layer over proved theorems),
  `Determinism.lean`/`Effects.lean` (wire per M2 or die),
  `ConvergentMachine`, string Session, `Parser.jump`, empty
  `Substrait/Decode/`, `target/lit.lean`, GateKit, proofkit
  (Ladder = `machine_safety` duplicate — merge; Binop → consumer
  or cut; ImplementedBy is a tutorial), ledger (delete, or grow
  into THE dbsp dogfood: deposits-as-deltas, balance-as-integral —
  the canon made demo), `Ty.eqViaAns` routing indirection,
  substrait's `decEq?` (299 lines) in favor of `eqAns` +
  completeness lemma (~60 lines), one of QLang's/substrait's two
  query surfaces (merge: QLang's compile/instance-as-data upstreams
  into substrait; `Query := Builder × Writer errors`), one of the
  two did-you-means, one of the two axiom gates (the env linter
  subsumes the shell grep — AxiomAllowlist.lean:15-17 says so
  itself), the third copy of the package inventory
  (PackageNamespace.lean:67-86 vs justfile lean_pkgs vs lakefiles —
  derive from the manifests).

## 6. The 25% cut — honest math

Non-test tree: ~38.6k lines. Verified per-region estimates:

| Region | Est. cut | Main levers |
|---|---|---|
| schema-lang proof core (7.1k) | ~1550 (22%) | D1/D2/F1 merges, comment debloat (44-55% comment files), Field deletion |
| emit/meta + codegen-core + LintKit (4.4k) | ~755 (17%) | M5, ToExpr consolidation, attr macro, comment debloat (Reflect 31%→~15%) |
| dbsp + Machines (7.4k) | ~1000-1100 (15%) | §4 macro families, M2 deletions, NestedCycle/Operators kit unification (~120+150→~120+50) |
| substrait + wasm-backend + qlang + edgepython (16.7k) | ~2900 (17%) without F3; ~4100 (25%) with | decEq→eqAns, nullability_split, Sem macros, comment debloat, edgepython evaluator deletion |
| **Total** | **~6.2k (16%)** safe; **~8.5-9k (22-23%)** with F3 + M6 deletions | |

The last ~2-3% to hit 25% tree-wide comes from the Tests side
(same macro families apply; out of scope here but large — substrait
Tests alone re-lists the op tables) and from M6 whole-module
deletions counted conservatively above. 25% with zero loss is
reachable; ~16-18% is reachable WITHOUT the grammar rewrite, purely
from dedup + debloat + automation.

Comment doctrine (the debloat rule set): module headers keep
OWNERSHIP + DELIBERATE EXCLUSIONS + DRIVING DECISION (three lines,
not fifty). Delete: session archaeology ("GATED OFF" followed by
"RESOLUTION (this session)" at WasmBackend.lean:543-554; "the
landing site's history" Gen.lean:135-143; v1→v2→v3 history lessons
GenCtx.lean:1-38), changelog-in-headers ("added by the cases lane"),
book-report provenance repeated per-section (Encoding.lean — one
header note suffices), docstrings restating the signature, the 8×
verbatim nolint-justification string in LintKit, and the 15 stale
`notes/lean/*.md` paths + 8 references to the absent `Flatland`
package (point at real paths in THIS repo or at flatland's notes by
name, not fake local paths). Keep: honesty ledgers (what's NOT
proved), trap warnings with the fix, decision records. Target
comment ratio: ~15% tree-wide (currently 25-30%, with files at
44-64%).

## 7. Sequencing

1. **P0** oracle single-source (silent test-strength regression).
2. M1 kit liberation + first instances (codecs as PartialIso;
   EnumWire generates the wrapper). Gate: no statement changes.
3. M6 deletions batch (all verified zero-consumer). Gate: build.
4. M5 emitter spine (pipelineRust, worldWitOf, asyncFns,
   runEmitters, ToExpr). Gate: byte-tie — outputs must not change.
5. §4 automation batch (macro families, grind sites, zset wire-or-
   strip, unusedSimpArgs on). Gate: proofs green, axiom gate.
6. D5 machine! entourage + M4 authoring derives. Gate: template
   dogfood — the template shrinks.
7. D1 VExpr tagless/RawTy + M2 DeltaSystem instance + Session
   deletion. Gate: cascade theorems green, byte-tie.
8. F3 substrait grammar framework (the big one; split Decode.lean
   along its section structure FIRST, per the doctrine's
   module-splitting rule).
9. M3 op-table semantics; D3 Sem GADT. Gate: wasm differential.
10. Product edges: Ckt→Rust with cert citations; Rel→Ckt lowering;
    aggregate measure operator. The point of everything above.

Each step ends green per the repo rule (`just lean-build &&
just lean-axioms && just gates`).
