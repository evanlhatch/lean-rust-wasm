# 06 — The Lean 4 operative rules

The kernel/elaborator constraints + the idioms this project lives by.
Every rule cost real time; do not re-pay. Provenance for each: the tree's
AGENTS.md trap list (the session's paid tuition).

## 1. The type system first

Correctness is a code property. Elaboration is the gate. Indexed types,
instance search, defaulted proof fields, `nomatch h` on impossible
indices — before any runtime check. Instance search is the legality
mechanism and stays SHALLOW: small class graphs, reducible wrappers,
short lists; a class needing `maxHeartbeats` is a design smell (07 §4
watches the cost — with the degradation rule: a gate that blows the
elaboration budget drops a ladder rung WITH A NOTE in the module header,
never a silent heartbeats bump).

## 2. Kernel constraints (do not fight them)

- No open-universe quantification — closed matches are the
  exhaustiveness authority; instance families ride on top.
- The GADT sibling rule: nested `List (Value t)` inside an indexed
  inductive is kernel-forbidden; sibling inductives or sigma-encoded
  packages are the pattern.
- wf-recursion (`termination_by`) is KERNEL-OPAQUE — `decide`/rfl over
  anything touching it never reduces. Prove a specialized reduction
  lemma for the concrete shape and route the check through it.
- `Option` carries no Prop — proof-carrying directed answers use
  EqAns-style inductives (`.yes h | .no`).

## 3. The abbrev rule

Field/type lists used in instance search MUST be `abbrev` (reducible);
a plain `def` defeats elaboration-time resolution. Same for role-named
types and boundary markers.

## 4. Dot-notation order

`x.f args` needs `f`'s FIRST explicit arg to be x's type. Check
signatures before dot-chaining; mismatches are silent elaboration
failures.

## 5. Equations and simplification

Every recursive def ships its `@[simp]` equation set where proofs
consume it; raw-equation consumers (wf/fuel proofs) are tagged + the
lint row names the reason. Match arms bind ctors dot-shaped (`.ctor`) —
a bare ident binds a variable and later arms become redundant
alternatives. `simp only` over hand lists is a smell where a named attr
or generated set exists; an attr with zero invocations is theater —
wire it or strip it.

## 6. Totality

Structural recursion or `termination_by` with an explicit measure is the
default (the `sizeI/sizeL` pattern). Fuel is semantics ONLY where it IS
semantics (exec step budgets, cascade caps); fuel for parsing/walking
converts to `termination_by` or a length index. `partial` carries a
written reason; the allowance ratchets down only.

## 7. Metaprogramming hygiene

- Generation > hand-writing: a family of N near-identical decls is a
  macro that hasn't been written (check family!/declare_*/deriving
  first).
- Generated decls carry `@[derived]`; no per-file `set_option linter…
  false` rituals.
- Quotations: prefer `Qq`; template references are PRERESOLVED idents
  (`mkCIdentFrom`) — plain quoted idents carry macro scopes and
  silently fail on dotted names.
- One reifier family for `Ty` (the shared ToExpr + the drift pin);
  never a new quoter per command.
- Every instance-gated surface ships curated failures (05 §4); a DSL
  whose elaborator spews a typeclass wall is not done.
- Build-time `#guard`s live at generation sites: derived entourage,
  emitter laws, codec sample round-trips — tests live IN the build for
  generated artifacts.
- the `prefix` token is reserved; the f! brace escape is `\{` not `{{`;
  GADTs forbid nested `List (Value t)` (mutual sibling inductive);
  Except monads: `throw`, never `return .error`; `String.replace` is
  (s pattern replacement) — check `|>` arg order; `intercalate` as
  dot-syntax swaps sep/list; root-module imports are NOT re-exported —
  import what you name; `String → Type` is `Type 1`; do-notation hoists
  `←` out of `&&` EAGERLY (short-circuit guards need nested ifs);
  `SimplePersistentEnvExtension.addImportedFn` takes `Array (Array α)`;
  a `module` cannot import a non-`module` file; attr-registering
  `initialize` must be in a meta section to run at import; in a module a
  theorem is `.axiomInfo` at attribute-application time; imported
  theorems aren't `isTheorem` in module consumers either; app_unexpanders
  must be public; `public meta import` for meta deps inside public meta
  sections; a public import of a mathlib-carrying module leaks mathlib's
  names into legacy consumers (the Flag collision) — registration
  surfaces never publicly depend on mathlib-carrying modules.

## 7b. Text building (the rope rule)

Emitted text's STRUCTURE = `Std.Format` or a rope (append O(1), one
linear render walk); leaves = `String.join`/`intercalate`. NEVER a
left-nested `++` loop over String/List (quadratic). Byte-tied emitters
stay string-exact (the tie forbids re-pinning churn) — the rope rule
governs NEW text surfaces.

## 7c. Quotients

Quotients ONLY where: order is semantically irrelevant AND a canonical
rep exists (deterministic, total) AND no wire/guest/decide/emitted layer
carries the quotient (they stay on the canonical rep — Lean quots kill
deriving/BEq/match and defeat the guest) AND the respect obligation is
paid once at the encoder boundary. Otherwise the structure-level theorem
(proved once, cited) is the Lean-correct form.

## 8. Batteries/core first

Before proving ANY List/Option/Fin/Char/String lemma, check core +
Batteries (host-side packages may import Batteries; guest-compiled
modules stay core-only; the kernel cones C0/C1 stay mathlib-free — the
import-ban table is DATA, a cone-low module importing cone-high is a
gate failure). A "core has no X" comment must cite the check run (the
zipIdx/mergeSort lesson).

## 9. Mathlib discipline

C2+ only; narrow imports in hot modules; never a blanket
`import Mathlib` where a module import does.

## 10. The honest ceiling

Generated proofs ≠ proof search: grind/aesop-grown terms rot under
drift; templates + decide are build-stable; cert-cited theorems stay
inspectable and reduction-native. A hand theorem's justification names
the relational content the ladder can't reach.

## 11. Two more traps (the audit caught them missing)

- **Equation lemmas bind ALL binders, implicits included, when the
  match needs them structurally** (the legacy `Row.setN` lesson): a
  wildcard `_` on an implicit the generated equation must mention
  leaves the equation unusable — bind it (named, dotted) at the match.
- **Deltas at the boundary, inversion in the log** (the event-sourcing
  architecture invariant): the journal carries the inversion witnesses;
  the boundary speaks net deltas. Never invert at the boundary, never
  ship the raw event stream across it. the pattern: the boundary's net delta is the table's lookup row.)

## 12. The grind discipline (the wave-31 policy)

Refines §10: grind is SANCTIONED where the value is SHRINKAGE +
solidity, never speed — a slower-but-solid grind closer beats a hand
simp chain that fights drift. The owner's framing is explicit: elab
cost may rise; robustness under small statement drift is the prize.

**The honest classes** (migrate these):
- Induction-heavy byte-arithmetic arms: the varint/fuel position
  arithmetic where a hand chain fights div/mod (the varint migration:
  15 LOC → 1 grind (splits := 24) line).
- Closed-ground set/arithmetic goals: bounded Nats, byte residues,
  length bookkeeping — nothing quantified at open universes.

**The hostile classes** (never grind these):
- Exact-image div/mod recursion: the splits explode — grind's case
  tree is exponential in the div/mod count; the hand chain wins.
- Decide-witnesses: a goal closed by `decide` stays `decide` (grind
  adds nothing and its terms are opaque).
- Pure omega one-liners: a proof already `by omega` gains nothing —
  grinding it only imports choice. Migration = SHRINKAGE; there is
  no shrinkage from 1 line to 1 line.
- Reduction-critical teeth: grind's terms are OPAQUE to kernel
  reduction — the tree's rfl teeth ride reduction. NEVER grind a
  proof whose TERM must reduce (the decoder's rfl teeth, the equation
  lemmas, anything consumed by `decide`/`rfl` downstream). A law
  consumed by rewriting only is fair game.

**The redundancy-gate spelling**: 4.33's redundancy gate FORBIDS
passing IHs (or any local names) explicitly — a hard error on local
names. The sanctioned spelling is named LEMMAS in the brackets +
`(splits := N)` where the case tree needs a nudge; local facts (the
IHs, the `have`s) are picked up automatically from the context. Keep
the needed facts in context and let grind find them.

**The choice-axiom note**: grind imports `Classical.choice` — a
tactic-migrated proof's pin gains choice over the bare triple. That
drift is HONEST (no `sorry`, no new axiom KIND): the Axioms.lean pins
update, the report notes it, and the INTEGRATOR re-baselines at the
wave's commit — never mid-order, never `--write`.

**Drift-stability**: where a grind closer feeds many downstream
goals, pin the pattern — a `grind_pattern` guard per lemma so a
statement drift fails the guard loudly instead of silently unfinding
the E-matching. A grind closer with no guard is acceptable only where
it consumes exactly one goal.

**The stays**: a migration that defeats you twice stays omega/hand —
and its shape joins the hostile list WITH THE EVIDENCE (the goal that
defeated grind, so the next agent doesn't re-pay). The wave-31 ledger
(wasmcore/WasmCore/Decode.lean):
- `decVarNatR_decVarNat`'s cons case — grind (splits := 32) over
  `decVarNatR`/`decVarNat?` equations cannot digest the `bind`
  lambda's paired destructuring against the `drop (pos' - pos)`
  arithmetic; the hand case tree (one defeat, shape matches this
  class) stays.
- `decFuncType_enc` and the seven slot laws — grind cannot reduce the
  byte-guard Decidable instances (the `badFuncType`-class refusals):
  the guard conditions sit behind `UInt8` casts that `simp only`
  fires but grind's terms treat as opaque. This is the
  reduction-tooth boundary showing up as an elaboration failure, not
  just a kernel one.
- `slebFits_step` needed TWO nudges (the `128 ^ (k + 1)` atom needs
  `Nat.pow_succ` passed as a named lemma + `slebP_prop` kept in
  context) — inside budget, landed; the nudge shape is the pattern.
