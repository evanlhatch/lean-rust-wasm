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
  ship the raw event stream across it. (15-patterns #7 is the
  meta-level analogue; this rule is the data-plane one.)
