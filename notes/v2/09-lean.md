# 09 — Lean 4 operative rules

The kernel/elaborator constraints and the Lean idioms this project lives by.
Every rule here has a failure that cost real time; do not re-pay them.

## 1. The type system first

- Correctness is a code property (01). Elaboration is the gate. When a Lean
  feature can move a failure from runtime/test to elaboration, use it:
  indexed types, instance search, defaulted proof fields (`:= by decide`),
  `nomatch h` on impossible indices.
- Instance search is the LEGALITY mechanism: classes with `outParam`s
  compute types from inputs (`HasCol s name t n`); head-priority instances
  resolve first. Keep search SHALLOW: small class graphs, reducible wrappers,
  short head/tail lists. A class whose synthesis recurses deeply or needs
  `set_option synthInstance.maxHeartbeats` is a design smell.

## 2. Kernel constraints (do not fight them)

- **No open-universe quantification**: you cannot quantify "for every `Ty`
  ctor" without a closed match. Keep universes closed under their folds; the
  19-arm scalar cascades are irreducible per consumer — the instance-family
  (ShapeLang) is the container, not a grand fold.
- **GADT sibling rule**: nested `List (Value t)` inside an indexed inductive
  is kernel-forbidden. Sibling inductives (`VList`, `Args`) or sigma-encoded
  packages (`AnyExpr`) are the pattern — already used; extend, don't fight.
- **Typeclass search over open families is fragile**: closed matches remain the
  exhaustiveness authority; instances ride on top.
- **wf-recursion is kernel-opaque**: a `termination_by` def's equations are
  NOT definitional. Prove a specialized reduction lemma for the concrete shape
  and route checks through it (the `decVarNat`/`beq_u64_ne` lesson).
- **`Option` cannot carry a `Prop`**: proof-carrying directed answers use
  `EqAns`-style inductives (`.yes h | .no`).

## 3. The abbrev rule

Field/type lists used in instance search MUST be `abbrev` (reducible): a plain
`def` defeats elaboration-time resolution. The same rule covers role-named
types and boundary markers: reducible or they don't resolve.

## 4. Dot-notation order

`x.f args` requires `f`'s FIRST explicit arg to be x's type. Check
signatures before dot-chaining; mismatches are silent elaboration failures.

## 5. Equations and simplification

- Every recursive def ships its @[simp] equation set (where the proofs can
  consume it); where raw equations are consumed on purpose (proofs of
  wf/fuel defs), the def is tagged and the lint row names the reason.
- Match arms bind ctors dot-shaped (`.ctor`); a bare ident binds a variable
  and every later arm becomes a redundant alternative.
- `simp only` over hand-listed sets is a smell if a named attr (`zset`) or a
  generated set exists; an attr with zero invocations is theater — wire it or
  strip it.

## 6. Totality

- `partial def` is a design decision with a written reason (07 §1). Structural
  recursion or `termination_by` is the default; the size-measure pattern
  (`Audit.go`'s `sizeI`/`sizeL` + `decreasing_by`) is the template for trees.
- Fuel is semantics ONLY where it is semantics (exec step budgets, cascade
  caps); fuel used for parsing/walking converts to `termination_by` or a
  length index (the D2 discipline).

## 7. Metaprogramming hygiene (the Generative Edge)

- Generation > hand-writing: before writing a declaration FAMILY, check
  `family!`/`declare_*`/`deriving` (05 §2). A family of N near-identical
  decls is a macro that hasn't been written.
- Generated decls carry the `@[derived]` stamp so lint exemptions are
  structural (no `set_option linter…false` rituals per file).
- Quotations: prefer `Qq`; template references are PRERESOLVED idents
  (`mkCIdentFrom`) — plain quoted identifiers carry macro scopes and
  resolution silently fails on dotted names.
- One reifier family for `Ty` (the shared `ToExpr` + drift pin); never a new
  quoter per command.
- Every instance-gated surface ships curated failures (04 §3); a DSL whose
  elaborator spews a typeclass wall is not done.
- Build-time `#guard`s live at generation sites: derived entourage, emitter
  laws, codec sample round-trips — tests live IN the build for generated
  artifacts.

## 7b. Text building (the rope rule — 16 §5)

- Structure of emitted text = `Std.Format` (a rope: append O(1), render one
  linear walk). Leaves = `String.join` / `intercalate`. NEVER a left-nested
  `++` loop over a `String`/list (`replicate`-style — quadratic).
- A spot-audit of the `String`-leaf layers (manifests, spawn strings, WIT
  text tails) runs the rule; `Format` is the default for all structure.

## 7c. Quotients (16 §2 — the discipline)

- Quotients ONLY where order is semantically irrelevant AND a canonical rep
  exists AND no wire/guest/decide/emitted layer carries them AND the respect
  obligation is paid once at the encoder boundary. Otherwise the
  structure-level theorem is the Lean-correct form (proved once, cited).

## 8. Batteries/core first

- Before proving ANY List/Option/Fin/Char/String lemma, check core + Batteries:
  `mergeSort`+`Sorted`, `partition`, `zipIdx`, `getD`/`getElem?`, `Perm`,
  `Pairwise`, `Nodup`, `String.join`/`intercalate`, `Substring`. A
  "core has no X" comment must cite the check run (the stale-claim class cost
  a review round).
- The decision lattice: decide / omega / bv_decide / grind (never aesop for
  cert-cited theorems). The ladder is `po_ladder`; rungs are `macro_rules`
  extensions by downstream.

## 9. Mathlib discipline

- Kernel cones (C0/C1, 02 §2) stay mathlib-free. Everything requiring mathlib
  lives C2+. The import-ban table is DATA: a cone-low package importing
  Mathlib/Dbsp/Machines is a gate failure, not a discussion.
- Inside C2: use mathlib narrowly (`Data.Finsupp`, order/fixpoints, `Finset`);
  never `import Mathlib` blanket in a hot module.

## 10. The honest ceiling

Generated proofs ≠ proof search: `grind`/`aesop`-grown terms rot under drift;
templates and `decide` are build-stable. Certificate-cited theorems stay
inspectable and reduction-native.
