/-
# Kit.Suggest — the did-you-mean routes (the shim over the ONE engine)

The closed-world error discipline (15-patterns #16): every failure over
a closed world ENUMERATES the valid space + appends the did-you-mean —
one engine, one suffix. THE CONVERGENCE ORDER: the engine's ONE home is
`TextKit.Suggest` (the cone/build call — the module-system C0 substrate
at the lowest point both diagnostic sides import; a `module` file
cannot import a pre-`module` file, so textkit→kit is build-impossible
and the engine lives down, where Kit already imports TextKit). These
`Kit`-namespaced definitions DELEGATE to it — kept so every Kit-side
consumer (`Kit.Diag.closedWorld`'s shim, FreshName, the KitTests pins)
is interface-preserved.

Provenance: mined from
`legacy/lean/codegen-core/CodegenCore/DidYouMean.lean` (the ranked
engine — landed at TextKit.Suggest as `TextKit.didYouMean`) +
`GenKit.lean` (`didYouMeanSuffix` — the one tree-wide suffix format,
`TextKit.suggestSuffix`).

Core-only (no mathlib/Batteries); the engine's `Lean.EditDistance` is
core.

The five questions (notes/v3/01-core.md):
- root: DATA — a pure suggestion value over String/List, no behavior.
- carrier grade: plain first-order data (guest-thinkable — no classes,
  nothing host-exclusive beyond the core DP).
- spine reading: as-data (the suffix is a String; no IO, no monad).
- ladder rung: rung 1 — the discipline lives in the SHAPE (the consumer
  route is one total function), no proof family needed.
- gate row: the axiom gate (Kit's report rows) + the test pins
  (KitTests: known-answer + ordering pins + the negative control).
-/

import TextKit.Suggest

namespace Kit

/-! ## the bounded edit distance -/

/-- The edit distance between `a` and `b`, when it is at most
    `maxDist`. `none` = the true distance exceeds the bound.
    DELEGATION: `TextKit.editDistance?` is the ONE engine. -/
def editDistance? (a b : String) (maxDist : Nat := 3) : Option Nat :=
  TextKit.editDistance? a b maxDist

/-! ## the suffix (the one tree-wide did-you-mean format) -/

/-- The did-you-mean suffix every closed-world error path appends —
    the legacy `GenKit.didYouMeanSuffix` format, verbatim: the ranked
    candidates (`TextKit.didYouMean`, nearest first, ties
    lexicographic), joined `", "`; empty ranking = empty suffix (no
    close match, no guess). DELEGATION: `TextKit.suggestSuffix`. -/
def suggestSuffix (got : String) (valid : List String) (maxDist : Nat := 3) : String :=
  TextKit.suggestSuffix got valid maxDist

/-- The suffix as data: `none` = nothing close (the error still
    enumerates `valid` — the enumeration is the message, the suffix is
    the shortcut), `some s` = the rendered did-you-mean. THE consumer
    route for every closed-world failure (Kit.Diag's `closedWorld`
    fills its `suggest` field here). DELEGATION: `TextKit.suggestFor`. -/
def suggestFor (got : String) (valid : List String) (maxDist : Nat := 3) :
    Option String :=
  TextKit.suggestFor got valid maxDist

end Kit
