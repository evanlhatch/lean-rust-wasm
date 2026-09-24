/-
# TextKit.Suggest — the ONE did-you-mean engine

The closed-world error discipline (15-patterns #16): every failure over a
closed world ENUMERATES the valid space + appends the did-you-mean —
one engine, one suffix. `suggestFor` is that suffix AS DATA: `none` =
nothing close, `some s` = the rendered suffix the consumer appends (or
stamps into `Diag.suggest` — `Diag.closedWorld`'s constructor is the
first consumer).

Provenance: mined from
`legacy/lean/codegen-core/CodegenCore/DidYouMean.lean` (the ranked
engine) + `GenKit.lean` (`didYouMeanSuffix` — the one tree-wide suffix
format, ported verbatim as `suggestSuffix`). The bounded edit distance
(`editDistance?`) names the exact-semantics wrapper over core
`Lean.EditDistance.levenshtein` (the compiler's own cutoff-bounded DP).

Cone/build note (06 §8): this is the engine's ONE home — the C0
module-system substrate, the lowest point both diagnostic sides import
(Kit's Suggest/Diag/Registry re-export or delegate to these; the
envelope `TextKit.Diag` sits directly above; nothing here imports any
Kit module — the textkit→kit direction is build-impossible, the
module→non-module boundary).

Core-only (no mathlib/Batteries); `Lean.EditDistance` is core.

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

module

public import Lean.Data.EditDistance

@[expose] public section

namespace TextKit

/-! ## the bounded edit distance -/

/-- The edit distance between `a` and `b`, when it is at most
    `maxDist`. `none` = the true distance exceeds the bound (core
    `levenshtein`'s `some` is NOT guaranteed to be under the cutoff —
    the explicit filter keeps the semantics exact). -/
def editDistance? (a b : String) (maxDist : Nat := 3) : Option Nat :=
  match Lean.EditDistance.levenshtein a b (maxDist + 1) with
  | some dist => if dist ≤ maxDist then some dist else none
  | none => none

/-! ## the ranking -/

/-- The ranked candidates: nearest first, ties lexicographic; the
    bounded DP's `none` rows drop out. The ONE ranking every
    did-you-mean reads. -/
def didYouMean (got : String) (dict : List String) (maxDist : Nat := 3) :
    List String :=
  let scored := dict.filterMap fun d =>
    match editDistance? got d maxDist with
    | some _dist => some (_dist, d)
    | none => none
  let sorted := scored.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  sorted.toList.map (·.2)

/-! ## the suffix (the one tree-wide did-you-mean format) -/

/-- The did-you-mean suffix every closed-world error path appends —
    the legacy `GenKit.didYouMeanSuffix` format, verbatim: the ranked
    candidates (`TextKit.didYouMean`), joined `", "`; empty ranking =
    empty suffix (no close match, no guess). -/
def suggestSuffix (got : String) (valid : List String) (maxDist : Nat := 3) : String :=
  let c := TextKit.didYouMean got valid maxDist
  if c.isEmpty then "" else s!" — did you mean: {String.intercalate ", " c}?"

/-- The suffix as data: `none` = nothing close (the error still
    enumerates `valid` — the enumeration is the message, the suffix is
    the shortcut), `some s` = the rendered did-you-mean. THE consumer
    route for every closed-world failure (`Diag.closedWorld` fills its
    `suggest` field here). -/
def suggestFor (got : String) (valid : List String) (maxDist : Nat := 3) :
    Option String :=
  match suggestSuffix got valid maxDist with
  | "" => none
  | s => some s

end TextKit

end -- @[expose] public section
