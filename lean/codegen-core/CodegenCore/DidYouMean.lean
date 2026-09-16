/-
# CodegenCore.DidYouMean — the closed-world suggestion engine

MOVED here from `SchemaLang.DidYouMean` (verbatim body, new home): the
engine is core-only (core `Lean.EditDistance.levenshtein` + core
`List`/`Array` machinery) but its consumers are every error path DOWNSTREAM
of codegen-core — the faults registry's payload diagnostics, the
wasm-backend's driver errors — and the backend is deliberately core-only
(it does not import SchemaLang; its lakefile records why). Home = the
highest package every error-path consumer already reaches.

Provenance: lifted verbatim from flatland's `FlatlandDsl.Error`
(TOOLKIT §11.1): our DSLs are CLOSED — we know every type, field, and
legal transition — so errors ENUMERATE THE VALID SPACE. For an LLM (or a
human), an error that lists the valid moves is a self-correcting prompt.

The distance engine is core `Lean.EditDistance.levenshtein` (the same
cutoff-bounded DP the compiler's own did-you-mean uses); dedup is core
`List.eraseDups`. Name lists are small; the cutoff bounds the work.
-/

module

public import Lean.Data.EditDistance

@[expose] public section

namespace CodegenCore

/-- The closest dictionary entries to `got`, nearest first. The closed
    world means the dictionary is always complete — the candidates ARE
    the valid space, not a heuristic. The cutoff (`maxDist + 1`) prunes
    the DP; the explicit `≤ maxDist` filter keeps the semantics exact
    (a `some` from `levenshtein` is not guaranteed under the cutoff). -/
def didYouMean (got : String) (dict : List String) (maxDist : Nat := 3) : List String :=
  let scored := dict.filterMap fun d =>
    match Lean.EditDistance.levenshtein got d (maxDist + 1) with
    | some dist => if dist ≤ maxDist then some (dist, d) else none
    | none => none
  let sorted := scored.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  sorted.toList.map (·.2)

end CodegenCore
