/-
# SchemaLang.DidYouMean — the closed-world suggestion engine

Lifted verbatim from flatland's `FlatlandDsl.Error` (TOOLKIT §11.1): our
DSLs are CLOSED — we know every type, field, and legal transition — so
errors ENUMERATE THE VALID SPACE. For an LLM (or a human), an error that
lists the valid moves is a self-correcting prompt.

`editDistance` is the naive DP on purpose: name lists are small.
-/

namespace SchemaLang

/-- Levenshtein edit distance — the did-you-mean engine. -/
def editDistance (a b : String) : Nat := Id.run do
  let xs := a.toList.toArray
  let ys := b.toList.toArray
  let n := xs.size
  let m := ys.size
  let mut prev : Array Nat := Array.range (m + 1)
  for i in [1 : n + 1] do
    let mut cur : Array Nat := Array.replicate (m + 1) 0
    cur := cur.set! 0 i
    for j in [1 : m + 1] do
      let cost := if xs[i - 1]! == ys[j - 1]! then 0 else 1
      cur := cur.set! j (min (min (prev[j]! + 1) (cur[j - 1]! + 1)) (prev[j - 1]! + cost))
    prev := cur
  return prev[m]!

/-- The closest dictionary entries to `got`, nearest first. The closed
    world means the dictionary is always complete — the candidates ARE
    the valid space, not a heuristic. -/
def didYouMean (got : String) (dict : List String) (maxDist : Nat := 3) : List String :=
  let scored := dict.map (fun d => (editDistance got d, d))
  let close := scored.filter (fun (dist, _) => dist ≤ maxDist)
  let sorted := close.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  sorted.toList.map (·.2)

/-- Order-preserving dedup for name lists. Well-founded: the recursive
    call is on a strictly shorter list (filter can only shrink). -/
def dedupStr : List String → List String
  | [] => []
  | n :: rest =>
      let rest' := rest.filter (· != n)
      n :: dedupStr rest'
termination_by
  l => l.length
decreasing_by
  simp_wf
  have h1 : (rest.filter (· != n)).length ≤ rest.length :=
    List.length_filter_le _ _
  have h2 : rest.length < (n :: rest).length := by simp
  omega

end SchemaLang
