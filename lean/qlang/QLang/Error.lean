/-
# QLang.Error — the error system foundation

Ported from the flatland lineage's `FlatlandDsl.Error` (TOOLKIT §11.1):
errors are a DESIGNED artifact. The closed-world superpower: our DSLs are
closed — we know every table and column — so errors ENUMERATE THE VALID
SPACE. For an LLM, an error that lists the valid moves is a self-correcting
prompt.

Every error: domain vocabulary, the valid space enumerated, a suggested fix
(the did-you-mean engine). Never a raw typeclass trace, never a bare string.

Excluded from the flatland port: the engine-facing constructors
(`illegalTransition`, `writeConflict`, `missingFloor`) — this package has no
machine/rule layer (the dig's SKIP list).
-/
import Substrait.Typed

namespace QLang

/-- Levenshtein edit distance — the did-you-mean engine. (Name lists are
    small; the naive DP is the right size.) -/
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

/-- The closest dictionary entries to `got`, nearest first. The closed world
    means the dictionary is always complete — the candidates ARE the valid
    space, not a heuristic. -/
def didYouMean (got : String) (dict : List String) (maxDist : Nat := 3) : List String :=
  let scored := dict.map (fun d => (editDistance got d, d))
  let close := scored.filter (fun (dist, _) => dist ≤ maxDist)
  let sorted := close.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  sorted.toList.map (·.2)

/-- One definition, two renderings. Every constructor: domain vocabulary +
    the valid space + the fix. (JSON rendering lands with an elaborator
    layer; the constructors carry the data either way.) -/
inductive QLangError where
  | unknownColumn (got : String) (candidates validSpace : List String)
  | unknownTable (got : String) (candidates validSpace : List String)
  | typeMismatch (context expected got : String)
deriving Repr

namespace QLangError

def renderList (xs : List String) : String := String.intercalate ", " xs

/-- The human/agent rendering. Every message: what was tried, what exists,
    what to do instead. -/
def render : QLangError → String
  | .unknownColumn got cands valid =>
    let hint := match cands with
      | [] => ""
      | cs => s!"\n  did you mean: {renderList cs}?"
    s!"no column `{got}` — has: {renderList valid}{hint}"
  | .unknownTable got cands valid =>
    let hint := match cands with
      | [] => ""
      | cs => s!"\n  did you mean: {renderList cs}?"
    s!"unknown table `{got}` — tables: {renderList valid}{hint}"
  | .typeMismatch ctx expected got =>
    s!"type mismatch in {ctx}: expected {expected}, got {got}"

/-- The plain-string form used by `Except String` failure channels
    (the DSL's only failure channel — never a panic). -/
def unknownColumnMsg (got : String) (validSpace : List String) : String :=
  QLangError.render (QLangError.unknownColumn got (didYouMean got validSpace) validSpace)

/-- Plain-string form for unknown tables. -/
def unknownTableMsg (got : String) (validSpace : List String) : String :=
  QLangError.render (QLangError.unknownTable got (didYouMean got validSpace) validSpace)

end QLangError

end QLang
