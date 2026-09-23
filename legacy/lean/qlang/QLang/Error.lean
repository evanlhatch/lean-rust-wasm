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
import CodegenCore

namespace QLang

/-- The closest dictionary entries to `got`, nearest first — the SHARED
    engine (`CodegenCore.didYouMean`; the local DP copy is deleted).
    Kept as an abbrev so the error renderers below read in domain
    vocabulary. -/
abbrev didYouMean := @CodegenCore.didYouMean

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
