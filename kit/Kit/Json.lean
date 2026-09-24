/-
# Kit.Json — the minimal JSON builders (the manifest emitters' surface)

`jsonStr` is the ONE escaping decision (quotes + backslashes — paths and
names are the whole payload today); the builders keep the seams (the
`", "` field/element separator, the `": "` after keys, the two brace
styles) in one place.

DELIBERATE SHAPE (mined from legacy
`codegen-core/CodegenCore/Emit/Core.lean`'s JSON section, ported fresh):
values are pre-rendered JSON TEXTS, not a `Json` AST — no parser, no
bignum, and NO escaping decisions beyond `jsonStr`'s. wasm-backend's
`Lean.Json` oracle keeps its own escaper — the two DISAGREE on control
characters, so the unification stops here (the byte-tie law: no output
byte changes).

`objPad` exists because the top-level manifest ROWS pad their braces
(`{ "package": … }` — byte-tied in the legacy manifests) while every
nested object is tight.

CONSUMER NOTE: `Kit.Duel.manifestBody` is TAB-delimited (the duel's
consumer contract splits rows on the tab), NOT JSON — deliberately NOT
rewired (rewiring would change the artifact bytes, breaking the consumer
contract for zero gain). The JSON consumers are the future manifest
emitters (the legacy WIT-fixture/sweep/forge-jobs manifests' mandate
ports); the KitTests pins are the standing evidence in the meantime.

Core-only (no mathlib/Batteries, no imports).

The five questions (notes/v3/01-core.md):
- root: Crossing — manifest text read by external JSON consumers.
- carrier grade: pre-rendered texts over ONE escaper — no `Json` AST,
  no second escaping decision anywhere.
- spine reading: the artifact stage's JSON leaf mechanics (05 §2: the
  byte-tie is the correspondence evidence for every future manifest).
- ladder rung: rung 1 — total string folds; every shape fact over
  concrete manifests is a `decide`/pin.
- gate row: none yet — lands with the first JSON manifest emitter's
  gate; the KitTests pins are the standing evidence.
-/

namespace Kit.Json

/-- Escape a JSON string (paths + names only — quotes and backslashes
    are the whole story). Shared by every manifest emitter, HERE so no
    two emitters can disagree on the escaping. -/
def jsonStr (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

/-- A JSON object, tight braces: `{"k": v, "k2": v2}`. Keys render
    through `jsonStr` (they are fixed identifiers — no escapes fire);
    values are pre-rendered JSON texts. -/
def obj (fields : List (String × String)) : String :=
  "{" ++ String.intercalate ", " (fields.map fun (k, v) => jsonStr k ++ ": " ++ v) ++ "}"

/-- A JSON object with PADDED braces: `{ "k": v, … }` — the manifest
    ROW style (every top-level entry in the byte-tied manifests). Same
    fields/separators as `obj`. -/
def objPad (fields : List (String × String)) : String :=
  "{ " ++ String.intercalate ", " (fields.map fun (k, v) => jsonStr k ++ ": " ++ v) ++ " }"

/-- A JSON array over pre-rendered element texts: `[e1, e2]` (the empty
    array renders `[]`). -/
def arr (elems : List String) : String :=
  "[" ++ String.intercalate ", " elems ++ "]"

end Kit.Json
