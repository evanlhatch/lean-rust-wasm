/-
# Kit.Text — the rope text-builder (the emitters' structure carrier)

The rope rule (notes/v3/06-lean-rules.md §7b): emitted text's STRUCTURE
is `Std.Format` or a rope (append O(1), one linear render walk); leaves
are `String.join`/`intercalate`; NEVER a left-nested `++` loop over
String/List. This module is the rope half.

WHY A ROPE AND NOT `Std.Format`: the rope rule offers two shapes, and
the choice is forced by the byte-tie. `Std.Format` is a pretty-printer —
its render inserts its OWN layout decisions (grouping, line breaks,
indentation) between the leaves, so a byte-tied emitter routed through
it re-pins (and re-layouts) on every `Format` upgrade: the tie forbids
that churn. A byte-tied emitter needs EXACT control of every byte, so
the structure carrier here is a plain chunk tree whose render is exact
concatenation — `render` is the identity on content, with no layout of
its own. `Std.Format` stays available for surfaces where layout IS the
semantics (human-facing diagnostics); generated artifacts do not ride
it.

THE SHAPE: `Text` is a binary tree of chunks — `.nil`, `.str` (a leaf,
the only place raw String bytes enter), `.app` (O(1) constructor). The
assembly is O(1) per structural join (`app`, `cat`, `sepBy`); the
render is ONE walk (`chunks`) that flattens the tree into the chunk
list, and the single leaf-level concatenation point is core's
`String.join` — the rule's sanctioned leaf op (06 §7b: leaves =
`String.join`/`intercalate`). Core's `join` is itself a left fold over
the chunk list, so the render's cost is linear in the node count plus
core's own fold — the point the rule scores is that the assembly never
re-pins: chunks are never re-copied at each structural step, only at
the ONE final render.

THE LAWS (the discipline a new text surface inherits):
- `render_app` — render is a monoid morphism over `.app`: structure
  composes without touching bytes.
- `render_cat_strs` — the template spine (`cat`) is core `String.join`.
- `render_sepBy_strs` — the line-join (`sepBy`) IS core
  `String.intercalate`, byte-for-byte. These two are the byte-tie's
  theorem face: a rope-assembled emitter renders EXACTLY what the
  string-level template spelled, so rewiring structure never moves the
  artifact bytes (`gates gen-check` is the runner-side proof).

THE DISCIPLINE FOR NEW TEXT SURFACES (06 §7b, operationalized):
1. Structure = `Text` (`app`/`cat`/`sepBy`); leaves = short fixed-shape
   String templates (`++` over literals + interpolated atoms is FINE
   at a leaf — the rule targets structure-building, not a leaf's
   bounded template).
2. One render at the consumer boundary (`render`), never an
   interleaved `++` chain that re-pins partial results.
3. List-shaped joins (statement sequences, line blocks) go through
   `sepBy`/`cat` — O(1) per element — never a fold of `++`.

CONSUMERS: `SchemaCore.Emit.Rust` (the first — the byte-tied rewire,
proved byte-identical by gen-check). Named follow-ups (separate
zones/risks, not yet rewired): `SchemaCore.Emit.witEmitter`
(schemacore/SchemaCore/Emit.lean) and `SchemaCore/Snapshot.lean`'s
printer.

Core-only (no imports — pure Init).

The five questions (notes/v3/01-core.md):
- root: Crossing — the emitter's STRUCTURE read into exact bytes (the
  carrier between the target grammar's shapes and the artifact text).
- carrier grade: first-order over String/List — guest-thinkable; the
  laws are decided/`rfl`-reducible at concrete use.
- spine reading: the artifact stage's material (01 §5: the emitter's
  `run` produces the files; this is what the files are built from).
- ladder rung: rung 1 + the three bridge theorems (the smallest honest
  rung for a carrier whose consumer is a byte-tie).
- gate row: gen-check (the byte-tie over the rewired emitter) + the
  test pins (KitTests: the bridge laws + the negative controls).
-/

namespace Kit

/-! ## the rope -/

/-- The rope: a binary tree of text chunks. `.str` is the ONLY leaf —
    the one place raw String bytes enter the structure. -/
inductive Text where
  /-- The empty structure (renders to `""`). -/
  | nil
  /-- One leaf chunk. -/
  | str (s : String)
  /-- O(1) structural append. -/
  | app (a b : Text)

/-- The ONE render walk: flatten the tree into its chunk list (linear
    in the node count for the right-nested shapes the combinators
    build), then core's `String.join` — the rule's sanctioned leaf op —
    does the single concatenation pass. -/
def Text.chunks : Text → List String
  | .nil => []
  | .str s => [s]
  | .app a b => Text.chunks a ++ Text.chunks b

def Text.render (t : Text) : String := String.join (Text.chunks t)

/-- The template spine: right-associated append, O(1) per element.
    The rope shape the `++`-chain templates take — every old `a ++ b`
    splice becomes one `.app` node, no re-pinning between steps. -/
def Text.cat : List Text → Text
  | [] => .nil
  | t :: ts => .app t (Text.cat ts)

/-- The line-join: `String.intercalate sep` over the elements, built
    structurally (O(1) per element; the separator is ONE `.str` node
    per gap, materialized only at render). -/
def Text.sepBy (sep : String) : List Text → Text
  | [] => .nil
  | [t] => t
  | t :: ts => .app t (.app (.str sep) (Text.sepBy sep ts))

/-! ## the laws — the byte-tie's theorem face -/

/-- Core's join distributes over list append (the bridge lemma the
    render laws reduce through). -/
theorem join_append (xs ys : List String) :
    String.join (xs ++ ys) = String.join xs ++ String.join ys := by
  induction xs with
  | nil => simp [String.empty_append]
  | cons x xs ih => simp [ih, String.append_assoc]

/-- A leaf renders to exactly its bytes. -/
theorem render_str (s : String) : Text.render (.str s) = s := by
  simp only [Text.render, Text.chunks, String.join]
  rfl

/-- THE composition law: render is a monoid morphism over `.app` —
    structural composition never touches bytes. -/
theorem render_app (a b : Text) :
    Text.render (.app a b) = Text.render a ++ Text.render b := by
  simp only [Text.render, Text.chunks, join_append]

/-- The template spine IS core `String.join`: a rope built by `cat`
    over string leaves renders byte-for-byte what the flat
    `++`-chain spelled. -/
theorem render_cat_strs (ss : List String) :
    Text.render (Text.cat (ss.map .str)) = String.join ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      rw [List.map_cons, Text.cat, render_app, ih]
      simp [render_str]

/-- The line-join IS core `String.intercalate`, byte-for-byte: a rope
    assembled with `sepBy` renders exactly the string-level
    `intercalate` (the rewire's equivalence, theorem-side). -/
theorem render_sepBy_strs (sep : String) (ss : List String) :
    Text.render (Text.sepBy sep (ss.map .str)) = String.intercalate sep ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      rw [List.map_cons]
      cases ss with
      | nil => simp [Text.sepBy, render_str]
      | cons u us =>
          rw [show Text.sepBy sep (Text.str s :: List.map Text.str (u :: us))
                = Text.app (Text.str s)
                  (Text.app (Text.str sep)
                    (Text.sepBy sep (List.map Text.str (u :: us))))
              from rfl,
            render_app, render_str, render_app, render_str, ih]
          simp [String.append_assoc]

end Kit
