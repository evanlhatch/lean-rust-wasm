/-
# SchemaCore.Emit.Spine — the target-parameterized emitter spine

Owner: the codegen-target lane (the mandate tree, `schemacore/`).

THE SEAM (notes/design-forward-surface.md §1): the emitter spine was
ALREADY shared — `Kit.Emit`'s plugin model, `Fold.lean`'s one walk,
`Kit.Mangle`, the rope, the byte-tie. What kept target #2 at ~1,300 LOC
was the last factoring: the section ORDER (prelude → universe faces →
records → lanes) and the record assembly were hardwired in
`Emit/Rust.lean`'s `libRope`/`renderRecord` with Rust leaves
interpolated. THIS module is that factoring: ONE `CodeTarget` structure
carries the target's faces as data; the spine's walks are its single
consumer. A target lands as ROWS, never as a new walk (07 R1's recipe;
15-patterns #10's emitter spine, one level parameterized).

The design note's honest gaps, named here rather than faked:
- THE TYPED-AST SLOT (07 R1 step 2): the sketch's `AST`/`tyOf` fields
  land with the first target that needs construction-boundary facts —
  the WIT lane is the precedent (`Wit.Ty` + `Wit.Render`). Until then
  the type-text face rides the shared `Descr` lift (`descrOfTy` —
  moved here from `Emit/Rust.lean`, the census's GENERIC band);
  a target's `tyText` is its fold over that lift. Rust renders the
  same face it always did; the byte-tie is the migration proof.
- THE LITERAL SLOT (`litOf`): the value→literal face stays with the
  migration lane's owner (`Emit/Rust.lean`'s `valueRust`); a target
  with no migration face (TS v0) has no literal slot to fill. The
  field arrives when a second migration face needs it — never before
  (the leftover rule).
- THE KEY ALGS: the key-position codec faces (`KeyTyAlg`) are the
  target's module rows its `encAlg`/`decAlg` rows cite — the target's
  FORM (Rust: bind statements; TS: validating expressions) is a target
  judgment, not a spine convention.

The five questions (notes/v3/01-core.md):
- root: Crossing — the universe (`DataRegistry Item`) read into a
  target's artifact through the target's declared faces.
- carrier grade: the naming precondition is `DataRegistry`'s
  nodup-in-the-type; the face-declaration check (`spineFacesOk`) is
  the target-side discipline — a face named but not declared REFUSES
  (the artifact's absence, the byte-tie's catch, the WIT lane's
  refusal-face precedent).
- spine reading: THE spine — Registry → Interpretation → artifact,
  parameterized over one structure; the driver owns IO (Kit.Emit's).
- ladder rung: total structural folds; the laws live at the targets
  (the byte-tie per artifact is the artifact-side proof).
- gate row: gen-check byte-ties every spine artifact; ownership +
  artifact-headers read the emitters; coverage grows the target's
  column.
-/

import SchemaCore.Describe
import SchemaCore.Item
import SchemaCore.Fold
import Kit.Emit
import Kit.Mangle
import Kit.Text

open Kit
open Kit.Emit

namespace SchemaCore.Emit.Spine

/-! ## The description lift — moved here from Emit/Rust.lean (the
     census's GENERIC band: the lift is target-independent) -/

/-- The C-family string literal (escaped) — the SHARED spelling both
    lane printers had carried as alpha-equivalent twins (the enforcement
    wave's adjudication: the duplicate was real, and the dedupe is the
    honest fix — TS and Rust string literals agree byte-for-byte today,
    both being the C-family escapes; a lane that diverges LATER owns its
    own spelling again, deliberately, not by copy-drift). -/
def strLit (s : String) : String :=
  Kit.escapeWith (fun c =>
    if c == '\\' then "\\\\"
    else if c == '"' then "\\\""
    else if c == '\n' then "\\n"
    else none) s

/-- The field-type lift INTO the description universe: the wrapper
    shapes (option/list) become the `Descr` wrappers; the closed
    universe's other ctors stay `.prim` leaves (ONE leaf universe —
    the description layer adds the record dimension, it does not
    re-interpret the leaves). -/
def descrOfTy (t : Ty) : Descr :=
  match t with
  | .option t' => .option (descrOfTy t')
  | .list t' => .list (descrOfTy t')
  | _ => .prim t

/-- The item's description (provenance-faithful name, registration
    field order — the same rows `itemOfDescr` flattens back). -/
def itemDescr (item : Item) : Descr :=
  .product item.name (item.fields.map fun f => (f.name, descrOfTy f.ty))

/-! ## The target's faces, as data -/

/-- One API-discipline face: a name + the face's render over one item.
    The record template places faces BY NAME (the target's `faceNames`
    order is its template's order); a face named but absent from the
    target's `faces` table refuses (`spineFacesOk`). The faces are the
    design note's "rows + instances" rule: the builder / lookups /
    serde faces are entries, never hardcoded sections. -/
structure TargetFace where
  name : String
  render : Item → Text

/-- The per-record facts the spine computes ONCE per item — the shared
    walk's product (the type lift, the per-field codec statements over
    the target's two algs, the target's spellings). The record
    template consumes the facts; it never re-walks the item. -/
structure RecordFacts where
  /-- The record's type spelling (the target's `identTy`). -/
  name : String
  /-- (field name, target type text) — registration order. -/
  fields : List (String × String)
  /-- Per-field encode statements (the target's `encRef` convention
    supplies the value reference). -/
  enc : List String
  /-- Per-field decode statements (the target's `decExpr` convention
    supplies the source expression). -/
  dec : List String

/-! ## THE CODETARGET — one codegen target -/

/-- ONE codegen target. The spine (walk registry → assemble sections →
    emitter row → byte-tie) is THIS structure's single consumer; a
    target lands as rows, never as a new walk. The Rust target
    (`Emit/Rust.lean`) is the migration proof — `gates gen-check`
    holds its artifacts byte-identical; TypeScript (`Emit/Ts.lean`) is
    the marginal-cost row (the design note's ≤150 metric). -/
structure CodeTarget where
  /-- The target's name (the emitter's `schema-<name>`). -/
  name : String
  /-- The generated header's comment style. -/
  style : CommentStyle
  /-- The artifact path (the type text's file — the lib/module face). -/
  outputPath : String
  /-- Files beyond the spine's rope (Rust: the differential's Rust
      consumer; TS: none). The emitter emits them AFTER the rope file,
      in list order — the target owns their content wholesale (the
      generated-test consumer text is target authoring, the design
      note's rule). -/
  extraOutputs : List GeneratedFile := []
  /-- The one-writer discipline, in the type (the emitter's proof
      field draws from here; the target literal decides it). -/
  outputs_nodup :
    (outputPath :: extraOutputs.map (fun f => f.path)).Nodup := by decide
  /-- The type-text face: the target's fold over the shared `Descr`
    lift (the typed-AST slot's honest v0 — see the module header). -/
  tyText : Descr → String
  /-- The record name's spelling (the registry name in — the ONE
      mangler's conventions out; rides the post-mangle uniqueness
      bridge). -/
  identTy : String → String
  /-- The encode position's value-reference convention (field name in:
      Rust `&self.f`, TS `v.f`). -/
  encRef : String → String
  /-- The decode position's source-expression convention (field name
      in: Rust the binder itself, TS the parsed object's key). -/
  decExpr : String → String
  /-- THE ENCODE STATEMENTS = the fold: the wire's statement templates
      as a `TyAlg (String → String)` — the wire is SchemaCore.Codec's,
      the templates are its target face. -/
  encAlg : TyAlg (String → String)
  /-- THE DECODE STATEMENTS = the fold (the encode side's mirror). -/
  decAlg : TyAlg (String → String)
  /-- The runtime prelude: the helpers the codec templates call. -/
  prelude : Text
  /-- The universe-faces slot: the closed universe's OWN types (Rust:
      the strum enums + the newtypes; TS: the union types + the
      branded key materials). Empty when the target has none. -/
  universeTypes : Text
  /-- The target's face table (the opted-in API disciplines, as
      data). -/
  faces : List TargetFace
  /-- The faces the record template places, in template order — every
      name MUST be in `faces` (`spineFacesOk` refuses otherwise). -/
  faceNames : List String
  /-- The record blocks' extra sections (Rust: the migration lane's
      Rust face). Emitted after the records, joined by the same
      section separator. -/
  lanes : List Text := []
  /-- The record template: the target's block over the spine's facts,
      placing its declared faces by name (the lookup the spine passes
      is over THIS item). -/
  renderRecord : RecordFacts → (String → Option Text) → Text

/-! ## The spine's walks (the structure's single consumer) -/

/-- The face-declaration check: every name the record template places
    is in the target's face table. A `false` here is a target-row bug
    — the emitter REFUSES (no artifact; the byte-tie's catch), and the
    SchemaTests pin makes the refusal a verdict (the mandatory
    negative control). -/
def spineFacesOk (t : CodeTarget) : Bool :=
  t.faceNames.all fun nm => t.faces.any fun f => f.name == nm

/-- The face lookup the spine passes the record template: the target's
    face table rendered over THIS item (a miss renders empty — the
    declared-face gate above is the discipline, not this default). -/
def spineFaceLookup (t : CodeTarget) (item : Item) (nm : String) : Option Text :=
  (t.faces.find? fun f => f.name == nm).map fun f => f.render item

/-- The per-record facts: the ONE shared walk (type lift + the two
    algs + the target's conventions). -/
def spineRecordFacts (t : CodeTarget) (item : Item) : RecordFacts where
  name := t.identTy item.name
  fields := item.fields.map fun f => (f.name, t.tyText (descrOfTy f.ty))
  enc := item.fields.map fun f => foldTy t.encAlg f.ty (t.encRef f.name)
  dec := item.fields.map fun f => foldTy t.decAlg f.ty (t.decExpr f.name)

/-- One record block: the target's template over the spine's facts +
    face lookup. -/
def spineRenderRecord (t : CodeTarget) (item : Item) : Text :=
  t.renderRecord (spineRecordFacts t item) (spineFaceLookup t item)

/-- The registry → the artifact body's ROPE (pure, total): the section
    assembly the Rust lane hardcoded — prelude → universe faces →
    records (ONE `sepBy` join, O(1) per block) → lanes — parameterized
    over the target. The rope is EXPOSED (not folded into a String):
    the golden modules' chunk literals ride `Text.chunks` of THIS (the
    monolithic-string whnf is quadratic in the body — Rust.lean's
    measured note). -/
def spineLibRope (t : CodeTarget) (reg : DataRegistry Item) : Text :=
  Text.cat
    [ Text.sepBy "\n\n"
        (t.prelude :: t.universeTypes ::
          reg.items.map (spineRenderRecord t) ++ t.lanes)
    , .str "\n" ]

/-- The spine's emitter row: the target's ONE emitter (the plugin
    model's discipline unchanged — outputs nodup from the target's
    proof field, the face gate the refusal face, the driver owns IO).
    The duel's vector-set convention is the TARGET's row when it has
    vectors (Rust's `duelEmitter` stays its own row — the wire bytes
    are the codec's, not the target's). -/
def spineEmitter (t : CodeTarget) : Emitter (DataRegistry Item) where
  name := s!"schema-{t.name}"
  style := t.style
  specSource := "SchemaCore.Slice"
  outputs := t.outputPath :: t.extraOutputs.map (fun f => f.path)
  outputs_nodup := t.outputs_nodup
  run reg :=
    if spineFacesOk t then
      { path := t.outputPath
        contents := Text.render (spineLibRope t reg) } :: t.extraOutputs
    else []
  law := none

end SchemaCore.Emit.Spine
