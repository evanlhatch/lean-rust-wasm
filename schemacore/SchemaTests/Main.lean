/-
# SchemaTests — the slice's test exe (TestingKit the whole way)

Per the slice: positive pins + the MANDATORY negative controls
(15-patterns #5 — each Spec's sabotages must FAIL or the verdict is
`.vacuous`, louder than failing). Suites:

1. `Ty` — the closed universe's rendering (every ctor's live witness).
2. The emitter — the artifact body is a GOLDEN PIN (a literal), plus
   the byte-tie's teeth at the value level (TestingKit.Golden).
3. The registry — duplicate item names are DECIDED and refused.
4. The obligation — fields-nodup discharges at `decidableNow`; the
   mis-wire (`Discharged` with a tier-mismatched evidence) is
   UNCONSTRUCTIBLE at the elaborator — the data-level `tierMismatch`
   check is the control that mirrors it.
5. The emitter's law — the closed-world naming precondition, certified.

The RUNTIME half of the slice (the olean replay + the driver's write
path) is exercised by `lake exe schema` + `gates gen-check` — a pure
test exe cannot replay extensions; the gate is that suite's runner.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import TestingKit.Harness
import TestingKit.Golden
import SchemaCore
import SchemaCore.DeriveMeta
import SchemaCore.Slice
import SchemaCore.CheckSlice
import SchemaCore.Keys
import SchemaCore.KeysSlice
import SchemaTests.Axioms
import SchemaTests.Events
import SchemaTests.Migrate
import SchemaTests.Commit
import SchemaTests.EntityMachine
import SchemaTests.Inc
import SchemaTests.Confluence

open Kit SchemaCore TestingKit

/-! ## Fixtures -/

-- The Example fixture's field list is `SchemaCore.CheckSlice`'s
-- `exampleCheckFields` (the reference — the same six fields, ONE copy;
-- the GADT INDEX: the abbrev rule, 06 §3 — a GADT-indexed match needs
-- the index to unfold, and the abbrev rides the reifier-shaped fields
-- literal as the index of every fixture row/bridge).

def exItem : Item := { name := "SchemaCore.Slice.Example", fields := exampleCheckFields }

/-- The grown fixture (mirrors SchemaCore.Slice.ExampleEx's
    registration; the build-time teeth below pin the hand fixture
    against the LIVE reflection). The `set` ctor has no authoring
    spelling (Slice.lean's note) — its lowering is pinned in
    `tyRenderSpec`/`losslessSpec`, its registration named the gap. -/
def exItemEx : Item :=
  { name := "SchemaCore.Slice.ExampleEx"
    fields := [ { name := "status", ty := .result .u64 .string }
              , { name := "counts", ty := .map .string .u64 }
              , { name := "small", ty := .bounded 42 } ] }

def exReg : DataRegistry Item := { items := [exItem, exItemEx], nameOf := fun it => it.name }

/-- An item with a DUPLICATE field name (the sabotaged sibling). -/
def dupFieldItem : Item :=
  { name := "SchemaCore.Slice.Bad"
    fields := [ { name := "a", ty := .bool }
              , { name := "a", ty := .u64 } ] }

/-- The GOLDEN PIN: the artifact body, byte-for-byte (the committed
    `gen/schema-slice.wit`'s body must equal this modulo nothing). The
    example-ex block is the honest growth: the sum shape renders as
    `result<…>`, the map as the association-list form (the declared
    retraction-with-note), the bounded as `u64` (the declared cap
    loss). -/
def expectedBody : String :=
  "package mandate:slice;\n\ninterface items {\n" ++
  "  record example {\n" ++
  "    ready: bool,\n" ++
  "    count: u64,\n" ++
  "    delta: i64,\n" ++
  "    label: string,\n" ++
  "    note: option<string>,\n" ++
  "    tags: list<string>,\n" ++
  "  }\n" ++
  "  record example-ex {\n" ++
  "    status: result<u64, string>,\n" ++
  "    counts: list<tuple<string, u64>>,\n" ++
  "    small: u64,\n" ++
  "  }\n" ++
  "}\n"

/-- Registry over one arbitrary item (the sabotage harness's helper;
    the singleton nodup is a one-step `simp` — never a free-variable
    `decide`). -/
def reg1 (item : Item) : DataRegistry Item :=
  { items := [item]
    nameOf := fun it => it.name
    nodup := by simp }

/-! ## The record↔row bridge — DERIVED (`deriving WireCodec, row_bridge`,
    the DeriveMeta handlers; the hand-built demonstration this file once
    carried — the toRow/ofRow pair, the VList box helpers, and both
    round-trip proofs, ~160 lines — is DELETED: the handlers generate
    it per record, the laws cited from the GENERIC theorems) -/

/-- The native record mirror of the Example fixture (the bridge's
    native side). The deriving clause mounts BOTH capabilities: the
    wire codec (`descr` + `tupleIso` + `codec` — the generic
    `deriveCodec_correct`/`deriveDec_eq` thin wrappers) and the row
    bridge (`fields` + `fieldNames` + `fields_nodup` + `nameIso` +
    `toRow`/`ofRow` + `rowIso` — the generic `ofRowF_toRowF`/
    `toRowF_ofRowF` thin wrappers). -/
structure ExampleRec where
  ready : Bool
  count : UInt64
  delta : Int64
  label : String
  note : Option String
  tags : List String
deriving Repr, BEq, Inhabited, WireCodec, row_bridge

/-- The generated field rows ARE the registry's snapshot — the GADT
    index is the SAME list literal (the abbrev rule, 06 §3): the
    derived bridge's rows typecheck against every fixture row. -/
example : ExampleRec.fields = exampleCheckFields := rfl

/-- The generated description: the fixture's fields, the declaration's
    own name (the kernel reduces it — the reflection's pin). -/
example : ExampleRec.descr = .product "ExampleRec"
    [ ("ready", .prim .bool), ("count", .prim .u64)
    , ("delta", .prim .i64), ("label", .prim .string)
    , ("note", .option (.prim .string))
    , ("tags", .list (.prim .string)) ] := rfl

/-- The generated tupleIso composes into the rowIso (the ONE
    `Kit.Iso`, both laws from the generic theorems via
    `Kit.Iso.trans` — the law fields were checked at the defs; this
    pin is the citation face). -/
example : ExampleRec.rowIso.to = ExampleRec.toRow := rfl
example : ExampleRec.rowIso.inv = ExampleRec.ofRow := rfl

/-- The determinacy fact, DECIDED at the mount (the obligation's
discharge rides it — the name↔index iso's domain). -/
example : ExampleRec.fieldNames.Nodup := ExampleRec.fields_nodup

/- BUILD-TIME TEETH (the deriving handlers are elaboration-time; the
   refusals are the curated Diag, rendered verbatim — got + the valid
   space + the did-you-mean). Drift FAILS THE BUILD. The refusal
   fixtures are declared ONLY under their guards (a failing deriving
   clause does not declare the structure, so each guard's command is
   the fixture's only declaration). -/

/-- error: deriving WireCodec refused `DeriveBadNat`: [SD0002] error: `DeriveBadNat.n`: the field type is outside the supported fragment — `describe` reflects the boundary universe's leaves, wrapped in option/list/sum (got: Nat) — valid: Bool, UInt64, Int64, String, Option _, List _, Sum _ _ -/
#guard_msgs in
structure DeriveBadNat where
  n : Nat
deriving WireCodec

/-- error: deriving row_bridge refused `DeriveBadNatRow`: [SD0002] error: `DeriveBadNatRow.n`: the field type is outside the supported fragment — `describe` reflects the boundary universe's leaves, wrapped in option/list/sum (got: Nat) — valid: Bool, UInt64, Int64, String, Option _, List _, Sum _ _ -/
#guard_msgs in
structure DeriveBadNatRow where
  n : Nat
deriving row_bridge


/-! ## The suites -/

/-- Every `Ty` ctor lowers (the closed universe's live witness — the
    honest WIT lowering: map/set lower to the association-list forms,
    bounded to `u64`; the two named collisions are pinned POSITIVELY —
    they ARE the declared loss). -/
def tyRenderSpec : Spec :=
  Spec.ofList "ty lowers to the honest WIT shapes"
    (fun _ => assert ((renderTy .bool == "bool")
        && (renderTy .u64 == "u64")
        && (renderTy .i64 == "i64")
        && (renderTy .string == "string")
        && (renderTy (.option .u64) == "option<u64>")
        && (renderTy (.list .string) == "list<string>")
        && (renderTy (.option (.list .u64)) == "option<list<u64>>")
        && (renderTy (.result .u64 .string) == "result<u64, string>")
        && (renderTy (.map .string .u64) == "list<tuple<string, u64>>")
        && (renderTy (.set .i64) == "list<i64>")
        && (renderTy (.map .string (.list .u64))
              == "list<tuple<string, list<u64>>>")
        && (renderTy (.bounded 42) == "u64")
        -- the NAMED collisions (the lossy rows' loss, pinned as data):
        && (renderTy (.set .string) == renderTy (.list .string))
        && (renderTy (.bounded 42) == renderTy .u64))
      "the closed universe's lowering drifted")
    [ ("sabotaged option render ties",
        fun _ => assert (renderTy (.option .u64) == "u64")
          "control: option must nest, not vanish")
    , ("sabotaged list render ties",
        fun _ => assert (renderTy (.list .string) == "list[string]")
          "control: list must bracket, not vanish")
    , ("the map lowers as the vanilla flavor",
        fun _ => assert (renderTy (.map .string .u64) == "map<string, u64>")
          "control: WIT has no map — the association-list form is the \
            declared lowering, not map<…>")
    , ("the map's key vanishes",
        fun _ =>
          assert (renderTy (.map .string .u64) == "list<tuple<u64, u64>>")
          "control: the KEY must render in the tuple (renderKeyTy routes it)")
    , ("the set lowers as the vanilla flavor",
        fun _ => assert (renderTy (.set .i64) == "set<i64>")
          "control: WIT has no set — the plain-list form is the declared \
            lowering, not set<…>")
    , ("the set/list collision is silently denied",
        fun _ =>
          assert (renderTy (.set .string) != renderTy (.list .string))
          "control: the collision IS the declared loss — it must stay \
            visible, not be denied")
    , ("sabotaged result render ties",
        fun _ => assert (renderTy (.result .u64 .string) == "u64")
          "control: result must keep BOTH summands")
    , ("the bounded lowers with its cap",
        fun _ => assert (renderTy (.bounded 42) == "bounded<42>")
          "control: WIT has no bounded ints — the cap is the declared loss")
    , ("the bounded/u64 collision is silently denied",
        fun _ =>
          assert (renderTy (.bounded 42) != renderTy .u64)
          "control: every cap lowers to u64 — the collision must stay \
            visible, not be denied") ]
    4 42

/-- The lossless FRAGMENT (the correspondence row, 07 R1): the
    non-lossy ctors' lowerings are pairwise distinct (`decide`-pinned),
    the lossy rows are flagged OUT — never silently admitted. -/
def losslessSpec : Spec :=
  Spec.ofList "the lossless fragment is flagged + distinct"
    (fun _ => assert (
      -- the fragment's verdicts per row
      (Ty.witLossless .bool)
        && (Ty.witLossless .u64)
        && (Ty.witLossless .i64)
        && (Ty.witLossless .string)
        && (Ty.witLossless (.option .u64))
        && (Ty.witLossless (.list .string))
        && (Ty.witLossless (.result .u64 .string))
        && (Ty.witLossless (.option (.list .u64)))
      -- the flagged exclusions
        && !(Ty.witLossless (.map .string .u64))
        && !(Ty.witLossless (.set .u64))
        && !(Ty.witLossless (.bounded 42))
        && !(Ty.witLossless (.option (.map .string .u64)))
      -- the distinctness pin over the lossless ctor sample
        && (witSurfaceDistinct [.bool, .u64, .i64, .string, .option .u64,
              .list .string, .result .u64 .string]))
      "the lossless fragment drifted")
    [ ("the checker admits the set/list collision",
        fun _ =>
          assert (witSurfaceDistinct [.list .string, .set .string])
          "control: the collision IS a surface tie — the checker must fire")
    , ("the checker admits the bounded/u64 collision",
        fun _ =>
          assert (witSurfaceDistinct [.u64, .bounded 42])
          "control: every cap lowers to u64 — the checker must fire")
    , ("the fragment admits a map",
        fun _ => assert (Ty.witLossless (.map .string .u64))
          "control: the map row is OUT — uniqueness is not WIT-carried")
    , ("the fragment admits a bounded",
        fun _ => assert (Ty.witLossless (.bounded 3))
          "control: the bounded row is OUT — the cap is not WIT-carried") ]
    4 42

/-! ## The recursion schemes (SchemaCore.Fold) — the migration's pins -/

/-- The PRE-FOLD hand walk, kept here as the migration's oracle: the
    OLD `renderTy` body (Ty.lean's match, verbatim). The core's own
    `renderTy` is the fold now; this copy exists so the suite can watch
    the two walks agree — the uniqueness law's runtime face. -/
def renderTyDirect : Ty → String
  | .bool => "bool"
  | .u64 => "u64"
  | .i64 => "i64"
  | .string => "string"
  | .option t => s!"option<{renderTyDirect t}>"
  | .list t => s!"list<{renderTyDirect t}>"
  | .result ok err => s!"result<{renderTyDirect ok}, {renderTyDirect err}>"
  | .map k v => s!"list<tuple<{renderKeyTy k}, {renderTyDirect v}>>"
  | .set k => s!"list<{renderKeyTy k}>"
  | .bounded _ => "u64"

/-- THE MIGRATION LAW: the hand walk IS the fold — the initiality
    theorem (`foldTy_unique`) applied to the oracle; every row commutes
    by `rfl` (the interpolation IS the concatenation). This theorem is
    the migration's evidence at the TYPE level; the byte-tie is its
    artifact-level face. -/
theorem renderTyDirect_eq (t : Ty) : renderTyDirect t = renderTy t :=
  foldTy_unique (f := renderTyDirect) rfl rfl rfl rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) t

/-- A function that does NOT commute on one constructor is NOT the
    fold: the saboteur drops the option child — the uniqueness law's
    hypotheses fail on exactly one row, and the agreement dies. (The
    negative control's data.) -/
def fBad : Ty → String
  | .bool => "bool"
  | .u64 => "u64"
  | .i64 => "i64"
  | .string => "string"
  | .option _ => "opt!"
  | .list t => s!"list<{renderTyDirect t}>"
  | .result ok err => s!"result<{renderTyDirect ok}, {renderTyDirect err}>"
  | .map k v => s!"list<tuple<{renderKeyTy k}, {renderTyDirect v}>>"
  | .set k => s!"list<{renderKeyTy k}>"
  | .bounded _ => "u64"

/-- The sabotage ALGEBRA: the fold with one row replaced (the option
    row loses its child). A wrong row is a wrong rendering — the fold
    does not paper over it. -/
def witAlgBad : TyAlg String := { witAlg with option := fun _ => "u64" }

/-- The FUSION LAW's exercise: `String.length` DISTRIBUTES over the WIT
    rows (a concatenation's length is the sum of the parts), so the
    rendered length is itself a fold over the length algebra — the
    fused walk computes the length WITHOUT building the text.
    (A cosmetic wrapper like `fun s => "W" ++ s ++ "W"` does NOT
    distribute — it double-wraps nested children — and fusion
    correctly refuses it.) -/
def lengthWitAlg : TyAlg Nat where
  bool := "bool".length
  u64 := "u64".length
  i64 := "i64".length
  string := "string".length
  option a := "option<".length + a + ">".length
  list a := "list<".length + a + ">".length
  result ok err := "result<".length + ok + ", ".length + err + ">".length
  map k a := "list<tuple<".length + (renderKeyTy k).length
    + ", ".length + a + ">>".length
  set k := "list<".length + (renderKeyTy k).length + ">".length
  bounded _ := "u64".length

theorem fold_fusion_exercise (t : Ty) :
    (renderTy t).length = foldTy lengthWitAlg t := by
  show (foldTy witAlg t).length = foldTy lengthWitAlg t
  exact foldTy_fusion (h := String.length) (alg := witAlg)
    (alg' := lengthWitAlg) rfl rfl rfl rfl
    (fun a => by simp [witAlg, lengthWitAlg, String.length_append])
    (fun a => by simp [witAlg, lengthWitAlg, String.length_append])
    (fun ok err => by simp [witAlg, lengthWitAlg, String.length_append])
    (fun k a => by simp [witAlg, lengthWitAlg, String.length_append])
    (fun k => by simp [witAlg, lengthWitAlg, String.length_append])
    (fun n => by simp [witAlg, lengthWitAlg])
    t

/-- The fold suite: the schemes' pins + the migration's evidence. -/
def foldSpec : Spec :=
  Spec.ofList "the recursion schemes: one fold, algebras, the laws"
    (fun _ => assert (
      -- the migration: the fold at the concrete types (renderTy IS
      -- foldTy witAlg definitionally — renderTyDirect_eq pins the walk
      -- agreement; here the rows' concrete outputs)
      (foldTy witAlg (.option (.list (.map .string .u64)))
              == renderTy (.option (.list (.map .string .u64))))
      -- the oracle agrees on the nested sample (renderTyDirect_eq's
      -- runtime face over a non-trivial type)
        && (renderTyDirect (.option (.list (.map .string .u64)))
              == renderTy (.option (.list (.map .string .u64))))
        && (renderTyDirect (.result (.option .i64) (.bounded 9))
              == renderTy (.result (.option .i64) (.bounded 9)))
      -- the lossless flag rides the fold (the migrated verdicts)
        && ((Ty.map .string .u64).witLossless == false)
        && ((Ty.result .u64 .string).witLossless == true)
      -- the RUST rendering rides the fold (the migrated rows)
        && (tyRustPrim .string == "String")
        && (tyRustPrim (.result .u64 .string) == "Result<u64, String>")
        && (tyRustPrim (.map .string .u64) == "Vec<(String, u64)>")
        && (tyRustPrim (.set .i64) == "Vec<i64>")
        && (tyRustPrim (.bounded 42) == "u64")
      -- the FUSION law's runtime face: the length fold agrees with
      -- measuring the rendered text
        && ((renderTy (.option .u64)).length
              == foldTy lengthWitAlg (.option .u64))
        && ((renderTy (.map .string (.list .u64))).length
              == foldTy lengthWitAlg (.map .string (.list .u64))))
      "the recursion schemes drifted")
    [ ("the saboteur agrees with the fold",
        fun _ =>
          assert (fBad (.option .u64) == renderTy (.option .u64))
          "control fired: a function that drops the option child is NOT \
            the fold — uniqueness law's hypotheses fail and the \
            agreement dies")
    , ("the sabotaged algebra row still renders",
        fun _ =>
          assert (foldTy witAlgBad (.option .u64) == renderTy (.option .u64))
          "control fired: a wrong algebra row renders wrong — the fold \
            does not paper over it")
    , ("the key position reads the Ty table",
        fun _ =>
          assert (renderKeyTy .string == "String")
          "control fired: the KEY fold reads keyWitAlg's rows — the \
            scalar sub-universe's table, never the Ty algebra's") ]
    4 42

/-- The emitter's artifact body is the golden pin; the byte-tie's teeth
    at the value level (a tampered body fails Golden.cmp). -/
def artifactSpec : Spec :=
  Spec.ofList "the emitter renders the slice artifact"
    (fun _ => assert ((renderWit exReg == expectedBody)
        && (exItem.wireName == "example")
        && (match Golden.cmp (renderWit exReg) expectedBody with
            | .ok () => true
            | .error _ => false))
      "the artifact body drifted from the golden pin")
    [ ("dropped field undetected",
        fun _ =>
          let dropped : Item := { exItem with fields := exampleCheckFields.drop 1 }
          assert (renderWit (reg1 dropped) == expectedBody)
          "control: a dropped field must change the body")
    , ("sabotaged ty undetected",
        fun _ =>
          let sabField : SchemaCore.Field := { exampleCheckFields.head! with ty := .i64 }
          let sab : Item := { exItem with fields := sabField :: exampleCheckFields.drop 1 }
          assert (renderWit (reg1 sab) == expectedBody)
          "control: a re-typed field must change the body") ]
    4 42

/-- Duplicate item names: the registry DECIDES the nodup fact and
    refuses loudly (the runtime mirror of the type-level discipline). -/
def registrySpec : Spec :=
  Spec.ofList "the registry decides duplicate item names"
    (fun _ =>
      match registryOfItems [exItem], registryOfItems [exItem, exItem] with
      | .ok _, .error _ => .ok ()
      | _, _ => .error "registry acceptance mismatch")
    [ ("duplicates accepted",
        fun _ =>
          match registryOfItems [exItem, exItem] with
          | .ok _ => .ok ()
          | .error e => .error s!"control fired: duplicates were refused ({e})")
    , ("nodup decide lies",
        fun _ => assert (([exItem.name, exItem.name]).Nodup)
          "control: the decide must see the duplicate") ]
    4 42

/-- The slice's obligation: fields-nodup discharges at `decidableNow`
    via the kit's backend; the mis-wire is data-detectable (the
    type-level refusal is the elaborator itself). -/
def obligationSpec : Spec :=
  Spec.ofList "fields-nodup discharges at decidableNow"
    (fun _ =>
      let d : Discharged (List String) ((exItem.fields.map (·.name))).Nodup :=
        { obligation := fieldNodupObligation exItem, evidence := .decided true }
      assert ((dischargeFieldNodup exItem == some (.decided true))
        && (d.obligation.tier == .decidableNow))
      "the slice's one checkable fact did not discharge")
    [ ("duplicate-field item discharges",
        fun _ =>
          assert (dischargeFieldNodup dupFieldItem == some (.decided true))
          "control: a dup-field item must be REFUSED (none), never fabricated")
    , ("mis-wire passes silently",
        fun _ =>
          assert (¬(Kit.tierMismatch (fieldNodupObligation exItem)
            (Kit.Evidence.oracleRow "oracle-1")))
          "control: an oracle-row evidence against decidableNow is a mis-wire") ]
    4 42

/-- The emitter's law: the closed-world naming precondition; the
    certified lane emits iff the certificate holds. -/
def lawSpec : Spec :=
  Spec.ofList "the emitter's law is the registry's nodup"
    (fun _ =>
      match witEmitter.law with
      | some L =>
          assert (((witEmitter.runCertified exReg exReg.nodup).map (·.contents))
            == ((witEmitter.run exReg).map (·.contents)))
          "the law or the certified lane drifted"
      | none => .error "the emitter lost its law")
    [ ("the law covers field names too",
        fun _ =>
          -- The law is the ITEM-name precondition; the FIELD-name fact
          -- rides the obligation row (a different invariant, a different
          -- mount). This control asserts the INVERTED mount — the law
          -- declaring the field-nodup fact false — and must FAIL (the
          -- suite catches the false belief).
          assert (decide ((exItem.fields.map (·.name)).Nodup) == false)
            "control fired: the field-nodup fact is TRUE — it rides the \
             obligation row, not the emitter's naming law")
    , ("law missing",
        fun _ =>
          match witEmitter.law with
          | none => .ok ()
          | some _ => .error "control fired: the law IS populated") ]
    4 42

/-- The Value universe: the evaluator's total denotation + the beq/
    render discipline (the coverage pins mirror Value.lean's `rfl`
    examples at the runtime level). -/
def valueSpec : Spec :=
  Spec.ofList "the Value evaluator + beq + render"
    (fun _ => assert (
      -- the evaluator reduces (structural, kernel-visible)
      (Value.eval .u64 (.u64 7) == 7)
        && (Value.eval (.option .string) (.some (.string "x")) == some "x")
        && (Value.eval (.result .u64 .i64) (.err (.i64 (-1)))
              == Sum.inr (-1 : Int64))
        && (Value.eval (.list .u64) (.list (.cons (.u64 1) .nil)) == [1])
        && (Value.eval (.map .string .u64)
              (.map (.cons (.string "k") (.u64 2) .nil)) == [("k", 2)])
        && (Value.eval (.set .string)
              (.set (.cons (.string "s") .nil)) == ["s"])
        && (Value.eval (.bounded 3) (.bounded ⟨2, by decide⟩)
              == (2 : Fin 3))
      -- the BEq discipline: structural equality (the refl LAW is the
      -- theorem `Value.beq_refl` — a Prop, pinned by the build itself;
      -- here the behavior, there the law)
        && Value.beq _ (.some (.string "x")) (.some (.string "x"))
        && !Value.beq (.option .string) (.some (.string "x")) .none
        && !Value.beq (.list .u64) (.list (.cons (.u64 1) .nil)) (.list .nil)
        && Value.beq (.map .string .u64)
              (.map (.cons (.string "k") (.u64 2) .nil))
              (.map (.cons (.string "k") (.u64 2) .nil))
      -- the rendering discipline
        && (toString (Value.string "hi") == "\"hi\"")
        && (toString (Value.some (.u64 2)) == "some 2"))
      "the value universe's denotation/BEq/render drifted")
    [ ("beq conflates none and some",
        fun _ =>
          assert (Value.beq (.option .string) .none (.some (.string "")))
            "control: none is distinct from some, even of the empty string")
    , ("beq conflates map entries",
        fun _ =>
          assert (Value.beq (.map .string .u64)
            (.map (.cons (.string "k") (.u64 2) .nil))
            (.map (.cons (.string "k") (.u64 3) .nil)))
          "control: map equality is pairwise, not shape-deep")
    , ("render drops the option wrapper",
        fun _ =>
          assert (toString (Value.some (.u64 2)) == "2")
          "control: some must render as some, not vanish") ]
    4 42

/-- The row layer: the bridge's round trips (via the kit's Iso laws),
    the name-keyed projection, and the name↔index iso. -/
def rowSpec : Spec :=
  Spec.ofList "the row bridge round-trips + the projection + the index iso"
    (fun _ =>
      let r : ExampleRec := ⟨true, 3, -2, "a", some "n", ["t1", "t2"]⟩
      let row := ExampleRec.toRow r
      let iso := ExampleRec.nameIso
      assert (
      -- the Iso laws, live: the record side on concrete data (the ROW
      -- side is the PROVED law — `RowVals` carries no BEq; the Iso's
      -- law fields are the GENERIC theorems' citations)
        (ExampleRec.ofRow row == r)
        && (ExampleRec.ofRow
              (ExampleRec.toRow ⟨false, 0, 1, "b", none, []⟩)
              == ⟨false, 0, 1, "b", none, []⟩)
      -- the name-keyed projection: first match, typed hit, loud miss
        && (match RowVals.project? exampleCheckFields row "label" with
            | some fv => match fv.ty with | .string => true | _ => false
            | none => false)
        && (RowVals.project? exampleCheckFields row "nope").isNone
      -- the name↔index iso: both round trips over the fixture's names
        && ((iso.to ⟨1, by decide⟩).1 == "count")
        && ((iso.inv ⟨"count", by decide⟩).1 == 1)
        && ((iso.to (iso.inv ⟨"count", by decide⟩)).1
              == "count"))
      "the row layer drifted")
    [ ("projection fabricates a miss",
        fun _ =>
          let r : ExampleRec := ⟨true, 3, -2, "a", some "n", ["t1", "t2"]⟩
          assert ((RowVals.project? exampleCheckFields (ExampleRec.toRow r) "nope").isSome)
            "control: a missing field name must project to none")
    , ("round trip forgets the note",
        fun _ =>
          let r : ExampleRec := ⟨true, 3, -2, "a", some "n", ["t1", "t2"]⟩
          assert (ExampleRec.ofRow (ExampleRec.toRow r)
            == { r with note := none })
          "control: the bridge must carry the option payload faithfully")
    , ("index iso maps to the wrong name",
        fun _ =>
          let iso := ExampleRec.nameIso
          assert ((iso.to ⟨1, by decide⟩).1 == "ready")
          "control: position 1's name is count, not ready") ]
    4 42

/-! ## The derived capability suite (SchemaCore.DeriveMeta — the mounts) -/

/-- The deriving handlers' end-to-end runtime face: the generated
    `fields`/`descr` literals, the wire grade's decode∘encode, the row
    bridge's both round trips, the name↔index iso, the decided
    determinacy fact. The LAWS themselves are the Iso/Codec law fields
    (checked at the defs); this suite pins the VALUES. -/
def deriveSpec : Spec :=
  Spec.ofList "the derived codec + row bridge round-trip"
    (fun _ =>
      let r : ExampleRec := ⟨true, 3, -2, "a", some "n", ["t1", "t2"]⟩
      assert ((
      -- the generated fields literal IS the registry's snapshot
        (ExampleRec.fields == exampleCheckFields)
      -- the generated descr: the fixture's fields, the decl's name
        && (ExampleRec.descr == .product "ExampleRec"
              [ ("ready", .prim .bool), ("count", .prim .u64)
              , ("delta", .prim .i64), ("label", .prim .string)
              , ("note", .option (.prim .string))
              , ("tags", .list (.prim .string)) ])
      -- the WIRE: the codec's decode∘encode (the law field routes
      -- through the GENERIC deriveCodec_correct — the runtime face)
        && (match ExampleRec.codec.decode (ExampleRec.codec.encode r) with
            | some w => w == r
            | none => false)
        && (match ExampleRec.codec.decode
              (ExampleRec.codec.encode ⟨false, 0, 1, "b", none, []⟩) with
            | some w => w == ⟨false, 0, 1, "b", none, []⟩
            | none => false)
      -- the ROW bridge: both round trips (the Iso laws live)
        && (ExampleRec.ofRow (ExampleRec.toRow r) == r)
        && (ExampleRec.ofRow (ExampleRec.toRow ⟨false, 0, 1, "b", none, []⟩)
              == ⟨false, 0, 1, "b", none, []⟩)
      -- the name↔index iso (the determinacy fact, decided)
        && ((ExampleRec.nameIso.to ⟨1, by decide⟩).1 == "count")
        && ((ExampleRec.nameIso.inv ⟨"count", by decide⟩).1 == 1)
      -- the fields-nodup obligation: DISCHARGED at the mount (the
      -- decided Prop — the type-level pin below)
        ))
      "the derived capability surface drifted")
    [ ("the codec forgets the tags payload",
        fun _ =>
          let r : ExampleRec := ⟨true, 3, -2, "a", some "n", ["t1", "t2"]⟩
          assert (match ExampleRec.codec.decode (ExampleRec.codec.encode r) with
                  | some w => w == { r with tags := [] }
                  | none => false)
          "control: the codec must carry the list payload faithfully")
    , ("the descr borrows the registry's name",
        fun _ =>
          assert (ExampleRec.descr == .product "Example"
            [ ("ready", .prim .bool), ("count", .prim .u64)
            , ("delta", .prim .i64), ("label", .prim .string)
            , ("note", .option (.prim .string))
            , ("tags", .list (.prim .string)) ])
          "control: the descr's product name is the DECLARATION's \
            (provenance-faithful — ExampleRec, not the registry's Example)")
    , ("the nameIso reads the wrong position",
        fun _ =>
          assert ((ExampleRec.nameIso.to ⟨1, by decide⟩).1 == "ready")
          "control: position 1's name is count, not ready")
    , ("the fields literal reorders",
        fun _ =>
          assert (ExampleRec.fields.reverse == exampleCheckFields)
          "control: the generated rows are in registration order") ]
    4 42

/-! ## The evidence entourage (Kit.Derive.Evidence + the mounts' emissions,
    16-surface §3) -/

/-- The sabotaged drawer (the sweep-teeth's producer): draws NOTHING —
    the sweep must report `failAt` (the drawer's loud gap), never a
    silent pass. -/
def sabDrawNone : TestingKit.Tape → Option (ExampleRec × TestingKit.Tape) :=
  fun _ => none

/-- The entourage suite: the derived capability arrives with its FULL
    evidence cone — the kind row (computed from the capability + the
    carrier shape), the obligation row (tier COMPUTED from the kind — a
    sweep reports `oracleSwept`, never `provedAtElab`), the
    tier-matched discharge, the LCG sweep, the mechanical controls, and
    the simp-set registration. THE CENSUS: the round trips are
    type-carried (`Kit.Iso`'s law fields) — the entourage generates
    NOTHING for them (`emissionsOf .rowBridge` is `[]`). The negatives:
    the mount's OWN mechanical controls (each must fail) + the
    tier-honesty control + the sweep-teeth control. -/
def entourageSpec : Spec :=
  Spec.ofList "the derived capability's evidence entourage (16-surface §3)"
    (fun _ => do
      -- the kind is COMPUTED from the capability + the carrier shape
      assert (ExampleRec.codecEvidenceKind == .lgcSweep) "entourage.kindComputed"
      -- the tier is COMPUTED from the kind: a sweep reports oracleSwept
      assert (ExampleRec.codecObligation.tier == .oracleSwept) "entourage.tierComputed"
      -- the discharge is tier-matched (the oracle-row evidence constructs)
      let _ := ExampleRec.codecDischarged
      -- the determinacy fact's kind: closed-finite → the kernel decides
      assert (ExampleRec.fieldsEvidenceKind == .kernelDecide) "entourage.fieldsKind"
      assert (ExampleRec.fieldsObligation.tier == .decidableNow) "entourage.fieldsTier"
      -- THE CENSUS: the type-carried facts generate NOTHING
      assert (Kit.Derive.Evidence.emissionsOf .rowBridge == []) "entourage.census.carried"
      assert (Kit.Derive.Evidence.emissionsOf .wireCodec
        == [Kit.Derive.Evidence.Emission.obligationRow,
            Kit.Derive.Evidence.Emission.sweepControls,
            Kit.Derive.Evidence.Emission.simpSet]) "entourage.emissions"
      -- the controls are the MECHANICAL shapes (the entourage's data —
      -- never hand-invented)
      assert ((ExampleRec.codecSabotages.map (·.1)).take 2
        == Kit.Derive.Evidence.mechanicalControls .unbounded)
        "entourage.mechanicalControls"
      -- the SWEEP: 16 drawn instances, round trip + discrimination
      assert (ExampleRec.codecSweep == .pass 16) "entourage.sweep"
      -- the simp-set registration: the citation face (the lemma IS the
      -- codec's own law field — zero new proof content)
      let _ := @ExampleRec.codec_roundtrip
      pure ())
    (ExampleRec.codecSabotages ++
      [ ("sabotage: the sweep mislabels itself provedAtElab",
          fun _ =>
            assert (ExampleRec.codecObligation.tier == .provedAtElab)
              "control fired: the tier-honesty theorem was violated")
      , ("sabotage: the sweep tolerates the silent drawer",
          fun _ =>
            assert (SchemaCore.runCodecSweep ExampleRec.codec
                (fun a => ExampleRec.codec.encode a) sabDrawNone 16 42
              == .pass 16)
              "control fired: the sweep passed over a drawer that drew nothing") ])
    4 42

/-! ## The description layer (SchemaCore.Describe — D19's meta-universe) -/

/-- A field OUTSIDE the fragment (the refusal fixture: `Nat` has no
    uncapped boundary spelling — the Nat lane's base type is
    `bounded <cap>`). -/
structure HasNatField where
  n : Nat

/-- Not a structure (the other refusal fixture). -/
def NotAStructure : Nat := 42

/-- A `Sum` field (the sum shape's positive reification fixture: the
    description has NO first-class sum ctor — the boundary's
    `result` carries it). -/
structure HasSumField where
  r : Sum UInt64 String

/-- The reflected slice item, NAME-FAITHFUL: the registered item's
    name IS the Lean declaration's name — `Example` (the fixture is
    root-level; the emitter reads only the wire name, so the golden
    artifact is unaffected). -/
def exItemLive : Item := { name := "Example", fields := exampleCheckFields }

/-- The slice's reflected description — the PINNED thin-wrapper shape:
    one description value, the derivations one line over it (D12). The
    build-time teeth below pin this literal against the LIVE
    reflector — the description IS the declaration's, not a hand copy
    that can drift. -/
def exampleDescr : Descr :=
  .product "Example"
    [ ("ready", .prim .bool)
    , ("count", .prim .u64)
    , ("delta", .prim .i64)
    , ("label", .prim .string)
    , ("note", .option (.prim .string))
    , ("tags", .list (.prim .string)) ]

/-- THE THIN WRAPPER (D12's shape): the generic derivation
    instantiated at the description — one line, no per-decl proof. -/
def exampleRender : String := deriveRender exampleDescr

/-- The coherence law, instantiated on the slice's leaf fragment —
    the generic theorem first; the specialization is a CITING, never a
    re-proof. -/
example : deriveRender (.option (.prim .string))
    = renderTy (.option .string) :=
  deriveRender_coherent _ _ rfl

/-- The denotation pin: the slice's description denotes the canonical
    tuple over the field order (the kernel sees it — `rfl`). -/
example : Descr.Ty exampleDescr =
    (Bool × (UInt64 × (Int64 × (String ×
      (Option String × (List String × Unit)))))) :=
  rfl

/-- BUILD-TIME TEETH (the reflector is elaboration-time; a pure exe
    cannot replay the environment — the same split as the registry's
    runtime half, whose runner is the gen-check gate): the LIVE
    reflection must equal the pinned description; the two reflection
    paths must AGREE on the fixture; every refusal must carry its
    named E-code + got + valid space. Drift FAILS THE BUILD. -/
meta def describeTeeth : Lean.Elab.Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  -- the LIVE reflection pins the description literal
  match SchemaCore.describe env `Example with
  | .error d => throwError "describe refused the slice: {d.toString}"
  | .ok d =>
      unless d == exampleDescr do
        throwError "the reflected description drifted from the pin: \
          {toString (repr d)}"
  -- the two reflection paths AGREE on the fixture (the convergence pin)
  match SchemaCore.reflectStruct env `Example,
        SchemaCore.reflectItemViaDescr env `Example with
  | .ok it1, .ok it2 =>
      unless it1 == it2 do
        throwError "the reflection paths diverged: \
          {toString (repr it1)} vs {toString (repr it2)}"
  | _, _ => throwError "a reflection path refused the slice fixture"
  -- curated refusal: unsupported leaf → SD0002, the named fragment
  match SchemaCore.describe env `HasNatField with
  | .ok _ => throwError "control fired: the Nat field was accepted"
  | .error d =>
      unless d.code == ⟨"SD0002"⟩ do
        throwError "wrong code: {d.toString}"
      unless d.got == some "Nat" do
        throwError "wrong got: {d.toString}"
      unless d.valid == describeFragment do
        throwError "wrong valid space: {d.toString}"
  -- curated refusal: not a structure → SD0001
  match SchemaCore.describe env `NotAStructure with
  | .ok _ => throwError "control fired: the non-structure was accepted"
  | .error d =>
      unless d.code == ⟨"SD0001"⟩ do
        throwError "wrong code: {d.toString}"
  -- the sum shape reflects (the positive interop pin)
  match SchemaCore.describe env `HasSumField with
  | .error d => throwError "the Sum field was refused: {d.toString}"
  | .ok d =>
      let expect : Descr :=
        .product "HasSumField" [("r", .prim (.result .u64 .string))]
      unless d == expect do
        throwError "the Sum reflection drifted: {toString (repr d)}"

#eval describeTeeth

/-- The description suite: the derivations on the slice, the registry
    bridge, and the refusal discipline's data-level negative controls
    (the elaboration-level teeth are `describeTeeth` above). -/
def describeSpec : Spec :=
  Spec.ofList "the description layer renders, projects, bridges"
    (fun _ => assert (
      -- the generic derivation: leaf positions delegate to the ONE
      -- boundary renderer; wrappers nest; products render the wire name
      (exampleRender == "record<example>")
        && (deriveRender (.prim (.result .u64 .string))
              == "result<u64, string>")
        && (deriveRender (.option (.list (.prim .string)))
              == "option<list<string>>")
      -- the projection into the boundary universe
        && (tyOfDescr (.option (.prim .u64)) == some (.option .u64))
        && (tyOfDescr (.list (.prim .string)) == some (.list .string))
      -- the registry bridge: the description flattens to the slice's item
        && (match itemOfDescr exampleDescr with
            | .ok it => it == exItemLive
            | .error _ => false))
      "the description layer drifted")
    [ ("the product projects to a boundary leaf",
        fun _ => assert (match tyOfDescr exampleDescr with
          | some _ => true | none => false)
          "control fired: a record is NOT a leaf — tyOfDescr must refuse")
    , ("the bridge accepts a nested product",
        fun _ =>
          let nested : Descr := .product "Inner" [("x", .prim .bool)]
          assert (match itemOfDescr (.product "Outer" [("in", nested)])
                  with | .ok _ => true | .error _ => false)
          "control fired: a nested product field must be REFUSED (SD0006)")
    , ("the bridge accepts a non-record",
        fun _ => assert (match itemOfDescr (.prim .bool) with
          | .ok _ => true | .error _ => false)
          "control fired: a leaf is not a record — the bridge must refuse")
    , ("the rendering forgets the option wrapper",
        fun _ => assert (deriveRender (.option (.prim .string)) == "string")
          "control fired: wrappers must render (the coherence law ties \
            them to the boundary's rendering)") ]
    4 42

/-! ## The codec suite (SchemaCore.Codec — the binary value lane) -/

/-- The append-form composition check at runtime: `decVal t (encVal t v ++ rest)`
    returns exactly `(v, rest)` — pattern #2 with the suffix live. -/
def codecRtOk (t : Ty) (v : Value t) (rest : List UInt8) : Bool :=
  match decVal t (encVal t v ++ rest) with
  | some p => p.1 == v && p.2 == rest
  | none => false

/-- The round trip through the `valCodec` wire grade itself. -/
def codecGradeOk (t : Ty) (v : Value t) : Bool :=
  match (valCodec t).decode ((valCodec t).encode v) with
  | some w => w == v
  | none => false

/-- Generators (the LCG discipline, #14): every draw is a pure Tape
    read — same seed, same values, byte-identical replay. -/
def genBoolV (tape : Tape) : Value .bool × Tape :=
  let (b, t) := tape.byte
  (.bool (b % 2 == 1), t)

def genNatBytes (tape : Tape) : Nat → List UInt8 × Tape
  | 0 => ([], tape)
  | n + 1 =>
      let (b, t) := tape.byte
      let (bs, t') := genNatBytes t n
      (b.toUInt8 :: bs, t')

def genU64V (tape : Tape) : Value .u64 × Tape :=
  let (bs, t) := genNatBytes tape 8
  (.u64 (UInt64.ofNat (bs.foldl (fun acc b => acc * 256 + b.toNat) 0)), t)

def genI64V (tape : Tape) : Value .i64 × Tape :=
  let (bs, t) := genNatBytes tape 8
  (.i64 (Int64.ofInt (unzigzag (bs.foldl (fun acc b => acc * 256 + b.toNat) 0))), t)

def genStringV (tape : Tape) : Value .string × Tape :=
  let (len, t1) := tape.below 5
  let rec loop : Nat → Tape → List Char × Tape
    | 0, t => ([], t)
    | n + 1, t =>
        let (b, t') := t.byte
        let (cs, t'') := loop n t'
        (Char.ofNat (32 + (b % 94).toNat) :: cs, t'')
  let (cs, t) := loop len t1
  (.string (String.ofList cs), t)

def genOptionV (tape : Tape) : Value (.option .u64) × Tape :=
  let (b, t1) := tape.byte
  if b % 2 == 0 then
    (.none, t1)
  else
    let (v, t) := genU64V t1
    (.some v, t)

def genListV (tape : Tape) : Value (.list .u64) × Tape :=
  let (len, t1) := tape.below 4
  let rec loop : Nat → Tape → List (Value .u64) × Tape
    | 0, t => ([], t)
    | n + 1, t =>
        let (v, t') := genU64V t
        let (vs, t'') := loop n t'
        (v :: vs, t'')
  let (vs, t) := loop len t1
  (.list (listToVList vs), t)

def genResultV (tape : Tape) : Value (.result .u64 .i64) × Tape :=
  let (b, t1) := tape.byte
  if b % 2 == 0 then
    let (v, t) := genU64V t1
    (.ok v, t)
  else
    let (v, t) := genI64V t1
    (.err v, t)

def genMapV (tape : Tape) : Value (.map .string .u64) × Tape :=
  let (len, t1) := tape.below 3
  let rec loop : Nat → Tape → List (Value .string × Value .u64) × Tape
    | 0, t => ([], t)
    | n + 1, t =>
        let (kv, t') := genStringV t
        let (vv, t'') := genU64V t'
        let (kvs, t3) := loop n t''
        ((kv, vv) :: kvs, t3)
  let (kvs, t) := loop len t1
  (.map (listToVMap kvs), t)

def genSetV (tape : Tape) : Value (.set .u64) × Tape :=
  let (len, t1) := tape.below 3
  let rec loop : Nat → Tape → List (Value .u64) × Tape
    | 0, t => ([], t)
    | n + 1, t =>
        let (v, t') := genU64V t
        let (vs, t'') := loop n t'
        (v :: vs, t'')
  let (vs, t) := loop len t1
  (.set (listToVList vs), t)

def genBoundedV (tape : Tape) : Value (.bounded 8) × Tape :=
  let (n, t) := tape.below 8
  (.bounded ⟨n % 8, Nat.mod_lt n (by decide)⟩, t)

/-- The known-answer vectors (the pinned bytes, mirroring the module's
    rfl coverage pins) + the append-form composition pins at concrete
    values. -/
def codecGoldenSpec : Spec :=
  Spec.ofList "the codec's known-answer vectors + composition pins"
    (fun _ =>
      assert ((
        (encVal .bool (.bool false) == [0])
          && (encVal .bool (.bool true) == [1])
          && (encVal .u64 (.u64 300) == [0xAC, 0x02])
          && (encVal .i64 (.i64 (-1)) == [1])
          && (encVal .i64 (.i64 1) == [2])
          && (encVal .string (.string "hi") == [2, 104, 105])
          && (encVal (.option .u64) .none == [0])
          && (encVal (.option .u64) (.some (.u64 5)) == [1, 5])
          && (encVal (.result .u64 .string) (.ok (.u64 1)) == [0, 1])
          && (encVal (.result .u64 .string) (.err (.string "x")) == [1, 1, 120])
          && (encVal (.list .u64)
                (.list (.cons (.u64 1) (.cons (.u64 2) .nil))) == [2, 1, 2])
          && (encVal (.bounded 5) (.bounded ⟨2, by decide⟩) == [2])
          && (encVal (.set .u64) (.set (.cons (.u64 3) .nil)) == [1, 3])
          && (encVal (.map .string .u64)
                (.map (.cons (.string "a") (.u64 1) .nil)) == [1, 1, 97, 1])
        -- the append-form composition pins: the suffix rides through
          && codecRtOk .u64 (.u64 7) [0xFF]
          && codecRtOk (.list .u64) (.list (.cons (.u64 1) .nil)) [0x00, 0x01]
          && codecRtOk (.option .string) (.some (.string "s")) [0xFF, 0x00]
          && codecGradeOk .u64 (.u64 42)))
        "the known-answer bytes or the composition pins drifted")
    [ ("u64 known answer drifts", fun _ =>
        assert (encVal .u64 (.u64 300) == [2, 0xAC])
          "control fired: the varint byte order is pinned (little-endian \
            base-128 groups)")
    , ("option tag drifts", fun _ =>
        assert (encVal (.option .u64) .none == [5])
          "control fired: the none tag is the data byte 0") ]
    4 42

/-- The round-trip sweep (LCG discipline #14): generated values of EVERY
    Ty ctor ride the append-form law against three suffixes, plus the
    wire grade's own decode∘encode. 64 seeded instances. -/
def codecRoundTripSpec : Spec :=
  Spec.ofList "the value codec round-trips every Ty ctor, append form"
    (fun tape0 =>
      let (vb, t1) := genBoolV tape0
      let (vu, t2) := genU64V t1
      let (vub, t3) := genU64V t2
      let (vi, t4) := genI64V t3
      let (vs, t5) := genStringV t4
      let (vo, t6) := genOptionV t5
      let (vl, t7) := genListV t6
      let (vr, t8) := genResultV t7
      let (vm, t9) := genMapV t8
      let (vse, t10) := genSetV t9
      let (vbo, _) := genBoundedV t10
      let suffixes : List (List UInt8) := [[], [0xFF], [0x00, 0x01]]
      let ok (t : Ty) (v : Value t) := suffixes.all (codecRtOk t v) && codecGradeOk t v
      assert (ok .bool vb && ok .u64 vu && ok .u64 vub && ok .i64 vi
        && ok .string vs && ok (.option .u64) vo && ok (.list .u64) vl
        && ok (.result .u64 .i64) vr && ok (.map .string .u64) vm
        && ok (.set .u64) vse && ok (.bounded 8) vbo)
        "a generated value failed the append-form law or the wire grade")
    [ ("truncation decodes", fun _ =>
        assert ((decVal .u64 [0x80]).isSome)
          "control fired: a truncated varint must refuse")
    , ("bad tag decodes", fun _ =>
        assert ((decVal (.option .u64) [7, 1]).isSome)
          "control fired: an unknown tag must refuse") ]
    64 42

/-- The refusal matrix: every out-of-policy shape refuses — truncation
    at every level, unknown tags, range gates (never a silent wrap),
    corrupted payloads. -/
def codecRefusalSpec : Spec :=
  Spec.ofList "the value decoder refuses out-of-policy bytes"
    (fun _ =>
      assert ((
        (decVal .u64 []).isNone
          && (decVal .u64 [0x80]).isNone
          && (decVal .u64 [0xFF, 0xFF]).isNone
          && (decVal (.option .u64) []).isNone
          && (decVal .string [5, 104]).isNone
          && (decVal (.list .u64) [3, 1]).isNone
          && (decVal (.option .u64) [2]).isNone
          && (decVal (.result .u64 .i64) [7]).isNone
          && (decVal .u64 [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80,
                0x80, 0x80, 0x01]).isNone
          && (decVal .i64 [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80,
                0x80, 0x80, 0x01]).isNone
          && (decVal (.bounded 8) [9]).isNone
          && (decVal .bool [2]).isNone))
        "an out-of-policy byte string decoded")
    [ ("truncation silently zero-parses", fun _ =>
        assert (decVal .u64 [0x80] == some (.u64 0, []))
          "control fired: truncation must refuse, never zero-parse")
    , ("cap wraps", fun _ =>
        assert ((decVal (.bounded 8) [9]).isSome)
          "control fired: the cap must gate the value") ]
    4 42

/-! ## The snapshot (the universe's serialization; SchemaCore.Snapshot) -/

/-- A second item (the canonicalization pin's second row). -/
def snapSecond : Item :=
  { name := "SchemaCore.Slice.Other"
    fields := [ { name := "ok", ty := .bool }
              , { name := "cap", ty := .bounded 42 } ] }

/-- The snapshot's byte-pin (the canonical form of the fixture's
    universe; the committed notes/universe.snapshot is this shape). -/
def expectedSnapshot : String :=
  "item SchemaCore.Slice.Example field ready bool field count u64 " ++
  "field delta i64 field label string field note option(string) " ++
  "field tags list(string)\n"

/-- The snapshot suite: the PROVED law live on the fixture (parse ∘
    print), the empty universe, the CANONICALIZATION pin (a
    reordered-but-equal registry prints byte-identically), and the
    mandatory negative controls (the parse refusals are the teeth). -/
def snapshotSpec : Spec :=
  Spec.ofList "the snapshot round-trips + canonicalizes"
    (fun _ => assert (
      -- the PROVED round-trip law, live on the fixture
      (match parse (print [exItem]) with
        | .ok its => its == [exItem]
        | .error _ => false)
      -- the empty universe IS the empty file
      && (match parse (print []) with
          | .ok its => its == []
          | .error _ => false)
      -- the CANONICALIZATION pin: print sorts
      && (print [exItem, snapSecond]
            == print [snapSecond, exItem])
      -- the two-item round trip (both rows survive the sort)
      && (match parse (print [exItem, snapSecond]) with
          | .ok its => its == [exItem, snapSecond]
          | .error _ => false)
      -- the byte-pin (the committed baseline's shape)
      && (print [exItem] == expectedSnapshot))
      "the snapshot drifted")
    [ ("a corrupted ty token parses",
        fun _ => match parse "item X field a u65\n" with
          | .ok _ => .ok ()
          | .error e => .error s!"control fired: the corrupt token was \
refused ({e})")
    , ("garbage parses",
        fun _ => match parse "hello world\n" with
          | .ok _ => .ok ()
          | .error e => .error s!"control fired: the garbage was refused ({e})")
    , ("a dropped field changes nothing",
        fun _ =>
          let dropped : Item := { exItem with fields := exampleCheckFields.drop 1 }
          assert (print [dropped] == print [exItem])
            "control fired: the dropped field's bytes are identical — the \n             round trip forgot it (the gate's byte-tie is the detector)")
    , ("a reordered registry prints differently",
        fun _ =>
          assert (print [exItem, snapSecond]
            != print [snapSecond, exItem])
          "control fired: the canonical form depends on the input order")
    , ("a duplicate item name survives the registry",
        fun _ =>
          match parse
              (print [exItem, exItem]) with
          | .ok its =>
              match registryOfItems its with
              | .error e => .error s!"control fired: the registry refused \
the duplicate item names ({e})"
              | .ok _ => .ok ()
          | .error e => .error s!"control fired: the parse refused ({e})") ]
    4 42

/-! ## The check lane (SchemaCore.Pred + SchemaCore.Check — the relational
    predicate core's seed) -/

/-- A sabotaged CheckItem whose pred reads an off-record field (the
    legality control's fixture; the fields literal is the item's
    snapshot). -/
def offRecordItem : CheckItem :=
  { name := "example-off-record"
    schemaRef := "Example"
    fields := exampleCheckFields
    pred := .u64GtLit "nope" 0 }

/-- The STALE-SNAPSHOT fixture: the stored fields drifted from the
    target's (one field dropped). -/
def staleItem : CheckItem :=
  { name := "example-stale"
    schemaRef := "Example"
    fields := exampleCheckFields.drop 1
    pred := .u64GtLit "count" 0 }

/-- The Pred fragment: evaluation pins (mirroring Pred.lean's `rfl`
    coverage at the runtime level) + the violating-rows discipline
    (02 §1: the failure carries the failing rows AS DATA). -/
def predSpec : Spec :=
  Spec.ofList "the Pred fragment evaluates + carries violating rows"
    (fun _ =>
      let r := badRow
      assert ((
      -- the scalar comparisons (the pins; the u64 columns)
        (Pred.check (fs := exampleCheckFields) (.u64EqLit "count" 3)
          goodRow == true)
        && (Pred.check (fs := exampleCheckFields) (.u64GtLit "count" 0)
              goodRow == true)
        && (Pred.check (fs := exampleCheckFields) (.u64GtLit "count" 0)
              r == false)
        && (Pred.check (fs := exampleCheckFields)
              (.and (.lit true) (.not (.u64EqLit "count" 0))) r == false)
        && (Pred.check (fs := exampleCheckFields)
              (.and (.lit true) (.not (.u64EqLit "count" 0))) goodRow == true)
      -- the refusal discipline: a missing/mistyped column refuses,
      -- never fabricates a comparison
        && (Pred.check (fs := exampleCheckFields) (.u64EqLit "nope" 0)
              goodRow == false)
        && (Pred.check (fs := exampleCheckFields) (.u64EqLit "ready" 0)
              goodRow == false)
      -- the violating rows come back AS DATA, in table order (the
      -- rows compared through the renderer — RowVals carries no BEq)
        && ((exampleCountZero.pred.violations mixedRows).length == 1)
        && ((exampleCountPositive.pred.violations mixedRows).map
              (Pred.renderRow exampleCheckFields)
              == [Pred.renderRow exampleCheckFields r])
      -- the diagnostics render the row's DATA (Value.render quotes
      -- strings — the pin carries the quotes verbatim)
        && (Pred.renderRow exampleCheckFields r
              == "ready=false; count=0; delta=1; label=\"b\"; \
                  note=some \"n\"; tags=[\"t\"]")
        && (exampleCountZero.violationDiag mixedRows).message.contains "violated"))
      "the Pred fragment drifted")
    [ ("missing column fabricates",
        fun _ =>
          assert (Pred.check (fs := exampleCheckFields) (.u64EqLit "nope" 0)
            goodRow == true)
          "control fired: a missing column must REFUSE, never fabricate")
    , ("mistyped column fabricates",
        fun _ =>
          assert (Pred.check (fs := exampleCheckFields) (.strEqLit "count" "x")
            goodRow == true)
          "control fired: a mistyped column must REFUSE, never fabricate")
    , ("violating rows dropped",
        fun _ =>
          assert ((exampleCountPositive.pred.violations mixedRows).isEmpty)
          "control fired: the failing rows ARE the diagnostic's payload")
    , ("violations forget order",
        fun _ =>
          -- a table with TWO distinct violations — order is observable
          let row7 : RowVals exampleCheckFields :=
            .cons (.bool true) (.cons (.u64 7) (.cons (.i64 0)
              (.cons (.string "c") (.cons .none (.cons (.list .nil) .nil)))))
          let vs := (exampleCountZero.pred.violations [goodRow, row7, badRow]).map
            (Pred.renderRow exampleCheckFields)
          -- the sabotaged belief: the rows ride in REVERSE table order
          assert (vs == vs.reverse)
          "control fired: the violating rows ride table order") ]
    4 42

/-- The check lane: the registered invariant discharges (the bridge's
    exercise — `checkRows_iff` decides the CLAIM); the violated one
    shows the loud gap + the violating rows; the guard refuses a
    foreign-schema table. -/
def checkSpec : Spec :=
  Spec.ofList "the registered invariants discharge at decidableNow"
    (fun _ =>
      assert ((
      -- the PASSING fixture: the discharge FIRES (the table bridge —
      -- the claim, not the checker's private Bool, is what decided)
        (exampleCountPositive.dischargeOn goodRows == some (.decided true))
      -- the item's shape: label, computed tier, payload (the data
      -- fields — claim-independent, read via the goodRows row)
        && ((exampleCountPositive.obligation goodRows).label
              == "schema/Example/example-count-positive")
        && ((exampleCountPositive.obligation goodRows).tier == .decidableNow)
        && ((exampleCountPositive.obligation goodRows).payload
              == exampleCheckFields.map (·.name))
      -- the mixed table: the verdict is the REAL failed check
        -- (`.checked false` — not the refusal; the schema is the
        -- item's own) + the violating rows ride
        && (exampleCountPositive.checkOn mixedRows == .checked false)
        && (exampleCountPositive.checkRows goodRows == true)
      -- the VIOLATED fixture: the loud gap (none — the backend
      -- refuses, it does not fabricate evidence)
        && (exampleCountZero.dischargeOn goodRows == none)
        && ((exampleCountZero.violationDiag goodRows).message
              == "invariant `example-count-zero` on `Example` violated — \
                  1 violating row(s)")))
      "the check lane drifted")
    [ ("foreign-schema table accepted",
        fun _ =>
          let foreignFields : List SchemaCore.Field := [{ name := "x", ty := .u64 }]
          let foreignRow : RowVals foreignFields := .cons (.u64 5) .nil
          assert (exampleCountPositive.checkOn [foreignRow] == .checked true)
          "control fired: a table for ANOTHER schema must refuse, never misread")
          -- the control asserts the MISREAD face (`.checked true`); the
          -- honest executor answers `.foreignSchema`, so the control fails
    , ("discharge fabricates evidence",
        fun _ =>
          assert (exampleCountZero.dischargeOn mixedRows == some (.decided true))
          "control fired: a violated claim must be the LOUD none")
    , ("tier mis-wire passes silently",
        fun _ =>
          assert (¬(Kit.tierMismatch (exampleCountPositive.obligation [])
            (Kit.Evidence.oracleRow "oracle-1")))
          "control fired: an oracle-row evidence against decidableNow is a \
            mis-wire")
    , ("legality bridge accepts an off-record field",
        fun _ =>
          let items : List Item :=
            [ { name := "Example", fields := exampleCheckFields } ]
          assert ((offRecordItem.scopedDiags items).isEmpty)
          "control fired: an off-record read must be a finding")
    , ("legality bridge accepts a stale snapshot",
        fun _ =>
          let items : List Item :=
            [ { name := "Example", fields := exampleCheckFields } ]
          assert ((staleItem.scopedDiags items).isEmpty)
          "control fired: a stale field snapshot must be a finding")
    , ("legality bridge misses an unknown target",
        fun _ =>
          let unknown : CheckItem := { offRecordItem with schemaRef := "Nope" }
          let items : List Item :=
            [ { name := "Example", fields := exampleCheckFields } ]
          assert ((unknown.scopedDiags items).isEmpty)
          "control fired: an unregistered target must be a finding") ]
    4 42

/-! ## The keys lane (SchemaCore.Keys — declared keys + foreign keys,
    the determinacy theorems, 02 §3) -/

/-- The hand-built two-table universe (the FK positive case needs a
target with a declared key — the slice's registered items can't host
one: ExampleEx has no scalar field — so the cascade's foreign rungs
exercise over hand-built data, the legacy test shape). -/
abbrev customerFields : List SchemaCore.Field :=
  [ { name := "id", ty := .u64 }
  , { name := "name", ty := .string } ]

abbrev orderFields : List SchemaCore.Field :=
  [ { name := "oid", ty := .u64 }
  , { name := "cust", ty := .u64 }
  , { name := "qty", ty := .u64 } ]

abbrev customerDecl : KeyDecl :=
  { record := "Customer", fields := customerFields, key := "id" }

abbrev orderDecl : KeyDecl :=
  { record := "Order", fields := orderFields, key := "oid"
    foreign := [{ field := "cust", target := "Customer" }] }

def keyItems : List Item :=
  [ ⟨"Customer", customerFields⟩, ⟨"Order", orderFields⟩ ]

/-- The good tables (distinct keys; every FK image resolves). -/
def custRows : List (RowVals customerFields) :=
  [ .cons (.u64 1) (.cons (.string "ann") .nil)
  , .cons (.u64 2) (.cons (.string "bob") .nil) ]

def orderRows : List (RowVals orderFields) :=
  [ .cons (.u64 100) (.cons (.u64 1) (.cons (.u64 3) .nil))
  , .cons (.u64 101) (.cons (.u64 2) (.cons (.u64 1) .nil)) ]

/-- The sabotaged table: two DISTINCT rows sharing the key image 100
(the conservative-inference control's data — determinacy fails without
the checked `uniqueOn`). -/
def dupOrderRows : List (RowVals orderFields) :=
  [ .cons (.u64 100) (.cons (.u64 1) (.cons (.u64 3) .nil))
  , .cons (.u64 100) (.cons (.u64 2) (.cons (.u64 4) .nil)) ]

/-- The key image of order 100 (the lookup's probe). -/
def orderKey100 : FieldVal := ⟨.u64, .u64 100⟩

/-- THE DETERMINACY THEOREM, exercised at the fixture: the rows
matching the key image are pairwise equal (the theorem itself — not a
Bool shadow — cited from the lane). -/
example (huniq : orderDecl.uniqueOn orderRows = true) :
    ∀ (r1 r2 : RowVals orderFields),
    r1 ∈ orderRows → r2 ∈ orderRows →
    orderDecl.matchesKey r1 orderKey100 = true →
    orderDecl.matchesKey r2 orderKey100 = true → r1 = r2 :=
  fun r1 r2 hmem1 hmem2 hm1 hm2 =>
    orderDecl.uniqueOn_determines orderKey100 orderRows r1 r2 huniq
      hmem1 hmem2 hm1 hm2

/-- The Option-shape corollary, exercised: the key-backed lookup's
results are subsingleton (the theorem `lookup?_atMostOne`). -/
example (r1 r2 : RowVals orderFields)
    (h1 : orderDecl.lookup? orderRows orderKey100 = some r1)
    (h2 : orderDecl.lookup? orderRows orderKey100 = some r2) :
    r1 = r2 :=
  orderDecl.lookup?_atMostOne orderRows (by rfl) orderKey100 h1 h2

/-- The keys lane's suite: the WF cascade's teeth (a broken FK refuses
with the NAMED RUNG's diagnostic), the determinacy payoff live, the
obligations discharged through the kit's backend, and the mandatory
negative controls. -/
def keysSpec : Spec :=
  Spec.ofList "the keys lane: WF cascade + determinacy + obligations"
    (fun _ => assert ((
    -- the WELL-FORMED fixture: the cascade is clean, the gate reading
    -- agrees, the CheckedProp is complete
      (keyDeclsCheck keyItems [customerDecl, orderDecl] == [])
      && (keyDeclsWellFormed keyItems [customerDecl, orderDecl])
      && keysChecked.isComplete
    -- the canonical meanings over the good tables
      && (orderDecl.uniqueOn orderRows == true)
      && (customerDecl.uniqueOn custRows == true)
      && (orderDecl.referencesOn { field := "cust", target := "Customer" }
            customerDecl orderRows custRows == true)
    -- the DETERMINACY PAYOFF live: the Option-shaped lookup hits the
    -- unique row; the List-shaped conservative surface sees both rows
      && (match orderDecl.lookup? orderRows orderKey100 with
          | some row => toString (Pred.renderRow orderFields row)
              == "oid=100; cust=1; qty=3"
          | none => false)
      && ((orderDecl.lookupAll dupOrderRows orderKey100).length == 2)
    -- the obligation view: BOTH rows discharge through the kit's
    -- decidableNow backend over the all-default singleton tables
      && (customerDecl.dischargeUniqueOn
            (customerDecl.defaultTable?.getD []) == some (.decided true))
      && (orderDecl.dischargeUniqueOn
            (orderDecl.defaultTable?.getD []) == some (.decided true))
      && (orderDecl.dischargeReferencesOn
            { field := "cust", target := "Customer" } customerDecl
            (orderDecl.defaultTable?.getD [])
            (customerDecl.defaultTable?.getD []) == some (.decided true))
      && ((KeyDecl.defaultObligations [exampleKey] exampleKey).length == 1)))
      "the keys lane drifted")
    [ ("the type-mismatch rung passes",
        fun _ =>
          -- cust carries STRING against the target's u64 key: the
          -- SABOTAGED belief is that the cascade is clean — the honest
          -- checker refuses at the foreignTy rung, the control fails
          let badFields : List SchemaCore.Field :=
            [ { name := "oid", ty := .u64 }
            , { name := "cust", ty := .string }
            , { name := "qty", ty := .u64 } ]
          let bad : KeyDecl :=
            { record := "Order", fields := badFields, key := "oid"
              foreign := [{ field := "cust", target := "Customer" }] }
          assert ((keyDeclsCheck keyItems [bad]).isEmpty)
          "control fired: the TYPE-AGREEMENT rung must refuse")
    , ("the forward-reference rung passes",
        fun _ =>
          -- the target's key NOT declared: the foreignDecl rung fires
          let noCust : KeyDecl :=
            { record := "Order", fields := orderFields, key := "oid"
              foreign := [{ field := "cust", target := "Customer" }] }
          assert ((keyDeclsCheck keyItems [noCust]).isEmpty)
          "control fired: the TARGET-DECLARATION rung must refuse")
    , ("the missing-FK-field rung passes",
        fun _ =>
          let bad : KeyDecl :=
            { record := "Order", fields := orderFields, key := "oid"
              foreign := [{ field := "nope", target := "Customer" }] }
          assert ((keyDeclsCheck keyItems [bad]).isEmpty)
          "control fired: the FK-FIELD rung must refuse")
    , ("the missing-target rung passes",
        fun _ =>
          let bad : KeyDecl :=
            { record := "Order", fields := orderFields, key := "oid"
              foreign := [{ field := "cust", target := "Nope" }] }
          assert ((keyDeclsCheck keyItems [bad]).isEmpty)
          "control fired: the TARGET-RESOLUTION rung must refuse")
    , ("the non-scalar-key rung passes",
        fun _ =>
          -- note is an option — outside the scalar key universe
          let bad : KeyDecl :=
            { record := "Example", fields := exampleCheckFields,
              key := "note" }
          let items : List Item :=
            [ { name := "Example", fields := exampleCheckFields } ]
          assert ((keyDeclsCheck items [bad]).isEmpty)
          "control fired: the KEY-FIELD scalar gate must refuse")
    , ("the stale-snapshot rung passes",
        fun _ =>
          let bad : KeyDecl :=
            { record := "Order", fields := orderFields.drop 1, key := "oid" }
          assert ((keyDeclsCheck keyItems [bad]).isEmpty)
          "control fired: the RESOLVED-RECORD rung must refuse")
    , ("the duplicate-declaration scan passes",
        fun _ =>
          assert ((keyDeclsCheck keyItems [customerDecl, customerDecl]).isEmpty)
          "control fired: the dup scan must refuse")
    , ("the unconstrained universe passes",
        fun _ =>
          -- the record is not IN the universe: the resolver rung fires
          let ghost : KeyDecl :=
            { record := "Ghost", fields := orderFields, key := "oid" }
          assert ((keyDeclsCheck keyItems [ghost]).isEmpty)
          "control fired: the RECORD-RESOLUTION rung must refuse")
    , ("determinacy without the checked key",
        fun _ =>
          -- the conservative-inference control: the SABOTAGED belief is
          -- that uniqueness holds WITHOUT the checked uniqueOn — the
          -- honest check says false (two distinct rows share the image)
          let r1 : RowVals orderFields :=
            .cons (.u64 100) (.cons (.u64 1) (.cons (.u64 3) .nil))
          let r2 : RowVals orderFields :=
            .cons (.u64 100) (.cons (.u64 2) (.cons (.u64 4) .nil))
          assert (orderDecl.uniqueOn dupOrderRows == true)
          "control fired: the duplicate-key rows must be visible as data — \
            the hypothesis is load-bearing")
    , ("the broken FK discharges",
        fun _ =>
          -- a type-mismatched FK image never resolves in the target's
          -- key images (beq is type-guarded): the SABOTAGED belief is
          -- that the obligation discharges — the honest backend shows
          -- the LOUD gap, never fabricated evidence
          let badFields : List SchemaCore.Field :=
            [ { name := "oid", ty := .u64 }
            , { name := "cust", ty := .string }
            , { name := "qty", ty := .u64 } ]
          let bad : KeyDecl :=
            { record := "Order", fields := badFields, key := "oid"
              foreign := [{ field := "cust", target := "Customer" }] }
          assert (bad.dischargeReferencesOn
            { field := "cust", target := "Customer" } customerDecl
            (bad.defaultTable?.getD [])
            (customerDecl.defaultTable?.getD []) == some (.decided true))
          "control fired: a broken FK's obligation must be the loud none")
    , ("the default-less record discharges",
        fun _ =>
          -- bounded 0 is default-less: the SABOTAGED belief is that a
          -- default table exists — the honest gap is the loud none
          let capless : KeyDecl :=
            { record := "Cap", fields := [{ name := "n", ty := .bounded 0 }],
              key := "n" }
          assert (capless.defaultTable?.isSome)
          "control fired: a default-less record must show the loud gap") ]
    4 42

/-! ## The update lane (SchemaCore.Update — the data plane's operational
    half: SET/INSERT/DELETE over declared keys) -/

abbrev updFields : List SchemaCore.Field :=
  [ { name := "id", ty := .u64 }
  , { name := "name", ty := .string }
  , { name := "qty", ty := .u64 } ]

/-- The write paths (hand-built — the GADT's index IS the evidence). -/
def updPathName : ColPath "name" .string updFields := .there .here
def updPathQty : ColPath "qty" .u64 updFields := .there (.there .here)

def updRow (i : UInt64) (n : String) (q : UInt64) : RowVals updFields :=
  .cons (.u64 i) (.cons (.string n) (.cons (.u64 q) .nil))

def updRows : List (RowVals updFields) :=
  [ updRow 1 "ann" 3, updRow 2 "bob" 1, updRow 3 "cy" 7 ]

/-- uRename: `name := "x"`, total guard. -/
def uRename : UpdateItem updFields where
  record := "Order"; name := "rename"
  guard := .lit true
  sets := [{ field := { name := "name", ty := .string }
             path := updPathName, value := .string "x" }]

/-- uRestock: `qty := 9` where qty > 0. -/
def uRestock : UpdateItem updFields where
  record := "Order"; name := "restock"
  guard := .u64GtLit "qty" 0
  sets := [{ field := { name := "qty", ty := .u64 }
             path := updPathQty, value := .u64 9 }]

/-- THE PREMISE PACK, discharged by decide over the concrete fixtures:
    the derived reads (never hand-listed), the disjoint writes, the
    refusals, the separations. -/
def renameRestockCompat : UpdateCompat uRename uRestock updRows where
  ni₁₂ := by decide
  ni₂₁ := by decide
  setDisj := by decide
  refuse₁₂ := by decide
  refuse₂₁ := by decide
  insertSep₁₂ := by decide
  insertSep₂₁ := by decide

/-- THE ORDER-FREEDOM PIN: the two disjoint updates compute the SAME
    table in either order (Law 5b, the compat pack riding it). -/
example :
    uRename.apply (uRestock.apply updRows)
      = uRestock.apply (uRename.apply updRows) :=
  apply2_comm renameRestockCompat rfl rfl

/-- the same table's VALUE pin (the concrete net effect). -/
example :
    uRename.apply (uRestock.apply updRows)
      = [updRow 1 "x" 9, updRow 2 "x" 9, updRow 3 "x" 9] := rfl

/-- uSet2: `qty := 2` — writes the column uPurge READS. -/
def uSet2 : UpdateItem updFields where
  record := "Order"; name := "set-two"
  guard := .lit true
  sets := [{ field := { name := "qty", ty := .u64 }
             path := updPathQty, value := .u64 2 }]

/-- uPurge: DELETE where qty > 2. -/
def uPurge : UpdateItem updFields where
  record := "Order"; name := "purge"
  guard := .u64GtLit "qty" 2
  sets := []
  delete := true

/-- THE SAME-KEY LATER-WINS WITNESS (the premise's teeth): OUTSIDE the
    disjointness premise the order IS observable — set-then-purge keeps
    every row (the write moved qty under the purge's guard), purge-then-
    set deletes two. PINNED as the counterexample. -/
example :
    uSet2.apply (uPurge.apply updRows) = [updRow 2 "bob" 2] := rfl

example :
    uPurge.apply (uSet2.apply updRows)
      = [updRow 1 "ann" 2, updRow 2 "bob" 2, updRow 3 "cy" 2] := rfl

/-- The keyed WF fixtures. -/
def updKeyDecl : KeyDecl :=
  { record := "Order", fields := updFields, key := "id" }

/-- uInsFresh: an INSERT with a declared key. -/
def uInsFresh : UpdateItem updFields where
  record := "Order"; name := "ins-fresh"
  guard := .lit true
  sets := []
  insert? := some (updRow 9 "d" 1)
  key? := some "id"

/-- uDel: a DELETE keyed on id. -/
def uDel : UpdateItem updFields where
  record := "Order"; name := "del"
  guard := .u64EqLit "id" 2
  sets := []
  delete := true
  key? := some "id"

/-- uDup: TWO clauses on one column (the dup-set rung's fixture). -/
def uDup : UpdateItem updFields where
  record := "Order"; name := "dup"
  guard := .lit true
  sets := [{ field := { name := "name", ty := .string }
             path := updPathName, value := .string "a" }
          ,{ field := { name := "name", ty := .string }
             path := updPathName, value := .string "b" }]

/-- uGhostKey: delete keyed on an UNDECLARED key. -/
def uGhostKey : UpdateItem updFields where
  record := "Order"; name := "ghost"
  guard := .lit true
  sets := []
  delete := true
  key? := some "nope"
/-- uInsDup: an insert COLLIDING with the default row's key (the
    obligation's loud gap fixture). -/
def uInsDup : UpdateItem updFields where
  record := "Order"; name := "ins-dup"
  guard := .lit true
  sets := []
  insert? := some (updRow 0 "d" 1)
  key? := some "id"

/-- The keyed delta's fixtures (the keyed put at the canonical keyed
    meaning). -/
def kxRow (i : UInt64) (n : String) (q : UInt64) : RowVals updFields :=
  updRow i n q

/-- The keyed state AS A FUNCTION (the canonical keyed meaning — the
    state IS a `KeyState`: key image → row). -/
def kxState (rows : List (RowVals updFields)) : KeyState updFields := fun k =>
  match rows with
  | [] => none
  | r :: rest =>
      match RowVals.project? updFields r "id" with
      | some v => if FieldVal.beq v k then some r else kxState rest k
      | none => kxState rest k

/-- The keyed state's RENDERING (states are functions — the comparison
    surface is the rendered row at each probed key). -/
def kxAt (X : Option (KeyState updFields)) (i : UInt64) : String :=
  match X with
  | none => "none"
  | some st =>
      match st ⟨.u64, .u64 i⟩ with
      | none => "none"
      | some r => Pred.renderRow updFields r

def kxPut (i : UInt64) (oldN : String) (newN : String) : KeyPut updFields where
  key := ⟨.u64, .u64 i⟩
  old? := some (kxRow i oldN 3)
  new? := some (kxRow i newN 3)

/-- The keyed updates' compat at the fixture (the same-shape pack over
    the ann-row). -/
def updateWfPin : UpdateWf uDel [updKeyDecl] :=
  ⟨by decide, by intro _; exact ⟨"id", updKeyDecl, rfl, rfl⟩⟩

/-- The update suite. -/
def updateSpec : Spec :=
  Spec.ofList "the update lane: laws, lowering, WF, obligations"
    (fun _ => assert ((
    -- the WF cascade: the good keyed updates are clean, the bridge rides
      ((updateDiags uInsFresh [updKeyDecl]).isEmpty)
      && ((updateDiags uDel [updKeyDecl]).isEmpty)
    -- the obligations: the keyed update's preservation discharges
      && ((uRename.dischargeUnique "id") == some (.decided true))
    -- the keyed delta: the checked put's round trip at the fixture
      && ((match (kxPut 1 "ann" "anna").apply (kxState updRows) with
          | some _ => true | none => false))
      ))
      "the update lane drifted")
    [ ("the SAME-key conflict is order-INDEPENDENT",
        fun _ =>
          -- the premise's teeth: OUTSIDE the disjointness premise the
          -- order IS observable (set-then-purge keeps all three rows,
          -- purge-then-set keeps one) — the control claims independence
          -- and must FAIL
          assert ((uSet2.apply (uPurge.apply updRows)).map
              (Pred.renderRow updFields)
            == (uPurge.apply (uSet2.apply updRows)).map
              (Pred.renderRow updFields))
          "control fired: the order-dependence outside the disjointness \
            premise is OBSERVABLE — later-wins is by design")
    , ("the dup-set update passes the WF",
        fun _ =>
          assert ((updateDiags uDup [updKeyDecl]).isEmpty)
          "control fired: two SET clauses on one column must trip the \
            dup-set rung (SU0001) — the order-freedom premise is the data")
    , ("the keyless insert passes the WF",
        fun _ =>
          let u : UpdateItem updFields :=
            { record := "Order", name := "ins", guard := .lit true
              sets := []
              insert? := some (updRow 9 "d" 1) }
          assert ((updateDiags u [updKeyDecl]).isEmpty)
          "control fired: an insert without a declared key must trip the \
            keyed rung (SU0002)")
    , ("the ghost key passes the WF",
        fun _ =>
          assert ((updateDiags uGhostKey [updKeyDecl]).isEmpty)
          "control fired: a delete keyed on an undeclared key must trip \
            the key-resolution rung (SU0003)")
    , ("the colliding insert discharges",
        fun _ =>
          -- the inserted row's key collides with the default row's:
          -- the post-table has TWO id-0 rows — the preservation claim
          -- is FALSE — the discharge must be the loud none
          assert (uInsDup.dischargeUnique "id" == some (.decided true))
          "control fired: a key-colliding insert must be the LOUD none — \
            the backend refuses, it never fabricates evidence")
    , ("the keyed delta's same-key puts commute",
        fun _ =>
          -- the Disjoint predicate's teeth: two puts at the SAME key
          -- are order-dependent — p then q chains (anna → bob); in the
          -- other order q's old image is absent and the fold REFUSES —
          -- the equality of the two orders must FAIL
          let X : Option (KeyState updFields) := some (kxState updRows)
          let p := kxPut 1 "ann" "anna"
          let q := kxPut 1 "anna" "bob"
          assert (kxAt ((X.bind (KeyPut.apply p)).bind (KeyPut.apply q)) 1
            == kxAt ((X.bind (KeyPut.apply q)).bind (KeyPut.apply p)) 1)
          "control fired: same-key puts are order-dependent (bob vs the \
            poisoned none) — Disjoint is load-bearing")
    , ("the delta-lowering folds to nothing",
        fun _ =>
          -- the lowering's refusal face: a delete whose key projection
          -- fails lowers to [] — the refusal reading, pinned
          let u : UpdateItem updFields :=
            { record := "Order", name := "del"
              guard := .lit true, sets := [], delete := true
              key? := some "id" }
          assert ((u.lowerRow (updRow 0 "x" 1)).isEmpty)
          "control fired: a delete of a non-projecting row must lower \
            to [] (the refusal reading), never misread") ]
    4 42

/-! ## The semantic-profiles lane (SchemaCore.Profile — 16-surface §4.5) -/

/-- The Money-cents fixture (scale 100): the profile AND the scale in
    the TYPE; the constructor's proof fields are the bounded lane's
    pattern — out-of-contract values unconstructible (the mod is the
    LCG discipline's clamp, a no-op below the capacity). -/
def mkMoney100 (u : Nat) : Money 100 :=
  ⟨u % 2 ^ 64, Nat.mod_lt u (by decide), by decide⟩

/-- The units draw: 8 bytes — below the capacity by construction. -/
def genMoney (tape : Tape) : Money 100 × Tape :=
  let (bs, t) := genNatBytes tape 8
  (mkMoney100 (bs.foldl (fun acc b => acc * 256 + b.toNat) 0), t)

/-- The laws at one generated instance: the add exactness/refusal
disjunction, the mul floor law, the total order, the codec legality
(the wire sees the bare u64, the suffix rides through). -/
def profileLawOk (a b : Money 100) : Bool :=
  let u := a.raw.units
  let v := b.raw.units
  let addOk :=
    match a.raw.add? b.raw with
    | some c => c.units == u + v
    | none => !(u + v < 2 ^ 64)
  let mulOk :=
    match a.raw.mul? b.raw with
    | some c => c.units == u * v / 100
      && (c.units * 100 ≤ u * v && u * v < (c.units + 1) * 100)
    | none => !(u * v / 100 < 2 ^ 64)
  let ordOk := a.raw ≤ b.raw || b.raw ≤ a.raw
  let wireOk :=
    match decVal .u64 (encVal .u64 a.raw.toValue ++ [0xFF]) with
    | some p => p.1 == a.raw.toValue && p.2 == [0xFF]
    | none => false
  addOk && mulOk && ordOk && wireOk

/-- The known-answer + erasure pins (the discipline's concrete face). -/
def profilePinSpec : Spec :=
  Spec.ofList "the profile lane: erasure pins + the deterministic known answers"
    (fun _ =>
      assert ((
        -- the ERASURE pins: the phantom index costs nothing at runtime
        ((⟨(7 : UInt64)⟩ : Profiled .plain UInt64).raw == 7)
          && ((Profiled.iso .plain UInt64).to ((Profiled.iso .plain UInt64).inv 7) == 7)
          && ((⟨(7 : UInt64)⟩ : Labeled UInt64)
                == (⟨(7 : UInt64)⟩ : Profiled .plain UInt64))
        -- the Money-cents known answers: exact add
          && (((mkMoney100 150).raw.add? (mkMoney100 275).raw).map (fun c => c.units)
                == some 425)
        -- the NAMED floor: 33¢ × 33¢ = 10.89 units² → 10 (NOT 11)
          && (((mkMoney100 33).raw.mul? (mkMoney100 33).raw).map (fun c => c.units)
                == some 10)
        -- the exact square: 50¢ × 50¢ = 25¢, no rounding needed
          && (((mkMoney100 50).raw.mul? (mkMoney100 50).raw).map (fun c => c.units)
                == some 25)
        -- the overflow REFUSAL: max units + 1 refuses, never wraps
          && ((mkMoney100 (2 ^ 64 - 1)).raw.add? (mkMoney100 1).raw) == none
        -- the scale is type-level data, not runtime
          && (Fixed.scaleOf (mkMoney100 25).raw) == 100
        -- the lift evals to the units (the value lane's erasure face)
          && ((mkMoney100 425).raw.toValue.eval == 425)))
        "the profile pins drifted")
    [ ("overflow wraps", fun _ =>
        assert (((mkMoney100 (2 ^ 64 - 1)).raw.add? (mkMoney100 1).raw).map (fun c => c.units)
          == some 0)
          "control fired: the checked add must refuse at the capacity, never wrap")
    , ("mul is exact", fun _ =>
        assert (((mkMoney100 33).raw.mul? (mkMoney100 33).raw).map (fun c => c.units)
          == some 1089)
          "control fired: mul rounds — the named floor, not an exact product")
    , ("the phantom leaks into the wire", fun _ =>
        assert (encVal .u64 (mkMoney100 425).raw.toValue
          != Kit.Varint.encVarNat 425)
          "control fired: codec legality is byte-identity with the bare u64 — \
            the profile text is nowhere in the bytes") ]
    4 42

/-- The law sweep (LCG discipline #14): two 8-byte draws per instance —
    the add/mul/order/codec laws at every instance, the overflow branch
    exercised (two uniform 64-bit draws sum past the capacity about
    half the time). -/
def profileSpec : Spec :=
  Spec.ofList "the deterministic laws hold at every generated instance"
    (fun tape0 =>
      let (a, t1) := genMoney tape0
      let (b, _) := genMoney t1
      assert (profileLawOk a b)
        "a generated instance broke the erasure, the fixed-point laws, or codec legality")
    [ ("unchecked wrap", fun _ =>
        assert (((mkMoney100 (2 ^ 64 - 1)).raw.add? (mkMoney100 1).raw).isSome)
          "control fired: the checked add must refuse at the capacity")
    , ("floor rounds up", fun _ =>
        assert (((mkMoney100 33).raw.mul? (mkMoney100 33).raw).map (fun c => c.units)
          == some 11)
          "control fired: the named floor rounds DOWN — 10.89 units² is 10") ]
    64 42

/-! ## The breaking lane (SchemaCore.Diff — the diff + verdict + remedy seed) -/

-- The fixtures: a pair of universes whose net change is KNOWN. `b` is
-- the bounded-cap field, so the widening remedy has a live target.
def widgetsOld : Item :=
  { name := "Widgets"
    fields := [ { name := "a", ty := .u64 }
              , { name := "b", ty := .bounded 42 } ] }

def widgetsWide : Item :=
  { name := "Widgets"
    fields := [ { name := "a", ty := .u64 }
              , { name := "b", ty := .bounded 100 } ] }

def extrasItem : Item :=
  { name := "Extras", fields := [ { name := "c", ty := .bool } ] }

def ghostItem : Item :=
  { name := "Ghost", fields := [ { name := "g", ty := .u64 } ] }

/-- The rename twin: SAME field contents, different name — the D13
    delete+add pair (candidates, never merged). -/
def ghostTwin : Item := { ghostItem with name := "Ghost2" }

-- The worked remedy: the bounded-cap widening 42 ≤ 100, soundness
-- discharged at the declaration site (`widenBounded_sound`).
def widenSmall : FieldMigration := widenBounded "b" 42 100 (by decide)

def widgetsWidening : Migration :=
  { item := "Widgets", fields := [widenSmall] }

/-- The diff's known answers: the net change over the name key, exact. -/
def diffSpec : Spec :=
  Spec.ofList "the diff's known answers"
    (fun _ => assert ((
      -- identical universes: the NET change is empty
      (diff [widgetsOld] [widgetsOld] = [])
      -- pure removal / pure addition
      && (diff [extrasItem] [] = [.removed "Extras"])
      && (diff [] [extrasItem] = [.added "Extras"])
      -- the retyped field carries the old AND new type as evidence
      && (diff [widgetsOld] [widgetsWide]
            = [.changed "Widgets"
                [.fieldTypeChanged "b" (.bounded 42) (.bounded 100)]])
      -- the field-level evidence set: a field add rides the changed item
      && (diff [ghostItem]
                [{ ghostItem with fields := ghostItem.fields ++ [ { name := "h", ty := .bool } ] }]
            = [.changed "Ghost" [.fieldAdded "h"]])
      -- the rename twin is NOT merged: removed + added, both named
      && (diff [ghostItem] [ghostTwin]
            = [.removed "Ghost", .added "Ghost2"])
      -- the rename CANDIDACY is named (the report's honesty face)
      && (renameCandidates [ghostItem] [ghostTwin] = [("Ghost", "Ghost2")])
      -- no candidacy without agreeing field contents
      && (renameCandidates [widgetsOld] [ghostTwin] = [])))
      "the diff's known answers drifted")
    [ ("an unchanged universe still diffs",
        fun _ => assert (diff [widgetsOld] [widgetsOld] != [])
          "control fired: the net change of an identical pair must be EMPTY \
(the Z-set discipline: net-zero = nothing changed)")
    , ("a rename is silently merged",
        fun _ => assert (diff [ghostItem] [ghostTwin] = [])
          "control fired: a delete+add pair must stay removed+added (D13: \
names are presentation; the diff never merges on field contents)")
    , ("a type change is invisible",
        fun _ => assert (diff [widgetsOld] [widgetsWide] = [])
          "control fired: a retyped field is a BREAKING finding with \
evidence, never silent") ]
    4 42

/-- The verdict's both faces + the exit-code discipline. -/
def verdictSpec : Spec :=
  Spec.ofList "the verdict's both faces + the bridge"
    (fun _ => assert ((
      -- clean: additions only
      (verdictOf (diff [] [extrasItem]) [] = .clean)
      -- unremedied: a removal, no remedy registered
      && (verdictOf (diff [extrasItem] []) [] = .unremedied)
      -- unremedied: the widening, NO remedy registered
      && (verdictOf (diff [widgetsOld] [widgetsWide]) [] = .unremedied)
      -- remedied: the widening WITH its registered migration
      && (verdictOf (diff [widgetsOld] [widgetsWide]) [widgetsWidening]
            = .remedied)
      -- the exit-code discipline (the ONLY mapping)
      && (CompatVerdict.exitCode .clean = 0)
      && (CompatVerdict.exitCode .remedied = 0)
      && (CompatVerdict.exitCode .unremedied = 2)
      -- the relation's both faces over concrete items
      && (backwardCompatible [widgetsOld] [widgetsOld, extrasItem])
      && !(backwardCompatible [extrasItem] [])))
      "the verdict's faces drifted")
    [ ("an unremedied retype exits clean",
        fun _ => assert (CompatVerdict.exitCode
          (verdictOf (diff [widgetsOld] [widgetsWide]) []) = 0)
          "control fired: a breaking change with no remedy exits 2 — the \
loud warning (`just gates` fails on 2), never a quiet success")
    , ("a removal is backward compatible",
        fun _ => assert (backwardCompatible [extrasItem] [])
          "control fired: a removal strands old readers — the relation \
must refuse it")
    , ("the bridge's clean face lies",
        fun _ => assert (!(backwardCompatible [widgetsOld] [widgetsOld, extrasItem]))
          "control fired: additions are replay-safe (no old data references \
them) — the clean verdict and the relation agree (pattern #1)") ]
    4 42

-- The near-miss migration: oldTy bounded 41 ≠ the found bounded 42
-- (the negative control's fixture).
def nearMissMigration : Migration :=
  { item := "Widgets"
    fields := [ { field := "b"
                , oldTy := .bounded 41
                , newTy := .bounded 100
                , apply := fun v =>
                    match v with
                    | .bounded f => .bounded (Fin.castLE (by decide) f) } ] }

/-- The remedy's soundness exercised + the honest unremedied rule. -/
def remedySpec : Spec :=
  Spec.ofList "the remedy's soundness is exercised + the honest unremedied rule"
    (fun _ => assert ((
      -- the diagram commutes: the widened value denotes the SAME number
      ((Value.eval (.bounded 100) (widenSmall.apply (Value.bounded ⟨40, by decide⟩))).val = 40)
      -- the migration remedies exactly the widening change (right item,
      -- right field, exactly the found old/new types)
      && (widgetsWidening.remedies
            (Change.changed "Widgets"
              [.fieldTypeChanged "b" (.bounded 42) (.bounded 100)]))
      -- field ADDITIONS ride along (no old data to map)
      && (widgetsWidening.remedies
            (Change.changed "Widgets" [.fieldAdded "h"]))
      -- REMOVALS ARE HONESTLY UNREMEDIED (no value-map target)
      && !(widgetsWidening.remedies (Change.removed "Widgets"))
      && !(widgetsWidening.remedies (Change.removed "Extras"))
      -- the item name gates the remedy
      && !(widgetsWidening.remedies
            (Change.changed "Other"
              [.fieldTypeChanged "b" (.bounded 42) (.bounded 100)]))))
      "the remedy's behavior drifted")
    [ ("a widened value changes the number",
        fun _ => assert ((Value.eval (.bounded 100)
          (widenSmall.apply (Value.bounded ⟨40, by decide⟩))).val = 41)
          "control fired: widening is not reinterpretation — the SAME \
number, or the soundness obligation is false")
    , ("a remedy with the wrong old type still remediess",
        fun _ => assert (nearMissMigration.remedies
          (Change.changed "Widgets"
            [.fieldTypeChanged "b" (.bounded 42) (.bounded 100)]))
          "control fired: the remedy must match the found old AND new \
types exactly — a near-miss migration is no evidence")
    , ("a removed item has a value-map target",
        fun _ => assert (widgetsWidening.remedies (Change.removed "Widgets"))
          "control fired: removals are honestly UNREMEDIED — there is no \
value-map target for gone data (the honest verdict, not an oversight)") ]
    4 42

-- The bridge, at theorem level: clean ⟺ the relation (both directions
-- pinned over concrete universes — the gate runs the checker, the
-- theorem says the checker is the relation's decision).
example : verdictOf (diff [widgetsOld] [widgetsOld]) [] = .clean := rfl
example : backwardCompatible [widgetsOld] [widgetsOld] = true := rfl
example : backwardCompatible [extrasItem] [] = false := rfl

/-! ## The writable-views lane (SchemaCore.View — 02 §7's relational lenses) -/

/-- The account row fixture (the Violate fixture's schema). -/
def vwAcct (i : UInt64) (o : String) (bal : Int64) : RowVals accountFields :=
  .cons (.u64 i) (.cons (.string o) (.cons (.i64 bal) .nil))

abbrev vwAcct1 : RowVals accountFields := vwAcct 1 "ann" 100
abbrev vwAcct2 : RowVals accountFields := vwAcct 2 "bob" 50
abbrev vwAccts : List (RowVals accountFields) := [vwAcct1, vwAcct2]

abbrev vwKd : KeyDecl := { record := "account", fields := accountFields, key := "id" }

/-- The balances view: the KEY-RESPECTING projection (id, balance) —
    the owner column is the complement (03 §2: what the surface can't
    express, the base retains). -/
abbrev vwIdCol : ViewCol accountFields :=
  { field := { name := "id", ty := .u64 }, path := .here }
abbrev vwBalCol : ViewCol accountFields :=
  { field := { name := "balance", ty := .i64 }
    path := .there (.there .here) }
abbrev balView : ViewDef accountFields :=
  { name := "balances", cols := [vwIdCol, vwBalCol] }

theorem balCoh : ViewCoherent vwKd balView where
  fieldNodup := by decide
  colNodup := by decide
  keyMem := ⟨vwIdCol, List.mem_cons_self, rfl⟩
  selKeyOnly := by
    intro n hn
    exact absurd hn (by simp [balView, Pred.reads])

/-- The view row over the balances view. -/
def balRow (i : UInt64) (b : Int64) : RowVals balView.vfields :=
  .cons (.u64 i) (.cons (.i64 b) .nil)

/-- THE WORKED EDIT: the balances view's row edited (balance 100 → 75).
    The verdict: the base delta is the update lane's `RowDelta.update` of
    the written row (the owner PRESERVED — the complement), the
    post-state the keyed applicator's output. -/
def vwEditVerdict := viewPut vwKd balView vwAccts (balRow 1 75)

example : (match vwEditVerdict with
    | .apply δ post =>
        δ.length == 1
          && (match δ with
              | [RowDelta.update w] => rowBeq accountFields w (vwAcct 1 "ann" 75)
              | _ => false)
          && (match post with
              | [r1, r2] =>
                  rowBeq accountFields r1 (vwAcct 1 "ann" 75)
                    && rowBeq accountFields r2 vwAcct2
              | _ => false)
    | _ => false) = true := by rfl

/-- LAW 1's instance (read-after-write): the applied edit's view returns
    the requested row. -/
example : ∀ δ r', vwEditVerdict = ViewEditVerdict.apply δ r' →
    balRow 1 75 ∈ balView.get r' :=
  viewPut_get vwKd balView balCoh vwAccts (balRow 1 75)

/-- LAW 2's instance (unchanged-view preservation): the edit that
    writes back what the view read restores the table exactly. -/
example : viewPut vwKd balView vwAccts
    (vpick accountFields balView.cols vwAcct1)
    = ViewEditVerdict.apply [RowDelta.update vwAcct1] vwAccts :=
  viewPut_preserves vwKd balView balCoh vwAccts vwAcct1 (by decide)
    List.mem_cons_self (by rfl)

/-- The lens at the fixture (the assembled view/update pair). -/
def vwLens : ViewLens vwKd balView := keyedViewLens vwKd balView

/-- The lens's read IS the view's query (one carrier, two names). -/
example : vwLens.get vwAccts = balView.get vwAccts := rfl

/-- The non-key-respecting view: the owner column only (no key). -/
abbrev vwOwnerCol : ViewCol accountFields :=
  { field := { name := "owner", ty := .string }, path := .there .here }
abbrev ownerView : ViewDef accountFields :=
  { name := "owners", cols := [vwOwnerCol] }
def ownerRow (o : String) : RowVals ownerView.vfields := .cons (.string o) .nil
abbrev vwAnns : List (RowVals accountFields) :=
  [vwAcct 1 "ann" 100, vwAcct 3 "ann" 7]

/-- THE AMBIGUITY TEETH: the key-less projection's edit refuses over the
    full-row fiber — TWO base rows read the same view row, and the
    refusal names the count (the aggregate-edit-many-preimages case). -/
example : (viewPut vwKd ownerView vwAnns (ownerRow "ann")).refusal?
    = some (.ambiguous 2) := by rfl

/-- An edit whose key image names no base row refuses, naming the key's
    absence. -/
example : (viewPut vwKd balView vwAccts (balRow 99 0)).refusal?
    = some (.noPreimage ⟨.u64, .u64 99⟩) := by rfl

/-- A violated `uniqueOn` makes the key no longer determine the row —
    the keyed edit refuses with the preimage count. -/
abbrev vwDups : List (RowVals accountFields) :=
  [vwAcct 1 "a" 1, vwAcct 1 "b" 2]
example : (viewPut vwKd balView vwDups (balRow 1 9)).refusal?
    = some (.ambiguous 2) := by rfl

/-- THE DELTA INTEGRATION: the view edit's base delta flows through the
    landed machinery — the post-state is a Db, the violation lane
    decides it. A sound edit keeps the world valid. -/
def vwPost : List (RowVals accountFields) :=
  match vwEditVerdict with
  | .apply _ post => post
  | .refuse _ => []
def vwDb75 : Db := { accounts := vwPost, transfers := [] }
example : (violations vwDb75).isEmpty = true := by rfl

/-- ... and a view edit that drives the balance negative is CAUGHT by
    the violation query — the proposed base delta validates through the
    violation lane where the lanes compose honestly. -/
def vwNegVerdict := viewPut vwKd balView vwAccts (balRow 1 (-5))
def vwNegPost : List (RowVals accountFields) :=
  match vwNegVerdict with
  | .apply _ post => post
  | .refuse _ => []
def vwDbNeg : Db := { accounts := vwNegPost, transfers := [] }
example : (match violations vwDbNeg with
    | [Violation.negative r] => accBal r == (-5 : Int64)
    | _ => false) = true := by rfl

/-- The view suite. -/
def viewSpec : Spec :=
  Spec.ofList "the writable-views lane: the keyed writeback, the lens laws, the named ambiguity"
    (fun _ => assert ((
      -- the worked edit: the delta + the post-state, owner preserved
      (match vwEditVerdict with
        | .apply δ post =>
            δ.length == 1
              && (match δ with
                  | [RowDelta.update w] => rowBeq accountFields w (vwAcct 1 "ann" 75)
                  | _ => false)
              && (match post with
                  | [r1, r2] =>
                      rowBeq accountFields r1 (vwAcct 1 "ann" 75)
                        && rowBeq accountFields r2 vwAcct2
                  | _ => false)
        | _ => false)
      -- read-after-write at the fixture (LAW 1's instance)
      && (match vwEditVerdict with
          | .apply _ post =>
              (balView.get post).any (fun vr => rowBeq _ vr (balRow 1 75))
          | _ => false)
      -- unchanged-view preservation (LAW 2's instance)
      && (match viewPut vwKd balView vwAccts
              (vpick accountFields balView.cols vwAcct1) with
          | .apply δ post =>
              (match δ, post with
                | [RowDelta.update w], [r1, r2] =>
                    rowBeq accountFields w vwAcct1
                      && rowBeq accountFields r1 vwAcct1
                      && rowBeq accountFields r2 vwAcct2
                | _, _ => false)
          | _ => false)
      -- the delta integration: the violation lane decides the post-state
      && ((violations vwDb75).isEmpty)))
      "the view lane drifted")
    [ ("the key-less edit applies", fun _ =>
        assert ((viewPut vwKd ownerView vwAnns (ownerRow "ann")).post?.isSome)
          "control fired: the non-key-respecting projection's edit must \
refuse with the named fiber count — many base preimages")
    , ("the absent-key edit applies", fun _ =>
        assert ((viewPut vwKd balView vwAccts (balRow 99 0)).post?.isSome)
          "control fired: an edit whose key image names no base row must \
refuse (noPreimage)")
    , ("the violated-uniqueness edit applies", fun _ =>
        assert ((viewPut vwKd balView vwDups (balRow 1 9)).post?.isSome)
          "control fired: a violated uniqueOn makes the key no longer \
determine the row — the aggregate-edit-many-preimages refusal")
    , ("the write reaches the complement", fun _ =>
        -- the owner is the complement: the writeback CANNOT touch it
        assert ((match vwEditVerdict with
          | .apply _ post =>
              (match post with
                | [r1, _] => rowBeq accountFields r1 (vwAcct 1 "eve" 75)
                | _ => false)
          | _ => false))
          "control fired: the base retains what the view can't express — \
the owner column survives the writeback (the complement lens)")
    , ("the OLD view row survives the edit", fun _ =>
        assert ((match vwEditVerdict with
          | .apply _ post =>
              (balView.get post).any (fun vr => rowBeq _ vr (balRow 1 100))
          | _ => false))
          "control fired: read-after-write — the requested view REPLACES \
the old row's reading") ]
    4 42

/-! ## The driver -/

/-! ## The functorial deepening (16-surface §4.4) — the ONE walk + the
     ONE generic correctness theorem

The deriving handlers are ALGEBRA VALUES over `Descr` (`DescrAlg` —
one row per ctor + the field-sibling rows), the ONE walk is
`foldDescr`/`foldFields`, and correctness claims are claim ALGEBRAS
discharged by `law_of_rows` — the ONE induction, performed in the
generic theorem, never per-handler. This suite pins: the handlers'
behaviors (the byte faces, unchanged), the fold's kernel-visible
equations, the generic theorem's FRESH exercise (a claim capability
beyond the landed ones, rows only, no induction), and the mandatory
negatives (a wrong claim is refutable — the theorem is not vacuous). -/

-- the handlers' byte faces are the ONE walk's rows (kernel pins)
example : deriveEnc (.product "p" [("x", .prim .u64)]) ((3 : UInt64), ())
    = [3] := rfl
example : deriveEnc (.option (.prim .u64)) (some (7 : UInt64))
    = [1, 7] := rfl
example : deriveDec (.option (.prim .u64)) [1, 7]
    = some ((some (7 : UInt64)), []) := rfl
example : tyOfDescr (.option (.list (.prim .i64)))
    = some (.option (.list .i64)) := by decide

-- the MOUNT byte-tie: the derived codec's bytes ARE the fold's rows
-- (the WireCodec mount rides the ONE walk — nothing parallel)
example : ∀ (r : ExampleRec),
    ExampleRec.codec.encode r
      = deriveEnc ExampleRec.descr (ExampleRec.tupleIso.to r) :=
  fun _ => rfl

-- the INSTANCE CITATIONS: the per-capability theorems are the generic
-- theorem at their claim algebras — no induction of their own
example : deriveCodec_correct = law_of_rows codecCorrectAlg := rfl
example : deriveDec_eq = law_of_rows decEqAlg := rfl
example : ∀ d, tyOfDescr_some d = law_of_rows coherenceAlg d := fun _ => rfl

-- the generic theorem's FRESH EXERCISE: the suffix law (the decoder's
-- remainder IS the appended suffix) as a NEW claim capability — the
-- rows below are the whole proof content (leaf laws + composition,
-- no `deriveCodec_correct` citation), the induction is the generic
-- theorem's (a new handler = data + rows, 16-surface §4.4's
-- "lands when the handlers multiply").
open Kit.Varint in
def suffixAlg :
    DescrAlg
      (P := fun d => ∀ (v : Descr.Ty d) (rest : List UInt8),
        ∃ r, deriveDec d (deriveEnc d v ++ rest) = some (v, r) ∧ r = rest)
      (Q := fun fs => ∀ (v : prodTyOf fs) (rest : List UInt8),
        ∃ r, decProdOf? fs (encProdOf fs v ++ rest) = some (v, r) ∧ r = rest) where
  prim t := fun v rest => ⟨rest, decNat?_encNat_append t v rest, rfl⟩
  option d ih := by
    intro v rest
    cases v with
    | none =>
        exact ⟨rest, by simp [deriveEnc_option, deriveDec_option, decByte?_cons],
          rfl⟩
    | some x =>
        obtain ⟨r, h1, h2⟩ := ih x rest
        refine ⟨rest, ?_, rfl⟩
        simp [deriveEnc_option, deriveDec_option, decByte?_cons, h1, h2]
  list d ih := by
    have hSome : ∀ (a : Descr.Ty d) (rest : List UInt8),
        deriveDec d (deriveEnc d a ++ rest) = some (a, rest) := by
      intro a rest
      obtain ⟨r, h1, h2⟩ := ih a rest
      subst h2
      exact h1
    intro v rest
    cases v with
    | nil =>
        refine ⟨rest, ?_, rfl⟩
        simp [deriveEnc_list, deriveDec_list, encList,
          decVarNat?_encVarNat_append, decManyBind?]
    | cons x xs =>
        refine ⟨rest, ?_, rfl⟩
        simp only [deriveEnc_list, deriveDec_list, encList, List.append_assoc,
          decVarNat?_encVarNat_append,
          decManyBind?_enc_append (deriveDec d) (deriveEnc d) hSome]
  product _ _ ih := ih
  pnil := by
    intro v rest
    cases v
    exact ⟨rest, by simp [decProdOf?_nil, encProdOf_nil], rfl⟩
  pcons fn d fs ih ihF := by
    intro v rest
    obtain ⟨x, xs⟩ := v
    have hSome : ∀ (a : Descr.Ty d) (rest : List UInt8),
        deriveDec d (deriveEnc d a ++ rest) = some (a, rest) := by
      intro a rest
      obtain ⟨r, h1, h2⟩ := ih a rest
      subst h2
      exact h1
    have hSomeF : ∀ (w : prodTyOf fs) (rest : List UInt8),
        decProdOf? fs (encProdOf fs w ++ rest) = some (w, rest) := by
      intro w rest
      obtain ⟨r, h1, h2⟩ := ihF w rest
      subst h2
      exact h1
    refine ⟨rest, ?_, rfl⟩
    rw [encProdOf_cons, List.append_assoc, decProdOf?_cons,
      hSome x (encProdOf fs xs ++ rest)]
    simp only [Option.bind_some, hSomeF xs rest]
    rfl

/-- The fresh capability, discharged: the suffix law at EVERY
    description, by the ONE induction. -/
theorem deriveSuffix_law (d : Descr) (v : Descr.Ty d) (rest : List UInt8) :
    ∃ r, deriveDec d (deriveEnc d v ++ rest) = some (v, r) ∧ r = rest :=
  law_of_rows suffixAlg d v rest

/-- THE NEGATIVE (the theorem-not-vacuous control): the WRONG claim —
    the suffix dropped — is refutable; a claim algebra with a false
    row cannot discharge. -/
theorem wrongSuffixClaim_refuted : ¬ (∀ (v : UInt64) (rest : List UInt8),
    (decNat? .u64 (encNat .u64 v ++ rest)).map (·.2) = some []) := by
  intro h
  exact absurd (h 300 [7]) (by decide)

/-- The deepening's suite: the one walk + the one generic theorem's
    faces, with the wrong-claim negative. -/
def deepeningSpec : Spec :=
  Spec.ofList "the functorial deepening: the ONE walk, the ONE theorem"
    (fun _ => do
      -- the fresh capability's runtime face (the rows are live)
      assert ((match deriveDec (.list (.prim .u64))
        (deriveEnc (.list (.prim .u64)) [1, 2] ++ [9]) with
        | some p => p.2 == [9]
        | none => false))
        "deepening.suffixLaw")
    [ ("sabotage: the suffix law drops the suffix",
        fun _ =>
          assert ((match decNat? .u64 (encNat .u64 300 ++ [7]) with
            | some p => p.2 == []
            | none => true))
            "control fired: the suffix survived — the wrong claim is \
              refutable, the generic theorem is not vacuous")
    , ("sabotage: the decoder accepts a bad tag",
        fun _ =>
          assert ((match deriveDec (.option (.prim .u64)) [2] with
            | none => false
            | some _ => true))
            "control fired: the decoder decoded the unknown tag") ]
    4 42

def main : IO UInt32 :=
  TestingKit.mainOfSuites
    [ ("SchemaCore.Ty", [tyRenderSpec, losslessSpec])
    , ("SchemaCore.Fold", [foldSpec])
    , ("SchemaCore.Value", [valueSpec])
    , ("SchemaCore.Codec", [codecGoldenSpec, codecRoundTripSpec, codecRefusalSpec])
    , ("SchemaCore.Emit", [artifactSpec, lawSpec])
    , ("SchemaCore.Item", [registrySpec, obligationSpec])
    , ("SchemaCore.RowVals", [rowSpec])
    , ("SchemaCore.Derive", [deriveSpec])
    , ("SchemaCore.DeriveMeta entourage", [entourageSpec])
    , ("SchemaCore.Snapshot", [snapshotSpec])
    , ("SchemaCore.Describe", [describeSpec])
    , ("SchemaCore.Derive deepening", [deepeningSpec])
    , ("SchemaCore.Pred", [predSpec])
    , ("SchemaCore.Check", [checkSpec])
    , ("SchemaCore.Keys", [keysSpec])
    , ("SchemaCore.Update", [updateSpec])
    , ("SchemaCore.View", [viewSpec])
    , ("SchemaCore.EventSourced", [eventSourcedSpec, esCodecSpec, esMigrationSpec])
    , ("SchemaCore.Migrate", [migrateSpec, migrateRefusalSpec])
    , ("SchemaCore.Profile", [profilePinSpec, profileSpec])
    , ("SchemaCore.EntityMachine", [entityMachineSpec])
    , ("SchemaCore.Diff", [diffSpec, verdictSpec, remedySpec])
    , ("SchemaCore.Violate+Commit", [commitFaceSpec, refuseFaceSpec,
        staleFaceSpec, duelSpec])
    , ("SchemaCore.IncViolate", [incSpec, incFallbackSpec])
    , ("SchemaCore.Confluence", [confluenceSpec]) ]

/-! ## The Rust lane (SchemaCore.Emit.Rust) — the differential's Lean side

The differential vectors are COMPUTED by the emitter through
SchemaCore.Codec's `encVal` (one source; the committed bytes are the
writer's output, byte-tied by gen-check). These kernel pins tie the
pinned bytes to the wire contract's own known-answer shapes; the Rust
half (crates/schema-generated/tests/differential.rs, generated)
decodes the committed vectors, re-encodes byte-identically (BOTH
directions), and the tamper vectors REFUSE (typed `CodecError`, no
panic) — notes/v3/03 §3's differential level, the correspondence row
of 01 §6. -/

/-- The full Example row's bytes: the fixture's fields in schema order
    (ready/count/delta/label/note/tags), each field's `encVal` bytes
    concatenated — the contract the generated `Example::encode` must
    reproduce byte-for-byte. -/
example : SchemaCore.Emit.Rust.goldenExample =
  [1, 172, 2, 1, 2, 104, 105, 1, 4, 110, 111, 116, 101, 2, 1, 97, 1, 98] :=
  rfl

/-- The record row's table carries exactly that row (the writer of the
    committed bytes). -/
example : (SchemaCore.Emit.Rust.rowGoldens.getLast!).2
    = SchemaCore.Emit.Rust.goldenExample := rfl

/-- The atom rows' bytes are the wire's own known-answer shapes. -/
example : (SchemaCore.Emit.Rust.atomGoldens.map (·.2.2))
    = [ [0], [1], [0xAC, 0x02], [1], [2], [2, 104, 105] ] := rfl

/-- THE NEGATIVE CONTROL's fixture: three refusals, computed from the
    golden row (truncation, bad bool tag, non-canonical varint). -/
example : SchemaCore.Emit.Rust.tamperVectors.length = 3 := rfl
example : (SchemaCore.Emit.Rust.tamperVectors.map (·.1))
    = ["truncated", "bad_bool_tag", "non_canonical_count"] := rfl

/-- The two emitters' outputs are disjoint (the cross-emitter
    one-writer audit, data level — 12 §3's global ownership rule). -/
example : Kit.Emit.outputsDisjoint
    [SchemaCore.witEmitter, SchemaCore.Emit.Rust.rustEmitter] = true := by
  decide

/-- THE DUEL VECTOR SET (the duel migration's pins): ten vectors —
    six atoms + the example row + three refusals — all `encVal`'s
    bytes, the ONE source. -/
example : SchemaCore.Emit.Rust.duelVectors.vectors.length = 10 := rfl

/-- The manifest's expectations cover exactly the emitted vectors
    (Kit.Duel's shape check — a manifest row over an absent vector is
    a generator bug, and the pin makes it a test verdict). -/
example : Kit.Duel.expectsCovered SchemaCore.Emit.Rust.duelVectors = true := rfl

/-! ### The JOURNAL DUEL's pins (SchemaCore.Emit.Journal — the Event
    lane's vector set over the mandate-delta crate's documented
    encR/encK instantiation) -/

/-- THE JOURNAL DUEL VECTOR SET: nine vectors — five goldens (the
    frames + the journals, the LANDED journal codec's bytes through
    `SchemaCore.Emit.Journal.encDeltaJ`/`encJournalJ`) + four refusal
    splices — never hand-composed. -/
example : SchemaCore.Emit.Journal.journalDuel.vectors.length = 9 := rfl

/-- The manifest's expectations cover exactly the emitted vectors
    (Kit.Duel's shape check, duel-shaped). -/
example : Kit.Duel.expectsCovered SchemaCore.Emit.Journal.journalDuel = true := rfl

/-- The golden bytes are the kernel's: varint(3) + the three frames,
    every atom a Codec.lean known-answer pin (u64 300 = AC 02;
    "hi" = 02 68 69; "ho" = 02 68 6F; the tags in ctor order 0/1/2). -/
example : SchemaCore.Emit.Journal.goldenJournalThree
    = [3, 0, 2, 0xAC, 0x02, 2, 104, 105,
       1, 2, 0xAC, 0x02, 2, 104, 111, 2, 0xAC, 0x02] := rfl

/-- The frame goldens: the tag bytes + the self-delimiting payloads. -/
example : SchemaCore.Emit.Journal.goldenFrameInsert
    = [0, 2, 0xAC, 0x02, 2, 104, 105] := rfl
example : SchemaCore.Emit.Journal.goldenFrameUpdate
    = [1, 2, 0xAC, 0x02, 2, 104, 105] := rfl
example : SchemaCore.Emit.Journal.goldenFrameRemove = [2, 0xAC, 0x02] := rfl
example : SchemaCore.Emit.Journal.goldenJournalEmpty = [0] := rfl

/-- THE NEGATIVE CONTROL's bytes: each splice is the out-of-policy
    shape its name claims (tag outside the ctor image / a torn tail /
    the non-canonical varint / the arity-skewed count). -/
example : SchemaCore.Emit.Journal.refuseUnknownTag
    = [1, 3, 2, 0xAC, 0x02, 2, 104, 105] := rfl
example : SchemaCore.Emit.Journal.refuseTruncatedFrame
    = [3, 0, 2, 0xAC, 0x02, 2, 104, 105, 1, 2, 0xAC, 0x02, 2, 104,
       111, 2, 0xAC] := rfl
example : SchemaCore.Emit.Journal.refuseNoncanonicalKey
    = [2, 0x80, 0x00] := rfl
example : SchemaCore.Emit.Journal.refuseRowCountSkew
    = [0, 3, 0xAC, 0x02, 2, 104, 105] := rfl

/-- NEGATIVE CONTROL (the shape check fires): a manifest row over an
    ABSENT vector fails `expectsCovered` — a generator bug cannot hide
    behind the coverage pin. -/
example : Kit.Duel.expectsCovered
    { SchemaCore.Emit.Journal.journalDuel with
      expects := [("crates/mandate-delta/tests/duel/absent.bin", .refuse)]
      expects_nodup := by decide }
    = false := rfl
