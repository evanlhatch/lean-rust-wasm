/-
# SchemaTests — the slice's test exe (TestKit the whole way)

Per the slice: positive pins + the MANDATORY negative controls
(15-patterns #5 — each Spec's sabotages must FAIL or the verdict is
`.vacuous`, louder than failing). Suites:

1. `Ty` — the closed universe's rendering (every ctor's live witness).
2. The emitter — the artifact body is a GOLDEN PIN (a literal), plus
   the byte-tie's teeth at the value level (TestKit.Golden).
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

import TestKit.Harness
import TestKit.Golden
import SchemaCore
import SchemaCore.Slice
import SchemaCore.CheckSlice
import SchemaTests.Axioms

open Kit SchemaCore TestKit

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
  "package macht:slice;\n\ninterface items {\n" ++
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

/-! ## The record↔row bridge (the `@[row_bridge]` shape, hand on the fixture —
    GenKit generates this per record when it lands; the SHAPE is the mined
    `Meta/RowIso.lean` discipline: toRow/ofRow + BOTH round-trip laws + the
    ONE `Kit.Iso`) -/

/-- The native record mirror of the Example fixture (the bridge's
    native side). -/
structure ExampleRec where
  ready : Bool
  count : UInt64
  delta : Int64
  label : String
  note : Option String
  tags : List String
deriving Repr, BEq, Inhabited

/-- `List String → VList .string` (the fixture's box half; the generic
    `List (Value t)` pair is the generated harness's work). -/
def exToVList : List String → VList .string
  | [] => .nil
  | x :: xs => .cons (.string x) (exToVList xs)

/-- The unbox half of `exToVList`. -/
def exOfVList : VList .string → List String
  | .nil => []
  | .cons (.string x) xs => x :: exOfVList xs

/-- The cons equation of `exOfVList` (the GADT matcher is
    kernel-opaque to `rfl` — the 06 §2 wf-opacity sibling — but the
    EQUATIONS fire under simp on ctor values; §5). -/
theorem exOfVList_cons (x : String) (xs : VList .string) :
    exOfVList (.cons (.string x) xs) = x :: exOfVList xs := by
  simp [exOfVList]

/-- Native → row (one `.cons` per field, boxed per its schema type). -/
def exampleToRow : ExampleRec → RowVals exampleCheckFields
  | ⟨r, c, d, l, n, t⟩ =>
      .cons (.bool r) (.cons (.u64 c) (.cons (.i64 d) (.cons (.string l)
        (.cons (match n with
                | some s => .some (.string s)
                | none => .none)
          (.cons (.list (exToVList t)) .nil)))))

/-- Row → native (one `.cons` level per field, unboxed; the note field
    splits on the `Value` ctor — the option's payload is a `Value`). -/
def exampleOfRow : RowVals exampleCheckFields → ExampleRec
  | .cons (.bool r) (.cons (.u64 c) (.cons (.i64 d) (.cons (.string l)
      (.cons (.some (.string s)) (.cons (.list vs) .nil))))) =>
      ⟨r, c, d, l, some s, exOfVList vs⟩
  | .cons (.bool r) (.cons (.u64 c) (.cons (.i64 d) (.cons (.string l)
      (.cons .none (.cons (.list vs) .nil))))) =>
      ⟨r, c, d, l, none, exOfVList vs⟩

/-- The list payload's round trip (the row-side law's helper — the
    cons case recurses; structural). -/
theorem exToOfVList : ∀ (vs : VList .string), exToVList (exOfVList vs) = vs := by
  intro vs
  match vs with
  | .nil => simp [exOfVList, exToVList]
  | .cons h xs =>
      cases h with
      | string s =>
          rw [exOfVList_cons]
          show VList.cons (.string s) (exToVList (exOfVList xs))
            = VList.cons (.string s) xs
          rw [exToOfVList xs]

/-- The record-side law's helper: the native list round trip (the
    easy direction — structural over the native list). -/
theorem exOfToVList : ∀ (xs : List String), exOfVList (exToVList xs) = xs
  | [] => by simp [exToVList, exOfVList]
  | x :: xs => by simp [exToVList, exOfVList_cons, exOfToVList xs]

/-- LAW: `exampleToRow (exampleOfRow row) = row` — the row side (the
    nested match; each `Value` ctor's projection is total; the tags
    payload rides the list round trip). -/
theorem exampleToRow_ofRow (row : RowVals exampleCheckFields) :
    exampleToRow (exampleOfRow row) = row := by
  cases row with
  | cons a as =>
      cases a with
      | bool r =>
          cases as with
          | cons b bs =>
              cases b with
              | u64 c =>
                  cases bs with
                  | cons d ds =>
                      cases d with
                      | i64 e =>
                          cases ds with
                          | cons g gs =>
                              cases g with
                              | string l =>
                                  cases gs with
                                  | cons h hs =>
                                      cases hs with
                                      | cons f fs =>
                                          cases fs with
                                          | nil =>
                                              cases f with
                                              | list vs =>
                                                  cases h with
                                                  | none =>
                                                      show (RowVals.cons (.bool r)
                                                        (.cons (.u64 c)
                                                        (.cons (.i64 e)
                                                        (.cons (.string l)
                                                        (.cons .none
                                                        (.cons (.list (exToVList (exOfVList vs))) .nil))))) : RowVals exampleCheckFields)
                                                        = RowVals.cons (.bool r)
                                                        (.cons (.u64 c)
                                                        (.cons (.i64 e)
                                                        (.cons (.string l)
                                                        (.cons .none
                                                        (.cons (.list vs) .nil)))))
                                                      rw [exToOfVList]
                                                  | some v =>
                                                      cases v with
                                                      | string s =>
                                                          show (RowVals.cons (.bool r)
                                                            (.cons (.u64 c)
                                                            (.cons (.i64 e)
                                                            (.cons (.string l)
                                                            (.cons (.some (.string s))
                                                            (.cons (.list (exToVList (exOfVList vs))) .nil))))): RowVals exampleCheckFields)
                                                            = RowVals.cons (.bool r)
                                                            (.cons (.u64 c)
                                                            (.cons (.i64 e)
                                                            (.cons (.string l)
                                                            (.cons (.some (.string s))
                                                            (.cons (.list vs) .nil)))))
                                                          rw [exToOfVList]

/-- LAW: `exampleOfRow (exampleToRow r) = r` — the record side (each
    field is a projection; the `show` exposes the reduced form, the
    list round trip rewrites). -/
theorem exampleOfRow_toRow (r : ExampleRec) :
    exampleOfRow (exampleToRow r) = r := by
  cases r with
  | mk ready count delta label note tags =>
      cases note with
      | none =>
          show ExampleRec.mk ready count delta label none
              (exOfVList (exToVList tags))
            = ExampleRec.mk ready count delta label none tags
          rw [exOfToVList tags]
      | some s =>
          show ExampleRec.mk ready count delta label (some s)
              (exOfVList (exToVList tags))
            = ExampleRec.mk ready count delta label (some s) tags
          rw [exOfToVList tags]

/-- THE ROW ISO — `Kit.Iso ExampleRec (RowVals exampleCheckFields)`: every lane's
    row bridge projects its fields (the correspondence preference: a
    TRUE Iso — the row side is total because `RowVals` admits only
    well-formed rows). -/
def exampleRowIso : Kit.Iso ExampleRec (RowVals exampleCheckFields) :=
  ⟨exampleToRow, exampleOfRow, exampleToRow_ofRow, exampleOfRow_toRow⟩

/-- The Example fixture's field-name list (the name↔index iso's
    domain; nodup decided — the determinacy content, 02 §3). -/
def exFieldNames : List String := exampleCheckFields.map (·.name)

theorem exFieldNames_nodup : exFieldNames.Nodup := by decide

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
      let d : Discharged (List String) :=
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
      let row := exampleToRow r
      let iso := fieldIndexIso exFieldNames_nodup
      assert (
      -- the Iso laws, live: the record side on concrete data (the ROW
      -- side is the PROVED law — `RowVals` carries no BEq; the theorem
      -- `exampleToRow_ofRow` is the pin)
        (exampleOfRow row == r)
        && (exampleOfRow
              (exampleToRow ⟨false, 0, 1, "b", none, []⟩)
              == ⟨false, 0, 1, "b", none, []⟩)
      -- the name-keyed projection: first match, typed hit, loud miss
        && (match RowVals.project? exampleCheckFields row "label" with
            | some fv => match fv.ty with | .string => true | _ => false
            | none => false)
        && (RowVals.project? exampleCheckFields row "nope").isNone
      -- the name↔index iso: both round trips over the fixture's names
        && ((iso.to ⟨1, by decide⟩).1 == "count")
        && ((iso.inv ⟨"count", by simp [exFieldNames]⟩).1 == 1)
        && ((iso.to (iso.inv ⟨"count", by simp [exFieldNames]⟩)).1
              == "count"))
      "the row layer drifted")
    [ ("projection fabricates a miss",
        fun _ =>
          let r : ExampleRec := ⟨true, 3, -2, "a", some "n", ["t1", "t2"]⟩
          assert ((RowVals.project? exampleCheckFields (exampleToRow r) "nope").isSome)
            "control: a missing field name must project to none")
    , ("round trip forgets the note",
        fun _ =>
          let r : ExampleRec := ⟨true, 3, -2, "a", some "n", ["t1", "t2"]⟩
          assert (exampleOfRow (exampleToRow r)
            == { r with note := none })
          "control: the bridge must carry the option payload faithfully")
    , ("index iso maps to the wrong name",
        fun _ =>
          let iso := fieldIndexIso exFieldNames_nodup
          assert ((iso.to ⟨1, by decide⟩).1 == "ready")
          "control: position 1's name is count, not ready") ]
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
      -- the item's shape: label, computed tier, payload
        && (exampleCountPositive.obligation.label
              == "schema/Example/example-count-positive")
        && (exampleCountPositive.obligation.tier == .decidableNow)
        && (exampleCountPositive.obligation.payload
              == exampleCheckFields.map (·.name))
      -- the mixed table: the check refuses; the violating rows ride
        && (exampleCountPositive.checkOn mixedRows == false)
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
          assert (exampleCountPositive.checkOn [foreignRow] == true)
          "control fired: a table for ANOTHER schema must refuse, never misread")
    , ("discharge fabricates evidence",
        fun _ =>
          assert (exampleCountZero.dischargeOn mixedRows == some (.decided true))
          "control fired: a violated claim must be the LOUD none")
    , ("tier mis-wire passes silently",
        fun _ =>
          assert (¬(Kit.tierMismatch exampleCountPositive.obligation
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

/-! ## The driver -/

def main : IO UInt32 :=
  TestKit.mainOfSuites
    [ ("SchemaCore.Ty", [tyRenderSpec, losslessSpec])
    , ("SchemaCore.Value", [valueSpec])
    , ("SchemaCore.Codec", [codecGoldenSpec, codecRoundTripSpec, codecRefusalSpec])
    , ("SchemaCore.Emit", [artifactSpec, lawSpec])
    , ("SchemaCore.Item", [registrySpec, obligationSpec])
    , ("SchemaCore.RowVals", [rowSpec])
    , ("SchemaCore.Snapshot", [snapshotSpec])
    , ("SchemaCore.Describe", [describeSpec])
    , ("SchemaCore.Pred", [predSpec])
    , ("SchemaCore.Check", [checkSpec]) ]

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
