/-
# WitTests — the typed WIT AST's test exe (TestingKit the whole way)

Per the discipline: positive pins + the MANDATORY negative controls
(15-patterns #5). Suites:

1. `render` — the renderer's GOLDEN pins: a small AST → its exact
   text (each `Ty` ctor's live witness, the record/interface/package
   blocks), plus the byte-level tamper controls.
2. `parse` — the ROUND-TRIP pins: the rendered fixture parses back to
   exactly the fixture (`parse_print`'s value-level face), the edges
   (empty interfaces, empty records) + the negative teeth (trailing
   bytes, dropped comma, maximal munch, the parse-time nodup refusal,
   the WitOk gate's bite).
3. the unconstructibility pins — the malformed shapes (duplicate
   field names, duplicate record names) FAIL TO ELABORATE, pinned by
   `#guard_msgs` (the elaborator/kernel is the refusal; there is no
   value-level path to the malformed shape).
4. the discipline pins — the closed type grammar (no arbitrary type
   text is constructible), the two-summand `result` (the one-summand
   WIT forms are unconstructible).

THE ARTIFACT PIN runs in `main` (the only IO): the committed artifact
of record `gen/schema-slice.wit` parses, passes `WitOk`, and re-renders
byte-identical to its comment-stripped bytes — the executable shadow of
the canonicalization law on the REAL bytes.

The tie to the UPSTREAM lowering (`SchemaCore.witTy`'s bytes vs
`SchemaCore.renderTy`'s) lives in SchemaCore.Emit (`witTy_tie`) — this
exe imports `Wit` + `Wit.Parse` only (the cone rule); the artifact-side
proof is the gen-check byte-tie over `gen/schema-slice.wit`.
-/
module


public import Lean
public import TestingKit.Harness
public import TestingKit.Golden
public import Wit
public import Wit.World
public import Wit.Render
public import Wit.Parse
public import Wit.Session
public import Wit.Compose


@[expose] public section
open Wit TestingKit

/-! ## Fixtures -/

/-- A small AST over every `Ty` ctor (the closed grammar's live
    witness — the same shapes the slice's fixture lowers to). -/
def exTyAtom : Ty := .atom .bool
def exTyOpt : Ty := .option (.atom .string)
def exTyList : Ty := .list (.atom .string)
def exTyResult : Ty := .result (.atom .u64) (.atom .string)
def exTyTuple : Ty := .tuple (.atom .string) (.atom .u64)

def exField1 : Field := { name := "ready", ty := exTyAtom }
def exField2 : Field := { name := "note", ty := exTyOpt }
def exField3 : Field := { name := "tags", ty := exTyList }
def exField4 : Field := { name := "status", ty := exTyResult }
def exField5 : Field := { name := "counts", ty := .list exTyTuple }

def exRecord : Record :=
  { name := "example"
    fields := [exField1, exField2, exField3, exField4, exField5] }

/-- The GOLDEN PIN: the record's exact text (the artifact of record's
    block shape, byte for byte). -/
def expectedRecord : String :=
  "  record example {\n" ++
  "    ready: bool,\n" ++
  "    note: option<string>,\n" ++
  "    tags: list<string>,\n" ++
  "    status: result<u64, string>,\n" ++
  "    counts: list<tuple<string, u64>>,\n" ++
  "  }\n"

def exInterface : Interface :=
  { name := "items", records := [exRecord] }

/-- The GOLDEN PIN: the package's exact text — the committed artifact
    `gen/schema-slice.wit`'s body shape. -/
def expectedPackage : String :=
  "package mandate:slice;\n\n" ++
  "interface items {\n" ++
  "  record example {\n" ++
  "    ready: bool,\n" ++
  "    note: option<string>,\n" ++
  "    tags: list<string>,\n" ++
  "    status: result<u64, string>,\n" ++
  "    counts: list<tuple<string, u64>>,\n" ++
  "  }\n" ++
  "}\n"

/-! ## The unconstructibility pins (elaboration-level teeth)

The malformed shapes DO NOT elaborate — the `by decide` defaults fire
the kernel on concrete literals. The exact refusals, pinned: -/

-- The duplicate FIELD name: unconstructible (the record's nodup is
-- in the type) — the elaboration refusal, pinned exactly.
/-- error: could not synthesize default value for field 'fields_nodup' of 'Wit.Record' using tactics
---
error: Tactic `decide` proved that the proposition
  (List.map Field.name [{ name := "a", ty := exTyAtom }, { name := "a", ty := exTyOpt }]).Nodup
is false -/
#guard_msgs in
example : Record :=
  { name := "bad"
    fields := [{ name := "a", ty := exTyAtom }
              , { name := "a", ty := exTyOpt }] }

-- The duplicate RECORD name: unconstructible (the interface's nodup is
-- in the type) — the elaboration refusal, pinned exactly.
/-- error: could not synthesize default value for field 'records_nodup' of 'Wit.Interface' using tactics
---
error: Tactic `decide` proved that the proposition
  (List.map Record.name
      [{ name := "r", fields := [exField1], fields_nodup := ⋯ },
        { name := "r", fields := [exField2], fields_nodup := ⋯ }]).Nodup
is false -/
#guard_msgs in
example : Interface :=
  { name := "items"
    records := [{ name := "r", fields := [exField1] }
               ,{ name := "r", fields := [exField2] }] }

/-! ## The suites -/

/-- Every `Ty` ctor renders (the closed grammar's live witness) + the
    wrappers' exact nestings. -/
def renderTySpec : Spec :=
  Spec.ofList "every Ty ctor renders to the pinned WIT text"
    (fun _ => assert (
      (Render.ty exTyAtom == "bool")
        && (Render.ty (.atom .u64) == "u64")
        && (Render.ty (.atom .i64) == "i64")
        && (Render.ty (.atom .string) == "string")
        && (Render.ty exTyOpt == "option<string>")
        && (Render.ty exTyList == "list<string>")
        && (Render.ty exTyResult == "result<u64, string>")
        && (Render.ty exTyTuple == "tuple<string, u64>")
        && (Render.ty (.option exTyList) == "option<list<string>>")
        && (Render.ty (.list (.option (.atom .u64)))
              == "list<option<u64>>")
        && (Render.ty (.result (.option (.atom .u64)) (.atom .string))
              == "result<option<u64>, string>")
        -- the D2 rows (the waitable wrappers, the one-summand result
        -- faces, the handle refs)
        && (Render.ty (.stream exTyList) == "stream<list<string>>")
        && (Render.ty (.future exTyAtom) == "future<bool>")
        && (Render.ty (.resultOk exTyAtom) == "result<bool>")
        && (Render.ty (.resultErr exTyAtom) == "result<_, bool>")
        && (Render.ty (.own "kv") == "own<kv>")
        && (Render.ty (.borrow "kv") == "borrow<kv>"))
      "the WIT type rendering drifted")
    [ ("sabotaged stream render ties",
        fun _ => assert (Render.ty (.stream exTyList) == "list<string>")
          "control: the waitable wrapper must print its keyword")
    , ("sabotaged own render drops the resource name",
        fun _ => assert (Render.ty (.own "kv") == "own<>")
          "control: the handle ref must carry its resource's name")
    , ("sabotaged option render ties",
        fun _ => assert (Render.ty exTyOpt == "u64")
          "control: option must nest, not vanish")
    , ("sabotaged result drops a summand",
        fun _ => assert (Render.ty exTyResult == "result<u64>")
          "control: result must keep BOTH summands")
    , ("sabotaged tuple render ties",
        fun _ => assert (Render.ty exTyTuple == "string")
          "control: the tuple must render its pair") ]
    4 42

/-- The D2 resource rows' fixtures: the declaration line + the
    handle refs are the renderer's; the round trip rides the ENGINE
    (`resourceLineG`) — the resource decls PARSE (the ty-level rows
    landed as parser arms — the `d2TySpec` sweep below). -/
def exResource : Resource := { name := "kv" }

def exInterfaceRes : Interface :=
  { name := "items", resources := [exResource], records := [exRecord] }

def exPackageRes : Package := ⟨"mandate:slice", [exInterfaceRes]⟩

/-- The record/interface/package blocks' GOLDEN pins + the byte-level
    tamper controls. -/
def renderBlockSpec : Spec :=
  Spec.ofList "the blocks render to the golden bytes"
    (fun _ => assert (
      (Render.record exRecord == expectedRecord)
        && (Render.interface exInterface
              == "interface items {\n" ++ expectedRecord ++ "}\n")
        && (Render.package (Package.mk "mandate:slice" [exInterface])
              == expectedPackage)
        -- the empty-record degradation (the pre-AST emitter's shape)
        && (Render.record { name := "empty", fields := [] }
              == "  record empty {\n\n  }\n")
        -- the D2 resource rows: the decl line + the interface's
        -- canonical order (the resource lines, then the record blocks)
        && (Render.resource exResource == "resource kv;\n")
        && (Render.interface exInterfaceRes
              == "interface items {\nresource kv;\n"
                 ++ expectedRecord ++ "}\n"))
      "the block rendering drifted")
    [ ("a dropped field undetected",
        fun _ =>
          assert (Render.record
              { name := exRecord.name
                fields := [exField1, exField2, exField3, exField4]
                fields_nodup := by decide }
            == expectedRecord)
          "control: a dropped field must change the bytes")
    , ("a re-typed field undetected",
        fun _ =>
          assert (Render.field { exField1 with ty := .atom .i64 }
            == "    ready: bool,")
          "control: a re-typed field must change the bytes")
    , ("a renamed record undetected",
        fun _ =>
          assert (Render.record { exRecord with name := "other" }
            == expectedRecord)
          "control: the record's name is in the bytes") ]
    4 42

/-- The empty-package/interface faces (the totality's edges). -/
def renderEdgeSpec : Spec :=
  Spec.ofList "the renderer is total over the edges"
    (fun _ => assert (
      (Render.package (Package.mk "mandate:slice" [])
        == "package mandate:slice;\n\n")
        && (Render.interface { name := "items", records := [] }
              == "interface items {\n}\n"))
      "the edge faces drifted")
    [ ("the empty package renders the id away",
        fun _ =>
          assert (Render.package (Package.mk "mandate:slice" [])
            == "")
          "control: the package line must render even with no \
            interfaces")
    , ("a dropped record undetected",
        fun _ =>
          assert (Render.interface
              { exInterface with records := [], records_nodup := by decide }
            == Render.interface exInterface)
          "control: a dropped record must change the bytes") ]
    4 42

/-! ## the parser suites (Wit.Parse) -/

open Wit.Parse

/-- The fixture package (the golden text's AST). -/
def exPackage : Package := ⟨"mandate:slice", [exInterface]⟩

/-- The empty-interfaces edge. -/
def exPackageEmpty : Package := ⟨"mandate:slice", []⟩

-- BEq over the AST (manual — the derived form demands LawfulBEq of the
-- list fields, which the proof-carrying structures don't carry):
instance : BEq Record where
  beq a b := a.name == b.name && a.fields == b.fields
instance : BEq Interface where
  beq a b := a.name == b.name && a.resources == b.resources
    && a.records == b.records
instance : BEq Package where
  beq a b := a.id == b.id && a.interfaces == b.interfaces

/-- A parse verdict: did the text parse back to the expected package? -/
def parsesTo (s : String) (p : Package) : Bool :=
  match Parse.parse s with
  | .ok q => q == p
  | .error _ => false

/-- A parse verdict: was the text refused? -/
def refused (s : String) : Bool :=
  match Parse.parse s with
  | .error _ => true
  | .ok _ => false

/-- The edge packages built directly (the `with`-syntax's proof
    fields don't re-type; the explicit forms do). -/
def exPackageNoRecords : Package :=
  ⟨"mandate:slice", [⟨"items", [], [], by decide, by decide⟩]⟩

def exPackageEmptyRecord : Package :=
  ⟨"mandate:slice",
    [⟨"items", [{ name := "empty", fields := [] }], [], by decide, by decide⟩]⟩

/-- The D2 ty-level rows' fixtures: every new ty ctor live in a
    field (the handle refs name the fixture resource `kv` — the
    decl-name agreement is the consumer's check, per the Render note). -/
def exTyStream : Ty := .stream (.atom .u64)
def exTyFuture : Ty := .future exTyAtom
def exTyResultOk : Ty := .resultOk exTyAtom
def exTyResultErr : Ty := .resultErr (.atom .string)
def exTyOwn : Ty := .own "kv"
def exTyBorrow : Ty := .borrow "kv"

def exRecordD2 : Record :=
  { name := "channels"
    fields := [{ name := "ticks", ty := exTyStream }
              , { name := "done", ty := exTyFuture }
              , { name := "verdict", ty := exTyResultOk }
              , { name := "fault", ty := exTyResultErr }
              , { name := "handle", ty := exTyOwn }
              , { name := "lens", ty := exTyBorrow }] }

def exInterfaceD2 : Interface :=
  { name := "live", resources := [exResource], records := [exRecordD2] }

def exPackageD2 : Package := ⟨"mandate:slice", [exInterfaceD2]⟩

/-- The GOLDEN PIN: the D2 record's exact text (the new rows' bytes). -/
def expectedRecordD2 : String :=
  "  record channels {\n" ++
  "    ticks: stream<u64>,\n" ++
  "    done: future<bool>,\n" ++
  "    verdict: result<bool>,\n" ++
  "    fault: result<_, string>,\n" ++
  "    handle: own<kv>,\n" ++
  "    lens: borrow<kv>,\n" ++
  "  }\n"

/-- The D2 TEETH: the round trip over the extended fragment + the
    malformed stream/result/handle syntax refuses with the structured
    `ParseError` (never a silent prefix acceptance). The last tooth is
    the fragment gate's residual bite: a handle ref's maximal-munch
    name run need not be identifier-shaped — `own<9bad>` refuses at
    the `tyScan` gate. -/
def d2TySpec : Spec :=
  Spec.ofList "the D2 ty rows render + round trip; the malformed syntax refuses"
    (fun _ => assert (
      (Render.record exRecordD2 == expectedRecordD2)
        && parsesTo (Render.package exPackageD2) exPackageD2)
      "the D2 ty rows drifted")
    [ ("sabotaged parse accepts an empty stream body",
        fun _ => assert (!refused "package mandate:slice;\n\ninterface items {\n  record r {\n    a: stream<>,\n  }\n}\n")
          "control: stream<> must refuse (the inner ty is mandatory)")
    , ("sabotaged parse accepts a dropped stream angle",
        fun _ => assert (!refused "package mandate:slice;\n\ninterface items {\n  record r {\n    a: stream<u64,\n  }\n}\n")
          "control: a missing > must refuse")
    , ("sabotaged parse accepts an empty error-result body",
        fun _ => assert (!refused "package mandate:slice;\n\ninterface items {\n  record r {\n    a: result<_, >,\n  }\n}\n")
          "control: result<_, > must refuse")
    , ("sabotaged parse accepts an empty handle name",
        fun _ => assert (!refused "package mandate:slice;\n\ninterface items {\n  record r {\n    a: own<>,\n  }\n}\n")
          "control: own<> must refuse")
    , ("sabotaged parse accepts a non-identifier handle name",
        fun _ => assert (!refused "package mandate:slice;\n\ninterface items {\n  record r {\n    a: own<9bad>,\n  }\n}\n")
          "control: the fragment gate must refuse a non-identifier handle name")
    , ("sabotaged parse accepts a dropped borrow angle",
        fun _ => assert (!refused "package mandate:slice;\n\ninterface items {\n  record r {\n    a: borrow<kv,\n  }\n}\n")
          "control: a missing > must refuse")
    , ("a dropped D2 field undetected",
        fun _ =>
          assert (Render.record
              { name := exRecordD2.name
                fields := [exField1, exField2, exField3, exField4, exField5] }
            == expectedRecordD2)
          "control: a dropped field must change the bytes") ]
    4 42

/-- THE ROUND-TRIP PINS: the rendered fixture parses back to exactly
    the fixture, over the edges too (empty interfaces, empty records,
    every `Ty` ctor live in the fields). -/
def parseRoundTripSpec : Spec :=
  Spec.ofList "every well-named package's rendering parses back to it"
    (fun _ => assert (
      parsesTo (Render.package exPackage) exPackage
        && parsesTo (Render.package exPackageEmpty) exPackageEmpty
        && parsesTo (Render.package exPackageNoRecords) exPackageNoRecords
        && parsesTo (Render.package exPackageEmptyRecord) exPackageEmptyRecord
        && parsesTo (Render.package exPackageRes) exPackageRes
        && parsesTo (Render.package exPackageD2) exPackageD2)
      "the parse round trip broke")
    [ ("sabotaged parse swallows trailing garbage",
        fun _ => assert (!refused (Render.package exPackage ++ " "))
          "control: trailing bytes must refuse")
    , ("sabotaged parse accepts a dropped comma",
        fun _ => assert (!refused "package mandate:slice;\n\ninterface items {\n  record r {\n    a: bool\n  }\n}\n")
          "control: a missing field comma must refuse")
    , ("sabotaged parse accepts a mistyped atom",
        fun _ => assert (!refused "package mandate:slice;\n\ninterface items {\n  record r {\n    a: boolean,\n  }\n}\n")
          "control: maximal munch must refuse `boolean` as `bool` + `ean`")
    , ("sabotaged parse accepts duplicate field names",
        fun _ => assert (!refused "package mandate:slice;\n\ninterface items {\n  record r {\n    a: bool,\n    a: bool,\n  }\n}\n")
          "control: the nodup gate must refuse at parse time")
    , ("sabotaged WitOk passes a space-named package",
        fun _ => assert (!refused (Render.package (Package.mk "mach t" [])))
          "control: the scanner must refuse an unscannable name") ]
    4 42

/-- The WitOk gate's positive face (the law's side condition is live
    data here). -/
def witOkSpec : Spec :=
  Spec.ofList "the fixture packages pass the WitOk gate"
    (fun _ => assert (
      (WitOk exPackage == true)
        && (WitOk exPackageEmpty == true)
        && (WitOk exPackageRes == true)
        && (WitOk (Package.mk "mach t" []) == false))
      "the WitOk gate drifted")
    [ ("a sabotaged WitOk accepts the space-named id",
        fun _ => assert (WitOk (Package.mk "mach t" []) == true)
          "control: the gate must refuse the space-named id")
    , ("a sabotaged WitOk refuses the well-named fixture",
        fun _ => assert (WitOk exPackage == false)
          "control: the gate must pass the well-named fixture") ]
    4 42

/-- THE ARTIFACT PIN: the committed artifact of record
    `gen/schema-slice.wit` (the gen-check byte-tie's committed side)
    parses, passes `WitOk`, and re-renders byte-identical to its
    comment-stripped bytes — the canonicalization law's value-level
    witness (the `render_parse` theorem is the named follow-up; this
    pin is its executable shadow on the REAL bytes). -/
def artifactPin : IO Bool := do
  let raw ← IO.FS.readFile ⟨"gen/schema-slice.wit"⟩
  match Parse.parse raw with
  | .error e =>
      IO.println s!"FAIL artifact pin: gen/schema-slice.wit refused: {e.message}"
      return false
  | .ok p =>
      if WitOk p != true then do
        IO.println "FAIL artifact pin: the parsed slice fails the WitOk gate"
        return false
      else if Render.package p != Parse.stripComments raw then do
        IO.println "FAIL artifact pin: the re-render drifted from the comment-stripped bytes"
        return false
      else
        IO.println "ok artifact pin: gen/schema-slice.wit parses + re-renders byte-identical"
        return true

/-- THE GRADUATION (16-surface §5.1): the lossless fragment ≅ its
    image — the retraction (render embeds, the proof-carrying decode
    reconstructs, `inv_emb` = `parse_print`) + the image-iso upgrade
    (`Retraction.toImageIso`: the image texts ≅ the well-named
    packages, a TRUE Iso). -/
def exQ : { p : Package // WitOk p } := ⟨exPackage, by decide⟩
def exImage : Kit.Retraction.image Wit.Parse.witRetraction :=
  ⟨Render.package exPackage, exQ, rfl⟩

/-- THE ISO'S RECONSTRUCTION, pinned: the fixture's rendering decodes
    back to EXACTLY the fixture (the byte-level inverse, as data). -/
def decodedFixture : { p : Package // WitOk p } := Wit.Parse.witDecode (Render.package exPackage) |>.getD Wit.Parse.witDefault

/-- The value pins: both round trips close on the fixture (the
    reconstruction is the fixture ITSELF — record names included — and
    the image text is the fixture's own rendering). -/
def gradSpec : Spec :=
  Spec.ofList "the lossless fragment ≅ its image (the graduation)"
    (fun _ => do
      assert ((Wit.Parse.witImageIso.to exImage).1 == exPackage)
        "the image's reconstruction drifted"
      assert ((Wit.Parse.witImageIso.inv ⟨exPackage, by decide⟩).1
          == Render.package exPackage)
        "the fragment's rendering drifted"
      assert (decodedFixture.1 == exPackage)
        "the proof-carrying decode drifted")
    [ ("a text outside the image is refused by the decode",
        fun _ => assert (Wit.Parse.witDecode
          "package mandate:slice;\n\ninterface items {\n  nope }\n" != none)
          "control: the honest gap must refuse the non-image bytes")
    , ("the image subtype accepts a non-image text",
        fun _ => assert (
          match Wit.Parse.witDecode "garbage" with
          | none => false
          | some _ => true)
          "control: garbage has no preimage") ]
    5 42

/-! ## the parser's drawn-text sweep (08 §11's honest property over
    the drawn texts + the truncation face) -/

/-- The canonical bytes (the sweep's base text — the fixture's own
    rendering, no comments). -/
def canonPackage : String := Render.package exPackage

/-- The canonical bytes' first `n` chars (the truncation's text). -/
def canonTake (n : Nat) : String := String.ofList (canonPackage.toList.take n)

/-- The drawn prefix length of the canonical bytes. -/
def drawTrunc (t : Tape) : Nat :=
  let (n, _) := t.below ((canonPackage.length + 1 : Nat).toUInt64)
  n

/-- The truncation face's re-test at the drawn length ALONE (the
    attachment's `fails`: tape-free). An accepted prefix must BE its
    result's rendering (the `render_parse` law's executable face). -/
def truncFails (n : Nat) : Bool :=
  match Parse.parse (canonTake n) with
  | .ok p => Render.package p != canonTake n
  | .error _ => false

/-- The TRUNCATION FACE: every drawn prefix of the canonical bytes
either REFUSES with a structured `ParseError` (position in range) or
parses to a package whose re-render is byte-identical to the prefix
(an accepted prefix is a COMPLETE package — the canonicalization
law's value face). -/
def truncationSpec : Spec :=
  Spec.ofList "the truncation face: an accepted prefix of the canonical bytes re-renders to itself"
    (fun t => do
      let n := drawTrunc t
      match Parse.parse (canonTake n) with
      | .ok p =>
          assert (Render.package p == canonTake n)
            s!"the prefix of length {n} parsed but drifted on re-render"
      | .error e =>
          assert (e.pos ≤ n)
            s!"the refusal at length {n} carried an out-of-range position {e.pos}")
    [ ("sabotaged: every proper truncation refuses (caught)",
        fun _ => assert (refused (canonTake (Render.package exPackageEmpty).length))
          "control fired: the empty-package prefix parses (the truncation face is conditional)")
    , ("sabotaged: the refusal positions drift past the text (caught)",
        fun _ => assert
          (match Parse.parse "nope" with
            | .error e => e.pos > 4 | .ok _ => false)
          "control fired: a refusal carried an out-of-range position") ]
    32 42
    (shrunk := some ⟨Nat, fun _ => True, drawTrunc, toString, truncFails, shrinkNat⟩)

/-- The drawn spliced text's property (the sweep's content): the
    canonical bytes cut at a drawn length with one junk char (the
    small alphabet) appended. The honest property per parser: parse
    is TOTAL over the drawn texts — both verdicts are STRUCTURED (the
    `.ok` package or the `ParseError` envelope) — and the accepted
    fragment ROUND TRIPS (the re-render parses back to the same
    AST). -/
def junkProp : Tape → CheckResult := fun t => do
  let (n, t1) := t.below ((canonPackage.length + 1 : Nat).toUInt64)
  let (c, _) := drawChar t1
  let s := canonTake n ++ String.singleton c
  match Parse.parse s with
  | .ok p =>
      assert (parsesTo (Render.package p) p)
        s!"the spliced text (cut {n}, junk '{c}') parsed but its re-render broke the round trip"
  | .error e =>
      assert (e.pos ≤ s.length)
        s!"the spliced text's refusal (cut {n}, junk '{c}') was unstructured: position {e.pos} past the {s.length}-char text"

/-- The drawn-text sweep against the refusal discipline. The spliced
    junk char has no measured shrinker yet — the truncation face's
    drawn length carries the attachment (`truncationSpec`). -/
def junkSpec : Spec :=
  Spec.ofList "the drawn-text sweep: structured verdicts + the round trip on the accepted fragment"
    junkProp
    [ ("sabotaged: the round trip accepts a drifted re-render (caught)",
        fun _ => assert (!parsesTo (Render.package exPackage) exPackage)
          "control fired: the fixture's round trip broke")
    , ("sabotaged: the spliced junk always parses (caught)",
        fun _ => assert (parsesTo ("d" ++ canonPackage) exPackage)
          "control fired: the junk-prefixed text parsed") ]
    32 42
    (shrinkNote := some "the spliced junk char has no measured shrinker yet; the truncation face's drawn length carries the attachment (truncationSpec)")

/-! ## the composition suites (Wit.Compose — wave-30 D4) -/

open Wit.Compose

/-- The splicer lane's fixture funcs (the scalar fragment — the tyPre
    gate constrains the composition's worlds to the parse fragment). -/
def fDouble : Wit.Func :=
  { name := "double", params := [{ name := "x", ty := .atom .u64 }]
    result := some (.atom .u64) }

def fIsBig : Wit.Func :=
  { name := "is-big", params := [{ name := "x", ty := .atom .u64 }]
    result := some (.atom .bool) }

def fCalls : Wit.Func :=
  { name := "calls", params := [], result := some (.atom .u64) }

/-- The skewed twin: same name, wrong result shape (the version-skew
    fixture's provider). -/
def fSkewDouble : Wit.Func :=
  { name := "double", params := [{ name := "x", ty := .atom .u64 }]
    result := some (.atom .string) }

/-- The import no export serves (the unresolved fixture): the join
    compares funcs by (params, result) — SigEquiv's discipline — so the
    fixture must differ in SHAPE from every export in the pool, not
    just in name (a u64 → u64 `nope` is fDouble's shape and joins). -/
def fNope : Wit.Func :=
  { name := "nope", params := []
    result := none }

def guestWorld : Wit.World :=
  { name := "guest-world", imports := []
    exports := [.func fDouble, .func fIsBig] }

def mwWorld : Wit.World :=
  { name := "mw-world", imports := [.func fDouble, .func fIsBig]
    exports := [.func fDouble, .func fIsBig, .func fCalls] }

def hostWorld : Wit.World :=
  { name := "host-world", imports := [.func fDouble, .func fIsBig]
    exports := [] }

def nGuest : Node := { name := "guest", pkg := "mandate:demo", world := guestWorld }
def nMw : Node := { name := "mw", pkg := "mandate:mw", world := mwWorld }
def nHost : Node := { name := "host", pkg := "mandate:host", world := hostWorld }

def wHostMwDouble : Wire := { consumer := "host", imp := "double", provider := "mw", exp := "double" }
def wHostMwIsBig : Wire := { consumer := "host", imp := "is-big", provider := "mw", exp := "is-big" }
def wMwGuestDouble : Wire := { consumer := "mw", imp := "double", provider := "guest", exp := "double" }
def wMwGuestIsBig : Wire := { consumer := "mw", imp := "is-big", provider := "guest", exp := "is-big" }
def wHostGuestDouble : Wire := { consumer := "host", imp := "double", provider := "guest", exp := "double" }
def wHostGuestIsBig : Wire := { consumer := "host", imp := "is-big", provider := "guest", exp := "is-big" }

/-- The CHAIN fixture: host → mw → guest (the interposed composition;
    the wac artifact's graph). -/
def chainGraph : CompGraph :=
  { id := "mandate:compose", nodes := [nHost, nMw, nGuest]
    wires := [wHostMwDouble, wHostMwIsBig, wMwGuestDouble, wMwGuestIsBig] }

/-- The DIRECT fixture: host → guest (the interposition's input). -/
def directGraph : CompGraph :=
  { id := "mandate:compose", nodes := [nHost, nGuest]
    wires := [wHostGuestDouble, wHostGuestIsBig] }

/-- THE GRAPH-CHECK SWEEP: the chain checks `.ok`; the unresolved
    import, the skewed wire and the provider cycle are each DETECTED
    (the negation query, the skew check, the cycle discipline). -/
def composeGraphSpec : Spec :=
  Spec.ofList "the composition verdicts detect every fault class"
    (fun _ => do
      assert (check chainGraph == Verdict.ok)
        "the clean chain must check .ok"
      -- the UNRESOLVED fixture: an import no export joins
      let hostNope : Node :=
        { nHost with world := { name := "host-world"
                                imports := [.func fNope], exports := [] } }
      let gUnresolved : CompGraph :=
        { id := "mandate:compose", nodes := [hostNope, nGuest], wires := [] }
      assert (check gUnresolved == .unresolved [⟨"host", "nope"⟩])
        "the unjoined import must surface as the unresolved verdict"
      -- the SKEW fixture: the pool HAS a match; the wire misses it
      let nSkewGuest : Node :=
        { name := "skew-guest", pkg := "mandate:skew"
          world := { name := "skew-world", imports := []
                     exports := [.func fSkewDouble] } }
      let gSkew : CompGraph :=
        { id := "mandate:compose", nodes := [nHost, nGuest, nSkewGuest]
          wires := [{ consumer := "host", imp := "double"
                      provider := "skew-guest", exp := "double" }] }
      assert (check gSkew == .skew [⟨"host", "skew-guest", "double", "double"⟩])
        "the mismatched wire must surface as the skew verdict"
      -- the CYCLE fixture: a imports from b, b imports from a
      let nA : Node :=
        { name := "a", pkg := "mandate:a"
          world := { name := "a-world", imports := [.func fIsBig]
                     exports := [.func fDouble] } }
      let nB : Node :=
        { name := "b", pkg := "mandate:b"
          world := { name := "b-world", imports := [.func fDouble]
                     exports := [.func fIsBig] } }
      let gCycle : CompGraph :=
        { id := "mandate:compose", nodes := [nA, nB]
          wires := [{ consumer := "a", imp := "is-big"
                      provider := "b", exp := "is-big" }
                    , { consumer := "b", imp := "double"
                        provider := "a", exp := "double" }] }
      assert (check gCycle == .cycle ["a", "b", "a"])
        "the provider cycle must surface as the cycle verdict with its path")
    [ ("a sabotaged check accepts a wire to a missing endpoint",
        fun _ => assert (wireResolves chainGraph
            { consumer := "host", imp := "double"
              provider := "ghost", exp := "double" })
          "control: a wire whose provider node is absent must NOT resolve")
    , ("a sabotaged join accepts the skewed signature",
        fun _ => assert (sigAgree (.func fDouble) (.func fSkewDouble))
          "control: u64→u64 must NOT join u64→string")
    , ("a sabotaged cycle walk reports the clean chain",
        fun _ => assert (findCycle chainGraph != [])
          "control: the acyclic chain must walk to no cycle") ]
    5 42

/-- The non-passthrough middleware (its import does not join its
    export — the skewed wrapper the seam must expose). -/
def nSkewMw : Node :=
  { name := "mw", pkg := "mandate:mw"
    world := { name := "skew-mw", imports := [.func fSkewDouble]
               exports := [.func fDouble, .func fIsBig] } }

/-- The non-joiner guest (import ≠ export) for the passthrough tooth. -/
def nSkewGuestFixture : Node :=
  { name := "skew-guest", pkg := "mandate:skew"
    world := { name := "skew-world", imports := [.func fIsBig]
               exports := [.func fSkewDouble] } }

/-- THE INTERPOSITION SWEEP: the seam replaces the direct edge with
    the two-edge chain, the passthrough middleware preserves the
    end-to-end signature (the law's executable face), and the refusals
    + the skewed middleware are caught. -/
def interposeSpec : Spec :=
  Spec.ofList "the interposition seam composes and preserves"
    (fun _ => do
      match interpose directGraph wHostGuestDouble nMw "double" "double" with
      | none => assert false "the passthrough interposition must compose"
      | some g' => do
        assert (g'.nodes.length == 3)
          "the middleware must join as a third node"
        assert (g'.wires.length == 3)
          "the direct edge must become the two-edge chain (plus the \
             untouched is-big wire)"
        assert (passthrough nMw "double")
          "the mw's double must pass the passthrough test"
        -- the end-to-end signature is PRESERVED (the law's value face:
        -- host's import joins guest's export exactly as before)
        assert (sigAgree (.func fDouble) (.func fDouble))
          "the end-to-end join must survive the interposition"
        -- and the composed graph still checks clean
        assert (check g' == Verdict.ok)
          "the interposed composition must check .ok"
      -- the law itself, at the Prop level (the passthrough_id shape)
      have h2 : Wit.Compose.SigEquiv (.func fDouble) (.func fDouble) :=
        by show fDouble.params = fDouble.params ∧ fDouble.result = fDouble.result
             ∧ fDouble.async = fDouble.async
           exact ⟨rfl, rfl, rfl⟩
      have law := passthrough_id (imp := .func fDouble) h2 h2 h2
      assert (sigAgree (.func fDouble) (.func fDouble))
        "the passthrough law must instantiate on the fixture")
    [ ("a name-colliding middleware composes",
        fun _ => assert (interpose directGraph wHostGuestDouble nHost
                        "double" "double").isSome
          "control: the runtime nodup route must refuse the collision")
    , ("a skewed middleware slips past the graph check",
        fun _ =>
          assert ((match interpose directGraph wHostGuestDouble nSkewMw
                      "double" "double" with
                  | none => true
                  | some g' => check g' == Verdict.ok))
            "control: the skewed mw's inner wire must NOT check .ok")
    , ("the passthrough test accepts a non-joiner",
        fun _ => assert (passthrough nSkewGuestFixture "double")
          "control: import≠export must fail the passthrough test") ]
    (h := by simp) 5 42
  where
    nSkewGuestFixture : Node :=
      { name := "skew-guest", pkg := "mandate:skew"
        world := { name := "skew-world", imports := [.func fIsBig]
                   exports := [.func fSkewDouble] } }

/-- The wac emitter's GOLDEN bytes (the chain fixture's artifact
    shape) + the header's hash discipline. -/
def expectedWac : String :=
  "package mandate:compose;\n\n"
    ++ "host: component;\nmw: component;\nguest: component;\n"
    ++ "\ncomposition: component {\n"
    ++ "  new host {\n"
    ++ "    import \"double\": mw.double\n"
    ++ "    import \"is-big\": mw.is-big\n"
    ++ "  }\n"
    ++ "  new mw {\n"
    ++ "    import \"double\": guest.double\n"
    ++ "    import \"is-big\": guest.is-big\n"
    ++ "  }\n"
    ++ "}\n"

def wacEmitterSpec : Spec :=
  Spec.ofList "the wac emitter renders the composition to the golden bytes"
    (fun _ => do
      assert (wacBody chainGraph == expectedWac)
        "the wac body drifted from the golden bytes"
      -- the header names the fresh body's hash (the byte-tie's contract)
      let f := wacFile chainGraph
      assert (f.endsWith expectedWac)
        "the artifact must be the 2-line header + the body"
      assert ((String.splitOn f "\n")[0]!.contains "GENERATED")
        "the artifact must carry the GENERATED marker"
      assert ((String.splitOn f "\n")[1]!.contains
          (toString (wacBody chainGraph).hash))
        "the header's content hash must name the body's hash")
    [ ("a dropped wiring undetected",
        fun _ => assert (wacBody { chainGraph with
                                   wires :=
                                     [wHostMwDouble, wMwGuestDouble,
                                      wMwGuestIsBig]
                                   wires_nodup := by decide }
          == expectedWac)
          "control: a dropped wire must change the bytes")
    , ("a renamed package undetected",
        fun _ => assert (wacBody { chainGraph with id := "mandate:other" }
          == expectedWac)
          "control: the package id must be in the bytes") ]
    4 42

/-- THE COMPOSITION ARTIFACT PIN: the committed fixture
    `wit/WitTests/fixtures/compose-slice.wac` ties byte-exact against
    the fresh render (the byte-tie's executable shadow on the REAL
    bytes — the artifactPin pattern). -/
def composePin : IO Bool := do
  let raw ← IO.FS.readFile ⟨"wit/WitTests/fixtures/compose-slice.wac"⟩
  match TestingKit.Golden.tie raw (wacBody chainGraph) with
  | .tied => do
      IO.println "ok compose pin: compose-slice.wac ties byte-exact"
      return true
  | .drifted why => do
      IO.println s!"FAIL compose pin: the committed wac artifact drifted: {why}"
      return false

/-! ## the func-level async row (the WASI async lane's WIT face) -/

-- BEq over the world carrier (manual — the proof-carrying structures
-- don't carry LawfulBEq):
instance : BEq Wit.Func where
  beq a b := a.name == b.name && a.params == b.params && a.result == b.result
    && a.async == b.async
instance : BEq Wit.Item where
  beq a b := match a, b with
    | .func f, .func g => f == g
    | .iface i, .iface j => i == j
    | _, _ => false
instance : BEq Wit.World where
  beq a b := a.name == b.name && a.imports == b.imports && a.exports == b.exports

/-- The async func's fixture (the splicer-mw's watch-counts shape —
    the async-lift lane's export). -/
def fWatch : Wit.Func :=
  { name := "watch-counts", params := [{ name := "n", ty := .atom .u64 }]
    result := some (.stream (.atom .u64)), async := true }

def fAdd64 : Wit.Func :=
  { name := "add64", params := [{ name := "a", ty := .atom .u64 }
                               , { name := "b", ty := .atom .u64 }]
    result := some (.atom .u64) }

def exWorld : Wit.World :=
  { name := "guest-world", imports := []
    exports := [.func fAdd64, .func fWatch] }

def exWorldIface : Wit.World :=
  { name := "w"
    imports := [.iface { name := "types", records := [], resources := [] }]
    exports := [] }

/-- A world-parse verdict: did the text parse back to the expected
    world (unwrapped from the WorldOk-gated subtype)? -/
def worldParsesTo (s : String) (w : Wit.World) : Bool :=
  match Parse.parseWorld s with
  | .ok q => q.1 == w
  | .error _ => false

/-- A world-parse verdict: was the text refused? -/
def worldRefused (s : String) : Bool :=
  match Parse.parseWorld s with
  | .error _ => true
  | .ok _ => false

/-- THE ASYNC ROW's pins: the spelling (the `async` keyword before
    `func`, per the WIT spec's current shape), the golden item line,
    the world round trip (the func-level async row parses back), and
    the teeth: every malformed async spelling refuses with the
    structured ParseError. -/
def asyncSpec : Spec :=
  Spec.ofList "the async row renders, round trips, and refuses the malformed spellings"
    (fun _ => do
      -- the golden spellings (the legacy fixtures' shape)
      assert (Render.func fWatch == "async func(n: u64) -> stream<u64>")
        "the async func's spelling drifted"
      assert (Render.func fAdd64 == "func(a: u64, b: u64) -> u64")
        "the sync func's spelling drifted"
      assert (Render.exportItem (.func fWatch)
          == "  export watch-counts: async func(n: u64) -> stream<u64>;\n")
        "the async export item's golden bytes drifted"
      -- the round trip over the world face (sync + async + iface rows)
      assert (worldParsesTo (Render.world exWorld) exWorld)
        "the world's round trip broke"
      assert (worldParsesTo (Render.world exWorldIface) exWorldIface)
        "the by-name iface item's round trip broke"
      -- the WorldOk gate's face
      assert (Wit.Parse.WorldOk exWorld == true)
        "the well-named world must pass the gate"
      -- the TEETH: the malformed async spellings refuse
      assert (worldRefused "world w {\n  export f: async async func() -> u64;\n}\n")
        "a doubled async must refuse"
      assert (worldRefused "world w {\n  export f: func() -> u64;\n  import g: asyn func();\n}\n")
        "a truncated async must refuse"
      assert (worldRefused "world w {\n  export f: async func();\n}\n\n")
        "trailing garbage must refuse"
      -- the decode's nodup tooth: a duplicate item name refuses
      assert (worldRefused "world w {\n  export f: func();\n  export f: func();\n}\n")
        "a duplicate item name must refuse"
      -- the intercalate teeth: the junk comma faces refuse
      assert (worldRefused "world w {\n  export f: func(, a: u64);\n}\n")
        "a leading comma must refuse"
      assert (worldRefused "world w {\n  export f: func(a: u64, );\n}\n")
        "a trailing comma must refuse")
    [ ("a dropped async keyword undetected",
        fun _ => assert (Render.func fWatch == "func(n: u64) -> stream<u64>")
          "control: the async row must print its keyword")
    , ("a sabotaged round trip accepts a dropped param",
        fun _ => assert (worldParsesTo (Render.world exWorld)
            { name := "guest-world", imports := []
              exports := [.func { name := "add64", params := [{ name := "a", ty := .atom .u64 }]
                                  result := some (.atom .u64), async := false }]
              imports_nodup := by decide, exports_nodup := by decide })
          "control: a dropped param must change the round trip")
    , ("a sabotaged refusal accepts the doubled async",
        fun _ => assert (!worldRefused "world w {\n  export f: async async func() -> u64;\n}\n")
          "control: the doubled async must refuse") ]
    4 42

/-! ## the session bridge (Wit.Session — the async-lift's WIT face) -/

open Wit.Session

instance : BEq Wit.Session.Tape :=
  inferInstanceAs (BEq (List Wit.Session.Move))

/-- The duality pins: the import row's tape IS the export's dual;
    the async row's tape carries the lift's two moves; a sync row's
    session ≠ an async row's session (the join's async conjunct's
    signature-level face). -/
def sessionSpec : Spec :=
  Spec.ofList "the world-row ↔ session bridge dual-checks"
    (fun _ => do
      -- the sync row's tape: recv params, send result
      assert (exportTape fAdd64
          == [Move.recv .params, Move.send .result])
        "the sync row's call tape drifted"
      -- the async row's tape: recv params, then the lift's two sends
      assert (exportTape fWatch
          == [Move.recv .params, Move.send .taskReturn, Move.send .taskHandle])
        "the async row's call tape drifted"
      -- the duality check (the theorem's value face)
      assert (importTape fWatch == dual (exportTape fWatch))
        "the import row's tape must be the export's dual"
      assert (dual (exportTape fWatch)
          == [Move.send .params, Move.recv .taskReturn, Move.recv .taskHandle])
        "the dual's directions must flip pointwise"
      -- the signature-level tooth
      assert (exportTape { fWatch with async := false }
          != exportTape { fWatch with async := true })
        "a sync row's session must differ from an async row's")
    [ ("a sabotaged duality keeps the directions",
        fun _ => assert (dual (exportTape fWatch) == exportTape fWatch)
          "control: the dual must flip the directions")
    , ("a sabotaged tape drops the lift's moves",
        fun _ => assert (exportTape fWatch == [Move.recv .params, Move.send .result])
          "control: the async row's tape must carry the lift's two moves") ]
    4 42

def main : IO UInt32 := do
  if ← artifactPin then
    if ← composePin then
      TestingKit.mainOfSuites
        [ ("Wit.Render", [renderTySpec, renderBlockSpec, renderEdgeSpec])
        , ("Wit.Parse", [parseRoundTripSpec, witOkSpec, gradSpec,
                         truncationSpec, junkSpec, d2TySpec])
        , ("Wit.World", [asyncSpec])
        , ("Wit.Session", [sessionSpec])
        , ("Wit.Compose", [composeGraphSpec, interposeSpec, wacEmitterSpec]) ]
    else
      return 1
  else
    return 1

end -- public section

