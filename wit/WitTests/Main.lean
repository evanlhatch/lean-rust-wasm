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

import Lean
import TestingKit.Harness
import Wit
import Wit.Render
import Wit.Parse

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
              == "result<option<u64>, string>"))
      "the WIT type rendering drifted")
    [ ("sabotaged option render ties",
        fun _ => assert (Render.ty exTyOpt == "u64")
          "control: option must nest, not vanish")
    , ("sabotaged result drops a summand",
        fun _ => assert (Render.ty exTyResult == "result<u64>")
          "control: result must keep BOTH summands")
    , ("sabotaged tuple render ties",
        fun _ => assert (Render.ty exTyTuple == "string")
          "control: the tuple must render its pair") ]
    4 42

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
              == "  record empty {\n\n  }\n"))
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
  beq a b := a.name == b.name && a.records == b.records
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
  ⟨"mandate:slice", [⟨"items", [], by decide⟩]⟩

def exPackageEmptyRecord : Package :=
  ⟨"mandate:slice", [⟨"items", [{ name := "empty", fields := [] }], by decide⟩]⟩

/-- THE ROUND-TRIP PINS: the rendered fixture parses back to exactly
    the fixture, over the edges too (empty interfaces, empty records,
    every `Ty` ctor live in the fields). -/
def parseRoundTripSpec : Spec :=
  Spec.ofList "every well-named package's rendering parses back to it"
    (fun _ => assert (
      parsesTo (Render.package exPackage) exPackage
        && parsesTo (Render.package exPackageEmpty) exPackageEmpty
        && parsesTo (Render.package exPackageNoRecords) exPackageNoRecords
        && parsesTo (Render.package exPackageEmptyRecord) exPackageEmptyRecord)
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

def main : IO UInt32 := do
  if ← artifactPin then
    TestingKit.mainOfSuites
      [ ("Wit.Render", [renderTySpec, renderBlockSpec, renderEdgeSpec])
      , ("Wit.Parse", [parseRoundTripSpec, witOkSpec, gradSpec]) ]
  else
    return 1
