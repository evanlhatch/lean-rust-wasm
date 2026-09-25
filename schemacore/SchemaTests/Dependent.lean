/-
# SchemaTests.Dependent — the dependent-schemas lane's suites

The dependent lane's teeth (15-patterns #5): the Packet fixture's
boundary validation (a length-mismatched packet REFUSES; a valid one
CONSTRUCTS the typed value — the proof-carrying parse, live), the
tagged payload's tag/arm gate, the restricted mutation's
re-validating discipline, the type-level dependent structure's
runge-1 face (a mismatched Packet is UNCONSTRUCTIBLE), and the
correspondence pin (the schema validator + the type-level smart
constructor agree on the fixture). Every law itself is theorem-backed
in SchemaCore.Dependent (`check_iff`, `validate_sound`, `validate_none`,
`setList_sound`, `setList_none`, `shapeDiags_nil_iff`); the runtime
rows pin the VALUES.

The five questions: root = the dependent lane's value-level evidence;
carrier = TestingKit's Spec (the negatives subtype); spine reading =
none; ladder rung = tested agreement rows over proved laws (the
theorem face is the authority; these pins are its regression surface);
gate row = SchemaTests' dependent suite + the axiom report.

-/

import TestingKit.Harness
import SchemaCore.Dependent

open SchemaCore TestingKit



/-! ## The type-level fixture — the honest dependent structure

The record's dependent shape AS A LEAN STRUCTURE: `bytes`'s type
DEPENDS on `length` (the subtype's proof field IS the invariant —
rung 1: a length-mismatched packet is unconstructible, no checker
pass). This is the review's `Packet { length : Nat, bytes : Vector
UInt8 length }` at the type level. -/

/-- The type-level Packet. -/
structure Packet where
  length : Nat
  bytes : { l : List UInt64 // l.length = length }

/-- The smart constructor: the ONLY way in from raw bytes; a
    length-breaking payload refuses (typed none, never a smuggled
    default). -/
def Packet.mkSmart (length : Nat) (bytes : List UInt64) : Option Packet :=
  if h : bytes.length = length then some ⟨length, ⟨bytes, h⟩⟩ else none

/-! ## The schema-level fixture — the Packet spec -/

/-- The u64-list value builder (the fixture's list payload). -/
def vListOfU64 : List UInt64 → VList .u64
  | [] => .nil
  | b :: bs => .cons (.u64 b) (vListOfU64 bs)

/-- A raw Packet row with an INDEPENDENT count (the validator's input
    face — the count is the wire's claim, the bytes the wire's
    truth). -/
def packetRowRaw (count : UInt64) (bs : List UInt64) (tag : UInt64)
    (v : Value (.result .u64 .string)) : RowVals packetFields :=
  .cons (.u64 count)
    (.cons (.list (vListOfU64 bs)) (.cons (.u64 tag) (.cons v .nil)))

/-- The self-consistent row builder (the count IS the bytes' length). -/
def packetRowOf (bs : List UInt64) (tag : UInt64)
    (v : Value (.result .u64 .string)) : RowVals packetFields :=
  packetRowRaw bs.length.toUInt64 bs tag v

/-- The correspondence's lowering: a Packet row → the type-level
    Packet. The bytes' length fact becomes the subtype's proof; a row
    whose length fact fails lowers to `none` (the gate rides HERE
    too — proof erasure at the target does not delete the check). -/
def packetOfRow (row : RowVals packetFields) : Option Packet :=
  match (RowVals.project? packetFields row "length").bind FieldVal.u64?,
        (RowVals.project? packetFields row "bytes") with
  | some n, some ⟨.list .u64, .list vl⟩ =>
      if h : vl.evalList.length = n.toNat then
        some ⟨n.toNat, ⟨vl.evalList, h⟩⟩
      else none
  | _, _ => none

/-! ## The suites -/

/-- The boundary validation's matrix: valid constructs, every
    out-of-policy shape refuses. -/
def dependentSpec : Spec :=
  Spec.ofList "the dependent lane: validate + the tagged gate + the mutation"
    (fun _ =>
      let okRow := packetRowOf [7, 9] 0 (.ok (.u64 1))
      let broken := packetRowRaw 2 [7, 9, 3] 0 (.ok (.u64 1))
      let badTag := packetRowOf [7, 9] 7 (.ok (.u64 1))
      let badArm := packetRowOf [7, 9] 1 (.ok (.u64 1))
      -- the valid row validates AND checks (the two faces agree)
      let vr := packetSpec.validate okRow
      assert ((vr.isSome) && (packetSpec.check okRow)
        -- the length check has TEETH: a mismatched packet refuses
        && !(packetSpec.check broken)
        && ((packetSpec.validate broken).isNone)
        -- the tagged payload's gate: a tag outside {0,1} refuses;
        -- a tag/arm disagreement refuses
        && ((packetSpec.validate badTag).isNone)
        && !(packetSpec.check badArm)
        && ((packetSpec.validate badArm).isNone)
        -- the correspondence: validator + smart constructor agree
        && (match packetOfRow okRow, Packet.mkSmart 2 [7, 9] with
            | some p1, some p2 => p1.length == p2.length && p1.bytes.1 == p2.bytes.1
            | _, _ => false)
        -- the lowering refuses the row the validator refuses
        && ((packetOfRow broken).isNone)
        -- the restricted mutation: a valid replace passes, a
        -- length-breaking one refuses, a foreign field refuses
        && (match vr with
            | some ⟨row, hv⟩ =>
                match packetSpec.setList? "bytes" (vListOfU64 [1, 2]) ⟨row, hv⟩ with
                | some _ => true | none => false
            | none => false)
        && (match vr with
            | some ⟨row, hv⟩ =>
                (packetSpec.setList? "bytes" (vListOfU64 [1, 2, 3]) ⟨row, hv⟩).isNone
                && (packetSpec.setList? "length" (vListOfU64 [1]) ⟨row, hv⟩).isNone
            | none => false))
      "the dependent lane drifted")
    [ ("the length check ignores a mismatch",
        fun _ =>
          assert (packetSpec.check (packetRowRaw 2 [7, 9, 3] 0 (.ok (.u64 1))))
            "control fired: the length dependency must refuse the mismatch")
    , ("the validator accepts a tag/arm disagreement",
        fun _ =>
          assert ((packetSpec.validate
            (packetRowOf [7, 9] 1 (.ok (.u64 1)))).isSome)
            "control fired: tag 1 must demand the err arm")
    , ("the mutation fabricates an invalid successor",
        fun _ =>
          match packetSpec.validate (packetRowOf [7, 9] 0 (.ok (.u64 1))) with
          | some ⟨row, hv⟩ =>
              assert ((packetSpec.setList? "bytes" (vListOfU64 [1, 2, 3])
                ⟨row, hv⟩).isSome)
                "control fired: the re-validating replace must refuse"
          | none => .error "control fixture broke: the valid row refused")
    , ("the type-level constructor accepts a mismatch",
        fun _ =>
          assert ((Packet.mkSmart 2 [7, 9, 3]).isSome)
            "control fired: mkSmart must refuse a length-breaking payload") ]
    4 42

/-- The type-level rung-1 pins: the smart constructor's teeth + the
    validated packet's data (kernel-visible). -/
def dependentTypeSpec : Spec :=
  Spec.ofList "the type-level dependent structure"
    (fun _ =>
      assert ((
        -- the valid construction
        ((Packet.mkSmart 2 [7, 9]).isSome)
        -- the mismatched construction refuses
        && ((Packet.mkSmart 2 [7, 9, 3]).isNone)
        -- the constructed packet carries the length fact (the
        -- subtype's proof field — the data is consistent by construction)
        && (match Packet.mkSmart 2 [7, 9] with
            | some p => p.length == 2 && p.bytes.1 == [7, 9]
            | none => false)
        -- the correspondence, kernel-pinned: the validated row lowers
        -- to EXACTLY the smart constructor's value
        && (match packetOfRow (packetRowOf [7, 9] 0 (.ok (.u64 1))),
              Packet.mkSmart 2 [7, 9] with
            | some p1, some p2 => p1.length == p2.length
              && p1.bytes.1 == p2.bytes.1
            | _, _ => false)))
      "the type-level face drifted")
    [ ("the constructed packet drops the length fact",
        fun _ =>
          match Packet.mkSmart 2 [7, 9] with
          | some p => assert (p.bytes.1.length == 3)
              "control fired: the subtype's proof field pins the bytes \
                to the length — the data cannot drift"
          | none => .error "control fixture broke")
    , ("the lowering accepts an unvalidated row",
        fun _ =>
          assert ((packetOfRow (packetRowRaw 2 [7, 9, 3] 0 (.ok (.u64 1)))).isSome)
            "control fired: the lowering must refuse the broken row") ]
    4 42

/-- The Rust face pins: the boundary validator's Rust text renders
    from the SAME `Dep` data the Lean checker reads (one owner). The
    emitter integration is the named step (SchemaCore.Emit's wave). -/
def dependentRustSpec : Spec :=
  Spec.ofList "the boundary validator's Rust face"
    (fun _ =>
      assert ((
        (Dep.rustCheck (.lengthEq "length" "bytes")
          == "    if record.bytes.len() as u64 != record.length {\n" ++
             "        return Err(ValidError::LengthMismatch {\n" ++
             "            count: record.length,\n" ++
             "            got: record.bytes.len() as u64,\n" ++
             "        });\n    }\n")
        && ((Dep.rustCheck (.tagMatches "tag" "result")).contains "TagMismatch")
        && ((packetSpec.rustChecks |>.length) > 0)))
      "the Rust face drifted")
    [ ("the two dependencies render the same text",
        fun _ =>
          assert (Dep.rustCheck (.lengthEq "length" "bytes")
            == Dep.rustCheck (.tagMatches "tag" "result"))
            "control fired: the two dep shapes must render different gates")
    , ("the rendered check forgets the bytes field",
        fun _ =>
          assert (!(Dep.rustCheck (.lengthEq "length" "bytes")).contains "record.bytes")
            "control fired: the length gate must name BOTH fields") ]
    4 42


