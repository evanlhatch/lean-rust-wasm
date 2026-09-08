/-
# Substrait.Proto.Rel

Wire-faithful model of Substrait's `algebra.proto` relation surface.  Plain
total Lean data, no proofs.  Every proto-optional message field is an
`Option`; singular fields are direct values.

The relation set mirrors the substrait-proto shapes as far as the skeleton
needs: Read / Filter / Project / Aggregate / Sort / Fetch / Join / Cross / Set /
Write / ExtensionLeaf / ExtensionSingle / ExtensionMulti.  Note that the text
emitter (substrait-explain grammar) supports only a strict subset — `Write`
and `Extension*` are unrepresentable there and hard-error in
`Substrait.Emit.Text`.

Every message here references `Rel` (directly or transitively), so the whole
relation surface lives in one `mutual` block and the instance derivations are
batched after it.
-/
import Substrait.Proto.Expression

namespace Substrait.Proto

/- All relation messages are mutually recursive with `Rel` — one block,
   instances batched at the end. -/
mutual

  /-- Proto `RelCommon.EmitKind` — Direct or an explicit output-mapping remap. -/
  inductive EmitKind where
    | direct
    | emit (outputMapping : List Nat)

  /-- Proto `RelCommon` — the emit kind plus an opaque advanced-extension slot. -/
  structure RelCommon where
    emit : Option EmitKind
    advancedExtension : Option String

  /-- Proto `NamedStruct` — a struct type plus column names. -/
  structure NamedStruct where
    fields : List PType
    names : List String

  /-- Proto `ReadRel.ReadType` — NamedTable (`names` is the dotted path). -/
  inductive ReadType where
    | namedTable (names : List String)
    | virtualTable (rows : List (List Expression)) (filter : Option Expression)

  /-- Proto `ReadRel` — the base scan relation. -/
  structure ReadRel where
    readType : ReadType
    baseSchema : Option NamedStruct
    common : Option RelCommon

  /-- Proto `FilterRel` — `{ condition, input, common }`. -/
  structure FilterRel where
    condition : Expression
    input : Rel
    common : Option RelCommon

  /-- Proto `ProjectRel` — `{ expressions, input, common }` (outputs = input ++ expressions). -/
  structure ProjectRel where
    expressions : List Expression
    input : Rel
    common : Option RelCommon

  /-- Proto `AggregateFunction` measure (minimal shape used by the emitter). -/
  structure AggregateFunction where
    functionReference : Nat
    args : List Expression
    outputType : PType

  /-- Proto `AggregateRel.Measure` (phase/invocation/filter/sorts are dropped by the text grammar). -/
  structure AggregateMeasure where
    measure : AggregateFunction

  /-- Proto `AggregateRel` — grouping expressions + measures. -/
  structure AggregateRel where
    groupingExpressions : List Expression
    measures : List AggregateMeasure
    input : Rel
    common : Option RelCommon

  /-- Proto `sort_field.SortDirection` (display names: `AscNullsFirst`, ...). -/
  inductive SortDirection where
    | unspecified
    | ascNullsFirst
    | ascNullsLast
    | descNullsFirst
    | descNullsLast
    | clustered

  /-- Proto `SortField` — expression + direction. -/
  structure SortField where
    expr : Expression
    direction : SortDirection

  /-- Proto `SortRel`. -/
  structure SortRel where
    sorts : List SortField
    input : Rel
    common : Option RelCommon

  /-- Proto `FetchRel` — limit/offset (None = absent on the wire). -/
  structure FetchRel where
    limit : Option Nat
    offset : Option Nat
    input : Rel
    common : Option RelCommon

  /-- Proto `join_rel.JoinType` (display names from substrait-explain). -/
  inductive JoinType where
    | unspecified
    | inner | outer | left | right
    | leftSemi | rightSemi | leftAnti | rightAnti
    | leftSingle | rightSingle | leftMark | rightMark

  /-- Proto `JoinRel` — left/right children + condition (+ optional post filter). -/
  structure JoinRel where
    joinType : JoinType
    left : Rel
    right : Rel
    condition : Expression
    postJoinFilter : Option Expression
    common : Option RelCommon

  /-- Proto `CrossRel`. -/
  structure CrossRel where
    left : Rel
    right : Rel
    common : Option RelCommon

  /-- Proto `set_rel.SetOp` (display names from substrait-explain). -/
  inductive SetOp where
    | unspecified
    | minusPrimary | minusPrimaryAll | minusMultiset
    | intersectionPrimary | intersectionMultiset | intersectionMultisetAll
    | unionDistinct | unionAll

  /-- Proto `SetRel` — N inputs, one set operation. -/
  structure SetRel where
    op : SetOp
    inputs : List Rel
    common : Option RelCommon

  /-- Proto `WriteRel` (DML).  `op` is the string form of `WriteOp`. -/
  structure WriteRel where
    tableName : String
    op : String
    tableSchema : Option NamedStruct
    input : Rel
    common : Option RelCommon

  /-- Proto `ExtensionLeafRel` — a custom operator with an opaque `Any` detail. -/
  structure ExtensionLeafRel where
    detail : Option String
    common : Option RelCommon

  /-- Proto `ExtensionSingleRel` — input + opaque detail. -/
  structure ExtensionSingleRel where
    input : Rel
    detail : Option String
    common : Option RelCommon

  /-- Proto `ExtensionMultiRel` — N inputs + opaque detail. -/
  structure ExtensionMultiRel where
    inputs : List Rel
    detail : Option String
    common : Option RelCommon

  /--
  Proto `Rel` — the union of every relation on the wire, mirroring
  `algebra.proto` `RelType`.
  -/
  inductive Rel where
    | read (r : ReadRel)
    | filter (r : FilterRel)
    | project (r : ProjectRel)
    | aggregate (r : AggregateRel)
    | sort (r : SortRel)
    | fetch (r : FetchRel)
    | join (r : JoinRel)
    | cross (r : CrossRel)
    | set (r : SetRel)
    | write (r : WriteRel)
    | extensionLeaf (r : ExtensionLeafRel)
    | extensionSingle (r : ExtensionSingleRel)
    | extensionMulti (r : ExtensionMultiRel)

end

/- Instances for the whole relation surface, declared after `Rel` exists. -/
deriving instance Repr, BEq for EmitKind, RelCommon, NamedStruct, ReadType, ReadRel, FilterRel, ProjectRel, AggregateFunction, AggregateMeasure, AggregateRel, SortDirection, SortField, SortRel, FetchRel, JoinType, JoinRel, CrossRel, SetOp, SetRel, WriteRel, ExtensionLeafRel, ExtensionSingleRel, ExtensionMultiRel, Rel

/-- The declared name of a rel, matching substrait-explain's `NamedRelation`. -/
def Rel.name : Rel → String
  | .read _             => "Read"
  | .filter _           => "Filter"
  | .project _          => "Project"
  | .aggregate _        => "Aggregate"
  | .sort _             => "Sort"
  | .fetch _            => "Fetch"
  | .join _             => "Join"
  | .cross _            => "Cross"
  | .set _              => "Set"
  | .write _            => "Write"
  | .extensionLeaf _    => "ExtensionLeaf"
  | .extensionSingle _  => "ExtensionSingle"
  | .extensionMulti _   => "ExtensionMulti"

end Substrait.Proto
