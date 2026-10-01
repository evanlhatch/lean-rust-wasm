/-
# Substrait.Wire — the plan fragment's protobuf encoding (the message layer)

Owner: the substrait wire agent (the mandate tree, `substrait/`).

The protobuf encoding of `Substrait.Proto`'s narrow plan model — the
typed layer's lowering target (Typed → Proto → THESE BYTES). The field
numbers are the VENDORED protos' (legacy/lean/substrait/protos — the
substrait upstream's wire discipline, read-only mining): the Type kind
oneof (bool = 1, i32 = 5, i64 = 7, string = 12, list = 27), the
Literal oneof (boolean = 1, i32 = 5, i64 = 7, string = 12, nullable =
50), the Expression rex_type oneof (literal = 1, selection = 2,
scalar_function = 3), the Rel rel_type oneof (read = 1, filter = 2,
fetch = 3, aggregate = 4, sort = 5, join = 6, project = 7, set = 8),
Plan.relations = 3, and the enum values (Nullability, JoinType,
SortDirection, SetOp) at their upstream numbers.

THE NAMED DIVERGENCES (the seed's honest face — each is a narrowing
the anchor ladder's port retires):
- the scalar-function NAME rides field 9 of the ScalarFunction message
  (upstream field 1 is the `function_reference` uint32 anchor — the
  seed carries the name directly, the anchor table is not yet built);
- the plan's function-name list rides field 100 of the Plan message
  (upstream field 2 is the `extensions` message — the seed's
  first-use name list is the stand-in);
- the aggregate's measures ride field 4 as RAW Expression messages
  (upstream wraps each in `Measure { AggregateFunction measure = 1 }` —
  the seed's narrowed model collapses the wrapper, per
  Substrait.Proto's header);
- the fetch window's limit/offset ride the upstream `count_expr` (6) /
  `offset_expr` (5) faces as literal-i64 Expressions (the constant
  window's honest shape).

THE DIALECT (the accepted-byte policy, canonical-form only): the
encoder writes every field in a fixed order; the decoder accepts
EXACTLY that face — every field present (absence is malformed, not a
default), trailing bytes refuse, and the canonical varint discipline
inherits `Kit.Varint`'s minimal-encodings-only policy. The lenient
interop face is the named follow-up (the interop lane's first
consumer).

THE FUEL (the recursive decoders' discipline): the recursive message
decoders (PType/Expression/Rel — the recursive types) are fuel-bounded
with the fuel as THE structural argument — the same discipline as
`decRep?` (the alternative, well-founded recursion on the byte
length, is the 06-trap: kernel-opaque equations kill the laws'
definitional reductions). The laws bound the fuel by the encoded
size + 1 (each nesting wrap spends ≥ 2 bytes, so the fuel walks the
depth).

THE INDOMAIN (pattern #18's admissible subdomain): the wire's literal
int32/int64 fields hold the two's-complement 64-bit face — the
admissible payloads are the 32/64-bit ranges; the wire's strings hold
the ASCII fragment (the full UTF-8 face rides TextKit's char level —
the char level is TextKit's alone). `inDomain*` gates the WHOLE plan
at the emission boundary; the off-domain face (truncation for
out-of-range ints, refusal or corruption for non-ASCII strings) is
PINNED in SubstraitTests — never a silent law gap.

THE LAW (LANDED): `decPlanBody?_encPlanBody_append` — the Plan body's
append-form round trip for `inDomainPlan p`, the fuel above the encoded
size, and a CLEAN SUFFIX (`CleanBytes` — the next tag is not
length-delimited, so every rep terminates there) — composed
field-by-field through the primitive laws (ProtoBuf's) and the Rel
law's one-fuel induction (`decRelBody?_law` — the two faces, append +
nil, together; the rel bodies are length-delimited so their reps
terminate at the message's OWN boundary — no suffix discipline below
the plan). The FULL face (`rest = []`) is unconditional:
`decPlan?_encPlan`.

THE PROMOTION (the second-consumer rule's move): the format-generic
primitive layer (the tag discipline, the length-delimited/repeat
faces, the signed varint + ASCII string faces, the oneof/message-
field/string/bool/enum combinator layer, the clean-suffix discipline,
and the `WireTarget` row structure) now lives in `Kit.Proto` — this
module is that layer's FIRST consumer (the vortex DType proto face the
SECOND); every law statement moved byte-identical in behavior (the
substrait sweeps below are the move's teeth). The canonical-order
choices recorded: the RelRoot writes the names rep BEFORE the input (the
input's field-1 tag then terminates the names' rep INSIDE the payload,
keeping the element's decode unconditional); the rel arms' frames are
consumed to their ends, the oneof's rest riding out.

THE FRAGMENT BOUNDARY (the honest statement): the round trip is at the
PROTO face — `Substrait.Typed`'s lowering (Typed → Proto) composes
with it (`toProto` then `encPlan`, pinned in SubstraitTests), and the
TYPED decode (Proto → Typed) reads the SAME plan back to the typed
term (`Substrait.TypedDecode` — the composed full circle is pinned in
SubstraitTests.TypedDecode).

Core-only (imports Substrait.Proto + Substrait.ProtoBuf — the cone
rule).

The five questions (notes/v3/01-core.md):
- root: Crossing (the wire) — the Proto plan model ↔ the proto bytes.
- carrier grade: the append-form law on the inDomain subdomain
  (patterns #2/#18); the exact-image policy (the full Kit.Codec grade)
  is the decode ladder's named follow-up.
- spine reading: Typed → Proto → Wire (this is the byte end).
- ladder rung: hand theorems of the small kind — each message's law is
  a chain through the primitive laws plus ONE fuel induction.
- gate row: the axiom report (Substrait is gated); SubstraitTests
  carries the round-trip sweeps + the negative controls + the
  composition pin.
-/
module


public import Substrait.Proto
public import Kit.Proto


@[expose] public section
namespace Substrait.Wire

open Substrait.Proto
open Kit.Proto
open Kit.Varint (encVarNat decVarNat? decVarNat?_encVarNat_append)

/-! ## the enum tables (ONE table read by both directions) -/

/-- The nullability enum's wire number. -/
def nullabilityNum : Nullability → Nat
  | .unspecified => 0
  | .nullable => 1
  | .required => 2

/-- The nullability enum's read-back. -/
def nullabilityOfNum? : Nat → Option Nullability
  | 0 => some .unspecified
  | 1 => some .nullable
  | 2 => some .required
  | _ => none

theorem nullabilityOfNum?_self (n : Nullability) :
    nullabilityOfNum? (nullabilityNum n) = some n := by
  cases n <;> rfl

/-- The join type's wire number (the upstream JoinType values). -/
def joinTypeNum : JoinType → Nat
  | .inner => 1
  | .outer => 2
  | .left => 3
  | .right => 4

/-- The join type's read-back. -/
def joinTypeOfNum? : Nat → Option JoinType
  | 1 => some .inner
  | 2 => some .outer
  | 3 => some .left
  | 4 => some .right
  | _ => none

theorem joinTypeOfNum?_self (jt : JoinType) :
    joinTypeOfNum? (joinTypeNum jt) = some jt := by
  cases jt <;> rfl

/-- The sort direction's wire number (the upstream SortField values). -/
def sortDirNum : SortDirection → Nat
  | .ascNullsFirst => 1
  | .descNullsFirst => 3

/-- The sort direction's read-back. -/
def sortDirOfNum? : Nat → Option SortDirection
  | 1 => some .ascNullsFirst
  | 3 => some .descNullsFirst
  | _ => none

theorem sortDirOfNum?_self (d : SortDirection) :
    sortDirOfNum? (sortDirNum d) = some d := by
  cases d <;> rfl

/-- The set op's wire number (the upstream SetRel values). -/
def setOpNum : SetOp → Nat
  | .unionDistinct => 5
  | .unionAll => 6

/-- The set op's read-back. -/
def setOpOfNum? : Nat → Option SetOp
  | 5 => some .unionDistinct
  | 6 => some .unionAll
  | _ => none

theorem setOpOfNum?_self (op : SetOp) :
    setOpOfNum? (setOpNum op) = some op := by
  cases op <;> rfl

/-- The write op's wire number (the upstream `WriteRel.WriteOp`
    values: UNSPECIFIED = 0 is never written — the typed layer's
    explicit-enum discipline). -/
def writeOpNum : WriteOp → Nat
  | .insert => 1
  | .delete => 2
  | .update => 3
  | .ctas => 4

/-- The write op's read-back. -/
def writeOpOfNum? : Nat → Option WriteOp
  | 1 => some .insert
  | 2 => some .delete
  | 3 => some .update
  | 4 => some .ctas
  | _ => none

theorem writeOpOfNum?_self (op : WriteOp) :
    writeOpOfNum? (writeOpNum op) = some op := by
  cases op <;> rfl

/-! ## the type wire (the Type kind oneof) -/

/-- The Type message's body: exactly one kind field, at the upstream
    oneof numbers. -/
def encPTypeBody : PType → List UInt8
  | .bool n => encLenBytes 1 (encVarField 2 (nullabilityNum n))
  | .i32 n => encLenBytes 5 (encVarField 2 (nullabilityNum n))
  | .i64 n => encLenBytes 7 (encVarField 2 (nullabilityNum n))
  | .string n => encLenBytes 12 (encVarField 2 (nullabilityNum n))
  | .list e n =>
      encLenBytes 27
        (encLenBytes 1 (encPTypeBody e) ++ encVarField 3 (nullabilityNum n))

/-- The scalar kind's inner message: the single nullability field. -/
def decNullBody? (payload : List UInt8) : Option Nullability :=
  match decEnumField? 2 nullabilityOfNum? payload with
  | some (Step.more n []) => some n
  | _ => none

/-- The scalar kind's inner law. -/
theorem decNullBody?_law (n : Nullability) :
    decNullBody? (encVarField 2 (nullabilityNum n)) = some n := by
  simp only [decNullBody?]
  rw [← List.append_nil (encVarField 2 (nullabilityNum n)),
    decEnumField?_encVarField_append 2 nullabilityOfNum? nullabilityNum
      nullabilityOfNum?_self n []]

/-- The Type body's read-back (fuel-bounded: the list kind nests; the
    element type's field-parse is INLINED — the recursive decoder cannot
    ride as a first-class value, the structural-recursion note at
    `decField?_encLenBytes_append`). -/
def decPTypeBody? : Nat → List UInt8 → Option (Step PType)
  | 0, _ => none
  | f + 1, bs =>
      match decOneof? bs with
      | none => none
      | some (1, payload, rest) =>
          match decNullBody? payload with
          | some n => some (Step.more (.bool n) rest)
          | none => none
      | some (5, payload, rest) =>
          match decNullBody? payload with
          | some n => some (Step.more (.i32 n) rest)
          | none => none
      | some (7, payload, rest) =>
          match decNullBody? payload with
          | some n => some (Step.more (.i64 n) rest)
          | none => none
      | some (12, payload, rest) =>
          match decNullBody? payload with
          | some n => some (Step.more (.string n) rest)
          | none => none
      | some (27, payload, rest) =>
          match decLenField? 1 payload with
          | some (Step.more pl rest') =>
              match decPTypeBody? f pl with
              | some (Step.more e []) =>
                  match decEnumField? 3 nullabilityOfNum? rest' with
                  | some (Step.more n []) => some (Step.more (.list e n) rest)
                  | _ => none
              | _ => none
          | _ => none
      | _ => none

/-- PATTERN #2 — the Type body's append-form law (unconditional: every
    PType of the narrow model has a wire spelling; the u64 REFUSAL is
    the TYPED layer's, upstream of the wire). -/
theorem decPTypeBody?_encPTypeBody_append : ∀ (fuel : Nat) (t : PType) (rest : List UInt8),
    (encPTypeBody t ++ rest).length + 1 ≤ fuel →
    decPTypeBody? fuel (encPTypeBody t ++ rest) = some (Step.more t rest) := by
  intro fuel
  induction fuel with
  | zero => intro t rest hfuel; exact absurd hfuel (by omega)
  | succ f ih =>
      intro t rest hfuel
      cases t with
      | bool n =>
          simp only [encPTypeBody, decPTypeBody?]
          rw [decOneof?_encLenBytes_append]
          simp [decNullBody?_law]
      | i32 n =>
          simp only [encPTypeBody, decPTypeBody?]
          rw [decOneof?_encLenBytes_append]
          simp [decNullBody?_law]
      | i64 n =>
          simp only [encPTypeBody, decPTypeBody?]
          rw [decOneof?_encLenBytes_append]
          simp [decNullBody?_law]
      | string n =>
          simp only [encPTypeBody, decPTypeBody?]
          rw [decOneof?_encLenBytes_append]
          simp [decNullBody?_law]
      | list e n =>
          simp only [encPTypeBody] at hfuel ⊢
          simp only [decPTypeBody?]
          rw [decOneof?_encLenBytes_append]
          simp only [reduceCtorEq]
          -- the element type's field: the inlined parse at fuel f
          have hfull : (encPTypeBody e).length + 1 ≤ f :=
            encLenBytes_fuel_split_wrap (N := 27) (M := 1) (pre := [])
              (inner := encPTypeBody e) (tail := encVarField 3 (nullabilityNum n))
              (rest := rest) hfuel
          rw [decLenField?_encLenBytes_append]
          dsimp only
          rw [← List.append_nil (encPTypeBody e), ih e [] (by simpa using hfull)]
          rw [← List.append_nil (encVarField 3 (nullabilityNum n)),
            decEnumField?_encVarField_append 3 nullabilityOfNum? nullabilityNum
              nullabilityOfNum?_self n []]

/-! ## the literal wire (the Literal oneof + the nullable field) -/

/-- The Literal body: the oneof (boolean = 1 / i32 = 5 / i64 = 7 /
    string = 12, at the upstream numbers) + the nullable field (50,
    always written — the canonical dialect). -/
def encLiteralBody (l : Literal) : List UInt8 :=
  (match l.literalType with
    | .bool b => encLenBytes 1 (encVarField 1 (if b then 1 else 0))
    | .i32 v => encLenBytes 5 (encI64 v)
    | .i64 v => encLenBytes 7 (encI64 v)
    | .string s => encLenBytes 12 (encStr s))
  ++ encVarField 50 (if l.nullable then 1 else 0)

/-- The Literal body's read-back (the nullable field is REQUIRED — the
    canonical dialect). -/
def decLiteralBody? : Nat → List UInt8 → Option (Step Literal)
  | _, bs =>
      match decOneof? bs with
      | none => none
      | some (1, payload, rest) =>
          match decBoolField? 1 payload with
          | some (Step.more b []) =>
              match decBoolField? 50 rest with
              | some (Step.more nbl rest') =>
                  some (Step.more { literalType := .bool b, nullable := nbl } rest')
              | _ => none
          | _ => none
      | some (5, payload, rest) =>
          match decI64? payload with
          | some (v, []) =>
              match decBoolField? 50 rest with
              | some (Step.more nbl rest') =>
                  some (Step.more { literalType := .i32 v, nullable := nbl } rest')
              | _ => none
          | _ => none
      | some (7, payload, rest) =>
          match decI64? payload with
          | some (v, []) =>
              match decBoolField? 50 rest with
              | some (Step.more nbl rest') =>
                  some (Step.more { literalType := .i64 v, nullable := nbl } rest')
              | _ => none
          | _ => none
      | some (12, payload, rest) =>
          match bytesToStr? payload with
          | some s =>
              match decBoolField? 50 rest with
              | some (Step.more nbl rest') =>
                  some (Step.more { literalType := .string s, nullable := nbl } rest')
              | _ => none
          | none => none
      | _ => none

/-! ## the inDomain discipline (pattern #18's admissible subdomain) -/

/-- The literal payloads' admissible ranges: the two's-complement
    32/64-bit faces (the off-domain truncation is the pinned loss). -/
def inDomainLitType : LiteralType → Bool
  | .bool _ => true
  | .i32 v => -2147483648 ≤ v && v < 2147483648
  | .i64 v => -9223372036854775808 ≤ v && v < 9223372036854775808
  | .string s => inDomainStr s

/-- The literal's gate: the payload's range. -/
def inDomainLiteral (l : Literal) : Bool := inDomainLitType l.literalType

-- The expressions' gate (the list walk — the mutual sibling; the
-- higher-order `List.all` breaks the structural-recursion check, and a
-- docstring cannot precede a `mutual` block — the mechanics notes).
mutual
def inDomainExpr : Expression → Bool
  | .literal l => inDomainLiteral l
  | .field _ => true
  | .scalarFunction nm args _ =>
      inDomainStr nm && inDomainExprs args

def inDomainExprs : List Expression → Bool
  | [] => true
  | e :: es => inDomainExpr e && inDomainExprs es
end

/-- The list gate's per-element face (the walk's read-back). -/
theorem inDomainExprs_self : ∀ (xs : List Expression) (x : Expression), x ∈ xs →
    inDomainExprs xs = true → inDomainExpr x = true := by
  intro xs
  induction xs with
  | nil => intro x h; cases h
  | cons y tl ih =>
      intro x h htrue
      simp only [inDomainExprs, Bool.and_eq_true] at htrue
      rcases List.mem_cons.mp h with rfl | htl
      · exact htrue.1
      · exact ih x htl htrue.2

/-- The sort key's gate: the ordering expression's. -/
def inDomainSortField (sf : SortField) : Bool := inDomainExpr sf.expr

/-- The sort keys' gate (the list walk). -/
def inDomainSortFields : List SortField → Bool
  | [] => true
  | sf :: sfs => inDomainSortField sf && inDomainSortFields sfs

/-- The sort-keys gate's per-element face (the walk's read-back). -/
theorem inDomainSortFields_self : ∀ (xs : List SortField) (k : SortField), k ∈ xs →
    inDomainSortFields xs = true → inDomainExpr k.expr = true := by
  intro xs
  induction xs with
  | nil => intro k h; cases h
  | cons y tl ih =>
      intro k h htrue
      simp only [inDomainSortFields, Bool.and_eq_true] at htrue
      rcases List.mem_cons.mp h with rfl | htl
      · exact htrue.1
      · exact ih k htl htrue.2

/-- The rel's gate: every literal payload's range + every string's
    ASCII face, over the whole tree (the fetch window's counts ride the
    literal-i64 face — below 2^63). -/
def inDomainRel : Rel → Bool
  | .read rt bs =>
      (match rt with | .namedTable nms => inDomainStrs nms)
      && (match bs with | some s => inDomainStrs s.names | none => true)
  | .filter c i => inDomainExpr c && inDomainRel i
  | .project es i => inDomainExprs es && inDomainRel i
  | .join _ l r c => inDomainRel l && inDomainRel r && inDomainExpr c
  | .aggregate gs ms i =>
      inDomainExprs gs && inDomainExprs ms && inDomainRel i
  | .sort ks i => inDomainSortFields ks && inDomainRel i
  | .fetch limit offset i =>
      (limit.all (· < 9223372036854775808))
        && (offset.all (· < 9223372036854775808)) && inDomainRel i
  | .set _ l r => inDomainRel l && inDomainRel r
  | .cross l r => inDomainRel l && inDomainRel r
  | .write nms _ ts i =>
      inDomainStrs nms && inDomainStrs ts.names && inDomainRel i

/-- The plan relation's gate. -/
def inDomainPlanRel : PlanRel → Bool
  | .rel r => inDomainRel r
  | .root nms r => nms.all inDomainStr && inDomainRel r

/-- THE PLAN'S GATE (the emission boundary's check — pattern #18). -/
def inDomainPlan (p : Plan) : Bool :=
  p.relations.all inDomainPlanRel && p.functions.all inDomainStr

/-! ## the literal's law (inDomain-conditional, no induction) -/

/-- PATTERN #2 — the Literal body's append-form law ON THE ADMISSIBLE
    SUBDOMAIN (the int ranges + the ASCII strings; the off-domain face
    is the pinned loss, SubstraitTests). -/
theorem decLiteralBody?_encLiteralBody_append : ∀ (fuel : Nat) (l : Literal) (rest : List UInt8),
    inDomainLiteral l →
    decLiteralBody? fuel (encLiteralBody l ++ rest) = some (Step.more l rest) := by
  intro fuel l rest hd
  cases l with
  | mk ltype nbl =>
      cases ltype with
      | bool b =>
          simp only [encLiteralBody, decLiteralBody?, List.append_assoc]
          rw [decOneof?_encLenBytes_append]
          simp [decBoolField?_encVarField, decBoolField?_encVarField_append]
      | i32 v =>
          simp [inDomainLiteral, inDomainLitType] at hd
          have hlo : -9223372036854775808 ≤ v := by have h1 := hd.1; omega
          have hhi : v < 9223372036854775808 := by have h1 := hd.2; omega
          simp only [encLiteralBody, decLiteralBody?, List.append_assoc]
          rw [decOneof?_encLenBytes_append]
          simp [decI64?_encI64 v hlo hhi, decBoolField?_encVarField,
            decBoolField?_encVarField_append]
      | i64 v =>
          simp [inDomainLiteral, inDomainLitType] at hd
          have hlo : -9223372036854775808 ≤ v := by have h1 := hd.1; omega
          have hhi : v < 9223372036854775808 := by have h1 := hd.2; omega
          simp only [encLiteralBody, decLiteralBody?, List.append_assoc]
          rw [decOneof?_encLenBytes_append]
          simp [decI64?_encI64 v hlo hhi, decBoolField?_encVarField,
            decBoolField?_encVarField_append]
      | string s =>
          simp [inDomainLiteral, inDomainLitType] at hd
          have hasc : s.toList.all (fun c => c.toNat < 128) := hd
          simp only [encLiteralBody, decLiteralBody?, List.append_assoc]
          rw [decOneof?_encLenBytes_append]
          simp [decFieldStr?_encLenBytes_append, bytesToStr?_encStr s hasc,
            decBoolField?_encVarField_append]

/-! ## the field-reference wire (the selection's three-level chain) -/

/-- The FieldReference body: the direct-reference chain at the upstream
    numbers — `direct_reference = 1` (ReferenceSegment) →
    `struct_field = 2` (StructField) → `field = 1` (the ordinal). -/
def encFieldRefBody (ref : FieldReference) : List UInt8 :=
  encLenBytes 1 (encLenBytes 2 (encVarField 1 ref.ordinal))

/-- The FieldReference body's read-back. -/
def decFieldRefBody? : Nat → List UInt8 → Option (Step FieldReference)
  | _, bs =>
      match decOneof? bs with
      | some (1, payload, rest) =>
          match decLenField? 2 payload with
          | some (Step.more pl rest') =>
              match decVarField? 1 pl with
              | some (Step.more v []) => some (Step.more { ordinal := v } rest)
              | _ => none
          | _ => none
      | _ => none

/-- PATTERN #2 — the FieldReference body's append-form law
    (unconditional). -/
theorem decFieldRefBody?_encFieldRefBody_append : ∀ (fuel : Nat) (ref : FieldReference)
    (rest : List UInt8),
    decFieldRefBody? fuel (encFieldRefBody ref ++ rest) = some (Step.more ref rest) := by
  intro fuel ref rest
  simp only [encFieldRefBody, decFieldRefBody?]
  rw [decOneof?_encLenBytes_append]
  simp only [reduceCtorEq]
  rw [← List.append_nil (encLenBytes 2 (encVarField 1 ref.ordinal)),
    decLenField?_encLenBytes_append]
  dsimp only
  rw [← List.append_nil (encVarField 1 ref.ordinal),
    decVarField?_encVarField_append]

/-! ## the expression wire (the rex_type oneof) -/

/- The Expression body: the rex_type oneof at the upstream numbers
    (literal = 1 / selection = 2 / scalar_function = 3). The
    scalar_function face carries THE NAMED DIVERGENCE: the seed's
    function NAME rides field 9 (upstream field 1 is the
    `function_reference` anchor uint32 — the anchor table is not yet
    built); the arguments ride field 4 (each a FunctionArgument whose
    `value = 3` Expression); the output type rides field 3. The
    arguments' walk is the MUTUAL sibling (the element call is not a
    direct ctor argument — the list walk keeps the recursion
    structural); a docstring cannot precede a `mutual` block — the
    mechanics note. -/
mutual
def encExpressionBody : Expression → List UInt8
  | .literal l => encLenBytes 1 (encLiteralBody l)
  | .field ref => encLenBytes 2 (encFieldRefBody ref)
  | .scalarFunction nm args out =>
      encLenBytes 3
        (encLenBytes 9 (encStr nm) ++
          encLenBytes 3 (encPTypeBody out) ++
          encArgs args)

def encArgs : List Expression → List UInt8
  | [] => []
  | e :: es => encLenBytes 4 (encLenBytes 3 (encExpressionBody e)) ++ encArgs es
end

/-- The Expression body's read-back (fuel-bounded: the arguments
    nest). -/
def decExpressionBody? : Nat → List UInt8 → Option (Step Expression)
  | 0, _ => none
  | f + 1, bs =>
      match decOneof? bs with
      | none => none
      | some (1, payload, rest) =>
          match decLiteralBody? f payload with
          | some (Step.more l []) => some (Step.more (.literal l) rest)
          | _ => none
      | some (2, payload, rest) =>
          match decFieldRefBody? f payload with
          | some (Step.more r []) => some (Step.more (.field r) rest)
          | _ => none
      | some (3, payload, rest) =>
          match decFieldStr? 9 payload with
          | some (Step.more nm rest1) =>
              match decLenField? 3 rest1 with
              | some (Step.more outPl rest2) =>
                  match decPTypeBody? f outPl with
                  | some (Step.more out []) =>
                      match decRep?
                          (fun el =>
                            match decLenField? 4 el with
                            | some (Step.more argl rest'') =>
                                match decLenField? 3 argl with
                                | some (Step.more argpl rest''') =>
                                    match decExpressionBody? f argpl with
                                    | some (Step.more a []) =>
                                        some (Step.more a rest'')
                                    | _ => none
                                | _ => none
                            | some (Step.stop rest'') => some (Step.stop rest'')
                            | none => none)
                          (rest2.length + 1) rest2 with
                      | some (args, []) =>
                          some (Step.more (.scalarFunction nm args out) rest)
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | _ => none

/-- The arg-element's face (the rep's element decoder, NAMED for the
    law's statement — the same parse the decoder inlines; the stop face
    passes through for the repeat's end). -/
def decArgElem? (f : Nat) (el : List UInt8) : Option (Step Expression) :=
  match decLenField? 4 el with
  | some (Step.more argl rest'') =>
      match decLenField? 3 argl with
      | some (Step.more argpl rest''') =>
          match decExpressionBody? f argpl with
          | some (Step.more a []) => some (Step.more a rest'')
          | _ => none
      | _ => none
  | some (Step.stop rest'') => some (Step.stop rest'')
  | none => none

/-- The arg element's encoding (the rep's element face). -/
def encArgElem (e : Expression) : List UInt8 :=
  encLenBytes 4 (encLenBytes 3 (encExpressionBody e))

/-- The arg element's read-back's NIL face (used only in tests; the
    law's face is the corollaries below). -/

theorem encArgs_eq_encRep (args : List Expression) :
    encArgs args = encRep encArgElem args := by
  induction args with
  | nil => rfl
  | cons e es ih =>
      simp only [encArgs, encRep, encArgElem, ih]

/-- The Literal body's NIL face. -/
theorem decLiteralBody?_encLiteralBody (fuel : Nat) (l : Literal) (hd : inDomainLiteral l) :
    decLiteralBody? fuel (encLiteralBody l) = some (Step.more l []) := by
  rw [← List.append_nil (encLiteralBody l),
    decLiteralBody?_encLiteralBody_append fuel l [] hd]

/-- The FieldReference body's NIL face. -/
theorem decFieldRefBody?_encFieldRefBody (fuel : Nat) (ref : FieldReference) :
    decFieldRefBody? fuel (encFieldRefBody ref) = some (Step.more ref []) := by
  rw [← List.append_nil (encFieldRefBody ref),
    decFieldRefBody?_encFieldRefBody_append fuel ref []]

/-- The inline arg-element face IS `decArgElem?` (the decoder's lambda,
    named for the law; the bodies are syntactically identical). -/
theorem decArgElem?_eq (f : Nat) :
    (fun el =>
      match decLenField? 4 el with
      | some (Step.more argl rest'') =>
          match decLenField? 3 argl with
          | some (Step.more argpl rest''') =>
              match decExpressionBody? f argpl with
              | some (Step.more a []) => some (Step.more a rest'')
              | _ => none
          | _ => none
      | some (Step.stop rest'') => some (Step.stop rest'')
      | none => none) = decArgElem? f := rfl

/-- PATTERN #2 — the Expression body's law, as ONE induction over the
    fuel carrying the THREE faces together (the append-form law, the
    NIL face, and the arg-element face — the mutual dependency between
    the law and the arg-element face dissolves into the induction's
    parts; each part cites the IH's parts and the step's own earlier
    parts). -/
theorem decExpressionBody?_law : ∀ (fuel : Nat),
    (∀ (e : Expression) (rest : List UInt8), inDomainExpr e = true →
      (encExpressionBody e ++ rest).length + 1 ≤ fuel →
      decLenField? 4 rest = some (Step.stop rest) →
      decExpressionBody? fuel (encExpressionBody e ++ rest) = some (Step.more e rest))
    ∧ (∀ (e : Expression), inDomainExpr e = true →
      (encExpressionBody e).length + 1 ≤ fuel →
      decExpressionBody? fuel (encExpressionBody e) = some (Step.more e []))
    ∧ (∀ (e : Expression) (r : List UInt8), inDomainExpr e = true →
      (encExpressionBody e).length + 1 ≤ fuel →
      decArgElem? fuel (encArgElem e ++ r) = some (Step.more e r)) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro e rest _ hfuel _; exact absurd hfuel (by omega)
      · intro e _ hfuel; exact absurd hfuel (by omega)
      · intro e r _ hfuel; exact absurd hfuel (by omega)
  | succ f ih =>
      have ih1 := ih.1
      have ih2 := ih.2.1
      have ih3 := ih.2.2
      -- part 1: the append-form law (the rep's helem cites ih3)
      have part1 : ∀ (e : Expression) (rest : List UInt8), inDomainExpr e = true →
          (encExpressionBody e ++ rest).length + 1 ≤ f + 1 →
          decLenField? 4 rest = some (Step.stop rest) →
          decExpressionBody? (f + 1) (encExpressionBody e ++ rest)
            = some (Step.more e rest) := by
        intro e rest hd hfuel hend
        cases e with
        | literal l =>
            have hd1 : inDomainLiteral l = true := by
              have h := hd; simp [inDomainExpr] at h; exact h
            have hbound : (encLiteralBody l).length + 1 ≤ f :=
              encLenBytes_fuel_split (M := 1) (pre := []) (inner := encLiteralBody l)
                (tail := rest) hfuel
            simp only [encExpressionBody, decExpressionBody?]
            rw [decOneof?_encLenBytes_append]
            simp only [reduceCtorEq]
            simp [decLiteralBody?_encLiteralBody f l hd1]
        | field ref =>
            have hbound : (encFieldRefBody ref).length + 1 ≤ f :=
              encLenBytes_fuel_split (M := 2) (pre := []) (inner := encFieldRefBody ref)
                (tail := rest) hfuel
            simp only [encExpressionBody, decExpressionBody?]
            rw [decOneof?_encLenBytes_append]
            simp only [reduceCtorEq]
            simp [decFieldRefBody?_encFieldRefBody f ref]
        | scalarFunction nm args out =>
            -- the gates: the name's ASCII + the arguments' inDomain
            have hd1 : inDomainStr nm = true := by
              have h := hd; simp [inDomainExpr] at h; exact h.1
            have hd2 : inDomainExprs args = true := by
              have h := hd; simp [inDomainExpr] at h; exact h.2
            -- the fuel bookkeeping: the wraps' ≥2-byte costs, chained
            -- (the length-level arithmetic by `grind` (06 §12) — the
            -- `encLenBytes_ge` family named, the List-length normals
            -- named, the goal facts kept in context)
            have hpayLen : (encLenBytes 9 (encStr nm) ++ encLenBytes 3 (encPTypeBody out)
                  ++ encArgs args).length
                = (encLenBytes 9 (encStr nm)).length
                  + ((encLenBytes 3 (encPTypeBody out)).length + (encArgs args).length) := by
              grind [List.length_append]
            have h1 : (encLenBytes 3 (encLenBytes 9 (encStr nm)
                    ++ encLenBytes 3 (encPTypeBody out) ++ encArgs args)
                  ++ rest).length + 1 ≤ f + 1 := hfuel
            have h1' : (encLenBytes 3 (encLenBytes 9 (encStr nm)
                    ++ encLenBytes 3 (encPTypeBody out) ++ encArgs args)).length
                + rest.length + 1 ≤ f + 1 := by simpa [List.length_append] using h1
            have hw := encLenBytes_ge 3 (encLenBytes 9 (encStr nm)
                    ++ encLenBytes 3 (encPTypeBody out) ++ encArgs args)
            have hw9 := encLenBytes_ge 9 (encStr nm)
            have hw3 := encLenBytes_ge 3 (encPTypeBody out)
            have hout : (encPTypeBody out ++ []).length + 1 ≤ f := by
              grind [encLenBytes_ge, List.length_append, List.append_nil]
            have hargs : ∀ x ∈ args, (encExpressionBody x).length + 1 ≤ f := by
              intro x hx
              have hmem := encRep_mem_le encArgElem args x hx
              rw [← encArgs_eq_encRep] at hmem
              grind [encLenBytes_ge, encArgElem, List.length_append]
            have hend2 : decArgElem? f rest = some (Step.stop rest) := by
              simp only [decArgElem?]
              rw [hend]
            simp only [encExpressionBody, decExpressionBody?]
            rw [decOneof?_encLenBytes_append]
            simp only [reduceCtorEq]
            rw [List.append_assoc]
            rw [decFieldStr?_encLenBytes_append 9 nm
              (encLenBytes 3 (encPTypeBody out) ++ encArgs args) hd1]
            dsimp only
            rw [decLenField?_encLenBytes_append]
            dsimp only
            rw [← List.append_nil (encPTypeBody out),
              decPTypeBody?_encPTypeBody_append f out [] hout]
            dsimp only
            rw [encArgs_eq_encRep]
            rw [← List.append_nil (encRep encArgElem args)]
            rw [decArgElem?_eq f]
            rw [decRep?_encRep_append (decArgElem? f) encArgElem
              (fun x => inDomainExpr x = true ∧ (encExpressionBody x).length + 1 ≤ f)
              (fun x hr hx => ih3 x hr hx.1 hx.2)
              (fun x => encLenBytes_pos 4 _)
              (List.nil : List UInt8) (by rfl)]
            · intro x hx
              exact ⟨inDomainExprs_self args x hx hd2, hargs x hx⟩
            · omega
      refine ⟨part1, ?_, ?_⟩
      · -- part 2: the NIL face (part 1 at the empty suffix)
        intro e hd hb
        have hstop : decLenField? 4 [] = some (Step.stop []) := rfl
        have h1 := part1 e [] hd (by simpa [List.length_append] using hb) hstop
        simpa using h1
      · -- part 3: the arg element (part 1 at THIS fuel, the empty suffix)
        intro e r hd hb
        have hstop : decLenField? 4 [] = some (Step.stop []) := rfl
        simp only [decArgElem?, encArgElem]
        rw [decLenField?_encLenBytes_append]
        dsimp only
        rw [← List.append_nil (encLenBytes 3 (encExpressionBody e)),
          decLenField?_encLenBytes_append]
        dsimp only
        rw [← List.append_nil (encExpressionBody e)]
        have hbound : (encExpressionBody e ++ []).length + 1 ≤ f + 1 :=
          by simpa [List.length_append] using hb
        rw [part1 e [] hd hbound hstop]

/-- The Expression body's NIL face (part 2's corollary). -/
theorem decExpressionBody?_encExpressionBody (fuel : Nat) (e : Expression)
    (hd : inDomainExpr e = true) (hb : (encExpressionBody e).length + 1 ≤ fuel) :
    decExpressionBody? fuel (encExpressionBody e) = some (Step.more e []) :=
  (decExpressionBody?_law fuel).2.1 e hd hb


/-! ## the sort-key wire (the SortField body) -/

/-- The SortField body: the ordering expression (field 1) + the
    direction enum (field 2, at the upstream SortDirection values). -/
def encSortFieldBody (sf : SortField) : List UInt8 :=
  encLenBytes 1 (encExpressionBody sf.expr) ++ encVarField 2 (sortDirNum sf.direction)

/-- The SortField body's read-back. -/
def decSortFieldBody? : Nat → List UInt8 → Option (Step SortField)
  | f, bs =>
      match decLenField? 1 bs with
      | some (Step.more pl rest') =>
          match decExpressionBody? f pl with
          | some (Step.more e []) =>
              match decEnumField? 2 sortDirOfNum? rest' with
              | some (Step.more d rest2) =>
                  some (Step.more { expr := e, direction := d } rest2)
              | _ => none
          | _ => none
      | _ => none

/-- PATTERN #2 — the SortField body's append-form law (inDomain + the
    fuel). -/
theorem decSortFieldBody?_encSortFieldBody_append : ∀ (fuel : Nat) (sf : SortField)
    (rest : List UInt8), inDomainExpr sf.expr = true →
    (encSortFieldBody sf ++ rest).length + 1 ≤ fuel →
    decSortFieldBody? fuel (encSortFieldBody sf ++ rest) = some (Step.more sf rest) := by
  intro fuel sf rest hd hfuel
  cases sf with
  | mk e d =>
      simp only [encSortFieldBody, List.append_assoc] at hfuel
      have hbound : (encExpressionBody e).length + 1 ≤ fuel :=
        encLenBytes_fuel_split_at (M := 1) (pre := []) (inner := encExpressionBody e)
          (tail := encVarField 2 (sortDirNum d) ++ rest) hfuel
      simp only [encSortFieldBody, decSortFieldBody?, List.append_assoc]
      rw [decLenField?_encLenBytes_append]
      dsimp only
      rw [decExpressionBody?_encExpressionBody fuel e hd hbound]
      rw [decEnumField?_encVarField_append 2 sortDirOfNum? sortDirNum
        sortDirOfNum?_self d rest]

/-! ## the named-struct wire (the read's base schema) -/

/-- The NamedStruct body: the column names (repeated field 1) + the
    struct type (field 2, whose payload is the repeated field-1 types —
    the upstream `NamedStruct { names = 1, struct = 2 { types = 1 } }`). -/
def encNamedStructBody (ns : NamedStruct) : List UInt8 :=
  encRep (fun n => encLenBytes 1 (encStr n)) ns.names
    ++ encLenBytes 2 (encRep (fun t => encLenBytes 1 (encPTypeBody t)) ns.fields)

/-- The NamedStruct body's read-back (the types' rep lives inside the
    struct field's payload — fully consumed there). -/
def decNamedStructBody? : Nat → List UInt8 → Option (Step NamedStruct)
  | f, bs =>
      match decRep? (decFieldStr? 1) (bs.length + 1) bs with
      | some (nms, rest1) =>
          match decLenField? 2 rest1 with
          | some (Step.more pl rest2) =>
              match decRep? (decField? 1 decPTypeBody? f) (pl.length + 1) pl with
              | some (ts, []) => some (Step.more { fields := ts, names := nms } rest2)
              | _ => none
          | _ => none
      | _ => none

/-- The gate's NamedStruct face: the column names' ASCII face. -/
def inDomainNamedStruct (ns : NamedStruct) : Bool := inDomainStrs ns.names

/-- PATTERN #2 — the NamedStruct body's append-form law (the names'
    ASCII + the fuel; the struct field is last — the suffix is
    unconditional). -/
theorem decNamedStructBody?_encNamedStructBody_append : ∀ (fuel : Nat) (ns : NamedStruct)
    (rest : List UInt8), inDomainNamedStruct ns = true →
    (encNamedStructBody ns ++ rest).length + 1 ≤ fuel →
    decNamedStructBody? fuel (encNamedStructBody ns ++ rest) = some (Step.more ns rest) := by
  intro fuel ns rest hd hfuel
  cases ns with
  | mk fields names =>
      have hd1 : inDomainStrs names = true := by
        have h := hd; simp [inDomainNamedStruct] at h; exact h
      -- the struct field's tag face: field 2, wire type wtLen (the
      -- names rep's stop face — 2 ≠ 1)
      have htag2 : decTag? (encLenBytes 2 (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields) ++ rest)
          = some (2, wtLen, encVarNat (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields).length
            ++ (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields ++ rest)) := by
        rw [show encLenBytes 2 (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields) ++ rest
              = encTag 2 wtLen
                ++ (encVarNat (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields).length
                  ++ (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields ++ rest))
          from by simp only [encLenBytes, List.append_assoc]]
        exact decTag?_encTag_append 2 wtLen (by unfold wtLen; decide)
          (encVarNat (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields).length
            ++ (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields ++ rest))
      have hendNames : decFieldStr? 1
          (encLenBytes 2 (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields) ++ rest)
          = some (Step.stop
            (encLenBytes 2 (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields) ++ rest)) := by
        apply decFieldStr?_stop
        · intro hh
          rw [htag2] at hh
          exact absurd hh (by simp)
        · intro f' w' r htag
          rw [htag2] at htag
          have hf2 : f' = 2 := by
            have h1 : 2 = f' :=
              congrArg (fun t : Nat × Nat × List UInt8 => t.1) (Option.some.inj htag)
            exact h1.symm
          exact fun hh => absurd (hh.1.symm.trans hf2) (by decide)
      simp only [encNamedStructBody, decNamedStructBody?, List.append_assoc]
      have hnames : decRep? (decFieldStr? 1)
          ((encRep (fun n => encLenBytes 1 (encStr n)) names
              ++ (encLenBytes 2 (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields)
                ++ rest)).length + 1)
          (encRep (fun n => encLenBytes 1 (encStr n)) names
            ++ (encLenBytes 2 (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields) ++ rest))
          = some (names,
            encLenBytes 2 (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields) ++ rest) :=
        decRep?_encRep_append (decFieldStr? 1)
          (fun n => encLenBytes 1 (encStr n))
          (fun s => inDomainStr s = true)
          (fun s r h => decFieldStr?_encLenBytes_append 1 s r h)
          (fun s => encLenBytes_pos 1 _)
          _ hendNames _ names
          (fun s hs => inDomainStrs_self names s hs hd1)
          (by simp only [List.length_append]; omega)
      rw [hnames]
      dsimp only
      rw [decLenField?_encLenBytes_append]
      dsimp only
      rw [← List.append_nil (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields)]
      have htypes : decRep? (decField? 1 decPTypeBody? fuel)
          ((encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields ++ []).length + 1)
          (encRep (fun t => encLenBytes 1 (encPTypeBody t)) fields ++ [])
          = some (fields, []) :=
        decRep?_encRep_append (decField? 1 decPTypeBody? fuel)
          (fun t => encLenBytes 1 (encPTypeBody t))
          (fun t => (encPTypeBody t).length + 1 ≤ fuel)
          (fun t r h => decField?_encLenBytes_append 1 encPTypeBody decPTypeBody? fuel
            (fun a rest hrest => decPTypeBody?_encPTypeBody_append fuel a rest hrest)
            t h r)
          (fun t => encLenBytes_pos 1 _)
          [] (by rfl) _ fields
          (fun t ht => by
            have hmem := encRep_mem_le (fun t => encLenBytes 1 (encPTypeBody t)) fields t ht
            grind [encLenBytes_ge, encNamedStructBody, List.length_append])
          (by simp)
      rw [htypes]

/-! ## the relation wire (the rel_type oneof) -/

/-- The expression ELEMENT face (a repeated-Expression field whose
    elements are field-3 wrapped bodies — project's expressions and
    the aggregate's groupings ride 3). -/
def encExprElem (e : Expression) : List UInt8 := encLenBytes 3 (encExpressionBody e)

def decExprElem? (fuel : Nat) (el : List UInt8) : Option (Step Expression) :=
  match decLenField? 3 el with
  | some (Step.more pl rest) =>
      match decExpressionBody? fuel pl with
      | some (Step.more e []) => some (Step.more e rest)
      | _ => none
  | some (Step.stop rest) => some (Step.stop rest)
  | none => none

/-- PATTERN #2 — the expression element's append-form law. -/
theorem decExprElem?_encExprElem_append (fuel : Nat) (e : Expression) (r : List UInt8)
    (hd : inDomainExpr e = true) (hb : (encExpressionBody e).length + 1 ≤ fuel) :
    decExprElem? fuel (encExprElem e ++ r) = some (Step.more e r) := by
  simp only [encExprElem, decExprElem?]
  rw [decLenField?_encLenBytes_append]
  dsimp only
  rw [decExpressionBody?_encExpressionBody fuel e hd hb]

/-- The expression element's NIL stop face (the rep law's `hend` at a
    body's end). -/
theorem decExprElem?_stop_nil (fuel : Nat) :
    decExprElem? fuel [] = some (Step.stop []) := rfl

/-- The measure ELEMENT face (the aggregate's measures ride field 4 as
    raw Expression messages — the seed's named divergence). -/
def encMeasureElem (e : Expression) : List UInt8 := encLenBytes 4 (encExpressionBody e)

def decMeasureElem? (fuel : Nat) (el : List UInt8) : Option (Step Expression) :=
  match decLenField? 4 el with
  | some (Step.more pl rest) =>
      match decExpressionBody? fuel pl with
      | some (Step.more e []) => some (Step.more e rest)
      | _ => none
  | some (Step.stop rest) => some (Step.stop rest)
  | none => none

/-- PATTERN #2 — the measure element's append-form law. -/
theorem decMeasureElem?_encMeasureElem_append (fuel : Nat) (e : Expression) (r : List UInt8)
    (hd : inDomainExpr e = true) (hb : (encExpressionBody e).length + 1 ≤ fuel) :
    decMeasureElem? fuel (encMeasureElem e ++ r) = some (Step.more e r) := by
  simp only [encMeasureElem, decMeasureElem?]
  rw [decLenField?_encLenBytes_append]
  dsimp only
  rw [decExpressionBody?_encExpressionBody fuel e hd hb]

/-- The measure element's NIL stop face. -/
theorem decMeasureElem?_stop_nil (fuel : Nat) :
    decMeasureElem? fuel [] = some (Step.stop []) := rfl

/-- The expression rep's NIL face (the rep law at the empty suffix —
    the payload-internal reps' termination face). -/
theorem decRep?_encExprElem_nil (f : Nat) (fuel : Nat) (es : List Expression)
    (hall : ∀ e ∈ es, inDomainExpr e = true ∧ (encExpressionBody e).length + 1 ≤ f)
    (hfuel : (encRep encExprElem es).length + 1 ≤ fuel) :
    decRep? (decExprElem? f) fuel (encRep encExprElem es) = some (es, []) := by
  rw [← List.append_nil (encRep encExprElem es)]
  exact decRep?_encRep_append (decExprElem? f) encExprElem
    (fun e => inDomainExpr e = true ∧ (encExpressionBody e).length + 1 ≤ f)
    (fun e r h => decExprElem?_encExprElem_append f e r h.1 h.2)
    (fun e => encLenBytes_pos 3 _)
    [] (decExprElem?_stop_nil f) fuel es hall
    (by simpa [List.length_append] using hfuel)

/-- The measure rep's NIL face. -/
theorem decRep?_encMeasureElem_nil (f : Nat) (fuel : Nat) (ms : List Expression)
    (hall : ∀ e ∈ ms, inDomainExpr e = true ∧ (encExpressionBody e).length + 1 ≤ f)
    (hfuel : (encRep encMeasureElem ms).length + 1 ≤ fuel) :
    decRep? (decMeasureElem? f) fuel (encRep encMeasureElem ms) = some (ms, []) := by
  rw [← List.append_nil (encRep encMeasureElem ms)]
  exact decRep?_encRep_append (decMeasureElem? f) encMeasureElem
    (fun e => inDomainExpr e = true ∧ (encExpressionBody e).length + 1 ≤ f)
    (fun e r h => decMeasureElem?_encMeasureElem_append f e r h.1 h.2)
    (fun e => encLenBytes_pos 4 _)
    [] (decMeasureElem?_stop_nil f) fuel ms hall
    (by simpa [List.length_append] using hfuel)

/-- The sort-key ELEMENT face (the sorts rep's elements are field-3
    wrapped SortField bodies). -/
def encSortElem (k : SortField) : List UInt8 := encLenBytes 3 (encSortFieldBody k)

def decSortElem? (fuel : Nat) (el : List UInt8) : Option (Step SortField) :=
  match decLenField? 3 el with
  | some (Step.more pl rest) =>
      match decSortFieldBody? fuel pl with
      | some (Step.more k []) => some (Step.more k rest)
      | _ => none
  | some (Step.stop rest) => some (Step.stop rest)
  | none => none

/-- PATTERN #2 — the sort-key element's append-form law. -/
theorem decSortElem?_encSortElem_append (fuel : Nat) (k : SortField) (r : List UInt8)
    (hd : inDomainExpr k.expr = true) (hb : (encSortFieldBody k).length + 1 ≤ fuel) :
    decSortElem? fuel (encSortElem k ++ r) = some (Step.more k r) := by
  simp only [encSortElem, decSortElem?]
  rw [decLenField?_encLenBytes_append]
  dsimp only
  have hbound : (encSortFieldBody k ++ []).length + 1 ≤ fuel := by simpa using hb
  have hsf : decSortFieldBody? fuel (encSortFieldBody k) = some (Step.more k []) := by
    simpa using decSortFieldBody?_encSortFieldBody_append fuel k [] hd hbound
  rw [hsf]

/-- The sort-key element's NIL stop face. -/
theorem decSortElem?_stop_nil (fuel : Nat) :
    decSortElem? fuel [] = some (Step.stop []) := rfl

/-- The sort-key rep's NIL face. -/
theorem decRep?_encSortElem_nil (f : Nat) (fuel : Nat) (ks : List SortField)
    (hall : ∀ k ∈ ks, inDomainExpr k.expr = true ∧ (encSortFieldBody k).length + 1 ≤ f)
    (hfuel : (encRep encSortElem ks).length + 1 ≤ fuel) :
    decRep? (decSortElem? f) fuel (encRep encSortElem ks) = some (ks, []) := by
  rw [← List.append_nil (encRep encSortElem ks)]
  exact decRep?_encRep_append (decSortElem? f) encSortElem
    (fun k => inDomainExpr k.expr = true ∧ (encSortFieldBody k).length + 1 ≤ f)
    (fun k r h => decSortElem?_encSortElem_append f k r h.1 h.2)
    (fun k => encLenBytes_pos 3 _)
    [] (decSortElem?_stop_nil f) fuel ks hall
    (by simpa [List.length_append] using hfuel)

/-! ## the rel bodies (the rel_type arms, at the upstream numbers) -/

/-- The ReadRel body: the base schema (field 2, OPTIONAL — the seed's
    `Option NamedStruct`) + the named table (field 7, whose payload is
    the repeated field-1 names — the upstream
    `ReadRel { base_schema = 2, read_type { named_table = 7 { names = 1 } } }`).
    The canonical order: the base schema first, the named table last. -/
def encReadBody (rt : ReadType) (bs : Option NamedStruct) : List UInt8 :=
  (match bs with
    | some s => encLenBytes 2 (encNamedStructBody s)
    | none => []) ++
  match rt with
  | .namedTable nms => encLenBytes 7 (encRep (fun n => encLenBytes 1 (encStr n)) nms)

/-- The ReadRel body's read-back (full consumption — trailing bytes
    refuse, the canonical dialect). -/
def decReadBody? (fuel : Nat) (bs : List UInt8)
    : Option (ReadType × Option NamedStruct) :=
  match decLenField? 2 bs with
  | some (Step.more pl rest1) =>
      match decNamedStructBody? fuel pl with
      | some (Step.more s []) =>
          match decLenField? 7 rest1 with
          | some (Step.more pl7 rest2) =>
              match decRep? (decFieldStr? 1) (pl7.length + 1) pl7 with
              | some (nms, []) =>
                  match rest2 with
                  | [] => some (.namedTable nms, some s)
                  | _ => none
              | _ => none
          | _ => none
      | _ => none
  | some (Step.stop _) =>
      match decLenField? 7 bs with
      | some (Step.more pl7 rest2) =>
          match decRep? (decFieldStr? 1) (pl7.length + 1) pl7 with
          | some (nms, []) =>
              match rest2 with
              | [] => some (.namedTable nms, none)
              | _ => none
          | _ => none
      | _ => none
  | none => none

/-- The ReadRel body's NIL-face law (the two option faces — the base
    schema present and absent; the names' ASCII + the fuel). -/
theorem decReadBody?_encReadBody (fuel : Nat) (rt : ReadType) (bs : Option NamedStruct)
    (hd : inDomainRel (.read rt bs) = true)
    (hfuel : (encReadBody rt bs).length + 1 ≤ fuel) :
    decReadBody? fuel (encReadBody rt bs) = some (rt, bs) := by
  cases rt with
  | namedTable nms =>
      -- the names rep's law, at the plain faces the decode reads
      have hrep : decRep? (decFieldStr? 1)
          ((encRep (fun n => encLenBytes 1 (encStr n)) nms).length + 1)
          (encRep (fun n => encLenBytes 1 (encStr n)) nms) = some (nms, []) := by
        rw [← List.append_nil (encRep (fun n => encLenBytes 1 (encStr n)) nms)]
        exact decRep?_encRep_append (decFieldStr? 1)
          (fun n => encLenBytes 1 (encStr n))
          (fun s => inDomainStr s = true)
          (fun s r h => decFieldStr?_encLenBytes_append 1 s r h)
          (fun s => encLenBytes_pos 1 _)
          [] (by rfl) _ nms
          (fun s hs => inDomainStrs_self nms s hs
            (by have h := hd; simp [inDomainRel] at h; exact h.1))
          (by simp only [List.length_append, List.append_nil]; omega)
      cases bs with
      | none =>
          have hd1 : inDomainStrs nms = true := by
            have h := hd; simp [inDomainRel] at h; exact h
          -- the absent schema's face: the field-2 parse sees the field-7
          -- tag and stops (the optional field's discrimination; the
          -- `++ []` faces are re-inserted where the laws read them)
          have hstop : decLenField? 2
                (encLenBytes 7 (encRep (fun n => encLenBytes 1 (encStr n)) nms))
              = some (Step.stop
                (encLenBytes 7 (encRep (fun n => encLenBytes 1 (encStr n)) nms))) := by
            simpa using decLenField?_other_stop 2 7
              (encRep (fun n => encLenBytes 1 (encStr n)) nms) [] (by decide)
          have h7 : decLenField? 7
                (encLenBytes 7 (encRep (fun n => encLenBytes 1 (encStr n)) nms))
              = some (Step.more (encRep (fun n => encLenBytes 1 (encStr n)) nms) []) := by
            simpa using decLenField?_encLenBytes_append 7
              (encRep (fun n => encLenBytes 1 (encStr n)) nms) []
          simp only [encReadBody, decReadBody?, List.nil_append, hstop, h7, hrep]
      | some s =>
          have hd1 : inDomainStrs nms = true := by
            have h := hd; simp [inDomainRel] at h; exact h.1
          have hd2 : inDomainStrs s.names = true := by
            have h := hd; simp [inDomainRel] at h; exact h.2
          have hns : inDomainNamedStruct s = true := hd2
          have hns' : decNamedStructBody? fuel (encNamedStructBody s)
              = some (Step.more s []) := by
            have h1 : (encLenBytes 2 (encNamedStructBody s)
                  ++ encLenBytes 7 (encRep (fun n => encLenBytes 1 (encStr n)) nms)).length
                + 1 ≤ fuel := hfuel
            have hw := encLenBytes_ge 2 (encNamedStructBody s)
            rw [← List.append_nil (encNamedStructBody s)]
            exact decNamedStructBody?_encNamedStructBody_append fuel s [] hns (by
              simp only [List.length_append, List.append_nil] at h1 hw ⊢
              omega)
          have h7 : decLenField? 7
                (encLenBytes 7 (encRep (fun n => encLenBytes 1 (encStr n)) nms))
              = some (Step.more (encRep (fun n => encLenBytes 1 (encStr n)) nms) []) := by
            simpa using decLenField?_encLenBytes_append 7
              (encRep (fun n => encLenBytes 1 (encStr n)) nms) []
          simp only [encReadBody, decReadBody?, List.nil_append]
          rw [decLenField?_encLenBytes_append]
          dsimp only
          rw [hns']
          dsimp only
          rw [h7]
          dsimp only
          rw [hrep]

-- the fetch window's literal-i64 face: the count/offset ride the
-- upstream `count_expr` (6) / `offset_expr` (5) faces as literal-i64
-- Expressions (the constant window's honest shape — the named divergence).
-- The i64 payload is the PLAIN varint — byte-identical to
-- `encLiteralBody { literalType := .i64 v }` on the in-domain range
-- (two's-complement ≡ plain below 2^63) — written directly so the
-- laws' whnf never touches the symbolic `Int.emod` of `twoComp` (the
-- kernel's deep recursion, the mechanics note).
def encNatLit (v : Nat) : List UInt8 :=
  encLenBytes 7 (encVarNat v) ++ encVarField 50 0

-- the arm FRAMES: each arm body's shape over the ALREADY-ENCODED inner
-- rel bytes (the frames are non-recursive — the rel recursion lives in
-- `encRelBody`'s structural walk alone; the mutual family's
-- pass-through calls broke the termination check, the wave's
-- mechanics note)
-- The FilterRel frame: the input (field 2) + the condition (field 3 —
-- the upstream `FilterRel { input = 2, condition = 3 }`).
def encFilterBody (inner : List UInt8) (c : Expression) : List UInt8 :=
  encLenBytes 2 inner ++ encLenBytes 3 (encExpressionBody c)

-- The ProjectRel frame: the input (field 2) + the expressions' rep
-- (field 3 — the upstream `ProjectRel { input = 2, expressions = 3 }`).
def encProjectBody (inner : List UInt8) (es : List Expression) : List UInt8 :=
  encLenBytes 2 inner ++ encRep encExprElem es

-- The JoinRel frame: the left (field 2) + the right (field 3) + the
-- condition (field 4, the upstream `expression`) + the type (field 6,
-- the enum — the upstream `JoinRel { left = 2, right = 3,
-- expression = 4, type = 6 }`).
def encJoinBody (jt : JoinType) (l r : List UInt8) (c : Expression) : List UInt8 :=
  encLenBytes 2 l ++ encLenBytes 3 r
    ++ encLenBytes 4 (encExpressionBody c) ++ encVarField 6 (joinTypeNum jt)

-- The AggregateRel frame: the input (field 2) + the groupings' rep
-- (field 3) + the measures' rep (field 4) — BOTH as plain Expression
-- elements (the seed's named divergence: the `Grouping`/`Measure`
-- wrappers collapse).
def encAggregateBody (inner : List UInt8) (gs ms : List Expression) : List UInt8 :=
  encLenBytes 2 inner
    ++ encRep encExprElem gs ++ encRep encMeasureElem ms

-- The SortRel frame: the input (field 2) + the sorts' rep (field 3 —
-- the upstream `SortRel { input = 2, sorts = 3 }`).
def encSortBody (inner : List UInt8) (ks : List SortField) : List UInt8 :=
  encLenBytes 2 inner ++ encRep encSortElem ks

-- The FetchRel frame: the input (field 2) + the offset (field 5,
-- OPTIONAL) + the limit (field 6, OPTIONAL — the upstream
-- `FetchRel { input = 2, offset_expr = 5, count_expr = 6 }`). The
-- canonical order: input, offset, limit.
def encFetchBody (inner : List UInt8) (limit offset : Option Nat) : List UInt8 :=
  encLenBytes 2 inner
    ++ (match offset with | some o => encLenBytes 5 (encNatLit o) | none => [])
    ++ (match limit with | some l => encLenBytes 6 (encNatLit l) | none => [])

-- The SetRel frame: the two inputs (field 2, twice — the seed's BINARY
-- narrowing) + the op (field 3, the enum — the upstream
-- `SetRel { inputs = 2, op = 3 }`).
def encSetBody (op : SetOp) (l r : List UInt8) : List UInt8 :=
  encLenBytes 2 l ++ encLenBytes 2 r
    ++ encVarField 3 (setOpNum op)

-- The CrossRel frame: the two inputs (fields 2, 3 — the upstream
-- `CrossRel { left = 2, right = 3 }`); no condition, no type field.
def encCrossBody (l r : List UInt8) : List UInt8 :=
  encLenBytes 2 l ++ encLenBytes 3 r

-- The WriteRel frame: the named table (field 1, whose payload is the
-- repeated field-1 names — the `NamedObjectWrite { names = 1 }` face)
-- + the table schema (field 3, the NamedStruct) + the op (field 4,
-- the enum) + the input (field 5 — the upstream `WriteRel {
-- named_table = 1, table_schema = 3, op = 4, input = 5 }`). The
-- canonical order: the field numbers ascending.
def encWriteBody (nms : List String) (op : WriteOp) (ts : NamedStruct)
    (inner : List UInt8) : List UInt8 :=
  encLenBytes 1 (encRep (fun n => encLenBytes 1 (encStr n)) nms)
    ++ encLenBytes 3 (encNamedStructBody ts)
    ++ encVarField 4 (writeOpNum op)
    ++ encLenBytes 5 inner

/-- The Rel body: the rel_type ONEOF at the upstream Rel fields
    (read = 1, filter = 2, fetch = 3, aggregate = 4, sort = 5, join = 6,
    project = 7, set = 8) — each arm's payload is that arm's frame over
    the recursively-encoded input rel(s). THE ONE recursive walk (each
    arm's input rel is a direct subterm — the structural check's
    requirement). The canonical order inside each arm: the input first,
    the arm's own fields after. -/
def encRelBody : Rel → List UInt8
  | .read rt bs => encLenBytes 1 (encReadBody rt bs)
  | .filter c input => encLenBytes 2 (encFilterBody (encRelBody input) c)
  | .fetch limit offset input =>
      encLenBytes 3 (encFetchBody (encRelBody input) limit offset)
  | .aggregate gs ms input =>
      encLenBytes 4 (encAggregateBody (encRelBody input) gs ms)
  | .sort ks input => encLenBytes 5 (encSortBody (encRelBody input) ks)
  | .join jt l r c => encLenBytes 6 (encJoinBody jt (encRelBody l) (encRelBody r) c)
  | .project es input => encLenBytes 7 (encProjectBody (encRelBody input) es)
  | .set op l r => encLenBytes 8 (encSetBody op (encRelBody l) (encRelBody r))
  | .cross l r => encLenBytes 12 (encCrossBody (encRelBody l) (encRelBody r))
  | .write nms op ts input =>
      encLenBytes 19 (encWriteBody nms op ts (encRelBody input))
def decNatLit? (fuel : Nat) (payload : List UInt8) : Option Nat :=
  match decOneof? payload with
  | some (7, pl, rest') =>
      match decVarNat? pl with
      | some (u, []) =>
          match decBoolField? 50 rest' with
          | some (Step.more _ []) =>
              if u < 9223372036854775808 then some u else none
          | _ => none
      | _ => none
  | _ => none

/-- PATTERN #2 — the window value's read-back law, ON THE WINDOW RANGE
    (the i64 literal face's admissible subdomain — at or above 2^63 the
    i64 semantics wrap, the gate refuses it at the emission boundary;
    the read-back's none is the decoder's honest face of that). -/
theorem decNatLit?_encNatLit (fuel : Nat) (v : Nat) (hv : v < 9223372036854775808) :
    decNatLit? fuel (encNatLit v) = some v := by
  show decNatLit? fuel (encLenBytes 7 (encVarNat v) ++ encVarField 50 0) = some v
  simp only [decNatLit?]
  rw [decOneof?_encLenBytes_append 7 (encVarNat v) (encVarField 50 0)]
  show (match decVarNat? (encVarNat v) with
        | some (u, []) =>
            match decBoolField? 50 (encVarField 50 0) with
            | some (Step.more _ []) =>
                if u < 9223372036854775808 then some u else none
            | _ => none
        | _ => none) = some v
  rw [show encVarNat v = encVarNat v ++ [] from (List.append_nil _).symm,
    decVarNat?_encVarNat_append]
  show (match decBoolField? 50 (encVarField 50 0) with
        | some (Step.more _ []) =>
            if v < 9223372036854775808 then some v else none
        | _ => none) = some v
  have hb : decBoolField? 50 (encVarField 50 0) = some (Step.more false []) := by
    simp [decBoolField?, decVarField?_encVarField 50 0]
  rw [hb]
  show (if v < 9223372036854775808 then some v else none) = some v
  rw [if_pos hv]

/-! ## the clean-suffix discipline (the rep-terminated streams' face) -/

/-- The string-field face's clean stop face (the plan's function-name
    rep's end). -/
theorem decFieldStr?_clean (field : Nat) (rest : List UInt8) (hc : CleanBytes rest) :
    decFieldStr? field rest = some (Step.stop rest) :=
  decElem?_clean (decFieldStr? field) field
    (fun bs h => by simp only [decFieldStr?, h]) rest hc

/-! ## the relation read-back (the rel_type oneof, fuel-bounded) -/

/-- The Rel body's read-back: the rel_type oneof at the upstream fields
    (read = 1, filter = 2, fetch = 3, aggregate = 4, sort = 5, join = 6,
    project = 7, set = 8), each arm's frame decoded field-by-field — the
    input rel recursively (the fuel IS the structural argument; each
    nesting level spends one fuel). THE CANONICAL DIALECT: each arm's
    frame is consumed to its END (the last field's parse at the empty
    tail — the payload is length-delimited, so the reps terminate at the
    message's own boundary), and the ONEOF's rest rides out. -/
def decRelBody? : Nat → List UInt8 → Option (Step Rel)
  | 0, _ => none
  | f + 1, bs =>
      match decOneof? bs with
      | none => none
      | some (1, payload, rest) =>
          match decReadBody? f payload with
          | some (rt, s) => some (Step.more (.read rt s) rest)
          | none => none
      | some (2, payload, rest) =>
          match decLenField? 2 payload with
          | some (Step.more pl rest1) =>
              match decRelBody? f pl with
              | some (Step.more r []) =>
                  match decLenField? 3 rest1 with
                  | some (Step.more cl []) =>
                      match decExpressionBody? f cl with
                      | some (Step.more c []) =>
                          some (Step.more (.filter c r) rest)
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | some (3, payload, rest) =>
          match decLenField? 2 payload with
          | some (Step.more pl rest1) =>
              match decRelBody? f pl with
              | some (Step.more r []) =>
                  match decLenField? 5 rest1 with
                  | some (Step.more ol rest2) =>
                      match decNatLit? f ol with
                      | none => none
                      | some o =>
                          match decLenField? 6 rest2 with
                          | some (Step.more ll []) =>
                              match decNatLit? f ll with
                              | some l => some (Step.more (.fetch (some l) (some o) r) rest)
                              | none => none
                          | some (Step.stop []) =>
                              some (Step.more (.fetch none (some o) r) rest)
                          | _ => none
                  | some (Step.stop rest2) =>
                      match decLenField? 6 rest2 with
                      | some (Step.more ll []) =>
                          match decNatLit? f ll with
                          | some l => some (Step.more (.fetch (some l) none r) rest)
                          | none => none
                      | some (Step.stop []) =>
                          some (Step.more (.fetch none none r) rest)
                      | _ => none
                  | none => none
              | _ => none
          | _ => none
      | some (4, payload, rest) =>
          match decLenField? 2 payload with
          | some (Step.more pl rest1) =>
              match decRelBody? f pl with
              | some (Step.more r []) =>
                  match decRep? (decExprElem? f) (rest1.length + 1) rest1 with
                  | some (gs, rest2) =>
                      match decRep? (decMeasureElem? f) (rest2.length + 1) rest2 with
                      | some (ms, []) =>
                          some (Step.more (.aggregate gs ms r) rest)
                      | _ => none
                  | none => none
              | _ => none
          | _ => none
      | some (5, payload, rest) =>
          match decLenField? 2 payload with
          | some (Step.more pl rest1) =>
              match decRelBody? f pl with
              | some (Step.more r []) =>
                  match decRep? (decSortElem? f) (rest1.length + 1) rest1 with
                  
                  | some (ks, []) =>
                      some (Step.more (.sort ks r) rest)
                  | _ => none
              | _ => none
          | _ => none
      | some (6, payload, rest) =>
          match decLenField? 2 payload with
          | some (Step.more pll rest1) =>
              match decRelBody? f pll with
              | some (Step.more l []) =>
                  match decLenField? 3 rest1 with
                  | some (Step.more plr rest2) =>
                      match decRelBody? f plr with
                      | some (Step.more r []) =>
                          match decLenField? 4 rest2 with
                          | some (Step.more cl rest3) =>
                              match decExpressionBody? f cl with
                              | some (Step.more c []) =>
                                  match decEnumField? 6 joinTypeOfNum? rest3 with
                                  | some (Step.more jt []) =>
                                      some (Step.more (.join jt l r c) rest)
                                  | _ => none
                              | _ => none
                          | _ => none
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | some (7, payload, rest) =>
          match decLenField? 2 payload with
          | some (Step.more pl rest1) =>
              match decRelBody? f pl with
              | some (Step.more r []) =>
                  match decRep? (decExprElem? f) (rest1.length + 1) rest1 with
                  
                  | some (es, []) =>
                      some (Step.more (.project es r) rest)
                  | _ => none
              | _ => none
          | _ => none
      | some (8, payload, rest) =>
          match decLenField? 2 payload with
          | some (Step.more pll rest1) =>
              match decRelBody? f pll with
              | some (Step.more l []) =>
                  match decLenField? 2 rest1 with
                  | some (Step.more plr rest2) =>
                      match decRelBody? f plr with
                      | some (Step.more r []) =>
                          match decEnumField? 3 setOpOfNum? rest2 with
                          | some (Step.more op []) =>
                              some (Step.more (.set op l r) rest)
                          | _ => none
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | some (12, payload, rest) =>
          match decLenField? 2 payload with
          | some (Step.more pll rest1) =>
              match decRelBody? f pll with
              | some (Step.more l []) =>
                  match decLenField? 3 rest1 with
                  | some (Step.more plr []) =>
                      match decRelBody? f plr with
                      | some (Step.more r []) =>
                          some (Step.more (.cross l r) rest)
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | some (19, payload, rest) =>
          match decLenField? 1 payload with
          | some (Step.more pl1 rest1) =>
              match decRep? (decFieldStr? 1) (pl1.length + 1) pl1 with
              | some (nms, []) =>
                  match decLenField? 3 rest1 with
                  | some (Step.more pl3 rest2) =>
                      match decNamedStructBody? f pl3 with
                      | some (Step.more ts []) =>
                          match decEnumField? 4 writeOpOfNum? rest2 with
                          | some (Step.more op rest3) =>
                              match decLenField? 5 rest3 with
                              | some (Step.more pl5 rest4) =>
                                  match decRelBody? f pl5 with
                                  | some (Step.more r []) =>
                                      some (Step.more (.write nms op ts r) rest)
                                  | _ => none
                              | _ => none
                          | _ => none
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | _ => none

/-! ## the relation law (ONE fuel induction, the two faces together) -/

/-- PATTERN #2/#18 — the Rel body's law, as ONE induction over the fuel
    carrying the TWO faces together (the append-form law and the NIL
    face — the nil face is the append face at the empty suffix). The
    gates: the inDomain emission boundary + the fuel above the encoded
    size. The payload is length-delimited, so the reps terminate at the
    message's own boundary — no suffix discipline at this level (the
    clean suffix enters at the PLAN's top-level reps). The chain
    discipline: `simp only` with the ONEOF law, the field laws, and the
    induction's faces; `++` is LEFT-associative, so
    `List.append_assoc` re-rights the frame's tail before the field
    laws' patterns land, and the nil-corollary forms carry the `++ []`
    faces. -/
theorem decRelBody?_law : ∀ (fuel : Nat),
    (∀ (r : Rel) (rest : List UInt8), inDomainRel r = true →
      (encRelBody r ++ rest).length + 1 ≤ fuel →
      decRelBody? fuel (encRelBody r ++ rest) = some (Step.more r rest))
    ∧ (∀ (r : Rel), inDomainRel r = true → (encRelBody r).length + 1 ≤ fuel →
      decRelBody? fuel (encRelBody r) = some (Step.more r [])) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro r rest _ hfuel; exact absurd hfuel (by omega)
      · intro r _ hfuel; exact absurd hfuel (by omega)
  | succ f ih =>
      have ih2 := ih.2
      have part1 : ∀ (r : Rel) (rest : List UInt8), inDomainRel r = true →
          (encRelBody r ++ rest).length + 1 ≤ f + 1 →
          decRelBody? (f + 1) (encRelBody r ++ rest) = some (Step.more r rest) := by
        intro r rest hd hfuel
        cases r with
        | read rt bs =>
            cases rt with
            | namedTable nms =>
                cases bs with
                | none =>
                    have hbound : (encReadBody (.namedTable nms) none).length + 1 ≤ f :=
                      encLenBytes_fuel_split (M := 1) (pre := [])
                        (inner := encReadBody (.namedTable nms) none)
                        (tail := rest) hfuel
                    simp only [encRelBody, decRelBody?,
                      decOneof?_encLenBytes_append,
                      decReadBody?_encReadBody f (.namedTable nms) none hd hbound]
                | some s =>
                    have hbound : (encReadBody (.namedTable nms) (some s)).length + 1 ≤ f :=
                      encLenBytes_fuel_split (M := 1) (pre := [])
                        (inner := encReadBody (.namedTable nms) (some s))
                        (tail := rest) hfuel
                    simp only [encRelBody, decRelBody?,
                      decOneof?_encLenBytes_append,
                      decReadBody?_encReadBody f (.namedTable nms) (some s) hd hbound]
        | filter c input =>
            have hde : inDomainExpr c = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1
            have hdr : inDomainRel input = true := by
              have h := hd; simp [inDomainRel] at h; exact h.2
            have hF : (encFilterBody (encRelBody input) c).length
                = (encLenBytes 2 (encRelBody input)).length
                  + (encLenBytes 3 (encExpressionBody c)).length := by
              simp only [encFilterBody, List.length_append]
            have hW := encLenBytes_ge 2 (encFilterBody (encRelBody input) c)
            have h1 : (encLenBytes 2 (encFilterBody (encRelBody input) c)
                ++ rest).length + 1 ≤ f + 1 := hfuel
            have hA := encLenBytes_ge 2 (encRelBody input)
            have hB := encLenBytes_ge 3 (encExpressionBody c)
            simp only [List.length_append] at h1 hW hF hA hB
            have hin : (encRelBody input).length + 1 ≤ f := by omega
            have hc : (encExpressionBody c).length + 1 ≤ f := by omega
            simp only [encRelBody, encFilterBody, decRelBody?, List.append_assoc,
              decOneof?_encLenBytes_append,
              decLenField?_encLenBytes_append,
              ih2 input hdr hin,
              decLenField?_encLenBytes 3 (encExpressionBody c),
              decExpressionBody?_encExpressionBody f c hde hc]
        | project es input =>
            have hde : inDomainExprs es = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1
            have hdr : inDomainRel input = true := by
              have h := hd; simp [inDomainRel] at h; exact h.2
            have hF : (encProjectBody (encRelBody input) es).length
                = (encLenBytes 2 (encRelBody input)).length
                  + (encRep encExprElem es).length := by
              simp only [encProjectBody, List.length_append]
            have hW := encLenBytes_ge 7 (encProjectBody (encRelBody input) es)
            have h1 : (encLenBytes 7 (encProjectBody (encRelBody input) es)
                ++ rest).length + 1 ≤ f + 1 := hfuel
            have hA := encLenBytes_ge 2 (encRelBody input)
            simp only [List.length_append] at h1 hW hF hA
            have hin : (encRelBody input).length + 1 ≤ f := by omega
            simp only [encRelBody, encProjectBody, decRelBody?, List.append_assoc,
              decOneof?_encLenBytes_append,
              decLenField?_encLenBytes_append,
              ih2 input hdr hin,
              decRep?_encExprElem_nil f ((encRep encExprElem es).length + 1) es
                (fun e he => ⟨inDomainExprs_self es e he hde, by
                  have hmem := encRep_mem_le encExprElem es e he
                  grind [encLenBytes_ge, encExprElem, List.length_append]⟩)
                (by omega)]
        | join jt l r c =>
            have hd3 : inDomainRel l = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1.1
            have hd4 : inDomainRel r = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1.2
            have hde : inDomainExpr c = true := by
              have h := hd; simp [inDomainRel] at h; exact h.2
            have hF : (encJoinBody jt (encRelBody l) (encRelBody r) c).length
                = (encLenBytes 2 (encRelBody l)).length
                  + ((encLenBytes 3 (encRelBody r)).length
                    + ((encLenBytes 4 (encExpressionBody c)).length
                      + (encVarField 6 (joinTypeNum jt)).length)) := by
              grind [encJoinBody, List.length_append]
            have hW := encLenBytes_ge 6 (encJoinBody jt (encRelBody l) (encRelBody r) c)
            have h1 : (encLenBytes 6 (encJoinBody jt (encRelBody l) (encRelBody r) c)
                ++ rest).length + 1 ≤ f + 1 := hfuel
            have hA := encLenBytes_ge 2 (encRelBody l)
            have hB := encLenBytes_ge 3 (encRelBody r)
            have hC := encLenBytes_ge 4 (encExpressionBody c)
            simp only [List.length_append] at h1 hW hF hA hB hC
            have hl : (encRelBody l).length + 1 ≤ f := by omega
            have hr : (encRelBody r).length + 1 ≤ f := by omega
            have hc : (encExpressionBody c).length + 1 ≤ f := by omega
            simp only [encRelBody, encJoinBody, decRelBody?, List.append_assoc,
              decOneof?_encLenBytes_append,
              decLenField?_encLenBytes_append,
              ih2 l hd3 hl,
              ih2 r hd4 hr,
              decLenField?_encLenBytes 4 (encExpressionBody c),
              decExpressionBody?_encExpressionBody f c hde hc,
              decEnumField?_encVarField 6 joinTypeOfNum? joinTypeNum
                joinTypeOfNum?_self jt]
        | aggregate gs ms input =>
            have hde : inDomainExprs gs = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1.1
            have hdm : inDomainExprs ms = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1.2
            have hdr : inDomainRel input = true := by
              have h := hd; simp [inDomainRel] at h; exact h.2
            have hF : (encAggregateBody (encRelBody input) gs ms).length
                = (encLenBytes 2 (encRelBody input)).length
                  + ((encRep encExprElem gs).length
                    + (encRep encMeasureElem ms).length) := by
              grind [encAggregateBody, List.length_append]
            have hW := encLenBytes_ge 4 (encAggregateBody (encRelBody input) gs ms)
            have h1 : (encLenBytes 4 (encAggregateBody (encRelBody input) gs ms)
                ++ rest).length + 1 ≤ f + 1 := hfuel
            have hA := encLenBytes_ge 2 (encRelBody input)
            simp only [List.length_append] at h1 hW hF hA
            have hin : (encRelBody input).length + 1 ≤ f := by omega
            simp only [encRelBody, encAggregateBody, decRelBody?, List.append_assoc,
              decOneof?_encLenBytes_append,
              decLenField?_encLenBytes_append,
              ih2 input hdr hin,
              decRep?_encRep_append (decExprElem? f) encExprElem
                (fun e => inDomainExpr e = true ∧ (encExpressionBody e).length + 1 ≤ f)
                (fun e r' h => decExprElem?_encExprElem_append f e r' h.1 h.2)
                (fun e => encLenBytes_pos 3 _)
                (encRep encMeasureElem ms)
                (by
                  cases ms with
                  | nil => exact decExprElem?_stop_nil f
                  | cons m ms' =>
                      simp only [decExprElem?, encRep, encMeasureElem]
                      rw [decLenField?_other_stop 3 4 (encExpressionBody m)
                        (encRep encMeasureElem ms') (by decide)])
                ((encRep encExprElem gs ++ encRep encMeasureElem ms).length + 1)
                gs
                (fun e he => ⟨inDomainExprs_self gs e he hde, by
                  have hmem := encRep_mem_le encExprElem gs e he
                  grind [encLenBytes_ge, encExprElem, List.length_append]⟩)
                (by omega),
              decRep?_encMeasureElem_nil f ((encRep encMeasureElem ms).length + 1) ms
                (fun e he => ⟨inDomainExprs_self ms e he hdm, by
                  have hmem := encRep_mem_le encMeasureElem ms e he
                  grind [encLenBytes_ge, encMeasureElem, List.length_append]⟩)
                (by omega)]
        | sort ks input =>
            have hdk : inDomainSortFields ks = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1
            have hdr : inDomainRel input = true := by
              have h := hd; simp [inDomainRel] at h; exact h.2
            have hF : (encSortBody (encRelBody input) ks).length
                = (encLenBytes 2 (encRelBody input)).length
                  + (encRep encSortElem ks).length := by
              simp only [encSortBody, List.length_append]
            have hW := encLenBytes_ge 5 (encSortBody (encRelBody input) ks)
            have h1 : (encLenBytes 5 (encSortBody (encRelBody input) ks)
                ++ rest).length + 1 ≤ f + 1 := hfuel
            have hA := encLenBytes_ge 2 (encRelBody input)
            simp only [List.length_append] at h1 hW hF hA
            have hin : (encRelBody input).length + 1 ≤ f := by omega
            simp only [encRelBody, encSortBody, decRelBody?, List.append_assoc,
              decOneof?_encLenBytes_append,
              decLenField?_encLenBytes_append,
              ih2 input hdr hin,
              decRep?_encSortElem_nil f ((encRep encSortElem ks).length + 1) ks
                (fun k hk => ⟨inDomainSortFields_self ks k hk hdk, by
                  have hmem := encRep_mem_le encSortElem ks k hk
                  grind [encLenBytes_ge, encSortElem, List.length_append]⟩)
                (by omega)]
        | fetch limit offset input =>
            cases limit with
            | none => cases offset with
              | none =>
                  have hdr : inDomainRel input = true := by
                    have h := hd; simp [inDomainRel] at h; exact h
                  have hF : (encFetchBody (encRelBody input) none none).length
                      = (encLenBytes 2 (encRelBody input)).length := by
                    simp only [encFetchBody, List.append_nil, List.length_append]
                  have hW := encLenBytes_ge 3 (encFetchBody (encRelBody input) none none)
                  have h1 : (encLenBytes 3 (encFetchBody (encRelBody input) none none)
                      ++ rest).length + 1 ≤ f + 1 := hfuel
                  have hA := encLenBytes_ge 2 (encRelBody input)
                  simp only [List.length_append] at h1 hW hF hA
                  have hin : (encRelBody input).length + 1 ≤ f := by omega
                  simp only [encRelBody, encFetchBody, decRelBody?, List.append_nil,
                    decOneof?_encLenBytes_append,
                    decLenField?_encLenBytes 2 (encRelBody input),
                    ih2 input hdr hin,
                    decLenField?_clean 5 [] CleanBytes.nil,
                    decLenField?_clean 6 [] CleanBytes.nil]
              | some o =>
                  have hdr : inDomainRel input = true := by
                    have h := hd; simp [inDomainRel] at h; exact h.2
                  have ho63 : o < 9223372036854775808 := by
                    have h := hd; simp [inDomainRel] at h; exact h.1
                  have hF : (encFetchBody (encRelBody input) none (some o)).length
                      = (encLenBytes 2 (encRelBody input)).length
                        + (encLenBytes 5 (encNatLit o)).length := by
                    grind [encFetchBody, List.append_nil, List.length_append]
                  have hW := encLenBytes_ge 3
                    (encFetchBody (encRelBody input) none (some o))
                  have h1 : (encLenBytes 3 (encFetchBody (encRelBody input) none (some o))
                      ++ rest).length + 1 ≤ f + 1 := hfuel
                  have hA := encLenBytes_ge 2 (encRelBody input)
                  have hX := encLenBytes_ge 5 (encNatLit o)
                  simp only [List.length_append] at h1 hW hF hA hX
                  have hin : (encRelBody input).length + 1 ≤ f := by omega
                  have ho : (encNatLit o).length + 1 ≤ f := by omega
                  simp only [encRelBody, encFetchBody, decRelBody?, List.append_nil,
                    List.append_assoc,
                    decOneof?_encLenBytes_append,
                    decLenField?_encLenBytes_append,
                    ih2 input hdr hin,
                    decLenField?_encLenBytes 5 (encNatLit o),
                    decNatLit?_encNatLit f o ho63,
                    decLenField?_clean 6 [] CleanBytes.nil]
            | some l => cases offset with
              | none =>
                  have hdr : inDomainRel input = true := by
                    have h := hd; simp [inDomainRel] at h; exact h.2
                  have hl63 : l < 9223372036854775808 := by
                    have h := hd; simp [inDomainRel] at h; exact h.1
                  have hF : (encFetchBody (encRelBody input) (some l) none).length
                      = (encLenBytes 2 (encRelBody input)).length
                        + (encLenBytes 6 (encNatLit l)).length := by
                    grind [encFetchBody, List.append_nil, List.length_append]
                  have hW := encLenBytes_ge 3
                    (encFetchBody (encRelBody input) (some l) none)
                  have h1 : (encLenBytes 3 (encFetchBody (encRelBody input) (some l) none)
                      ++ rest).length + 1 ≤ f + 1 := hfuel
                  have hA := encLenBytes_ge 2 (encRelBody input)
                  have hY := encLenBytes_ge 6 (encNatLit l)
                  simp only [List.length_append] at h1 hW hF hA hY
                  have hin : (encRelBody input).length + 1 ≤ f := by omega
                  have hl : (encNatLit l).length + 1 ≤ f := by omega
                  simp only [encRelBody, encFetchBody, decRelBody?, List.append_nil,
                    List.append_assoc,
                    decOneof?_encLenBytes_append,
                    decLenField?_encLenBytes_append,
                    ih2 input hdr hin,
                    decLenField?_other_stop_nil 5 6 (encNatLit l) (by decide),
                    decLenField?_encLenBytes 6 (encNatLit l),
                    decNatLit?_encNatLit f l hl63]
              | some o =>
                  have hdr : inDomainRel input = true := by
                    have h := hd; simp [inDomainRel] at h; exact h.2
                  have hl63 : l < 9223372036854775808 := by
                    have h := hd; simp [inDomainRel] at h; exact h.1.1
                  have ho63 : o < 9223372036854775808 := by
                    have h := hd; simp [inDomainRel] at h; exact h.1.2
                  have hF : (encFetchBody (encRelBody input) (some l) (some o)).length
                      = (encLenBytes 2 (encRelBody input)).length
                        + ((encLenBytes 5 (encNatLit o)).length
                          + (encLenBytes 6 (encNatLit l)).length) := by
                    grind [encFetchBody, List.append_nil, List.length_append]
                  have hW := encLenBytes_ge 3
                    (encFetchBody (encRelBody input) (some l) (some o))
                  have h1 : (encLenBytes 3
                      (encFetchBody (encRelBody input) (some l) (some o))
                      ++ rest).length + 1 ≤ f + 1 := hfuel
                  have hA := encLenBytes_ge 2 (encRelBody input)
                  have hX := encLenBytes_ge 5 (encNatLit o)
                  have hY := encLenBytes_ge 6 (encNatLit l)
                  simp only [List.length_append] at h1 hW hF hA hX hY
                  have hin : (encRelBody input).length + 1 ≤ f := by omega
                  have ho : (encNatLit o).length + 1 ≤ f := by omega
                  have hl : (encNatLit l).length + 1 ≤ f := by omega
                  simp only [encRelBody, encFetchBody, decRelBody?, List.append_nil,
                    List.append_assoc,
                    decOneof?_encLenBytes_append,
                    decLenField?_encLenBytes_append,
                    ih2 input hdr hin,
                    decLenField?_encLenBytes_append 5 (encNatLit o)
                      (encLenBytes 6 (encNatLit l)),
                    decNatLit?_encNatLit f o ho63,
                    decLenField?_encLenBytes 6 (encNatLit l),
                    decNatLit?_encNatLit f l hl63]
        | set op l r =>
            have hd3 : inDomainRel l = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1
            have hd4 : inDomainRel r = true := by
              have h := hd; simp [inDomainRel] at h; exact h.2
            have hF : (encSetBody op (encRelBody l) (encRelBody r)).length
                = (encLenBytes 2 (encRelBody l)).length
                  + ((encLenBytes 2 (encRelBody r)).length
                    + (encVarField 3 (setOpNum op)).length) := by
              grind [encSetBody, List.length_append]
            have hW := encLenBytes_ge 8 (encSetBody op (encRelBody l) (encRelBody r))
            have h1 : (encLenBytes 8 (encSetBody op (encRelBody l) (encRelBody r))
                ++ rest).length + 1 ≤ f + 1 := hfuel
            have hA := encLenBytes_ge 2 (encRelBody l)
            have hB := encLenBytes_ge 2 (encRelBody r)
            simp only [List.length_append] at h1 hW hF hA hB
            have hl : (encRelBody l).length + 1 ≤ f := by omega
            have hr : (encRelBody r).length + 1 ≤ f := by omega
            simp only [encRelBody, encSetBody, decRelBody?, List.append_assoc,
              decOneof?_encLenBytes_append,
              decLenField?_encLenBytes_append,
              ih2 l hd3 hl,
              ih2 r hd4 hr,
              decEnumField?_encVarField 3 setOpOfNum? setOpNum
                setOpOfNum?_self op]
        | cross l r =>
            have hd3 : inDomainRel l = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1
            have hd4 : inDomainRel r = true := by
              have h := hd; simp [inDomainRel] at h; exact h.2
            have hF : (encCrossBody (encRelBody l) (encRelBody r)).length
                = (encLenBytes 2 (encRelBody l)).length
                  + (encLenBytes 3 (encRelBody r)).length := by
              simp only [encCrossBody, List.length_append]
            have hW := encLenBytes_ge 12 (encCrossBody (encRelBody l) (encRelBody r))
            have h1 : (encLenBytes 12 (encCrossBody (encRelBody l) (encRelBody r))
                ++ rest).length + 1 ≤ f + 1 := hfuel
            have hA := encLenBytes_ge 2 (encRelBody l)
            have hB := encLenBytes_ge 3 (encRelBody r)
            simp only [List.length_append] at h1 hW hF hA hB
            have hl : (encRelBody l).length + 1 ≤ f := by omega
            have hr : (encRelBody r).length + 1 ≤ f := by omega
            simp only [encRelBody, encCrossBody, decRelBody?, List.append_assoc,
              decOneof?_encLenBytes_append,
              decLenField?_encLenBytes_append,
              decLenField?_encLenBytes 3 (encRelBody r),
              ih2 l hd3 hl,
              ih2 r hd4 hr]
        | write nms op ts input =>
            -- the write arm's gate: `inDomainRel`'s write row is the
            -- LEFT-assoc `&&`-chain, so the accessors are h.1.1/h.1.2/h.2
            have hd1 : inDomainStrs nms = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1.1
            have hd2 : inDomainNamedStruct ts = true := by
              have h := hd; simp [inDomainRel] at h; exact h.1.2
            have hd3 : inDomainRel input = true := by
              have h := hd; simp [inDomainRel] at h; exact h.2
            have hF : (encWriteBody nms op ts (encRelBody input)).length
                = (encLenBytes 1 (encRep (fun n => encLenBytes 1 (encStr n)) nms)).length
                  + ((encLenBytes 3 (encNamedStructBody ts)).length
                    + ((encVarField 4 (writeOpNum op)).length
                      + (encLenBytes 5 (encRelBody input)).length)) := by
              grind [encWriteBody, List.length_append]
            have hW := encLenBytes_ge 19 (encWriteBody nms op ts (encRelBody input))
            have h1 : (encLenBytes 19 (encWriteBody nms op ts (encRelBody input))
                ++ rest).length + 1 ≤ f + 1 := hfuel
            have hA := encLenBytes_ge 1 (encRep (fun n => encLenBytes 1 (encStr n)) nms)
            have hB := encLenBytes_ge 3 (encNamedStructBody ts)
            have hD := encLenBytes_ge 5 (encRelBody input)
            simp only [List.length_append] at h1 hW hF hA hB hD
            -- the named-struct law's NIL face (the payload's own end)
            have hns : (encNamedStructBody ts ++ []).length + 1 ≤ f := by
              grind [List.append_nil]
            have hin : (encRelBody input).length + 1 ≤ f := by omega
            -- the struct's read-back at the goal's exact shape (the
            -- read arm's hns' pattern: re-insert the `++ []` face)
            have hnsr : decNamedStructBody? f (encNamedStructBody ts)
                = some (Step.more ts []) := by
              rw [← List.append_nil (encNamedStructBody ts)]
              exact decNamedStructBody?_encNamedStructBody_append f ts [] hd2 hns
            -- the names' rep, at the goal's exact shape (the read
            -- arm's hrep pattern)
            have hrer : decRep? (decFieldStr? 1)
                ((encRep (fun n => encLenBytes 1 (encStr n)) nms).length + 1)
                (encRep (fun n => encLenBytes 1 (encStr n)) nms)
                = some (nms, []) := by
              rw [← List.append_nil (encRep (fun n => encLenBytes 1 (encStr n)) nms)]
              exact decRep?_encRep_append (decFieldStr? 1)
                (fun n => encLenBytes 1 (encStr n))
                (fun n => inDomainStr n = true)
                (fun n r' h => decFieldStr?_encLenBytes_append 1 n r' h)
                (fun n => encLenBytes_pos 1 _)
                [] (by rfl) _ nms
                (fun n hn => inDomainStrs_self nms n hn hd1)
                (by simp only [List.length_append, List.append_nil]; omega)
            simp only [encRelBody, encWriteBody, decRelBody?, List.append_assoc,
              decOneof?_encLenBytes_append,
              decLenField?_encLenBytes_append,
              hrer,
              hnsr,
              decEnumField?_encVarField_append 4 writeOpOfNum? writeOpNum
                writeOpOfNum?_self op (encLenBytes 5 (encRelBody input)),
              decLenField?_encLenBytes 5 (encRelBody input),
              ih2 input hd3 hin]
      exact ⟨part1, fun r hd hb => by
        rw [← List.append_nil (encRelBody r)]
        exact part1 r [] hd (by grind [List.append_nil])⟩

/-! ## the plan wire (the PlanRel elements + the Plan container) -/

/-- The PlanRel body: the rel_type oneof at the upstream fields
    (`PlanRel { rel = 1, root = 2 }`). The ROOT arm's payload is the
    `RelRoot { input = 1, names = 2 }` message — the CANONICAL ORDER
    writes the names rep FIRST (the seed's order choice, recorded: the
    input's field-1 tag then terminates the names' rep INSIDE the
    payload, so the element's decode never faces the outer stream). The
    canonical dialect: each arm's payload is consumed to its end, the
    ONEOF's rest rides out. -/
def encPlanRelBody : PlanRel → List UInt8
  | .rel r => encLenBytes 1 (encRelBody r)
  | .root nms r =>
      encLenBytes 2
        (encRep (fun n => encLenBytes 2 (encStr n)) nms
          ++ encLenBytes 1 (encRelBody r))

/-- The PlanRel body's read-back. -/
def decPlanRelBody? (fuel : Nat) (bs : List UInt8) : Option (Step PlanRel) :=
  match decOneof? bs with
  | some (1, payload, rest) =>
      match decRelBody? fuel payload with
      | some (Step.more r []) => some (Step.more (.rel r) rest)
      | _ => none
  | some (2, payload, rest) =>
      match decRep? (decFieldStr? 2) (payload.length + 1) payload with
      | some (nms, rest1) =>
          match decLenField? 1 rest1 with
          | some (Step.more pl []) =>
              match decRelBody? fuel pl with
              | some (Step.more r []) => some (Step.more (.root nms r) rest)
              | _ => none
          | _ => none
      | _ => none
  | _ => none

/-- The plan-relation ELEMENT face (the relations rep's elements are
    field-3 wrapped PlanRel bodies — the upstream `Plan.relations = 3`). -/
def encPlanRelElem (pr : PlanRel) : List UInt8 := encLenBytes 3 (encPlanRelBody pr)

def decPlanRelElem? (fuel : Nat) (el : List UInt8) : Option (Step PlanRel) :=
  match decLenField? 3 el with
  | some (Step.more pl rest) =>
      match decPlanRelBody? fuel pl with
      | some (Step.more pr []) => some (Step.more pr rest)
      | _ => none
  | some (Step.stop rest) => some (Step.stop rest)
  | none => none

/-- PATTERN #2 — the plan-relation element's append-form law, on the
    inDomain subdomain (the root's names' ASCII face) + the fuel (the
    ELEMENT's encoded size + 1 — the inner rel's decode rides the same
    fuel, the wraps' ≥ 4 bytes the slack). -/
theorem decPlanRelElem?_encPlanRelElem_append : ∀ (fuel : Nat) (pr : PlanRel)
    (rest : List UInt8), inDomainPlanRel pr = true →
    (encPlanRelElem pr).length + 1 ≤ fuel →
    decPlanRelElem? fuel (encPlanRelElem pr ++ rest) = some (Step.more pr rest) := by
  intro fuel pr rest hd hfuel
  simp only [encPlanRelElem, decPlanRelElem?]
  rw [decLenField?_encLenBytes_append]
  dsimp only
  cases pr with
  | rel r =>
      have hbound : (encRelBody r).length + 1 ≤ fuel :=
        encLenBytes_fuel_split_wrap_at (N := 3) (M := 1) (inner := encRelBody r)
          (pre := []) (tail := []) (rest := []) (by
            have h := hfuel
            simp only [List.nil_append, List.append_nil] at h ⊢
            exact h)
      simp only [encPlanRelBody, decPlanRelBody?, decOneof?_encLenBytes]
      rw [(decRelBody?_law fuel).2 r hd hbound]
  | root nms r =>
      have hd1 : (∀ n ∈ nms, inDomainStr n = true) := by
        have h := hd; simp [inDomainPlanRel] at h; exact h.1
      have hdr : inDomainRel r = true := by
        have h := hd; simp [inDomainPlanRel] at h; exact h.2
      -- THREE wraps (the element's 3, the root payload's 2, the rel's
      -- 1) — the budget peels one wrap per step, then the length
      -- arithmetic closes
      have hbound : (encRelBody r).length + 1 ≤ fuel := by
        have h3 := encLenBytes_fuel_budget_at fuel 3
          (encLenBytes 2 (encRep (fun n => encLenBytes 2 (encStr n)) nms
            ++ encLenBytes 1 (encRelBody r))) hfuel
        have h2 := encLenBytes_fuel_budget_at fuel 2
          (encRep (fun n => encLenBytes 2 (encStr n)) nms
            ++ encLenBytes 1 (encRelBody r)) (Nat.le_of_succ_le h3)
        -- the wrap-peel arithmetic by `grind` (06 §12): the closed-ground
        -- length bookkeeping — `encLenBytes_ge` named, the budgets in context
        grind [encLenBytes_ge, List.length_append]
      have hend : decFieldStr? 2 (encLenBytes 1 (encRelBody r))
          = some (Step.stop (encLenBytes 1 (encRelBody r))) := by
        simp only [decFieldStr?]
        rw [decLenField?_other_stop_nil 2 1 (encRelBody r) (by decide)]
      simp only [encPlanRelBody, decPlanRelBody?, decOneof?_encLenBytes,
        decRep?_encRep_append (decFieldStr? 2) (fun n => encLenBytes 2 (encStr n))
        (fun n => inDomainStr n = true)
        (fun n r' h => decFieldStr?_encLenBytes_append 2 n r' h)
        (fun n => encLenBytes_pos 2 _)
        (encLenBytes 1 (encRelBody r))
        hend
        ((encRep (fun n => encLenBytes 2 (encStr n)) nms
          ++ encLenBytes 1 (encRelBody r)).length + 1)
        nms
        (fun n hn => hd1 n hn)
        (by
          simp only [List.length_append]
          omega)]
      simp only [decLenField?_encLenBytes 1 (encRelBody r)]
      rw [(decRelBody?_law fuel).2 r hdr hbound]

/-- The Plan body: the relations rep (field 3, the upstream
    `Plan.relations = 3`) then the functions' name rep (field 100 — the
    seed's named divergence: the stand-in for the extension-declaration
    table). The canonical order: relations first, functions last. -/
def encPlanBody (p : Plan) : List UInt8 :=
  encRep encPlanRelElem p.relations
    ++ encRep (fun n => encLenBytes 100 (encStr n)) p.functions

/-- The Plan body's read-back (the two reps against the trailing
    stream; the trailing bytes ride out as the `Step`'s rest — the
    full-consumption refusal is `decPlan?`'s face). -/
def decPlanBody? (fuel : Nat) (bs : List UInt8) : Option (Step Plan) :=
  match decRep? (decPlanRelElem? fuel) (bs.length + 1) bs with
  | some (rels, rest1) =>
      match decRep? (decFieldStr? 100) (rest1.length + 1) rest1 with
      | some (fns, rest2) =>
          some (Step.more { functions := fns, relations := rels } rest2)
      | _ => none
  | _ => none

/-- The plan-relation element's clean stop face (the relations rep's
    end at the functions' stream or at the clean suffix). -/
theorem decPlanRelElem?_clean (fuel : Nat) (rest : List UInt8) (hc : CleanBytes rest) :
    decPlanRelElem? fuel rest = some (Step.stop rest) :=
  decElem?_clean (decPlanRelElem? fuel) 3
    (fun bs h => by simp only [decPlanRelElem?, h]) rest hc

/-- PATTERN #2/#18 — THE PLAN LAW: the Plan body's append-form round
    trip on the inDomain subdomain, with THE CLEAN SUFFIX (the
    last-rep's termination face on the outer stream — the header's
    clean-suffix discipline; Substrait.Text's FollowClean is the text
    twin). THE FUEL: the whole plan's encoded size + 1. -/
theorem decPlanBody?_encPlanBody_append : ∀ (fuel : Nat) (p : Plan) (rest : List UInt8),
    inDomainPlan p = true → (encPlanBody p ++ rest).length + 1 ≤ fuel → CleanBytes rest →
    decPlanBody? fuel (encPlanBody p ++ rest) = some (Step.more p rest) := by
  intro fuel p rest hd hfuel hclean
  have hdr : (∀ pr ∈ p.relations, inDomainPlanRel pr = true) := by
    have h := hd; simp [inDomainPlan] at h; exact h.1
  have hdf : (∀ n ∈ p.functions, inDomainStr n = true) := by
    have h := hd; simp [inDomainPlan] at h; exact h.2
  have hfuel' : (encRep encPlanRelElem p.relations).length
      + ((encRep (fun n => encLenBytes 100 (encStr n)) p.functions ++ rest).length + 1)
      ≤ fuel := by
    -- the two-rep budget split by `grind` (06 §12): closed-ground length
    -- bookkeeping — the body's def equation + append assoc/norms named
    grind [encPlanBody, List.append_assoc, List.length_append]
  have hendRels : decPlanRelElem? fuel
      (encRep (fun n => encLenBytes 100 (encStr n)) p.functions ++ rest)
      = some (Step.stop
        (encRep (fun n => encLenBytes 100 (encStr n)) p.functions ++ rest)) := by
    cases p.functions with
    | nil => exact decPlanRelElem?_clean fuel rest hclean
    | cons fn fns =>
        simp only [decPlanRelElem?, encRep, List.append_assoc]
        rw [decLenField?_other_stop 3 100 (encStr fn)
          (encRep (fun n => encLenBytes 100 (encStr n)) fns ++ rest) (by decide)]
  simp only [encPlanBody, List.append_assoc, decPlanBody?]
  rw [decRep?_encRep_append (decPlanRelElem? fuel) encPlanRelElem
    (fun pr => inDomainPlanRel pr = true ∧ (encPlanRelElem pr).length + 1 ≤ fuel)
    (fun pr r' h => decPlanRelElem?_encPlanRelElem_append fuel pr r' h.1 h.2)
    (fun pr => encLenBytes_pos 3 _)
    (encRep (fun n => encLenBytes 100 (encStr n)) p.functions ++ rest)
    hendRels
    ((encRep encPlanRelElem p.relations
      ++ (encRep (fun n => encLenBytes 100 (encStr n)) p.functions ++ rest)).length + 1)
    p.relations
    (fun pr hpr => ⟨hdr pr hpr, by
      have hmem := encRep_mem_le encPlanRelElem p.relations pr hpr
      grind [encLenBytes_ge, encPlanRelElem, encPlanRelBody, List.length_append]⟩)
    (by omega)]
  simp only [decRep?_encRep_append (decFieldStr? 100) (fun n => encLenBytes 100 (encStr n))
    (fun n => inDomainStr n = true)
    (fun n r' h => decFieldStr?_encLenBytes_append 100 n r' h)
    (fun n => encLenBytes_pos 100 _)
    rest
    (decFieldStr?_clean 100 rest hclean)
    ((encRep (fun n => encLenBytes 100 (encStr n)) p.functions ++ rest).length + 1)
    p.functions
    (fun n hn => hdf n hn)
    (by omega)]

/-- The Plan's full face: the body + the trailing-bytes refusal (the
    canonical dialect's top-level entry). -/
def encPlan (p : Plan) : List UInt8 := encPlanBody p

/-- The Plan's full read-back. -/
def decPlan? (fuel : Nat) (bs : List UInt8) : Option Plan :=
  decFull? decPlanBody? fuel bs

/-- The full face's law (the plan law's NIL face + `decFull?`'s
    refusal of any trailing byte). -/
theorem decPlan?_encPlan (fuel : Nat) (p : Plan) (hd : inDomainPlan p = true)
    (hfuel : (encPlan p).length + 1 ≤ fuel) :
    decPlan? fuel (encPlan p) = some p := by
  have hnil : decPlanBody? fuel (encPlanBody p) = some (Step.more p []) := by
    rw [encPlan] at hfuel
    rw [← List.append_nil (encPlanBody p)]
    exact decPlanBody?_encPlanBody_append fuel p [] hd (by simpa using hfuel)
      CleanBytes.nil
  simp only [decPlan?, decFull?, encPlan]
  rw [hnil]


/-- The plan wire target: the Kit.Proto WireTarget row's FIRST consumer
    (the leftover rule). The honest CONDITIONAL grade — the plan law is
    inDomain-conditional (the emission boundary's gate) +
    clean-suffix-conditional (the rep-terminated streams' discipline);
    the full exact-image Codec grade is the decode ladder's named
    follow-up. The off-domain control: a plan whose function name is
    outside the ASCII fragment — the gate refuses it at the emission
    boundary. -/
def planWireTarget : WireTarget Plan where
  enc := encPlanBody
  dec := decPlanBody?
  inDomain := inDomainPlan
  clean := CleanBytes
  law := decPlanBody?_encPlanBody_append
  offDomain := [{ functions := ["dé"], relations := [] }]
  offDomainProof := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil] at ha
    rcases ha with rfl | habs
    · simp [inDomainPlan, inDomainStr]
    · exact absurd habs (by simp)
  grade := .conditionalRetraction
      "the plan law is inDomain-conditional (the emission boundary gate) + clean-suffix-conditional; the exact-image Codec grade is the decode ladder named follow-up"
  entourage := { vectors := true, goldens := true, controls := true, ifaceRow := "substrait.wire.plan" }

end Substrait.Wire

end -- public section

