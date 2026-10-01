/-
# Vortex.DTypeProto — the DType proto face (the wire message layer)

The message-shape wire face over the promoted protobuf primitives
(`Kit.Proto` — the promotion's SECOND consumer; the leftover rule's
move is complete: the primitives left substrait when this module
arrived to consume them). Riding `Vortex.DType`'s named seam:

- THE ONEOF TAGS are `DType.dtypeWireTag` — the seam's registry IS the
  wire's kind tag, ONE table read by both directions (the encoder
  writes it; no parallel table can drift). Nullability is CONTENT, not
  a discriminator (the Vortex-vs-Arrow discipline): every non-null
  variant's payload carries the flag as a varint field (1 = nullable);
  the null variant is nullable by nature.
- THE MESSAGE STRUCTURE per vortex's proto module: the DType oneof's
  variant payloads (Bool/Primitive/Decimal/List/FixedSizeList/Map/
  Struct/Union/Extension/FixedSizeTensor), the Field message (name +
  dtype — the struct's ordered named fields, list order = field
  order), and the tensor's shape rep (outermost first). FieldPath is
  NOT here — a path is a list of ordinals, not a dtype message; it
  ports with its first consumer.

The dialect is the canonical-form policy (the Substrait.Wire
precedent): every field written in a fixed order, the decoder accepts
exactly that face, trailing bytes refuse, minimal varints only.
Strings ride the ASCII fragment (`Kit.Proto.inDomainStr` — the full
UTF-8 face rides TextKit's char level, the named follow-up); the
off-domain face is the pinned control, never a silent law gap.

THE LAWS (15-patterns #2, append-form; #18's inDomain discipline):
- `decDTypeBody?_encDTypeBody_append` — the round trip for
  `inDomainDType d`, fuel above the encoded size; unconditional in the
  suffix (the nested bodies are length-delimited, so every rep
  terminates at the message's OWN boundary — no clean-suffix premise).
- `decDType?_encDType` — the full face (exact consumption).
- The WireTarget ROW: `dtypeWireTarget` — the scanable checklist as
  data, the honest conditionalRetraction grade (inDomain-conditional;
  the exact-image Codec grade is the named follow-up).

Recursion mechanics (06's discipline): the DECODER recurses
structurally on the fuel (never well-founded — the kernel-opaque
equations trap; the sibling calls ride the same fuel application, the
probe-verified form); the ENCODER + the domain gate recurse through
the `List (String × DType)` struct fields, so they are well-founded —
their per-constructor FORWARD equations are established ONCE below
(the repeated-agent trap: never fight the unfolding per lemma).

Core-only (imports Kit.Proto + Vortex.DType — the cone rule).

The five questions (notes/v3/01-core.md):
- root: Crossing (the wire) — the DType message bytes ↔ the dtypes.
- carrier grade: the append-form law on the inDomain subdomain
  (patterns #2/#18); the exact-image policy is the named follow-up.
- spine reading: DType → THESE BYTES (the dtype's wire face; the
  layout/encoding lane is orthogonal — encodings ride the column-data
  codecs, not the schema wire).
- ladder rung: hand theorems of the small kind — chains through
  Kit.Proto's primitive laws + ONE fuel induction.
- gate row: the axiom report (Vortex is gated); VortexTests carries
  the round-trip sweeps + the negative controls + the known-answer
  byte vectors.
-/
module

public import Kit.Proto
public import Vortex.DType
@[expose] public section


namespace Vortex

open Kit.Proto
open Kit.Varint (encVarNat decVarNat? decVarNat?_encVarNat_append)

/-! ## the wire tables (ONE table read by both directions) -/

/-- The physical type's wire number (the proto PType enum's order:
    u8..u64, i8..i64, f16..f64). -/
def ptypeNum : PType → Nat
  | .u8 => 0 | .u16 => 1 | .u32 => 2 | .u64 => 3
  | .i8 => 4 | .i16 => 5 | .i32 => 6 | .i64 => 7
  | .f16 => 8 | .f32 => 9 | .f64 => 10

/-- The physical type's read-back. -/
def ptypeOfNum? : Nat → Option PType
  | 0 => some .u8 | 1 => some .u16 | 2 => some .u32 | 3 => some .u64
  | 4 => some .i8 | 5 => some .i16 | 6 => some .i32 | 7 => some .i64
  | 8 => some .f16 | 9 => some .f32 | 10 => some .f64
  | _ => none

theorem ptypeOfNum?_self (p : PType) : ptypeOfNum? (ptypeNum p) = some p := by
  cases p <;> rfl

/-- The nullability flag's wire face: 1 = nullable, 0 = not. -/
def boolNum : Bool → Nat | true => 1 | false => 0

/-- The flag's read-back. -/
def decNl? (payload : List UInt8) : Option Bool :=
  match decVarField? 1 payload with
  | some (Step.more 1 []) => some true
  | some (Step.more 0 []) => some false
  | _ => none

theorem decNl?_boolNum (b : Bool) : decNl? (encVarField 1 (boolNum b)) = some b := by
  cases b <;> simp [decNl?, boolNum, decVarField?_encVarField]

/-! ## the domain gate (pattern #18's admissible subdomain) -/

/- The dtypes' admissible subdomain: every wire string (struct field
    names, extension ids) on the ASCII fragment. -/
mutual
def inDomainDType : DType → Bool
  | .null => true
  | .bool _ => true
  | .primitive _ _ => true
  | .decimal _ _ _ => true
  | .utf8 _ => true
  | .binary _ => true
  | .list e _ => inDomainDType e
  | .fixedSizeList e _ _ => inDomainDType e
  | .map _ k v _ => inDomainDType k && inDomainDType v
  | .struct fs _ => inDomainDTypeFields fs
  | .union vs _ => inDomainDTypes vs
  | .variant _ => true
  | .extension id st _ _ => inDomainStr id && inDomainDType st
  | .fixedSizeTensor _ _ _ => true

def inDomainDTypeFields : List (String × DType) → Bool
  | [] => true
  | f :: fs => inDomainStr f.1 && inDomainDType f.2 && inDomainDTypeFields fs

def inDomainDTypes : List DType → Bool
  | [] => true
  | d :: ds => inDomainDType d && inDomainDTypes ds
end

/-- The gate's per-constructor forward equations (the WF unfolding
    faces — established ONCE). -/
theorem inDomainDType_list (e : DType) (nl : Bool) :
    inDomainDType (.list e nl) = inDomainDType e := rfl
theorem inDomainDType_fixedSizeList (e : DType) (len : Nat) (nl : Bool) :
    inDomainDType (.fixedSizeList e len nl) = inDomainDType e := rfl
theorem inDomainDType_map (ks : Bool) (k v : DType) (nl : Bool) :
    inDomainDType (.map ks k v nl) = (inDomainDType k && inDomainDType v) := rfl
theorem inDomainDType_struct (fs : List (String × DType)) (nl : Bool) :
    inDomainDType (.struct fs nl) = inDomainDTypeFields fs := rfl
theorem inDomainDType_union (vs : List DType) (nl : Bool) :
    inDomainDType (.union vs nl) = inDomainDTypes vs := rfl
theorem inDomainDType_extension (id : String) (st : DType)
    (md : Option (List UInt8)) (nl : Bool) :
    inDomainDType (.extension id st md nl) = (inDomainStr id && inDomainDType st) := rfl

/-- The fields' gate's per-field read-back (the emission boundary's
    face at the struct row). -/
theorem inDomainDTypeFields_self : ∀ (fs : List (String × DType)) (fld : String × DType),
    fld ∈ fs → inDomainDTypeFields fs = true →
    inDomainStr fld.1 = true ∧ inDomainDType fld.2 = true := by
  intro fs
  induction fs with
  | nil => intro fld h; cases h
  | cons y tl ih =>
      intro fld h hd
      simp only [inDomainDTypeFields, Bool.and_eq_true] at hd
      rcases List.mem_cons.mp h with rfl | htl
      · exact ⟨hd.1.1, hd.1.2⟩
      · exact ih fld htl hd.2

/-- The list gate's per-element read-back. -/
theorem inDomainDTypes_self : ∀ (xs : List DType) (d : DType), d ∈ xs →
    inDomainDTypes xs = true → inDomainDType d = true := by
  intro xs
  induction xs with
  | nil => intro d h; cases h
  | cons y tl ih =>
      intro d h htrue
      simp only [inDomainDTypes, Bool.and_eq_true] at htrue
      rcases List.mem_cons.mp h with rfl | htl
      · exact htrue.1
      · exact ih d htl htrue.2

/-! ## the encoder (the canonical wire face; WF — see the header) -/

/- The DType message's body: the oneof kind (the field numbers ARE
    `DType.dtypeWireTag` — the seam's registry), each variant's payload
    carrying its own nullability flag; the reps end at the trailing
    field-9 flag INSIDE the payload (the canonical-order discipline —
    the element decodes stay unconditional). -/
mutual
def encDTypeBody : DType → List UInt8
  | .null => encLenBytes 1 []
  | .bool nl => encLenBytes 2 (encVarField 1 (boolNum nl))
  | .primitive p nl =>
      encLenBytes 3 (encVarField 1 (ptypeNum p) ++ encVarField 2 (boolNum nl))
  | .decimal prec scale nl =>
      encLenBytes 4 (encVarField 1 prec ++ encVarField 2 scale
        ++ encVarField 3 (boolNum nl))
  | .utf8 nl => encLenBytes 5 (encVarField 1 (boolNum nl))
  | .binary nl => encLenBytes 6 (encVarField 1 (boolNum nl))
  | .list e nl =>
      encLenBytes 7 (encLenBytes 1 (encDTypeBody e) ++ encVarField 2 (boolNum nl))
  | .fixedSizeList e len nl =>
      encLenBytes 8 (encLenBytes 1 (encDTypeBody e) ++ encVarField 2 len
        ++ encVarField 3 (boolNum nl))
  | .map ks k v nl =>
      encLenBytes 9 (encLenBytes 1 (encDTypeBody k)
        ++ encLenBytes 2 (encDTypeBody v) ++ encVarField 3 (boolNum ks)
        ++ encVarField 4 (boolNum nl))
  | .struct fs nl =>
      encLenBytes 10 (encFieldElems fs ++ encVarField 9 (boolNum nl))
  | .union vs nl =>
      encLenBytes 11 (encDTypeElems vs ++ encVarField 9 (boolNum nl))
  | .variant nl => encLenBytes 12 (encVarField 1 (boolNum nl))
  | .extension id st md nl =>
      encLenBytes 13 (encLenBytes 1 (encStr id) ++ encLenBytes 2 (encDTypeBody st)
        ++ (match md with | some m => encLenBytes 3 m | none => [])
        ++ encVarField 9 (boolNum nl))
  | .fixedSizeTensor p shape nl =>
      encLenBytes 14 (encVarField 1 (ptypeNum p) ++ encRep (encVarField 2) shape
        ++ encVarField 9 (boolNum nl))

/-- The struct's Field rep: each field a length-delimited field-1
    message (the rep's element face). -/
def encFieldElems : List (String × DType) → List UInt8
  | [] => []
  | fld :: fs => encLenBytes 1 (encFieldBody fld) ++ encFieldElems fs

/-- The Field message's body: the name (field 1, ASCII) + the dtype
    (field 2, a nested DType body). -/
def encFieldBody (fld : String × DType) : List UInt8 :=
  encLenBytes 1 (encStr fld.1) ++ encLenBytes 2 (encDTypeBody fld.2)

/-- The union's variant rep: each variant a length-delimited field-1
    DType body. -/
def encDTypeElems : List DType → List UInt8
  | [] => []
  | v :: vs => encLenBytes 1 (encDTypeBody v) ++ encDTypeElems vs
end

/-- The Field rep's encoding IS the generic rep (the rep law's
    application face). -/
theorem encFieldElems_eq_encRep (fs : List (String × DType)) :
    encFieldElems fs
      = encRep (fun fld => encLenBytes 1 (encFieldBody fld)) fs := by
  induction fs with
  | nil => rfl
  | cons fld tl ih =>
      simp only [encFieldElems, encRep, ih]

/-- The variant rep's encoding IS the generic rep. -/
theorem encDTypeElems_eq_encRep (vs : List DType) :
    encDTypeElems vs = encRep (fun u => encLenBytes 1 (encDTypeBody u)) vs := by
  induction vs with
  | nil => rfl
  | cons v tl ih =>
      simp only [encDTypeElems, encRep, ih]

/-- The encoder's per-constructor forward equations (the WF unfolding
    faces — established ONCE; the laws ride these names). -/
theorem encDTypeBody_null : encDTypeBody .null = encLenBytes 1 [] := rfl
theorem encDTypeBody_bool (nl : Bool) :
    encDTypeBody (.bool nl) = encLenBytes 2 (encVarField 1 (boolNum nl)) := rfl
theorem encDTypeBody_primitive (p : PType) (nl : Bool) :
    encDTypeBody (.primitive p nl)
      = encLenBytes 3 (encVarField 1 (ptypeNum p) ++ encVarField 2 (boolNum nl)) := rfl
theorem encDTypeBody_decimal (prec scale : Nat) (nl : Bool) :
    encDTypeBody (.decimal prec scale nl)
      = encLenBytes 4 (encVarField 1 prec ++ encVarField 2 scale
          ++ encVarField 3 (boolNum nl)) := rfl
theorem encDTypeBody_utf8 (nl : Bool) :
    encDTypeBody (.utf8 nl) = encLenBytes 5 (encVarField 1 (boolNum nl)) := rfl
theorem encDTypeBody_binary (nl : Bool) :
    encDTypeBody (.binary nl) = encLenBytes 6 (encVarField 1 (boolNum nl)) := rfl
theorem encDTypeBody_list (e : DType) (nl : Bool) :
    encDTypeBody (.list e nl)
      = encLenBytes 7 (encLenBytes 1 (encDTypeBody e) ++ encVarField 2 (boolNum nl)) := rfl
theorem encDTypeBody_fixedSizeList (e : DType) (len : Nat) (nl : Bool) :
    encDTypeBody (.fixedSizeList e len nl)
      = encLenBytes 8 (encLenBytes 1 (encDTypeBody e) ++ encVarField 2 len
          ++ encVarField 3 (boolNum nl)) := rfl
theorem encDTypeBody_map (ks : Bool) (k v : DType) (nl : Bool) :
    encDTypeBody (.map ks k v nl)
      = encLenBytes 9 (encLenBytes 1 (encDTypeBody k)
          ++ encLenBytes 2 (encDTypeBody v) ++ encVarField 3 (boolNum ks)
          ++ encVarField 4 (boolNum nl)) := rfl
theorem encDTypeBody_struct (fs : List (String × DType)) (nl : Bool) :
    encDTypeBody (.struct fs nl)
      = encLenBytes 10 (encFieldElems fs ++ encVarField 9 (boolNum nl)) := rfl
theorem encDTypeBody_union (vs : List DType) (nl : Bool) :
    encDTypeBody (.union vs nl)
      = encLenBytes 11 (encDTypeElems vs ++ encVarField 9 (boolNum nl)) := rfl
theorem encDTypeBody_variant (nl : Bool) :
    encDTypeBody (.variant nl) = encLenBytes 12 (encVarField 1 (boolNum nl)) := rfl
theorem encDTypeBody_extension (id : String) (st : DType) (md : Option (List UInt8))
    (nl : Bool) :
    encDTypeBody (.extension id st md nl)
      = encLenBytes 13 (encLenBytes 1 (encStr id) ++ encLenBytes 2 (encDTypeBody st)
          ++ (match md with | some m => encLenBytes 3 m | none => [])
          ++ encVarField 9 (boolNum nl)) := rfl
theorem encDTypeBody_fixedSizeTensor (p : PType) (shape : List Nat) (nl : Bool) :
    encDTypeBody (.fixedSizeTensor p shape nl)
      = encLenBytes 14 (encVarField 1 (ptypeNum p) ++ encRep (encVarField 2) shape
          ++ encVarField 9 (boolNum nl)) := rfl

/-! ## the decoder (structural on the fuel — the 06 discipline) -/

/- The DType body's read-back: the oneof at `dtypeWireTag`'s numbers,
    each arm decoding its variant payload field-by-field (the canonical
    dialect: every field present, in order). The Field/variant reps and
    the Field bodies are siblings of the SAME fuel recursion (the
    probe-verified structural form). -/
mutual
def decDTypeBody? : Nat → List UInt8 → Option (Step DType)
  | 0, _ => none
  | f + 1, bs =>
      match decOneof? bs with
      | none => none
      | some (1, _, rest) => some (Step.more .null rest)
      | some (2, payload, rest) =>
          (decNl? payload).map fun nl => Step.more (.bool nl) rest
      | some (3, payload, rest) =>
          match decEnumField? 1 ptypeOfNum? payload with
          | some (Step.more pt rest') =>
              match decBoolField? 2 rest' with
              | some (Step.more nl []) => some (Step.more (.primitive pt nl) rest)
              | _ => none
          | _ => none
      | some (4, payload, rest) =>
          match decVarField? 1 payload with
          | some (Step.more prec rest') =>
              match decVarField? 2 rest' with
              | some (Step.more scale rest'') =>
                  match decBoolField? 3 rest'' with
                  | some (Step.more nl []) =>
                      some (Step.more (.decimal prec scale nl) rest)
                  | _ => none
              | _ => none
          | _ => none
      | some (5, payload, rest) =>
          (decNl? payload).map fun nl => Step.more (.utf8 nl) rest
      | some (6, payload, rest) =>
          (decNl? payload).map fun nl => Step.more (.binary nl) rest
      | some (7, payload, rest) =>
          match decLenField? 1 payload with
          | some (Step.more pl rest') =>
              match decDTypeBody? f pl with
              | some (Step.more e []) =>
                  match decBoolField? 2 rest' with
                  | some (Step.more nl []) => some (Step.more (.list e nl) rest)
                  | _ => none
              | _ => none
          | _ => none
      | some (8, payload, rest) =>
          match decLenField? 1 payload with
          | some (Step.more pl rest') =>
              match decDTypeBody? f pl with
              | some (Step.more e []) =>
                  match decVarField? 2 rest' with
                  | some (Step.more len rest''') =>
                      match decBoolField? 3 rest''' with
                      | some (Step.more nl []) =>
                          some (Step.more (.fixedSizeList e len nl) rest)
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | some (9, payload, rest) =>
          match decLenField? 1 payload with
          | some (Step.more pl rest') =>
              match decDTypeBody? f pl with
              | some (Step.more k []) =>
                  match decLenField? 2 rest' with
                  | some (Step.more pl2 rest''') =>
                      match decDTypeBody? f pl2 with
                      | some (Step.more v []) =>
                          match decBoolField? 3 rest''' with
                          | some (Step.more ks rest5) =>
                              match decBoolField? 4 rest5 with
                              | some (Step.more nl []) =>
                                  some (Step.more (.map ks k v nl) rest)
                              | _ => none
                          | _ => none
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | some (10, payload, rest) =>
          match decRep? (decFieldElem? f) f payload with
          | some (fs, rest') =>
              match decBoolField? 9 rest' with
              | some (Step.more nl []) => some (Step.more (.struct fs nl) rest)
              | _ => none
          | _ => none
      | some (11, payload, rest) =>
          match decRep? (decDTypeElem? f) f payload with
          | some (vs, rest') =>
              match decBoolField? 9 rest' with
              | some (Step.more nl []) => some (Step.more (.union vs nl) rest)
              | _ => none
          | _ => none
      | some (12, payload, rest) =>
          (decNl? payload).map fun nl => Step.more (.variant nl) rest
      | some (13, payload, rest) =>
          match decFieldStr? 1 payload with
          | some (Step.more id r1) =>
              match decLenField? 2 r1 with
              | some (Step.more pl r2) =>
                  match decDTypeBody? f pl with
                  | some (Step.more st []) =>
                      match decLenField? 3 r2 with
                      | some (Step.more md r3) =>
                          match decBoolField? 9 r3 with
                          | some (Step.more nl []) =>
                              some (Step.more (.extension id st (some md) nl) rest)
                          | _ => none
                      | some (Step.stop _) =>
                          match decBoolField? 9 r2 with
                          | some (Step.more nl []) =>
                              some (Step.more (.extension id st none nl) rest)
                          | _ => none
                      | none => none
                  | _ => none
              | _ => none
          | _ => none
      | some (14, payload, rest) =>
          match decEnumField? 1 ptypeOfNum? payload with
          | some (Step.more p rest') =>
              match decRep? (decVarField? 2) f rest' with
              | some (shape, rest'') =>
                  match decBoolField? 9 rest'' with
                  | some (Step.more nl []) =>
                      some (Step.more (.fixedSizeTensor p shape nl) rest)
                  | _ => none
              | _ => none
          | _ => none
      | _ => none

/-- The union's variant rep element (a field-1 wrapped DType body). -/
def decDTypeElem? : Nat → List UInt8 → Option (Step DType)
  | 0, _ => none
  | f + 1, el =>
      match decLenField? 1 el with
      | some (Step.more pl rest) =>
          match decDTypeBody? f pl with
          | some (Step.more v []) => some (Step.more v rest)
          | _ => none
      | some (Step.stop rest) => some (Step.stop rest)
      | none => none

/-- The struct's Field rep element: the name (field 1, ASCII) + the
    dtype (field 2, fully consumed), INLINED (the Field body's read —
    the fuel's ONE drop per nesting level: the rep element's dtype
    decode rides the element's own reduced fuel, so the law's IH
    composes without a second fuel gap). -/
def decFieldElem? : Nat → List UInt8 → Option (Step (String × DType))
  | 0, _ => none
  | f + 1, el =>
      match decLenField? 1 el with
      | some (Step.more pl rest) =>
          match decFieldStr? 1 pl with
          | some (Step.more nm r1) =>
              match decLenField? 2 r1 with
              | some (Step.more pl2 r2) =>
                  match decDTypeBody? f pl2 with
                  | some (Step.more d []) => some (Step.more (nm, d) rest)
                  | _ => none
              | _ => none
          | _ => none
      | some (Step.stop rest) => some (Step.stop rest)
      | none => none
end

/-- The Field message's body's forward equation (the name field 1 +
    the dtype field 2 — the law's byte bookkeeping rides it). -/
theorem encFieldBody_eq (fld : String × DType) :
    encFieldBody fld
      = encLenBytes 1 (encStr fld.1) ++ encLenBytes 2 (encDTypeBody fld.2) := by
  simp only [encFieldBody]

/-- The Field body's wrap cost (the struct rep's per-element fuel
    bound's engine: the two nested wraps cost 4 bytes over the parts). -/
theorem lenFieldBody_ge (fld : String × DType) :
    (encLenBytes 1 (encStr fld.1)).length
      + (encLenBytes 2 (encDTypeBody fld.2)).length + 2
      ≤ (encLenBytes 1 (encFieldBody fld)).length := by
  have h1 := encLenBytes_ge 1
    (encLenBytes 1 (encStr fld.1) ++ encLenBytes 2 (encDTypeBody fld.2))
  rw [encFieldBody_eq]
  simp only [List.length_append] at h1 ⊢
  omega

/-! ## the laws (pattern #2, composed through Kit.Proto's primitive laws) -/

/-- The Bool-field face's append-form law at the `boolNum` spelling
    (the gate's wire form — `boolNum` IS the 0/1 face by cases). -/
theorem decBoolField?_boolNum_append (field : Nat) (b : Bool) (rest : List UInt8) :
    decBoolField? field (encVarField field (boolNum b) ++ rest)
      = some (Step.more b rest) := by
  cases b <;> simp [decBoolField?, decVarField?_encVarField_append, boolNum]

/-- The Bool-field face's NIL form at the `boolNum` spelling. -/
theorem decBoolField?_boolNum (field : Nat) (b : Bool) :
    decBoolField? field (encVarField field (boolNum b))
      = some (Step.more b []) := by
  rw [← List.append_nil (encVarField field (boolNum b)),
    decBoolField?_boolNum_append]

/-- The encoder's non-emptiness (the rep-element fuel bounds' base:
    every body encoding carries its own ≥2-byte wrap). -/
theorem encDTypeBody_pos (d : DType) : 0 < (encDTypeBody d).length := by
  cases d <;>
    simp only [encDTypeBody_null, encDTypeBody_bool, encDTypeBody_primitive,
      encDTypeBody_decimal, encDTypeBody_utf8, encDTypeBody_binary,
      encDTypeBody_list, encDTypeBody_fixedSizeList, encDTypeBody_map,
      encDTypeBody_struct, encDTypeBody_union, encDTypeBody_variant,
      encDTypeBody_extension, encDTypeBody_fixedSizeTensor] <;>
    exact encLenBytes_pos _ _

/-- The Field rep element's append-form law (the dtype premise rides
    the main law's IH — passed as `hD`). -/
theorem decFieldElem?_encFieldElem_append (f : Nat)
    (hD : ∀ (d : DType) (r : List UInt8), inDomainDType d = true →
      (encDTypeBody d ++ r).length + 1 ≤ f →
      decDTypeBody? f (encDTypeBody d ++ r) = some (Step.more d r))
    (fld : String × DType) (r : List UInt8)
    (hasc : inDomainStr fld.1 = true) (hd : inDomainDType fld.2 = true)
    (hb : (encDTypeBody fld.2).length + 1 ≤ f) :
    decFieldElem? (f + 1) (encLenBytes 1 (encFieldBody fld) ++ r)
      = some (Step.more fld r) := by
  simp only [decFieldElem?]
  rw [decLenField?_encLenBytes_append 1 (encFieldBody fld) r]
  simp only [List.append_assoc, encFieldBody_eq]
  rw [decFieldStr?_encLenBytes_append 1 fld.1 (encLenBytes 2 (encDTypeBody fld.2)) hasc]
  simp only [List.append_assoc]
  rw [decLenField?_encLenBytes 2 (encDTypeBody fld.2)]
  simp only [List.append_assoc]
  rw [← List.append_nil (encDTypeBody fld.2), hD fld.2 [] hd (by simpa using hb)]

/-- The Field rep element's stop face at a trailing varint (the
    rep's termination face inside the struct payload; the OTHER field
    number is the rep caller's trailing flag — 9 here). -/
theorem decFieldElem?_clean_at (f other v : Nat) :
    decFieldElem? (f + 1) (encVarField other v)
      = some (Step.stop (encVarField other v)) :=
  decElem?_clean (decFieldElem? (f + 1)) 1
    (fun bs h => by simp only [decFieldElem?, h]) (encVarField other v)
    (cleanVarField other v)

/-- The union's variant rep element's append-form law. -/
theorem decDTypeElem?_encDTypeElem_append (f : Nat)
    (hD : ∀ (d : DType) (r : List UInt8), inDomainDType d = true →
      (encDTypeBody d ++ r).length + 1 ≤ f →
      decDTypeBody? f (encDTypeBody d ++ r) = some (Step.more d r))
    (v : DType) (r : List UInt8) (hd : inDomainDType v = true)
    (hb : (encDTypeBody v).length + 1 ≤ f) :
    decDTypeElem? (f + 1) (encLenBytes 1 (encDTypeBody v) ++ r)
      = some (Step.more v r) := by
  simp only [decDTypeElem?]
  rw [decLenField?_encLenBytes_append 1 (encDTypeBody v) r]
  simp only [List.append_assoc]
  rw [← List.append_nil (encDTypeBody v), hD v [] hd (by simpa using hb)]

/-- The variant rep element's stop face at a trailing field-9 varint. -/
theorem decDTypeElem?_clean_at (f other v : Nat) :
    decDTypeElem? (f + 1) (encVarField other v)
      = some (Step.stop (encVarField other v)) :=
  decElem?_clean (decDTypeElem? (f + 1)) 1
    (fun bs h => by simp only [decDTypeElem?, h]) (encVarField other v)
    (cleanVarField other v)

/-- THE LAW — the DType body's append-form round trip on the admissible
    subdomain (pattern #2 at the message level, #18's gate; the
    suffix-UNCONDITIONAL face: the reps terminate at the message's own
    length-delimited boundary). The statement is FUEL-MONOTONE (the
    inner `g ≤ fuel`): the rep elements' inner bodies decode ONE fuel
    below the rep's, so the induction's IH must reach every smaller
    fuel — a fixed-fuel IH cannot compose through the rep element. -/
theorem decDTypeBody?_encDTypeBody_append :
    ∀ (fuel g : Nat), g ≤ fuel → ∀ (d : DType) (rest : List UInt8),
    inDomainDType d = true →
    (encDTypeBody d ++ rest).length + 1 ≤ g →
    decDTypeBody? g (encDTypeBody d ++ rest) = some (Step.more d rest) := by
  intro fuel
  induction fuel with
  | zero =>
      intro g hg d rest _ hfuel
      exact absurd hfuel (by omega)
  | succ f ih =>
      intro g hg d rest hd hfuel
      rcases Nat.lt_or_ge g (f + 1) with hlt | hge
      · -- the strictly-smaller fuel: the IH's own coverage
        exact ih g (Nat.le_of_lt_succ hlt) d rest hd hfuel
      · -- the working face: g = f + 1; the IH reaches every g' ≤ f
        have hgf : g = f + 1 := Nat.le_antisymm hg hge
        subst hgf
        have hD : ∀ (g' : Nat), g' ≤ f → ∀ (e : DType) (r : List UInt8),
            inDomainDType e = true →
            (encDTypeBody e ++ r).length + 1 ≤ g' →
            decDTypeBody? g' (encDTypeBody e ++ r) = some (Step.more e r) :=
          fun g' hg' e r he hb => ih g' hg' e r he hb
        cases d with
        | null =>
            rw [encDTypeBody_null, decDTypeBody?, decOneof?_encLenBytes_append]
            try rfl
        | bool nl =>
            rw [encDTypeBody_bool, decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decNl?_boolNum]
            try rfl
        | primitive p nl =>
            rw [encDTypeBody_primitive, decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decEnumField?_encVarField_append 1 ptypeOfNum? ptypeNum ptypeOfNum?_self
              p (encVarField 2 (boolNum nl))]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decBoolField?_boolNum 2 nl]
            try rfl
        | decimal prec scale nl =>
            rw [encDTypeBody_decimal] at hfuel ⊢
            rw [decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decVarField?_encVarField_append 1 prec
              (encVarField 2 scale ++ encVarField 3 (boolNum nl))]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decVarField?_encVarField_append 2 scale (encVarField 3 (boolNum nl))]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decBoolField?_boolNum 3 nl]
            try rfl
        | utf8 nl =>
            rw [encDTypeBody_utf8, decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decNl?_boolNum]
            try rfl
        | binary nl =>
            rw [encDTypeBody_binary, decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decNl?_boolNum]
            try rfl
        | list e nl =>
            rw [encDTypeBody_list] at hfuel ⊢
            rw [decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decLenField?_encLenBytes_append 1 (encDTypeBody e)
              (encVarField 2 (boolNum nl))]
            simp only [reduceCtorEq, List.append_assoc]
            have hbound : (encDTypeBody e).length + 1 ≤ f :=
              encLenBytes_fuel_split_wrap (N := 7) (M := 1) (pre := [])
                (inner := encDTypeBody e) (tail := encVarField 2 (boolNum nl))
                (rest := rest) hfuel
            rw [← List.append_nil (encDTypeBody e),
              hD f (Nat.le_refl f) e [] hd (by simpa using hbound)]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decBoolField?_boolNum 2 nl]
            try rfl
        | fixedSizeList e len nl =>
            rw [encDTypeBody_fixedSizeList] at hfuel ⊢
            rw [decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decLenField?_encLenBytes_append 1 (encDTypeBody e)
              (encVarField 2 len ++ encVarField 3 (boolNum nl))]
            simp only [reduceCtorEq, List.append_assoc]
            rw [List.append_assoc] at hfuel
            have hbound : (encDTypeBody e).length + 1 ≤ f :=
              encLenBytes_fuel_split_wrap (N := 8) (M := 1) (pre := [])
                (inner := encDTypeBody e)
                (tail := encVarField 2 len ++ encVarField 3 (boolNum nl))
                (rest := rest) hfuel
            rw [← List.append_nil (encDTypeBody e),
              hD f (Nat.le_refl f) e [] hd (by simpa using hbound)]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decVarField?_encVarField_append 2 len (encVarField 3 (boolNum nl))]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decBoolField?_boolNum 3 nl]
            try rfl
        | map ks k v nl =>
            rw [encDTypeBody_map] at hfuel ⊢
            rw [decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decLenField?_encLenBytes_append 1 (encDTypeBody k)
              (encLenBytes 2 (encDTypeBody v) ++ (encVarField 3 (boolNum ks)
                  ++ encVarField 4 (boolNum nl)))]
            simp only [reduceCtorEq, List.append_assoc]
            have hsplit : (inDomainDType k && inDomainDType v) = true := by
              rw [← inDomainDType_map ks k v nl]; exact hd
            rw [Bool.and_eq_true] at hsplit
            have hk : inDomainDType k = true := hsplit.1
            have hv : inDomainDType v = true := hsplit.2
            -- the K/V associations differ (the left-assoc frame needs
            -- one `append_assoc` per citation's shape)
            have hfuel' := hfuel
            rw [List.append_assoc, List.append_assoc] at hfuel'
            have hboundK : (encDTypeBody k).length + 1 ≤ f :=
              encLenBytes_fuel_split_wrap (N := 9) (M := 1) (pre := [])
                (inner := encDTypeBody k)
                (tail := encLenBytes 2 (encDTypeBody v)
                  ++ (encVarField 3 (boolNum ks) ++ encVarField 4 (boolNum nl)))
                (rest := rest) hfuel'
            rw [List.append_assoc] at hfuel
            have hboundV : (encDTypeBody v).length + 1 ≤ f :=
              encLenBytes_fuel_split_wrap (N := 9) (M := 2)
                (pre := encLenBytes 1 (encDTypeBody k)) (inner := encDTypeBody v)
                (tail := encVarField 3 (boolNum ks) ++ encVarField 4 (boolNum nl))
                (rest := rest) hfuel
            rw [← List.append_nil (encDTypeBody k),
              hD f (Nat.le_refl f) k [] hk (by simpa using hboundK)]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decLenField?_encLenBytes_append 2 (encDTypeBody v)
              (encVarField 3 (boolNum ks) ++ encVarField 4 (boolNum nl))]
            simp only [reduceCtorEq, List.append_assoc]
            rw [← List.append_nil (encDTypeBody v),
              hD f (Nat.le_refl f) v [] hv (by simpa using hboundV)]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decBoolField?_boolNum_append 3 ks (encVarField 4 (boolNum nl))]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decBoolField?_boolNum 4 nl]
            try rfl
        | struct fs nl =>
            rw [encDTypeBody_struct] at hfuel ⊢
            rw [decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            -- the fields' gate read-back (per-field facts for the rep law)
            have hall : ∀ g' ∈ fs, inDomainStr g'.1 = true ∧ inDomainDType g'.2 = true :=
              fun g' hg' => inDomainDTypeFields_self fs g' hg'
                (inDomainDType_struct fs nl ▸ hd)
            -- the rep's per-element fuel bound (the +2 slack: the element's
            -- inner dtype decode rides ONE fuel below the rep's own)
            have hmem : ∀ g' ∈ fs, (encDTypeBody g'.2).length + 2 ≤ f := by
              intro g' hg'
              have h1 := hfuel
              have hw1 := encLenBytes_ge 10 (encFieldElems fs ++ encVarField 9 (boolNum nl))
              have hw2 := encLenBytes_ge 1 (encFieldBody g')
              have hw3 := encLenBytes_ge 1 (encStr g'.1)
              have hw4 := encLenBytes_ge 2 (encDTypeBody g'.2)
              have hw5 := encVarField_ge 9 (boolNum nl)
              have hw7 := lenFieldBody_ge g'
              have hw6 : (encLenBytes 1 (encFieldBody g')).length
                  ≤ (encRep (fun fld => encLenBytes 1 (encFieldBody fld)) fs).length :=
                encRep_mem_le (fun fld => encLenBytes 1 (encFieldBody fld)) fs g' hg'
              rw [encFieldElems_eq_encRep fs] at h1 hw1
              simp only [List.length_append] at h1 hw1 hw2 hw3 hw4 hw5 hw7 ⊢
              omega
            rw [encFieldElems_eq_encRep fs]
            -- the rep element's law at the REP's fuel (the element lemma
            -- is at `g+1`; the rep's fuel `f` is ≥ 2 by the budget above)
            have helem : ∀ (g' : String × DType) (r : List UInt8),
                inDomainStr g'.1 = true → inDomainDType g'.2 = true →
                (encDTypeBody g'.2).length + 2 ≤ f →
                decFieldElem? f (encLenBytes 1 (encFieldBody g') ++ r)
                  = some (Step.more g' r) := by
              intro g' r hasc hdom hlen
              cases f with
              | zero => omega
              | succ f' =>
                  exact decFieldElem?_encFieldElem_append f'
                    (fun e r2 he hb => hD f' (by omega) e r2 he hb)
                    g' r hasc hdom (by omega)
            have hend : decFieldElem? f (encVarField 9 (boolNum nl))
                = some (Step.stop (encVarField 9 (boolNum nl))) := by
              cases f with
              | zero =>
                  -- the flag's ≥2 bytes + the wrap's ≥2 exceed the budget
                  have h1 := hfuel
                  have hw1 := encLenBytes_ge 10
                    (encFieldElems fs ++ encVarField 9 (boolNum nl))
                  have hw2 := encVarField_ge 9 (boolNum nl)
                  simp only [List.length_append] at h1 hw1 hw2 ⊢
                  omega
              | succ f' => exact decFieldElem?_clean_at f' 9 (boolNum nl)
            rw [decRep?_encRep_append (decFieldElem? f)
              (fun fld => encLenBytes 1 (encFieldBody fld))
              (fun g' => inDomainStr g'.1 = true ∧ inDomainDType g'.2 = true
                ∧ (encDTypeBody g'.2).length + 2 ≤ f)
              (fun g' r hgp => helem g' r hgp.1 hgp.2.1 hgp.2.2)
              (fun g' => encLenBytes_pos 1 (encFieldBody g'))
              (encVarField 9 (boolNum nl)) hend f fs
              (fun g' hg' => ⟨(hall g' hg').1, (hall g' hg').2, hmem g' hg'⟩)
              (by
                have h1 := hfuel
                have hw1 := encLenBytes_ge 10 (encFieldElems fs ++ encVarField 9 (boolNum nl))
                rw [encFieldElems_eq_encRep fs] at h1 hw1
                simp only [List.length_append] at h1 hw1 ⊢
                omega)]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decBoolField?_boolNum 9 nl]
            try rfl
        | union vs nl =>
            rw [encDTypeBody_union] at hfuel ⊢
            rw [decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            have hvdom : ∀ v ∈ vs, inDomainDType v = true :=
              fun v hv => inDomainDTypes_self vs v hv (inDomainDType_union vs nl ▸ hd)
            have hmem : ∀ v ∈ vs, (encDTypeBody v).length + 2 ≤ f := by
              intro v hv
              have h1 := hfuel
              have hw1 := encLenBytes_ge 11 (encDTypeElems vs ++ encVarField 9 (boolNum nl))
              have hw2 := encLenBytes_ge 1 (encDTypeBody v)
              have hw5 := encVarField_ge 9 (boolNum nl)
              have hw6 : (encLenBytes 1 (encDTypeBody v)).length
                  ≤ (encRep (fun u => encLenBytes 1 (encDTypeBody u)) vs).length :=
                encRep_mem_le (fun u => encLenBytes 1 (encDTypeBody u)) vs v hv
              rw [encDTypeElems_eq_encRep vs] at h1 hw1
              simp only [List.length_append] at h1 hw1 hw2 hw5 ⊢
              omega
            rw [encDTypeElems_eq_encRep vs]
            have helem : ∀ (v : DType) (r : List UInt8), inDomainDType v = true →
                (encDTypeBody v).length + 2 ≤ f →
                decDTypeElem? f (encLenBytes 1 (encDTypeBody v) ++ r)
                  = some (Step.more v r) := by
              intro v r hd hlen
              cases f with
              | zero => omega
              | succ f' =>
                  exact decDTypeElem?_encDTypeElem_append f'
                    (fun e r2 he hb => hD f' (by omega) e r2 he hb) v r hd (by omega)
            have hend : decDTypeElem? f (encVarField 9 (boolNum nl))
                = some (Step.stop (encVarField 9 (boolNum nl))) := by
              cases f with
              | zero =>
                  have h1 := hfuel
                  have hw1 := encLenBytes_ge 11
                    (encDTypeElems vs ++ encVarField 9 (boolNum nl))
                  have hw2 := encVarField_ge 9 (boolNum nl)
                  simp only [List.length_append] at h1 hw1 hw2 ⊢
                  omega
              | succ f' => exact decDTypeElem?_clean_at f' 9 (boolNum nl)
            rw [decRep?_encRep_append (decDTypeElem? f)
              (fun u => encLenBytes 1 (encDTypeBody u))
              (fun v => inDomainDType v = true ∧ (encDTypeBody v).length + 2 ≤ f)
              (fun v r hvp => helem v r hvp.1 hvp.2)
              (fun v => encLenBytes_pos 1 (encDTypeBody v))
              (encVarField 9 (boolNum nl)) hend f vs
              (fun v hv => ⟨hvdom v hv, hmem v hv⟩)
              (by
                have h1 := hfuel
                have hw1 := encLenBytes_ge 11 (encDTypeElems vs ++ encVarField 9 (boolNum nl))
                rw [encDTypeElems_eq_encRep vs] at h1 hw1
                simp only [List.length_append] at h1 hw1 ⊢
                omega)]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decBoolField?_boolNum 9 nl]
            try rfl
        | variant nl =>
            rw [encDTypeBody_variant, decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decNl?_boolNum]
            try rfl
        | extension id st md nl =>
            cases md with
            | some m =>
                rw [encDTypeBody_extension] at hfuel ⊢
                simp only [reduceCtorEq] at hfuel ⊢
                rw [decDTypeBody?, decOneof?_encLenBytes_append]
                simp only [reduceCtorEq, List.append_assoc]
                have hsplit : (inDomainStr id && inDomainDType st) = true := by
                  rw [← inDomainDType_extension id st (some m) nl]; exact hd
                rw [Bool.and_eq_true] at hsplit
                have hasc : inDomainStr id = true := hsplit.1
                have hst : inDomainDType st = true := hsplit.2
                rw [List.append_assoc] at hfuel
                have hbound : (encDTypeBody st).length + 1 ≤ f :=
                  encLenBytes_fuel_split_wrap (N := 13) (M := 2)
                    (pre := encLenBytes 1 (encStr id)) (inner := encDTypeBody st)
                    (tail := encLenBytes 3 m ++ encVarField 9 (boolNum nl))
                    (rest := rest) hfuel
                rw [decFieldStr?_encLenBytes_append 1 id
                  (encLenBytes 2 (encDTypeBody st) ++ (encLenBytes 3 m
                      ++ encVarField 9 (boolNum nl))) hasc]
                simp only [reduceCtorEq, List.append_assoc]
                rw [decLenField?_encLenBytes_append 2 (encDTypeBody st)
                  (encLenBytes 3 m ++ encVarField 9 (boolNum nl))]
                simp only [reduceCtorEq, List.append_assoc]
                rw [← List.append_nil (encDTypeBody st),
                  hD f (Nat.le_refl f) st [] hst (by simpa using hbound)]
                simp only [reduceCtorEq, List.append_assoc]
                rw [decLenField?_encLenBytes_append 3 m (encVarField 9 (boolNum nl))]
                simp only [reduceCtorEq, List.append_assoc]
                rw [decBoolField?_boolNum 9 nl]
                try rfl
            | none =>
                rw [encDTypeBody_extension] at hfuel ⊢
                simp only [reduceCtorEq, List.append_nil] at hfuel ⊢
                rw [decDTypeBody?, decOneof?_encLenBytes_append]
                simp only [reduceCtorEq, List.nil_append, List.append_assoc]
                have hsplit : (inDomainStr id && inDomainDType st) = true := by
                  rw [← inDomainDType_extension id st none nl]; exact hd
                rw [Bool.and_eq_true] at hsplit
                have hasc : inDomainStr id = true := hsplit.1
                have hst : inDomainDType st = true := hsplit.2
                have hbound : (encDTypeBody st).length + 1 ≤ f :=
                  encLenBytes_fuel_split_wrap (N := 13) (M := 2)
                    (pre := encLenBytes 1 (encStr id)) (inner := encDTypeBody st)
                    (tail := encVarField 9 (boolNum nl))
                    (rest := rest) hfuel
                rw [decFieldStr?_encLenBytes_append 1 id
                  (encLenBytes 2 (encDTypeBody st) ++ encVarField 9 (boolNum nl)) hasc]
                simp only [reduceCtorEq, List.append_assoc]
                rw [decLenField?_encLenBytes_append 2 (encDTypeBody st)
                  (encVarField 9 (boolNum nl))]
                simp only [reduceCtorEq, List.append_assoc]
                rw [← List.append_nil (encDTypeBody st),
                  hD f (Nat.le_refl f) st [] hst (by simpa using hbound)]
                simp only [reduceCtorEq, List.append_assoc]
                rw [show decLenField? 3 (encVarField 9 (boolNum nl))
                      = some (Step.stop (encVarField 9 (boolNum nl))) from by
                    simpa using decLenField?_varint_stop 3 9 (boolNum nl) [] (by decide)]
                simp only [reduceCtorEq, List.append_assoc]
                rw [decBoolField?_boolNum 9 nl]
                try rfl
        | fixedSizeTensor p shape nl =>
            rw [encDTypeBody_fixedSizeTensor] at hfuel ⊢
            rw [decDTypeBody?, decOneof?_encLenBytes_append]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decEnumField?_encVarField_append 1 ptypeOfNum? ptypeNum ptypeOfNum?_self
              p (encRep (encVarField 2) shape ++ encVarField 9 (boolNum nl))]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decRep?_encRep_append (decVarField? 2) (encVarField 2) (fun _ => True)
              (fun x r _ => decVarField?_encVarField_append 2 x r)
              (fun x => encVarField_pos 2 x)
              (encVarField 9 (boolNum nl))
              (by simpa using
                decVarField?_other_stop 2 9 (boolNum nl) [] (by decide)) f shape
              (fun _ _ => True.intro)
              (by
                have h1 := hfuel
                have hw1 := encLenBytes_ge 14
                  (encVarField 1 (ptypeNum p) ++ encRep (encVarField 2) shape
                    ++ encVarField 9 (boolNum nl))
                have hw2 := encVarField_ge 1 (ptypeNum p)
                have hw3 := encVarField_ge 9 (boolNum nl)
                simp only [List.length_append] at h1 hw1 hw2 hw3 ⊢
                omega)]
            simp only [reduceCtorEq, List.append_assoc]
            rw [decBoolField?_boolNum 9 nl]
            try rfl

/-- The law's exact-fuel form (the consumers' shape). -/
theorem decDTypeBody?_encDTypeBody_append_at (fuel : Nat) (d : DType)
    (rest : List UInt8) (hd : inDomainDType d = true)
    (hfuel : (encDTypeBody d ++ rest).length + 1 ≤ fuel) :
    decDTypeBody? fuel (encDTypeBody d ++ rest) = some (Step.more d rest) :=
  decDTypeBody?_encDTypeBody_append fuel fuel (Nat.le_refl fuel) d rest hd hfuel

/-- The full face: the DType message read back from its exact bytes
    (trailing bytes refuse — the canonical dialect). -/
def decDType? (fuel : Nat) (bs : List UInt8) : Option DType :=
  decFull? decDTypeBody? fuel bs

/-- The full face's law. -/
theorem decDType?_encDType (fuel : Nat) (d : DType) (hd : inDomainDType d = true)
    (hfuel : (encDTypeBody d).length + 1 ≤ fuel) :
    decDType? fuel (encDTypeBody d) = some d := by
  simp only [decDType?, decFull?]
  rw [← List.append_nil (encDTypeBody d),
    decDTypeBody?_encDTypeBody_append_at fuel d [] hd (by simpa using hfuel)]

/-! ## the WireTarget row (the checklist as data — the SECOND consumer) -/

/-- The dtype wire target: the Kit.Proto `WireTarget` row's SECOND
    consumer (the plan row the first). The honest conditionalRetraction
    grade — the law is inDomain-conditional (the emission boundary's
    gate); the exact-image Codec grade is the named follow-up. The
    off-domain controls: a struct field name and an extension id
    outside the ASCII fragment — the gate refuses at the boundary. -/
def dtypeWireTarget : WireTarget DType where
  enc := encDTypeBody
  dec := decDTypeBody?
  inDomain := inDomainDType
  clean := CleanBytes
  law := by
    intro fuel a rest hd hfuel _
    exact decDTypeBody?_encDTypeBody_append_at fuel a rest hd hfuel
  offDomain := [.struct [("é", .bool false)] false,
                .extension "é" (.bool false) none false]
  offDomainProof := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | habs
    · rfl
    · rcases List.mem_cons.mp habs with rfl | hnil
      · rfl
      · exact absurd hnil (by simp)
  grade := .conditionalRetraction
    "the dtype law is inDomain-conditional (the emission boundary gate); the exact-image Codec grade is the named follow-up"
  entourage := { vectors := true, goldens := false, controls := true,
                 ifaceRow := "vortex.dtype" }

end Vortex

end -- public section
