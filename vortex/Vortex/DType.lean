/-
# Vortex.DType — the LOGICAL dtype universe (the encodings' target)

Owner: the Vortex agent (the mandate tree, `vortex/`).
Driving decisions: notes/design-vortex-encodings.md (the encodings are
physical layouts FOR a logical dtype — the surjection physical→logical:
an encoding maps INTO a dtype, never changes it) + the Vortex-vs-Arrow
nullability discipline (nullability is a property of the DTYPE, never
the field) + notes/v3/07-extensibility.md R1 (the lowering over the
closed universes, no new schema universe).

## The model

`PType` — the 11 physical scalar types (u8..u64, i8..i64, f16..f64),
with the derived ops TOTAL and their laws decide-able: bit/byte width,
int/float classification, the signed/unsigned moves, the max/min
values, and the smallest-ptype-for-a-value searches (the FoR/bitpack
width arithmetic's dtype face).

`DType` — the logical universe: Null / Bool / Primitive / Decimal /
Utf8 / Binary / List / FixedSizeList / Map / Struct / Union / Variant /
Extension / FixedSizeTensor. FIRST-CLASS NULLABILITY: every ctor
carries its own `nullable` flag — a struct field's dtype carries the
field's nullability (struct fields' names ordered, the list order IS
the field order); a Union's OUTER nullability (does the union cell
itself admit null) is DISTINCT from the selected variant's own
nullability (the variants are full `DType`s with their own flags).
The logical/physical split: `DType` is logical ONLY — the encodings
(`Vortex.Encoding`) are orthogonal.

NO SCHEMA TYPE: a struct dtype IS columnar data — there is no separate
schema/table universe here (the boundary schema universe is
`SchemaCore.Ty`; the honest correspondence below is the bridge).

## The SchemaCore.Ty correspondence — the honest grade

`tyToDType` embeds the boundary universe; `inTyImage` names the image;
`dtypeToTy`/`selfFalseTy` are the total section (a MUTUAL pair: the
containers' section recurses through the ELEMENTS' full section — a
list's element dtype carries its own nullability, which only the full
section carries; the section law's induction is size-indexed because
the structural recursor gives no IH through the `List DType` fields).
NOT a `Kit.Retraction`, NAMED: the option wrapper COLLAPSES
(nullability is a Bool, not a stack — `option (option u64)` and
`option u64` map to the same dtype; pinned in VortexTests), so the
`inv_emb` round trip is IMPOSSIBLE and a fake total iso would be the
lie the grade discipline exists to prevent. The honest face: the image
is named, the embedding lands in it (`inTyImage_tyToDType`), and the
SECTION law holds on the image (`tyToDType_dtypeToTy_image` — the
`toImageIso` round trip at the image's own members).

The image's named narrowings (each is the boundary Ty's reach, not a
dtype restriction): the map's keysSorted is FALSE (the boundary map
declares no sort), the union is the RESULT shape (exactly 2 variants),
the bounded cap is schema metadata (the dtype face is u64).

## The proto tie-in — THE SEAM (named)

The DType proto message's WIRE FACE (the tag/varint/len-delimited
bytes) is NOT here: `Substrait.ProtoBuf` owns the proto primitives
(encTag/encVarField/encLenBytes/encI64/decVarField?/decLenField?/
decI64? + the decRep? repeat layer) — substrait-local, SAME cone
(c1domain; the SchemaCore.Emit ← Wit precedent), but that lane is
mid-landing by the protobuf agent, so importing it now couples this
lane to their churn. THE DEPENDENCY, exactly: those primitives are
the wire face's atoms; the kit promotion happens when DType is the
SECOND consumer (the leftover rule), a later wave. What lands HERE is
the message SHAPE as data: the oneof discriminator registry
(`dtypeWireTag`, total, the kind-level injectivity pinned) + the
message structure this file's types already carry.

Core-only (imports Kit + SchemaCore.Ty — the cone rule).
-/
module

public import Kit.Correspondence
public import Kit.Relation
public import Kit.Hyper
public import Kit.Obligation
public import Kit.Registry
public import Kit.CheckedProp
public import Kit.Emit
public import Kit.Suggest
public import Kit.Diag
public import Kit.Cli
public import Kit.CodeRegistry
public import Kit.Change
public import Kit.Observer
public import Kit.Varint
public import Kit.Proto
public import Kit.Duel
public import Kit.Mangle
-- the Kit barrel itself stays pre-module (Kit.Lane/Kit.Text are the
-- named stays); the module-only members are imported directly
public import SchemaCore.Ty
@[expose] public section


open Kit SchemaCore

namespace Vortex

/-! ## PType — the 11 physical scalar types -/

/-- The physical scalar types: the 8-bit-aligned ints and floats. -/
inductive PType where
  | u8 | u16 | u32 | u64
  | i8 | i16 | i32 | i64
  | f16 | f32 | f64
deriving Repr, BEq, DecidableEq, Inhabited

namespace PType

/-- The bit width (the physical layout's atom count). -/
def bitWidth : PType → Nat
  | .u8 => 8 | .u16 => 16 | .u32 => 32 | .u64 => 64
  | .i8 => 8 | .i16 => 16 | .i32 => 32 | .i64 => 64
  | .f16 => 16 | .f32 => 32 | .f64 => 64

/-- The byte width (the layout's addressing unit). -/
def byteWidth (p : PType) : Nat := p.bitWidth / 8

/-- The int face of the classification (the kernel-dispatch face). -/
def isInt : PType → Bool
  | .u8 | .u16 | .u32 | .u64 | .i8 | .i16 | .i32 | .i64 => true
  | _ => false

/-- The float face of the classification. -/
def isFloat : PType → Bool
  | .f16 | .f32 | .f64 => true
  | _ => false

/-- The unsigned face (the terminal-encoding policy's key lane). -/
def isUnsigned : PType → Bool
  | .u8 | .u16 | .u32 | .u64 => true
  | _ => false

/-- The signed move: u-p promotes to the same-width i-p; i/f stay. -/
def toSigned : PType → PType
  | .u8 => .i8 | .u16 => .i16 | .u32 => .i32 | .u64 => .i64
  | p => p

/-- The unsigned move: i-p demotes to the same-width u-p; u/f stay. -/
def toUnsigned : PType → PType
  | .i8 => .u8 | .i16 => .u16 | .i32 => .u32 | .i64 => .u64
  | p => p

/-- The byte-width law: the addressing unit tiles the bit width. -/
theorem byteWidth_bitWidth (p : PType) : p.byteWidth * 8 = p.bitWidth := by
  cases p <;> rfl

/-- The classification's disjointness: an int is never a float. -/
theorem isInt_isFloat_disjoint (p : PType) (h : p.isInt = true) :
    p.isFloat = false := by
  cases p <;> simp_all [isInt, isFloat]

/-- The unsigned round trip: the SIGNED move is undone by the unsigned
    move on the unsigned subdomain (the avoid-signed wire policy's
    face). -/
theorem toUnsigned_toSigned_unsigned (p : PType) (h : p.isUnsigned = true) :
    p.toSigned.toUnsigned = p := by
  cases p <;> simp_all [isUnsigned, toUnsigned, toSigned]

end PType

/-! ## THE TERMINAL-ENCODING POLICY ROWS (flatland's locked policy —
    E3's dtype face; the static tree's lane is `Vortex.Encoding`) -/

/-- The terminal-encoding policy row per physical scalar — flatland's
    locked policy ("u*-only keys; i* via FoR; f* via ALP-as-terminal;
    BitPacked is the terminal everywhere"; the compiler predicts
    encodings, never searches). The u*-only-keys clause is the KEY
    sub-universe's convention (SchemaCore owns `KeyTy` — a position,
    not a type); the per-TYPE rows are the three below. -/
inductive TerminalPolicy where
  /-- i*: FoR (the zigzag-or-rebase discipline — the offsets are
      unsigned either way). -/
  | viaFoR
  /-- f*: ALP-as-terminal — the NAMED face; the ALP lane lands with
      its first float consumer (the honest refusal until then). -/
  | alpTerminal
  /-- BitPacked: the terminal everywhere (the u* lane + the fallback). -/
  | bitPackedTerminal
deriving Repr, BEq, DecidableEq, Inhabited

/-- The policy row per physical scalar: i* → FoR, f* → ALP, u* → the
    BitPacked terminal (the FoR refinement rides the static range row
    — `Vortex.Encoding.foRGuard`'s lane). -/
def policyRow : PType → TerminalPolicy
  | .u8 | .u16 | .u32 | .u64 => .bitPackedTerminal
  | .i8 | .i16 | .i32 | .i64 => .viaFoR
  | .f16 | .f32 | .f64 => .alpTerminal

/-- The signed row: every SIGNED scalar's policy row is FoR. -/
theorem policyRow_signed_viaFoR (p : PType) (h : p.isUnsigned = false)
    (hi : p.isInt = true) : policyRow p = .viaFoR := by
  cases p <;> simp_all [policyRow, PType.isUnsigned, PType.isInt]

/-- THE f* ROW — the named face: every FLOAT scalar's policy row is
    ALP-as-terminal. -/
theorem policyRow_float_alp (p : PType) (h : p.isFloat = true) :
    policyRow p = .alpTerminal := by
  cases p <;> simp_all [policyRow, PType.isFloat]

/-! ## DType — the logical universe (nullability first-class) -/

/-- The LOGICAL dtype universe. Every ctor carries its own `nullable`
    flag — nullability is a property of the DTYPE, never the field
    (the Vortex-vs-Arrow discipline). The nested dtypes (a list's
    element, a struct's fields, a union's variants) are FULL `DType`s
    with their own flags — the per-cell nullability the columnar data
    carries. -/
inductive DType where
  /-- The all-null column (nullable by nature). -/
  | null
  | bool (nullable : Bool)
  | primitive (p : PType) (nullable : Bool)
  | decimal (precision scale : Nat) (nullable : Bool)
  | utf8 (nullable : Bool)
  | binary (nullable : Bool)
  | list (elem : DType) (nullable : Bool)
  /-- The FIXED-SIZE list: static length (the legacy `Ty.tensor`'s
      1-D face; the multi-dim shape lives on the tensor row below). -/
  | fixedSizeList (elem : DType) (len : Nat) (nullable : Bool)
  /-- The map: keys-sorted flag + the keys' and values' dtypes (the
      keys' dtype carries the keys' own nullability). -/
  | map (keysSorted : Bool) (keys : DType) (values : DType) (nullable : Bool)
  /-- THE STRUCT — a struct dtype IS columnar data (no schema type
      exists here): the ordered named fields, list order = field
      order, each field's dtype carrying its own nullability. -/
  | struct (fields : List (String × DType)) (nullable : Bool)
  /-- The tagged union: per-row u8 tag + the variants (each a FULL
      dtype — a variant's own nullability is independent of the
      union's OUTER nullability, which is this ctor's flag). -/
  | union (variants : List DType) (nullable : Bool)
  /-- The open variant (the tagged union of arbitrary dtype). -/
  | variant (nullable : Bool)
  /-- The extension: an id, the storage dtype (a full `DType`), the
      metadata bytes. -/
  | extension (id : String) (storage : DType) (metadata : Option (List UInt8))
      (nullable : Bool)
  /-- The dense row-major fixed-size tensor: the element PType + the
      static shape (outermost first — the legacy `Ty.tensor`'s dims
      convention, legacy/lean/schema-lang/SchemaLang/Ty.lean:85; the
      legacy shape is dims-over-`Ty`, this is the dtype-level element
      face). -/
  | fixedSizeTensor (elem : PType) (shape : List Nat) (nullable : Bool)
deriving Repr, BEq, Inhabited

/-- The dtype's own nullability (the first-class face: read it off the
    ctor's flag). -/
def nullableOf : DType → Bool
  | .null => true
  | .bool nl => nl
  | .primitive _ nl => nl
  | .decimal _ _ nl => nl
  | .utf8 nl => nl
  | .binary nl => nl
  | .list _ nl => nl
  | .fixedSizeList _ _ nl => nl
  | .map _ _ _ nl => nl
  | .struct _ nl => nl
  | .union _ nl => nl
  | .variant nl => nl
  | .extension _ _ _ nl => nl
  | .fixedSizeTensor _ _ nl => nl

/-- The nullability MOVE: the same logical dtype, the flag rewritten
    (the option wrapper's dtype-level face — the wrapper adds
    nullability, it does not change the logical type). The null row
    stays null (an all-null column is nullable by nature — the move
    cannot de-null it; the move's law states the move, never more). -/
def setNullable : DType → Bool → DType
  | .null, _ => .null
  | .bool _, b => .bool b
  | .primitive p _, b => .primitive p b
  | .decimal prec scale _, b => .decimal prec scale b
  | .utf8 _, b => .utf8 b
  | .binary _, b => .binary b
  | .list e _, b => .list e b
  | .fixedSizeList e len _, b => .fixedSizeList e len b
  | .map ks k v _, b => .map ks k v b
  | .struct fs _, b => .struct fs b
  | .union vs _, b => .union vs b
  | .variant _, b => .variant b
  | .extension id st md _, b => .extension id st md b
  | .fixedSizeTensor e shape _, b => .fixedSizeTensor e shape b

/-- The move overwrites (every row but null): the last flag wins —
    the composition face the section law's option layer rides. -/
theorem setNullable_setNullable (d : DType) (a b : Bool) (h : d ≠ .null) :
    setNullable (setNullable d a) b = setNullable d b := by
  cases d <;> simp [setNullable] at h ⊢ <;> rfl

/-- The move to a dtype's OWN flag is the identity (the flag round
    trip the section law's option layer rides). -/
theorem setNullable_of_nullable (d : DType) (h : nullableOf d = true) :
    setNullable d true = d := by
  cases d <;> simp_all [nullableOf, setNullable]

/-! ## The SchemaCore.Ty correspondence (the honest grade) -/

/-- The key sub-universe's dtype (the map-keys' lane). -/
def keyTyToDType : KeyTy → DType
  | .bool => .bool false
  | .u64 => .primitive .u64 false
  | .i64 => .primitive .i64 false
  | .string => .utf8 false

/-- THE EMBEDDING: the boundary universe's dtype. The option wrapper
    becomes NULLABILITY (the dtype-level face — the wrapper never
    changes the logical type); result becomes the 2-variant union; set
    becomes the element list (the SET-ness is schema-level); the
    bounded cap is SCHEMA metadata (the dtype face is u64); the map's
    keys-sorted is false (the boundary map declares no sort). -/
def tyToDType : Ty → DType
  | .bool => .bool false
  | .u64 => .primitive .u64 false
  | .i64 => .primitive .i64 false
  | .string => .utf8 false
  | .option e => setNullable (tyToDType e) true
  | .list e => .list (tyToDType e) false
  | .result ok err => .union [tyToDType ok, tyToDType err] false
  | .map k v => .map false (keyTyToDType k) (tyToDType v) false
  | .set k => .list (keyTyToDType k) false
  | .bounded _ => .primitive .u64 false

/-- The image: exactly the dtypes `tyToDType` lands on (the boundary
    universe's dtype face, named — the surjection's CARRIER). The
    nullability faces: BOTH the base and the option-wrapped shapes are
    in the image (the wrapper is a Ty ctor — the flag is content, the
    container shape is the membership); the map's keysSorted is false
    (the boundary declares no sort); the union is the result shape
    (exactly 2 variants); the keys are the four scalars. -/
def inTyImage : DType → Bool
  | .bool _ => true
  | .primitive p _ =>
      match p with
      | .u64 => true
      | .i64 => true
      | _ => false
  | .utf8 _ => true
  | .list e _ => inTyImage e
  | .map ks k v _ => ks == false && keyImage k && inTyImage v
  | .union variants _ =>
      match variants with
      | [a, b] => inTyImage a && inTyImage b
      | _ => false
  | _ => false
where
  /-- The map-keys' image face: the four scalar dtypes (the KeyTy
      sub-universe's dtype lane — a key's dtype is non-nullable). -/
  keyImage : DType → Bool
    | .bool false => true
    | .primitive .u64 false => true
    | .primitive .i64 false => true
    | .utf8 false => true
    | _ => false

/-- The keys' dtype → KeyTy (the section's map-key face; total via the
    u64 filler — the law only uses the image). -/
def dtypeToKeyTy : DType → KeyTy
  | .bool _ => .bool
  | .primitive .u64 _ => .u64
  | .primitive .i64 _ => .i64
  | .utf8 _ => .string
  | _ => .u64

/-- The image's per-shape unfolding faces. `inTyImage` is
    well-founded recursive, so its equations are `backward_defeq` —
    `simp only [inTyImage]` does NOT fire them forward; the unfolding
    goes through the FORWARD equations (rfl-provable per constructor
    shape), ONCE, here, and the law-family rides these names (the
    repeated-agent trap: fighting the unfolding per lemma — never
    again). -/

theorem inTyImage_list (e : DType) (nl : Bool) :
    inTyImage (.list e nl) = inTyImage e := rfl

theorem inTyImage_map_unsorted (k v : DType) (nl : Bool) :
    inTyImage (.map false k v nl) =
      (inTyImage.keyImage k && inTyImage v) := rfl

theorem inTyImage_union2 (a b : DType) (nl : Bool) :
    inTyImage (.union [a, b] nl) = (inTyImage a && inTyImage b) := rfl

/-- The image-preservation face of the nullability move: the image is
    blind to the SELF flag (it reads the CONTAINER shape — the
    elements', variants' and fields' flags are the content). -/
theorem inTyImage_setNullable (d : DType) (b : Bool) :
    inTyImage (setNullable d b) = inTyImage d := by
  cases d with
  | union vs nl =>
      cases vs with
      | nil => simp [setNullable, inTyImage]
      | cons a rest =>
          cases rest with
          | nil => simp [setNullable, inTyImage]
          | cons c rest' =>
              cases rest' with
              | nil => simp only [setNullable, inTyImage_union2]
              | cons _ _ => simp [setNullable, inTyImage]
  | map ks k v nl => simp [setNullable, inTyImage]
  | list e nl => simp [setNullable, inTyImage]
  | _ => simp [setNullable, inTyImage]

/-- THE EMBEDDING LANDS IN THE IMAGE (the surjection's carrier face). -/
theorem inTyImage_tyToDType (t : Ty) : inTyImage (tyToDType t) = true := by
  induction t with
  | bool => rfl
  | u64 => rfl
  | i64 => rfl
  | string => rfl
  | option e ih => simp [tyToDType, inTyImage_setNullable, ih]
  | list e ih => simp [tyToDType, inTyImage, ih]
  | result ok err iho ihe => simp [tyToDType, inTyImage, iho, ihe]
  | map k v ihv =>
      cases k <;>
        simp [tyToDType, inTyImage, keyTyToDType, inTyImage.keyImage, ihv]
  | set k => cases k <;> rfl
  | bounded _ => rfl

/-- THE SECTION (the mutual pair's container face): the total dtype →
    Ty face. Off the image this is the u64 filler (the law never rides
    it); on the image it inverts. The option layer reads the SELF
    flag; the containers recurse through the ELEMENTS' FULL section
    (the elements' nullability is content — only the full section
    carries it). The `termination_by` measure: the union's variants
    ride a `List DType` field, where the structural recursor gives no
    IH — the section law's induction is size-based instead. -/
def dtypeToTy (d : DType) : Ty :=
  if nullableOf d then .option (selfFalseTy d) else selfFalseTy d
where
  /-- The self-flag-off face (the section's inner layer: the SAME
      container shape, the ctor's own nullability dropped). -/
  selfFalseTy : DType → Ty
    | .bool _ => .bool
    | .primitive .u64 _ => .u64
    | .primitive .i64 _ => .i64
    | .primitive _ _ => .u64
    | .utf8 _ => .string
    | .list e _ => .list (dtypeToTy e)
    | .map _ k v _ => .map (dtypeToKeyTy k) (dtypeToTy v)
    | .union variants _ =>
        match variants with
        | [a, b] => .result (dtypeToTy a) (dtypeToTy b)
        | _ => .u64
    | _ => .u64

/-! ### The section's unfolding lemmas

The section is well-founded recursive (the union's variants ride a
`List DType` field, where the structural recursor gives no IH), so
NOTHING about `dtypeToTy` reduces by `rfl`/`show` — the unfolding
goes through the equation lemmas, ONCE, here; the section law below
rides these names (the repeated-agent trap: fighting the unfolding
per lemma — never again). The `simp only` sets close because their
equation lemmas have constructor patterns (no mangling of the
recursive occurrences the law's IHs need). -/

/-- The nullable face: the option wrapper reads the SELF flag. -/
theorem dtypeToTy_nullable (d : DType) (h : nullableOf d = true) :
    dtypeToTy d = .option (dtypeToTy.selfFalseTy d) := by
  simp only [dtypeToTy, h, if_true]

/-- The non-nullable face. -/
theorem dtypeToTy_self (d : DType) (h : nullableOf d = false) :
    dtypeToTy d = dtypeToTy.selfFalseTy d := by
  simp only [dtypeToTy, h, Bool.false_eq_true, if_false]

theorem selfFalseTy_bool (nl : Bool) : dtypeToTy.selfFalseTy (.bool nl) = .bool := by
  simp only [dtypeToTy.selfFalseTy]

theorem selfFalseTy_prim_u64 (nl : Bool) :
    dtypeToTy.selfFalseTy (.primitive .u64 nl) = .u64 := by
  simp only [dtypeToTy.selfFalseTy]

theorem selfFalseTy_prim_i64 (nl : Bool) :
    dtypeToTy.selfFalseTy (.primitive .i64 nl) = .i64 := by
  simp only [dtypeToTy.selfFalseTy]

theorem selfFalseTy_utf8 (nl : Bool) :
    dtypeToTy.selfFalseTy (.utf8 nl) = .string := by
  simp only [dtypeToTy.selfFalseTy]

theorem selfFalseTy_list (e : DType) (nl : Bool) :
    dtypeToTy.selfFalseTy (.list e nl) = .list (dtypeToTy e) := by
  simp only [dtypeToTy.selfFalseTy]

theorem selfFalseTy_map (ks : Bool) (k v : DType) (nl : Bool) :
    dtypeToTy.selfFalseTy (.map ks k v nl) = .map (dtypeToKeyTy k) (dtypeToTy v) := by
  simp only [dtypeToTy.selfFalseTy]

theorem selfFalseTy_union2 (a b : DType) (nl : Bool) :
    dtypeToTy.selfFalseTy (.union [a, b] nl) = .result (dtypeToTy a) (dtypeToTy b) := by
  simp only [dtypeToTy.selfFalseTy]

/-- THE SECTION'S FLAG FACE (the law's false/true fork, ONCE): the
    section reads the self flag (the option layer wraps iff the flag is
    set), and the embedding's own option layer writes the flag back —
    the section's value is the dtype re-flagged. The per-shape fork in
    `dtypeSectionLaw` is this lemma's citation. -/
theorem tyToDType_dtypeToTy_flag (d : DType) (ty : Ty) (hnull : d ≠ .null)
    (hself : dtypeToTy.selfFalseTy d = ty)
    (hinv : tyToDType ty = setNullable d false)
    (b : Bool) (hn : nullableOf d = b) :
    tyToDType (dtypeToTy d) = setNullable d b := by
  cases b with
  | false =>
      rw [dtypeToTy_self _ hn, hself]
      exact hinv
  | true =>
      rw [dtypeToTy_nullable _ hn, hself]
      simp only [tyToDType]
      rw [hinv, setNullable_setNullable d false true hnull,
        setNullable_of_nullable d hn]

/-- THE SECTION LAW: on the image, the section inverts the embedding —
    `tyToDType (dtypeToTy d) = d`. The honest face of the
    correspondence (the `toImageIso` round trip at the image's own
    members); the FULL `Kit.Retraction` grade is impossible — the
    option wrapper collapses — and the header names it. The unfolding
    rides the per-shape lemmas above (WF definitions do not reduce by
    `rfl`/`show`); the union case's element laws ride the recursion
    (the `List DType` field has no structural IH — the measure is
    `sizeOf`). -/
theorem dtypeSectionLaw (d : DType) (h : inTyImage d = true) :
    tyToDType (dtypeToTy d) = d := by
  cases d with
  | null => simp [inTyImage] at h
  | bool nl =>
      rw [tyToDType_dtypeToTy_flag (.bool nl) .bool (by simp)
        (selfFalseTy_bool nl) rfl nl rfl]
      rfl
  | primitive p nl =>
      cases p with
      | u64 =>
          rw [tyToDType_dtypeToTy_flag (.primitive .u64 nl) .u64 (by simp)
            (selfFalseTy_prim_u64 nl) rfl nl rfl]
          rfl
      | i64 =>
          rw [tyToDType_dtypeToTy_flag (.primitive .i64 nl) .i64 (by simp)
            (selfFalseTy_prim_i64 nl) rfl nl rfl]
          rfl
      | _ => simp [inTyImage] at h
  | decimal _ _ _ => simp [inTyImage] at h
  | utf8 nl =>
      rw [tyToDType_dtypeToTy_flag (.utf8 nl) .string (by simp)
        (selfFalseTy_utf8 nl) rfl nl rfl]
      rfl
  | binary _ => simp [inTyImage] at h
  | list e nl =>
      simp only [inTyImage_list] at h
      have he := dtypeSectionLaw e h
      rw [tyToDType_dtypeToTy_flag (.list e nl) (.list (dtypeToTy e)) (by simp)
        (selfFalseTy_list e nl) (by simp only [tyToDType, setNullable]; rw [he]) nl rfl]
      rfl
  | fixedSizeList _ _ _ => simp [inTyImage] at h
  | map ks k v nl =>
      cases ks with
      | true => simp [inTyImage] at h
      | false =>
          simp only [inTyImage_map_unsorted, Bool.and_eq_true] at h
          obtain ⟨hkeyImg, hv⟩ := h
          have hv := dtypeSectionLaw v hv
          have hkey : keyTyToDType (dtypeToKeyTy k) = k := by
            revert hkeyImg
            cases k with
            | bool nl => cases nl <;> intro hk <;>
                first | rfl | (exfalso; simp [inTyImage.keyImage] at hk)
            | primitive p nl =>
                cases p with
                | u64 => cases nl <;> intro hk <;>
                    first | rfl | (exfalso; simp [inTyImage.keyImage] at hk)
                | i64 => cases nl <;> intro hk <;>
                    first | rfl | (exfalso; simp [inTyImage.keyImage] at hk)
                | _ => intro hk; exfalso; simp [inTyImage.keyImage] at hk
            | utf8 nl => cases nl <;> intro hk <;>
                first | rfl | (exfalso; simp [inTyImage.keyImage] at hk)
            | _ => intro hk; exfalso; simp [inTyImage.keyImage] at hk
          rw [tyToDType_dtypeToTy_flag (.map false k v nl)
            (.map (dtypeToKeyTy k) (dtypeToTy v)) (by simp)
            (selfFalseTy_map false k v nl)
            (by simp only [tyToDType, setNullable]; rw [hkey, hv]) nl rfl]
          rfl
  | struct _ _ => simp [inTyImage] at h
  | union variants nl =>
      cases variants with
      | nil => simp [inTyImage] at h
      | cons a rest =>
          cases rest with
          | nil => simp [inTyImage] at h
          | cons b rest' =>
              cases rest' with
              | nil =>
                  simp only [inTyImage_union2, Bool.and_eq_true] at h
                  obtain ⟨himg_a, himg_b⟩ := h
                  have ha := dtypeSectionLaw a himg_a
                  have hb := dtypeSectionLaw b himg_b
                  rw [tyToDType_dtypeToTy_flag (.union [a, b] nl)
                    (.result (dtypeToTy a) (dtypeToTy b)) (by simp)
                    (selfFalseTy_union2 a b nl)
                    (by simp only [tyToDType, setNullable]; rw [ha, hb]) nl rfl]
                  rfl
              | cons _ _ => simp [inTyImage] at h
  | variant _ => simp [inTyImage] at h
  | extension _ _ _ _ => simp [inTyImage] at h
  | fixedSizeTensor _ _ _ => simp [inTyImage] at h
termination_by sizeOf d

/-- The theorem face of the section law (the named carrier). -/
theorem tyToDType_dtypeToTy_image (d : DType) (h : inTyImage d = true) :
    tyToDType (dtypeToTy d) = d :=
  dtypeSectionLaw d h

/-- The nullability move preserves the top ctor's shape (the option
    layer re-flags, never re-shapes — the refusal pin's helper). -/
theorem setNullable_primitive {d : DType} {p : PType} {b nl : Bool}
    (h : setNullable d b = .primitive p nl) :
    ∃ nl', d = .primitive p nl' := by
  cases d with
  | primitive q nq => exact ⟨nq, by simp_all [setNullable]⟩
  | _ => simp [setNullable] at h

/-- THE f* ROW'S REFUSAL FACE (the E3 dtype-policy pin): the boundary
    image's primitive rows are the INT scalars — no float enters the
    static selection. The ALP terminal (`policyRow`'s float row) is
    the NAMED face for when the float lane lands; until then the
    refusal is the honesty — never a silent bitPacked-of-floats lie. -/
theorem tyToDType_no_float : ∀ (t : Ty) (p : PType) (nl : Bool),
    tyToDType t = .primitive p nl → p.isFloat = false := by
  intro t
  induction t with
  | bool => intro p nl h; simp [tyToDType] at h
  | u64 => intro p nl h; simp [tyToDType] at h; cases p <;> simp_all [PType.isFloat]
  | i64 => intro p nl h; simp [tyToDType] at h; cases p <;> simp_all [PType.isFloat]
  | string => intro p nl h; simp [tyToDType] at h
  | option e ih =>
      intro p nl h
      obtain ⟨nl', hd⟩ := setNullable_primitive h
      exact ih p nl' hd
  | list e ih => intro p nl h; simp [tyToDType] at h
  | result ok err iho ihe => intro p nl h; simp [tyToDType] at h
  | map k v ihv => intro p nl h; simp [tyToDType] at h
  | set k => intro p nl h; simp [tyToDType] at h
  | bounded _ => intro p nl h; simp [tyToDType] at h; cases p <;> simp_all [PType.isFloat]
/-- The DType proto message's oneof discriminator: the field number
    each dtype SHAPE occupies in the wire message (the SHAPE as data —
    nullability is content, not a discriminator; the byte face is the
    named seam — Substrait.ProtoBuf's primitives, next wave's kit
    promotion). -/
def dtypeWireTag : DType → Nat
  | .null => 1
  | .bool _ => 2
  | .primitive _ _ => 3
  | .decimal _ _ _ => 4
  | .utf8 _ => 5
  | .binary _ => 6
  | .list _ _ => 7
  | .fixedSizeList _ _ _ => 8
  | .map _ _ _ _ => 9
  | .struct _ _ => 10
  | .union _ _ => 11
  | .variant _ => 12
  | .extension _ _ _ _ => 13
  | .fixedSizeTensor _ _ _ => 14

/-- The dtype SHAPE (the nullability-erased face — the discriminator's
    actual carrier). -/
inductive DTypeKind where
  | nullK | boolK | primK | decimalK | utf8K | binaryK | listK
  | fixedSizeListK | mapK | structK | unionK | variantK | extensionK
  | tensorK
deriving Repr, BEq, DecidableEq, Inhabited

/-- The shape-erasure: the discriminator's kind face. -/
def dtypeKind : DType → DTypeKind
  | .null => .nullK
  | .bool _ => .boolK
  | .primitive _ _ => .primK
  | .decimal _ _ _ => .decimalK
  | .utf8 _ => .utf8K
  | .binary _ => .binaryK
  | .list _ _ => .listK
  | .fixedSizeList _ _ _ => .fixedSizeListK
  | .map _ _ _ _ => .mapK
  | .struct _ _ => .structK
  | .union _ _ => .unionK
  | .variant _ => .variantK
  | .extension _ _ _ _ => .extensionK
  | .fixedSizeTensor _ _ _ => .tensorK

/-- The discriminator registry is INJECTIVE ON THE KINDS (one field
    number per shape — the wire's oneof discipline, total over the
    closed universe). -/
theorem dtypeWireTag_kind_injective (d d' : DType)
    (h : dtypeWireTag d = dtypeWireTag d') :
    dtypeKind d = dtypeKind d' := by
  cases d <;> cases d' <;> simp only [dtypeKind, dtypeWireTag] at h ⊢ <;>
    first
    | rfl
    | (exfalso; omega)

end Vortex

end -- public section
