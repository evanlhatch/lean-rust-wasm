/-
# SchemaLang.Vortex.Batch — the column-oriented batch layer

The tabular half of the Vortex port: a batch is rows over ONE schema,
and the ops are the COLUMN-oriented ones (Vortex's unit of work is the
column). Built entirely over OUR landed layers — `Validate`'s
`RowVals`/`ColPath` (the schema-aligned rows and constructor paths) and
`Subschema`'s total projection — nothing in those modules is touched.

Provenance: flatland's batch layer is engine-domain
(`LaneKernels`/`applyTo`, the kernel templates over mutable state).
What ports cleanly to the schema-language side is the READ side: batch
projection and column extraction, with the retention theorems:

- `RowVals.project_weaken` — the projection is blind to weakening
  (prepending fields to the BIG schema does not change what it reads).
- `RowVals.project_self` — projecting by the reflexive embedding IS
  the identity (the can't-fail projection, retained).
- `RowVals.project_get` / `Batch.col_project` — column extraction
  COMMUTES with projection: reading a column of the projected batch is
  reading the widened path off the original. The read side of a schema
  change is answerable from the row — the `Subschema` header's spec,
  now a theorem over batches.
- `Batch.u64col_rle_roundtrip` — the tie to `Encoding.lean`: a u64
  column RLE-round-trips exactly (the retention theorem, consumed at
  the batch level).

Deliberate exclusions: the WRITE side (gather/scatter, write-disjoint
batch ordering — flatland's `applySeq_perm` territory) needs the
mutable-state engine model; the schema-language side is the total-read
spec those kernels are held to.
-/
module

public import SchemaLang.Validate
public import SchemaLang.Subschema
public import SchemaLang.Vortex.Encoding

@[expose] public section

namespace SchemaLang.Vortex

/-- A batch: rows over ONE schema `fs`, in schema order (the
    column-oriented physical half — the rows are `RowVals`). -/
abbrev Batch (fs : List Field) := List (RowVals fs)

/-- Column extraction: one field's values, out of every row (the
    `ColPath` walk per row — pure data, no closure). -/
def Batch.col {fs : List Field} {n : String} {t : Ty} (p : ColPath n t fs)
    (b : Batch fs) : List (Value t) :=
  b.map p.get

/-- The projection consumed at the batch level: per-row `RowVals.project`
    — total by construction (the can't-fail read). -/
def Batch.project {s' s : List Field} (b : Batch s) (emb : Subschema s' s) :
    Batch s' :=
  b.map (·.project emb)

/-- The projection is blind to weakening: prepending a field to the BIG
    schema (and its rows — the new head value `v`) does not change what
    the projection reads. The recursive shape: `weaken` prepends to the
    big index only, so the row grows by ONE cons and the theorem strips
    exactly that cons. -/
theorem RowVals.project_weaken {smaller bigger : List Field}
    (emb : Subschema smaller bigger) {f : Field} (v : Value f.ty)
    (r : RowVals bigger) :
    (RowVals.cons v r).project (emb.weaken (f := f)) = r.project emb := by
  induction emb with
  | nil => rfl
  | cons h rest ih =>
      simp only [RowVals.project, Subschema.weaken, ColPath.get]
      exact congrArg _ (ih r)

/-- **Projection retention**: the reflexive embedding projects the row
    to ITSELF — the can't-fail projection cannot lose. -/
theorem RowVals.project_self {fs : List Field} (r : RowVals fs) :
    r.project (Subschema.reflexive fs) = r := by
  match r with
  | .nil => rfl
  | .cons v vs =>
      simp only [RowVals.project, Subschema.reflexive, ColPath.get,
        RowVals.project_weaken]
      exact congrArg _ (project_self vs)

/-- **Column/projection commutation**: reading a field out of a
    projected row IS reading the widened path off the original row.
    The induction is on the EMBEDDING (generalizing the row): the
    embedding's `cons` decomposes the SMALL schema, the row is read
    through `project` whole — no case split on the row is needed. -/
theorem RowVals.project_get {s' s : List Field} (emb : Subschema s' s)
    {n : String} {t : Ty} (p : ColPath n t s') (r : RowVals s) :
    p.get (r.project emb) = (emb.widen p).get r := by
  induction emb with
  | nil => cases p
  | cons h rest ih =>
      cases p with
      | here => simp only [RowVals.project, ColPath.get, Subschema.widen]
      | there p' =>
          simp only [RowVals.project, ColPath.get, Subschema.widen]
          exact ih p' r

/-- **Batch projection retention**: extracting a column of the projected
    batch = extracting the widened column of the original batch. The
    old schema's every read is still answerable — at the batch level. -/
theorem Batch.col_project {s' s : List Field} (emb : Subschema s' s)
    {n : String} {t : Ty} (p : ColPath n t s') (b : Batch s) :
    (b.project emb).col p = b.col (emb.widen p) := by
  induction b with
  | nil => rfl
  | cons r rs ih =>
      simp only [Batch.project, Batch.col, List.map_cons]
      rw [RowVals.project_get]
      exact congrArg _ ih

/-- The scalar reading of a u64 value — the physical form the
    encodings consume (the column's boxed layer, unboxed). -/
def u64Unbox : Value .u64 → UInt64
  | .u64 v => v

/-- The u64 column, unboxed to scalars — the shape `rleEncode` acts on. -/
def Batch.u64col {fs : List Field} {n : String} (p : ColPath n .u64 fs)
    (b : Batch fs) : List UInt64 :=
  (Batch.col p b).map u64Unbox

/-- **The encoding tie at the batch level**: the batch's u64 column
    RLE-round-trips exactly (the retention theorem, consumed). -/
theorem Batch.u64col_rle_roundtrip {fs : List Field} {n : String}
    (p : ColPath n .u64 fs) (b : Batch fs) :
    rleDecode (rleEncode (Batch.u64col p b)) = Batch.u64col p b :=
  rleDecode_rleEncode _

end SchemaLang.Vortex
