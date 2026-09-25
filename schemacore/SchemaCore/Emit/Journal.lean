/- # SchemaCore.Emit.Journal — the journal duel's emitter (the Event
   lane's byte vectors)

Owner: the event-sourcing lane (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/03-bidirectional.md §3 (the differential:
the Lean kernel emits the golden vectors; the Rust consumer agrees or
names the divergence) + the duel discipline (Kit.Duel's vector-set
convention: ONE directory per duel, the vectors the binary lane's
artifacts, a committed text manifest naming the generator + the
expectations). The seed precedent is `SchemaCore.Emit.Rust.duelEmitter`
(the atom codec's differential over the schema-generated crate); THIS
lane's consumer is the `mandate-delta` crate — the host's persistence
lane, whose README names this emitter as its integration step.

THE INSTANTIATION (the honest center): `SchemaCore.Event`'s journal
codec is POLYMORPHIC in its row/key encoders (`encDelta encR encK` /
`encJournal encR encK` over any `fs : List Field`) — the Lean tree
lands no concrete row codec. The `mandate-delta` crate pins ONE
instantiation, documented in its README; THIS module computes that
SAME instantiation through the LANDED codec's own combinators, so the
emitted vectors are the wire's kernel-checked face:

- `encR` — `SchemaCore.encList`'s shape: varint field count + one
  `encVal` per field in schema order (the row's positional values as
  `FieldVal`s);
- `encK` — `SchemaCore.Codec.encKey`'s bytes at the key's own type:
  `encVal kv.ty kv.val` (a `FieldVal`'s `Ty` IS the `KeyTy.toTy` face
  of the scalar universe — `encKey_foldVal` proves `encKey k v` is
  exactly the value fold's scalar slice, so these are encKey's bytes
  verbatim).

The fixture schema is the delta crate's: `id : u64` keyed,
`name : string`. The REFUSAL rows are byte-level splices off the
golden encodings (the tamperVectors discipline — each an out-of-policy
shape the Rust decoder must refuse with a typed error, never a panic).

The five questions (notes/v3/01-core.md):
- root: Crossing — the Event lane's journal codec read into the duel
  vector-set convention (the mandate-delta crate's byte contract).
- carrier grade: the vector paths' nodup IN THE TYPE (Kit.Duel's
  VectorSet proof fields); the bytes are `encDelta`/`encJournal`'s
  kernel-reducible folds — never hand-composed.
- spine reading: the evidence stage — the vectors emit through the ONE
  spine (the manifest's text lane + the vectors' binary lane).
- ladder rung: rung 1 — pure data + total folds; the agreement is
  TESTED on the Rust side (the duel is a regression surface, never a
  theorem — Kit.Duel's header).
- gate row: gen-check (the manifest rides the text compare, the
  vectors the binary loop — the emitter's env-free `regen` is the
  writer's and the gate's ONE copy, `WasmCore.Duel.regen`'s shape) +
  the SchemaTests pins (the vector count, the coverage check, the
  golden bytes, the splices).

Core-only (imports SchemaCore.Event + SchemaCore.Codec + Kit.Duel —
the cone rule).
-/

import SchemaCore.Event
import SchemaCore.Codec
import Kit.Duel

open Kit.Emit

namespace SchemaCore.Emit.Journal

/-! ## The row/key instantiation (the delta crate's documented shape) -/

/-- The fixture schema: the delta crate's slice — `id : u64` keyed,
    `name : string`. -/
def journalFields : List Field :=
  [{ name := "id", ty := .u64 }, { name := "name", ty := .string }]

/-- The row's positional values (the `FieldVal` walk the row codec
    folds — schema order IS the positional order). -/
def rowValsElems : (fs : List Field) → RowVals fs → List FieldVal
  | [], .nil => []
  | _ :: _, .cons v vs => { ty := _, val := v } :: rowValsElems _ vs

/-- THE ROW ENCODER (`encR`): `SchemaCore.encList`'s shape — varint
    field count + one `encVal` per field in schema order. -/
def encRowJ : RowVals journalFields → List UInt8 :=
  fun r => encList (fun kv => encVal kv.ty kv.val) (rowValsElems journalFields r)

/-- THE KEY ENCODER (`encK`): `SchemaCore.Codec.encKey`'s bytes at the
    key image's own type — `encKey_foldVal` ties `encKey k v` to the
    value fold's scalar slice (the key's `KeyTy.toTy` IS the `Ty` a
    `FieldVal` carries), so this is encKey verbatim at the byte level. -/
def encKeyJ : FieldVal → List UInt8 := fun kv => encVal kv.ty kv.val

/-- The frame codec's instantiation (the Event lane's `encDelta`). -/
def encDeltaJ : RowDelta journalFields → List UInt8 :=
  encDelta encRowJ encKeyJ

/-- The whole-log codec's instantiation (the Event lane's
    `encJournal`). -/
def encJournalJ : List (RowDelta journalFields) → List UInt8 :=
  encJournal encRowJ encKeyJ

/-! ## The pinned fixture values -/

/-- The key image: `id = 300`. -/
def key300 : FieldVal := { ty := .u64, val := .u64 300 }

/-- The row `[id = 300, name = "hi"]`. -/
def rowHi : RowVals journalFields :=
  .cons (.u64 300) (.cons (.string "hi") .nil)

/-- The row `[id = 300, name = "ho"]`. -/
def rowHo : RowVals journalFields :=
  .cons (.u64 300) (.cons (.string "ho") .nil)

/-- The three-frame journal: insert 300:hi, update 300:ho, remove 300 —
    the replay ends at the empty table (the delta crate's own pin). -/
def logThree : List (RowDelta journalFields) :=
  [.insert rowHi, .update rowHo, .remove key300]

/-! ## The golden bytes (the LANDED codec's emissions — never hand-composed) -/

/-- The insert frame: tag 0 ++ the row. -/
def goldenFrameInsert : List UInt8 := encDeltaJ (.insert rowHi)

/-- The update frame: tag 1 ++ the row. -/
def goldenFrameUpdate : List UInt8 := encDeltaJ (.update rowHi)

/-- The remove frame: tag 2 ++ the key. -/
def goldenFrameRemove : List UInt8 := encDeltaJ (.remove key300)

/-- The empty journal: the varint count alone. -/
def goldenJournalEmpty : List UInt8 := encJournalJ []

/-- The three-frame journal: varint count + the frames. -/
def goldenJournalThree : List UInt8 := encJournalJ logThree

/-! ## THE REFUSAL ROWS (byte-level splices off the goldens — the
     tamperVectors discipline; each an out-of-policy shape the Rust
     decoder must refuse with a typed error, never a panic) -/

/-- One-frame journal (the unknown-tag splice's substrate). -/
private def journalOne : List UInt8 := encJournalJ [.insert rowHi]

/-- The frame TAG byte outside the ctor image (0/1/2 are the wire's
    whole tag vocabulary — 3 is a splice, never an encoding): the
    journal's count byte stays, the frame's tag byte is spliced. -/
def refuseUnknownTag : List UInt8 :=
  journalOne.take 1 ++ [3] ++ journalOne.drop 2

/-- The three-frame journal, torn at the tail (a torn write's shape —
    the last byte gone). -/
def refuseTruncatedFrame : List UInt8 :=
  goldenJournalThree.take (goldenJournalThree.length - 1)

/-- The remove frame whose key varint is NON-CANONICAL (`0x80 0x00` —
    the canonical-minimal gate's refusal shape). -/
def refuseNoncanonicalKey : List UInt8 :=
  goldenFrameRemove.take 1 ++ [0x80, 0x00]

/-- The insert frame whose ROW COUNT disagrees with the schema's arity
    (count 3, two fields — the count is framing, and a skewed count
    refuses). -/
def refuseRowCountSkew : List UInt8 :=
  goldenFrameInsert.take 1 ++ [3] ++ goldenFrameInsert.drop 2

/-! ## The vector set (Kit.Duel's convention) -/

/-- The duel's directory: ONE directory per duel (Kit.Duel's committed
    convention — the manifest + the vectors live there). This is the
    delta crate's duel directory; the emitter OWNS its paths now (the
    fixture era is over — the vectors' bytes are the Lean kernel's). -/
def duelDir : String := "crates/mandate-delta/tests/duel"

/-- The duel's vector path for one row name. -/
def duelPath (name : String) : String := duelDir ++ "/" ++ name ++ ".bin"

/-- THE JOURNAL DUEL VECTOR SET (Kit.Duel's convention): the Event
    lane's golden bytes + the splices as the binary lane's files, the
    manifest the text lane's. The `decode` notes are the consumer's
    value-level pins (the delta crate's `tests/duel_vectors.rs` parses
    them — a drift from the bytes fails the duel loudly); the `refuse`
    rows are the negative controls. -/
def journalDuel : Kit.Duel.VectorSet where
  dir := duelDir
  name := "journal-delta"
  generator := "SchemaCore.Emit.Journal"
  -- The manifest sits next to Rust code (the artifact-headers gate's
  -- shape contract checks the `//` spelling) — the DRY sweep: the
  -- style is the VectorSet's OWN field.
  style := .doubleSlash
  vectors :=
    [ { path := duelPath "frame_insert", contents := goldenFrameInsert.toByteArray }
    , { path := duelPath "frame_update", contents := goldenFrameUpdate.toByteArray }
    , { path := duelPath "frame_remove", contents := goldenFrameRemove.toByteArray }
    , { path := duelPath "journal_empty", contents := goldenJournalEmpty.toByteArray }
    , { path := duelPath "journal_three", contents := goldenJournalThree.toByteArray }
    , { path := duelPath "refuse_unknown_tag", contents := refuseUnknownTag.toByteArray }
    , { path := duelPath "refuse_truncated_frame", contents := refuseTruncatedFrame.toByteArray }
    , { path := duelPath "refuse_noncanonical_key", contents := refuseNoncanonicalKey.toByteArray }
    , { path := duelPath "refuse_row_count_skew", contents := refuseRowCountSkew.toByteArray } ]
  expects :=
    [ (duelPath "frame_insert", .decode "frame-insert id=300 name=hi")
    , (duelPath "frame_update", .decode "frame-update id=300 name=hi")
    , (duelPath "frame_remove", .decode "frame-remove id=300")
    , (duelPath "journal_empty", .decode "journal-empty")
    , (duelPath "journal_three", .decode "journal insert:300:hi|update:300:ho|remove:300")
    , (duelPath "refuse_unknown_tag", .refuse)
    , (duelPath "refuse_truncated_frame", .refuse)
    , (duelPath "refuse_noncanonical_key", .refuse)
    , (duelPath "refuse_row_count_skew", .refuse) ]

/-! ## The emitter + the regen -/

/-- THE JOURNAL DUEL EMITTER: the manifest rides the TEXT lane, the
    vectors the BINARY lane — Kit.Duel's ONE emitter body
    (`emitterWith`) at this lane's parameters (the DRY sweep; the spec
    is `Unit` — the vector set is a PINNED CONSTANT, so the law field
    is the trivial one; the vector bytes' authority is the
    kernel-reducible codec folds + the SchemaTests pins). -/
def journalDuelEmitter : Emitter Unit :=
  Kit.Duel.emitterWith journalDuel "SchemaCore.Event"

/-- THE REGEN (the writer's and the gate's ONE copy — `WasmCore.Duel.
    regen`'s shape, env-free: a pinned-constant vector set cannot
    fail, so no `Except`). `gates gen-check` byte-ties BOTH lanes
    against this; the `schema` exe writes it. -/
def regen : List GeneratedFile × List BinaryFile :=
  (journalDuelEmitter.run (), journalDuel.vectors)

end SchemaCore.Emit.Journal
