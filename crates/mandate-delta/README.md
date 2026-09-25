# mandate-delta

The host's persistence lane: the append-only delta log over
SchemaCore's delta/journal model. **The byte format is the Lean side's
codec, ported byte-exact** — this crate invents no format; every byte
it writes is a byte `SchemaCore` emits. Hand-written crate (no emitter
owns it; the ownership gate's scan roots do not include it).

## The wire (the spec of record is the Lean codec; this is the map)

| Layer | Lean owner | The bytes |
|---|---|---|
| atoms | `SchemaCore.Codec` | bool = 1 byte (0/1); u64 = canonical-minimal LEB128 varint; i64 = varint of the zigzag; string = varint char count + one varint code point per char (NOT UTF-8) |
| frame | `SchemaCore.Event.encDelta`/`decDelta?` | tag byte in CTOR ORDER (0 = insert, 1 = update, 2 = remove — reordering is a WIRE-BREAKING change) + the self-delimiting payload: insert/update → `enc_row`, remove → `enc_key` |
| whole-log wire | `SchemaCore.Event.encJournal`/`decJournal?` | varint count + the frames in occurrence order |

The Lean journal codec is POLYMORPHIC in its row/key encoders
(`encDelta encR encK`); it lands no concrete row codec yet, so this
crate pins ONE instantiation, built from the Lean codec's OWN
combinators:

- `enc_row(row)` := `SchemaCore.encList`'s shape — varint field count +
  one `encVal` per field in schema order;
- `enc_key(k)` := `SchemaCore.Codec.encKey` verbatim (the key's type
  rides the schema's key field).

Value universe in scope: the scalar `KeyTy` sub-universe (bool/u64/
i64/string). The container arms of `SchemaCore.Ty` land here only with
their Lean-side byte-exactness authority — a Rust-side arm without a
Lean emitter would be format invention.

## The duel vectors (the journal duel emitter — LANDED)

The duel directory `tests/duel/` is the journal duel emitter's artifact
surface: `SchemaCore.Emit.Journal` (Lean, `schemacore/SchemaCore/Emit/
Journal.lean`) computes every byte through the LANDED journal codec
(`SchemaCore.Event.encDelta`/`encJournal`) over EXACTLY the
instantiation documented above, plus the four refusal splices (the
tamperVectors discipline — tag outside the ctor image, a torn tail, a
non-canonical key varint, an arity-skewed row count). The manifest is
the generator's too (the `generator` row names the module); the vectors
+ manifest commit through the byte-tie (`just gen` writes, `gates
gen-check` byte-ties the manifest's text lane AND each vector's binary
lane through its `.hdr` sidecar). Never hand-edit any of it — `just
gen` restores.

This crate's consumer is `tests/duel_vectors.rs` (Kit.Duel's consumer
contract: manifest reader, decode/refuse rows, decode → re-encode byte-
identical, the value pins parsed from the `decode` notes). A wire drift
between the Lean kernel's encodings and this crate fails the duel
loudly — the crate's byte-exactness is mechanically enforced, never
asserted.

## The atom codec's one home

The atom implementations (the canonical-minimal varint, the zigzag, the
char-varint string) live in the generated crate `schema-generated`
 ONLY — this crate depends on it (`Cargo.toml`'s one dependency) and
consumes the codec; `src/value.rs` keeps the `Ty`/`Value` layer + the
count-framing wrapper, and re-exports `enc_varint`/`zigzag_i64`. The
generated codec's u64 range gate (a canonical varint in `[2^64, 2^70)`
refuses — never a wrapped value) is the reason: the hand-mirrored
decoder this replaced silently wrapped that shape at the count and atom
positions; the generated codec's gate + the `u64_range_gate_never_wraps`
test are the fix's teeth.

## The crash-recovery honesty

The log is a frame stream; open walks it frame by frame:

- a **truncated tail** (the decoder ran past EOF — the ONLY shape a
  torn write can produce at the tail, since a crash mid-append leaves
  the file a good prefix): the recovering open (`DeltaLog::open`)
  cuts the backend to the last good frame AND REPORTS the cut
  (`log.recovery()` — offset + surviving frames). `DeltaLog::
  open_strict` refuses the same tail with the typed `TornTail` error.
  Never a silent truncation;
- a **complete frame that fails to decode** (unknown tag, invalid
  atom, non-canonical varint, ill-typed payload): the typed `Corrupt`
  error in EVERY mode — the log refuses, it never truncates data away
  (mid-log corruption is not a torn write's shape);
- every decode refusal is a typed error — never a panic, never a
  silent misparse (the accepted-byte policy is the exact image of the
  encoder, Lean-side theorem-backed).

## The inversion

`SchemaCore.Delta`'s witnessed shape, not a second scheme: each
entry's witness (position + OLD row + NEW row) is computed against the
state at its append/replay time; `rewind_to(seq)` applies the inverse
journal (`reverse ∘ invertW`) through CHECKED patches — a lying
witness refuses — and the result is checked against the independent
prefix replay (`state_at`): a disagreement is the typed refusal. The
witnesses are in-memory data (Lean names no witness wire bytes —
`SchemaCore.Delta`'s declared exclusion), so the on-disk format stays
exactly the Lean journal codec's. A durable rollback surface
(compensation appends) follows its first consumer.

## Build / test

```
export PATH="/home/evan/lean-rust-wasm/legacy/.devenv/profiles/wasm/profile/bin:$PATH"
export CC=/home/evan/lean-rust-wasm/legacy/.devenv/profiles/wasm/profile/bin/cc
cd crates/mandate-delta && cargo test
```
