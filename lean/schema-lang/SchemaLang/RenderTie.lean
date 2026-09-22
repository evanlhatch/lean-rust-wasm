/-
# SchemaLang.RenderTie — the scalar-spelling agreements MEANT to hold across targets

Pins the narrow contract between the snapshot-text renderer and the Rust
type renderer for the `KeyTy` scalar atoms:

- `KeyTy.toSnapshot` (SchemaLang.Snapshot — the committed-universe text:
  `bool`, `u8`…`u64`, `i8`…`i64`, `string`) vs
- `SchemaLang.Emit.Rust.keyRust` (the Rust domain-crate type spellings:
  `bool`, `u8`…`u64`, `i8`…`i64`, `String`).

What is MEANT to hold: the numeric atom spellings agree VERBATIM between
the two targets (`i8` over there = `i8` over here). The one intended
divergence is the string casing: the snapshot text keeps `string` (its
parser's token — see `Snapshot.tyTokenLegals`), Rust needs the
capitalized type name `String`.

What is target-divergent BY DESIGN and therefore NOT pinned here: the WIT
emitter spells the same scalars `s8`…`s64` (its signed-integer prefix)
and `string`. Cross-target divergence is CONTENT, not drift — the B5
correction: an emitter disagreement with the snapshot/Rust pair is a
design fact to record, not a drift signal to "fix". A drift signal is
only an UNINTENDED change within one target's spelling. These theorems
exist so the intended agreements can never silently drift without a
compile-time flag.
-/

module

public import SchemaLang.Snapshot
public import SchemaLang.Emit.Rust

@[expose] public section

namespace SchemaLang

/-- The numeric `KeyTy` atoms render VERBATIM identically in the
    snapshot text and the Rust type emitter; the only KeyTy divergence is
    the string casing (`string` vs `String` — pinned separately). If this
    theorem stops closing, an emitter spelling drifted. -/
theorem KeyTy.snapshot_rust_numeric (k : KeyTy) (h : k ≠ .string) :
    KeyTy.toSnapshot k = SchemaLang.Emit.Rust.keyRust k := by
  cases k <;> (try contradiction) <;> rfl

/-- The NEGATIVE pin: the string casing divergence is intended, not
    drift — the snapshot keeps its parser's lowercase `string` token, the
    Rust emitter requires the capitalized type name `String`. -/
theorem KeyTy.snapshot_string_ne_rust :
    KeyTy.toSnapshot .string ≠ SchemaLang.Emit.Rust.keyRust .string := by
  decide

end SchemaLang
