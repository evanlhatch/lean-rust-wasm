# Design — vortex encoding selection as a derived static function (no runtime search)

Status: design, owner-confirmed direction (2026-09-22). Informed by
flatland's locked policy ("compiler predicts, never searches" —
notes/vortex-fork.md; the stats-driven decision tree —
REBUILD-architecture.md §E8) and the lean-rust-wasm lane audit
(SchemaLang/Vortex: EncodingKind is unconsumed + unparameterized;
selection signals exist but nothing consumes them).

## The core move

Encoding selection is a PURE FUNCTION from static shape facts, with
per-encoding applicability laws — never a runtime tree search
(BTrBlocks is the anti-model; flatland locked the same policy):

    ShapeFacts := { range? : Option (Int × Int)      -- Refine.lean
                  ; cardBound : Option Nat           -- variant/enum cases.length, KeyTy
                  ; sorted? : Option SortDir         -- declared only (see §4)
                  ; nullable : Bool                  -- optionality
                  ; isKey : Bool                     -- Keys.lean (FK → Dict)
                  ; tensorDims? : Option (List Nat)  -- static dims
                  }

    select : DType → ShapeFacts → EncodingSpec      -- total; fallback = bitpack/identity

Every encoding is a `PartialIso` on its ADMISSIBLE SUBDOMAIN (the
Encoding.lean shape — decode∘encode = id where applicable), and the
selection law is:

    applicable enc facts → decode (encode xs) = xs

`applicable` is DECIDABLE over the static facts. The discharge rides
the obligation ladder at the tightest tier that computes:
- range / enum cardinality / key-ness / nullability / dims — fully
  static ⇒ `decidableNow` (or `provedAtElab` for the type-derived ones).
- sortedness / run-length / actual cardinality — data-dependent ⇒
  `oracleSwept` over a sample (the backend is wired; the coverage gate
  makes a dangling row-ref fail CI), OR a host-measured fact with a
  re-derivation trigger (flatland's ~5% re-encode drift threshold).

## The decision tree as data + no dead rules

Flatland's §E8 tree, as a Lean table (the substrait Grammar pattern):
each rule = (guard over ShapeFacts) → encoding; the table carries
`nodup`-on-guards + a totality proof (the fallback row) + a COVERAGE
obligation: every rule must be exercised by a test (flatland's
"falsify-eliminated dead rules" discipline, mechanized).

Order (flatland's locked policy, adapted):
  is-constant → Constant | declared sorted+fixed-step → Sequence |
  FK/enum/low-card → Dict | small int range → FoR over BitPacked(width)
  | float → ALP(precision) | fallback → BitPacked/identity.
RunEnd/Sequence for the event-log-shaped columns (flatland's flagged
gap: its hot set lacked them — we get them from the start).

## The encoding vocabulary upgrade

`EncodingKind` (identity | constant | rle | dict | forr) becomes
parameterized `EncodingSpec`: BitPacked(width), FoR(base), Dict,
RunEnd, Sequence, ALP(precision), Constant, plus Sparse + the frame
codecs as OUTER layers (zstd over the terminal — nested cascades are
non-terminal per flatland §E6: kernels peel layers). Each spec carries
its applicability predicate + its PartialIso instance. The ExtDType
lane stays the extension point for fork-owned encodings.

## The wire contract

The emitter emits the plan per column into the generated host code
(`vortex_generated.rs` gains the encoding hint per column — a byte-tied
artifact change, deliberate re-pin). The host applies the hints at
write time; a measured-drift hook (data contradicts the prediction
beyond the threshold) re-derives the plan via the obligation lane —
a loud event, not silent re-encoding.

## Sequencing

1. EncodingSpec + applicability + PartialIso instances (Encoding.lean).
2. ShapeFacts + its derivation from the universe (Refine/Keys/variants/
   nullability; `sorted?` stays a DECLARED fact — no sortedness
   inference without evidence).
3. `select` + totality + the coverage-obligation wiring.
4. Emitter hints + byte-tie re-pin + the host's apply path.
5. The end-to-end proof-of-life: guestlang-host writes a real .vortex file
   with the predicted encodings, reads it back, values agree (the
   fixture-pair pattern from the snapshot differential).
6. Oracle: the plan's predictions become oracle rows (predicted vs
   applicable on sample data = the oracleSwept discharge evidence).

## Explicit non-goals

No runtime tree search / sampling optimizer (BTrBlocks). No new Ty
ctors (shape facts are metadata). No query-layer work (scope lock).
No FSST/decimal-parts/datetime-parts until a column shape needs them
(the anti-museum rule: an encoding enters the vocabulary with its
consumer).
