//! # wasm-delta — host-side persistence for the delta/trace model
//!
//! The append-only delta log for the event-sourcing shape
//! (notes/vision.md: "deltas at the boundary, inversion in the log").
//! The wire format is NOT invented here: it is the Lean-side codec —
//! `SchemaLang.Codec` (varint/combinators/envelope),
//! `SchemaLang.CodecValue` (typed values), `SchemaLang.Trace` (rows,
//! schema-out-of-band), `SchemaLang.Delta` (the change variant:
//! insert/update full record, remove key; wire tags in declaration
//! order) — ported byte-exact and pinned by golden vectors generated
//! from the Lean definitions (tests/codec_golden.rs).
//!
//! Inversion mirrors `Dbsp.ChangeSpec.ChangeInversion`
//! (`correct_invert`: `patch (patch t Δ) (invert Δ) = t`): every logged
//! entry carries its inverse computed against the materialized state
//! at append time (invertible-by-construction); `rewind_to` replays
//! stored inverses as compensation appends.
//!
//! Backend decision: the `Backend` trait is the seam; v1 ships
//! `MemBackend` + `FsBackend` (append-only file over `std::fs`,
//! `sync_data` per append, torn-tail truncation on open). NAMED
//! FOLLOW-UP: a sled or redb embedded-KV backend — neither is in the
//! workspace's offline dependency tree (Cargo.lock has neither; the
//! vendor dir holds only gonzalgo), so the durable v1 is the file
//! backend and the KV backend lands behind the same trait when the
//! dependency becomes available.
//!
//! Deliberate exclusions: floats, tensors, `.ty` refs, futures/streams
//! (the `CodecClosed` doctrine — see value.rs). Multi-writer/concurrent
//! logs: out (one writer per log; the engine is single-threaded by
//! design).

#![forbid(unsafe_code)]
#![warn(missing_docs)]

mod codec;
pub mod delta;
mod log;
pub mod row;
pub mod value;

pub use delta::{Change, Table};
pub use log::{Backend, DeltaEntry, DeltaError, DeltaLog, FsBackend, MemBackend, SchemaSet, VERSION};
pub use row::{Field, Row, Schema, decode_row, encode_row};
pub use value::{Ty, Value, decode_value, encode_value};
