# verified-ledger study — 2026-09-15

Source: /tmp/verified-ledger (welltyped-systems; ~1k lines total: Lean
model 59 + proofs 146 + FFI 39, Rust impl+fuzz ~600). Read in full.
Companion: notes/cedar-study.md.

## What it is

The minimal complete loop of our genre: a Lean 4 model of a ledger
(deposit/withdraw/transfer over `List (String × UInt64)`), frame
theorems per op, an intentionally-buggy Rust implementation, and a
seeded differential fuzzer that catches the bugs. `cargo run` drives
everything; build.rs invokes `lake`.

## The third interop pattern (the reason it matters)

Cedar: lean-sys + Rust RAII + protobuf-in/JSON-out (broad interface).
verified-ledger: **`lake lean FFI.lean -- -c out.c`** — Lean compiled to
C SOURCE — plus a ~100-line hand-written C shim presenting a
project-owned stable C ABI (`src/lean_wrapper.c`: C strings + u64 in,
`void*` opaque state handles, `ok` out-params). Rust binds ONLY the
shim. No lean-sys, no `lean_object` in Rust, cargo rebuilds Lean via
`rerun-if-changed` (build.rs:1-5). Lean-side: `@[export]` on plain
defs (FFI.lean — 5 exports, live `State` passed as opaque handle).

Trade: ABI churn absorbed in C (the most stable possible Rust-side
interface), at the cost of hand refcounting in C and — their one real
mistake — reading Lean STRUCTURE FIELDS in C (`lean_ctor_get_uint8`,
wrapper:62-70): ctor layout coupling.

**Our synthesis (the solid-as-fuck rule):** verified-ledger's build
simplicity + cedar's "only bytes cross" discipline + our proved codec.
Concretely: C-shim pattern, but the payload is ALWAYS a byte array in
our codec's wire format (round-trip-proved on the Lean side) and
handles are fully opaque — no field reads in C, ever. Interface stays
≤ ~10 functions of scalars + bytes. This kills: lean-sys version
coupling, hand-C layout coupling, and marshaling mirrors, in one
move. If a rich live-object channel is ever needed, THAT is when
cedar's Rust-RAII layer earns its complexity.

## The proof shape (per-op frame conditions)

146 lines proving, per op: effect on the target account, non-effect
on all OTHER accounts, and the failure mode. This is exactly our
`ColPath.set_neutral` / `TickCascade` locality family instantiated at
application level — and the evidence that our abstraction pays: their
`balance_filter_other`-style hand lemmas are what `set_neutral` +
`reads`-derived congruence give us structurally. (Their proofs are
workmanlike, `open Classical`, not golfed — fine for 146 lines, not a
style to scale.)

## What it teaches the ledger dogfood (execution-plan W5.1)

verified-ledger is the SHAPE our `lean/ledger` should grow past —
theirs is the pre-tooling version of ours:
- Their `Op` inductive + `apply` + `applyAll` fold = our Machine +
  event-sourcing lane (`@[event_sourced]`: delta variant + journal +
  replay + migration, derived).
- Their frame theorems = our derived `reads`/locality theorems.
- Their missing invariant: conservation (total supply invariant across
  transfer) — ours is one `schema_invariant` with a `proved` citation.
- Their intentional-bug fuzzing = our sabotage controls, which we
  already gate harder (the wasmtime/wasmi duel).
The dogfood success criterion: our ledger demo should express their
entire system — model, ops, invariants, differential harness — as
schema items + updates + one machine, with the Rust side and the
oracle manifest GENERATED. ~100 author lines reproducing their 1k.
