# 13 — The interface index

The contracts between the toolkit's pieces. **This file is an INDEX,
not a spec** — the doctrine's own rule: the committed artifact + its
emitter are the spec of record; a hand-written format spec is a second
authority that drifts. Per interface below: the OWNER (the one writer),
the artifact/entry point, the evidence that pins it, and where the
detail lives (the emitter's module header or a generated doc). A change
to any interface is a versioned event (the breaking gate + the
migration lane apply).

Where a format has no generated doc yet, the detail's home is the
owning module's header — and the missing generated doc is a named gap
(the ModuleDocs discipline extends to these).

## The boundary

| Interface | Owner | Artifact / entry | Evidence |
|---|---|---|---|
| the WIT worlds | schema-lang's WIT emitter (+ wasm-backend for the demo world) | `wit/*.wit`, `demo-world.wit` | wit-parser gate + the skew triple-agreement + the lossless-fragment injectivity law |
| the canonical-ABI flattening (records/variants/async) | wasm-backend's adapter lane | the generated component | the oracle duel + the conformance partitions |
| the WIT error channel (`result<T, fault>`) | the faults lane + the WIT emitter | the committed world | the end-to-end typed-error replay (guest answers typed errors, never traps) |

## The evidence channels

| Interface | Owner | Artifact / entry | Evidence |
|---|---|---|---|
| the oracle manifest + verdicts | wasm-backend Oracle.lean | `lake exe oracle`; `target/diff.json` (committed) | the manifest's byte-frozen hash + the wasm_diff replay + the sabotage control |
| the witness wire (guestVerified) | schema-lang Witness lane | `src/witnesses_generated.rs` + `verify-witness: func(list<u8>) -> bool` | the codec's RoundTripSpec + the checker soundness theorem + the tamper refusals + the guest replay |
| the delta log (persistence) | schema-lang Delta/Trace; wasm-delta is the byte-exact port | the log + its frames | the golden vectors + the crash-recovery suite + the inversion laws |

## The binary formats

| Format | Owner | The law | The note |
|---|---|---|---|
| the envelope (version + length + payload) | schema-lang Codec | version checked first; mismatch = named refusal | both language ports ride the append-form law |
| the atoms (varint, fixed ints, tags, lists, maps, strings, tensors) | schema-lang Codec/CodecValue | `dec (enc a ++ rest) = some (a, rest)` per codec | maps are canonical key-sorted; tensor dims live in the SCHEMA, not the wire |
| the universe snapshot | schema-lang Snapshot (the ONE writer); the committed `goldens/universe.snapshot` baseline | the sweep + the Lean↔Rust differential; the round-trip LAW is deferred (decisions.md) with its cost record | lossless by design (the WIT view is the lossy one, never the baseline) |

## The diagnostic + generation contracts

| Contract | Owner | The rule |
|---|---|---|
| the E-code universe | the faults package | ONE code space (Lean elaboration + gates + Rust spans + wasm refusals); STABLE persisted allocation (never position/import-derived — the review catch) |
| the generated-Rust conventions | the emitters | `src/*_generated.rs`; the 2-line GENERATED header (tool + timestamp + spec-sha + content hash + regen recipe); `#[rustfmt::skip]` (the emitter is the formatting authority); consumers `#[path]`-include |
| the gates' subcommand contracts | the gates exe | each subcommand: inputs + the verdict shape + the exit code + its baseline discipline (the committed report + the loud re-baseline); a new subcommand = a registry row + the driver + a justfile delegation line |
| the CI surface | the justfile + .github/workflows | `just gates` locally; CI runs the same; a red gate names the gate + the divergence, never a bare failure |

## The rule for this file

Adding an interface = adding its ROW here (owner + artifact + evidence)
in the same change as the interface. Changing an interface = the
breaking gate + the migration lane. A row whose evidence column rots is
a docs-check/self-audit finding. The formats themselves are NEVER
specified here — the emitter + the artifact are the truth; this file is
the map to them.
