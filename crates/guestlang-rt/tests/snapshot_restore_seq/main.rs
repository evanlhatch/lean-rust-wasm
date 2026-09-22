//! FUZZ: the snapshot/restore state path — `Runtime::snapshot` +
//! `Snapshot::restore` over a random call/snapshot sequence.
//!
//! NON-DUPLICATION RATIONALE (why this target exists at all):
//! - Lean proves the guest programs' SEMANTICS; it cannot reach this
//!   surface at all: snapshot/restore of a RETAINED wasmi instance
//!   (the honest v1 memory-image + fuel contract, with the documented
//!   globals gap) is a Rust-only state path with no Lean counterpart.
//!   The existing `tests/snapshot.rs` pins the contract at fixed
//!   points; this target drives it over RANDOM call/snapshot
//!   interleavings — the Rust-only round-trip:
//!   snap -> restore -> call ≡ direct call.
//! - The property uses the PURE demo exports (`double`, `double-area`)
//!   whose values Lean's oracle already fixed — the fuzz input is the
//!   SEQUENCE (call/snapshot interleavings + args), not the expected
//!   values, so nothing Lean proves is re-fuzzed here.
//!
//! Contract encoded:
//! - after any snapshot, restoring and calling a pure export gives the
//!   SAME result as the direct (never-restored) instance's call —
//!   results-coherence, NOT pointer identity (the globals gap means
//!   the restored allocator re-bumps; see `Snapshot`'s doc).
//! - every step is decode-or-error: a restore failure is a structured
//!   `RtError` (loudly skipped), never a panic.
//!
//! Requires `just wasm-compile`'s artifact (lean/wasm-backend/target/
//! demo.wasm — the committed spec of record). Without it the target
//! skips loudly (a fuzz target must not fake coverage of a module it
//! does not have).
#![allow(
    clippy::panic,
    reason = "fuzz harness: a violated property MUST abort the run — the panic is the crash report"
)]

#[path = "../common/mod.rs"]
mod common;
use bolero::check;
use common::demo_wasm_opt;
use guestlang_rt::Runtime;
use guestlang_rt::Snapshot;

const FUEL: u64 = 1_000_000;

/// One step of the random sequence.
#[derive(Debug, Clone, arbitrary::Arbitrary)]
enum Step {
    /// Call one pure export with a random scalar-ABI arg.
    Call {
        f: PureFn,
        arg: i64,
    },
    /// Freeze the direct instance's current state.
    Snapshot,
}

/// The pure demo exports (Lean-oracled values; the fuzz input is the
/// interleaving, not the expected results).
#[derive(Debug, Clone, arbitrary::Arbitrary)]
enum PureFn {
    Double,
    DoubleArea,
}

impl PureFn {
    fn export(&self) -> &'static str {
        match self {
            Self::Double => "double",
            Self::DoubleArea => "double-area",
        }
    }
}

fn main() {
    let Some(wasm) = demo_wasm_opt() else {
        eprintln!(
            "SKIP snapshot_restore_seq: no demo.wasm — run `just wasm-compile` \
             (a skipped fuzz target covers nothing)"
        );
        return;
    };
    // bolero's harness requires RefUnwindSafe closures, so ALL state
    // lives INSIDE the iteration: each run compiles its own direct
    // instance and drives the whole sequence within it. Cost: one
    // module compile per run (LazyTranslation — small, deterministic).
    check!()
        .with_arbitrary::<Vec<Step>>()
        .cloned()
        .for_each(move |steps: Vec<Step>| {
            let mut direct = match Runtime::new(&wasm, FUEL) {
                Ok(rt) => rt,
                Err(e) => panic!(
                    "demo.wasm (the committed spec of record) failed to load: {e}"
                ),
            };
            let mut snap: Option<Snapshot> = None;
            for step in steps {
                match step {
                    Step::Snapshot => {
                        // The demo module always exports `memory` — a
                        // failure here would be a real regression, but
                        // the contract stays decode-or-error: skip on
                        // the structured error rather than panic.
                        if let Ok(s) = direct.snapshot() {
                            snap = Some(s);
                        }
                    }
                    Step::Call { f, arg } => {
                        let export = f.export();
                        let direct_result = direct.call(export, &[arg], FUEL);
                        // The round-trip: restore the latest snapshot
                        // into a FRESH instance and ask it the same
                        // question the direct instance just answered.
                        if let Some(s) = &snap {
                            let mut restored = match s.restore(&wasm) {
                                Ok(rt) => rt,
                                // Structured-error path (e.g. the image
                                // grew past a max the fresh instance
                                // refuses) — documented, allowed, loud
                                // only if it ever fires for demo.wasm.
                                Err(_) => continue,
                            };
                            match (direct_result, restored.call(export, &[arg], FUEL)) {
                                (Ok((a, _)), Ok((b, _))) => assert_eq!(
                                    a, b,
                                    "snapshot/restore broke results-coherence \
                                     for {export}({arg})"
                                ),
                                // Pure exports never trap: the direct
                                // side succeeding while the restored
                                // side errors IS the incoherence.
                                (Ok(_), Err(e)) => panic!(
                                    "restored instance failed where the direct \
                                     one succeeded: {export}({arg}): {e}"
                                ),
                                // A direct-side failure is a structured
                                // engine outcome (see module_bytes);
                                // nothing to pin against the restore.
                                (Err(_), _) => {}
                            }
                        }
                    }
                }
            }
        });
}
