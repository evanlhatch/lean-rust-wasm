//! The bolero property/fuzz LAYER over the delta-log DECODER (the
//! log/codec reader), additive to the crash-recovery suite
//! (`crash_recovery.rs`, the torn-tail sweep): that suite proves
//! TRUNCATIONS at every offset recover; this layer attacks the
//! remaining corruption classes with RANDOM mutations — byte flips,
//! byte deletions, arbitrary journals — where the sweep is silent.
//!
//! Two targets, both run under plain `cargo test` (bolero's test
//! engine, deterministic iteration count — not a cargo-fuzz-night
//! campaign):
//!
//! 1. ARBITRARY JOURNAL: any byte string is a journal; `open_with`
//!    must return Ok (with the decoded-entry invariants) or a
//!    STRUCTURED `DeltaError` (Corrupt / WrongVersion /
//!    FingerprintMismatch — never a silent accept, never a panic).
//! 2. VALID-THEN-MUTATED: a genuinely valid journal (built through
//!    the real `append` path, so the envelopes are exactly the
//!    writer's output) with ONE random byte flipped, one byte
//!    deleted, or a random truncation — the mutation complement of
//!    the crash-recovery sweep. Same Ok-or-structured-Err contract,
//!    plus: a surviving open decodes NO MORE entries than were
//!    written (mutation can merge or drop records, never invent
//!    them).
//!
//! Replay discipline: bolero prints `BOLERO_RANDOM_SEED=<n>` on a
//! failure; re-run with that env var set to reproduce the exact case.
//! The mutation RNG is derived from the input bytes, so the seed
//! alone reconstructs everything.

use std::sync::atomic::{AtomicUsize, Ordering};

use wasm_delta::{Backend, Change, DeltaError, DeltaLog, Field, Row, Schema, SchemaSet, Ty, Value};

/// The iterations per `cargo test` run (the CI lane — the long
/// campaigns are `just fuzz`'s business).
const ITERATIONS: usize = 512;

/// The single-table schema set the fuzz journals speak (the
/// crash-recovery suite's table: `k u64`, `v Str`).
fn schemas() -> SchemaSet {
    let mut s = SchemaSet::new();
    s.register(
        "t",
        Schema::new(vec![
            Field { name: "k".into(), ty: Ty::U64 },
            Field { name: "v".into(), ty: Ty::Str },
        ]),
    );
    s
}

/// A journal of raw bytes (the fuzz input IS the journal): the
/// `Backend` seam means the decoder is attacked in memory — no fs,
/// no IO failure mode to mask a decode bug.
struct RawJournal(Vec<u8>);

impl RawJournal {
    fn bytes(&self) -> &[u8] {
        &self.0
    }
}

impl Backend for RawJournal {
    fn load(&mut self) -> Result<Vec<u8>, DeltaError> {
        Ok(self.0.clone())
    }

    fn append(&mut self, record: &[u8]) -> Result<(), DeltaError> {
        self.0.extend_from_slice(record);
        Ok(())
    }

    fn truncate(&mut self, len: u64) -> Result<(), DeltaError> {
        self.0.truncate(usize::try_from(len).unwrap_or(usize::MAX));
        Ok(())
    }
}

/// Deterministic small PRNG seeded from the fuzz input (the
/// crash-recovery suite's Lcg): the mutation schedule is a pure
/// function of the input, so a printed seed replays exactly.
struct Lcg(u64);

impl Lcg {
    fn from_bytes(bytes: &[u8]) -> Self {
        let mut seed = 0xcbf2_9ce4_8422_2325u64; // FNV offset basis
        for b in bytes {
            seed ^= u64::from(*b);
            seed = seed.wrapping_mul(0x0000_0100_0000_01b3);
        }
        Self(seed | 1)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 16
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A random valid row for table `t`.
fn fuzz_row(schema: &Schema, r: &mut Lcg) -> Row {
    Row::new(schema, vec![Value::U64(r.below(8)), Value::Str(format!("fuzz-{}", r.below(1000)).into())])
        .unwrap_or_else(|| panic!("fuzz row checks"))
}

/// Build a GENUINELY valid journal through the real append path.
fn build_valid_journal(r: &mut Lcg) -> (Vec<u8>, usize) {
    let schema = schemas().get("t").unwrap_or_else(|| panic!("registered")).clone();
    let mut log = DeltaLog::open_with(RawJournal(Vec::new()), schemas())
        .unwrap_or_else(|e| panic!("empty journal opens: {e}"));
    let n = 1 + r.below(8) as usize;
    for i in 0..n {
        let change = match r.below(3) {
            0 => Change::Insert(fuzz_row(&schema, r)),
            1 => Change::Update(fuzz_row(&schema, r)),
            _ => Change::Remove(Value::U64(r.below(8))),
        };
        log.append("t", change)
            .unwrap_or_else(|e| panic!("valid append {i} must land: {e}"));
    }
    let bytes = log.backend().bytes().to_vec();
    (bytes, n)
}

/// The decoded-open contract: Ok entries all speak a known table,
/// state equals prefix replay (the crash-recovery invariant), and any
/// Err is one of the STRUCTURED decode classes (the in-memory backend
/// cannot produce `Io`; `UnknownTable`/`SchemaMismatch` are
/// append-time classes).
fn assert_open_contract(bytes: Vec<u8>, max_entries: Option<usize>) {
    match DeltaLog::open_with(RawJournal(bytes), schemas()) {
        Ok(log) => {
            for e in log.entries() {
                assert_eq!(e.table, "t", "decoded entry named an unregistered table");
            }
            if let Some(max) = max_entries {
                assert!(
                    log.len() <= u64::try_from(max).unwrap_or(u64::MAX),
                    "mutation DECODED MORE entries ({} > {max}) than were written",
                    log.len()
                );
            }
            // state == replay (the crash-recovery invariant, with the
            // suite's None-is-empty normalization for a table with no
            // decoded entries yet)
            let rows_of = |t: Option<wasm_delta::Table>| t.map(|t| t.rows().count()).unwrap_or(0);
            assert_eq!(
                rows_of(log.state("t").cloned()),
                rows_of(log.state_at("t", log.len())),
                "state != replay at the log's own length"
            );
        }
        Err(e @ DeltaError::Io(_))
        | Err(e @ DeltaError::UnknownTable(_))
        | Err(e @ DeltaError::SchemaMismatch { .. }) => {
            panic!("in-memory open leaked a non-decode error: {e}")
        }
        Err(DeltaError::WrongVersion { .. } | DeltaError::FingerprintMismatch { .. } | DeltaError::Corrupt { .. }) => {
            // the structured decode classes: exactly what the contract
            // allows (data, not strings — see DeltaError)
        }
    }
}

/// TARGET 1: an arbitrary byte string IS a journal — the decoder must
/// never panic and never silently accept garbage.
#[test]
fn arbitrary_journal_never_panics() {
    let ran = AtomicUsize::new(0);
    bolero::check!()
        .with_iterations(ITERATIONS)
        .for_each(|input: &[u8]| {
            ran.fetch_add(1, Ordering::Relaxed);
            assert_open_contract(input.to_vec(), None);
        });
    assert!(
        ran.load(Ordering::Relaxed) >= ITERATIONS,
        "vacuous: the target did not run its iterations"
    );
}

/// TARGET 2: valid-then-mutated — ONE random edit (flip / delete /
/// truncate) over a genuinely valid journal. The structured-error
/// complement of the crash-recovery sweep: random corruption, not
/// just truncation.
#[test]
fn valid_then_mutated_is_ok_or_structured_err() {
    let ran = AtomicUsize::new(0);
    bolero::check!()
        .with_iterations(ITERATIONS)
        .for_each(|input: &[u8]| {
            ran.fetch_add(1, Ordering::Relaxed);
            let mut r = Lcg::from_bytes(input);
            let (bytes, n) = build_valid_journal(&mut r);
            if bytes.is_empty() {
                return; // cannot happen (n >= 1), but never index into empty
            }
            let mut mutated = bytes;
            match r.below(3) {
                0 => {
                    // flip one byte anywhere
                    let pos = r.below(mutated.len() as u64) as usize;
                    mutated[pos] = (r.next() & 0xff) as u8;
                }
                1 => {
                    // delete one byte anywhere
                    let pos = r.below(mutated.len() as u64) as usize;
                    mutated.remove(pos);
                }
                _ => {
                    // random truncation (the sweep's op, random point)
                    let cut = r.below((mutated.len() + 1) as u64) as usize;
                    mutated.truncate(cut);
                }
            }
            assert_open_contract(mutated, Some(n));
        });
    assert!(
        ran.load(Ordering::Relaxed) >= ITERATIONS,
        "vacuous: the target did not run its iterations"
    );
}
