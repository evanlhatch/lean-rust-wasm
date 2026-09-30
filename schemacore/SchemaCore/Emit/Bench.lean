/-
# SchemaCore.Emit.Bench — the bench/e2e face (wave-30 C2)

Owner: the codegen-target lane (the mandate tree, `schemacore/`).
Driving decisions: notes/design-wave-30.md C2 (the flatland bench
templates — benches as DUEL ROWS: candidate vs baseline, same seeded
inputs, the threshold verdict — plus the e2e validator generated per
schema) and Kit.Duel's bench discipline (the `BenchSpec` pair + the
`BenchThreshold`/`BenchVerdict` vocabulary — ONE decision walk, two
renderings: this module renders its Rust face).

THE THREE ARTIFACTS (each byte-tied by `gates gen-check`; the ONE
writer is `benchEmitter`, the writer `just gen` + the gate's regen
share the fold):

- `crates/schema-generated/benches/codec_round_trip.rs` — the codec
  round-trip bench: the GENERATED codec vs the hand-rolled Vec walk,
  same LCG-seeded rows, divan (`harness = false`), mimalloc,
  black_box, the sample count scaled — and the THRESHOLD verdict
  printed from `main` (a lone number is telemetry). The profiled face
  (`bench_profiled`) rides the PRODUCTION scopes: C1's
  `schema.example.encode`/`decode` spans ARE the instrumentation —
  the bench opens no span of its own.
- `crates/mandate-delta/benches/commit_path.rs` — the commit-path
  bench: propose/check/commit (witness_of PROPOSES, patch_w_checked
  CHECKS, the patched state COMMITS) at N rows vs the hand-rolled
  keyed Vec walk, same seeded deltas, the same verdict discipline.
  The delta crate has no fast-observe dep yet — the profiled seam is
  NAMED in the file, not faked.
- `crates/schema-generated/tests/e2e_validator.rs` — the e2e
  validator: the twin-world discipline (two loads of the same seeded
  log — direct vs wire-mediated — produce IDENTICAL state hashes at
  EVERY step) + the per-rule expected values with notes. CI runs THIS
  (`just rust`); the benches are the perf face, on demand (`just
  bench`).

Each bench dir carries a `manifest.txt` (Kit.Duel's benchManifestRows
— the consumer contract: the pair, the seed, the threshold live in
ONE place, read via `include_str!`, never re-encoded in the bench).

The five questions (notes/v3/01-core.md):
- root: Crossing — the registry's items read into the benches' +
  validator's provenance, the bench discipline into their verdicts.
- carrier grade: the emitter's outputs nodup IN THE TYPE; the pins
  are the run-then-pin loop's committed known answers (deterministic
  by the seed — never re-measured by hand).
- spine reading: the evidence stage — the benches/validator are
  artifacts through the ONE spine (the text lane); they READ the
  manifests, never re-encode them.
- ladder rung: rung 1 — pure data + total folds; the verdicts are
  TESTED harness output, never theorems (Kit.Duel's header).
- gate row: gen-check (byte-tie per artifact) + audit (the
  banned-pattern sweep) + ownership (the declared set) — the
  ownership gate's rows land with this emitter's wiring.
-/

import SchemaCore.Emit
import Kit.Duel

open Kit
open Kit.Emit

namespace SchemaCore.Emit.Bench

/-! ## The bench rows (Kit.Duel's BenchSpec — the pair, Lean-side) -/

/-- The codec round-trip row: the generated codec vs the hand Vec
    walk over 64 LCG-seeded rows (seed 42), the flatland 5% band. -/
def codecRoundTrip : Kit.Duel.BenchSpec :=
  { name := "codec-round-trip"
    candidate := "generated-codec"
    baseline := "hand-vec"
    seed := 42
    rows := 64
    threshold := .fivePct
    note := "the generated wire's round trip vs the no-codegen hand walk" }

/-- The commit-path row: the witnessed propose/check/commit vs the
    hand-rolled keyed Vec walk over 64 LCG-seeded deltas (seed 7),
    the flatland 5% band. -/
def commitPath : Kit.Duel.BenchSpec :=
  { name := "commit-path"
    candidate := "witnessed-commit"
    baseline := "hand-keyed-vec"
    seed := 7
    rows := 64
    threshold := .fivePct
    note := "the data plane's commit path vs the unwitnessed equivalent" }

/-- The bench manifests' generator provenance (the ONE writer's
    module — the manifests' `generator` row names THIS). -/
def generatorModule : String := "SchemaCore.Emit.Bench"

/-! ## The validator's pinned expected values -/

/- The run-then-pin loop's committed face: the validator's seeds make
   every chain deterministic, so these are known answers — a drift is
   a determinism break, never a re-measured baseline. Baked by
   running the validator and committing the values it prints; NEVER
   `--write`-style laundered. -/

/-- The codec-face twin world's hash-chain tail (seed 300, 96 ops). -/
def pinCodecTail : UInt64 := 4693743145306144929

/-- The journal-face twin world's hash-chain tail (seed 301, 96 ops). -/
def pinJournalTail : UInt64 := 5841812612511657845

/-- The per-rule table's insert-new hash (the seeded rule row). -/
def pinRuleInsertNew : UInt64 := 10933067564000509762

/-- The per-rule table's update-existing hash (the seeded rule row). -/
def pinRuleUpdateExisting : UInt64 := 1245298943954259335

/-- The per-rule table's remove-existing hash — a priori: the empty
    state hashes to the bare seed (no bytes consumed). -/
def pinRuleRemoveExisting : UInt64 := 1442695040888963407

/-! ## The shared Rust faces (the ONE copy, rendered per bench) -/

/-- TestingKit's ONE recurrence (Knuth 64) in Rust — the pair's rows,
    the bench input, and the validator's hash chain draw through THIS
    walk, never a second generator. -/
def rustLcg : String :=
"struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    /// The tape's byte face (the top 8 bits — TestingKit.Tape.byte).
    fn byte(&mut self) -> u8 {
        (self.next() >> 56) as u8
    }
    /// The tape's below face (the high bits mod bound —
    /// TestingKit.Tape.below; modulo bias accepted for test data).
    fn below(&mut self, bound: u64) -> u64 {
        (self.next() >> 16) % bound
    }
}
"

/-- The THRESHOLD verdict's Rust face — Kit.Duel.benchVerdict's tier
    ladder, u64 rendering (the ONE vocabulary, two renderings). -/
def rustVerdict : String :=
"/// The THRESHOLD verdict (Kit.Duel's tier ladder, u64 face): the
/// floored per-mille ratio — at-or-under 1000 parity, at-or-under
/// 1020 within-noise, the fivePct band at-or-under 1050 within-5%,
/// beyond = the ratio names the factor. A lone number is telemetry;
/// the printed line names the PAIR.
fn verdict(cand: u64, base: u64, threshold: &str) -> String {
    let r = if base == 0 { 0 } else { cand * 1000 / base };
    let tier = if r <= 1000 {
        \"parity\".to_string()
    } else if r <= 1020 {
        \"within-noise\".to_string()
    } else if threshold == \"within-5%\" && r <= 1050 {
        \"within-5%\".to_string()
    } else {
        format!(\"beyond ({} permille)\", r)
    };
    format!(
        \"candidate {}ns/op vs baseline {}ns/op — verdict: {}\",
        cand, base, tier
    )
}
"

/-- The bench-row parse (Kit.Duel's consumer walk): the manifest is
    READ, never re-encoded — a one-sided pair (a missing baseline)
    REFUSES at the column count. -/
def rustBenchRow : String :=
"/// The parsed bench row (the manifest's `bench\\t` row): the pair's
/// identity + the seeded-input parameters + the threshold. The
/// candidate/baseline names are the PAIR's provenance (the verdict
/// line's context; this file's fn names mirror them) — read here,
/// never dereferenced.
#[allow(dead_code)]
struct BenchRow {
    name: String,
    candidate: String,
    baseline: String,
    seed: u64,
    rows: usize,
    threshold: String,
}

/// Kit.Duel's consumer walk: skip the 2-line GENERATED header and the
/// `generator` provenance row, split the `bench\\t` row on the tab —
/// 7 columns; a one-sided pair REFUSES here (the pair discipline is
/// enforced at the manifest's reader, not hoped for).
fn bench_row() -> BenchRow {
    let line = MANIFEST
        .lines()
        .skip(2)
        .find(|l| l.starts_with(\"bench\\t\"))
        .expect(\"manifest: no bench row\");
    let cols: Vec<&str> = line.split('\\t').collect();
    assert!(
        cols.len() == 7,
        \"manifest bench row: expected 7 columns, got {}\",
        cols.len()
    );
    BenchRow {
        name: cols[1].to_string(),
        candidate: cols[2].to_string(),
        baseline: cols[3].to_string(),
        seed: cols[4].parse().expect(\"manifest: seed\"),
        rows: cols[5].parse().expect(\"manifest: rows\"),
        threshold: cols[6].to_string(),
    }
}
"

/-- Per-op nanoseconds, MIN of the batches (the min is the standard
    noise-reduced statistic — the machine's quiet state). -/
def rustNsPerOp : String :=
"/// Per-op nanoseconds, MIN of the batches (the noise-reduced
/// statistic — the machine's quiet state; the warm-up batch is never
/// counted).
fn ns_per_op(f: impl Fn() -> usize, iterations: usize) -> u64 {
    f(); // warm-up
    let mut best = u64::MAX;
    for _ in 0..5 {
        let t = std::time::Instant::now();
        for _ in 0..iterations {
            f();
        }
        let per = t.elapsed().as_nanos() as u64 / iterations as u64;
        if per < best {
            best = per;
        }
    }
    best
}
"

/-! ## The codec round-trip bench (crates/schema-generated/benches/) -/

/-- The codec round-trip bench's body: the PAIR (the generated codec
    vs the hand Vec walk, same seeded rows) + the divan benches + the
    profiled face riding the PRODUCTION scopes + the verdict. -/
def codecBenchRust : String :=
"//! GENERATED bench — the codec round-trip DUEL (Kit.Duel's bench
//! discipline, wave-30 C2): a bench is a PAIR — candidate vs
//! baseline, the SAME seeded inputs — with a THRESHOLD verdict
//! (parity / within-noise / within-5%). A lone number is telemetry.
//!
//! - candidate: the GENERATED codec (`Example::encode` /
//!   `decode_full` — the schema's wire; C1's production `scope!`
//!   spans open inside, so the observability face is IN the
//!   measurement)
//! - baseline: the hand-rolled `Vec<u8>` walk below — the shape a
//!   no-codegen consumer writes
//! - input: LCG-seeded rows (ONE tape, both sides — the pair
//!   discipline)
//!
//! Run: `just bench` (on-demand, never CI — CI runs the e2e
//! validator, the determinism face; the benches are the perf face,
//! run deliberately).

// The flatland invariants: no harness (main drives), mimalloc (the
// pair shares ONE allocator), black_box on every observed output,
// the sample count scaled to the op's cost.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use fast_observe::bench::{BenchExt, divan};
use schema_generated::Example;

/// The bench manifest, compile-time pinned (Kit.Duel's consumer
/// contract: the manifest is READ, never re-encoded — the pair, the
/// seed, the threshold live in ONE place, the Lean emitter's row).
const MANIFEST: &str = include_str!(\"manifest.txt\");

" ++ rustLcg ++ rustVerdict ++ rustBenchRow ++ "
/// The seeded input: `n` Example values off ONE tape (both pair
/// sides consume THE SAME rows — the pair discipline).
fn seeded_rows(n: usize, seed: u64) -> Vec<Example> {
    let mut t = Lcg(seed);
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let ready = t.byte() & 1 == 1;
        let count = t.next();
        let delta = (t.next() >> 1) as i64;
        let label = format!(\"k{}\", t.below(16));
        let note = if t.byte() & 1 == 1 {
            Some(format!(\"n{}\", t.below(1024)))
        } else {
            None
        };
        let ntags = t.below(4);
        let mut tags = Vec::new();
        for _ in 0..ntags {
            tags.push(format!(\"t{}\", t.below(32)));
        }
        out.push(Example { ready, count, delta, label, note, tags });
    }
    out
}

/// The shared rows (built once; the divan benches and the verdict
/// driver consume the SAME Vec, seeded from the manifest's row).
fn input() -> &'static Vec<Example> {
    static INPUT: std::sync::OnceLock<Vec<Example>> = std::sync::OnceLock::new();
    INPUT.get_or_init(|| {
        let row = bench_row();
        seeded_rows(row.rows, row.seed)
    })
}

/// The BASELINE's hand wire walk (the no-codegen shape): the same
/// SchemaCore.Codec atom conventions, written out — bool byte, LEB128
/// varint, zigzag i64, varint-len char-varint string, option tag,
/// list count. The atom IMPLEMENTATIONS stay the generated crate's
/// concern; the baseline is the hand shape they replace.
fn hand_varint(mut n: u64, out: &mut Vec<u8>) {
    loop {
        if n < 128 {
            out.push(n as u8);
            return;
        }
        out.push((128 + n % 128) as u8);
        n /= 128;
    }
}

fn hand_str(s: &str, out: &mut Vec<u8>) {
    hand_varint(s.chars().count() as u64, out);
    for c in s.chars() {
        hand_varint(c as u64, out);
    }
}

fn hand_encode(r: &Example, out: &mut Vec<u8>) {
    out.push(if r.ready { 1 } else { 0 });
    hand_varint(r.count, out);
    hand_varint(((r.delta << 1) ^ (r.delta >> 63)) as u64, out);
    hand_str(&r.label, out);
    match &r.note {
        None => out.push(0),
        Some(s) => {
            out.push(1);
            hand_str(s, out);
        }
    }
    hand_varint(r.tags.len() as u64, out);
    for t in &r.tags {
        hand_str(t, out);
    }
}

fn hand_decode(bs: &[u8]) -> Option<Example> {
    fn varint(bs: &[u8], i: &mut usize) -> Option<u64> {
        let mut result = 0u64;
        let mut groups = 0u32;
        loop {
            let b = *bs.get(*i)?;
            *i += 1;
            result |= ((b & 0x7f) as u64) << (7 * groups);
            if b < 128 {
                return Some(result);
            }
            groups += 1;
        }
    }
    fn string(bs: &[u8], i: &mut usize) -> Option<String> {
        let n = varint(bs, i)?;
        let mut s = String::new();
        for _ in 0..n {
            s.push(char::from_u32(varint(bs, i)? as u32)?);
        }
        Some(s)
    }
    let mut i = 0usize;
    let ready = *bs.get(i)? == 1;
    i += 1;
    let count = varint(bs, &mut i)?;
    let zz = varint(bs, &mut i)? as i64;
    let delta = (zz >> 1) ^ -(zz & 1);
    let label = string(bs, &mut i)?;
    let note = match bs.get(i)? {
        0 => {
            i += 1;
            None
        }
        1 => {
            i += 1;
            Some(string(bs, &mut i)?)
        }
        _ => return None,
    };
    let ntags = varint(bs, &mut i)?;
    let mut tags = Vec::new();
    for _ in 0..ntags {
        tags.push(string(bs, &mut i)?);
    }
    Some(Example { ready, count, delta, label, note, tags })
}

/// The CANDIDATE: the generated codec's round trip.
fn candidate(rows: &[Example]) -> usize {
    let mut acc = 0usize;
    for r in rows {
        let mut wire = Vec::with_capacity(64);
        r.encode(&mut wire);
        let back = Example::decode_full(&wire)
            .expect(\"the codec round-trips its own wire\");
        acc += back.count as usize;
    }
    acc
}

/// The BASELINE: the hand walk over the same rows.
fn baseline(rows: &[Example]) -> usize {
    let mut acc = 0usize;
    for r in rows {
        let mut wire = Vec::with_capacity(64);
        hand_encode(r, &mut wire);
        let back = hand_decode(&wire)
            .expect(\"the hand walk round-trips the same bytes\");
        acc += back.count as usize;
    }
    acc
}

#[divan::bench(crate = fast_observe::bench::divan, sample_count = 200)]
fn candidate_generated_codec() -> usize {
    divan::black_box(candidate(divan::black_box(input())))
}

#[divan::bench(crate = fast_observe::bench::divan, sample_count = 200)]
fn baseline_hand_vec() -> usize {
    divan::black_box(baseline(divan::black_box(input())))
}

/// `bench_profiled` rides the PRODUCTION scopes (wave-30 C2's hook):
/// the generated codec's C1 spans (`schema.example.encode` /
/// `schema.example.decode`) ARE the production instrumentation — the
/// profiled run attributes phase time through the SAME `scope!` calls
/// production opens, never a bench-only span. The breakdown table
/// prints after the sample loop.
#[divan::bench(crate = fast_observe::bench::divan, sample_count = 32)]
fn candidate_profiled(bencher: divan::Bencher) {
    let rows = input();
    let run = bencher.bench_profiled(|| {
        for r in rows.iter() {
            let mut wire = Vec::with_capacity(64);
            r.encode(&mut wire);
            divan::black_box(
                Example::decode_full(&wire).expect(\"round trip\"),
            );
        }
    });
    run.print();
}

" ++ rustNsPerOp ++ "
fn main() {
    let row = bench_row();
    // the pair's SEMANTIC control: both sides decode the same rows
    assert_eq!(
        candidate(input()),
        baseline(input()),
        \"the bench pair must agree on the values\"
    );
    let iterations = 100;
    let c = ns_per_op(|| candidate(input()), iterations);
    let b = ns_per_op(|| baseline(input()), iterations);
    println!(\"bench duel {}: {}\", row.name, verdict(c, b, &row.threshold));
    divan::main();
}
"

/-! ## The commit-path bench (crates/mandate-delta/benches/) -/

/-- The commit-path bench's body: the witnessed propose/check/commit
    vs the hand-rolled keyed Vec walk, same seeded deltas + the
    verdict; the profiled seam NAMED (the delta crate has no
    fast-observe dep yet). -/
def commitBenchRust : String :=
"//! GENERATED bench — the commit-path DUEL (Kit.Duel's bench
//! discipline, wave-30 C2): propose/check/commit (the witnessed path
//! — `witness_of` PROPOSES, `patch_w_checked` CHECKS, the patched
//! state COMMITS) at N rows vs the hand-rolled keyed Vec walk. The
//! SAME seeded deltas feed both sides; the THRESHOLD verdict
//! (parity / within-noise / within-5%) prints from main() — a lone
//! number is telemetry.
//!
//! THE SEAM (named, the honest integration): the delta crate has NO
//! fast-observe dependency yet — C1's scopes landed on the generated
//! codec only. When the commit path grows its production `scope!`
//! (a `schema.commit.append` span), THIS bench rides it: add the
//! `bench_profiled` bencher exactly as codec_round_trip.rs's
//! `candidate_profiled` does. Named, not faked.
//!
//! Run: `just bench` (on-demand, never CI — CI runs the e2e
//! validator, the determinism face).

// The flatland invariants: no harness, mimalloc (the pair shares ONE
// allocator), black_box on every observed output, the sample count
// scaled to the op's cost.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use mandate_delta::delta::{Table, patch_w_checked, witness_of};
use mandate_delta::schema::fixtures;
use mandate_delta::{Delta, Row, Schema, Value};

/// The bench manifest, compile-time pinned (Kit.Duel's consumer
/// contract: the manifest is READ, never re-encoded).
const MANIFEST: &str = include_str!(\"manifest.txt\");

" ++ rustLcg ++ rustVerdict ++ rustBenchRow ++ "
/// The seeded commit path: `n` deltas off ONE tape over the fixture
/// schema (id:u64 keyed, name:string) — ONE tape, both sides.
fn seeded_deltas(n: usize, seed: u64) -> Vec<Delta> {
    let mut t = Lcg(seed);
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let id = t.below(64);
        let name = format!(\"n{}\", t.below(1024));
        out.push(match t.byte() % 3 {
            0 => Delta::Insert(fixtures::fixture_row(id, &name)),
            1 => Delta::Update(fixtures::fixture_row(id, &name)),
            _ => Delta::Remove(Value::U64(id)),
        });
    }
    out
}

/// The shared input (built once; schema + deltas, seeded from the
/// manifest's row).
fn input() -> &'static (Schema, Vec<Delta>) {
    static INPUT: std::sync::OnceLock<(Schema, Vec<Delta>)> = std::sync::OnceLock::new();
    INPUT.get_or_init(|| {
        let row = bench_row();
        (fixtures::fixture(), seeded_deltas(row.rows, row.seed))
    })
}

/// The CANDIDATE: the commit path's three phases at N rows.
fn commit_path(schema: &Schema, deltas: &[Delta]) -> usize {
    let mut table = Table::new();
    for d in deltas {
        let w = witness_of(schema, d, &table); // PROPOSE
        let patched = patch_w_checked(&table, &w) // CHECK: a lying
            // witness REFUSES, it never silently mispatches
            .expect(\"the witness is by-construction valid (witnessOf_valid)\");
        table = patched; // COMMIT
    }
    table.rows().len()
}

/// The BASELINE: the hand-rolled equivalent — the raw keyed Vec walk
/// the witnessed path replaces (scan by key, replace/append/erase),
/// over the same seeded deltas.
fn hand_commit(schema: &Schema, deltas: &[Delta]) -> usize {
    let mut rows: Vec<Row> = Vec::new();
    for d in deltas {
        match d {
            Delta::Insert(r) | Delta::Update(r) => {
                match rows.iter().position(|row| schema.same_key(row, r)) {
                    Some(i) => rows[i] = r.clone(),
                    None => rows.push(r.clone()),
                }
            }
            Delta::Remove(k) => {
                if let Some(i) =
                    rows.iter().position(|row| schema.same_key_img(row, k))
                {
                    rows.remove(i);
                }
            }
        }
    }
    rows.len()
}

#[divan::bench(sample_count = 100)]
fn candidate_witnessed_commit() -> usize {
    let (schema, deltas) = input();
    divan::black_box(commit_path(schema, divan::black_box(deltas)))
}

#[divan::bench(sample_count = 100)]
fn baseline_hand_keyed_vec() -> usize {
    let (schema, deltas) = input();
    divan::black_box(hand_commit(schema, divan::black_box(deltas)))
}

" ++ rustNsPerOp ++ "
fn main() {
    let row = bench_row();
    let (schema, deltas) = input();
    // the pair's SEMANTIC control: both walks end at the same state
    assert_eq!(
        commit_path(schema, deltas),
        hand_commit(schema, deltas),
        \"the bench pair must agree on the final row count\"
    );
    let iterations = 50;
    let c = ns_per_op(|| commit_path(schema, deltas), iterations);
    let b = ns_per_op(|| hand_commit(schema, deltas), iterations);
    println!(\"bench duel {}: {}\", row.name, verdict(c, b, &row.threshold));
    divan::main();
}
"

/-! ## The e2e validator (crates/schema-generated/tests/) -/

/-- The registry's item-name manifest (the validator's provenance
    face — generated PER SCHEMA: a registry drift regenerates the
    file and the pins move with it). -/
def itemsLine (reg : DataRegistry Item) : String :=
  String.intercalate ", " (reg.items.map (·.name))

/-- The item-name const's Rust literal list. -/
def itemsRustList (reg : DataRegistry Item) : String :=
  "[" ++ String.intercalate ", " (reg.items.map fun i => "\"" ++ i.name ++ "\"") ++ "]"

/-- The e2e validator's body: the twin-world discipline (two loads of
    the same seeded log — direct vs wire-mediated — identical state
    hashes at EVERY step) + the per-rule expected values with notes. -/
def e2eValidatorRust (reg : DataRegistry Item) : String :=
"//! GENERATED e2e validator — the twin-world discipline (wave-30 C2):
//! two loads of the same seeded log produce IDENTICAL state hashes at
//! EVERY step (the machines' determinism discipline, cited); the
//! per-rule expected values are pinned with notes.
//!
//! CI runs THIS (`just rust` — cargo test); the benches are the perf
//! face, run on demand (`just bench`).
//!
//! THE HASH: Kit.Emit.bytesHash's fold — TestingKit's Knuth-64 LCG
//! (h = (h + b) * 6364136223846793005 + 1442695040888963407,
//! wrapping, seeded 1442695040888963407) over the state's wire bytes.
//! ONE hash, both worlds compute it identically; a divergent step is
//! a loud per-step refusal, never a silent skew.

use mandate_delta::delta::{Table, dec_journal, enc_journal};
use mandate_delta::schema::{enc_row, fixtures};
use mandate_delta::{Delta, Row, Schema, Value};
use schema_generated::Example;

/// The registered schema items (the emitter's provenance face — the
/// validator is generated PER SCHEMA; a registry drift regenerates
/// THIS file and the pins move with it). " ++ toString reg.items.length ++ " item(s): " ++ itemsLine reg ++ ".
const SCHEMA_ITEMS: [&str; " ++ toString reg.items.length ++ "] = " ++ itemsRustList reg ++ ";

/// Kit.Emit.bytesHash's fold (the ONE hash — see the module header).
fn bytes_hash(bs: &[u8]) -> u64 {
    bs.iter().fold(1442695040888963407u64, |h, b| {
        (h + *b as u64)
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407)
    })
}

" ++ rustLcg ++ "
/// The seeded op log over the generated codec face (`Example`, the
/// declared key `label`): tag 0/1 = insert/update (keyed upsert),
/// 2 = remove. ONE tape — same seed, same log, both worlds.
fn seeded_ops(n: usize, seed: u64) -> Vec<(u8, Example)> {
    let mut t = Lcg(seed);
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let tag = t.byte() % 3;
        let ready = t.byte() & 1 == 1;
        let count = t.next();
        let delta = (t.next() >> 1) as i64;
        let label = format!(\"k{}\", t.below(16));
        let note = if t.byte() & 1 == 1 {
            Some(format!(\"n{}\", t.below(1024)))
        } else {
            None
        };
        let ntags = t.below(4);
        let mut tags = Vec::new();
        for _ in 0..ntags {
            tags.push(format!(\"t{}\", t.below(32)));
        }
        out.push((tag, Example { ready, count, delta, label, note, tags }));
    }
    out
}

/// The keyed application (the delta semantics over the codec face —
/// `SchemaCore.deltaApply`'s keyed upsert/erase).
fn apply(rows: &mut Vec<Example>, tag: u8, row: Example) {
    match tag {
        0 | 1 => match rows.iter().position(|r| r.label == row.label) {
            Some(i) => rows[i] = row,
            None => rows.push(row),
        },
        _ => {
            if let Some(i) = rows.iter().position(|r| r.label == row.label) {
                rows.remove(i);
            }
        }
    }
}

/// The codec-face state hash: the state's wire bytes (each row's
/// `encode` in table order) through the ONE hash.
fn state_hash(rows: &[Example]) -> u64 {
    let mut wire = Vec::new();
    for r in rows {
        r.encode(&mut wire);
    }
    bytes_hash(&wire)
}

/// The journal-face state hash: each row's `enc_row` bytes through
/// the ONE hash.
fn journal_state_hash(schema: &Schema, rows: &[Row]) -> u64 {
    let mut wire = Vec::new();
    for r in rows {
        enc_row(r, &mut wire);
    }
    bytes_hash(&wire)
}

/// The seeded delta log over the fixture schema (the journal face's
/// twin world — ONE tape, both loads).
fn seeded_deltas(n: usize, seed: u64) -> Vec<Delta> {
    let mut t = Lcg(seed);
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let id = t.below(64);
        let name = format!(\"n{}\", t.below(1024));
        out.push(match t.byte() % 3 {
            0 => Delta::Insert(fixtures::fixture_row(id, &name)),
            1 => Delta::Update(fixtures::fixture_row(id, &name)),
            _ => Delta::Remove(Value::U64(id)),
        });
    }
    out
}

/// TWIN WORLD, codec face: world A applies the log directly; world B
/// loads each op through the GENERATED wire (encode → decode_full)
/// before applying. Identical state hashes at EVERY step — the seed's
/// chain tail is the PINNED known answer (" ++ toString pinCodecTail ++ ").
#[test]
fn twin_world_codec() {
    let ops = seeded_ops(96, 300);
    let mut world_a: Vec<Example> = Vec::new();
    let mut world_b: Vec<Example> = Vec::new();
    for (step, (tag, row)) in ops.iter().enumerate() {
        apply(&mut world_a, *tag, row.clone());
        let mut wire = Vec::new();
        row.encode(&mut wire);
        let back = Example::decode_full(&wire).expect(\"the log decodes\");
        apply(&mut world_b, *tag, back);
        assert_eq!(
            state_hash(&world_a),
            state_hash(&world_b),
            \"twin worlds diverged at step {} (same seed, two loads)\",
            step
        );
    }
    assert_eq!(
        state_hash(&world_a),
        " ++ toString pinCodecTail ++ ",
        \"the codec-face chain tail left its pinned known answer\"
    );
}

/// TWIN WORLD, journal face: the whole log through the Lean journal
/// codec's wire, then two independent loads (the original deltas vs
/// the WIRE-LOADED deltas). Identical state hashes at EVERY step; the
/// chain tail is the PINNED known answer (" ++ toString pinJournalTail ++ ").
#[test]
fn twin_world_journal() {
    let schema = fixtures::fixture();
    let log = seeded_deltas(96, 301);
    let mut journal = Vec::new();
    enc_journal(&schema, &log, &mut journal);
    let decoded =
        dec_journal(&schema, &mut journal.as_slice()).expect(\"the journal decodes\");
    assert_eq!(decoded, log, \"the journal round-trips its own wire\");
    let mut world_a = Table::new();
    let mut world_b = Table::new();
    for (step, (d_a, d_b)) in log.iter().zip(decoded.iter()).enumerate() {
        world_a.apply(&schema, d_a);
        world_b.apply(&schema, d_b);
        assert_eq!(
            journal_state_hash(&schema, world_a.rows()),
            journal_state_hash(&schema, world_b.rows()),
            \"twin journal loads diverged at step {}\",
            step
        );
    }
    assert_eq!(
        journal_state_hash(&schema, world_a.rows()),
        " ++ toString pinJournalTail ++ ",
        \"the journal-face chain tail left its pinned known answer\"
    );
}

/// The per-rule expected values (each names its note — the honest
/// known-answer table over the codec face's keyed semantics).
#[test]
fn per_rule_known_answers() {
    let mk = |label: &str, n: u64| Example {
        ready: true,
        count: n,
        delta: 0,
        label: label.to_string(),
        note: None,
        tags: Vec::new(),
    };
    // rule insert-new — note: keyed upsert APPENDS on an absent key.
    let mut rows = vec![mk(\"k0\", 1)];
    assert_eq!(rows.len(), 1);
    assert_eq!(
        state_hash(&rows),
        " ++ toString pinRuleInsertNew ++ ",
        \"insert-new left its pinned hash\"
    );
    // rule update-existing — note: FULL replacement at the first key
    // match; the count never grows.
    apply(&mut rows, 1, mk(\"k0\", 2));
    assert_eq!(rows.len(), 1);
    assert_eq!(
        state_hash(&rows),
        " ++ toString pinRuleUpdateExisting ++ ",
        \"update-existing left its pinned hash\"
    );
    // rule remove-existing — note: the FIRST key match is erased.
    apply(&mut rows, 2, mk(\"k0\", 0));
    assert_eq!(rows.len(), 0);
    assert_eq!(
        state_hash(&rows),
        " ++ toString pinRuleRemoveExisting ++ ",
        \"remove-existing left its pinned hash (a priori: the bare seed)\"
    );
    // rule remove-absent — note: the erase of an absent key is a
    // no-op (the total semantics); the state is unchanged.
    apply(&mut rows, 2, mk(\"k7\", 0));
    assert_eq!(rows.len(), 0);
    assert_eq!(
        state_hash(&rows),
        " ++ toString pinRuleRemoveExisting ++ ",
        \"remove-absent left its pinned hash (a priori: the bare seed)\"
    );
}

/// The schema manifest's provenance check (the per-schema face).
#[test]
fn schema_manifest_names_the_registered_items() {
    assert!(!SCHEMA_ITEMS.is_empty(), \"the registry replay named no items\");
    assert!(
        SCHEMA_ITEMS.contains(&\"Example\"),
        \"the keyed fixture item must be registered\"
    );
}
"

/-! ## The emitter -/

/-- THE BENCH EMITTER (the spine's bench row): the two benches' +
    validator's artifacts, the manifests the consumer contract's one
    copy. `outputs_nodup` is in the type; the registry's items are
    the validator's provenance face. -/
def benchEmitter : Emitter (DataRegistry Item) where
  name := "schema-bench"
  style := .doubleSlash
  specSource := "SchemaCore.Slice"
  outputs :=
    [ "crates/schema-generated/benches/manifest.txt"
    , "crates/schema-generated/benches/codec_round_trip.rs"
    , "crates/mandate-delta/benches/manifest.txt"
    , "crates/mandate-delta/benches/commit_path.rs"
    , "crates/schema-generated/tests/e2e_validator.rs" ]
  run := fun reg =>
    [ { path := "crates/schema-generated/benches/manifest.txt"
        contents := Kit.Duel.benchManifestRows generatorModule [codecRoundTrip] }
    , { path := "crates/schema-generated/benches/codec_round_trip.rs"
        contents := codecBenchRust }
    , { path := "crates/mandate-delta/benches/manifest.txt"
        contents := Kit.Duel.benchManifestRows generatorModule [commitPath] }
    , { path := "crates/mandate-delta/benches/commit_path.rs"
        contents := commitBenchRust }
    , { path := "crates/schema-generated/tests/e2e_validator.rs"
        contents := e2eValidatorRust reg } ]
  law := none

end SchemaCore.Emit.Bench
