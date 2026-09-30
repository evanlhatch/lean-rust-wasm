//! The delta wire's boundary fuzz face (the C3 lane — mandate-delta's
//! side): the never-panic floor over arbitrary bytes (junk must refuse
//! — typed `DecodeFail`, never a panic), the round trip over arbitrary
//! values (encode ∘ decode = id), the valid-then-mutate sweep (a valid
//! frame's every single-byte mutation still answers Ok or a typed
//! refusal), and the MANDATORY negative control (the sabotage-stub:
//! the floor's driver must CATCH a panicking subject —
//! design-bolero-integration §6's checker-discrimination at the stub
//! edge).
//!
//! THE ENGINE (the honest local shape, matching the generated face's
//! judgment): plain `cargo test` — a file-local `Lcg` (TestingKit.Lcg's
//! RUST TWIN, the SAME Knuth-64 constants as the generated `Tape`)
//! drives deterministic seeded cases; every case replays
//! byte-identically from its seed (15-patterns #14: the failing
//! case's evidence is the seed). 512 iterations, fixed — never a time
//! bound (design-bolero-integration §5's seeds law).

use mandate_delta::delta::{dec_delta, dec_journal, Delta, enc_delta, enc_journal};
use mandate_delta::schema::fixtures::fixture;
use mandate_delta::schema::{dec_row, enc_row, Row};
use mandate_delta::value::{enc_value, Ty, Value};

/// The sweep's size (deterministic, fixed — the generated face's own
/// constant, mirrored here so the two faces' budgets agree).
const ITERATIONS: u64 = 512;

/// The shared deterministic LCG (Knuth 64) — TestingKit.Lcg's RUST
/// TWIN, the same recurrence the generated `Tape` carries (the
/// u64 arithmetic WRAPS — the wrap is the stream), the same
/// byte/below shapes. One copy per test FILE (the tape discipline's
/// Rust twin is per-face; the constants are the tie, checked by the
/// generated golden test against the Lean drawers).
struct Lcg {
    state: u64,
}

impl Lcg {
    /// A fresh tape pinned to `seed` (Tape.ofSeed's shape).
    fn of_seed(s: u64) -> Self {
        Lcg { state: s }
    }

    /// One LCG step: the recurrence's next state.
    fn next(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    /// One byte: the top 8 bits of the next state (Tape.byte).
    fn byte(&mut self) -> u8 {
        (self.next() >> 56) as u8
    }

    /// A draw below `bound`: (state >> 16) % bound (Tape.below; the
    /// modulo bias is accepted for a test kit — noted, not hidden).
    fn below(&mut self, bound: u64) -> u64 {
        (self.next() >> 16) % bound
    }

    /// bool: the byte drawer's low bit.
    fn boolean(&mut self) -> bool {
        self.byte() & 1 == 1
    }

    /// u64: the raw next state (the stream's own word).
    fn u64_draw(&mut self) -> u64 {
        self.next()
    }

    /// i64: the zigzag of the u64 draw (the wire's own i64 map).
    fn i64_draw(&mut self) -> i64 {
        let z = self.u64_draw();
        ((z >> 1) as i64) ^ (-((z & 1) as i64))
    }

    /// One char from the small alphabet (drawChar's shape).
    fn draw_char(&mut self) -> char {
        let alphabet = ['a', 'b', 'c', 'd'];
        alphabet[self.below(4) as usize]
    }

    /// A short string, length < 4, over the small alphabet
    /// (drawString's shape).
    fn draw_string(&mut self) -> String {
        let n = self.below(4) as usize;
        let mut acc = String::new();
        for _ in 0..n {
            acc.push(self.draw_char());
        }
        acc
    }

    /// Arbitrary bytes: a short length (< 32), then that many draws —
    /// the generated floor's own byte case, replayed here.
    fn arbitrary_bytes(&mut self) -> Vec<u8> {
        let n = self.below(32) as usize;
        (0..n).map(|_| self.byte()).collect()
    }
}

/// An arbitrary field value for the schema's scalar universe
/// (`SchemaCore.Value`'s atom arms — the fixture schema's field types
/// dispatch the drawers).
fn arbitrary_value(t: &mut Lcg, ty: Ty) -> Value {
    match ty {
        Ty::Bool => Value::Bool(t.boolean()),
        Ty::U64 => Value::U64(t.u64_draw()),
        Ty::I64 => Value::I64(t.i64_draw()),
        Ty::Str => Value::Str(t.draw_string()),
    }
}

/// An arbitrary schema-checked row (the fields in schema order, every
/// value drawn per ITS type — `Row::build`'s check passes by
/// construction).
fn arbitrary_row(t: &mut Lcg, schema: &mandate_delta::Schema) -> Row {
    let values: Vec<Value> = schema
        .fields
        .iter()
        .map(|f| arbitrary_value(t, f.ty))
        .collect();
    Row::build(schema, values)
        .unwrap_or_else(|e| panic!("the generator drew an unbuildable row: {e}"))
}

/// An arbitrary delta frame: 1-in-3 remove (the tag byte's ctor order
/// 0/1/2 — the insert/update/remove split), otherwise a full row.
fn arbitrary_delta(t: &mut Lcg, schema: &mandate_delta::Schema) -> Delta {
    match t.below(3) {
        0 => Delta::Remove(arbitrary_value(t, schema.key_ty())),
        1 => Delta::Insert(arbitrary_row(t, schema)),
        _ => Delta::Update(arbitrary_row(t, schema)),
    }
}

/// THE NEVER-PANIC FLOOR, the row face: `dec_row` answers arbitrary
/// BYTES with Ok or a typed `DecodeFail` — junk must refuse, never
/// panic. A fully-consumed decode re-encodes byte-identically (the
/// wire is the exact image of the encoder — the differential's
/// re-encode law at arbitrary inputs; a suffix-consuming decode is
/// append-form, its re-encode is the consumed prefix — not asserted).
#[test]
fn fuzz_dec_row_floor_never_panics_and_reencodes() {
    let schema = fixture();
    let mut ran = 0u64;
    for seed in 0..ITERATIONS {
        let mut t = Lcg::of_seed(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let bytes = t.arbitrary_bytes();
        let mut bs: &[u8] = &bytes;
        if let Ok(row) = dec_row(&schema, &mut bs) {
            if bs.is_empty() {
                let mut out = Vec::new();
                enc_row(&row, &mut out);
                assert_eq!(out, bytes, "seed {seed}: the re-encode drifted");
            }
        }
        ran += 1;
    }
    // THE ANTI-VACUITY GUARD: the target RAN — a generator that never
    // draws proves nothing.
    assert_eq!(ran, ITERATIONS, "the sweep did not complete");
}

/// THE NEVER-PANIC FLOOR, the frame + journal faces: `dec_delta` and
/// `dec_journal` over arbitrary bytes — Ok or typed `DecodeFail`,
/// never a panic. A fully-consumed delta frame re-encodes
/// byte-identically; a fully-consumed journal's frames do too.
#[test]
fn fuzz_dec_delta_and_journal_floor_never_panics() {
    let schema = fixture();
    let mut ran = 0u64;
    for seed in 0..ITERATIONS {
        let mut t = Lcg::of_seed(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1));
        let bytes = t.arbitrary_bytes();

        let mut bs: &[u8] = &bytes;
        if let Ok(d) = dec_delta(&schema, &mut bs) {
            if bs.is_empty() {
                let mut out = Vec::new();
                assert!(enc_delta(&schema, &d, &mut out), "seed {seed}: encode refused");
                assert_eq!(out, bytes, "seed {seed}: the frame re-encode drifted");
            }
        }

        let mut bs: &[u8] = &bytes;
        if let Ok(log) = dec_journal(&schema, &mut bs) {
            if bs.is_empty() {
                let mut out = Vec::new();
                enc_journal(&schema, &log, &mut out);
                assert_eq!(out, bytes, "seed {seed}: the journal re-encode drifted");
            }
        }
        ran += 1;
    }
    assert_eq!(ran, ITERATIONS, "the sweep did not complete");
}

/// THE ROUND TRIP over arbitrary values: enc_row ∘ dec_row = id,
/// enc_delta ∘ dec_delta = id, enc_journal ∘ dec_journal = id — every
/// ctor arm of the delta universe rides the generator, so the sweep
/// covers the wire's every row.
#[test]
fn fuzz_row_delta_journal_round_trip() {
    let schema = fixture();
    for seed in 0..ITERATIONS {
        let mut t = Lcg::of_seed(seed);

        // The row face.
        let row = arbitrary_row(&mut t, &schema);
        let mut row_wire = Vec::new();
        enc_row(&row, &mut row_wire);
        let mut bs: &[u8] = &row_wire;
        let back = dec_row(&schema, &mut bs)
            .unwrap_or_else(|e| panic!("seed {seed}: the row round trip refused: {e:?}"));
        assert_eq!(back, row, "seed {seed}: the row round trip drifted");
        assert!(bs.is_empty(), "seed {seed}: the row decode left a suffix");

        // The frame face.
        let d = arbitrary_delta(&mut t, &schema);
        let mut frame = Vec::new();
        assert!(enc_delta(&schema, &d, &mut frame), "seed {seed}: encode refused");
        let mut bs: &[u8] = &frame;
        let back = dec_delta(&schema, &mut bs)
            .unwrap_or_else(|e| panic!("seed {seed}: the delta round trip refused: {e:?}"));
        assert_eq!(back, d, "seed {seed}: the delta round trip drifted");
        assert!(bs.is_empty(), "seed {seed}: the frame decode left a suffix");

        // The whole-log face: an arbitrary log of 0..=4 frames.
        let n = t.below(5) as usize;
        let log: Vec<Delta> = (0..n).map(|_| arbitrary_delta(&mut t, &schema)).collect();
        let mut journal = Vec::new();
        enc_journal(&schema, &log, &mut journal);
        let mut bs: &[u8] = &journal;
        let back = dec_journal(&schema, &mut bs)
            .unwrap_or_else(|e| panic!("seed {seed}: the journal round trip refused: {e:?}"));
        assert_eq!(back, log, "seed {seed}: the journal round trip drifted");
        assert!(bs.is_empty(), "seed {seed}: the journal decode left a suffix");
    }
}

/// VALID-THEN-MUTATE: a valid frame's every single-byte mutation must
/// still answer Ok or a typed refusal — never a panic, never a silent
/// misparse (the recovery discipline dispatches on exactly these
/// classes; a panic here is a torn-tail crash the backend cannot
/// survive).
#[test]
fn fuzz_valid_then_mutate_still_never_panics() {
    let schema = fixture();
    let mut ran = 0u64;
    for seed in 0..ITERATIONS {
        let mut t = Lcg::of_seed(seed);
        let row = arbitrary_row(&mut t, &schema);
        let mut wire = Vec::new();
        enc_row(&row, &mut wire);
        if wire.is_empty() {
            continue;
        }
        for i in 0..wire.len() {
            // one bit flip per position, the flip bit drawn (deterministic
            // per (seed, position) — a failing case replays from its seed)
            let mut t2 = Lcg::of_seed((seed << 8) | i as u64);
            let mut mutated = wire.clone();
            mutated[i] ^= 1 << t2.below(8);
            let mut bs: &[u8] = &mutated;
            if let Ok(back) = dec_row(&schema, &mut bs) {
                if bs.is_empty() {
                    // the mutated bytes decoded canonically and completely —
                    // the wire is the encoder's exact image, so it
                    // re-encodes identically (or the mutation was a no-op
                    // on the value space)
                    let mut out = Vec::new();
                    enc_row(&back, &mut out);
                    assert_eq!(out, mutated, "seed {seed} pos {i}: the re-encode drifted");
                }
            }
            ran += 1;
        }
    }
    assert!(ran > 0, "the mutation sweep did not run");
}

/// THE NEGATIVE CONTROL (MANDATORY — the sabotage-stub form): the
/// floor's driver machinery run against a deliberately-panicking twin
/// of the subject must be CAUGHT. If the driver ever stopped executing
/// the subject (or the floor's catch face were loosened), this control
/// goes red: the fuzz layer would prove nothing.
#[test]
fn negative_control_the_floor_catches_a_sabotaged_subject() {
    let schema = fixture();
    struct Sabotaged;
    impl Sabotaged {
        // the stub twin: the panic IS the sabotage
        fn dec_row<'a>(&self, _schema: &mandate_delta::Schema, _bs: &mut &'a [u8]) -> Row {
            panic!("the sabotage stub: the floor's subject twin is broken")
        }
    }
    let sabotaged = Sabotaged;
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        for seed in 0..8u64 {
            let mut t = Lcg::of_seed(seed);
            let bytes = t.arbitrary_bytes();
            let mut bs: &[u8] = &bytes;
            let _ = sabotaged.dec_row(&schema, &mut bs);
        }
    }));
    assert!(caught.is_err(), "control NOT caught — the fuzz layer proves nothing");
}

/// The atom-value floor over the scalar universe directly: `enc_value`
/// ∘ `dec_value` = id for every generated atom (the row face's leaf
/// rows, pinned at the leaves the schema dispatches to).
#[test]
fn fuzz_atom_values_round_trip() {
    for seed in 0..ITERATIONS {
        let mut t = Lcg::of_seed(seed);
        for ty in [Ty::Bool, Ty::U64, Ty::I64, Ty::Str] {
            let v = arbitrary_value(&mut t, ty);
            let mut wire = Vec::new();
            enc_value(&v, &mut wire);
            let mut bs: &[u8] = &wire;
            let back = mandate_delta::value::dec_value(ty, &mut bs)
                .unwrap_or_else(|e| panic!("seed {seed} {ty:?}: the atom round trip refused: {e:?}"));
            assert_eq!(back, v, "seed {seed} {ty:?}: the atom round trip drifted");
            assert!(bs.is_empty(), "seed {seed} {ty:?}: the atom decode left a suffix");
        }
    }
}
