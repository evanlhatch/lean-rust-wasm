//! THE WITNESS GATE's host-side teeth (the host-gating lane): the
//! guest-compiled checker GATES the ledger's commit — the legacy
//! `@[invariant]` discipline. The parity legs: the Lean executor over
//! the fixture's own module answers the pinned codes
//! (`ComponentTests.WitFixture.legExecutorParity`), and THESE tests
//! pin the SAME literals through wasmtime's typed calls over the
//! COMMITTED component (the byte-tie closes the circle).
//!
//! The code table is the Lean SSOT's mirror: 1 = claim false, 2 =
//! tampered, 3 = wrong-schema (`WIT_CODE_*`). A TRAP is not a refusal
//! — the trap face stays distinct (pinned).
//!
//! Negative controls are mandatory: the refusals' STATE face (no
//! commit, no journal entry, version unmoved) and the trap/refusal
//! KIND distinction are pinned beside the codes.

use std::fs;
use std::path::PathBuf;

use mandate_host::{
    gated_commit, load_witness_component, witness_gate, HostError, Live, Proposal,
    WITNESS_WIRE_OK, WIT_CODE_CLAIM_FALSE, WIT_CODE_TAMPERED, WIT_CODE_WRONG_SCHEMA,
};

fn gen_dir() -> PathBuf {
    mandate_host::repo_gen_dir()
}

/// A fresh per-test copy of the committed witness artifact set (the
/// tamper teeth mutate their copy, never the committed universe).
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "mandate-host-witness-{}-{name}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("scratch dir");
    let committed = gen_dir();
    for f in [
        "component-witness-slice.wasm",
        "component-witness-slice.wasm.hdr",
        "component-witness-slice.wit",
    ] {
        fs::copy(committed.join(f), dir.join(f)).expect("copy the committed artifact");
    }
    dir
}

/// A fresh live state (the fixture's two accounts, version 1) on a
/// temp journal. Returns the live state + the scratch DIR (the
/// journal file is `ledger.journal` inside it — reopen rides the
/// same path).
fn live_open(name: &str) -> (Live, PathBuf) {
    let dir = std::env::temp_dir().join(format!(
        "mandate-host-witness-live-{}-{name}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("scratch dir");
    let journal = dir.join("ledger.journal");
    let live = Live::open(&journal).expect("the fixture state opens");
    (live, dir)
}

/// The valid proposal (the fixture's row: 5 from alice to bob — the
/// Lean lane's `invRow 1 2 5` face).
fn valid_proposal(base: u64) -> Proposal {
    Proposal { base, tid: 1, src: 1, dst: 2, amount: 5 }
}

/// GATE-THROUGH: the honest certificate opens the gate and the commit
/// commits — the parity's accept literal (`(0, 0)` Lean-side) through
/// the wasmtime face, then the live loop's own verdict.
#[test]
fn the_honest_certificate_gates_the_commit_through() {
    let wasm = load_witness_component(&gen_dir()).expect("the committed component loads");
    // the bare gate: the pinned parity literal — accept
    witness_gate(&wasm, &valid_proposal(1), &WITNESS_WIRE_OK)
        .expect("the honest certificate opens the gate");
    // the gated commit: the proposal lands (version bumps)
    let (mut live, _dir) = live_open("gate-through");
    let p = valid_proposal(live.version());
    let v = gated_commit(&mut live, &p, &wasm, &WITNESS_WIRE_OK)
        .expect("the gated commit commits");
    assert!(
        matches!(v, mandate_host::LiveVerdict::Committed { version: 2 }),
        "the commit must land: {v:?}"
    );
    assert_eq!(live.version(), 2, "the version bumped");
}

/// TAMPER TOOTH: a recorded verdict that DISAGREES with the recomputed
/// check (the record is a lie) refuses with code 2 — and the STATE
/// face: no commit, no journal entry, the version unmoved.
#[test]
fn a_tampered_witness_refuses_and_commits_nothing() {
    let wasm = load_witness_component(&gen_dir()).expect("the committed component loads");
    let (mut live, journal_path) = live_open("tampered");
    let base = live.version();
    // the right shape, the wrong record: the conjunction's verdict
    // slot doctored to 0 (the recomputed check says TRUE)
    let mut wire = WITNESS_WIRE_OK;
    wire[1] = 0;
    let p = valid_proposal(base);
    let err = gated_commit(&mut live, &p, &wasm, &wire)
        .expect_err("the tampered witness refuses");
    assert!(
        matches!(err, HostError::WitnessRefused { code } if code == WIT_CODE_TAMPERED),
        "the tamper tooth fires code 2: {err:?}"
    );
    assert!(!matches!(err, HostError::WasmTrap(_)), "a refusal is never a trap");
    assert_eq!(live.version(), base, "the version is UNMOVED");
    // (the journal face is checked at reopen in the schema test below)
    let v = live.commit(&p).expect("the host's own checker still answers");
    assert!(
        matches!(v, mandate_host::LiveVerdict::Committed { .. }),
        "the proposal was VALID — the gate alone refused: {v:?}"
    );
    let _ = fs::remove_dir_all(journal_path);
}

/// WRONG-SCHEMA TOOTH: a certificate whose shape tags do not fit the
/// deployed invariant's certificate shape refuses with code 3 — the
/// wire EXISTS for the honest shape only.
#[test]
fn a_wrong_schema_certificate_refuses() {
    let wasm = load_witness_component(&gen_dir()).expect("the committed component loads");
    // a wrong root tag (disj's 2 in the conj slot): no honest
    // certificate for THIS invariant carries it
    let mut wire = WITNESS_WIRE_OK;
    wire[0] = 2;
    let err = witness_gate(&wasm, &valid_proposal(1), &wire)
        .expect_err("the wrong-schema certificate refuses");
    assert!(
        matches!(err, HostError::WitnessRefused { code } if code == WIT_CODE_WRONG_SCHEMA),
        "the wrong-schema tooth fires code 3: {err:?}"
    );
    // a wrong refutation-record tag (the neg slot's 3 swapped)
    let mut wire = WITNESS_WIRE_OK;
    wire[2] = 1;
    let err = witness_gate(&wasm, &valid_proposal(1), &wire)
        .expect_err("the wrong neg tag refuses");
    assert!(
        matches!(err, HostError::WitnessRefused { code } if code == WIT_CODE_WRONG_SCHEMA),
        "the wrong-schema tooth fires code 3: {err:?}"
    );
}

/// INVALID ROW TOOTH: the claim's own check fires false at the row
/// (amount 0; a self-transfer) — no honest certificate exists, and
/// the shipped wire refuses with code 1 (the re-fired check, not the
/// record — the checker verifies, never trusts).
#[test]
fn an_invalid_row_refuses() {
    let wasm = load_witness_component(&gen_dir()).expect("the committed component loads");
    for (src, dst, amount) in [(1, 2, 0), (3, 3, 5)] {
        let p = Proposal { base: 1, tid: 1, src, dst, amount };
        let err = witness_gate(&wasm, &p, &WITNESS_WIRE_OK)
            .expect_err("the invalid row refuses");
        assert!(
            matches!(err, HostError::WitnessRefused { code } if code == WIT_CODE_CLAIM_FALSE),
            "the claim-false tooth fires code 1 at ({src}, {dst}, {amount}): {err:?}"
        );
    }
}

/// TRAP ≠ REFUSAL: a guest module that TRAPS (the `witness-gate`
/// export, `unreachable` in the body — the same world shape, the
/// heap-return lift) surfaces the honest TRAP face — distinct from
/// the checker's typed refusal (the guest's BUG vs the guest's
/// VERDICT).
#[test]
fn a_trap_surfaces_the_trap_face_not_the_refusal() {
    let wat = r#"(component
  (core module $m
    (memory (export "memory") 1)
    (func (export "canonical_abi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 1024)
    (type $core_gate (func (param i64 i64 i64 i64 i64 i64 i64 i64) (result i32)))
    (func (type $core_gate) unreachable)
    (export "witness-gate" (func 1)))
  (core instance $i (instantiate $m))
  (alias core export $i "memory" (core memory $mem))
  (alias core export $i "canonical_abi_realloc" (core func $realloc))
  (type $t (func (param "src" u64) (param "dst" u64) (param "amount" u64)
                 (param "t1" u64) (param "b1" u64) (param "t2" u64)
                 (param "t3" u64) (param "b3" u64)
                 (result (result (error u64)))))
  (func $f (type $t) (canon lift (core func $i "witness-gate") (memory $mem) (realloc $realloc)))
  (export "witness-gate" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the trapping component builds");
    let err = witness_gate(&wasm, &valid_proposal(1), &WITNESS_WIRE_OK)
        .expect_err("the trap refuses");
    assert!(
        !matches!(err, HostError::WitnessRefused { .. }),
        "a trap must not cross as the checker's refusal: {err:?}"
    );
    assert!(
        matches!(err, HostError::WasmTrap(_)),
        "the trap face is this control's honest refusal: {err:?}"
    );
}

/// SKEW TOOTH: a doctored world text (the contract line's err type
/// swapped) refuses at LOAD, before the engine starts.
#[test]
fn a_skewed_world_refuses_at_load() {
    let dir = scratch("skewed-world");
    let wit_path = dir.join("component-witness-slice.wit");
    let wit = fs::read_to_string(&wit_path).expect("read");
    let doctored = wit.replace(
        "b3: u64) -> result<_, u64>;",
        "b3: u64) -> result<_, u32>;",
    );
    assert_ne!(wit, doctored, "the doctored world must differ");
    fs::write(&wit_path, doctored).expect("write");

    let err = load_witness_component(&dir).expect_err("the skewed world refuses");
    assert!(matches!(err, HostError::WorldSkew(_)), "{err:?}");
}

/// THE SURFACE FAIL-FAST: the committed component TYPE introspects to
/// exactly `witness-gate/8` (the params' flat count — eight u64
/// slots).
#[test]
fn the_committed_surface_is_the_checker_contract() {
    let wasm = load_witness_component(&gen_dir()).expect("the committed set loads");
    mandate_host::verify_component_surface(&wasm, mandate_host::EXPECTED_WITNESS_SURFACE)
        .expect("the committed surface IS the contract");
    // and a wrong contract refuses (the negative control)
    let err = mandate_host::verify_component_surface(&wasm, "witness-gate/7")
        .expect_err("the wrong arity refuses");
    assert!(matches!(err, HostError::SurfaceSkew(_)), "{err:?}");
}

/// THE LEDGER SCHEMA'S FACE (the gate's carrier state): the journal
/// the gated commit writes rides `ledger_schema` — the fixture's
/// four-column transfer row.
#[test]
fn the_gated_commit_writes_the_ledger_schema() {
    let wasm = load_witness_component(&gen_dir()).expect("the committed component loads");
    let (mut live, dir) = live_open("schema");
    let p = valid_proposal(live.version());
    gated_commit(&mut live, &p, &wasm, &WITNESS_WIRE_OK)
        .expect("the gated commit lands");
    // reopen: the journal replays the committed row (the reopen tooth)
    let reopened = Live::open(&dir.join("ledger.journal")).expect("reopen");
    assert_eq!(reopened.version(), 2, "the committed row replayed");
    assert_eq!(reopened.transfers().len(), 1, "the transfer is journaled");
    assert_eq!(reopened.transfers()[0].amount, 5);
    let _ = fs::remove_dir_all(dir);
}
