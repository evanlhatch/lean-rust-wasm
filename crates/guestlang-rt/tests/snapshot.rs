//! SNAPSHOT/RESTORE CONFORMANCE: the honest v1 memory-image contract
//! (linear memory + fuel; the globals gap is documented on
//! `guestlang_rt::Snapshot`). Each test pins one clause of the contract.

use guestlang_rt::Runtime;

fn demo_wasm() -> Vec<u8> {
    let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..//lean/wasm-backend/target/demo.wasm");
    std::fs::read(std::fs::canonicalize(&p).expect("run `just wasm-compile`")).unwrap()
}

#[test]
fn snapshot_restore_is_fresh_call_equivalent() {
    // THE CONTRACT: call → snapshot → (more calls) → restore → the
    // restored instance answers like the fresh-call equivalent.
    let wasm = demo_wasm();
    let mut rt = Runtime::new(&wasm, 1_000_000).unwrap();
    assert_eq!(rt.call("double", &[21], 1_000_000).unwrap().0, vec![42]);
    let snap = rt.snapshot().unwrap();
    // the ORIGINAL instance keeps living (state moves forward)…
    assert_eq!(rt.call("double", &[100], 1_000_000).unwrap().0, vec![200]);
    // …while the RESTORED one rewinds to the snapshot point.
    let mut restored = snap.restore(&wasm).unwrap();
    assert_eq!(
        restored.call("double", &[21], 1_000_000).unwrap().0,
        vec![42]
    );
    assert_eq!(
        restored.call("double", &[100], 1_000_000).unwrap().0,
        vec![200]
    );
}

#[test]
fn restored_heap_is_coherent_alloc_heavy() {
    // The heap test: the pooled allocator + RC objects live IN the
    // memory image. An alloc-heavy run, snapshot, MORE allocs on the
    // same instance, then restore — the restored heap must serve
    // correct results (the free-lists/cursors in the image re-cohere).
    let wasm = demo_wasm();
    let mut rt = Runtime::new(&wasm, 1_000_000).unwrap();
    assert_eq!(
        rt.call("double-area", &[5], 1_000_000).unwrap().0,
        vec![100]
    );
    let snap = rt.snapshot().unwrap();
    // alloc-heavy continuation on the retained instance: fresh objects
    // on top of the snapshot's heap layout
    // the ORACLE: double-area 100 = (2*100)^2 = 40000 (the duel's authority)
    assert_eq!(
        rt.call("double-area", &[100], 1_000_000).unwrap().0,
        vec![40000]
    );
    assert_eq!(rt.call("run-paps", &[5], 1_000_000).unwrap().0, vec![8]);
    // restore: the image's heap is coherent — both a replayed call AND
    // a fresh allocation pattern give the right answers
    let mut restored = snap.restore(&wasm).unwrap();
    assert_eq!(
        restored.call("double-area", &[5], 1_000_000).unwrap().0,
        vec![100]
    );
    // the ORACLE: double-area 7 = (2*7)^2 = 196
    assert_eq!(
        restored.call("double-area", &[7], 1_000_000).unwrap().0,
        vec![196]
    );
    assert_eq!(
        restored.call("run-paps", &[3], 1_000_000).unwrap().0,
        vec![6]
    );
}

#[test]
fn snapshot_carries_live_state_not_zeros() {
    // NEGATIVE CONTROL against a vacuous snapshot: if the captured
    // image equals a fresh instance's image, the API "restores"
    // nothing. The heap bytes MUST diverge once the guest allocated.
    let wasm = demo_wasm();
    let mut rt = Runtime::new(&wasm, 1_000_000).unwrap();
    let fresh = rt.snapshot().unwrap();
    // the ORACLE: double-area 9 = (2*9)^2 = 324
    assert_eq!(
        rt.call("double-area", &[9], 1_000_000).unwrap().0,
        vec![324]
    );
    let dirty = rt.snapshot().unwrap();
    assert_ne!(
        fresh.memory(),
        dirty.memory(),
        "snapshot captured no live heap state — the memory image is vacuous"
    );
}

#[test]
fn fuel_state_is_captured_and_restored() {
    let wasm = demo_wasm();
    let mut rt = Runtime::new(&wasm, 1_000_000).unwrap();
    rt.call("double", &[21], 1_000_000).unwrap();
    let snap = rt.snapshot().unwrap();
    // the capture: strictly less fuel than the initial endowment, and
    // the burn is the run-stable consumption the conformance pin ties
    let consumed = 1_000_000 - snap.fuel();
    assert!(consumed > 0, "snapshot lost the fuel burn");
    // the restore: the fuel state comes back exactly
    let restored = snap.restore(&wasm).unwrap();
    assert_eq!(restored.fuel().unwrap(), snap.fuel());
}

#[test]
fn snapshot_requires_a_memory_export() {
    // NEGATIVE CONTROL for the memory-export precondition: a module
    // with no memory at all is refused LOUDLY at snapshot time — never
    // a silently-empty image. Hand-encoded: (func (export "f")
    // (result i32) i32.const 7) — no memory section.
    let no_memory_wasm: &[u8] = &[
        0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, // magic + version
        0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7F, // type: () -> i32
        0x03, 0x02, 0x01, 0x00, // func 0: type 0
        0x07, 0x05, 0x01, 0x01, 0x66, 0x00, 0x00, // export "f" func 0
        0x0A, 0x06, 0x01, 0x04, 0x00, 0x41, 0x07, 0x0B, // i32.const 7, end
    ];
    let mut rt = Runtime::new(no_memory_wasm, 1_000).unwrap();
    assert_eq!(rt.call("f", &[], 1_000).unwrap().0, vec![7]);
    let err = rt.snapshot().unwrap_err();
    assert!(err.0.contains("`memory` export"), "{err}");
}

#[test]
fn retained_instance_state_accumulates_until_snapshot() {
    // The other half of the contract: a RETAINED Runtime is NOT
    // stateless — calls accumulate on the same heap (this is what the
    // snapshot freezes). double-area twice on one instance must match
    // the one-shot results both times (the allocator keeps serving).
    let wasm = demo_wasm();
    let mut rt = Runtime::new(&wasm, 1_000_000).unwrap();
    // the ORACLE: double-area 3 = 36
    assert_eq!(rt.call("double-area", &[3], 1_000_000).unwrap().0, vec![36]);
    // the ORACLE: double-area 4 = (2*4)^2 = 64
    assert_eq!(rt.call("double-area", &[4], 1_000_000).unwrap().0, vec![64]);
    // and the snapshot of THIS accumulated heap still rewinds cleanly
    let snap = rt.snapshot().unwrap();
    let mut restored = snap.restore(&wasm).unwrap();
    // the ORACLE: the restored heap computes identically
    assert_eq!(
        restored.call("double-area", &[3], 1_000_000).unwrap().0,
        vec![36]
    );
}
