//! THE STREAM LANE'S TEETH (the D2 `stream<u64>` row's runtime face).
//!
//! - the PULL DISCIPLINE: the host reads the stream's items until the
//!   end — the empty stream observes ONLY the end (a real guest
//!   crossing: `stream.new` + `stream.drop-writable` + the readable
//!   handle returned);
//! - the MULTI-ITEM face: the items cross IN ORDER (the session's
//!   guarantee — `ComponentTests.StreamFixture.msgs_wire`'s payloads
//!   7, 8, 9, end are the SAME literals here) — via the host-producer
//!   side of the same pull consumer, and through the zero-copy handle
//!   pass-through export (the legacy `splicer-mw` evidence);
//! - the REFUSAL teeth: a mis-shaped stream export refuses
//!   pre-instantiation with the surface named (the skew fail-fast);
//!   a stream-typed surface whose runtime answer is NOT a stream
//!   refuses at the lift (typed, never a panic).
//!
//! THE HONEST BOUNDARY (the module doc in `mandate_host::stream`): the
//! guest fixture PRODUCES no items mid-body — a guest suspending a
//! write until the consumer attaches is the async-lift callback
//! discipline (the stack-switching face), NOT landed; the
//! multi-item producer here is the HOST side of the same pull
//! discipline, and guest-side production is the named seam
//! (`mandate-host::wasi_async`).

use mandate_host::HostError;
use mandate_host::stream::{
    check_stream_pipeline_surface, check_stream_surface, drain_host_stream,
    drain_stream_u64_export, pass_through_stream, stream_engine,
};
use wasmtime::component::Component;

/// THE GOLDEN (the session's shared literals —
/// `ComponentTests.StreamFixture.streamGolden`): the multi-item face's
/// payloads, in order.
const GOLDEN: [u64; 3] = [7, 8, 9];

/// THE EMPTY-STREAM GUEST (the sync crossing): the guest body creates
/// a `stream<u64>` via the `stream.new` intrinsic (the writer in the
/// HIGH half of the packed i64, the reader in the low), drops the
/// writable half, and returns the readable handle — the export the
/// host consumes with the pull discipline.
const EMPTY_STREAM_COMPONENT: &str = r#"
(component
  (type $s (stream u64))
  (core module $m
    (import "" "stream.new" (func $sn (result i64)))
    (import "" "stream.drop-writable" (func $sdw (param i32)))
    (func (export "make") (result i32)
      (local $p i64) (local $r i32)
      call $sn
      local.set $p
      (local.set $r (i32.wrap_i64 (local.get $p)))
      (call $sdw (i32.wrap_i64 (i64.shr_u (local.get $p) (i64.const 32))))
      (local.get $r)
    )
  )
  (core func $sn (canon stream.new $s))
  (core func $sdw (canon stream.drop-writable $s))
  (core instance $i (instantiate $m
    (with "" (instance
      (export "stream.new" (func $sn))
      (export "stream.drop-writable" (func $sdw))))))
  (func $make (result (stream u64)) (canon lift (core func $i "make")))
  (export "make" (func $make))
)
"#;

/// THE PASS-THROUGH GUEST (the legacy `splicer-mw` evidence): the
/// export takes the readable half AS a handle and returns it
/// unchanged — the zero-copy handle pass-through; the items flow
/// through the handle, never through the guest's memory.
const PASS_THROUGH_COMPONENT: &str = r#"
(component
  (type $s (stream u64))
  (core module $m
    (func (export "pass") (param i32) (result i32)
      (local.get 0)
    )
  )
  (core instance $i (instantiate $m))
  (func $pass (param "s" (stream u64)) (result (stream u64))
    (canon lift (core func $i "pass")))
  (export "pass" (func $pass))
)
"#;

/// THE MIS-SHAPED EXPORT: the surface the skew tooth refuses — the
/// export is a plain u64 scalar, not a stream.
const NOT_STREAM_COMPONENT: &str = r#"
(component
  (core module $m
    (func (export "make") (result i64) (i64.const 42))
  )
  (core instance $i (instantiate $m))
  (func $make (result u64) (canon lift (core func $i "make")))
  (export "make" (func $make))
)
"#;

fn component_bytes(wat: &str) -> Vec<u8> {
    wat::parse_str(wat).expect("fixture wat parses")
}

// ---------------------------------------------------------------------------
// The empty stream (the real guest crossing)
// ---------------------------------------------------------------------------

#[test]
fn the_empty_stream_observes_only_the_end() {
    let items = drain_stream_u64_export(&component_bytes(EMPTY_STREAM_COMPONENT), "make")
        .expect("the empty stream export drains");
    assert!(items.is_empty(), "the empty stream: got {items:?}");
}

// ---------------------------------------------------------------------------
// The multi-item face: the items cross IN ORDER
// ---------------------------------------------------------------------------

#[test]
fn the_multi_item_stream_crosses_in_order() {
    // The host-producer face of the SAME pull consumer (wasmtime 47's
    // `StreamProducer` for `Vec<u64>`: items in order, then the end).
    let items = drain_host_stream(GOLDEN.to_vec()).expect("the host stream drains");
    assert_eq!(items, GOLDEN.to_vec(), "the items cross in order");
}

#[test]
fn the_empty_host_stream_drains_to_nothing() {
    let items = drain_host_stream(Vec::new()).expect("the empty host stream drains");
    assert!(items.is_empty(), "the empty host stream: got {items:?}");
}

#[test]
fn the_pass_through_stream_forwards_the_items_in_order() {
    // The legacy middleware's face: the host creates the stream over
    // the golden producer, LOWERS the readable half into the guest's
    // `pass` export (the handle crosses AS a u32), the guest answers
    // the handle unchanged, and the drain pulls the items THROUGH the
    // returned handle — the items never touch the guest's memory.
    let items = mandate_host::stream::pass_through_stream(
        &component_bytes(PASS_THROUGH_COMPONENT),
        "pass",
        GOLDEN.to_vec(),
    )
    .expect("the pass-through stream drains");
    assert_eq!(items, GOLDEN.to_vec(), "the forwarded items cross in order");
}

#[test]
fn the_pass_through_surface_refuses_a_non_stream_pipeline() {
    // The pipeline tooth: `pass` against the not-a-stream component —
    // the pipeline surface check refuses pre-instantiation.
    let err = mandate_host::stream::pass_through_stream(
        &component_bytes(NOT_STREAM_COMPONENT),
        "pass",
        GOLDEN.to_vec(),
    )
    .expect_err("a u64 export is not a pass-through pipeline");
    assert!(
        matches!(err, HostError::MissingExport(_) | HostError::SurfaceSkew(_)),
        "the pipeline tooth fires typed: {err}"
    );
}

// ---------------------------------------------------------------------------
// The refusal teeth
// ---------------------------------------------------------------------------

#[test]
fn the_mis_shaped_export_refuses_pre_instantiation() {
    let err = drain_stream_u64_export(&component_bytes(NOT_STREAM_COMPONENT), "make")
        .expect_err("a u64 export is not a stream export");
    let msg = format!("{err}");
    assert!(
        matches!(err, HostError::SurfaceSkew(_)),
        "the skew tooth fires, not a trap or a panic: {msg}"
    );
    assert!(
        msg.contains("stream<u64>") && msg.contains("make"),
        "the refusal names the export + the expected surface: {msg}"
    );
}

#[test]
fn the_missing_export_refuses() {
    let err = drain_stream_u64_export(&component_bytes(EMPTY_STREAM_COMPONENT), "nope")
        .expect_err("a missing export refuses");
    assert!(
        matches!(&err, HostError::MissingExport(n) if n == "nope"),
        "the missing-export tooth fires: {err}"
    );
}

#[test]
fn the_surface_check_is_the_pre_instantiation_gate() {
    // The surface check ALONE (no instantiation): the same teeth, at
    // the type level — the D2 row's shape read from the component TYPE.
    let engine = mandate_host::stream::stream_engine().expect("engine");
    let good = Component::from_binary(&engine, &component_bytes(EMPTY_STREAM_COMPONENT))
        .expect("the empty-stream component compiles");
    assert!(check_stream_surface(&engine, &good, "make").is_ok());
    let bad = Component::from_binary(&engine, &component_bytes(NOT_STREAM_COMPONENT))
        .expect("the not-a-stream component compiles");
    assert!(check_stream_surface(&engine, &bad, "make").is_err());
}
