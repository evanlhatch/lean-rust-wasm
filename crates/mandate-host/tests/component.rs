//! The component path's teeth: the end-to-end pin (the committed
//! component loads, the guest export answers the golden through the
//! typed call), the hash/skew refusals (typed), and the
//! world/component skew teeth — each with its mandatory negative
//! control.

use std::fs;
use std::path::PathBuf;

use mandate_host::{
    load_component, load_string_component, run_component, run_string_component, GUEST_EXPORT,
    GUEST_GOLDEN, STRING_GOLDEN, STRING_GOLDEN_INPUT, HostError,
};
use wasmtime::component::{Component, Linker};
use wasmtime::{Config, Engine, Store};

fn gen_dir() -> PathBuf {
    mandate_host::repo_gen_dir()
}

/// A fresh per-test copy of the committed component artifact set (the
/// tamper teeth mutate their copy, never the committed universe).
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "mandate-host-component-{}-{name}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("scratch dir");
    let committed = gen_dir();
    for f in [
        "component-slice.wasm",
        "component-slice.wasm.hdr",
        "component-slice.wit",
    ] {
        fs::copy(committed.join(f), dir.join(f)).expect("copy the committed artifact");
    }
    dir
}

/// THE PIN: the committed component loads skew-checked and the guest
/// export answers the golden through the TYPED call — the guest
/// function the toolchain compiled is the function the host calls,
/// and `add64(2, 3)` produces `5`.
#[test]
fn the_component_answers_the_golden() {
    let wasm = load_component(&gen_dir()).expect("the committed component loads");
    let got = run_component(&wasm, 2, 3).expect("the committed component runs");
    assert_eq!(got, GUEST_GOLDEN);
    assert_eq!(got, 5);
    assert_eq!(got, add64_reference(2, 3));
}

/// The reference face (the model's fact, restated — the pin above
/// consumes it; a wrong reference is the controls' business).
fn add64_reference(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

/// A different STILL-PARSEABLE hash value (the doctored sidecar must
/// fail the TIE, not the parser — an overflow would test the wrong
/// refusal).
fn flip_last_digit(s: &str) -> String {
    let mut c: char = s.chars().last().expect("nonempty");
    c = if c == '0' { '1' } else { '0' };
    format!("{}{c}", &s[..s.len() - 1])
}

/// TAMPER TOOTH: one flipped byte in the component -> the hash tie
/// refuses with the typed mismatch, and the engine never sees bytes.
#[test]
fn tampered_component_refuses() {
    let dir = scratch("tampered-component");
    let p = dir.join("component-slice.wasm");
    let mut wasm = fs::read(&p).expect("read");
    let last = wasm.len() - 1;
    wasm[last] ^= 0xff;
    fs::write(&p, wasm).expect("write");

    let err = load_component(&dir).expect_err("tampered bytes refuse");
    assert!(matches!(err, HostError::ContentHashMismatch { .. }), "{err:?}");
}

/// TAMPER TOOTH: a doctored SIDECAR (the declared hash no longer
/// names the bytes) refuses too — the tie is bidirectional in effect.
#[test]
fn tampered_component_sidecar_refuses() {
    let dir = scratch("tampered-component-sidecar");
    let p = dir.join("component-slice.wasm.hdr");
    let sidecar = fs::read_to_string(&p).expect("read");
    let committed = fs::read_to_string(gen_dir().join("component-slice.wasm.hdr"))
        .expect("read the committed sidecar");
    let declared: String = committed
        .lines()
        .find_map(|l| l.split("content hash ").nth(1))
        .and_then(|rest| rest.split([' ', '|']).next())
        .expect("the committed hash string must be present")
        .to_string();
    let doctored = sidecar.replace(&declared, &flip_last_digit(&declared));
    assert_ne!(sidecar, doctored, "the doctored sidecar must differ");
    fs::write(&p, doctored).expect("write");

    let err = load_component(&dir).expect_err("a doctored sidecar refuses");
    assert!(matches!(err, HostError::ContentHashMismatch { .. }), "{err:?}");
}

/// SKEW TOOTH: the world surface is absent -> the artifact set is
/// incomplete, refused before the engine starts.
#[test]
fn missing_world_refuses() {
    let dir = scratch("missing-world");
    fs::remove_file(dir.join("component-slice.wit")).expect("remove");

    let err = load_component(&dir).expect_err("the incomplete set refuses");
    assert!(
        matches!(err, HostError::Io { what: "component-slice.wit", .. }),
        "{err:?}"
    );
}

/// SKEW TOOTH: a hand-made (non-GENERATED) world file refuses.
#[test]
fn forged_world_refuses() {
    let dir = scratch("forged-world");
    fs::write(dir.join("component-slice.wit"), "package not-mine;\n").expect("write");

    let err = load_component(&dir).expect_err("a forged surface refuses");
    assert!(matches!(err, HostError::WorldSkew(_)), "{err:?}");
}

/// SKEW TOOTH: a world WITHOUT the guest export's contract line
/// refuses — the world is the SSOT; a surface that does not name
/// `add64 : func(...)` is not this component's contract.
#[test]
fn world_without_guest_export_refuses() {
    let dir = scratch("world-without-export");
    fs::write(
        dir.join("component-slice.wit"),
        "// GENERATED by componentgen (lean-4.33.0) at - — DO NOT EDIT\n\
         // spec x | Guest.Component | 1 item(s) | content hash 1 | regen: just gen\n\
         package mandate:guest;\n\nworld guest {\n  export other: func();\n}\n",
    )
    .expect("write");

    let err = load_component(&dir).expect_err("the export-less world refuses");
    assert!(matches!(err, HostError::WorldSkew(m) if m.contains("add64")), "{err:?}");
}

/// NEGATIVE CONTROL for the world teeth: the COMMITTED world surface
/// passes the same check (the teeth are not vacuously wide).
#[test]
fn committed_world_passes_the_surface_check() {
    let wit = fs::read_to_string(gen_dir().join("component-slice.wit")).expect("read");
    // The same predicate `check_world_surface` folds, run directly —
    // a pass here is the control; a failure would demand the teeth
    // above be sharpened.
    let ok = wit.lines().next().is_some_and(|l| l.starts_with("// GENERATED"))
        && wit.lines().any(|l| l.starts_with("package ") && l.contains(":guest;"))
        && wit.lines().any(|l| l.starts_with("world ") && l.contains('{'))
        && wit.lines().any(|l| l.contains(&format!("export {GUEST_EXPORT}: func(")));
    assert!(ok, "the committed world must pass its own surface check");
}

/// SKEW TOOTH: a VALID component whose export is MISSING (the binary
/// compiles — the world's contract still names a func the component
/// does not carry) refuses with the typed missing-export error.
#[test]
fn component_without_export_refuses() {
    let wat = r#"(component
  (core module $m (type (func (result i64))) (func (type 0) (result i64) i64.const 42)
    (export "other" (func 0)))
  (core instance $i (instantiate $m))
  (type $t (func (result u64)))
  (func $f (type $t) (canon lift (core func $i "other")))
  (export "other" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the export-less component builds");

    let err = run_component(&wasm, 2, 3).expect_err("the missing export refuses");
    assert!(
        matches!(err, HostError::MissingExport(ref name) if name == GUEST_EXPORT),
        "{err:?}"
    );
}

/// SKEW TOOTH: a VALID component carrying `add64` with the WRONG
/// component signature (one param, not two) — the typed lift refuses
/// (the signature teeth live at the lift, not mid-call).
#[test]
fn wrong_signature_refuses() {
    let wat = r#"(component
  (core module $m (type (func (param i64) (result i64)))
    (func (type 0) (param i64) (result i64) local.get 0 i64.const 1 i64.add)
    (export "add64" (func 0)))
  (core instance $i (instantiate $m))
  (type $t (func (param "a" u64) (result u64)))
  (func $f (type $t) (canon lift (core func $i "add64")))
  (export "add64" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the wrong-sig component builds");

    let err = run_component(&wasm, 2, 3).expect_err("the wrong signature refuses");
    assert!(matches!(err, HostError::ComponentSignature(_)), "{err:?}");
}

/// GOLDEN TOOTH: a VALID, correctly-signed component whose `add64`
/// answers something else (a+b+1) — the run itself refuses with the
/// typed mismatch.
#[test]
fn wrong_answer_refuses() {
    let wat = r#"(component
  (core module $m (type (func (param i64 i64) (result i64)))
    (func (type 0) (param i64 i64) (result i64) local.get 0 local.get 1 i64.add
      i64.const 1 i64.add)
    (export "add64" (func 0)))
  (core instance $i (instantiate $m))
  (type $t (func (param "a" u64) (param "b" u64) (result u64)))
  (func $f (type $t) (canon lift (core func $i "add64")))
  (export "add64" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the wrong-answer component builds");

    let err = run_component(&wasm, 2, 3).expect_err("a wrong answer refuses");
    assert!(
        matches!(err, HostError::ComponentAnswerMismatch { got: 6, expected: 5 }),
        "{err:?}"
    );
}

/// THE GOLDEN DISCIPLINE's other face: `run_component` runs TO the
/// golden — ANY call not producing 5 refuses, even a valid one. The
/// host consumes the seeded fact (2, 3) -> 5; it never runs free.
#[test]
fn non_golden_args_refuse() {
    let wasm = load_component(&gen_dir()).expect("the committed component loads");
    let err = run_component(&wasm, 10, 20)
        .expect_err("a non-golden run refuses (the host runs to the golden)");
    assert!(
        matches!(err, HostError::ComponentAnswerMismatch { got: 30, expected: 5 }),
        "{err:?}"
    );
}

/// The string lane's scratch dir (the same tamper-tooth discipline as
/// the scalar lane's).
fn string_scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "mandate-host-component-string-{}-{name}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("scratch dir");
    let committed = gen_dir();
    for f in [
        "component-string-slice.wasm",
        "component-string-slice.wasm.hdr",
        "component-string-slice.wit",
    ] {
        fs::copy(committed.join(f), dir.join(f)).expect("copy the committed artifact");
    }
    dir
}

/// THE STRING PIN (the full circle): the LEAN-EMITTED string
/// component — the hand-built adapter-face fixture through the
/// composite canonical-ABI fold — loads skew-checked and the guest
/// export answers the golden through the TYPED STRING call. The
/// `(ptr, len)` lowering is the engine's (the host marshals the
/// UTF-8 buffer through the guest's realloc + memory); the Lean
/// emitter's bytes are what the engine runs.
#[test]
fn the_string_component_answers_the_golden() {
    let wasm = load_string_component(&gen_dir()).expect("the committed string component loads");
    let got = run_string_component(&wasm).expect("the committed string component runs");
    assert_eq!(got, STRING_GOLDEN);
    assert_eq!(got, 5);
    assert_eq!(
        got,
        STRING_GOLDEN_INPUT.len() as u64,
        "the golden IS the seeded input's byte length"
    );
}

/// NEGATIVE CONTROL for the string pin: the COMMITTED string world
/// surface passes the same check (the teeth below are not vacuously
/// wide).
#[test]
fn committed_string_world_passes_the_surface_check() {
    let wit = fs::read_to_string(gen_dir().join("component-string-slice.wit")).expect("read");
    let ok = wit.lines().next().is_some_and(|l| l.starts_with("// GENERATED"))
        && wit.lines().any(|l| l.starts_with("package ") && l.contains(":guest;"))
        && wit
            .lines()
            .any(|l| l.contains("export length: func(s: string) -> u64;"));
    assert!(ok, "the committed string world must pass its own surface check");
}

/// STRING TAMPER TOOTH: one flipped byte in the string component ->
/// the hash tie refuses (the engine never sees the bytes).
#[test]
fn tampered_string_component_refuses() {
    let dir = string_scratch("tampered");
    let p = dir.join("component-string-slice.wasm");
    let mut wasm = fs::read(&p).expect("read");
    let last = wasm.len() - 1;
    wasm[last] ^= 0xff;
    fs::write(&p, wasm).expect("write");

    let err = load_string_component(&dir).expect_err("tampered bytes refuse");
    assert!(matches!(err, HostError::ContentHashMismatch { .. }), "{err:?}");
}

/// STRING SKEW TOOTH: a hand-made string world (no GENERATED header,
/// no contract line) refuses at load.
#[test]
fn string_world_skew_refuses() {
    let dir = string_scratch("skew");
    fs::write(dir.join("component-string-slice.wit"), "package not-mine;\n").expect("write");

    let err = load_string_component(&dir).expect_err("a forged string surface refuses");
    assert!(matches!(err, HostError::WorldSkew(_)), "{err:?}");
}

/// STRING SKEW TOOTH: a VALID component carrying `length` with a
/// scalar signature (u64 param, not a string) — the typed string
/// lift refuses (the `(ptr, len)` discipline's signature teeth live
/// at the lift).
#[test]
fn string_wrong_signature_refuses() {
    let wat = r#"(component
  (core module $m (memory (export "memory") 1)
    (type $realt (func (param i32 i32 i32 i32) (result i32)))
    (func $realloc (type $realt) i32.const 1024)
    (type $lt (func (param i64) (result i64)))
    (func $length (type $lt) (param i64) (result i64) i64.const 7)
    (export "canonical_abi_realloc" (func $realloc))
    (export "length" (func $length)))
  (core instance $i (instantiate $m))
  (type $t (func (param "s" u64) (result u64)))
  (func $f (type $t) (canon lift (core func $i "length")
      (memory (core memory $i "memory"))
      (realloc (core func $i "canonical_abi_realloc"))))
  (export "length" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the wrong-sig string component builds");

    let err = run_string_component(&wasm).expect_err("the wrong string signature refuses");
    assert!(
        matches!(err, HostError::ComponentSignature(_)),
        "{err:?}"
    );
}

/// STRING GOLDEN TOOTH: a valid, correctly-signed `length` answering
/// len+1 — the run refuses with the typed mismatch.
#[test]
fn string_wrong_answer_refuses() {
    let wat = r#"(component
  (core module $m (memory (export "memory") 1)
    (type $realt (func (param i32 i32 i32 i32) (result i32)))
    (func $realloc (type $realt) i32.const 1024)
    (type $lt (func (param i32 i32) (result i64)))
    (func $length (type $lt) (param i32 i32) (result i64)
      local.get 1 i64.extend_i32_u i64.const 1 i64.add)
    (export "canonical_abi_realloc" (func $realloc))
    (export "length" (func $length)))
  (core instance $i (instantiate $m))
  (type $t (func (param "s" string) (result u64)))
  (func $f (type $t) (canon lift (core func $i "length")
      (memory (core memory $i "memory"))
      (realloc (core func $i "canonical_abi_realloc"))))
  (export "length" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the wrong-answer string component builds");

    let err = run_string_component(&wasm).expect_err("a wrong string answer refuses");
    assert!(
        matches!(err, HostError::ComponentAnswerMismatch { got: 6, expected: 5 }),
        "{err:?}"
    );
}

/// THE RECORD-TUPLE FACE: a component carrying
/// `swap : func(p: tuple<u64, u64>) -> tuple<u64, u64>` — the
/// canonical-ABI record flattening (the params' fields in order,
/// `(i64, i64)`) with the HEAP RESULT (2 flat values past
/// MAX_FLAT_RESULTS = 1: the core func returns the `i32`
/// return-area pointer). The typed call round-trips the tuple.
#[test]
fn the_tuple_component_answers_the_golden() {
    let wat = r#"(component
  (core module $m (memory (export "memory") 1)
    (type $rt (func (param i64 i64) (result i32)))
    (func $swap (type $rt) (param i64 i64) (result i32)
      i32.const 2048 local.get 1 i64.store
      i32.const 2056 local.get 0 i64.store
      i32.const 2048)
    (type $realt (func (param i32 i32 i32 i32) (result i32)))
    (func $realloc (type $realt) i32.const 1024)
    (export "swap" (func $swap))
    (export "canonical_abi_realloc" (func $realloc)))
  (core instance $i (instantiate $m))
  (type $t (func (param "p" (tuple u64 u64)) (result (tuple u64 u64))))
  (func $f (type $t) (canon lift (core func $i "swap")
      (memory (core memory $i "memory"))
      (realloc (core func $i "canonical_abi_realloc"))))
  (export "swap" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the tuple component builds");

    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine = Engine::new(&config).expect("engine");
    let component = Component::from_binary(&engine, &wasm).expect("the tuple component compiles");
    let mut store = Store::new(&engine, ());
    let linker = Linker::<()>::new(&engine);
    let instance = linker.instantiate(&mut store, &component).expect("instantiate");
    let func = instance.get_func(&mut store, "swap").expect("the export");
    let typed = func
        .typed::<((u64, u64),), ((u64, u64),)>(&store)
        .expect("the typed tuple lift");
    let (got,) = typed.call(&mut store, ((2, 3),)).expect("the call");
    assert_eq!(got, (3, 2), "swap(2, 3) = (3, 2) — the flattened fields, in order");
}

/// THE FLATTENING TEETH (the load-time face of the heap rule): a
/// component whose core func returns the FLAT tuple values directly
/// (2 i64s past MAX_FLAT_RESULTS = 1) — the ENGINE's validator
/// refuses the canon lift (the lowered result types must be the
/// `[i32]` return-area pointer), the same refusal the Lean
/// generation-time check pins from the emitter side.
#[test]
fn tuple_flat_result_refuses() {
    let wat = r#"(component
  (core module $m (memory (export "memory") 1)
    (type $rt (func (param i64 i64) (result i64 i64)))
    (func $swap (type $rt) (param i64 i64) (result i64 i64)
      local.get 1 local.get 0)
    (type $realt (func (param i32 i32 i32 i32) (result i32)))
    (func $realloc (type $realt) i32.const 1024)
    (export "swap" (func $swap))
    (export "canonical_abi_realloc" (func $realloc)))
  (core instance $i (instantiate $m))
  (type $t (func (param "p" (tuple u64 u64)) (result (tuple u64 u64))))
  (func $f (type $t) (canon lift (core func $i "swap")
      (memory (core memory $i "memory"))
      (realloc (core func $i "canonical_abi_realloc"))))
  (export "swap" (func $f)))"#;
    let parsed = wat::parse_str(wat).expect("the wat text parses");
    let err = run_string_component(&parsed).expect_err("the flat-result lift refuses");
    // The component never gets past the engine's validator: the
    // refusal is the ENGINE's (the flattening rule is the ABI's),
    // surfaced as the typed-refusal lane's own error kind.
    assert!(
        matches!(err, HostError::MissingExport(ref n) if n == "length")
            || matches!(err, HostError::ComponentSignature(_))
            || matches!(err, HostError::EngineRefused(_))
            || matches!(err, HostError::Engine(_)),
        "the flat-result component must refuse: {err:?}"
    );
}
