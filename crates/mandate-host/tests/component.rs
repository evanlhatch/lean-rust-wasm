//! The component path's teeth: the end-to-end pin (the committed
//! component loads, the guest export answers the golden through the
//! typed call), the hash/skew refusals (typed), and the
//! world/component skew teeth — each with its mandatory negative
//! control.

use std::fs;
use std::path::PathBuf;

use mandate_host::{
    load_component, load_edge_component, load_fault_component, load_string_component,
    run_component, run_edge_component, run_fault_component, run_string_component,
    verify_component_surface, EDGE_EXPORTS_1, EDGE_EXPORTS_2, EDGE_PARITY,
    EXPECTED_EDGE_SURFACE, EXPECTED_STRING_SURFACE, EXPECTED_WORLD_SURFACE,
    GUEST_EXPORT, GUEST_GOLDEN, STRING_GOLDEN, STRING_GOLDEN_INPUT, HostError,
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

/// THE SCHEMA SKEW FAIL-FAST (the D6 port — legacy guestlang-host's
/// `schema.rs`): the component TYPE's export surface (read
/// pre-instantiation from `Component::component_type`) verified
/// against the host's committed expectation.

/// THE PIN: the committed components pass their own introspection —
/// the surface the component TYPE carries IS the surface the host's
/// expectation names (the load paths run this check; the explicit
/// call is the control that the teeth are not vacuous).
#[test]
fn committed_components_pass_their_own_introspection() {
    let world = fs::read(gen_dir().join("component-slice.wasm")).expect("read");
    verify_component_surface(&world, EXPECTED_WORLD_SURFACE)
        .expect("the committed scalar component's surface matches");
    let string = fs::read(gen_dir().join("component-string-slice.wasm")).expect("read");
    verify_component_surface(&string, EXPECTED_STRING_SURFACE)
        .expect("the committed string component's surface matches");
    let edge = fs::read(gen_dir().join("component-edge-slice.wasm")).expect("read");
    verify_component_surface(&edge, EXPECTED_EDGE_SURFACE)
        .expect("the committed edge component's surface matches");
}

/// SKEW TOOTH: a valid component MISSING the expected export refuses
/// at load with the mismatch NAMED (`add64` + both surfaces in the
/// detail) — the fail-fast, not a wasm trap mid-request.
#[test]
fn surface_skew_missing_export_refuses() {
    let wat = r#"(component
  (core module $m (type (func (result i64))) (func (type 0) (result i64) i64.const 42)
    (export "other" (func 0)))
  (core instance $i (instantiate $m))
  (type $t (func (result u64)))
  (func $f (type $t) (canon lift (core func $i "other")))
  (export "other" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the export-less component builds");

    let err = verify_component_surface(&wasm, EXPECTED_WORLD_SURFACE)
        .expect_err("the missing export refuses at the surface check");
    assert!(
        matches!(err, HostError::SurfaceSkew(ref d) if d.contains("add64") && d.contains("missing export")),
        "{err:?}"
    );
}

/// SKEW TOOTH: a valid component carrying `add64` with the WRONG
/// ARITY (one flat arg, not two) refuses with the arity named.
#[test]
fn surface_skew_arity_refuses() {
    let wat = r#"(component
  (core module $m (type (func (param i64) (result i64)))
    (func (type 0) (param i64) (result i64) local.get 0)
    (export "add64" (func 0)))
  (core instance $i (instantiate $m))
  (type $t (func (param "a" u64) (result u64)))
  (func $f (type $t) (canon lift (core func $i "add64")))
  (export "add64" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the arity-skewed component builds");

    let err = verify_component_surface(&wasm, EXPECTED_WORLD_SURFACE)
        .expect_err("the arity skew refuses at the surface check");
    assert!(
        matches!(err, HostError::SurfaceSkew(ref d)
            if d.contains("add64") && d.contains("expected arity 2, guest arity 1")),
        "{err:?}"
    );
}

/// NEGATIVE CONTROL for the fail-fast itself: the surface check does
/// not refuse an honest component — the same walk over a component
/// carrying EXACTLY the expected surface passes (the extra `other`
/// export is out of contract).
#[test]
fn surface_check_passes_the_honest_component() {
    let wat = r#"(component
  (core module $m (type (func (param i64 i64) (result i64)))
    (func (type 0) (param i64 i64) (result i64) local.get 0 local.get 1 i64.add)
    (export "add64" (func 0))
    (type (func (result i64))) (func (type 1) (result i64) i64.const 7)
    (export "other" (func 1)))
  (core instance $i (instantiate $m))
  (type $t (func (param "a" u64) (param "b" u64) (result u64)))
  (func $f (type $t) (canon lift (core func $i "add64")))
  (export "add64" (func $f))
  (type $u (func (result u64)))
  (func $g (type $u) (canon lift (core func $i "other")))
  (export "other" (func $g)))"#;
    let wasm = wat::parse_str(wat).expect("the honest component builds");
    verify_component_surface(&wasm, EXPECTED_WORLD_SURFACE)
        .expect("the honest surface passes (extras are out of contract)");
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

// ── The edge lane (the edgepython frontend's parity set through the
//    SAME wasmtime harness — the three-way parity's wasmtime leg:
//    Py.pyEval ≡ the Lean executor ≡ these typed calls; the goldens
//    are the literals the Lean battery pins at the same points). ──

/// THE EDGE PIN: the committed edge component loads skew-checked and
/// every parity point answers its golden through the TYPED call —
/// double 21 = 42, adder 40 2 = 42, dec1 5 = 4, loop_sum 10 = 45 (and
/// the 0 edge), if_max both routes. The export names are the
/// component face's kebab forms; the arities dispatch on the world's
/// contract.
#[test]
fn the_edge_component_answers_the_parity_set() {
    let wasm = load_edge_component(&gen_dir()).expect("the committed edge component loads");
    for (name, a, b, want) in mandate_host::EDGE_PARITY {
        let got = run_edge_component(&wasm, name, *a, *b)
            .unwrap_or_else(|e| panic!("{name}({a}, {b}) refused: {e:?}"));
        assert_eq!(got, *want, "{name}({a}, {b}) diverged from the parity set");
    }
}

/// A fresh per-test copy of the committed EDGE artifact set (the
/// tamper teeth mutate their copy, never the committed universe).
fn edge_scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "mandate-host-edge-{}-{name}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("scratch dir");
    let committed = gen_dir();
    for f in [
        "component-edge-slice.wasm",
        "component-edge-slice.wasm.hdr",
        "component-edge-slice.wit",
    ] {
        fs::copy(committed.join(f), dir.join(f)).expect("copy the committed artifact");
    }
    dir
}

/// TAMPER TOOTH: one flipped byte in the edge component -> the hash
/// tie refuses with the typed mismatch, and the engine never sees
/// bytes (a tampered module cannot run, let alone answer).
#[test]
fn tampered_edge_component_refuses() {
    let dir = edge_scratch("tampered-edge");
    let p = dir.join("component-edge-slice.wasm");
    let mut wasm = fs::read(&p).expect("read");
    let last = wasm.len() - 1;
    wasm[last] ^= 0xff;
    fs::write(&p, wasm).expect("write");

    let err = load_edge_component(&dir).expect_err("tampered bytes refuse");
    assert!(matches!(err, HostError::ContentHashMismatch { .. }), "{err:?}");
}

/// TAMPER TOOTH: a doctored EDGE SIDECAR (the declared hash no longer
/// names the bytes) refuses too — the tie is bidirectional in effect.
#[test]
fn tampered_edge_component_sidecar_refuses() {
    let dir = edge_scratch("tampered-edge-sidecar");
    let p = dir.join("component-edge-slice.wasm.hdr");
    let sidecar = fs::read_to_string(&p).expect("read");
    let committed = fs::read_to_string(gen_dir().join("component-edge-slice.wasm.hdr"))
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

    let err = load_edge_component(&dir).expect_err("a doctored sidecar refuses");
    assert!(matches!(err, HostError::ContentHashMismatch { .. }), "{err:?}");
}

/// SKEW TOOTH: the edge world WITHOUT a contract line (the frontend's
/// parity set IS the surface — a world that lost `loop-sum` is not
/// this component's contract) refuses at load.
#[test]
fn edge_world_missing_export_refuses() {
    let dir = edge_scratch("edge-missing-export");
    let wit = fs::read_to_string(dir.join("component-edge-slice.wit")).expect("read");
    let doctored: String = wit
        .lines()
        .filter(|l| !l.contains("export loop-sum: func("))
        .chain(std::iter::once("}"))
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(dir.join("component-edge-slice.wit"), doctored).expect("write");

    let err = load_edge_component(&dir).expect_err("the export-less world refuses");
    assert!(matches!(err, HostError::WorldSkew(_)), "{err:?}");
}

/// MISMATCH TOOTH: a VALID-shaped edge component whose export carries
/// the WRONG arity (`double` with two core params, the lift declaring
/// one) — the mismatch refuses LOUDLY before any call runs: wasmtime
/// validates the lift against the core function at compile (the
/// engine's typed refusal — `EngineRefused`), the typed lift the
/// backstop (`ComponentSignature`). The host never runs a contract it
/// cannot name.
#[test]
fn edge_wrong_arity_refuses() {
    let wat = r#"(component
  (core module $m (type (func (param i64 i64) (result i64)))
    (func (type 0) (param i64 i64) (result i64) local.get 0 local.get 1 i64.add)
    (export "double" (func 0)))
  (core instance $i (instantiate $m))
  (type $t (func (param "x" u64) (result u64)))
  (func $f (type $t) (canon lift (core func $i "double")))
  (export "double" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the wat text parses");

    let err = run_edge_component(&wasm, "double", 21, 0)
        .expect_err("the wrong-arity export refuses");
    assert!(
        matches!(err, HostError::EngineRefused(_))
            || matches!(err, HostError::ComponentSignature(_)),
        "{err:?}"
    );
}

/// NEGATIVE CONTROL for the edge teeth: the COMMITTED edge artifact
/// set passes the same load path (the teeth are not vacuously wide).
#[test]
fn committed_edge_world_passes_the_surface_check() {
    let wasm = load_edge_component(&gen_dir()).expect("the committed set loads");
    assert!(!wasm.is_empty(), "the committed bytes must be present");
}

// ---------------------------------------------------------------------------
// THE FAULT LANE (the D6 port): the fault-typed result channel — the
// guest's typed refusal crosses as the host's TYPED error, never a
// trap; the trap face stays distinct.
// ---------------------------------------------------------------------------

/// The fault lane's scratch dir (the tamper-tooth discipline).
fn fault_scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "mandate-host-component-fault-{}-{name}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("scratch dir");
    let committed = gen_dir();
    for f in [
        "component-fault-slice.wasm",
        "component-fault-slice.wasm.hdr",
        "component-fault-slice.wit",
    ] {
        fs::copy(committed.join(f), dir.join(f)).expect("copy the committed artifact");
    }
    dir
}

/// THE PIN: the committed fault component loads skew-checked and the
/// guest's typed refusal crosses as the host's TYPED error — the
/// `Err(FAULT_GOLDEN)` variant rides the result channel, NOT a trap,
/// NOT an engine string.
#[test]
fn the_guest_typed_refusal_crosses_as_the_typed_fault() {
    let wasm = load_fault_component(&gen_dir()).expect("the committed fault component loads");
    let err = run_fault_component(&wasm).expect_err("the committed probe refuses (that IS its answer)");
    assert!(
        matches!(err, HostError::ComponentFault { code: c } if c == mandate_host::FAULT_GOLDEN),
        "{err:?}"
    );
    // the distinctness teeth: NOT the trap face, NOT the engine face
    assert!(!matches!(err, HostError::WasmTrap(_)), "a typed refusal is never a trap");
    assert!(!matches!(err, HostError::Engine(_)), "a typed refusal is never an engine string");
}

/// TRAP CONTROL: a guest module that TRAPS (the `probe` export,
/// `unreach` in the body — the same world shape as the committed lane,
/// heap-return lift options included) surfaces the honest TRAP face —
/// distinct from the typed-fault channel above (the same lane shape, a
/// different failure KIND: the guest's bug vs the guest's answer).
#[test]
fn a_trap_surfaces_the_trap_face_not_the_typed_fault() {
    let wat = r#"(component
  (core module $m
    (memory (export "memory") 1)
    (func (export "canonical_abi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 1024)
    (type $core_probe (func (result i32)))
    (func (type $core_probe) (result i32) unreachable)
    (export "probe" (func 1)))
  (core instance $i (instantiate $m))
  (alias core export $i "memory" (core memory $mem))
  (alias core export $i "canonical_abi_realloc" (core func $realloc))
  (type $t (func (result (result (error u64)))))
  (func $f (type $t) (canon lift (core func $i "probe") (memory $mem) (realloc $realloc)))
  (export "probe" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the trapping component builds");

    let err = run_fault_component(&wasm).expect_err("the trap refuses");
    // the honest assertion is the DISTINCTION: a trap is never the
    // typed-fault channel
    assert!(
        !matches!(err, HostError::ComponentFault { .. }),
        "a trap must not cross as a typed fault: {err:?}"
    );
    assert!(
        matches!(err, HostError::WasmTrap(_)),
        "the trap face is this control's honest refusal: {err:?}"
    );
}

/// THE OK-FACE CONTROL: a probe answering `Ok(())` is not the artifact
/// the host runs — the golden discipline refuses (the committed
/// probe's meaning is the typed refusal; an ok answer is a different
/// component wearing the world's name). The ok face still rides the
/// heap return (the disc+payload flattening) — the disc is 0, the
/// payload slot skipped.
#[test]
fn an_ok_answer_refuses_the_golden() {
    let wat = r#"(component
  (core module $m
    (memory (export "memory") 1)
    (func (export "canonical_abi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 1024)
    (type $core_ok (func (result i32)))
    (func (type $core_ok) (result i32)
      (local i32)
      i32.const 0 i32.const 0 i32.const 0 i32.const 0
      call 0
      local.tee 0
      i32.const 0
      i32.store
      local.get 0)
    (export "probe" (func 1)))
  (core instance $i (instantiate $m))
  (alias core export $i "memory" (core memory $mem))
  (alias core export $i "canonical_abi_realloc" (core func $realloc))
  (type $t (func (result (result (error u64)))))
  (func $f (type $t) (canon lift (core func $i "probe") (memory $mem) (realloc $realloc)))
  (export "probe" (func $f)))"#;
    let wasm = wat::parse_str(wat).expect("the ok-faced component builds");

    let err = run_fault_component(&wasm).expect_err("an ok answer is not the committed probe");
    assert!(
        matches!(err, HostError::ComponentAnswerMismatch { got: 0, expected: 42 }),
        "{err:?}"
    );
}
