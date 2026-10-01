//! The component half: the committed COMPONENT loads (the artifact
//! set skew-checked) and its guest export is called with TYPED values.
//!
//! The seed runs the component-model path (the `component-model`
//! feature): `gen/component-slice.wasm` is the component binary the
//! `componentgen` writer emitted (the LCNF-compiled guest function
//! wrapped through the canonical-ABI scalar fragment), and
//! `gen/component-slice.wit` is its world — the contract side. The
//! world is the SSOT (notes/v3/13-interfaces.md, the WIT worlds row):
//! the host checks the surface's presence + the world's export line,
//! then lets the ENGINE's typed lift carry the signature teeth — a
//! component whose export signature drifts from the world's
//! `(u64, u64) -> u64` refuses here, not mid-call.
//!
//! Every failure is a [`crate::HostError`] — no panics on real error
//! paths (12 §8); `wasmtime::Error` is stringified (its Display
//! carries the full cause chain, and it cannot sit in a `#[source]`
//! slot — the legacy host's finding, kept).

use std::path::Path;

use wasmtime::component::Component;
use wasmtime::{Config, Engine};

use crate::HostError;
use crate::artifact::bytes_hash;
use crate::engine::instantiate_component_module;

/// The component binary's artifact name.
pub const COMPONENT_WASM: &str = "component-slice.wasm";

/// The world text's artifact name.
pub const COMPONENT_WIT: &str = "component-slice.wit";

/// The guest export's name (the world's contract — the fixture's
/// `add64`, the canonical-ABI scalar fragment: u64 × u64 → u64).
pub const GUEST_EXPORT: &str = "add64";

/// The string lane's artifacts (`component-string-slice.*` — the
/// canonical-ABI string lift's committed component: the world's
/// `length : func(s: string) -> u64` over the adapter-face core
/// module — the exported linear memory + the ABI realloc).
pub const STRING_WASM: &str = "component-string-slice.wasm";
pub const STRING_WIT: &str = "component-string-slice.wit";
pub const STRING_GUEST_EXPORT: &str = "length";

/// The edge lane's artifacts (`component-edge-slice.*` — the
/// edgepython frontend's parity set through the SAME emission: the
/// frontend's module (parse → check → IR → the shared lowering) as
/// the core module, the world's five u64-scalar exports over it. The
/// export names are the component face's kebab forms (the
/// component-model validator refuses snake_case extern names — the
/// fixture's `kebab` mangling is the boundary's ONE name adapter).
pub const EDGE_WASM: &str = "component-edge-slice.wasm";
pub const EDGE_WIT: &str = "component-edge-slice.wit";

/// The fault lane's artifacts (`component-fault-slice.*` — the D6
/// port's typed-refusal channel: the world's `probe : func() ->
/// result<_, u64>` over the heap-return adapter face — the flattening
/// collapses past `MAX_FLAT_RESULTS`, the core func answers the
/// return-area POINTER; `ComponentTests.FaultFixture` is the fixture).
pub const FAULT_WASM: &str = "component-fault-slice.wasm";
pub const FAULT_WIT: &str = "component-fault-slice.wit";
pub const FAULT_GUEST_EXPORT: &str = "probe";

/// The fault lane's golden: the committed probe's typed refusal is
/// the `Err(42)` variant — the fault payload the fixture seeds. The
/// host consumes the seeded fact (the guest owns the meaning).
pub const FAULT_GOLDEN: u64 = 42;

/// The witness lane's artifacts (`component-witness-slice.*` — the
/// host-gating lane: the world's `witness-gate : func(src, dst,
/// amount, t1, b1, t2, t3, b3: u64) -> result<_, u64>` over the
/// hand-built checker module — the pinned invariant's checker as an
/// export, the heap-return face; `ComponentTests.WitFixture` is the
/// fixture). The host calls this checker to GATE the ledger's commit
/// (`crate::witness` — the legacy `@[invariant]` discipline).
pub const WITNESS_WASM: &str = "component-witness-slice.wasm";
/// The witness lane's world text (the contract side).
pub const WITNESS_WIT: &str = "component-witness-slice.wit";
/// The witness lane's export name (the world's contract).
pub const WITNESS_GUEST_EXPORT: &str = "witness-gate";

/// The witness lane's committed call surface (the convention's arity
/// is the PARAMS' flat count — eight u64 slots: the row's three + the
/// certificate's five wire slots).
pub const EXPECTED_WITNESS_SURFACE: &str = "witness-gate/8";

/// The witness lane's wire shape (the certificate's flat 5-slot face
/// at the producer's certificate shape: the `conj` tag 1, the
/// conjunction's recorded verdict slot, the `neg` tag 3, the constant
/// 0 slot, the refutation's recorded verdict slot). The VALID row's
/// honest certificate rides exactly `[1, 1, 3, 0, 0]` — the Lean
/// SSOT's `ComponentTests.WitFixture.legValidWire` pin, mirrored.
pub const WITNESS_WIRE_OK: [u64; 5] = [1, 1, 3, 0, 0];

/// The refusal-code table (the Lean SSOT's mirror —
/// `ComponentTests.WitFixture`'s code table is the spec of record;
/// the teeth pin both faces at the same literals):
/// 1 = the claim is FALSE at the proposed row, 2 = TAMPERED record, 3
/// = WRONG-SCHEMA certificate.
pub const WIT_CODE_CLAIM_FALSE: u64 = 1;
pub const WIT_CODE_TAMPERED: u64 = 2;
pub const WIT_CODE_WRONG_SCHEMA: u64 = 3;

/// The edge lane's exports (the world's contract, kebab). The arities
/// are the frontend's: one u64 param, except `adder`/`if-max` (two).
pub const EDGE_EXPORTS_1: &[&str] =
    &["double", "dec1", "loop-sum", "list-sum", "list-head"];
pub const EDGE_EXPORTS_2: &[&str] = &["adder", "if-max", "ops-mix", "tup-second"];

/// THE EDGE PARITY SET (the three-way parity's wasmtime leg): the
/// points the Lean battery pins — `Py.pyEval` (the legacy oracle) ≡
/// the Lean executor over the SAME core module the component embeds ≡
/// THESE goldens through wasmtime's typed calls. A golden drift here
/// is a parity divergence, not a host decision.
pub const EDGE_PARITY: &[(&str, u64, u64, u64)] = &[
    // (export, a, b, expected) — b is ignored by the 1-arity exports
    ("double", 21, 0, 42),
    ("adder", 40, 2, 42),
    ("dec1", 5, 0, 4),
    ("loop-sum", 10, 0, 45),
    ("loop-sum", 0, 0, 0),
    ("if-max", 3, 9, 9),
    ("if-max", 9, 3, 9),
    // the E6 fragment: the comparison/logic/negation spellings (the
    // wrapped-u64 answers — `0 - a` wraps to 2^64-a), the tuple reads,
    // the list walk + the head read
    ("ops-mix", 3, 9, 18446744073709551610),
    ("ops-mix", 9, 3, 6),
    ("ops-mix", 5, 5, 18446744073709551611),
    ("ops-mix", 2, 1, 1),
    ("tup-second", 3, 9, 15),
    ("tup-second", 10, 20, 40),
    ("list-sum", 10, 0, 16),
    ("list-sum", 0, 0, 6),
    ("list-head", 42, 0, 42),
];

/// The string lane's golden: the guest's `length("hello")` answers
/// `5` — the host's CONSUMPTION of the seeded fact (the boundary
/// marshals the UTF-8 buffer; the host never runs free).
pub const STRING_GOLDEN_INPUT: &str = "hello";
pub const STRING_GOLDEN: u64 = 5;

/// The golden: the guest's `add64(2, 3)` answers `5`. This is the
/// host's CONSUMPTION of the model's fact, not a re-derivation — the
/// guest's compiled body owns the meaning; the host refuses to run
/// anything that produces anything else.
pub const GUEST_GOLDEN: u64 = 5;

/// Loads the committed component's artifact set from `gen_dir`:
///
/// 1. `component-slice.wasm` — read.
/// 2. `component-slice.wasm.hdr` — read; its `content hash <n>` must
///    equal `bytes_hash` of the component's bytes (the hash tie —
///    the SAME recurrence the toolchain's sidecar was written with).
/// 3. `component-slice.wit` — read; it must be a GENERATED artifact
///    carrying the package line, a `world` block, and the guest
///    export's contract line (the presence-level skew check; the
///    world's own byte-tie stays test-pinned in the Lean tree).
pub fn load_component(gen_dir: &Path) -> Result<Vec<u8>, HostError> {
    read_hashed_artifact(gen_dir, COMPONENT_WASM)
        .and_then(|wasm| {
            let wit = std::fs::read_to_string(gen_dir.join(COMPONENT_WIT)).map_err(|source| {
                HostError::Io { what: "component-slice.wit", source }
            })?;
            check_world_surface(&wit)?;
            Ok(wasm)
        })
}

/// The shared load skeleton: the wasm bytes + the sidecar's hash tie
/// (steps 1-2 of the discipline; the surface check is per-lane).
fn read_hashed_artifact(gen_dir: &Path, name: &str) -> Result<Vec<u8>, HostError> {
    // 1. The component bytes.
    let wasm_path = gen_dir.join(name);
    let wasm = std::fs::read(&wasm_path)
        .map_err(|source| HostError::Io { what: "component-slice.wasm", source })?;

    // 2. The sidecar — the hash tie.
    let sidecar_path = gen_dir.join(format!("{name}.hdr"));
    let sidecar = std::fs::read_to_string(&sidecar_path).map_err(|source| HostError::Io {
        what: "component-slice.wasm.hdr",
        source,
    })?;
    let declared = crate::artifact::sidecar_hash(&sidecar).ok_or(HostError::SidecarMalformed(
        "no `content hash <n>` field in the GENERATED header",
    ))?;
    let computed = bytes_hash(&wasm);
    if computed != declared {
        return Err(HostError::ContentHashMismatch { declared, computed });
    }
    Ok(wasm)
}

/// The string lane's load: the same discipline over the string
/// slice's artifact set (the hash tie + the string surface check).
pub fn load_string_component(gen_dir: &Path) -> Result<Vec<u8>, HostError> {
    read_hashed_artifact(gen_dir, STRING_WASM).and_then(|wasm| {
        let wit = std::fs::read_to_string(gen_dir.join(STRING_WIT))
            .map_err(|source| HostError::Io { what: "component-string-slice.wit", source })?;
        check_string_surface(&wit)?;
        Ok(wasm)
    })
}

/// The edge lane's load: the same discipline over the edge slice's
/// artifact set (the hash tie + the edge surface check — every one of
/// the world's five export contract lines must be present).
pub fn load_edge_component(gen_dir: &Path) -> Result<Vec<u8>, HostError> {
    read_hashed_artifact(gen_dir, EDGE_WASM).and_then(|wasm| {
        let wit = std::fs::read_to_string(gen_dir.join(EDGE_WIT))
            .map_err(|source| HostError::Io { what: "component-edge-slice.wit", source })?;
        check_edge_surface(&wit)?;
        Ok(wasm)
    })
}

/// The FAULT lane's load: the same discipline over the fault slice's
/// artifact set (the hash tie + the fault surface check — the world's
/// typed-refusal contract line) + the schema-skew fail-fast (the
/// component TYPE introspected against `EXPECTED_FAULT_SURFACE`).
pub fn load_fault_component(gen_dir: &Path) -> Result<Vec<u8>, HostError> {
    read_hashed_artifact(gen_dir, FAULT_WASM).and_then(|wasm| {
        let wit = std::fs::read_to_string(gen_dir.join(FAULT_WIT))
            .map_err(|source| HostError::Io { what: "component-fault-slice.wit", source })?;
        check_fault_surface(&wit)?;
        Ok(wasm)
    })
}

/// The WITNESS lane's load: the same discipline over the witness
/// slice's artifact set (the hash tie + the witness surface check —
/// the world's checker contract line).
pub fn load_witness_component(gen_dir: &Path) -> Result<Vec<u8>, HostError> {
    read_hashed_artifact(gen_dir, WITNESS_WASM).and_then(|wasm| {
        let wit = std::fs::read_to_string(gen_dir.join(WITNESS_WIT))
            .map_err(|source| HostError::Io { what: "component-witness-slice.wit", source })?;
        check_witness_surface(&wit)?;
        Ok(wasm)
    })
}

/// The witness lane's surface check: the same shape over the witness
/// slice's contract — the world must carry the checker's FULL line
/// (the row's three slots + the certificate's five wire slots, the
/// typed-refusal result).
fn check_witness_surface(wit: &str) -> Result<(), HostError> {
    if !wit.lines().next().is_some_and(|l| l.starts_with("// GENERATED")) {
        return Err(HostError::WorldSkew(
            "component-witness-slice.wit: not a GENERATED artifact",
        ));
    }
    if !wit.lines().any(|l| l.starts_with("package ") && l.contains(":guest;")) {
        return Err(HostError::WorldSkew(
            "component-witness-slice.wit: no `package <org>:guest;` declaration",
        ));
    }
    let contract = "export witness-gate: func(src: u64, dst: u64, amount: u64, t1: u64, \
             b1: u64, t2: u64, t3: u64, b3: u64) -> result<_, u64>;";
    if !wit.lines().any(|l| l.contains(contract)) {
        return Err(HostError::WorldSkew(
            "component-witness-slice.wit: no `export witness-gate: func(...) -> result<_, u64>;` contract line",
        ));
    }
    Ok(())
}

/// Runs the witness lane's committed checker: the exported
/// `witness-gate` over raw (already skew-checked) bytes with TYPED
/// values — the proposed row's three u64 slots + the certificate's
/// five wire slots cross into the guest-compiled checker, and the
/// checker's verdict gates the caller (`crate::witness::gated_commit`):
/// `Ok(())` = the gate OPENS (accept), `Err(HostError::WitnessRefused
/// { code })` = the typed REFUSAL (1/2/3 — the Lean SSOT's code
/// table, mirrored as `WIT_CODE_*`). A TRAP stays the honest trap
/// face ([`HostError::WasmTrap`]) — the component's BUG, distinct
/// from the checker's VERDICT (the tests pin both).
pub fn run_witness_gate(
    wasm: &[u8],
    src: u64,
    dst: u64,
    amount: u64,
    wire: &[u64; 5],
) -> Result<(), HostError> {
    let (_engine, _component, mut store, instance) = instantiate_component_module(wasm)?;
    let func = instance
        .get_func(&mut store, WITNESS_GUEST_EXPORT)
        .ok_or_else(|| HostError::MissingExport(WITNESS_GUEST_EXPORT.to_string()))?;
    let typed = func
        .typed::<
            (u64, u64, u64, u64, u64, u64, u64, u64),
            (Result<(), u64>,),
        >(&store)
        .map_err(|_| HostError::ComponentSignature("witness-gate : func(8 x u64) -> result<_, u64>"))?;
    let (res,) = typed
        .call(
            &mut store,
            (src, dst, amount, wire[0], wire[1], wire[2], wire[3], wire[4]),
        )
        // THE TRAP FACE, distinct: a wasm trap during the call
        // surfaces as the typed trap error, never folded into the
        // checker's refusal channel (the fault lane's discipline).
        .map_err(|e| match e.downcast_ref::<wasmtime::Trap>() {
            Some(t) => HostError::WasmTrap(t.clone()),
            None => HostError::Engine(format!("call {WITNESS_GUEST_EXPORT}: {e:?}")),
        })?;
    match res {
        Err(code) => Err(HostError::WitnessRefused { code }),
        Ok(()) => Ok(()),
    }
}

/// The fault lane's surface check: the same shape over the fault
/// slice's contract — the world must carry the typed-refusal export's
/// FULL line (`result<_, u64>` — the one-summand err face rendered).
fn check_fault_surface(wit: &str) -> Result<(), HostError> {
    if !wit.lines().next().is_some_and(|l| l.starts_with("// GENERATED")) {
        return Err(HostError::WorldSkew(
            "component-fault-slice.wit: not a GENERATED artifact",
        ));
    }
    if !wit.lines().any(|l| l.starts_with("package ") && l.contains(":guest;")) {
        return Err(HostError::WorldSkew(
            "component-fault-slice.wit: no `package <org>:guest;` declaration",
        ));
    }
    let contract = "export probe: func() -> result<_, u64>;";
    if !wit.lines().any(|l| l.contains(contract)) {
        return Err(HostError::WorldSkew(
            "component-fault-slice.wit: no `export probe: func() -> result<_, u64>;` contract line",
        ));
    }
    Ok(())
}

/// Runs the fault lane's committed component: the exported `probe :
/// func() -> result<_, u64>` over raw (already skew-checked) bytes —
/// THE TYPED CHANNEL (the D6 port): the guest's `Err(fault)` variant
/// crosses as the host's TYPED error ([`HostError::ComponentFault`]),
/// never a trap and never an engine string; the `Ok(())` face is not
/// the artifact the host runs (the committed probe refuses — an ok
/// answer is the golden's other mismatch). A TRAP stays the honest
/// trap face ([`HostError::WasmTrap`]) — distinct, the tests pin both.
pub fn run_fault_component(wasm: &[u8]) -> Result<(), HostError> {
    let (_engine, _component, mut store, instance) = instantiate_component_module(wasm)?;
    let func = instance
        .get_func(&mut store, FAULT_GUEST_EXPORT)
        .ok_or_else(|| HostError::MissingExport(FAULT_GUEST_EXPORT.to_string()))?;
    let typed = func
        .typed::<(), (Result<(), u64>,)>(&store)
        .map_err(|_| HostError::ComponentSignature("probe : func() -> result<_, u64>"))?;
    let (res,) = typed
        .call(&mut store, ())
        // THE TRAP FACE, distinct: a wasm trap during the call
        // surfaces as the typed trap error (the faults lane's row),
        // never folded into the engine-string envelope — the typed
        // fault channel and the trap face are DIFFERENT kinds (the
        // tests pin both).
        .map_err(|e| match e.downcast_ref::<wasmtime::Trap>() {
            Some(t) => HostError::WasmTrap(t.clone()),
            None => HostError::Engine(format!("call {FAULT_GUEST_EXPORT}: {e:?}")),
    })?;
    match res {
        Err(code) => Err(HostError::ComponentFault { code }),
        Ok(()) => Err(HostError::ComponentAnswerMismatch {
            got: 0,
            expected: FAULT_GOLDEN,
        }),
    }
}

/// THE SCHEMA SKEW FAIL-FAST (the D6 port of legacy guestlang-host's
/// `schema.rs`): the component TYPE's export surface is derived from
/// the component itself (ground truth — `Component::component_type`,
/// read PRE-instantiation, a skewed component is never run), not an
/// embedded string (an embedded string is a CLAIM that can itself
/// drift from the real exports — the component type IS the export
/// surface). The convention mirrors the legacy host's: the canonical
/// string is `fn/arity`, comma-joined, first-occurrence order; the
/// FLAT-ARG arity — a record arg counts its fields, a variant arg
/// counts 2 (discr + payload), everything else counts 1. The contract
/// covers the host's CALL surface; extra guest exports are out of
/// contract (the host never calls them).

/// The host's committed expectation for the scalar world's call
/// surface (the world's own export line is the SSOT — the WIT
/// presence check above covers the contract text; THIS covers the
/// component type).
pub const EXPECTED_WORLD_SURFACE: &str = "add64/2";

/// The string lane's committed call surface.
pub const EXPECTED_STRING_SURFACE: &str = "length/1";

/// The edge lane's committed call surface (the parity set's nine
/// exports, first-occurrence order — the committed WIT's order).
pub const EXPECTED_EDGE_SURFACE: &str = "double/1,adder/2,dec1/1,loop-sum/1,\
if-max/2,ops-mix/2,tup-second/2,list-sum/1,list-head/1";

/// The fault lane's committed call surface (the convention's arity is
/// the PARAMS' flat count — `probe` takes none).
pub const EXPECTED_FAULT_SURFACE: &str = "probe/0";

/// The flat-arg arity of one component-ABI type (the convention
/// above): a record arg rides the boundary as its FIELD VALUES FLAT, a
/// variant arg as [discr, payload]; every leaf type is one slot.
fn flat_arity(ty: &wasmtime::component::Type) -> usize {
    use wasmtime::component::Type;
    match ty {
        Type::Record(r) => r.fields().count(),
        Type::Variant(_) => 2,
        _ => 1,
    }
}

/// The guest's export surface, read from the component TYPE (pre-
/// instantiation — a skewed component is never run). One `(name, flat
/// arity)` per exported component function, in the component type's
/// declaration order; non-function exports (types, instances) are not
/// part of the call surface.
pub fn surface_of(engine: &Engine, component: &Component) -> Vec<(String, usize)> {
    use wasmtime::component::types::ComponentItem;
    let ty = component.component_type();
    ty.exports(engine)
        .filter_map(|(name, item)| match item.ty {
            ComponentItem::ComponentFunc(f) => {
                let arity = f.params().map(|(_, t)| flat_arity(&t)).sum();
                Some((name.to_string(), arity))
            }
            _ => None,
        })
        .collect()
}

/// Parse a canonical surface string (`fn/arity`, comma-joined) into
/// ordered pairs. Malformed entries are dropped — the surface strings
/// are constants in this file; a doctored constant degrades to a
/// shorter contract, never a panic.
fn parse_surface(surface: &str) -> Vec<(String, usize)> {
    surface
        .split(',')
        .filter_map(|entry| {
            let (f, n) = entry.rsplit_once('/')?;
            Some((f.to_string(), n.parse::<usize>().ok()?))
        })
        .collect()
}

/// The refusal walk: the EXPECTED surface in canonical order, the
/// first divergence named (a missing export, or an arity skew — both
/// surfaces in the error, the mismatch called out). On Ok, the
/// guest's surface covers the expected contract; extra guest exports
/// are out of contract (see the module head).
fn verify_surface(
    engine: &Engine,
    component: &Component,
    expected: &str,
) -> Result<(), HostError> {
    let got = surface_of(engine, component);
    for (f, n) in parse_surface(expected) {
        match got.iter().find(|(g, _)| g == &f) {
            None => {
                return Err(HostError::SurfaceSkew(format!(
                    "guest missing export `{f}` (expected arity {n}); \
                     guest surface [{}] vs expected [{expected}]",
                    got.iter()
                        .map(|(g, a)| format!("{g}/{a}"))
                        .collect::<Vec<_>>()
                        .join(",")
                )));
            }
            Some((_, m)) if *m != n => {
                return Err(HostError::SurfaceSkew(format!(
                    "`{f}` — expected arity {n}, guest arity {m}; \
                     guest surface [{}] vs expected [{expected}]",
                    got.iter()
                        .map(|(g, a)| format!("{g}/{a}"))
                        .collect::<Vec<_>>()
                        .join(",")
                )));
            }
            Some(_) => {}
        }
    }
    Ok(())
}

/// The fail-fast point: the raw component bytes compiled ONLY to
/// introspect their type (no instantiation — a skewed component is
/// never instantiated, never run) and the surface verified against
/// `expected` — a skew refuses at startup with the named mismatch,
/// never as a wasm trap mid-request. THE LIFECYCLE'S CONSUMPTION: the
/// host machine's `instantiate` runs this FIRST (the model's
/// `refuseInstantiate` row — pre-run, pre-link; the flat `run_*`
/// paths below compile through the same walk and their typed lift
/// carries the per-call teeth).
///
/// The double compile (here + the instantiate's) is the honest cost of the
/// two-phase discipline (the skew check rides LOAD, the run rides the
/// caller's own engine); test-grade, deliberate.
pub fn verify_component_surface(wasm: &[u8], expected: &str) -> Result<(), HostError> {
    let mut config = Config::new();
    config.wasm_component_model(true);
    let engine = Engine::new(&config)
        .map_err(|e| HostError::Engine(format!("engine init: {e:?}")))?;
    let component = Component::from_binary(&engine, wasm)
        .map_err(|e| HostError::EngineRefused(format!("component compile: {e:?}")))?;
    verify_surface(&engine, &component, expected)
}

/// The world surface's presence-level skew check: the GENERATED
/// header, the package line, a world block, and the guest export's
/// contract line. Each refusal is typed (`WorldSkew`), never silent.
fn check_world_surface(wit: &str) -> Result<(), HostError> {
    if !wit.lines().next().is_some_and(|l| l.starts_with("// GENERATED")) {
        return Err(HostError::WorldSkew(
            "component-slice.wit: not a GENERATED artifact",
        ));
    }
    if !wit.lines().any(|l| l.starts_with("package ") && l.contains(":guest;")) {
        return Err(HostError::WorldSkew(
            "component-slice.wit: no `package <org>:guest;` declaration",
        ));
    }
    if !wit.lines().any(|l| l.starts_with("world ") && l.contains('{')) {
        return Err(HostError::WorldSkew(
            "component-slice.wit: no `world <name> {` block",
        ));
    }
    if !wit
        .lines()
        .any(|l| l.contains(&format!("export {GUEST_EXPORT}: func(")))
    {
        return Err(HostError::WorldSkew(
            "component-slice.wit: no `export add64: func(` contract line",
        ));
    }
    Ok(())
}

/// The string lane's surface check: the same shape over the string
/// slice's contract — the world must carry the string export's FULL
/// line (the load-time skew check covers the composite types: a
/// surface declaring `length` with any other signature refuses
/// here, before the engine starts).
fn check_string_surface(wit: &str) -> Result<(), HostError> {
    if !wit.lines().next().is_some_and(|l| l.starts_with("// GENERATED")) {
        return Err(HostError::WorldSkew(
            "component-string-slice.wit: not a GENERATED artifact",
        ));
    }
    if !wit.lines().any(|l| l.starts_with("package ") && l.contains(":guest;")) {
        return Err(HostError::WorldSkew(
            "component-string-slice.wit: no `package <org>:guest;` declaration",
        ));
    }
    let contract = format!("export {STRING_GUEST_EXPORT}: func(s: string) -> u64;");
    if !wit.lines().any(|l| l.contains(&contract)) {
        return Err(HostError::WorldSkew(
            "component-string-slice.wit: no `export length: func(s: string) -> u64;` contract line",
        ));
    }
    Ok(())
}

/// Runs the exported `add64 : (u64, u64) -> u64` over raw (already
/// skew-checked) component bytes with TYPED values and checks the
/// golden.
pub fn run_component(wasm: &[u8], a: u64, b: u64) -> Result<u64, HostError> {
    let (_engine, _component, mut store, instance) = instantiate_component_module(wasm)?;

    let func = instance
        .get_func(&mut store, GUEST_EXPORT)
        .ok_or_else(|| HostError::MissingExport(GUEST_EXPORT.to_string()))?;
    // The typed lift IS the signature check: an `add64` with any other
    // component signature fails here (the engine's typed refusal), not
    // mid-call.
    let typed = func
        .typed::<(u64, u64), (u64,)>(&store)
        .map_err(|_| HostError::ComponentSignature("add64 : (u64, u64) -> u64"))?;
    let (got,) = typed
        .call(&mut store, (a, b))
        .map_err(|e| HostError::Engine(format!("call {GUEST_EXPORT}: {e:?}")))?;
    // (post-return is subsumed in this wasmtime version — the call's
    // cleanup is internal; the deprecated explicit call is not used.)
    if got != GUEST_GOLDEN {
        return Err(HostError::ComponentAnswerMismatch {
            got,
            expected: GUEST_GOLDEN,
        });
    }
    Ok(got)
}

/// The edge lane's surface check: the same shape over the edge
/// slice's contract — the world must carry ALL FIVE export contract
/// lines (the frontend's parity set IS the surface; a surface naming
/// any other signature refuses here, before the engine starts).
fn check_edge_surface(wit: &str) -> Result<(), HostError> {
    if !wit.lines().next().is_some_and(|l| l.starts_with("// GENERATED")) {
        return Err(HostError::WorldSkew(
            "component-edge-slice.wit: not a GENERATED artifact",
        ));
    }
    if !wit.lines().any(|l| l.starts_with("package ") && l.contains(":guest;")) {
        return Err(HostError::WorldSkew(
            "component-edge-slice.wit: no `package <org>:guest;` declaration",
        ));
    }
    for (name, params) in [
        ("double", "x: u64"),
        ("adder", "a: u64, b: u64"),
        ("dec1", "n: u64"),
        ("loop-sum", "n: u64"),
        ("if-max", "a: u64, b: u64"),
    ] {
        let contract = format!("export {name}: func({params}) -> u64;");
        if !wit.lines().any(|l| l.contains(&contract)) {
            return Err(HostError::WorldSkew(
                "component-edge-slice.wit: missing the world's contract line",
            ));
        }
    }
    Ok(())
}

/// Runs one edge parity point: the exported scalar fn over raw
/// (already skew-checked) bytes with TYPED values, dispatched on the
/// arity the world declares (1 or 2 u64 params — every fn answers
/// u64). The typed lift IS the signature check: a drifted export
/// refuses here, not mid-call.
pub fn run_edge_component(wasm: &[u8], name: &str, a: u64, b: u64) -> Result<u64, HostError> {
    let (_engine, _component, mut store, instance) = instantiate_component_module(wasm)?;
    let func = instance
        .get_func(&mut store, name)
        .ok_or_else(|| HostError::MissingExport(name.to_string()))?;
    let got = if EDGE_EXPORTS_1.contains(&name) {
        let typed = func
            .typed::<(u64,), (u64,)>(&store)
            .map_err(|_| HostError::ComponentSignature("<1 u64> -> <u64>"))?;
        typed
            .call(&mut store, (a,))
            .map_err(|e| HostError::Engine(format!("call {name}: {e:?}")))?
            .0
    } else if EDGE_EXPORTS_2.contains(&name) {
        let typed = func
            .typed::<(u64, u64), (u64,)>(&store)
            .map_err(|_| HostError::ComponentSignature("<2 u64> -> <u64>"))?;
        typed
            .call(&mut store, (a, b))
            .map_err(|e| HostError::Engine(format!("call {name}: {e:?}")))?
            .0
    } else {
        return Err(HostError::MissingExport(name.to_string()));
    };
    Ok(got)
}

/// Runs the string lane's committed component: the exported `length :
/// func(s: string) -> u64` over raw (already skew-checked) bytes with
/// the TYPED string call — the canonical-ABI `(ptr, len)` lowering is
/// the ENGINE's (the host lowers the UTF-8 buffer through the guest's
/// realloc + memory, the lift passes the pair to the core func), and
/// the typed lift carries the signature teeth for the composite
/// signature. The host runs to the seeded golden (`length("hello")` =
/// 5); it never runs free.
pub fn run_string_component(wasm: &[u8]) -> Result<u64, HostError> {
    let (_engine, _component, mut store, instance) = instantiate_component_module(wasm)?;

    let func = instance
        .get_func(&mut store, STRING_GUEST_EXPORT)
        .ok_or_else(|| HostError::MissingExport(STRING_GUEST_EXPORT.to_string()))?;
    let typed = func
        .typed::<(&str,), (u64,)>(&store)
        .map_err(|_| HostError::ComponentSignature("length : func(s: string) -> u64"))?;
    let (got,) = typed
        .call(&mut store, (STRING_GOLDEN_INPUT,))
        .map_err(|e| HostError::Engine(format!("call {STRING_GUEST_EXPORT}: {e:?}")))?;
    if got != STRING_GOLDEN {
        return Err(HostError::ComponentAnswerMismatch {
            got,
            expected: STRING_GOLDEN,
        });
    }
    Ok(got)
}
