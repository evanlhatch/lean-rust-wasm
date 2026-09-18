//! Version-skew FAIL-FAST: the host refuses to start against a guest
//! component whose export surface diverges from the host's committed
//! expectation — at startup, with both hashes and the first differing
//! `fn/arity` named, never as a wasm trap mid-request.
//!
//! DESIGN DECISION: the guest's surface is DERIVED FROM THE COMPONENT
//! TYPE (ground truth — readable via
//! [`Component::component_type`](wasmtime::component::Component::component_type)
//! before instantiation), not an embedded string. The string-embedding
//! channel (a custom section, or an exported const fn returning the
//! surface) was considered and rejected: WAT cannot express custom
//! sections (the section would ride a post-emit binary rewrite step),
//! and an embedded string is a CLAIM that can itself drift from the
//! real exports — the component type IS the export surface.
//!
//! The convention mirrors `Oracle.schemaSurface` (lean/wasm-backend):
//! the canonical string is `fn/arity`, comma-joined, in the oracle's
//! first-occurrence order; arity is the manifest FLAT-ARG count — a
//! record arg counts its fields, a variant arg counts 2 (discr +
//! payload), everything else counts 1. The schema hash is sha256 OF
//! THE STRING, computed consumer-side (Lean never hashes). The
//! contract covers the host's CALL surface (the 15 replayed fns);
//! extra guest exports (e.g. `watch-orders`) are out of contract — the
//! host never calls them and [`crate::valves::HostFault::MissingExport`]
//! guards the reverse direction.
//!
//! Hasher provenance: `sha2` here duplicates oracle-runner's
//! `schema_hash` (crates/oracle-runner/src/main.rs — the twin) in ~8
//! lines. Sharing was rejected: oracle-runner is a binary crate and
//! `forge` is the codegen tool — both are wrong dependency directions
//! for the host. Keep the two in lockstep (same input bytes, same hex
//! rendering); the triple-agreement test pins this hasher against a
//! coreutils-computed constant.

use wasmtime::component::Component;
use wasmtime::component::types::ComponentItem;
use wasmtime::{Engine, component::Type};

use crate::valves::HostFault;

/// The host's committed expectation for the demo component: byte-equal
/// to `Oracle.schemaSurface` (the `schema-skew` test's triple-agreement
/// pin: Lean's committed rendering in lean/wasm-backend/COVERAGE.md ==
/// this constant == the surface derived from the built
/// demo.component.wasm).
pub const EXPECTED_DEMO_SURFACE: &str = "double/1,is-big/1,adder/2,double-area/1,run-paps/1,total/3,pick/3,str-len-demo/1,greet/1,get-user/1,watch-counts/1,watch-users/1,user-valid/4,order-error-valid/2,user-complete/4,verify-witness/1";

/// sha256 of the surface string, lowercase hex (64 chars).
/// Twin: oracle-runner's `schema_hash` — see the module header.
pub fn schema_hash(surface: &str) -> String {
    use sha2::Digest;
    let digest = sha2::Sha256::digest(surface.as_bytes());
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

/// The flat-arg arity of one component-ABI type (the oracle's
/// convention): a record arg rides the boundary as its FIELD VALUES
/// FLAT, a variant arg as [discr, payload]; every leaf type is one slot.
fn flat_arity(ty: &Type) -> usize {
    match ty {
        Type::Record(r) => r.fields().len(),
        Type::Variant(_) => 2,
        _ => 1,
    }
}

/// Parse a canonical surface string (`fn/arity`, comma-joined) into
/// ordered pairs. Malformed entries are dropped — the surface strings
/// are machine-generated; a hand-edited expectation degrades to a
/// shorter contract, never a panic. `pub(crate)`: hostgen's contract
/// check parses the SAME expectation string with it (one parser per
/// format).
pub(crate) fn parse_surface(surface: &str) -> Vec<(String, usize)> {
    surface
        .split(',')
        .filter_map(|entry| {
            let (f, n) = entry.rsplit_once('/')?;
            Some((f.to_string(), n.parse::<usize>().ok()?))
        })
        .collect()
}

/// Render ordered pairs back to the canonical string.
fn render_surface(pairs: &[(String, usize)]) -> String {
    pairs
        .iter()
        .map(|(f, n)| format!("{f}/{n}"))
        .collect::<Vec<_>>()
        .join(",")
}

/// The guest's export surface, read from the component TYPE (pre-
/// instantiation — a skewed component is never run). One `(name, flat
/// arity)` per exported component function, in the component type's
/// declaration order; non-function exports (types, instances) are not
/// part of the call surface.
pub fn surface_of(engine: &Engine, component: &Component) -> Vec<(String, usize)> {
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

/// The refusal: both surfaces (with their schema hashes) and the first
/// difference in canonical order.
#[derive(Debug)]
pub struct SchemaSkew {
    /// The host's committed expectation (canonical string).
    expected: String,
    /// The guest's actual surface (its component type, declaration
    /// order).
    actual: String,
    /// The first differing `fn/arity` (or the first missing export).
    detail: String,
}

impl std::fmt::Display for SchemaSkew {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "schema skew: refusing to start — the guest component's export surface \
             diverges from the host's committed expectation\n  \
             expected sha256:{} ({})\n  \
             guest    sha256:{} ({})\n  \
             first difference: {}",
            schema_hash(&self.expected),
            self.expected,
            schema_hash(&self.actual),
            self.actual,
            self.detail,
        )
    }
}

impl std::error::Error for SchemaSkew {}

/// Compare the guest's component-type surface against the host's
/// expectation. Walks the EXPECTED surface in canonical order (the
/// oracle's first-occurrence order) and reports the first divergence;
/// extra guest exports are out of contract (see the module header).
/// On Ok, the guest's surface rendered over the contract IS the
/// expected string, so the two schema hashes are equal by construction.
pub fn verify_surface(
    engine: &Engine,
    component: &Component,
    expected: &str,
) -> Result<(), SchemaSkew> {
    let want = parse_surface(expected);
    let got = surface_of(engine, component);
    let skew = |detail: String| SchemaSkew {
        expected: expected.to_string(),
        actual: render_surface(&got),
        detail,
    };
    for (f, n) in &want {
        match got.iter().find(|(g, _)| g == f) {
            None => {
                return Err(skew(format!(
                    "guest missing export `{f}` (expected arity {n})"
                )));
            }
            Some((_, m)) if m != n => {
                return Err(skew(format!(
                    "`{f}` — expected arity {n}, guest arity {m}"
                )));
            }
            Some(_) => {}
        }
    }
    Ok(())
}

/// Startup failure: either the surface diverged (the fail-fast point
/// of this module) or the engine faulted during instantiation.
#[derive(Debug)]
pub enum StartError {
    /// The guest's export surface diverged from the expectation.
    Skew(SchemaSkew),
    /// Instantiation/linking faulted (the untyped path's fault).
    Engine(fast_observe::exn::Fault<HostFault>),
}

impl std::fmt::Display for StartError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Skew(s) => write!(f, "{s}"),
            Self::Engine(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for StartError {}

impl From<fast_observe::exn::Fault<HostFault>> for StartError {
    fn from(e: fast_observe::exn::Fault<HostFault>) -> Self {
        Self::Engine(e)
    }
}
