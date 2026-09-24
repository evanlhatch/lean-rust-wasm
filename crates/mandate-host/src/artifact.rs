//! The artifact-loading half of the skew check: the host runs the
//! artifact the toolchain emitted — proven by RECOMPUTING the content
//! hash, not by trusting the sidecar.
//!
//! The twin (`Observed` vs `Inferred`): `Kit.Emit.bytesHash` is the
//! Lean authority — the LCG fold (TestingKit.lcg, Knuth 64) seeded at
//! `1442695040888963407`, one step per byte. `bytes_hash` below is the
//! consumer-side twin, byte-for-byte the same recurrence in wrapping
//! `u64` arithmetic; the pin test proves it against the committed
//! sidecar's value. Sharing the code was impossible (Lean is the
//! owner; Rust consumes), so the twin is kept lockstep by the test.
//!
//! This mirrors the kit's own `tieBytes` verdict from the consumer
//! side: `drifted "sidecar content hash does not name the fresh
//! bytes' hash"` becomes [`crate::HostError::ContentHashMismatch`].

use std::path::Path;

use crate::HostError;

/// The LCG seed (TestingKit.lcg's stream seed — Kit.Emit.bytesHash's
/// fold base).
const LCG_SEED: u64 = 1442695040888963407;
/// The LCG multiplier (Knuth 64 — the ONE recurrence; never a
/// hand-copied table).
const LCG_MULT: u64 = 6364136223846793005;
/// The LCG increment (same constant as the seed — Knuth 64's shape).
const LCG_INC: u64 = 1442695040888963407;

/// The binary content hash — the consumer-side twin of
/// `Kit.Emit.bytesHash`: the bytes folded through the LCG, one step
/// per byte (`h' = lcg(h + b)`, wrapping u64).
///
/// Hashes establish IDENTITY, not correctness (notes/v3/03 §5): this
/// pins which bytes the toolchain emitted; the module's validity was
/// established at generation (the validator runs in wasmgen) and again
/// at compile time (wasmtime refuses invalid modules).
pub fn bytes_hash(bs: &[u8]) -> u64 {
    bs.iter().fold(LCG_SEED, |h, &b| {
        (h.wrapping_add(b as u64))
            .wrapping_mul(LCG_MULT)
            .wrapping_add(LCG_INC)
    })
}

/// Extracts the `content hash <n>` field from a sidecar's text (the
/// 2nd GENERATED line). `None` = malformed — the caller refuses.
/// `pub(crate)`: the duel runner re-uses it per vector (the duel's
/// own skew discipline rides the SAME parser — never a second one).
pub(crate) fn sidecar_hash(sidecar: &str) -> Option<u64> {
    sidecar
        .lines()
        .find_map(|l| l.split("content hash ").nth(1))
        .and_then(|rest| rest.split([' ', '|']).next())
        .and_then(|num| num.trim().parse().ok())
}

/// The checked artifact set for the wasm slice: the module's bytes
/// (hash-tied to their sidecar) + the WIT surface (presence-checked).
#[derive(Debug, Clone)]
pub struct GenSlice {
    /// The verified module bytes — safe to hand to the engine.
    pub wasm: Vec<u8>,
}

/// Loads the committed slice's artifact set from `gen_dir`:
///
/// 1. `wasm-slice.wasm` — read.
/// 2. `wasm-slice.wasm.hdr` — read; its `content hash <n>` must equal
///    `bytes_hash` of the module's bytes (the hash tie). A mismatch or
///    a malformed sidecar is a refusal, never a warning.
/// 3. `schema-slice.wit` — must exist and carry the GENERATED header
///    naming the `<org>:slice` package (presence-level: the surface's
///    own byte-tie stays Lean-gate-owned; the host consumes it as the
///    completeness witness of the artifact set; the org component is
///    the renamer's business, not the host's).
pub fn load_gen_slice(gen_dir: &Path) -> Result<GenSlice, HostError> {
    // 1. The module bytes.
    let wasm_path = gen_dir.join("wasm-slice.wasm");
    let wasm = std::fs::read(&wasm_path)
        .map_err(|source| HostError::Io { what: "wasm-slice.wasm", source })?;

    // 2. The sidecar — the hash tie.
    let sidecar_path = gen_dir.join("wasm-slice.wasm.hdr");
    let sidecar = std::fs::read_to_string(&sidecar_path)
        .map_err(|source| HostError::Io { what: "wasm-slice.wasm.hdr", source })?;
    let declared = sidecar_hash(&sidecar).ok_or(HostError::SidecarMalformed(
        "no `content hash <n>` field in the GENERATED header",
    ))?;
    let computed = bytes_hash(&wasm);
    if computed != declared {
        return Err(HostError::ContentHashMismatch { declared, computed });
    }

    // 3. The WIT surface — the artifact set's completeness witness.
    let wit_path = gen_dir.join("schema-slice.wit");
    let wit = std::fs::read_to_string(&wit_path)
        .map_err(|source| HostError::Io { what: "schema-slice.wit", source })?;
    if !wit.lines().next().is_some_and(|l| l.starts_with("// GENERATED")) {
        return Err(HostError::Incomplete("schema-slice.wit: not a GENERATED artifact"));
    }
    if !wit.lines().any(|l| l.starts_with("package ") && l.contains(":slice;")) {
        return Err(HostError::Incomplete(
            "schema-slice.wit: no `package <org>:slice;` declaration",
        ));
    }

    Ok(GenSlice { wasm })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repo_gen_dir;

    /// THE PIN: the twin's hash over the committed bytes equals the
    /// value the committed sidecar declares. If either side moves
    /// without the other, this names the drift.
    #[test]
    fn bytes_hash_pin_matches_committed_sidecar() {
        let committed = repo_gen_dir();
        let wasm =
            std::fs::read(committed.join("wasm-slice.wasm")).expect("the committed module");
        let sidecar = std::fs::read_to_string(committed.join("wasm-slice.wasm.hdr"))
            .expect("the committed sidecar");
        let declared = sidecar_hash(&sidecar).expect("the sidecar names a content hash");
        assert_eq!(bytes_hash(&wasm), declared);
    }

    /// The fold's known-answer check (independent of the committed
    /// artifacts): the empty tape stays at the seed; each byte advances
    /// exactly one LCG step from wherever the state stands.
    #[test]
    fn bytes_hash_known_answers() {
        let lcg = |s: u64| s.wrapping_mul(LCG_MULT).wrapping_add(LCG_INC);
        assert_eq!(bytes_hash(&[]), LCG_SEED);
        assert_eq!(bytes_hash(&[0]), lcg(LCG_SEED));
        assert_eq!(bytes_hash(&[0, 0]), lcg(lcg(LCG_SEED)));
    }

    /// The sidecar parser's negative controls: no field, a non-numeric
    /// field, a trailing-token field — all malformed; a normal header
    /// parses.
    #[test]
    fn sidecar_hash_parses_and_refuses() {
        let good = "// GENERATED by wasmgen (lean-4.33.0) at - — DO NOT EDIT\n\
                    // spec unknown | WasmCore.Module | 3 item(s) | content hash \
                    10175063987543006018 | regen: just gen; drift fails CI\n";
        assert_eq!(sidecar_hash(good), Some(10175063987543006018));
        assert_eq!(sidecar_hash("// no field here\n"), None);
        assert_eq!(sidecar_hash("// content hash not-a-number\n"), None);
        assert_eq!(sidecar_hash(""), None);
    }
}
