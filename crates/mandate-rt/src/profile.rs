//! The deterministic profile's READER face (WasmCore.Profile's Rust
//! consumer; notes/design-wave-30.md D1).
//!
//! THE ONE PROFILE TABLE: the profile is a Lean VALUE
//! (`WasmCore.Profile.theProfile`) whose rendered rows are committed
//! through the duel emitter's text lane — `gen/wasm-duel/profile.txt`
//! (byte-tied by `gates gen-check`). THIS module parses those rows
//! into the typed [`DeterministicProfile`]; BOTH engines' configs ride
//! the parsed value (the wasmi applier here, the wasmtime applier in
//! mandate-host's engine lane) — never two hand-synced configs.
//!
//! THE PARSER'S DISCIPLINE: strict, total over the failure surface —
//! an unknown KEY, an unknown VALUE, a duplicate row, a missing axis,
//! a bad generator row is a typed refusal ([`ProfileError`]), never a
//! silent skip. The committed universe is the spec of record; a reader
//! that guessed would launder a profile drift into engine configs.

use std::fmt;
use std::path::Path;

/// The profile file's path inside the gen directory (the duel lane's
/// convention — the file lives BESIDE the vectors it governs).
pub const PROFILE_FILE: &str = "wasm-duel/profile.txt";

/// The profile's compilation mode (WasmCore.Profile.CompilationMode's
/// face — the closed three-ctor universe).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompilationMode {
    /// Compiled eagerly at instantiation.
    Eager,
    /// Translated lazily on first use (may diverge across
    /// implementations — the mode the profile does NOT pin).
    Lazy,
    /// Validated eagerly, translated lazily on first use — wasmi's
    /// deterministic mode, THE profile's pin.
    LazyTranslation,
}

impl CompilationMode {
    /// The manifest-row vocabulary (WasmCore.Profile's rendering —
    /// the ONE spelling each).
    fn of_row(s: &str) -> Option<CompilationMode> {
        match s {
            "eager" => Some(CompilationMode::Eager),
            "lazy" => Some(CompilationMode::Lazy),
            "lazy-translation" => Some(CompilationMode::LazyTranslation),
            _ => None,
        }
    }
}

/// The parsed deterministic profile (WasmCore.Profile.DeterministicProfile's
/// face): the fuel knob, the pinned compilation mode, and the CLOSED
/// feature-flag set. Adding a Lean axis adds a field HERE — and every
/// applier's match on the struct refuses to compile until it names it
/// (the never-two-hand-synced-configs discipline's compile tooth).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeterministicProfile {
    /// The deterministic resource bound — ON.
    pub consume_fuel: bool,
    /// The pinned compilation mode — `lazy-translation`.
    pub compilation: CompilationMode,
    /// Float instructions allowed? OFF (the fragment is integer-only).
    pub floats: bool,
    /// The memory64 proposal allowed? OFF.
    pub memory64: bool,
    /// Multiple memories allowed? OFF.
    pub multi_memory: bool,
    /// The wide-arithmetic proposal allowed? OFF.
    pub wide_arithmetic: bool,
    /// Custom page sizes allowed? OFF.
    pub custom_page_sizes: bool,
    /// The simd FEATURE axis (the crate feature, not a config knob) —
    /// OFF: carried so the flag set stays closed; an applier that
    /// cannot honor a demanded axis refuses loudly.
    pub simd: bool,
}

/// The profile reader's typed refusal surface (no panics — 12 §8).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProfileError {
    /// The generator provenance row is absent or wrong (a file from
    /// another lane is not a profile).
    Generator(String),
    /// A row's key is not one of the profile's eight axes.
    UnknownKey(String),
    /// A row's value is not in the axis's vocabulary.
    UnknownValue { key: String, value: String },
    /// A row's key appears twice (contradictory config).
    DuplicateKey(String),
    /// The file is not `key\tvalue` rows.
    MalformedRow(String),
    /// A required axis is absent — a partial profile is not a profile.
    MissingKey(String),
}

impl fmt::Display for ProfileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProfileError::Generator(got) => write!(
                f,
                "profile: bad/missing generator row (expected `generator\tWasmCore.Profile`, got {got:?})"
            ),
            ProfileError::UnknownKey(k) => write!(f, "profile: unknown axis {k:?}"),
            ProfileError::UnknownValue { key, value } => {
                write!(f, "profile: axis {key:?}: unknown value {value:?}")
            }
            ProfileError::DuplicateKey(k) => write!(f, "profile: duplicate axis {k:?}"),
            ProfileError::MalformedRow(r) => write!(f, "profile: malformed row {r:?}"),
            ProfileError::MissingKey(k) => write!(f, "profile: missing axis {k:?}"),
        }
    }
}

impl std::error::Error for ProfileError {}

/// The profile file's parser: the generator row, then the eight
/// `key\tvalue` axes — strict (every failure typed, nothing skipped).
pub fn parse_profile(text: &str) -> Result<DeterministicProfile, ProfileError> {
    // The GENERATED header lines are the driver's; the BODY starts at
    // the generator row. Skip `#` comment lines, split on tabs.
    let mut gen_seen = false;
    let mut rows: Vec<(&str, &str)> = Vec::new();
    for line in text.lines() {
        if line.starts_with('#') {
            continue;
        }
        let Some((k, v)) = line.split_once('\t') else {
            if line.is_empty() {
                continue;
            }
            return Err(ProfileError::MalformedRow(line.to_string()));
        };
        if k == "generator" {
            if gen_seen || v != "WasmCore.Profile" {
                return Err(ProfileError::Generator(line.to_string()));
            }
            gen_seen = true;
        } else {
            rows.push((k, v));
        }
    }
    if !gen_seen {
        return Err(ProfileError::Generator(String::new()));
    }
    // Every axis exactly once, every value in its vocabulary.
    let mut seen: Vec<&str> = Vec::new();
    let mut consume_fuel = None;
    let mut compilation = None;
    let mut floats = None;
    let mut memory64 = None;
    let mut multi_memory = None;
    let mut wide_arithmetic = None;
    let mut custom_page_sizes = None;
    let mut simd = None;
    for (k, v) in rows {
        let slot: &mut Option<bool> = match k {
            "compilation" => {
                let m = CompilationMode::of_row(v).ok_or_else(|| ProfileError::UnknownValue {
                    key: k.to_string(),
                    value: v.to_string(),
                })?;
                if compilation.replace(m).is_some() {
                    return Err(ProfileError::DuplicateKey(k.to_string()));
                }
                continue;
            }
            "consume-fuel" => &mut consume_fuel,
            "floats" => &mut floats,
            "memory64" => &mut memory64,
            "multi-memory" => &mut multi_memory,
            "wide-arithmetic" => &mut wide_arithmetic,
            "custom-page-sizes" => &mut custom_page_sizes,
            "simd" => &mut simd,
            other => return Err(ProfileError::UnknownKey(other.to_string())),
        };
        let b = match v {
            "on" => true,
            "off" => false,
            _ => {
                return Err(ProfileError::UnknownValue {
                    key: k.to_string(),
                    value: v.to_string(),
                });
            }
        };
        if slot.replace(b).is_some() {
            return Err(ProfileError::DuplicateKey(k.to_string()));
        }
        seen.push(k);
    }
    // The strict completeness face: eight axes, all present.
    let _ = seen;
    Ok(DeterministicProfile {
        consume_fuel: consume_fuel
            .ok_or_else(|| ProfileError::MissingKey("consume-fuel".into()))?,
        compilation: compilation.ok_or_else(|| ProfileError::MissingKey("compilation".into()))?,
        floats: floats.ok_or_else(|| ProfileError::MissingKey("floats".into()))?,
        memory64: memory64.ok_or_else(|| ProfileError::MissingKey("memory64".into()))?,
        multi_memory: multi_memory
            .ok_or_else(|| ProfileError::MissingKey("multi-memory".into()))?,
        wide_arithmetic: wide_arithmetic
            .ok_or_else(|| ProfileError::MissingKey("wide-arithmetic".into()))?,
        custom_page_sizes: custom_page_sizes
            .ok_or_else(|| ProfileError::MissingKey("custom-page-sizes".into()))?,
        simd: simd.ok_or_else(|| ProfileError::MissingKey("simd".into()))?,
    })
}

/// Reads + parses the committed profile from the repo's gen directory
/// (the consumer contract: the Lean-emitted artifact is the authority;
/// the reader re-derives nothing).
pub fn load_profile(gen_dir: &Path) -> Result<DeterministicProfile, ProfileError> {
    let text = std::fs::read_to_string(gen_dir.join(PROFILE_FILE)).map_err(|e| {
        ProfileError::MalformedRow(format!(
            "{} unreadable: {e}",
            gen_dir.join(PROFILE_FILE).display()
        ))
    })?;
    parse_profile(&text)
}

#[cfg(test)]
mod tests {
    use super::*;

    const GOOD: &str = "generator\tWasmCore.Profile\n\
        consume-fuel\ton\n\
        compilation\tlazy-translation\n\
        floats\toff\n\
        memory64\toff\n\
        multi-memory\toff\n\
        wide-arithmetic\toff\n\
        custom-page-sizes\toff\n\
        simd\toff\n";

    /// The committed file's shape parses to the deterministic profile.
    #[test]
    fn parses_the_deterministic_profile() {
        let p = parse_profile(GOOD).expect("the profile parses");
        assert!(p.consume_fuel);
        assert_eq!(p.compilation, CompilationMode::LazyTranslation);
        assert!(!p.floats);
        assert!(!p.memory64);
        assert!(!p.multi_memory);
        assert!(!p.wide_arithmetic);
        assert!(!p.custom_page_sizes);
        assert!(!p.simd);
    }

    /// THE NEGATIVE CONTROLS: the strict parser refuses — typed, never
    /// a guess — an unknown axis, an unknown value, a missing axis, a
    /// duplicate row, a bad generator row.
    #[test]
    fn refuses_malformed_profiles() {
        assert_eq!(
            parse_profile(&GOOD.replace("simd\toff", "spectre\toff")).unwrap_err(),
            ProfileError::UnknownKey("spectre".into())
        );
        assert!(matches!(
            parse_profile(&GOOD.replace("compilation\tlazy-translation", "compilation\tturbo")),
            Err(ProfileError::UnknownValue { .. })
        ));
        assert!(matches!(
            parse_profile(&GOOD.replace("floats\toff\n", "")),
            Err(ProfileError::MissingKey(_))
        ));
        let dup = GOOD.replace("floats\toff", "floats\toff\nfloats\toff");
        assert_eq!(
            parse_profile(&dup).unwrap_err(),
            ProfileError::DuplicateKey("floats".into())
        );
        assert!(matches!(
            parse_profile(&GOOD.replace("generator\tWasmCore.Profile", "generator\tSomeoneElse")),
            Err(ProfileError::Generator(_))
        ));
        // A profile with a flipped axis parses — the VALUE carries it
        // (the reader is honest; the ENGINES decide what to do — the
        // wasmi applier refuses an axis it cannot honor).
        let flipped = GOOD.replace("floats\toff", "floats\ton");
        assert!(parse_profile(&flipped).unwrap().floats);
    }
}
