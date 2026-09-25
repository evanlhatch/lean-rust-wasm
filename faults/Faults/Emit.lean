/-
# Faults.Emit — the Rust face (fast-observe's `error!` macro syntax)

The fault registry's Rust rendering (notes/v3/12-construction.md §8: "never
hand-write error types — declare faults in the Lean registry"): the emitted
artifact is ONE `fast_observe::error!` block — the macro (fast-observe's
OWN proc-macro, `fast-observe-macros/src/error_macro.rs` is the attribute
grammar) generates the enum + per-variant payload structs + the Display/
Error wiring + the `Coded` impl + the per-variant `ENTRY` consts + the
enum's `ENTRIES` (the registry ENTRIES — the wasm composition path) + the
`Fault<E>` conversions.

The mapping, one source two faces:
- the allocated E-code maps onto `#[code = "…"]` VERBATIM (the persisted
  registry's spelling — never a hand constant);
- the Lean `Category` maps onto fast-observe's `ErrorCategory`
  (fatal/content/transient/invariant — `.unsupported` is rejected at
  registration, fast-observe has no such category), so the category↔policy
  axis is aligned BY CONSTRUCTION (fast-observe's `policy()`:
  Content→FixInput, Transient→Retry, Invariant→Poison, Fatal→Abort);
- the advice is the spec's field (`#[code = "…", advice = "…"]`).

THE GENERATED SHAPE (the macro's grammar, verified against the crate):
struct variants emit as NEWTYPE variants wrapping a generated payload
struct (Debug only — the macro derives nothing else on the payloads, and
`#[derive]` on a variant is not expressible in the grammar); an EMPTY
payload emits as a UNIT variant; the enum's derives are the macro's
auto-Debug. The consumers' value pins therefore ride `code()`/`category()`
— the registry's projection — not payload equality.

NIGHTLY (the honest cost, surfaced — wave-30 C1): the generated
`Error::provide` (code/category through `&dyn Error`) needs
`error_generic_member_access` — the Rust lane pins nightly
(`crates/rust-toolchain.toml`). VERIFIED: the devenv profile's cargo IS
nightly (1.100.0-nightly, no rustup in the build env — the toolchain file
is the floor for rustup environments), so the HAND-SHAPED `Coded` fallback
(hypothesis: the unsealed-trait face may work on stable; the registry's
provide-discipline stays nightly-gated) is NOT needed — named here only so
the disposition is on the record.

THE SEAM (named, not built): the observer-transparency theorem (U2 — the
instrumented host refines the plain host) is a SEPARATE later item; the
causal-tree crossing (a guest fault as a host `Frame`,
`FrameKind::Remote`) is design-faults-observability §2.3's W10.3.

The generated crate's dependency is `fast-observe = { path =
"../../../fast-observe", default-features = false }` — the honest LOCAL
shape (the crate is ours, unbumped 0.x; the path pin is the semver-drift
tooth, design-faults R1). `default-features = false`: libraries do not
enable fastrace — the BINARY enables it (fast-observe's
library-level-tracing rule).

Names ride the ONE mangler (Kit.Mangle): variants `Kit.pascal`, fields
`Kit.rustIdent` — the emitter's law is the post-mangle uniqueness (the
collision scan's emptiness), so a colliding fault name cannot emit silently
(and under the macro the variant name names the payload struct too — one
name, two spellings of the same uniqueness fact).

Core-only (imports Kit + SchemaCore's fold — the cone rule; schemacore is
READ-ONLY here).
Five questions (notes/v3/01-core.md):
- root: Crossing — the allocated registry read into the Rust target.
- carrier grade: the emitter's law field (the mangled-name nodup) + the
  byte-tie (the artifact is the spelling pin — Alloc's coverage note).
- spine reading: THE Interpretation stage (01 §5): one registry, the
  generated artifact, the Kit.Emit driver's header + hash.
- ladder rung: total string folds; the goldens are the tests' pins.
- gate row: gen-check (the byte-tie over crates/mandate-faults/src/lib.rs)
  + ownership (the declared output) + the FaultsTests goldens + the audit's
  fault-coverage row (the observability-inheritance rule, 09 §5).
-/

import Kit.Emit
import Kit.Mangle
import SchemaCore.Fold
import Faults.Item
import Faults.Alloc

namespace Faults

/-! ## the renderers -/

/-- A Rust string literal's spelling (backslash, quote, newline escaped). -/
def rustStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\"
    else if c == '"' then "\\\""
    else if c == '\n' then "\\n"
    else c.toString) ++ "\""

/-- The generated Rust variant's name (the ONE mangler's pascal). Under
    the macro this name names BOTH the enum variant and the generated
    payload struct (struct variants) — one mangled name, one uniqueness
    fact. -/
def variantName (m : FaultItem) : String := Kit.pascal m.name

/-- The generated Rust field's spelling (`name: Type`, the ONE mangler +
    the ONE type fold). -/
def fieldDecl (f : String × SchemaCore.Ty) : String :=
  Kit.rustIdent f.1 ++ ": " ++ SchemaCore.tyRustPrim f.2

/-- One fault → its enum variant's text (the attributes + the fields; the
    macro's attribute grammar: `#[error("…")]` is REQUIRED on every
    variant; the `#[code = "…", category = …, advice = "…"]` tail carries
    the registry's projection — code verbatim, category as fast-observe's
    ErrorCategory ident, advice the spec's field). The empty payload is a
    UNIT variant (the macro keeps units — no payload struct). -/
def renderVariant (p : FaultItem × Nat) : String :=
  let m := p.1
  let fields := m.payload.map fieldDecl
  let variant :=
    match fields with
    | [] => variantName m
    | fs => variantName m ++ " { " ++ String.intercalate ", " fs ++ " }"
  String.intercalate "\n"
    ["    #[error(" ++ rustStr m.display ++ ")]", 
     "    #[code = " ++ rustStr (ecodeSpelling p.2) ++ ", category = "
       ++ m.category.rustName ++ ", advice = " ++ rustStr m.advice ++ "]",
     "    " ++ variant ++ ","]

/-- The generated module's body (the crate's `lib.rs`; the 2-line GENERATED
    header is the DRIVER's prepend, never part of this render). -/
def renderLib (modes : List (FaultItem × Nat)) : String :=
  let doc : List String :=
    ["//! mandate-faults — the GENERATED fault surface (the faults lane's",
     "//! Rust face, fast-observe's `error!` macro syntax).",
     "//!",
     "//! One variant per registered `@[fault]` row (Faults.Spec — the",
     "//! registry is the SSOT); the E-codes allocated from the persisted",
     "//! registry (notes/code-registry.txt — `code()` reports the spelling;",
     "//! never hand-set, never position-derived) map onto `#[code = \"…\"]`",
     "//! VERBATIM; the Lean category maps onto fast-observe's ErrorCategory",
     "//! (fatal/content/transient/invariant — the category↔policy axis is",
     "//! aligned by construction: ONE registry, two faces); the advice is",
     "//! the spec's field. NEVER hand-edit this file: the regen is",
     "//! `lake exe faultsgen`, the byte-tie `gates gen-check` — a hand edit",
     "//! fails the gate (12 §8's discipline: the error surface is declared,",
     "//! not written).",
     "//!",
     "//! SHAPE (the macro's grammar — fast-observe-macros/src/error_macro.rs):",
     "//! struct variants emit as NEWTYPE variants wrapping a generated",
     "//! payload struct (Debug only — the macro derives nothing else on the",
     "//! payloads, and `#[derive]` on a variant is not expressible), an",
     "//! empty payload emits as a UNIT variant; the enum's derives are the",
     "//! macro's auto-Debug. The consumers' value pins therefore ride",
     "//! code()/category() — the registry's projection — not payload",
     "//! equality.",
     "//!",
     "//! NIGHTLY (the honest cost, surfaced — wave-30 C1): the generated",
     "//! `Error::provide` (code/category through `&dyn Error`) needs",
     "//! `error_generic_member_access` — the Rust lane pins nightly",
     "//! (crates/rust-toolchain.toml; the devenv profile's pinned nightly",
     "//! is the actual toolchain — no rustup in the build env).",
     "//!",
     "//! THE SEAM (named, not built): the observer-transparency theorem",
     "//! (U2 — the instrumented host refines the plain host) is a separate",
     "//! later item; the causal-tree crossing (a guest fault as a host",
     "//! Frame, FrameKind::Remote) is design-faults-observability §2.3's",
     "//! W10.3.",
     ""]
  let feature : List String :=
    ["#![feature(error_generic_member_access)]",
     ""]
  let reexport : List String :=
    ["/// The error taxonomy's policy axis (fast-observe's — the Lean",
     "/// registry's Category is the ONE source this spelling renders; the",
     "/// policy lives on it: Content→FixInput, Transient→Retry,",
     "/// Invariant→Poison, Fatal→Abort).",
     "pub use fast_observe::ErrorCategory;",
     ""]
  let enum : List String :=
    (["fast_observe::error! {",
      "    /// The generated typed-error enum (the declared faults — the",
      "    /// registry's rows; Debug is the macro's own derive — the",
      "    /// consumers' value pins ride code()/category(), the registry's",
      "    /// projection, not payload equality).",
      "    pub enum FaultError {"]
      ++ modes.map renderVariant
      ++ ["    }", "}", ""])
  let methods : List String :=
    (["impl FaultError {",
      "    /// The retry policy (the category's method — never a second",
      "    /// table): `transient` is the ONLY retryable category — a",
      "    /// `content` error means unchanged input fails again, an",
      "    /// `invariant` error means the engine is wrong.",
      "    pub fn retryable(&self) -> bool {",
      "        matches!(self.category().policy(), fast_observe::Policy::Retry)",
      "    }",
      "}",
      "",
      "/// The composition root's registration (the wasm discipline: no",
      "/// linker sections there — `register_statics` populates the STATIC",
      "/// registry; on native the linkme slice already carries the entries",
      "/// and this is harmless). Call once at startup, before any",
      "/// `lookup_error`.",
      "pub fn init_host() {",
      "    fast_observe::register_statics(FaultError::ENTRIES);",
      "}"])
  String.intercalate "\n" (doc ++ feature ++ reexport ++ enum ++ methods) ++ "\n"

/-! ## the emitter row -/

/-- The faults lane's emitter: the ONE writer of
    `crates/mandate-faults/src/lib.rs`. The law: the mangled variant names
    are pairwise distinct (Kit.Mangle's post-mangle uniqueness — the
    collision scan's emptiness IS the nodup, `collDiags_eq_nil_iff`). -/
def faultsEmitter : Kit.Emit.Emitter (List (FaultItem × Nat)) where
  name := "faults-rust"
  style := .doubleSlash
  specSource := "Faults.Spec"
  outputs := ["crates/mandate-faults/src/lib.rs"]
  run modes :=
    [{ path := "crates/mandate-faults/src/lib.rs"
       contents := renderLib modes }]
  law := some fun modes => (modes.map (fun p => variantName p.1)).Nodup

end Faults
