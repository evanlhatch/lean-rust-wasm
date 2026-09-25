/-
# FaultsTests — the faults lane's test exe (TestingKit the whole way)

Per the slice: positive pins + the MANDATORY negative controls (15-patterns
#5). Suites (the checks stay PURE — the driver computes the live faces once):

1. THE ALLOCATION — the persisted-registry discipline at the lane: a
   declared fault's code is its row's, a missing row is the FT0001
   refusal, a code collision the FT0004 tooth (the negative controls
   demand the refusals — a wrongly-passing allocation proves nothing).
2. THE SPELLING — the derived E-code spellings (`FT` + the padded
   allocation; the coverage-tooth note: derived, never spelled in Lean —
   the pin here + the artifact byte-tie are the countermeasures).
3. THE EMITTER — the generated Rust face: the golden body over the
   fixture (fast-observe's `error!` face + the discipline methods), the
   law (the mangled names' post-mangle uniqueness), the payload types
   through the ONE fold.
4. THE LIVE ARTIFACT — the runtime replay + the persisted allocation →
   the committed `crates/mandate-faults/src/lib.rs` byte-ties (THE
   artifact pin: the generated file's spellings are the allocation's).

The build-time half (the replay pins + the curated-failure controls) is
FaultsTests.Reg — the lane-substrate's discipline (a module's initializers
run at import; the pins ride the build).
-/

import TestingKit.Harness
import TestingKit.Golden
import Faults
import FaultsTests.Reg
import FaultsTests.Axioms

open Faults Kit TestingKit

-- The generated-file record needs a default for the driver's head!.
deriving instance Inhabited for Kit.Emit.GeneratedFile

/-! ## Fixtures -/

/-- The persisted-registry fixture: the four declared rows' allocations
    (the REAL rows' numbers at the fixture's writing — the gate replays
    them; a re-allocation moves the LIVE pin, never this pure fixture). -/
def regFixture : Kit.CodeRegistry :=
  [ ⟨"KB0001", 1, false⟩
  , ⟨"fault.content_hash_mismatch", 133, false⟩
  , ⟨"fault.journal_corrupt", 134, false⟩
  , ⟨"fault.lifecycle_illegal_transition", 135, false⟩
  , ⟨"fault.wasm_trap", 136, false⟩ ]

/-- The fixture faults: two of the declared rows (the live replay pins the
    whole set; the pure fixture pins the DISCIPLINE). -/
def faultFixture : List FaultItem :=
  [ { name := "content_hash_mismatch"
      display := "mismatch: {declared} vs {computed}"
      category := .content
      advice := "rebuild"
      payload := [("declared", .u64), ("computed", .u64)] }
  , { name := "wasm_trap"
      display := "wasm trap: {detail}"
      category := .fatal
      advice := "inspect the module"
      payload := [("detail", .string)] } ]

/-- A near-miss fault name (one edit from a registered row — the
    did-you-mean's fixture). -/
def unallocatedFault : FaultItem :=
  { name := "wasm_traps"
    display := "unallocated"
    category := .content
    advice := "no"
    payload := [] }

/-- The fixture's rendered body (the allocation + the render, once). -/
def fixtureBody : String :=
  match Faults.allocAll regFixture faultFixture with
  | .ok ps => Faults.renderLib ps
  | .error e => s!"ALLOCATION REFUSED: {e}"

/-! ## THE GOLDEN PIN -/

/-- THE GOLDEN PIN: the fixture's rendered lib.rs, byte-for-byte. The
    generated file's committed body must equal this modulo nothing (the
    fixture codes are the LIVE rows' — a re-allocation re-pins here AND
    regenerates the artifact, the same commit). -/
def goldenFaultLib : String :=
"//! mandate-faults — the GENERATED fault surface (the faults lane's
//! Rust face, fast-observe's `error!` macro syntax).
//!
//! One variant per registered `@[fault]` row (Faults.Spec — the
//! registry is the SSOT); the E-codes allocated from the persisted
//! registry (notes/code-registry.txt — `code()` reports the spelling;
//! never hand-set, never position-derived) map onto `#[code = \"…\"]`
//! VERBATIM; the Lean category maps onto fast-observe's ErrorCategory
//! (fatal/content/transient/invariant — the category↔policy axis is
//! aligned by construction: ONE registry, two faces); the advice is
//! the spec's field. NEVER hand-edit this file: the regen is
//! `lake exe faultsgen`, the byte-tie `gates gen-check` — a hand edit
//! fails the gate (12 §8's discipline: the error surface is declared,
//! not written).
//!
//! SHAPE (the macro's grammar — fast-observe-macros/src/error_macro.rs):
//! struct variants emit as NEWTYPE variants wrapping a generated
//! payload struct (Debug only — the macro derives nothing else on the
//! payloads, and `#[derive]` on a variant is not expressible), an
//! empty payload emits as a UNIT variant; the enum's derives are the
//! macro's auto-Debug. The consumers' value pins therefore ride
//! code()/category() — the registry's projection — not payload
//! equality.
//!
//! NIGHTLY (the honest cost, surfaced — wave-30 C1): the generated
//! `Error::provide` (code/category through `&dyn Error`) needs
//! `error_generic_member_access` — the Rust lane pins nightly
//! (crates/rust-toolchain.toml; the devenv profile's pinned nightly
//! is the actual toolchain — no rustup in the build env).
//!
//! THE SEAM (named, not built): the observer-transparency theorem
//! (U2 — the instrumented host refines the plain host) is a separate
//! later item; the causal-tree crossing (a guest fault as a host
//! Frame, FrameKind::Remote) is design-faults-observability §2.3's
//! W10.3.

#![feature(error_generic_member_access)]

/// The error taxonomy's policy axis (fast-observe's — the Lean
/// registry's Category is the ONE source this spelling renders; the
/// policy lives on it: Content→FixInput, Transient→Retry,
/// Invariant→Poison, Fatal→Abort).
pub use fast_observe::ErrorCategory;

fast_observe::error! {
    /// The generated typed-error enum (the declared faults — the
    /// registry's rows; Debug is the macro's own derive — the
    /// consumers' value pins ride code()/category(), the registry's
    /// projection, not payload equality).
    pub enum FaultError {
    #[error(\"mismatch: {declared} vs {computed}\")]
    #[code = \"FT0133\", category = Content, advice = \"rebuild\"]
    ContentHashMismatch { declared: u64, computed: u64 },
    #[error(\"wasm trap: {detail}\")]
    #[code = \"FT0136\", category = Fatal, advice = \"inspect the module\"]
    WasmTrap { detail: String },
    }
}

impl FaultError {
    /// The retry policy (the category's method — never a second
    /// table): `transient` is the ONLY retryable category — a
    /// `content` error means unchanged input fails again, an
    /// `invariant` error means the engine is wrong.
    pub fn retryable(&self) -> bool {
        matches!(self.category().policy(), fast_observe::Policy::Retry)
    }
}

/// The composition root's registration (the wasm discipline: no
/// linker sections there — `register_statics` populates the STATIC
/// registry; on native the linkme slice already carries the entries
/// and this is harmless). Call once at startup, before any
/// `lookup_error`.
pub fn init_host() {
    fast_observe::register_statics(FaultError::ENTRIES);
}
"

/-! ## The suites (every check's arguments on ONE line — the do-layout
     discipline; the multi-line application inside a match arm's do-block
     leaks the continuation out of the arm) -/

def allocSpecs : List Spec :=
  [ Spec.ofList "the allocation: each fault's code is its persisted row's \
      (never position-derived — the fixture's codes are non-adjacent on \
      purpose)"
      (fun _ => do
        match Faults.allocAll regFixture faultFixture with
        | .error e => TestingKit.assert false s!"allocation refused: {e}"
        | .ok ps =>
            TestingKit.assertEq "the allocated codes" (ps.map (·.2)) [133, 136]
            TestingKit.assertEq "the registration order preserved"
              (ps.map (·.1.name)) ["content_hash_mismatch", "wasm_trap"])
      [ ("control: the codes are the POSITIONS (a LIE — caught)",
         fun _ => do
           match Faults.allocAll regFixture faultFixture with
           | .ok ps =>
               TestingKit.assert (ps.map (·.2) == [0, 1])
                 "the control demands the positions as the codes"
           | .error _ => pure ())
      , ("control: the registration order inverts (a LIE — caught)",
         fun _ => do
           match Faults.allocAll regFixture faultFixture with
           | .ok ps =>
               TestingKit.assert
                 (ps.map (fun p => p.1.name)
                   == ["wasm_trap", "content_hash_mismatch"])
                 "the control demands the inverted order"
           | .error _ => pure ())
      ]
      1 80
  , Spec.ofList "the FT0001 tooth: a fault with no persisted row REFUSES — \
      the closed-world Diag (the did-you-mean over the registry's fault \
      rows)"
      (fun _ => do
        match Faults.allocOne regFixture unallocatedFault with
        | .ok _ => TestingKit.assert false "an unallocated fault must refuse"
        | .error e =>
            TestingKit.assert (e.contains "[FT0001]")
              s!"the refusal must be the FT0001 Diag, got: {e}"
            TestingKit.assert (e.contains "fault.wasm_traps")
              "the refusal names the missing row key"
            TestingKit.assert (e.contains "did you mean")
              "the closed-world curation carries the did-you-mean \
                (the near-miss row's suggestion)")
      [ ("control: the unallocated fault ALLOCATES (a LIE — caught)",
         fun _ => do
           match Faults.allocOne regFixture unallocatedFault with
           | .ok _ => pure ()
           | .error _ =>
               TestingKit.assert false
                 "the control demands the missing row to allocate")
      , ("control: the refusal is UNGOVERNED (a LIE — caught)",
         fun _ => do
           match Faults.allocOne regFixture unallocatedFault with
           | .ok _ => pure ()
           | .error e =>
               TestingKit.assert (!(e.contains "[FT0001]"))
                 "the control demands the refusal to lose its code")
      ]
      1 81
  , Spec.ofList "the FT0004 collision tooth: two faults on one code \
      REFUSE (the mount's duplicate refusal makes distinct keys, so the \
      collision tooth is the decided belt-and-braces)"
      (fun _ => do
        -- the sabotaged rows: two distinct fault keys pointing at ONE code
        let sabotaged : Kit.CodeRegistry :=
          [ ⟨"fault.a", 5, false⟩, ⟨"fault.b", 5, false⟩ ]
        let items : List FaultItem :=
          [ { name := "a", display := "", category := .content
              advice := "", payload := [] }
          , { name := "b", display := "", category := .content
              advice := "", payload := [] } ]
        match Faults.allocAllCheck sabotaged items with
        | .ok _ => TestingKit.assert false "a code collision must refuse"
        | .error e =>
            TestingKit.assert (e.contains "[FT0004]")
              s!"the refusal must be the FT0004 Diag, got: {e}")
      [ ("control: the colliding codes PASS (a LIE — caught)",
         fun _ => do
           let sabotaged : Kit.CodeRegistry :=
             [ ⟨"fault.a", 5, false⟩, ⟨"fault.b", 5, false⟩ ]
           let items : List FaultItem :=
             [ { name := "a", display := "", category := .content
                 advice := "", payload := [] }
             , { name := "b", display := "", category := .content
                 advice := "", payload := [] } ]
           match Faults.allocAllCheck sabotaged items with
           | .ok _ => pure ()
           | .error _ =>
               TestingKit.assert false
                 "the control demands the collision to pass")
      , ("control: the CLEAN allocation refuses (a LIE — caught)",
         fun _ => do
           match Faults.allocAllCheck regFixture faultFixture with
           | .ok _ =>
               TestingKit.assert false
                 "the control demands the clean allocation to refuse"
           | .error _ => pure ())
      ]
      1 82
  ]

def spellingSpecs : List Spec :=
  [ Spec.ofList "the spelling: the E-code's spelling is DERIVED from the \
      allocation (FT + the 4-digit pad) — never spelled, never hand-set"
      (fun _ => do
        -- the pin rides the CHAR LIST: the coverage tooth scans string
        -- literals, and a spelled code here would refuse (the digits are
        -- COMPUTED, never spelled — Alloc's coverage note); the SPELLED
        -- pins are the generated artifact's, byte-tied by gen-check.
        TestingKit.assert ((Faults.pad4 133).toList == ['0', '1', '3', '3'])
          "the pad must be the 4-digit zero-padded decimal"
        TestingKit.assert
          ((Faults.ecodeSpelling 133).toList == ['F', 'T', '0', '1', '3', '3'])
          "the spelling must be FT + the padded allocation"
        TestingKit.assertEq "the key" (Faults.ecodeKey "wasm_trap")
          "fault.wasm_trap"
        TestingKit.assert
          (([133, 134, 135, 136].map Faults.ecodeSpelling).Nodup)
          "distinct codes must spell distinctly")
      [ ("control: the spelling is the CONSTANT (a LIE — caught)",
         fun _ =>
           -- both spellings DERIVED (never spelled — the coverage tooth's
           -- discipline): the lie is a spelling that ignores its code
           TestingKit.assert
             (Faults.ecodeSpelling 133 == Faults.ecodeSpelling 134)
             "the control demands two codes to spell alike")
      , ("control: the key DROPS the namespace (a LIE — caught)",
         fun _ =>
           TestingKit.assert (Faults.ecodeKey "wasm_trap" == "wasm_trap")
             "the control demands the raw name as the key")
      ]
      1 83
  ]

def emitSpecs : List Spec :=
  [ Spec.ofList "the emitter's law: the mangled variant names are pairwise \
      distinct (the post-mangle uniqueness — the bridge, not a hope)"
      (fun _ =>
        TestingKit.assert
          (Kit.mangleWf Kit.pascal
            (faultFixture.map (fun p => Kit.pascal p.name)))
          "the fixture's mangled names must be unique")
      [ ("control: the colliding names are UNIQUE (a LIE — caught)",
         fun _ =>
           -- two DIFFERENT names mangling to one variant (pascal's
           -- non-injectivity: camel humps + separators)
           TestingKit.assert
             (Kit.mangleWf Kit.pascal
               (([{ name := "a_b", display := "", category := .content,
                    advice := "", payload := [] },
                  { name := "aB", display := "", category := .content,
                    advice := "", payload := [] }] : List FaultItem).map
                 (fun p => Kit.pascal p.name)))
             "the control demands the collision to pass the law")
      , ("control: the fixture's names COLLIDE (a LIE — caught)",
         fun _ =>
           TestingKit.assert
             (!Kit.mangleWf Kit.pascal
               (faultFixture.map (fun p => Kit.pascal p.name)))
             "the control demands the fixture to collide")
      ]
      1 84
  , Spec.ofList "the generated Rust face: the golden body over the \
      fixture (fast-observe's error! face + the discipline methods, the \
      payload types through the ONE fold)"
      (fun _ =>
        TestingKit.assertEq "the golden body" fixtureBody goldenFaultLib)
      [ ("control: the render DROPS a variant (a LIE — caught)",
         fun _ => TestingKit.assert (!fixtureBody.contains "WasmTrap")
           "the control demands the second variant to vanish")
      , ("control: the render LOSES the code discipline (a LIE — caught)",
         fun _ => TestingKit.assert (!fixtureBody.contains "#[code =")
           "the control demands the #[code] attributes to vanish (the \
             macro's code() is generated from them)")
      ]
      1 85
  ]

/-! ## The live artifact face (the driver computes once) -/

/-- The live pin's product: the runtime replay + the persisted allocation +
    the committed artifact's tie verdict. -/
structure LivePin where
  modes : List (FaultItem × Nat)
  tie : Bool
  tieWhy : String
  deriving Inhabited

/-- The runtime half: `Faults.regen` (the ONE copy the writer + the gate
    run) + the committed artifact's TEXT TIE (Kit.Emit.tieText — the body
    byte-exact, the header naming the fresh body's hash). -/
unsafe def computeLivePin : IO (Except String LivePin) := do
  match ← Faults.regen with
  | .error e => return .error e
  | .ok modes =>
    match Faults.faultsEmitter.run modes with
    | [fresh] =>
        let path : System.FilePath := fresh.path
        if ← path.pathExists then do
          let committed ← IO.FS.readFile path
          match Kit.Emit.tieText committed fresh.contents with
          | .tied => return .ok { modes := modes, tie := true, tieWhy := "" }
          | .drifted why =>
              return .ok { modes := modes, tie := false, tieWhy := why }
        else
          return .ok { modes := modes, tie := false,
                       tieWhy := s!"{fresh.path} absent — run `lake exe faultsgen`" }
    | _ => return .error "the emitter declared more than its one output"

def liveSpecs (pin : LivePin) : List Spec :=
  [ Spec.ofList "the live artifact: the replayed registry, allocated from \
      the PERSISTED registry, byte-ties the committed generated file"
      (fun _ => do
        TestingKit.assertEq "the live registry (the four declared rows)"
          (pin.modes.map (·.1.name))
          ["content_hash_mismatch", "journal_corrupt",
           "lifecycle_illegal_transition", "wasm_trap"]
        TestingKit.assertEq "the live codes (the persisted rows')"
          (pin.modes.map (·.2)) [133, 134, 135, 136]
        TestingKit.assert pin.tie
          s!"the committed artifact drifted: {pin.tieWhy}")
      [ ("control: the committed artifact DRIFTS (a LIE — caught)",
         fun _ => TestingKit.assert (!pin.tie)
           "the control demands the byte-tie to fail")
      , ("control: the live codes are the POSITIONS (a LIE — caught)",
         fun _ =>
           TestingKit.assert (pin.modes.map (·.2) == [0, 1, 2, 3])
             "the control demands the positions as the codes")
      ]
      (h := by simp) 1 86
  ]

unsafe def main : IO UInt32 := do
  match ← computeLivePin with
  | .error e =>
    IO.eprintln s!"FaultsTests: LIVE PIN FAILED — {e}"
    return 1
  | .ok pin =>
    TestingKit.mainOfSuites
      [ ("the allocation", allocSpecs)
      , ("the spelling", spellingSpecs)
      , ("the emitter", emitSpecs)
      , ("the live artifact", liveSpecs pin) ]
