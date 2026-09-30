/-
# WasmCore.Profile — the deterministic profile AS DATA

THE ONE PROFILE TABLE (notes/design-wave-30.md D1 — "ONE profile table
all engines share; never two hand-synced configs"): the deterministic
execution profile as a Lean VALUE, the honest home for the wasm feature
flags WITH the discipline's teeth. Every engine that executes the
toolchain's modules — the wasmtime host (`mandate-host`'s engine
config) and the wasmi standalone runtime (`mandate-rt`'s engine
config) — reads ITS config axes from the RENDERED rows of this one
value (the committed `gen/wasm-duel/profile.txt` through the duel
emitter); a Rust config hand-set instead of parsed is the drift class
this module exists to close.

The profile's face (mined from legacy guestlang-rt — the DISCIPLINE,
not the code): the Lean spec's compiled fragment is integer-only
structured control flow, so the deterministic profile is:

- `consume-fuel` ON — the deterministic resource bound (wasmi's stable
  fuel metering; wasmtime's fuel);
- `floats` OFF — the f64 in the WIT world is a TYPE; the core module
  has zero f64 instructions. A spec bug that starts emitting outside
  the fragment = a LOAD refusal in the engines that can refuse it
  (wasmi's `floats(false)`), never silent nondeterminism;
- `memory64` / `multi-memory` / `wide-arithmetic` /
  `custom-page-sizes` OFF — the closed module universe's memory axes
  (the validator's fragment, mirrored at every engine);
- `simd` OFF — the FEATURE axis: wasmi's simd is a compile-time crate
  feature, NOT a config knob, so its absence is the dependency edge
  (the Cargo.toml — check the lockfile, not the config). The profile
  CARRIES the axis so the flag set stays closed; an engine whose
  applier cannot honor a demanded axis refuses loudly.
- `compilation` PINNED to `lazy-translation` — wasmi 2.0's
  deterministic compilation mode (`Lazy` may diverge across
  implementations; wasmtime's AOT compiler is the duel's other leg,
  its mode knob has no `lazy-translation` spelling — the applier
  names the pin and documents the face).

THE BYTE-TIE: the profile rides the duel emitter's TEXT lane
(`duelEmitter` — the profile file joins the manifest + the vectors in
the ONE regen `WasmCore.Duel.regen`), so `gates gen-check` byte-ties
the committed profile to this module exactly like every artifact; a
hand-edited profile.txt or a drifted engine config is a gate failure.

The five questions (notes/v3/01-core.md):
- root: Crossing — the Lean profile value vs every engine's runtime
  config, coupled through the committed rendered artifact.
- carrier grade: none new — the profile is data over Bool + a closed
  three-ctor mode universe.
- spine reading: the artifact spine — the duel emitter's text lane;
  the Rust readers re-derive nothing.
- ladder rung: rung 1 — pure data + total folds; nothing here is
  proved, everything is consumed (the engines' appliers + the tests).
- gate row: `gates gen-check`'s duel rows (the profile file is the
  emitter's declared output). WasmCoreTests pins the profile's rows.
-/

import Kit.Emit

namespace WasmCore.Profile

/-! ## The compilation mode (the closed three-ctor universe) -/

/-- The interpreter's compilation mode (the wasmi 2.0 face): `eager`
    compiles every function at instantiation; `lazy` compiles at first
    call (may diverge across implementations); `lazyTranslation`
    compiles at first call but TRANSLATES the whole module up front —
    wasmi's deterministic mode, the profile's pin. -/
inductive CompilationMode where
  | eager
  | lazy
  | lazyTranslation
deriving DecidableEq, Repr

/-- The manifest-row spelling (the Rust readers' vocabulary). -/
def CompilationMode.render : CompilationMode → String
  | .eager => "eager"
  | .lazy => "lazy"
  | .lazyTranslation => "lazy-translation"

/-! ## The profile -/

/-- The deterministic profile: the fuel knob, the pinned compilation
    mode, and the CLOSED feature-flag set. The flags are the engine
    CONFIG axes (`off` = the engine refuses the feature at load); the
    simd axis is the crate-FEATURE axis (see the module header). -/
structure DeterministicProfile where
  /-- The deterministic resource bound (wasmi's stable fuel metering,
      wasmtime's fuel) — ON in the deterministic profile. -/
  consumeFuel : Bool
  /-- The pinned compilation mode — `lazyTranslation` in the
      deterministic profile (the deterministic face, see above). -/
  compilation : CompilationMode
  /-- Float instructions allowed? OFF (the fragment is integer-only;
      the WIT f64 is a TYPE, the core module has zero f64 ops). -/
  floats : Bool
  /-- The memory64 proposal allowed? OFF. -/
  memory64 : Bool
  /-- Multiple memories allowed? OFF. -/
  multiMemory : Bool
  /-- The wide-arithmetic proposal allowed? OFF. -/
  wideArithmetic : Bool
  /-- Custom page sizes allowed? OFF. -/
  customPageSizes : Bool
  /-- The simd FEATURE axis (the crate feature, not a config knob) —
      OFF: the wasmi dependency edge carries it; an applier that
      cannot honor a demanded axis refuses loudly. -/
  simd : Bool
deriving DecidableEq, Repr

/-- THE deterministic profile (D1's one table — the duel's and both
    engines' shared config source). -/
def theProfile : DeterministicProfile where
  consumeFuel := true
  compilation := .lazyTranslation
  floats := false
  memory64 := false
  multiMemory := false
  wideArithmetic := false
  customPageSizes := false
  simd := false

/-! ## The rendered rows (the ONE textual face the engines read) -/

/-- A profile row: `key` + the tab + `value` (the manifest's row
    shape — the text convention the Rust readers parse). -/
def ProfileRow := String × String

/-- The profile's rows, in field order (the ONE rendering — both
    engines parse THIS, never a second encoding). `on`/`off` is the
    Bool vocabulary; the mode renders its own spelling. -/
def rows (p : DeterministicProfile) : List ProfileRow :=
  [ ("consume-fuel", boolOf p.consumeFuel)
  , ("compilation", p.compilation.render)
  , ("floats", boolOf p.floats)
  , ("memory64", boolOf p.memory64)
  , ("multi-memory", boolOf p.multiMemory)
  , ("wide-arithmetic", boolOf p.wideArithmetic)
  , ("custom-page-sizes", boolOf p.customPageSizes)
  , ("simd", boolOf p.simd) ]
where
  /-- The Bool vocabulary (the shared helper — one copy). -/
  boolOf : Bool → String := fun b => if b then "on" else "off"

/-- THE deterministic profile's rendered rows (the value the duel
    emitter writes into `gen/wasm-duel/profile.txt`). -/
def theRows : List ProfileRow := rows theProfile

/-- The profile file's body (the generator row + the rows; the driver
    prepends the 2-line GENERATED header — the manifest's shape). -/
def fileBody : String :=
  "generator\tWasmCore.Profile\n" ++
  String.intercalate "\n" (theRows.map fun (k, v) => k ++ "\t" ++ v) ++ "\n"

end WasmCore.Profile
