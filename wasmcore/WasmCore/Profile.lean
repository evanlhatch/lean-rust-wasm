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

THE FEATURE UNIVERSE (the wasm-feature-detect discipline, landed):
the detector list IS the feature table — one `WasmFeature` ctor per
wasm-feature-detect export, one axis row per ctor (the `featureAxis`
total match: the deterministic-fragment status + the honest note +
the detector name). The teeth: a new wasm feature = ONE ctor + ONE
row, compile-enforced both ways (a ctor without an axis is a type
error; a ctor missing from `featureList` fails the
`featureList_covers` pin). The selection shim rides the SAME table:
`shimEmitter` renders `gen/wasm-feature-shim.mjs` (the dual-build
discipline's load-time face — detect simd128, pick the bundle),
byte-tied through the emitter spine like every artifact.

THE BYTE-TIE: the profile rides the duel emitter's TEXT lane
(`duelEmitter` — the profile file joins the manifest + the vectors in
the ONE regen `WasmCore.Duel.regen`), so `gates gen-check` byte-ties
the committed profile to this module exactly like every artifact; a
hand-edited profile.txt or a drifted engine config is a gate failure.
The shim rides its own text row (the `wasmgen` writer + the gen-check
gate share the ONE emitter), the same discipline.

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
module


public import Kit.Emit


@[expose] public section
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

/-! ## The feature universe (the wasm-feature-detect detector list AS DATA) -/

/-- ONE wasm feature: a ctor per detector in the wasm-feature-detect
    package's export list (23, the package's own naming). THE
    EXTENSION DISCIPLINE: a new wasm feature = ONE ctor here + ONE row
    in `featureAxis` (+ the `featureList` member the covers pin
    demands) — the compile error IS the checklist, the closed-universe
    rule at the feature face. -/
inductive WasmFeature where
  | bigInt | bulkMemory | exceptions | exceptionsFinal | extendedConst
  | gc | jsStringBuiltins | jspi | memory64 | multiMemory | multiValue
  | mutableGlobals | referenceTypes | relaxedSimd | saturatedFloatToInt
  | signExtensions | simd | streamingCompilation | tailCall | threads
  | typeReflection | typedFunctionReferences | wideArithmetic
deriving DecidableEq, Repr

/-- A feature's status in the deterministic fragment: `on` (the
    fragment admits it today), `off` (refused — the note names the
    gate that flips it), `conditional` (the note names the condition).
    A `conditional` without a named condition in its note is a lie
    this table refuses. -/
inductive FeatureStatus where
  | on | off | conditional
deriving DecidableEq, Repr

/-- ONE feature's axis row: the deterministic-fragment status (+ the
    honest note) and the DETECTION face — the wasm-feature-detect
    export the selection shim probes. -/
structure FeatureAxis where
  status : FeatureStatus
  detector : String
  note : String

/-- THE feature-axis table: one TOTAL match, one row per ctor. The
    statuses are the DETERMINISTIC fragment's (the engine faces and
    the dual-build bundles read them through the shim + the profile
    knobs); the notes carry the named gates. -/
def featureAxis : WasmFeature → FeatureAxis
  | .bigInt => ⟨.conditional, "bigInt",
      "the i64 ABI face: a guest i64 crosses the JS boundary AS a BigInt; the core ops are unaffected — conditional on the host surface, never the core"⟩
  | .bulkMemory => ⟨.off, "bulkMemory",
      "no bulk-memory ctor in the op table's closed set (memory.fill/copy); the fragment is integer-only structured control flow"⟩
  | .exceptions => ⟨.off, "exceptions",
      "the LEGACY exceptions proposal; superseded by exceptionsFinal — the detector name is carried for the detection face (wasm-feature-detect lists it), not as a direction"⟩
  | .exceptionsFinal => ⟨.off, "exceptionsFinal",
      "the NAMED next fragment: the exnref direction (throw/throw_ref/try_table; the OpTable's reserved rows). Off until that order lands — the axis is carried, the instructions are not"⟩
  | .extendedConst => ⟨.off, "extendedConst",
      "const-expression extension; the module model's constant surface is MVP-shaped"⟩
  | .gc => ⟨.off, "gc",
      "the NAMED next fragment: the GC direction (struct/array types, ref.cast/ref.test; the OpTable's reserved rows). Off until that order lands"⟩
  | .jsStringBuiltins => ⟨.off, "jsStringBuiltins",
      "the JS string builtins import face — the component boundary's concern (the Guest lane), not the core's"⟩
  | .jspi => ⟨.off, "jspi",
      "JS promise integration is HOST scheduling — nondeterministic by construction; the deterministic profile refuses it at the semantic level"⟩
  | .memory64 => ⟨.off, "memory64",
      "the deterministic profile's memory64 axis (theProfile.memory64) — one fact, two faces: the engine-config knob reads this row"⟩
  | .multiMemory => ⟨.off, "multiMemory",
      "the profile's multi-memory axis; the closed module universe carries ONE memory"⟩
  | .multiValue => ⟨.conditional, "multiValue",
      "the engines all ship it; the emitted fragment's blocks are single-result today — on only when the lowering starts emitting multi-value blocks (then the validator's flow face carries it explicitly)"⟩
  | .mutableGlobals => ⟨.on, "mutableGlobals",
      "MVP+ mutable globals: universally shipped, no determinism face; the module model's globals admit mutable"⟩
  | .referenceTypes => ⟨.off, "referenceTypes",
      "table.get/set + externref; callindirect's MVP table predates the proposal and carries none of it"⟩
  | .relaxedSimd => ⟨.off, "relaxedSimd",
      "NONDETERMINISTIC BY CONSTRUCTION: relaxed ops admit implementation-defined results — refused at the semantic level, not just the fragment level"⟩
  | .saturatedFloatToInt => ⟨.off, "saturatedFloatToInt",
      "floats are off (the WIT f64 is a TYPE; the core has zero float ops) — the conversion's determinism face is moot while its operands cannot occur"⟩
  | .signExtensions => ⟨.off, "signExtensions",
      "deterministic integer ops (i32.extend8_s/16_s + the i64 twins), but no ctor in the closed op set — off until an order needs them (then: ONE ctor + ONE row, R6)"⟩
  | .simd => ⟨.conditional, "simd",
      "THE DUAL-BUILD face: the Rust wasm faces build TWO bundles (RUSTFLAGS -C target-feature=+simd128 on/off) and the selection shim picks at load (the wasm-feature-detect discipline); the Lean-emitted guest fragment carries no v128 op today — conditional on the bundle, off in the deterministic core (theProfile.simd stays off: the engines execute the scalar core)"⟩
  | .streamingCompilation => ⟨.off, "streamingCompilation",
      "a HOST compilation-strategy detector, not a module feature; the detection face carries it (wasm-feature-detect lists it), the execution profile has no knob for it"⟩
  | .tailCall => ⟨.off, "tailCall",
      "return_call*: no ctor in the closed op set; the structured control flow's call/ret surface is MVP-shaped"⟩
  | .threads => ⟨.off, "threads",
      "shared memory + atomics are SHARED MUTABLE STATE — nondeterministic by construction; the deterministic profile's other semantic refusal"⟩
  | .typeReflection => ⟨.off, "typeReflection",
      "the GC proposal's rtts face; rides the gc row's gate (the same order lands both or neither)"⟩
  | .typedFunctionReferences => ⟨.off, "typedFunctionReferences",
      "the function-references proposal (call_ref, typed tables); rides the gc direction's gate"⟩
  | .wideArithmetic => ⟨.off, "wideArithmetic",
      "the profile's wide-arithmetic axis; i128 widening ops — no ctor in the closed op set"⟩

/-- The universe, as a value (the shim's fold source; the covers pin's
    surface). The ctor order is the wasm-feature-detect list's. -/
def featureList : List WasmFeature :=
  [ .bigInt, .bulkMemory, .exceptions, .exceptionsFinal, .extendedConst
  , .gc, .jsStringBuiltins, .jspi, .memory64, .multiMemory, .multiValue
  , .mutableGlobals, .referenceTypes, .relaxedSimd, .saturatedFloatToInt
  , .signExtensions, .simd, .streamingCompilation, .tailCall, .threads
  , .typeReflection, .typedFunctionReferences, .wideArithmetic ]

/-- The table: one row per ctor, the row FROM the function (no second
    copy of any fact — the note lives in `featureAxis` alone). -/
def featureTable : List (WasmFeature × FeatureAxis) :=
  featureList.map fun f => (f, featureAxis f)

/-- THE closed-universe tooth: every ctor appears in `featureList`
    EXACTLY once. The two faces close the extension both ways: a ctor
    WITHOUT an axis row is a type error (the total match), a ctor
    missing from `featureList` fails HERE (the silent under-report the
    match cannot see). -/
theorem featureList_covers (f : WasmFeature) :
    featureList.countP (· == f) = 1 := by
  cases f <;> decide

/-! ## The selection shim (the wasm-feature-detect discipline, OUR face) -/

/-- The status vocabulary (the shim's rendered spelling). -/
def statusRender : FeatureStatus → String
  | .on => "on"
  | .off => "off"
  | .conditional => "conditional"

/-- One feature row's JS line (the shim's table body — rendered from
    the axis, never a hand copy; the notes carry no double quote by
    construction — the JS-string escape would be a second encoding). -/
def featureJsRow : WasmFeature × FeatureAxis → String :=
  fun p => match p with
    | (_, a) =>
      s!"  \{ name: \"{a.detector}\", status: \"{statusRender a.status}\", note: \"{a.note}\" },"

/-- The simd128 probe: a 43-byte module whose single instruction is a
    v128.const (the 0xFD 0x0C prefix pair) — a validator with simd128
    accepts it, one without refuses it. OBSERVED (the build env's
    wasmtime): `wasmtime compile` accepts the probe with simd on and
    refuses it with `-W simd=no,relaxed-simd=no` (SIMD support is not
    enabled), while the same-shaped i32.const control is accepted both
    ways — the probe DISCRIMINATES simd128 and nothing else. -/
def simdProbe : List UInt8 :=
  [ 0, 97, 115, 109, 1, 0, 0, 0, 1, 5, 1, 96, 0, 1, 123, 3, 2, 1, 0
  , 10, 22, 1, 20, 0, 253, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  , 0, 0, 0, 11 ]

/-- THE selection shim's body (the driver prepends the 2-line
    GENERATED header — the `//` style): the feature table (rendered
    FROM `featureTable`) + the simd128 selection the dual-build
    contract needs BY DEFAULT. WASM SIMD HAS NO RUNTIME FEATURE
    DETECTION other than this probe shape — a validated probe module
    is the wasm-feature-detect discipline's core, and the two-bundle
    loader contract (`select`) is OUR face over it. -/
def shimBody : String :=
  "export const FEATURES = [\n" ++
  String.intercalate "\n" (featureTable.map featureJsRow) ++ "\n];\n" ++
  "\n" ++
  "// The simd128 probe (WasmCore.Profile.simdProbe — the observed\n" ++
  "// discriminator; the wasmtime both-ways evidence is the Lean\n" ++
  "// constant's note).\n" ++
  "const PROBE = new Uint8Array ([" ++
  String.intercalate "," (simdProbe.map toString) ++ "]);\n" ++
  "\n" ++
  "// True iff the surrounding engine supports simd128.\n" ++
  "export function detectSimd128 () {\n" ++
  "  return WebAssembly.validate (PROBE);\n" ++
  "}\n" ++
  "\n" ++
  "// THE dual-build contract: two bundles (the simd128 build and the\n" ++
  "// scalar build of the same crate), ONE selector. The loader calls\n" ++
  "// select () with both bundle loaders; the probe picks.\n" ++
  "export function select (loadSimd, loadScalar) {\n" ++
  "  return detectSimd128 () ? loadSimd () : loadScalar ();\n" ++
  "}\n"

/-- The shim's artifact path (the gen root — the scan's surface). -/
def shimPath : String := "gen/wasm-feature-shim.mjs"

/-- The shim's emitter row (pure over Unit — the feature table is
    module data; the witness emitters' shape). The byte-tie: the
    writer (`wasmgen`) and `gates gen-check` share THIS emitter —
    never a second encoding. -/
def shimEmitter : Kit.Emit.Emitter Unit where
  name := "wasm:feature-shim"
  style := .doubleSlash
  specSource := "WasmCore.Profile"
  outputs := [shimPath]
  run := fun _ => [{ path := shimPath, contents := shimBody }]
  reads := [`WasmCore.Profile]
  rev := "wasm-feature-shim-r1"

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

end -- public section

