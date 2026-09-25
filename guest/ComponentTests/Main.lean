/-
# ComponentTests.Main — the component lane's test battery

The end-to-end pin + the skew teeth + the mandatory negative controls
(15-patterns #5). The driver owns the unsafe IO (the importModules +
the LCNF re-run — the GuestTests.Main pattern); the suites consume the
computed results as data (the checks stay PURE — the IO face computes
once, the specs assert on data).

Suites:

1. `the component emission` — add64: LCNF → the lowered core module →
   the world-checked component binary (the BYTES pinned against the
   golden; the committed artifacts byte-tied — the render + the
   binary lanes both).
2. `the skew teeth` — the export/sig/non-scalar refusals fire with
   the named diagnostics (the skew discipline at generation).
-/

import Guest
import Guest.Component
import WasmCore
import TestingKit.Harness
import ComponentTests.Fixture
import ComponentTests.StringFixture
import ComponentTests.Axioms

open Guest WasmCore TestingKit ComponentTests.StringFixture

/-! ## The driver's IO face (the GuestTests.Main pattern) -/

/-- Import the fixture module in-process (`compiler.reuse` disabled —
    the emitter cannot lower reset/reuse joins). The search path: the
    root build dir FIRST (the gates' `loadPkgEnv` discipline). -/
unsafe def importFixture : IO (Except String Lean.Environment) := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.searchPathRef.set (".lake/build/lib/lean" :: (← Lean.searchPathRef.get))
  try
    let env ← Lean.importModules #[{ module := `ComponentTests.Fixture }]
      (opts := Guest.lcnfOptions) (loadExts := true)
    return .ok env
  catch e =>
    return .error s!"importModules failed: {toString e}"

/-! ## The world (the component boundary's contract side —
    `ComponentTests.Fixture.componentWorld`) -/

/-! ## The byte pin's face (the hex rendering) -/

/-- One byte's two hex digits. -/
def byteHex (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  let n := b.toNat
  String.singleton (digits.getD (n / 16) '0')
    ++ String.singleton (digits.getD (n % 16) '0')

/-- The hex rendering (the byte pin's readable face). -/
def toHex : List UInt8 → String :=
  fun bs => (bs.map (fun b => "0x" ++ byteHex b ++ " ")).foldl (· ++ ·) ""

/-! ## The computed face (the pipeline's product, once) -/

/-- The emitted product: the component bytes, the world text, and the
    committed artifacts' tie verdicts (the IO face's data). -/
structure Emitted where
  bytes : List UInt8
  witText : String
  binTie : CheckResult
  witTie : CheckResult
  deriving Inhabited

/-- The string emission's product: the same shape over the composite
    lane (the bytes, the world text, the committed ties). -/
structure StringEmitted where
  bytes : List UInt8
  witText : String
  binTie : CheckResult
  witTie : CheckResult
  deriving Inhabited

/-- The byte-tie face over a committed binary artifact (the
    sidecar's hash + the exact bytes — `Kit.Emit.tieBytes`). -/
def tieCommittedAt (wasmPath sidecarPath : String) (fresh : List UInt8) :
    IO CheckResult := do
  let committed ← IO.FS.readBinFile wasmPath
  let sidecar ← IO.FS.readFile sidecarPath
  return match Kit.Emit.tieBytes sidecar committed (ByteArray.mk fresh.toArray) with
    | .tied => .ok ()
    | .drifted why => .error s!"the committed component drifted: {why}"

/-- The byte-tie face over the committed binary artifact (the
    scalar slice's paths). -/
def tieCommitted (fresh : List UInt8) : IO CheckResult :=
  tieCommittedAt "gen/component-slice.wasm" "gen/component-slice.wasm.hdr" fresh

/-- The world text's tie face: the committed `.wit` body (the 2
    GENERATED header lines stripped) must be the fresh render. -/
def tieCommittedWitAt (witPath : String) (fresh : String) : IO CheckResult := do
  let committed ← IO.FS.readFile witPath
  let body := String.intercalate "\n" ((committed.splitOn "\n").drop 2)
  return if body == fresh then .ok ()
    else .error s!"the committed world text drifted: got «{body}»"

/-- The component emission's product (the committed artifact's
    source + its ties). -/
unsafe def computeEmitted : IO (Except String Emitted) := do
  match ← importFixture with
  | .error e => return .error e
  | .ok env =>
    match ← Guest.readDecl? env `add64 with
    | .error e => return .error s!"readDecl: {e}"
    | .ok d =>
      match Guest.lowerFunc d with
      | .error e => return .error s!"lower: {e.render}"
      | .ok m =>
        match Guest.Component.encodeComponent m componentWorld with
        | .error e => return .error s!"component: {e.render}"
        | .ok bs => do
            let witText := Wit.Render.worldFile "mandate:guest" componentWorld
            let binTie ← tieCommitted bs
            let witTie ← tieCommittedWitAt "gen/component-slice.wit" witText
            return .ok { bytes := bs, witText := witText
                       , binTie := binTie, witTie := witTie }

/-! ## The skew teeth (the pure faces — hand-built modules) -/

/-- A hand-built module: one type, one func, exported as `name` (the
    sig-drift / export-drift teeth's shape). -/
def oneFuncModule (name : String) (ps rs : List WasmCore.ValType) :
    WasmCore.Module :=
  { types := [⟨ps, rs⟩]
  , funcs := [⟨0, [], []⟩]
  , exports := [{ name := name, desc := .func 0 }] }

/-- The world's export the module LACKS (the export drift). -/
def exportDriftCheck :
    Except Guest.Component.ComponentError
      (List (Wit.Func × WasmCore.FuncType)) :=
  Guest.Component.check (oneFuncModule "other" [.i64, .i64] [.i64]) componentWorld

/-- The world's export with the WRONG core signature (the sig drift:
    the module's add64 takes no params). -/
def sigDriftCheck :
    Except Guest.Component.ComponentError
      (List (Wit.Func × WasmCore.FuncType)) :=
  Guest.Component.check (oneFuncModule "add64" [] [.i64]) componentWorld

/-- A world export whose string param the module does NOT flatten
    (the composite flattening's sig drift: the module's add64 carries
    (i64, i64) where the world's declared (u64, string) needs
    (i64, i32, i32) — the string's (ptr, len) pair). -/
def stringWorld : Wit.World :=
  { name := "guest"
  , imports := []
  , exports :=
      [.func { name := "add64"
             , params := [{ name := "a", ty := .atom .u64 }
                        , { name := "b", ty := .atom .string }]
             , result := some (.atom .u64) }] }

def stringSigDriftCheck :
    Except Guest.Component.ComponentError
      (List (Wit.Func × WasmCore.FuncType)) :=
  Guest.Component.check (oneFuncModule "add64" [.i64, .i64] [.i64]) stringWorld

/-- THE GOLDEN COMPONENT's bytes (the committed artifact's exact
    bytes — the byte-tie pin's face). The LCNF re-run is
    toolchain-pinned (leanprover/lean4:v4.33.0), so the compiled core
    module — and this byte list — is deterministic. The memory
    section (`05 03 01 00 01`) rides the lowering's growth (the
    boxed-Nat lane's module now carries the one-page linear memory
    the adapter face will consume); the component encoding itself is
    unchanged. -/
def goldenBytes : List UInt8 :=
  [0x00, 0x61, 0x73, 0x6D, 0x0D, 0x00, 0x01, 0x00,  -- the component header (layer 1)
   0x01, 0x41,  -- the core module section (the LCNF-compiled add64)
   0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, 0x01, 0x07, 0x01, 0x60,
   0x02, 0x7E, 0x7E, 0x01, 0x7E, 0x03, 0x02, 0x01, 0x00, 0x05, 0x03, 0x01,
   0x00, 0x01, 0x07, 0x09, 0x01, 0x05, 0x61, 0x64, 0x64, 0x36, 0x34, 0x00, 0x00, 0x0A, 0x1A, 0x01, 0x18,
   0x02, 0x01, 0x7E, 0x01, 0x7E, 0x02, 0x40, 0x20, 0x00, 0x20, 0x01, 0x7C,
   0x21, 0x03, 0x20, 0x03, 0x21, 0x02, 0x0C, 0x00, 0x0B, 0x20, 0x02, 0x0B,
   0x02, 0x04, 0x01, 0x00, 0x00, 0x00,  -- the core instance section
   0x06, 0x0B, 0x01, 0x00, 0x00, 0x01, 0x00, 0x05, 0x61, 0x64, 0x64, 0x36,
   0x34,  -- the alias section (the core func out of the instance)
   0x07, 0x0B, 0x01, 0x40, 0x02, 0x01, 0x61, 0x77, 0x01, 0x62, 0x77, 0x00,
   0x77,  -- the component func type (a: u64, b: u64) -> u64
   0x08, 0x06, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,  -- the canon lift
   0x0B, 0x0B, 0x01, 0x00, 0x05, 0x61, 0x64, 0x64, 0x36, 0x34, 0x01, 0x00,
   0x00]  -- the component export

/-! ## The suites -/

def emissionSpecs (e : Emitted) : List TestingKit.Spec :=
  [ Spec.ofList "the component emission: add64 through LCNF → core module → \
      the world-checked component binary (the bytes pinned)"
      (fun _ => do
        TestingKit.assertEq "the component's byte pin" (toHex e.bytes)
          (toHex goldenBytes)
        TestingKit.assert (e.witText.startsWith "package mandate:guest;\n")
          "the world text must carry the package line"
        TestingKit.assert (e.witText.contains "world guest {")
          "the world text must carry the world block"
        TestingKit.assert
          (e.witText.contains "export add64: func(a: u64, b: u64) -> u64;")
          "the world text must carry the add64 export")
      [ ("control: a tampered byte pin is caught (the header's last \
          byte doctored)",
         fun _ => TestingKit.assertEq "tampered" (toHex (e.bytes.take 8))
           (toHex [0x00, 0x61, 0x73, 0x6D, 0x0D, 0x00, 0x01, 0x01]))
      , ("control: the world text's export line is a LIE (wrong sig — \
          caught)",
         fun _ => TestingKit.assert
           (e.witText.contains "export add64: func(a: u64) -> u64;")
           "the control demands the wrong signature to be present")
      ]
      (h := by simp) 1 60
  , Spec.ofList "the committed artifact set byte-ties (the render face + \
      the binary face, both)"
      (fun _ => do
        TestingKit.assert (e.bytes.length > 8)
          "the emission must produce bytes"
        match e.binTie, e.witTie with
        | .ok (), .ok () => .ok ()
        | .error why, _ => .error s!"the binary tie failed: {why}"
        | _, .error why => .error s!"the render tie failed: {why}")
      [ ("control: the tie face is a LIE (the committed binary is \
          ABSENT — the control demands the tie to fail)",
         fun _ => TestingKit.assert (e.bytes.isEmpty)
           "the control demands empty bytes")
      , ("control: the world text is DOCTORED (the export name is \
          wrong — the control demands the doctored text to be the \
          fresh render)",
         fun _ =>
           TestingKit.assert
             (e.witText.contains "export addXX: func(a: u64) -> u64;")
             "the control demands the doctored export name")
      ]
      (h := by simp) 1 61
  ]

def skewSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the skew teeth: the component's shape is checked against \
      the world at generation"
      (fun _ => do
        -- the export drift: the world names an export the module lacks
        match exportDriftCheck with
        | .error (.exportDrift name) =>
            TestingKit.assertEq "the export drift names the func" name "add64"
        | .error e =>
            TestingKit.assert false s!"the export drift fired the WRONG \
              diagnostic: {e.render}"
        | .ok _ => TestingKit.assert false "the export drift did NOT refuse"
        -- the sig drift: the module's add64 carries the wrong signature
        match sigDriftCheck with
        | .error (.sigDrift name want got) => do
            TestingKit.assertEq "the sig drift names the func" name "add64"
            TestingKit.assertEq "the sig drift's want" want
              "(i64, i64) -> (i64)"
            TestingKit.assertEq "the sig drift's got" got "() -> (i64)"
        | .error e =>
            TestingKit.assert false s!"the sig drift fired the WRONG \
              diagnostic: {e.render}"
        | .ok _ => TestingKit.assert false "the sig drift did NOT refuse"
        -- the composite flattening: a string param's (ptr, len) pair
        -- is REQUIRED of the module (the sig drift names the pair)
        match stringSigDriftCheck with
        | .error (.sigDrift name want got) => do
            TestingKit.assertEq "the string sig drift names the func" name "add64"
            TestingKit.assertEq "the string sig drift's want (the (ptr,len) pair)"
              want "(i64, i32, i32) -> (i64)"
            TestingKit.assertEq "the string sig drift's got" got
              "(i64, i64) -> (i64)"
        | .error e =>
            TestingKit.assert false s!"the string sig drift fired the WRONG \
              diagnostic: {e.render}"
        | .ok _ => TestingKit.assert false "the string sig drift did NOT refuse"
        -- the adapter face: a string world needs the memory + realloc
        -- exports (each absence refuses with the named face)
        match Guest.Component.check
            ComponentTests.StringFixture.stringModuleNoMemory
            ComponentTests.StringFixture.lengthWorld with
        | .error (.adapterMissing name what) => do
            TestingKit.assertEq "the no-memory refusal names the func" name "length"
            TestingKit.assert (what.contains "memory")
              s!"the no-memory refusal names the face: {what}"
        | .error e =>
            TestingKit.assert false s!"the no-memory check fired the WRONG \
              diagnostic: {e.render}"
        | .ok _ => TestingKit.assert false "the no-memory module did NOT refuse"
        match Guest.Component.check
            ComponentTests.StringFixture.stringModuleNoRealloc
            ComponentTests.StringFixture.lengthWorld with
        | .error (.adapterMissing name what) => do
            TestingKit.assertEq "the no-realloc refusal names the func" name "length"
            TestingKit.assert (what.contains "realloc")
              s!"the no-realloc refusal names the face: {what}"
        | .error e =>
            TestingKit.assert false s!"the no-realloc check fired the WRONG \
              diagnostic: {e.render}"
        | .ok _ => TestingKit.assert false "the no-realloc module did NOT refuse"
        match Guest.Component.check
            ComponentTests.StringFixture.stringModuleBadRealloc
            ComponentTests.StringFixture.lengthWorld with
        | .error (.adapterMissing _ what) =>
            TestingKit.assert (what.contains "realloc")
              s!"the bad-realloc refusal names the face: {what}"
        | .error e =>
            TestingKit.assert false s!"the bad-realloc check fired the WRONG \
              diagnostic: {e.render}"
        | .ok _ => TestingKit.assert false "the bad-realloc module did NOT refuse")
      [ ("control: the GOOD pair refuses (wrong claim — it checks \
          clean, the control is caught)",
         fun _ => do
           let good :=
             Guest.Component.check (oneFuncModule "add64" [.i64, .i64] [.i64])
               componentWorld
           match good with
           | .error _ => .ok ()
           | .ok _ => TestingKit.assert false "the good pair CHECKS (the \
             control demanded a refusal)")
      , ("control: the sig-drift diagnostic carries the WRONG code \
          (GC9999 — the real code is GC2014; the control is caught)",
         fun _ =>
           let r := match sigDriftCheck with
             | .error e => e.render
             | .ok _ => ""
           TestingKit.assert (r.contains ("GC99" ++ "99"))
             s!"the sig drift's Diag must carry its real code: {r}")
      ]
      (h := by simp) 1 62
  ]

/-! ## The string emission's computed face (the composite lane) -/

/-- THE STRING GOLDEN COMPONENT's bytes: the hand-built adapter-face
    fixture through the composite emission — the canon lift with the
    memory + realloc options, the defined-type-free string func type
    (the string primitive 0x73), the adapter aliases. The bytes are
    double-pinned: wasm-tools VALIDATES the committed artifact, and
    wasmtime runs it through the typed string call (the host test's
    full-circle pin). -/
def stringGoldenBytes : List UInt8 :=
  [0x00, 0x61, 0x73, 0x6D, 0x0D, 0x00, 0x01, 0x00,  -- the component header (layer 1)
   0x01, 0x5F,  -- the core module section (the adapter face + the length func)
   0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, 0x01, 0x0F, 0x02, 0x60,
   0x04, 0x7F, 0x7F, 0x7F, 0x7F, 0x01, 0x7F, 0x60, 0x02, 0x7F, 0x7F, 0x01,
   0x7E, 0x03, 0x03, 0x02, 0x00, 0x01, 0x05, 0x03, 0x01, 0x00, 0x01, 0x07,
   0x2B, 0x03, 0x15, 0x63, 0x61, 0x6E, 0x6F, 0x6E, 0x69, 0x63, 0x61, 0x6C,
   0x5F, 0x61, 0x62, 0x69, 0x5F, 0x72, 0x65, 0x61, 0x6C, 0x6C, 0x6F, 0x63,
   0x00, 0x00, 0x06, 0x6C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x00, 0x01, 0x06,
   0x6D, 0x65, 0x6D, 0x6F, 0x72, 0x79, 0x02, 0x00, 0x0A, 0x0D, 0x02, 0x05,
   0x00, 0x41, 0x80, 0x08, 0x0B, 0x05, 0x00, 0x20, 0x01, 0xAD, 0x0B,
   0x02, 0x04, 0x01, 0x00, 0x00, 0x00,  -- the core instance section
   0x06, 0x31, 0x03, 0x00, 0x00, 0x01, 0x00, 0x06, 0x6C, 0x65, 0x6E, 0x67,
   0x74, 0x68, 0x00, 0x00, 0x01, 0x00, 0x15, 0x63, 0x61, 0x6E, 0x6F, 0x6E,
   0x69, 0x63, 0x61, 0x6C, 0x5F, 0x61, 0x62, 0x69, 0x5F, 0x72, 0x65, 0x61,
   0x6C, 0x6C, 0x6F, 0x63, 0x00, 0x02, 0x01, 0x00, 0x06, 0x6D, 0x65, 0x6D,
   0x6F, 0x72, 0x79,  -- the alias section (the func + the adapter aliases)
   0x07, 0x08, 0x01, 0x40, 0x01, 0x01, 0x73, 0x73, 0x00, 0x77,  -- the func type (s: string) -> u64
   0x08, 0x0A, 0x01, 0x00, 0x00, 0x00, 0x02, 0x03, 0x00, 0x04, 0x01, 0x00,  -- the canon lift + the memory/realloc options
   0x0B, 0x0C, 0x01, 0x00, 0x06, 0x6C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x01,
   0x00, 0x00]  -- the component export

/-- The string emission's product (the committed artifact's source +
    its ties; the emission is PURE — the hand-built fixture needs no
    LCNF re-run). -/
def computeStringEmitted : IO (Except String StringEmitted) := do
  match Guest.Component.encodeComponent
      ComponentTests.StringFixture.stringModule
      ComponentTests.StringFixture.lengthWorld with
  | .error e => return .error s!"string component: {e.render}"
  | .ok bs => do
      let witText := Wit.Render.worldFile "mandate:guest"
        ComponentTests.StringFixture.lengthWorld
      let binTie ← tieCommittedAt "gen/component-string-slice.wasm"
        "gen/component-string-slice.wasm.hdr" bs
      let witTie ← tieCommittedWitAt "gen/component-string-slice.wit" witText
      return .ok { bytes := bs, witText := witText
                 , binTie := binTie, witTie := witTie }

def stringSpecs (s : StringEmitted) : List TestingKit.Spec :=
  [ Spec.ofList "the string emission: the adapter-face fixture through \
      the composite canonical-ABI fold (the bytes pinned; the (ptr,len) \
      lift + the memory/realloc options)"
      (fun _ => do
        TestingKit.assertEq "the string component's byte pin" (toHex s.bytes)
          (toHex stringGoldenBytes)
        TestingKit.assert (s.witText.contains "export length: func(s: string) -> u64;")
          "the world text must carry the string export's contract line")
      [ ("control: a tampered byte pin is caught (the canon section's \
          option count doctored)",
         fun _ => TestingKit.assert
           (s.bytes.length > 180 && s.bytes.getD 177 0 == 0x02)
           "the control demands the canon options' count to be 2")
      , ("control: the world text's string contract is a LIE (wrong \
          result type — caught)",
         fun _ => TestingKit.assert
           (s.witText.contains "export length: func(s: string) -> string;")
           "the control demands the wrong result type to be present")
      ]
      (h := by simp) 1 63
  , Spec.ofList "the committed string slice byte-ties (the render face + \
      the binary face, both)"
      (fun _ => do
        TestingKit.assert (s.bytes.length > 8)
          "the emission must produce bytes"
        match s.binTie, s.witTie with
        | .ok (), .ok () => .ok ()
        | .error why, _ => .error s!"the binary tie failed: {why}"
        | _, .error why => .error s!"the render tie failed: {why}")
      [ ("control: the tie face is a LIE (the committed binary is \
          ABSENT — the control demands the tie to fail)",
         fun _ => TestingKit.assert (s.bytes.isEmpty)
           "the control demands empty bytes")
      , ("control: the world text is DOCTORED (the export name is \
          wrong — the control demands the doctored line to be the \
          fresh render)",
         fun _ =>
           TestingKit.assert
             (s.witText.contains "export lengthXX: func(s: string) -> u64;")
             "the control demands the doctored export name")
      ]
      (h := by simp) 1 64
  ]

/-! ## The driver -/

unsafe def main : IO UInt32 := do
  match ← computeEmitted with
  | .error e =>
      IO.eprintln s!"ComponentTests: PIPELINE FAILED — {e}"
      return 1
  | .ok e =>
    match ← computeStringEmitted with
    | .error es =>
        IO.eprintln s!"ComponentTests: STRING PIPELINE FAILED — {es}"
        return 1
    | .ok s =>
      TestingKit.mainOfSuites
        [ ("the component emission", emissionSpecs e)
        , ("the skew teeth", skewSpecs)
        , ("the string emission", stringSpecs s) ]
