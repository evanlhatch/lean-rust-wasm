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
3. `the manifest discipline` (ComponentTests.Gen) — the compile set
   + the world DERIVE from the registered surface (the `@[guest]`
   marks), the growth teeth + the port pin (the derived world IS the
   hand-declared SSOT).
-/

import Guest
import Guest.Component
import Guest.Layout
import WasmCore
import TestingKit.Golden
import TestingKit.Harness
import ComponentTests.Fixture
import ComponentTests.StringFixture
import ComponentTests.EdgeFixture
import ComponentTests.WitFixture
import ComponentTests.ImportFixture
import ComponentTests.AsyncFixture
import ComponentTests.StreamFixture
import ComponentTests.Axioms
import ComponentTests.Gen

open Guest WasmCore TestingKit ComponentTests.StringFixture
open ComponentTests.EdgeFixture (edgeCore edgeWorld edgeSpec execAt pyAt resultOf)
open ComponentTests.WitFixture (gateRun gateVerdict)

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

/-- The world text's tie face: the committed `.wit` body (the ONE
    strip — `TestingKit.Golden.bodyOf`: exactly the leading 2-line
    GENERATED header block is exempt, keyed on the header's own
    markers; a headerless committed text ties WHOLE, never silently
    mis-stripped by a blind line count) must be the fresh render. -/
def tieCommittedWitAt (witPath : String) (fresh : String) : IO CheckResult := do
  let committed ← IO.FS.readFile witPath
  let body := TestingKit.Golden.bodyOf committed
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
      match Guest.compile [d] with
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

/-! ## The edgepython component lane's computed face (the SECOND FRONTEND through the SAME emission) -/

/-- The edge emission's product: the same shape over the edgepython
    lane (the bytes, the world text, the committed ties). The pipeline
    is PURE (`EdgeFixture.edgeCore` — the frontend's product, no LCNF
    re-run). -/
structure EdgeEmitted where
  bytes : List UInt8
  witText : String
  binTie : CheckResult
  witTie : CheckResult
  deriving Inhabited

/-- The edge emission's product (the committed artifact's source + its
    ties). -/
def computeEdgeEmitted : IO (Except String EdgeEmitted) := do
  match Guest.Component.encodeComponent edgeSpec.core edgeSpec.world with
  | .error e => return .error s!"edge component: {e.render}"
  | .ok bs => do
      let witText := Wit.Render.worldFile "mandate:guest" edgeWorld
      let binTie ← tieCommittedAt "gen/component-edge-slice.wasm"
        "gen/component-edge-slice.wasm.hdr" bs
      let witTie ← tieCommittedWitAt "gen/component-edge-slice.wit" witText
      return .ok { bytes := bs, witText := witText
                 , binTie := binTie, witTie := witTie }

/-- The edge world's nine export contract lines (the render's exact
    shape — `Wit.Render.exportItem`). -/
def edgeExportLines : List String :=
  [ "export double: func(x: u64) -> u64;"
  , "export adder: func(a: u64, b: u64) -> u64;"
  , "export dec1: func(n: u64) -> u64;"
  , "export loop-sum: func(n: u64) -> u64;"
  , "export if-max: func(a: u64, b: u64) -> u64;"
  , "export ops-mix: func(a: u64, b: u64) -> u64;"
  , "export tup-second: func(a: u64, b: u64) -> u64;"
  , "export list-sum: func(n: u64) -> u64;"
  , "export list-head: func(n: u64) -> u64;" ]

/-- THE THREE-WAY PARITY's point table: (name, args, the literal the
    three faces must agree on). The legs: `pyAt` (the legacy Python
    oracle) ≡ `execAt` (the Lean executor over the SAME core module
    the component embeds) ≡ the wasmtime execution of the committed
    component (the Rust host's goldens — the same literals,
    `mandate-host`'s edge lane). -/
def parityPoints : List (String × List Int × Int) :=
  [ ("double", [21], 42), ("adder", [40, 2], 42), ("dec1", [5], 4)
  , ("loop_sum", [10], 45), ("loop_sum", [0], 0)
  , ("if_max", [3, 9], 9), ("if_max", [9, 3], 9)
  , ("ops_mix", [3, 9], 18446744073709551610)
  , ("ops_mix", [9, 3], 6)
  , ("ops_mix", [5, 5], 18446744073709551611)
  , ("ops_mix", [2, 1], 1)
  , ("tup_second", [3, 9], 15), ("tup_second", [10, 20], 40)
  , ("list_sum", [10], 16), ("list_sum", [0], 6)
  , ("list_head", [42], 42) ]

def edgeSpecs (e : EdgeEmitted) : List TestingKit.Spec :=
  [ Spec.ofList "the edgepython emission: the frontend's module through \
      the SAME world-checked component binary (the second frontend's \
      component face)"
      (fun _ => do
        -- the shape pins: the component header + the five contract lines
        TestingKit.assertEq "the edge component's header pin"
          (e.bytes.take 8) [0x00, 0x61, 0x73, 0x6D, 0x0D, 0x00, 0x01, 0x00]
        TestingKit.assert (e.witText.startsWith "package mandate:guest;\n")
          "the edge world text must carry the package line"
        TestingKit.assert (e.witText.contains "world edge {")
          "the edge world text must carry the world block"
        for line in edgeExportLines do
          TestingKit.assert (e.witText.contains line)
            s!"the edge world text must carry the contract line: {line}"
        -- the embedded core module IS the frontend's product (section 1
        -- carries the core wasm magic right after its length prefix —
        -- the varint's width shifts the offset, so the pin scans the
        -- section head's first bytes)
        TestingKit.assert (((e.bytes.drop 9).take 6).contains 0x61)
          "the edge component embeds a core wasm module")
      [("control: the edge world text's adder contract is a LIE (wrong \
          arity — caught)",
         fun _ => TestingKit.assert
           (e.witText.contains "export adder: func(a: u64) -> u64;")
           "the control demands the wrong arity to be present")
      , ("control: the edge component's header is DOCTORED (caught)",
         fun _ => TestingKit.assertEq "tampered"
           (e.bytes.take 8) [0x00, 0x61, 0x73, 0x6D, 0x0D, 0x00, 0x01, 0x01])
      ]
      (h := by simp) 1 65
  , Spec.ofList "the committed edge slice byte-ties (the render face + \
      the binary face, both)"
      (fun _ => do
        TestingKit.assert (e.bytes.length > 8)
          "the emission must produce bytes"
        match e.binTie, e.witTie with
        | .ok (), .ok () => .ok ()
        | .error why, _ => .error s!"the binary tie failed: {why}"
        | _, .error why => .error s!"the render tie failed: {why}")
      [("control: the tie face is a LIE (the committed binary is \
          ABSENT — the control demands the tie to fail)",
         fun _ => TestingKit.assert (e.bytes.isEmpty)
           "the control demands empty bytes")
      , ("control: the edge world text is DOCTORED (the export name is \
          wrong — the control demands the doctored line to be the fresh \
          render)",
         fun _ => TestingKit.assert
           (e.witText.contains "export doubleXX: func(x: u64) -> u64;")
           "the control demands the doctored export name")
      ]
      (h := by simp) 1 66
  , Spec.ofList "THE THREE-WAY PARITY: the Python oracle ≡ the Lean \
      executor ≡ the wasmtime face's goldens, at every point"
      (fun _ => do
        for (name, args, want) in parityPoints do
          -- leg 1: the legacy Python oracle answers the literal
          TestingKit.assertEq s!"py {name} {args}" (pyAt name args) (some want)
          -- leg 2: the Lean executor over the SAME core module agrees
          TestingKit.assertEq s!"exec {name} {args}" (resultOf (execAt name args))
            (some want)
          -- leg 3 (the wasmtime face) runs in crates/mandate-host's
          -- edge lane over the COMMITTED component — its goldens are
          -- THESE literals; the byte-tie above ties that component to
          -- this core module, closing the circle
          TestingKit.assert (e.bytes.length > 0) s!"component for {name}")
      [("control: the parity claim BROKEN (double 21 = 999) is caught",
         fun _ => TestingKit.assertEq "wrong"
           (resultOf (execAt "double" [21])) (some 999))
      , ("control: the oracle disagrees with itself is caught (pyEval \
          loop_sum 10 = 999)",
         fun _ => TestingKit.assertEq "wrong"
           (pyAt "loop_sum" [10]) (some 999))
      ]
      (h := by simp) 1 67
  ]

/-! ## The WITNESS lane's computed face (the host-gating lane: the
    pinned invariant's checker as an export, the heap-return face) -/

/-- The witness emission's product: the same shape over the checker
    component (the bytes, the world text, the committed ties; the
    emission is PURE — the hand-built fixture needs no LCNF re-run). -/
structure WitnessEmitted where
  bytes : List UInt8
  witText : String
  binTie : CheckResult
  witTie : CheckResult
  deriving Inhabited

/-- The witness emission's product (the committed artifact's source +
    its ties). -/
def computeWitnessEmitted : IO (Except String WitnessEmitted) := do
  match Guest.Component.encodeComponent
      ComponentTests.WitFixture.witGateModule
      ComponentTests.WitFixture.witGateWorld with
  | .error e => return .error s!"witness component: {e.render}"
  | .ok bs => do
      let witText := Wit.Render.worldFile "mandate:guest"
        ComponentTests.WitFixture.witGateWorld
      let binTie ← tieCommittedAt "gen/component-witness-slice.wasm"
        "gen/component-witness-slice.wasm.hdr" bs
      let witTie ← tieCommittedWitAt "gen/component-witness-slice.wit" witText
      return .ok { bytes := bs, witText := witText
                 , binTie := binTie, witTie := witTie }

def witnessSpecs (w : WitnessEmitted) : List TestingKit.Spec :=
  [ Spec.ofList "the witness emission: the pinned invariant's checker
      module through the SAME world-checked component binary (the
      heap-return face: `witness-gate : func(...) -> result<_, u64>`; the
      committed artifact byte-tied)"
      (fun _ => do
        TestingKit.assertEq "the witness component's header pin"
          (w.bytes.take 8) [0x00, 0x61, 0x73, 0x6D, 0x0D, 0x00, 0x01, 0x00]
        TestingKit.assert (w.witText.contains
          "export witness-gate: func(src: u64, dst: u64, amount: u64, t1: u64, \
           b1: u64, t2: u64, t3: u64, b3: u64) -> result<_, u64>;"
        ) "the world text must carry the witness-gate contract line"
        TestingKit.assert (w.witText.startsWith "package mandate:guest;\n")
          "the witness world text must carry the package line"
        -- the LEAN teeth (the fixture's legs — the checker's own
        -- calculus + the Lean-EXECUTOR parity, all pure): the parity's
        -- wasmtime leg runs in crates/mandate-host's witness lane over
        -- the COMMITTED component; the byte-tie above ties that
        -- component to this module, closing the circle.
        TestingKit.assert ComponentTests.WitFixture.legValid
          "the producer's certificate must ACCEPT at the valid row"
        TestingKit.assert ComponentTests.WitFixture.legValidWire
          "the valid row's wire must be the pinned 5 slots"
        TestingKit.assert ComponentTests.WitFixture.legTampered
          "the tampered record must refuse (its wire exists)"
        TestingKit.assert ComponentTests.WitFixture.legWrongSchema
          "the wrong-shape certificate must refuse (no wire)"
        TestingKit.assert ComponentTests.WitFixture.legInvalid
          "the invalid row must refuse (no honest certificate)"
        TestingKit.assert ComponentTests.WitFixture.legExecutorParity
          "the fixture's own module must answer the pinned verdicts"
        match w.binTie, w.witTie with
        | .ok (), .ok () => .ok ()
        | .error why, _ => .error s!"the binary tie failed: {why}"
        | _, .error why => .error s!"the render tie failed: {why}")
      [("control: the witness world's contract is a LIE (wrong err type
          — caught)",
         fun _ => TestingKit.assert
           (w.witText.contains "export witness-gate: func() -> result<_, u64>;")
           "the control demands the wrong signature to be present")
      , ("control: the executor parity claim BROKEN (the tampered wire
          accepted) is caught",
         fun _ => TestingKit.assertEq "wrong" (gateVerdict (gateRun 1 2 5 1 0 3 0 0))
           (some (0, 0)))
      ]
      (h := by simp) 1 70
  ]

/-! ## The layout suite (the D6 port: Guest.Layout — the canonical-ABI
    flat-record layout's proof content + its concrete pins) -/

def layoutSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the canonical-ABI flat-record layout: the offsets walk's
      soundness (the non-overlap theorem, kernel-checked) + the
      concrete pins (the D6 port)"
      (fun _ => do
        -- the pins' VALUES are the rfl theorems' subjects — the kernel
        -- checked the equalities; the suite consumes the same numbers
        -- (a drift here is a proof drift, impossible-by-construction —
        -- the pin is the consumer's tooth)
        TestingKit.assertEq "the user record's offsets"
          (Guest.Layout.offsets Guest.Layout.userTys) [0, 8, 16, 24]
        TestingKit.assertEq "the user record's size (the stream item
          stride)" (Guest.Layout.size Guest.Layout.userTys) 32
        TestingKit.assertEq "the u64 field's offset"
          (Guest.Layout.offsets [.atom .u64]) [0])
      [ ("control: the offsets pin BROKEN (tags at 25) is caught",
         fun _ => TestingKit.assertEq "wrong"
           (Guest.Layout.offsets Guest.Layout.userTys) [0, 8, 16, 25])
      , ("control: the size pin BROKEN (stride 31) is caught",
         fun _ => TestingKit.assertEq "wrong"
           (Guest.Layout.size Guest.Layout.userTys) 31)
      ]
      (h := by simp) 1 68
  ]

/-! ## The Layout emitter consumer (the object-slot lane: Guest.Lower's
    boxed-Nat constants are the proved walk's outputs — the hand
    numbers died into `Guest.Layout.offsets`/`size`, and the generated
    components' bytes are unchanged — the same layout, now
    proved-derived) -/

def layoutConsumerSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the object-slot lane's constants are Layout-derived
      (the emitter consumer: the legacy hand-numbered rows ride the
      proved walk)"
      (fun _ => do
        TestingKit.assertEq "the boxed object's size"
          Guest.boxSize 16
        TestingKit.assertEq "the rc cell's offset (slot 0)"
          Guest.rcCellOff 0
        TestingKit.assertEq "the box payload's offset (slot 1)"
          Guest.boxPayloadOff 8
        TestingKit.assertEq "the closure fnIdx's offset (slot 1)"
          Guest.closureFnIdxOff 8
        TestingKit.assertEq "the closure's first capture offset (slot 2)"
          Guest.closureCapOff 16
        TestingKit.assertEq "the closure's size (2 captures)"
          (Guest.closureSize 2) 32)
      [ ("control: the object-size pin BROKEN (15) is caught",
         fun _ => TestingKit.assertEq "wrong" Guest.boxSize 15)
      , ("control: the payload-offset pin BROKEN (slot 0 — the legacy's
          wrong-twice face) is caught",
         fun _ => TestingKit.assertEq "wrong" Guest.boxPayloadOff 0)
      ]
      (h := by simp) 1 69
  ]

/-! ## The IMPORT lane (the externs' OTHER half — the declared trust
    boundary's far side: the world's import row + the core module's
    wasm import + the host's provision) -/

/-- The import emission's product (the WitnessEmitted shape over the
    import fixture's paths). -/
def ImportEmitted := WitnessEmitted

/-- The import emission's computed face (the witness pattern). -/
def computeImportEmitted : IO (Except String ImportEmitted) := do
  match Guest.Component.encodeComponent
      ComponentTests.ImportFixture.importSpecOk.core
      ComponentTests.ImportFixture.importWorld with
  | .error e => return .error s!"import component: {e.render}"
  | .ok bs => do
      let witText := Wit.Render.worldFile "mandate:guest"
        ComponentTests.ImportFixture.importWorld
      let binTie ← tieCommittedAt "gen/component-import-slice.wasm"
        "gen/component-import-slice.wasm.hdr" bs
      let witTie ← tieCommittedWitAt "gen/component-import-slice.wit" witText
      return .ok { bytes := bs, witText := witText
                 , binTie := binTie, witTie := witTie }

/-- The lowering's MODULE-shape facts (pure; the decided face). -/
def importModuleFacts : List Bool :=
  match ComponentTests.ImportFixture.importModule with
  | .error _ => [false]
  | .ok m =>
      [ -- THE IMPORT FACE's module shape: ONE core import (the
        -- declared type, tyIdx 1 — the import types ride after the
        -- sig types), ONE local function (the export at the SHIFTED
        -- absolute index 1 — the imports take 0..k-1)
        m.imports.length == 1
          && m.imports.head!.mod == "host"
          && m.imports.head!.name == "host-add"
          && m.imports.head!.tyIdx == 1
          && m.funcs.length == 1
          && m.exports.length == 1
          && m.exports.head!.name == "add64"
          && m.exports.head!.desc == WasmCore.ExportDesc.func 1
      -- the module VALIDATES (the import's declared type rides the
      -- call-typing premises)
      , match WasmCore.checkModule m with
        | .ok _ => true | .error _ => false ]

/-- The import lane's suite (the witness suite's shape over the
    import fixture: the byte-ties, the module-shape pins, the MODEL's
    extern-call semantics (the provision row answers; the unprovisioned
    run answers unmodeled), and the GENERATION teeth (the
    undeclared/skewed/unprovisioned refusals — the E-codes pinned). -/
def importSpecs (w : ImportEmitted) : List TestingKit.Spec :=
  [ Spec.ofList "the import emission: the guest's add64 calling the
      imported host-add — the world's import row + the component's
      import section + the canon LOWERS + the shim instance (the
      committed artifact byte-tied; the wasm-tools-validated shape)"
      (fun _ => do
        TestingKit.assertEq "the import component's header pin"
          (w.bytes.take 8) [0x00, 0x61, 0x73, 0x6D, 0x0D, 0x00, 0x01, 0x00]
        TestingKit.assert (w.witText.contains
          "import host-add: func(a: u64, b: u64) -> u64;")
          "the world text must carry the host-add import row"
        TestingKit.assert (w.witText.contains
          "export add64: func(a: u64, b: u64) -> u64;")
          "the world text must carry the add64 export row"
        TestingKit.assert (w.witText.startsWith "package mandate:guest;\n")
          "the import world text must carry the package line"
        match w.binTie, w.witTie with
        | .ok (), .ok () => .ok ()
        | .error why, _ => .error s!"the binary tie failed: {why}"
        | _, .error why => .error s!"the render tie failed: {why}")
      [("control: the world's import row is a LIE (wrong name — caught)",
         fun _ => TestingKit.assert
           (w.witText.contains "import host-sub: func(a: u64, b: u64) -> u64;")
           "the control demands the wrong import row to be present")
      , ("control: the header pin BROKEN (the core-layer magic — caught)",
         fun _ => TestingKit.assertEq "wrong"
           (w.bytes.take 8) [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00])
      ]
      (h := by simp) 1 71
  , Spec.ofList "the lowering's import face: the core module carries
      ONE wasm import (the declared type at the sig-types-after type
      index), the local function at the SHIFTED absolute index, and
      the module validates"
      (fun _ => TestingKit.assert (importModuleFacts.all (· == true))
        "the lowered module's import shape drifted")
      [("control: the module-shape claim BROKEN (the empty module —
          caught)",
         fun _ => TestingKit.assert
           (match ComponentTests.ImportFixture.importModule with
            | .ok m => m.imports.isEmpty
            | .error _ => false)
           "the control demands the imports to be absent")
      , ("control: the validation claim BROKEN (the export's index —
          caught)",
         fun _ => TestingKit.assert
           (match ComponentTests.ImportFixture.importModule with
            | .ok m => m.exports.head!.desc == WasmCore.ExportDesc.func 0
            | .error _ => false)
           "the control demands the UNSHIFTED index")
      ]
      (h := by simp) 1 72
  , Spec.ofList "the MODEL's extern-call semantics: the provision row
      answers (the closed op the model's host computes — i64add) and
      the value crosses (runFunc over the shifted index 1); the
      UNPROVISIONED model run answers the honest ledger (.unmodeled,
      never a wrong answer) — the three-way's Lean leg (the wasmtime
      leg is crates/mandate-host's import lane)"
      (fun _ => TestingKit.assert
        (match ComponentTests.ImportFixture.modelRun 1000 2 3 with
        | .ok s' => s'.stack == [WasmCore.Val.i64 5]
        | _ => false)
        "the provision's value did not cross (the model run drifted)")
      [("control: the crossing claim BROKEN (the wrong golden — caught)",
         fun _ => TestingKit.assert
           (match ComponentTests.ImportFixture.modelRun 1000 2 3 with
            | .ok s' => s'.stack == [WasmCore.Val.i64 6]
            | _ => false)
           "the control demands the wrong value to cross")
      , ("control: the unprovisioned ledger claim BROKEN (the provision
          — caught)",
         fun _ => TestingKit.assert
           (match ComponentTests.ImportFixture.bareRun 1000 2 3 with
            | .ok _ => true | _ => false)
           "the control demands the unprovisioned run to answer ok")
      ]
      (h := by simp) 1 73
  , Spec.ofList "the import teeth at GENERATION (the mandatory negative
      controls): the undeclared import refuses (importDrift), the
      signature skew refuses (importSigDrift), the unclaimed module
      import refuses (importUnclaimed) — each with its E-code pinned,
      nothing written"
      (fun _ => do
        let tooth (spec : Except Guest.LowerError Guest.Component.Spec)
            (code : String) : Bool :=
          match spec with
          | .error _ => false
          | .ok s =>
              match Guest.Component.checkImports s.core s.world with
              | .error e => (Kit.Diag.toString e.toDiag).contains code
              | .ok _ => false
        TestingKit.assert
          (tooth ComponentTests.ImportFixture.driftSpec "GC2026")
          "the undeclared import did not refuse at generation"
        TestingKit.assert
          (tooth ComponentTests.ImportFixture.skewSpec "GC2027")
          "the skewed import did not refuse at generation"
        TestingKit.assert
          (tooth ComponentTests.ImportFixture.unclaimedSpec "GC2028")
          "the unclaimed import did not refuse at generation")
      [("control: the drift tooth BROKEN (the E-code misattributed —
          caught)",
         fun _ => TestingKit.assert
           (tooth ComponentTests.ImportFixture.driftSpec "GC2027")
           "the control demands the drift to carry the SKEW code")
      , ("control: the teeth claim BROKEN (the valid spec refused —
          caught)",
         fun _ => TestingKit.assert
           (match ComponentTests.ImportFixture.importSpec with
            | .ok s =>
                match Guest.Component.checkImports s.core s.world with
                | .error _ => true | .ok _ => false
            | .error _ => false)
           "the control demands the VALID import pair to refuse")
      ]
      (h := by simp) 1 74
  ]
where
  tooth (spec : Except Guest.LowerError Guest.Component.Spec)
      (code : String) : Bool :=
    match spec with
    | .error _ => false
    | .ok s =>
        match Guest.Component.checkImports s.core s.world with
        | .error e => (Kit.Diag.toString e.toDiag).contains code
        | .ok _ => false

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
      match ← computeEdgeEmitted with
      | .error ee =>
          IO.eprintln s!"ComponentTests: EDGE PIPELINE FAILED — {ee}"
          return 1
      | .ok ed =>
        match ← computeWitnessEmitted with
        | .error ew =>
            IO.eprintln s!"ComponentTests: WITNESS PIPELINE FAILED — {ew}"
            return 1
        | .ok wd =>
          match ← computeGen with
          | .error eg =>
              IO.eprintln s!"ComponentTests: GEN PIPELINE FAILED — {eg}"
              return 1
          | .ok (g, pin) =>
            match ← computeImportEmitted with
            | .error ei =>
                IO.eprintln s!"ComponentTests: IMPORT PIPELINE FAILED — {ei}"
                return 1
            | .ok im =>
              TestingKit.mainOfSuites
                [ ("the component emission", emissionSpecs e)
                , ("the skew teeth", skewSpecs)
                , ("the string emission", stringSpecs s)
                , ("the edgepython component lane", edgeSpecs ed)
                , ("the witness component lane", witnessSpecs wd)
                , ("the import component lane", importSpecs im)
                , ("the async component lane", ComponentTests.AsyncFixture.asyncSpecs)
                , ("the stream component lane", ComponentTests.StreamFixture.streamSpecs)
                , ("the flat-record layout", layoutSpecs)
                , ("the Layout emitter consumer", layoutConsumerSpecs)
                , ("the manifest discipline", genSpecs g pin) ]
