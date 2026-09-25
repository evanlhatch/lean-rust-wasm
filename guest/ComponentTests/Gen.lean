/-
# ComponentTests.Gen — the manifest discipline's battery

The manifest-driven generation's pins + the growth teeth + the
mandatory negative controls (15-patterns #5). The IO face computes the
two derivations ONCE (the Main.lean pattern — the checks stay PURE):

1. **the growth manifest** — a test-side `Guest.Gen.Manifest` over
   `ComponentTests.GenFixture` (the module whose guest MARKS are the
   registered surface): the compile set = the marks (genInc + genNarrow
   in, the unmarked genQuiet out), the world = the honest ABI surface
   (genInc only; the `UInt32`-result genNarrow compiled-but-unexported
   and REPORTED), and the derived component bytes carry genInc's export
   name and NOTHING unregistered (the growth teeth: a registered fn
   lands in the artifact, an unregistered one does not).
2. **the port pin** — the mandate manifest's derived world IS the
   hand-declared SSOT (`ComponentTests.Fixture.componentWorld`): the
   manifest discipline's derivation reproduces the committed surface
   byte-for-byte (the render equality + the skew check through
   `Guest.Component.check` against the derived core module).

Suites consumed by `ComponentTests.Main` (the driver imports this
module + the computed product feeds the suite list).
-/

import Guest
import Guest.GenMain
import Guest.Component
import ComponentTests.Fixture
import ComponentTests.GenFixture
import TestingKit.Harness

open Guest TestingKit

/-! ## The growth manifest (the test's authoring surface) -/

/-- THE GROWTH manifest: the fixture module's marks ARE the surface —
    no hand list of functions. -/
def growthManifest : Guest.Gen.Manifest :=
  { world := "growth", implModules := [`ComponentTests.GenFixture] }

/-! ## The byte-search face (the artifact's export-name teeth) -/

/-- How many times does the string's UTF-8 ride the byte list? (The
    component binary spells a WORLD export THREE times — the embedded
    core module's export + the alias section + the component export
    section — while a COMPILED-but-unexported fn rides only the
    embedded core module's export: the occurrence count IS the
    surface's shape.) -/
def bytesCount (bs : List UInt8) (s : String) : Nat :=
  let nd := s.toByteArray.toList
  let len := nd.length
  if len == 0 then 0
  else
    (List.range (bs.length - len + 1)).filter
      (fun i => (bs.drop i).take len == nd)
    |>.length

/-! ## The computed face (the two derivations, once) -/

/-- The growth derivation's product: the compile set, the world, the
    compiled-but-unexported row, and the derived component's bytes. -/
structure GenEmitted where
  compileSet : List Lean.Name
  world : Wit.World
  excluded : List Lean.Name
  bytes : List UInt8
  deriving Inhabited

/-- The mandate pin's product: the derived world + the skew-check
    verdict against the derived core module. -/
structure MandatePin where
  compileSet : List Lean.Name
  worldText : String
  skewOk : Bool
  deriving Inhabited

/-- One derivation, end to end: manifest → replayed env → compile set
    → world → LCNF re-run → lowering → component bytes. -/
unsafe def deriveComponent (m : Guest.Gen.Manifest) :
    IO (Except String (List Lean.Name × Wit.World × List Lean.Name × List UInt8)) := do
  match ← Guest.Gen.loadEnv m with
  | .error e => return .error e
  | .ok env =>
    let targets := Guest.Gen.compileSetOf env m
    match Guest.Gen.surfaceOf env m targets with
    | .error e => return .error e
    | .ok surf =>
      match ← Guest.Gen.readTargets? env targets with
      | .error e => return .error e
      | .ok decls =>
        match Guest.compile decls with
        | .error e => return .error s!"lower: {e.render}"
        | .ok core =>
          match Guest.Component.encodeComponent core surf.world with
          | .error e => return .error s!"component: {e.render}"
          | .ok bs => return .ok (targets.toList, surf.world, surf.excluded, bs)

/-- The mandate pin: the derived world's render + the skew check of
    the derived pair (the world the writer emits, checked against the
    core module it lowers). -/
unsafe def computeMandatePin : IO (Except String MandatePin) := do
  match ← Guest.Gen.loadEnv Guest.Gen.mandate with
  | .error e => return .error e
  | .ok env =>
    let targets := Guest.Gen.compileSetOf env Guest.Gen.mandate
    match Guest.Gen.surfaceOf env Guest.Gen.mandate targets with
    | .error e => return .error e
    | .ok surf =>
      match ← Guest.Gen.readTargets? env targets with
      | .error e => return .error e
      | .ok decls =>
        match Guest.compile decls with
        | .error e => return .error s!"lower: {e.render}"
        | .ok core =>
            let skewOk :=
              match Guest.Component.check core surf.world with
              | .ok _ => true
              | .error _ => false
            return .ok { compileSet := targets.toList
                       , worldText := Wit.Render.worldFile "mandate:guest" surf.world
                       , skewOk := skewOk }

/-! ## The suites -/

def genSpecs (g : GenEmitted) (pin : MandatePin) : List TestingKit.Spec :=
  [ Spec.ofList "the manifest discipline: the compile set + the world \
      DERIVE from the registered surface (the marks), never a hand list"
      (fun _ => do
        -- the marks ARE the compile set: genInc + genNarrow in
        TestingKit.assert (g.compileSet.contains `genInc)
          "the marked genInc must join the compile set by the registration"
        TestingKit.assert (g.compileSet.contains `genNarrow)
          "the marked genNarrow must join the compile set by the registration"
        -- the world = the honest ABI surface
        TestingKit.assertEq "the world's exports (the honest surface)"
          (g.world.exports.map (·.name)) ["genInc"]
        TestingKit.assertEq "the compiled-but-unexported row (the report's \
          honesty)"
          g.excluded [`genNarrow])
      [ ("control: the UNMARKED fn is in the compile set (a LIE — \
          caught)",
         fun _ => TestingKit.assert
           (g.compileSet.contains `genQuiet)
           "the control demands the unregistered fn to be compiled into \
           the surface")
      , ("control: the ABI-outside fn is world-EXPORTED (a LIE — \
          caught)",
         fun _ => TestingKit.assert
           (g.world.exports.any fun f => f.name == "genNarrow")
           "the control demands the UInt32-result fn to carry a lying \
           WIT type")
      ]
      (h := by simp) 1 70
  , Spec.ofList "the growth teeth: a registered fn lands in the \
      component's export surface (3 spellings: core module + alias + \
      export section); an unregistered one appears NOWHERE; a \
      compiled-but-unexported one rides the embedded core module only"
      (fun _ => do
        TestingKit.assertEq "the registered fn's surface spellings"
          (bytesCount g.bytes "genInc") 3
        TestingKit.assertEq "the unregistered fn's spellings"
          (bytesCount g.bytes "genQuiet") 0
        TestingKit.assertEq "the compiled-but-unexported fn's spellings \
          (the embedded core module's export only)"
          (bytesCount g.bytes "genNarrow") 1)
      [ ("control: the unregistered fn IS in the component's surface \
          (a LIE — caught)",
         fun _ => TestingKit.assert
           (bytesCount g.bytes "genQuiet" >= 2)
           "the control demands the unmarked fn to ride the export \
           surface")
      , ("control: the registered fn is ABSENT from the bytes (a LIE — \
          caught)",
         fun _ => TestingKit.assert
           (bytesCount g.bytes "genInc" == 0)
           "the control demands the marked fn's export to be missing")
      ]
      (h := by simp) 1 71
  , Spec.ofList "the port pin: the mandate manifest's derived world IS \
      the hand-declared SSOT (the committed surface reproduces)"
      (fun _ => do
        TestingKit.assertEq "the mandate compile set (the mark fold)"
          pin.compileSet [`add64]
        TestingKit.assertEq "the derived world's render (== the committed \
          gen/component-slice.wit body)"
          pin.worldText
          (Wit.Render.worldFile "mandate:guest" componentWorld)
        TestingKit.assert pin.skewOk
          "the derived pair must pass the component lane's skew check")
      [ ("control: the derived world DRIFTS from the SSOT (a LIE — \
          caught)",
         fun _ => TestingKit.assert
           (pin.worldText != Wit.Render.worldFile "mandate:guest" componentWorld)
           "the control demands the derivation to disagree with the hand \
           world")
      , ("control: the mandate compile set is EMPTY (a LIE — caught)",
         fun _ => TestingKit.assert (pin.compileSet.isEmpty)
           "the control demands the mark fold to have found nothing")
      ]
      (h := by simp) 1 72
  ]

/-! ## The driver face (ComponentTests.Main consumes these) -/

/-- The IO face's one product (the Main driver computes once). -/
unsafe def computeGen : IO (Except String (GenEmitted × MandatePin)) := do
  match ← deriveComponent growthManifest with
  | .error e => return .error s!"growth derivation: {e}"
  | .ok (cs, w, ex, bs) =>
    match ← computeMandatePin with
    | .error e => return .error s!"mandate pin: {e}"
    | .ok pin => return .ok ({ compileSet := cs, world := w
                             , excluded := ex, bytes := bs }, pin)
