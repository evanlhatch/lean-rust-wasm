/-
# Scaffold.Generate — the interpreter: AppSpec → the consumer's skeleton

The generative engine's Lean-syntax target reading (notes/v3/01-core.md
§5): the AppSpec is the spec, the scaffold is the artifact — THIS
generator IS that spine reading, an emitter into Lean source (the
shape is Kit.Emit's: pure + total, files with declared paths, the
2-line GENERATED header whose content hash is the byte-tie anchor).

Generated modules (the name convention derives everything from the
spec's `name`):

- `<Name>/Reg.lean` — the registration module: the item type + the ONE
  `register_lane` call (Kit.Lane's lane recipe steps 1–2, R3). This
  module's generated initializers run at import, so the consumption is
  the NEXT module (the KitTests.LaneReg→LaneDemo discipline — a
  module's own initializers do not run during its own elaboration).
- `<Name>/App.lean` — the application module: the lane consumption
  (one sample entry), the obligation view (15-patterns #4), and one
  SECTION per requested capability (checks / diagnostics /
  migration-hooks — each section names its recipe and its FILL
  OBLIGATIONS; the skeleton's placeholders are honest stubs-with-notes,
  never silent lies).
- `<Name>/Flow.lean` — the consumer's HAND-OWNED extension module,
  SEEDED once (no GENERATED header, no byte-tie — the driver writes it
  only when absent; the consumer owns every byte after). The emitter
  row lives HERE (R1 step 4 / 12 §3): its `run` is app logic, not spec
  data — the fill obligations must point into a file the consumer may
  edit, never into a DO-NOT-EDIT artifact (the byte-tie would read the
  fill as a drift). The seed is born-green: the emitter stub + a
  two-control suite the consumer widens.
- `<Name>/Tests.lean` — the test suite: the replay pin + the TestingKit
  `Spec` WITH the two mandatory sabotage controls (15-patterns #5 —
  the template REFUSES to generate a control-free suite: the
  `negatives` subtype is satisfied by the template's own controls) +
  the exe wiring seed.

The header discipline: every generated module carries the
`Kit.Emit.header` block (the @[derived]-equivalent stamp — 01 §5: the
generated surface is byte-tie-stable; the content hash folds the body
through the LCG BEFORE the header is prepended — no circularity).

The generator is TOTAL: `generate : AppSpec → Except Kit.Diag …` —
defined for every input; a malformed spec is the Diag refusal (the
curated failures live in `Scaffold.validate`, the closed-world
constructor fills the valid space + the did-you-mean).

Adoption (the generated files' consumer side — a deliberate act):
commit the files, add the lakefile rows, wire the gates. The seed's
byte-tie lives in ScaffoldTests (golden-pinned); the generated
registration module is elaborated IN-PROCESS by the tests (the
compiled-ness proof where honestly checkable).

Core-only (imports Kit.Emit + Scaffold.Spec + TestingKit.Golden — the
cone rule).

Five questions (notes/v3/01-core.md):
- root: Crossing — the generative engine: spec read into Lean source.
- carrier grade: the emitter discipline inherited (pure total run,
  declared paths, the content-hash header); the skeleton's law slots
  ride the sections' fill obligations.
- spine reading: THE spine — Registry (the AppSpec) → Interpretation
  (this fold) → artifact (the Lean source).
- ladder rung: rung 1 (the discipline lives in the shapes: the closed
  spec, the header stamp, the mandatory controls); the generated
  modules' own rungs are the spec's `rung` answer.
- gate row: ScaffoldTests (the golden byte-tie + the in-process
  elaboration + the teeth); the gates' wiring is the adoption act.
-/

import Kit.Emit
import Kit.Derive.Evidence
import TestingKit.Golden
import Scaffold.Spec

namespace Scaffold

/-! ## The name conventions (everything derives from the spec's name) -/

/-- The lane item's type name: `<Name>Item`. -/
def itemTyOf (spec : AppSpec) : String := spec.name ++ "Item"

/-- The lane's base name: the item type's last component decapitalized
    (Kit.Lane's convention) — the attr is `@[<base>]`, the accessors
    `get<Base>s` / `<base>Registry` / `<base>NameOf`. -/
def baseOf (spec : AppSpec) : String := (itemTyOf spec).decapitalize

/-- Does the validated spec carry the capability? (`capsOf` is `none`
    only off the validated path; the empty default reads as absent.) -/
def hasCap (spec : AppSpec) (c : Capability) : Bool :=
  ((capsOf spec).getD []).contains c

/-- The five-questions block, filled from the spec (the generated
    modules' headers). -/
def fiveQuestions (spec : AppSpec) : String :=
  "Five questions (notes/v3/01-core.md), filled from the AppSpec:\n"
    ++ "- root: " ++ spec.root ++ "\n"
    ++ "- carrier grade: " ++ spec.carrier ++ "\n"
    ++ "- spine reading: " ++ spec.spine ++ "\n"
    ++ "- ladder rung: " ++ spec.rung ++ "\n"
    ++ "- gate row: " ++ String.intercalate ", " spec.gateRows ++ "\n"
    ++ "Consumes (the schema registry refs): "
       ++ String.intercalate ", " spec.consumes ++ "\n"
    ++ "Capabilities generated: " ++ String.intercalate ", " spec.capabilities

/-! ## The registration module -/

/-- The registration module's body: the item type + the ONE
    `register_lane` call (R3 steps 1–2, Kit.Lane mechanized). -/
def regBody (spec : AppSpec) : String :=
  String.intercalate "\n"
    ["/-"
    , "# " ++ spec.name ++ ".Reg — the generated registration module (Scaffold)"
    , ""
    , "Generated from the AppSpec VALUE `Scaffold.AppSpec` (Scaffold.Spec —"
    , "the spec of record). The GENERATED header above is the"
    , "@[derived]-equivalent stamp (01 §5): the content hash is the"
    , "byte-tie anchor; DO NOT EDIT by hand — regen is a deliberate,"
    , "commit-visible act."
    , ""
    , fiveQuestions spec
    , "-/"
    , ""
    , "import Kit.Lane"
    , ""
    , "namespace " ++ spec.name
    , ""
    , "/-! ## The lane item + the registration (capability: registry-lane, R3) -/"
    , ""
    , "/-- The lane's item type: the skeleton's seed shape (the consumer"
    , "    widens the fields; the naming fn below pins the lookup key). -/"
    , "structure " ++ itemTyOf spec ++ " where"
    , "  name : String"
    , "  weight : Nat"
    , "deriving Inhabited, Repr, BEq"
    , ""
    , "-- The lane registration (Kit.Lane's ONE kit call — the env"
    , "-- extension + the attribute mount; the accessors, the fold hook"
    , "-- and the registry derive from the base name)."
    , "register_lane " ++ itemTyOf spec ++ " where"
    , "  naming := fun it => it.name"
    , ""
    , "end " ++ spec.name
    , ""]

/-! ## The application module -/

/-- The application module's body: the consumption + one section per
    requested capability (each names its recipe + its fill
    obligations). -/
def appBody (spec : AppSpec) : String :=
  String.intercalate "\n"
    (["/-"
    , "# " ++ spec.name ++ ".App — the generated application module (Scaffold)"
    , ""
    , "The lane consumption lives HERE (the Reg module's initializers"
    , "ran at ITS import — the LaneReg→LaneDemo discipline)."
    , ""
    , fiveQuestions spec
    , "-/"
    , ""
    , "import Kit.Emit"
    , "import Kit.Obligation"
    , "import Kit.Derive.Evidence"
    , "import Kit.Diag"
    , "import " ++ spec.name ++ ".Reg"
    , ""
    , "namespace " ++ spec.name
    , ""
    , "/-! ## The consumed items (the AppSpec's echo) -/"
    , ""
    , "/-- The schema items this app consumes (the AppSpec's echo — the"
    , "    consumption wiring lands with the schema lanes; the schema is"
    , "    the schema lane's artifact, never the scaffold's). -/"
    , "def " ++ baseOf spec ++ "Consumes : List String := ["
      ++ String.intercalate ", " (spec.consumes.map (fun s => "\"" ++ s ++ "\"")) ++ "]"
    , ""]
    ++ (if hasCap spec .registryLane then
    ["/-! ## The lane consumption (capability: registry-lane) -/"
    , ""
    , "/-- One sample entry — the lane consumption's live seed (the"
    , "    attribute appends at elaboration; the replay reads it in the"
    , "    consumers of this module). -/"
    , "@[" ++ baseOf spec ++ "]"
    , "def sampleEntry : " ++ itemTyOf spec ++ " := { name := \"sample\", weight := 1 }"
    , ""
    , "/-! ## The obligation view (15-patterns #4 — one row per item) -/"
    , ""
    , "/-- The obligation row over one item: the label, the COMPUTED"
    , "    tier, the payload, the provenance — and THE CLAIM AS THE TYPE"
    , "    INDEX (the row claims the item's name is nonempty — the"
    , "    naming fn's precondition), so the tier/evidence/discharge can"
    , "    never drift from the claim. The tier is COMPUTED from the"
    , "    evidence kind (Kit.Derive.Evidence — 16-surface §3): the claim"
    , "    is decidable over the closed field space, the kernel decides —"
    , "    the machinery cannot mislabel. The discharge rides the"
    , "    KIT backends (`Kit.Obligation.decideDischarge` — it discharges"
    , "    the row's OWN index; there is no claim parameter to mis-wire),"
    , "    never a hand-rolled trio. -/"
    , "def " ++ baseOf spec ++ "Obligation (it : " ++ itemTyOf spec
      ++ ") : Kit.Obligation String (it.name ≠ \"\") :="
    , "  { label := s!\"" ++ spec.name ++ "/" ++ "\" ++ it.name"
    , "    tier := (Kit.Derive.Evidence.evidenceKindOfShape"
    , "              Kit.Derive.Evidence.CarrierShape.closedFinite).tier!"
    , "    payload := it.name"
    , "    provenance := `" ++ spec.name ++ " }"
    , ""]
    else [])
    ++ (if hasCap spec .checks then
    ["/-! ## The check face (capability: checks — R5) -/"
    , ""
    , "/-- The checker face the skeleton pins: a decidable legality over"
    , "    one item. FILL OBLIGATIONS (R5): the Statement instance (the"
    , "    checker + `sound`; completeness `.missing` unless proved) and"
    , "    the mounts (gate/lint/test/obligation/monitor) land when the"
    , "    app's real judgment exists — never new check-shaped"
    , "    infrastructure. -/"
    , "def " ++ baseOf spec ++ "Check (it : " ++ itemTyOf spec ++ ") : Bool :="
    , "  !it.name.isEmpty"
    , ""
    , "/-- The check's curated refusal shape (the ONE envelope; the"
    , "    closed-world constructor fills the valid space + the"
    , "    did-you-mean). -/"
    , "def " ++ baseOf spec ++ "CheckDiag (it : " ++ itemTyOf spec ++ ") : Kit.Diag :="
    , "  Kit.Diag.closedWorld ⟨\"SCF0013\"⟩  -- eSCF0013: Scaffold.Spec's"
    , "    -- allocated row (the persisted registry; never a hand-strung code)"
    , "    (s!\"" ++ spec.name ++ ": item \" ++ it.name"
    , "      ++ \" fails " ++ baseOf spec ++ "Check — the name must be nonempty\")"
    , "    .error it.name [\"a nonempty name\"]"
    , ""]
    else [])
    ++ (if hasCap spec .diagnostics then
    ["/-! ## The diagnostics rows (capability: diagnostics — 05 §4) -/"
    , ""
    , "/-- The usage-Diag helper (the `Kit.Lane.usageDiag` shape): every"
    , "    failure path constructs the ONE envelope, the E-code named at"
    , "    the call site (the persisted registry allocates them — never"
    , "    position-derived). -/"
    , "def " ++ baseOf spec ++ "UsageDiag (code message : String) : Kit.Diag :="
    , "  { code := ⟨code⟩, message := message, severity := .error }"
    , ""]
    else [])
    ++ (if hasCap spec .migrationHooks then
    ["/-! ## The migration hook (capability: migration-hooks — R3) -/"
    , ""
    , "/-- The migration lane's honest identity seed: old item → new"
    , "    item. The migration law (the LOCAL equation, 01 §2) is stated"
    , "    when the real migration exists — the hook keeps the lane"
    , "    mountable. -/"
    , "def " ++ baseOf spec ++ "Migrate (it : " ++ itemTyOf spec ++ ") : "
      ++ itemTyOf spec ++ " := it"
    , ""]
    else [])
    ++ ["end " ++ spec.name, ""])

/-! ## The flow module (the consumer's hand-owned extension seed) -/

/-- The flow module's body: the emitter row (its `run` is app logic —
    it lives in the ONE file the consumer owns) + the flow suite seed
    with the entourage's two control shapes (the consumer widens both).
    NO GENERATED header: the driver seeds this file ONCE and never
    overwrites it; it carries no content hash, no byte-tie — the
    one-writer rule hands the path to the consumer at adoption. -/
def flowBody (spec : AppSpec) : String :=
  -- the controls' names come from the ENTOURAGE'S DATA (the same two
  -- mechanical rows the Tests module pins)
  let controls := Kit.Derive.Evidence.mechanicalControls .closedFinite
  let c0 := controls.getD 0 ""
  let c1 := controls.getD 1 ""
  String.intercalate "\n"
    (["/-"
    , "# " ++ spec.name ++ ".Flow — the consumer's hand-owned extension module (Scaffold seed)"
    , ""
    , "Seeded ONCE by scaffold; NEVER regenerated (`scaffoldgen` skips an"
    , "existing Flow — one writer: the consumer). NO GENERATED header, no"
    , "byte-tie: this module is where the fill obligations land (12 §3) —"
    , "the emitter row's real fold (its `run` is app logic, not spec"
    , "data), the widened properties and the REAL must-fail controls"
    , "(one per coverage family, 15-patterns #5). The generated modules"
    , "stay byte-tie-clean; the app's real content lives HERE."
    , ""
    , fiveQuestions spec
    , "-/"
    , ""]
    ++ (if hasCap spec .emitter then
    ["import Kit.Emit"
    , ""]
    else [])
    ++ ["import TestingKit.Harness"
    , "import " ++ spec.name ++ ".App"
    , ""
    , "open " ++ spec.name ++ " TestingKit"
    , ""
    , "namespace " ++ spec.name
    , ""]
    ++ (if hasCap spec .emitter then
    ["/-! ## The emitter row (capability: emitter — R1 step 4 / 12 §3) -/"
    , ""
    , "/-- The emitter row: pure and total over the item list, the"
    , "    declared outputs nodup IN THE TYPE. FILL OBLIGATIONS (12 §3):"
    , "    the real fold replaces `run`'s empty body; the law is cited"
    , "    when the fold's correspondence exists (`law := some ...` —"
    , "    until then this header note IS the why-not); the outputs join"
    , "    the cross-emitter one-writer audit. -/"
    , "def " ++ baseOf spec ++ "Emitter : Kit.Emit.Emitter (List "
      ++ itemTyOf spec ++ ") where"
    , "  name := \"" ++ baseOf spec ++ "-emitter\""
    , "  style := .lean"
    , "  specSource := \"AppSpec " ++ spec.name ++ "\""
    , "  outputs := []"
    , "  run := fun _ => []"
    , ""]
    else [])
    ++ ["/-! ## The consumer's real content (defs land below this line) -/"
    , ""
    , "/-! ## The flow suite (the consumer widens the property and the"
    , "    controls — one real must-fail control per coverage family) -/"
    , ""
    , "/-- The seed suite: born-green (the property holds, both control"
    , "    shapes are caught); every assert here is the consumer's to"
    , "    widen. -/"
    , "def " ++ baseOf spec ++ "FlowSpec : Spec :="
    , "  Spec.ofList \"" ++ spec.name ++ " flow invariants\" (fun _ => do"
    , "    assert (true) \"the seed property — the consumer widens it\")"
    , "    [ (\"" ++ c0 ++ "\", fun _ =>"
    , "        assert (false) \"control fired: the seed control must fail\")"
    , "    , (\"" ++ c1 ++ "\", fun _ =>"
    , "        assert (false) \"control fired: the seed control must fail\")"
    , "    ]"
    , "    8 42"
    , ""
    , "end " ++ spec.name
    , ""])

/-! ## The test module -/

/-- The test module's body: the replay pin + the TestingKit Spec with the
    TWO mandatory sabotage controls — the ENTOURAGE'S MECHANICAL SHAPES
    (Kit.Derive.Evidence.mechanicalControls .closedFinite renders the
    rows; the generator never invents a control) — + the exe wiring
    seed. The template refuses to generate a control-free suite
    (15-patterns #5). -/
def testsBody (spec : AppSpec) : String :=
  -- the controls' names come from the ENTOURAGE'S DATA (the
  -- closed-finite shape's two mechanical rows — the count is the
  -- pinned `mechanicalControls_closedFinite_two`)
  let controls := Kit.Derive.Evidence.mechanicalControls .closedFinite
  let c0 := controls.getD 0 ""
  let c1 := controls.getD 1 ""
  String.intercalate "\n"
    ["/-"
    , "# " ++ spec.name ++ ".Tests — the generated test suite (Scaffold)"
    , ""
    , "The MANDATORY negative controls are structural (15-patterns #5):"
    , "the two sabotage placeholders below are caught by construction —"
    , "the consumer WIDENS the property and REPLACES each placeholder"
    , "with a real must-fail control (one per coverage family); the"
    , "suite never generates control-free."
    , ""
    , fiveQuestions spec
    , "-/"
    , ""
    , "import Lean"
    , "import TestingKit.Harness"
    , "import " ++ spec.name ++ ".App"
    , ""
    , "open " ++ spec.name ++ " TestingKit"
    , ""
    , "-- The replay pin: the App module's entry replayed (the Reg"
    , "-- module's initializers ran at ITS import; the entries ride the"
    , "-- app module's elaboration). A drift FAILS the build."
    , "#eval show Lean.CoreM Unit from do"
    , "  let env ← Lean.getEnv"
    , "  match " ++ baseOf spec ++ "Registry env with"
    , "  | .error e => Lean.throwError s!\"lane fold drifted: {e}\""
    , "  | .ok reg =>"
    , "    if reg.items.length ≥ 1 && reg.items[0]!.name == \"sample\" then"
    , "      pure ()"
    , "    else"
    , "      Lean.throwError \"lane replay drifted: wrong item count or name\""
    , ""
    , "/-- The suite: the property widens to the app's real invariants;"
    , "    the two controls are the ENTOURAGE'S mechanical shapes"
    , "    (Kit.Derive.Evidence.mechanicalControls .closedFinite — the"
    , "    generated names are the data's, never hand-invented) — caught"
    , "    by construction (the vacuity tripwire fires if a refactor ever"
    , "    lets one pass). -/"
    , "def " ++ baseOf spec ++ "Spec : Spec :="
    , "  Spec.ofList \"" ++ spec.name ++ " lane invariants\" (fun _ => do"
    , "    assert (" ++ baseOf spec ++ "NameOf sampleEntry == \"sample\") \"naming pin\""
    , "    assert (sampleEntry.weight == 1) \"entry pin\""
    , "    assert ((" ++ baseOf spec ++ "Obligation sampleEntry).tier"
    , "        == .decidableNow) \"the tier is computed from the evidence kind\")"
    , "    [ (\"" ++ c0 ++ "\", fun _ =>"
    , "        assert (" ++ baseOf spec ++ "NameOf sampleEntry == \"\")"
    , "          \"control fired: naming dropped the name\")"
    , "    , (\"" ++ c1 ++ "\", fun _ =>"
    , "        assert (sampleEntry.weight != 1)"
    , "          \"control fired: the entry drifted\")"
    , "    ]"
    , "    8 42"
    , ""
    , "/-- The exe wiring seed (adopt: the app's lakefile test exe roots"
    , "    HERE). -/"
    , "def " ++ baseOf spec ++ "Main : IO UInt32 :="
    , "  TestingKit.mainOfSuites [(\"" ++ spec.name ++ "\", [" ++ baseOf spec ++ "Spec])]"
    , ""]

/-! ## The generator -/

/-- THE generator: the validated spec → the four generated files
    (Reg / App / Flow-seed / Tests — the Flow seed headerless,
    hand-owned); a malformed spec is the FIRST curated refusal
    (`Scaffold.validate`'s order). Pure + total. -/
def generate (spec : AppSpec) : Except Kit.Diag (List Kit.Emit.GeneratedFile) :=
  match validate spec with
  | d :: _ => .error d
  | [] =>
      let mk (path body : String) : Kit.Emit.GeneratedFile :=
        let gm : Kit.Emit.GenMeta :=
          { time := "-"
            specSha := "scaffold-golden"
            items := spec.capabilities.length
            contentHash := TestingKit.Golden.contentHash body }
        { path := path
          contents := Kit.Emit.header .lean "scaffold" s!"AppSpec {spec.name}" gm ++ body }
      let files :=
        [ mk s!"{spec.name}/Reg.lean" (regBody spec)
        , mk s!"{spec.name}/App.lean" (appBody spec)
        -- the Flow seed is emitted WITHOUT the GENERATED header (the
        -- consumer's file — the driver writes it once, never overwrites)
        , { path := s!"{spec.name}/Flow.lean"
            contents := flowBody spec }
        , mk s!"{spec.name}/Tests.lean" (testsBody spec) ]
      -- The cross-file one-writer audit (the per-emitter nodup rides
      -- Kit.Emit's type over literals; the paths here are computed, so
      -- the check is the data-level audit face — the loud gap).
      if (files.map (·.path)).Nodup then .ok files
      else
        .error (usageDiag eSCF0011
          "the generated paths collide — one writer per artifact path")

end Scaffold
