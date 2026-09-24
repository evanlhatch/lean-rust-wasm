/-
# Scaffold.Spec — the AppSpec: a declarative VALUE describing a consumer app

The scaffold generator's spec of record (notes/v3/07-extensibility.md —
the recipes R1–R6 mechanized at the application level; notes/v3/
01-core.md §5 — the generative engine is an emitter into the
Lean-syntax target: the AppSpec is the spec, the scaffold is the
artifact). A consumer app/lane — the future substrait, qlang,
edgepython, vortex lanes — is described by a `Scaffold.AppSpec` Lean
VALUE (data, never free text) and GENERATED into a born-compliant
skeleton: the registration lane wired (Kit.Lane's `register_lane`), the
emitter riding the spine (Kit.Emit, the law-slot discipline), the
obligations flowing, the test suite with its mandatory negative
controls (unconstructible without), the diagnostics rows, the
migration-lane hooks — the discipline by default, not by memory.

## The closed capability enum (the honest minimal set)

`Capability` is CLOSED — the six capabilities the doctrine's recipes
name as row sets; each is generated as a SECTION of the skeleton:

- `registryLane` — the lane registration (R3 steps 1–2: the item type
  + `register_lane`; the registration and the consumption land in
  DIFFERENT generated modules — a module's own initializers do not run
  during its own elaboration, the KitTests.LaneReg→LaneDemo shape).
- `emitter` — the emitter row skeleton (R1 step 4 / 12 §3: outputs
  nodup in the type, the law slot or the header note).
- `checks` — the check face + its curated refusal shape (R5: the
  Statement instance + the mounts land when the real judgment exists —
  the skeleton pins the checker face and the mount points).
- `tests` — the suite skeleton WITH the mandatory negative controls
  (12 §2 step 6, 15-patterns #5): the generated `Spec` carries two
  sabotage placeholders — the template REFUSES to generate a
  control-free suite (the `negatives` subtype is satisfied by the
  template's own controls).
- `diagnostics` — the Diag envelope rows (05 §4: every failure path
  constructs the ONE envelope; the skeleton's helper is the
  `Kit.Lane.usageDiag` shape).
- `migrationHooks` — the migration-lane hook (R3: migrations as lanes;
  the skeleton's hook is the honest identity seed).

## The NAMED EXCLUSIONS (capabilities deliberately NOT in the enum)

- `dsl` — R4's authoring surface is its own grammar spec (05 §1), never
  a scaffold row: a DSL's spec IS a spec, not something a second-order
  scaffold generates.
- `machine` — 12 §5: `machine!`'s entourage IS the generator for
  machines; a scaffold row would parallel it (the no-parallel-tables
  rule, 15's meta-pattern).
- `gate` — 12 §7: gates are rows in the gates exe's registry (the
  gates lane's ownership); a consumer app lands UNDER gate rows (the
  spec's `gateRows`), it does not generate them.
- `schemacore` items — the app CONSUMES schema items by registry
  reference (`consumes`); the schema is the schema lane's artifact,
  never the scaffold's to generate.

Extending the enum is a deliberate act naming the recipe (07's reuse
contract) — the closed-world compiler drives it (15-patterns #15).

The spellings surface: the AppSpec carries capability/root/rung
SPELLINGS (Strings) validated against the closed enums — so the
curated unknown-value error EXISTS (the closed-world refusal enumerates
the valid space + the ONE engine's did-you-mean, Kit.Diag.closedWorld).
A Lean-enum-typed field would make typos unrepresentable and the error
unreachable; the curated error is the teaching surface (15-patterns
#16), the enum is the closed world it teaches.

E-codes: `SCF0001`–`SCF00xx`, call-site-named per Kit.Diag's note (the
persisted registry is the later lane; the Kit.Lane precedent).

Core-only (imports Kit.Diag + Kit.Suggest — the cone rule).

Five questions (notes/v3/01-core.md):
- root: DATA — a pure spec value; the generator is its total reading.
- carrier grade: first-order over String/List — the spec is a Lean
  value, the validation is a total fold into `List Diag`.
- spine reading: Registry → Interpretation → artifact with the AppSpec
  at the Registry end (the scaffold generator IS an interpretation of
  it — Generate.lean's spine reading).
- ladder rung: rung 1 — the closed-world discipline lives in the shape
  (`closedWorld` fills valid + did-you-mean; there is no bare-string
  refusal path).
- gate row: ScaffoldTests (the golden byte-tie + the curated-failure
  teeth + the negative controls); the gates' OWN wiring of Scaffold
  (Gates.Packages' row, the axiom report sweep) lands with the gates
  lane's next order — named follow-up, not done here.
-/

import Kit.Diag
import Kit.Suggest

namespace Scaffold

/-! ## The closed capability enum -/

/-- The closed capability set (the header names each one's recipe slot
    and the exclusions). -/
inductive Capability where
  | registryLane
  | emitter
  | checks
  | tests
  | diagnostics
  | migrationHooks
deriving Repr, BEq, DecidableEq, Inhabited

/-- The spelling (the AppSpec's surface form + the error's valid space). -/
def Capability.render : Capability → String
  | .registryLane => "registry-lane"
  | .emitter => "emitter"
  | .checks => "checks"
  | .tests => "tests"
  | .diagnostics => "diagnostics"
  | .migrationHooks => "migration-hooks"

/-- The closed list — the did-you-mean world. -/
def Capability.all : List Capability :=
  [.registryLane, .emitter, .checks, .tests, .diagnostics, .migrationHooks]

/-- The valid space as spellings (the error's enumeration). -/
def Capability.renderAll : List String :=
  Capability.all.map Capability.render

/-- Parse a spelling over the closed enum: `none` = unknown (the
    curated refusal's `got`). -/
def Capability.ofString? (s : String) : Option Capability :=
  Capability.all.find? (fun c => c.render == s)

/-! ## The closed root + rung enums (the five-questions header's
    closed slots) -/

/-- The doctrine root (01 §1's table, closed): which root the app's
    shape is an instance of. -/
inductive Root where
  | universe
  | change
  | traceModel
  | crossing
  | none_
deriving Repr, BEq, DecidableEq, Inhabited

def Root.render : Root → String
  | .universe => "universe"
  | .change => "change"
  | .traceModel => "trace-model"
  | .crossing => "crossing"
  | .none_ => "none"

def Root.all : List Root := [.universe, .change, .traceModel, .crossing, .none_]

def Root.renderAll : List String := Root.all.map Root.render

def Root.ofString? (s : String) : Option Root :=
  Root.all.find? (fun r => r.render == s)

/-- The ladder rung (01 §7's hierarchy, closed). -/
inductive Rung where
  | unrepresentable
  | noInstance
  | defaultedDecide
  | generated
  | disclosedNative
  | handTheorem
deriving Repr, BEq, DecidableEq, Inhabited

def Rung.render : Rung → String
  | .unrepresentable => "unrepresentable"
  | .noInstance => "no-instance"
  | .defaultedDecide => "defaulted-decide"
  | .generated => "generated"
  | .disclosedNative => "disclosed-native"
  | .handTheorem => "hand-theorem"

def Rung.all : List Rung :=
  [.unrepresentable, .noInstance, .defaultedDecide, .generated,
   .disclosedNative, .handTheorem]

def Rung.renderAll : List String := Rung.all.map Rung.render

def Rung.ofString? (s : String) : Option Rung :=
  Rung.all.find? (fun r => r.render == s)

/-! ## The closed gate-row vocabulary -/

/-- The gate rows of `just gates` (the gates exe's registry, 09 §3) —
    the app's `gateRows` are spellings over this closed list. Extending
    it is the gates lane's deliberate act. -/
def gateRowNames : List String :=
  ["axioms", "docs-check", "gen-check", "code-registry-check",
   "snapshot-check", "audit", "artifact-headers", "native-policy",
   "coverage", "kernel-check"]

/-! ## The AppSpec -/

/-- THE declarative spec of a consumer app/lane: a Lean VALUE — every
    field data, no free text; the enum-typed slots ride their closed
    worlds' spellings (the curated errors live at `validate`). -/
structure AppSpec where
  /-- The app's module base (identifier-shaped, capitalized — the
      generated modules are `<name>.Reg`, `<name>.App`, `<name>.Tests`). -/
  name : String
  /-- The schema item names the app consumes (the registry refs — the
      schema is never the scaffold's to generate). -/
  consumes : List String
  /-- The capabilities, as spellings over the CLOSED `Capability` enum
      (at least one — the scaffold refuses to generate an empty skeleton). -/
  capabilities : List String
  /-- The `just gates` rows the app lands under (spellings over
      `gateRowNames`). -/
  gateRows : List String
  /-- The five-questions answers the generated headers fill: the root
      (over the closed `Root` enum) and the rung (over the closed
      `Rung` enum); the carrier grade and the spine reading are the
      app's own prose answers (structured slots, per-app content). -/
  root : String
  rung : String
  carrier : String
  spine : String
deriving Repr, BEq, Inhabited

/-! ## The name check -/

/-- An identifier-shaped name: nonempty, first char a letter, the rest
    letters/digits/underscores (the generated modules + the lane
    substrate's name conventions derive from it). -/
def isIdentName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
      c.isAlpha && cs.all (fun d => d.isAlphanum || d == '_')

/-! ## The curated failures (Kit.Diag — the ONE envelope) -/

/-- The SCF family — the scaffold's E-codes, allocated from the
    PERSISTED registry (`notes/code-registry.txt`, the spec of record;
    05 §4's stable-allocation rule). The constants are the family's
    DECLARATION — the validate/generate sites use them, never a bare
    string, and the code-registry gate's coverage scan ties every
    spelling to its allocated live row. -/
def eSCF0001 : Kit.ECode := ⟨"SCF0001"⟩
def eSCF0002 : Kit.ECode := ⟨"SCF0002"⟩
def eSCF0003 : Kit.ECode := ⟨"SCF0003"⟩
def eSCF0004 : Kit.ECode := ⟨"SCF0004"⟩
def eSCF0005 : Kit.ECode := ⟨"SCF0005"⟩
def eSCF0006 : Kit.ECode := ⟨"SCF0006"⟩
def eSCF0007 : Kit.ECode := ⟨"SCF0007"⟩
def eSCF0008 : Kit.ECode := ⟨"SCF0008"⟩
def eSCF0009 : Kit.ECode := ⟨"SCF0009"⟩
def eSCF0010 : Kit.ECode := ⟨"SCF0010"⟩
def eSCF0011 : Kit.ECode := ⟨"SCF0011"⟩
def eSCF0012 : Kit.ECode := ⟨"SCF0012"⟩
def eSCF0013 : Kit.ECode := ⟨"SCF0013"⟩

/-- The literal Diag for a positional misuse (the `Kit.Lane.usageDiag`
    shape — no got/valid slot; the message names the context, the
    construct, the valid usage). Local here so Spec does not import
    Kit.Lane (the lane substrate is Generate's import, not the spec's).
    The code slot is an `ECode` of the registry's allocated family — a
    bare string cannot reach the envelope. -/
def usageDiag (code : Kit.ECode) (message : String) : Kit.Diag :=
  { code := code, message := message, severity := .error }

/-- The validation Diags for an AppSpec — ALL problems, in field order.
    Empty = valid. Every closed-world failure rides `Kit.Diag.closedWorld`
    (the valid space + the did-you-mean are unforgable). -/
def validate (spec : AppSpec) : List Kit.Diag :=
  -- the name (SA0001)
  (if isIdentName spec.name then [] else
    [Kit.Diag.closedWorld eSCF0001
      s!"AppSpec {spec.name}: the name must be identifier-shaped \
        (a letter, then letters/digits/underscores) — the generated \
        modules derive `<name>.Reg`, `<name>.App`, `<name>.Tests` and \
        the lane's base name from it"
      .error spec.name [s!"an identifier-shaped name (got: {spec.name})"]])
  -- the capabilities (SA0002 unknown, SA0003 duplicate, SA0010 empty)
  ++ (if spec.capabilities.isEmpty then
    [usageDiag eSCF0010
      s!"AppSpec {spec.name}: the capability list is empty — the scaffold \
        refuses to generate an empty skeleton; valid capabilities: \
        {String.intercalate ", " Capability.renderAll}"]
  else []) ++ (spec.capabilities.flatMap fun cap =>
    match Capability.ofString? cap with
    | none =>
        [Kit.Diag.closedWorld eSCF0002
          s!"AppSpec {spec.name}: `{cap}` is not a capability — \
            the capability enum is closed (07's recipes name each one)"
          .error cap Capability.renderAll]
    | some _ => [])
  ++ (if (spec.capabilities.map Capability.ofString?).any Option.isSome
        && (spec.capabilities.eraseDups) != spec.capabilities then
    [Kit.Diag.closedWorld eSCF0003
      s!"AppSpec {spec.name}: a capability is listed twice — each \
        capability is ONE generated section, duplicates are refused"
      .error (String.intercalate ", " spec.capabilities) Capability.renderAll]
  else []) ++
  -- the gate rows (SA0004 unknown, SA0005 duplicate)
  (spec.gateRows.flatMap fun row =>
    if gateRowNames.contains row then [] else
    [Kit.Diag.closedWorld eSCF0004
      s!"AppSpec {spec.name}: `{row}` is not a gate row — the app lands \
        under the `just gates` registry's rows"
      .error row gateRowNames])
  ++ (if spec.gateRows.eraseDups != spec.gateRows then
    [Kit.Diag.closedWorld eSCF0005
      s!"AppSpec {spec.name}: a gate row is listed twice — one row, one \
        landing"
      .error (String.intercalate ", " spec.gateRows) gateRowNames]
  else []) ++
  -- the capability dependencies (SCF0012): every capability that folds
  -- the lane's generated item type requires `registry-lane` — the item
  -- type, the entries and the accessors ARE the registry-lane's
  -- generated surface; a fold over nothing is not generated.
  (let laneDependent := ["emitter", "checks", "tests", "migration-hooks"]
   let hasLane := spec.capabilities.contains "registry-lane"
   let orphan := laneDependent.filter (fun c => spec.capabilities.contains c && !hasLane)
   if orphan.isEmpty then [] else
    [Kit.Diag.closedWorld eSCF0012
      (s!"AppSpec {spec.name}: {String.intercalate ", " orphan} " ++
        "fold the lane's generated item type — add `registry-lane`")
      .error (String.intercalate ", " orphan) ["registry-lane"]]) ++
  -- the consumes (SA0006: empty or duplicate refs)
  (if spec.consumes.any (fun c => c.isEmpty) then
    [usageDiag eSCF0006
      s!"AppSpec {spec.name}: an entry in `consumes` is empty — the \
        consumed items are the schema registry's item names"]
  else if spec.consumes.eraseDups != spec.consumes then
    [Kit.Diag.closedWorld eSCF0006
      s!"AppSpec {spec.name}: a consumed item is listed twice — one \
        reference each"
      .error (String.intercalate ", " spec.consumes) spec.consumes.eraseDups]
  else []) ++
  -- the five-questions slots (SA0007 root, SA0008 rung, SA0009 prose)
  (match Root.ofString? spec.root with
    | none =>
        [Kit.Diag.closedWorld eSCF0007
          s!"AppSpec {spec.name}: `{spec.root}` is not a doctrine root \
            (01 §1's closed table)"
          .error spec.root Root.renderAll]
    | some _ => [])
  ++ (match Rung.ofString? spec.rung with
    | none =>
        [Kit.Diag.closedWorld eSCF0008
          s!"AppSpec {spec.name}: `{spec.rung}` is not a ladder rung \
            (01 §7's closed hierarchy)"
          .error spec.rung Rung.renderAll]
    | some _ => [])
  ++ (if spec.carrier.isEmpty || spec.spine.isEmpty then
    [usageDiag eSCF0009
      s!"AppSpec {spec.name}: the five-questions header refuses blanks — \
        `carrier` (the carrier grade) and `spine` (the spine reading) \
        must name the app's answers"]
  else [])

/-- The spec's validity (the generator's admission face). -/
def isValid (spec : AppSpec) : Bool := validate spec |>.isEmpty

/-- The typed capability view (the validated spec's caps, in spelling
    order; `none` = the spec is invalid — `generate` refuses first). -/
def capsOf (spec : AppSpec) : Option (List Capability) :=
  spec.capabilities.mapM Capability.ofString?

end Scaffold
