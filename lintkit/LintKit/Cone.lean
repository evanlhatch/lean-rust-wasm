/-
LintKit.Cone — the cone table as DATA + the import-cone linter
(notes/v3/06-lean-rules.md §8: "the kernel cones C0/C1 stay mathlib-free
— the import-ban table is DATA; a cone-low module importing cone-high is
a gate failure").

The table is a plain Lean value, NOT a lakefile boundary: the lakefile
records build shape, the cone records DISCIPLINE; they coincide today by
choice and drift apart loudly here, not silently.

Shape:
* `Cone` — the order `c0machinery ≤ c1domain ≤ c2theory ≤ c3app`
  (notes/v3/01-core.md's ladder shape, one rung per cone).
* `coneOfRoot?` — project root → cone. A NEW PROJECT ROOT LANDS HERE
  DELIBERATELY with the cone its content earns; an untabled root is a
  LOUD GAP, not a pass — `coneVerdict` reports it as `.untabled` (the
  2025 discipline fix: the first cut returned `#[]` for untabled
  importers, so a landed library that forgot its row passed the cone
  rule silently — exactly the lapse the table exists to prevent).
* `Cone.bannedRoots` — the per-importer-cone external ban: C0/C1 ban
  `Mathlib` and `Batteries` (06 §8; host-side packages may import
  Batteries per the same rule, and a host-side C0 row that wants the
  Batteries exception edits `bannedRoots` with a comment, in the open).
* `readerRoots` — the host-side READER exemption: the gate/driver
  machinery whose job is to read (and replay) the packages it gates
  (Gates.GenCheck consumes SchemaCore.regen — "one copy, never two";
  forbidding the gate to read the gated package would forbid gates).
  A reader root keeps its cone and the Mathlib/Batteries ban, but is
  exempt from the cone-high rule against TABLED roots. Guest-compiled
  roots never land here.
* `coneVerdict` — the pure verdict core for one importer:
  `.untabled` (the loud gap, above) or `.offences` — which of the
  imported roots offend the importer's cone. Two rules: a cone-high
  PROJECT root is an offence for any cone-low importer (reader roots
  excepted, above); the banned external roots are offences for C0/C1
  importers. `coneOffences` is the tabled-importer case, factored out.

The linter is MODULE-level, not per-declaration: the input is the import
graph (a module's direct imports, read from `env.header`), and the
finding's site is the module itself — an empty module can violate, so a
per-decl test cannot express it. The option lives at TOP LEVEL (the
LintKit.Basic header note's registration contract); the runner
(`LintKit.Runner.runModuleLinters`) drives it. Gating: the option value
+ the CLI override; `@[nolint]` cannot attach to a module.

TRANSITIVITY (the honest state of the first cut): DIRECT imports only.
A cone-low module importing a cone-low shim that publicly imports a
cone-high module is NOT flagged here — the shim itself is. The env's
`header.moduleNames` makes the transitive closure computable, so the
closure-based ratchet is a deliberate follow-up, not a dead end; it is
deferred until a shim actually exists (nothing-without-a-consumer).

The five questions (notes/v3/01-core.md's acceptance test): root =
Universe (finite data: the table + a decided check over it); carrier
grade = none (no crossing — the check IS the decidable shadow of the
cone rule, no correspondence to state); spine reading = registry
(the table) → interpretation (the import scan) → artifact (the finding);
ladder rung = decided (decidable finite table lookup, no proofs
disclosed); gate row = the cone gate (06 §8) — Gates consumes the
runner's findings, never re-encodes the table.
-/
module

public import LintKit.Basic

public meta section

open Lean Meta

namespace LintKit

/-- The cones, low to high (notes/v3/01-core.md's ladder shape):
machinery any package may sit on → domain cores → theory → app lanes. -/
public inductive Cone where
  | c0machinery | c1domain | c2theory | c3app
  deriving Repr, DecidableEq, Inhabited

/-- The cone order's index. -/
def Cone.idx : Cone → Nat
  | .c0machinery => 0
  | .c1domain    => 1
  | .c2theory    => 2
  | .c3app       => 3

/-- The cone order: a module may sit on its own cone and every cone
below it; importing cone-HIGH is the gate failure. -/
def Cone.le (a b : Cone) : Prop := a.idx ≤ b.idx

instance : LE Cone := ⟨Cone.le⟩

instance (a b : Cone) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.idx ≤ b.idx))

/-- Render a cone for findings. -/
def Cone.render : Cone → String
  | .c0machinery => "C0 (machinery)"
  | .c1domain    => "C1 (domain)"
  | .c2theory    => "C2 (theory)"
  | .c3app       => "C3 (app)"

/-- THE cone table: project root → cone. DATA (06 §8) — the lakefile
records build shape, this records discipline. A new root lands here
deliberately with the cone its content earns; an unknown root is
table-extension debt (the linter never guesses). -/
def coneOfRoot? : Name → Option Cone
  -- C0 machinery: the core-only substrate any package may import.
  | `Kit | `TextKit | `TestingKit | `LintKit => some .c0machinery
  -- Gates: host-side, core-only (the gate spine consumes C0 findings).
  | `Gates | `LintKitTests => some .c0machinery
  -- LintKit's fixture roots: the planted teeth modules (C0 machinery —
  -- they import LintKit and nothing else) + the LOUD-GAP tooth, whose
  -- project root is deliberately LEFT OUT of the table (see
  -- LintKitFixturesUntabled in LintKitTests.Main).
  | `LintKitFixtures => some .c0machinery
  -- C0 tests + exe drivers (verified imports: their C0 lib + TestingKit
  -- + Lean — nothing cone-high).
  | `KitTests | `TestingKitTests | `TextKitTests => some .c0machinery
  | `LintMain | `GatesMain => some .c0machinery
  -- C1 domain cores + their tests + the schema package's own regen
  -- driver (verified imports: Kit/TextKit + each other; SchemaCore.Emit
  -- ← Wit/Wit.Render, same cone; SchemaMain ← SchemaCore + Lean).
  | `SchemaCore | `SchemaTests | `SchemaMain => some .c1domain
  | `WasmCore | `WasmCoreTests => some .c1domain
  | `Wit | `WitTests => some .c1domain
  | `Machines | `MachinesTests => some .c1domain
  | `ZSet | `ZSetTests => some .c1domain
  | `Datalog | `DatalogTests => some .c1domain
  | `Cost | `CostTests => some .c1domain
  -- Effects: the C1-ADJACENT machinery (the closed effect lattice + the
  -- resources split + the footprint laws — notes/v3/08-capabilities.md
  -- §8): annotation/accounting substrate for the domain lanes'
  -- composition joins, imports Kit only (the cone rule) — the
  -- ZSet/Cost precedent.
  | `Effects | `EffectsTests => some .c1domain
  | `Analysis | `AnalysisTests => some .c1domain
  | `Query | `QueryTests => some .c1domain
  | `Vortex | `VortexTests => some .c1domain
  -- C2: the host-side tooling lanes — read the domain cores' public
  -- surfaces without being domain cores: Inspector ← SchemaCore.Check
  -- (+ Kit.Obligation, Lean); Scaffold ← Kit + TestingKit (the AppSpec →
  -- generated-skeleton engine). InspectorTests rides Inspector's cone;
  -- InspectorMain is its driver.
  | `Inspector | `InspectorTests | `InspectorMain => some .c2theory
  | `Scaffold => some .c2theory
  -- Guest: the LCNF→wasm compilation lane's host side (Guest.Lcnf ←
  -- Lean + Lean.Compiler.LCNF; Guest.Lower ← WasmCore's ONE AST +
  -- Kit.Diag — the domain core read-only; the EMITTED code is the
  -- guest). Its tests ride the lane's cone.
  | `Guest | `GuestTests => some .c2theory
  -- C3: the app rows — the adopted generated app (DemoApp.Reg/App/
  -- Tests: the generator's own output, imports Kit/TestingKit/Lean but its
  -- content IS the app rung) + Scaffold's test root, which consumes
  -- DemoApp.Tests (C3) for the byte-tie and so sits at C3 honestly.
  | `DemoApp | `ScaffoldTests => some .c3app
  | _ => none

/-- The per-importer-cone EXTERNAL ban (06 §8): the kernel cones C0/C1
stay mathlib-free — `Mathlib` and `Batteries` may not be imported by
them, whatever the root table says. Host-side rows that earn the
Batteries exception (06 §8's host-side allowance) edit this table with a
comment, in the open. -/
def Cone.bannedRoots : Cone → List Name
  | .c0machinery | .c1domain => [`Mathlib, `Batteries]
  | .c2theory | .c3app => []

/-- Host-side READER roots: the gate/driver machinery that reads (and
replays) the packages it gates — exempt from the cone-high rule against
TABLED roots (the gate must consume the writer, never re-encode it:
Gates.GenCheck ← SchemaCore.regen), still subject to the C0/C1
external ban (kernel hygiene). Guest-compiled roots never land here;
adding a row is a deliberate doctrine decision, in the open. -/
def readerRoots : List Name := [`Gates]

/-- The pure verdict core: for an importer rooted at `importerRoot`
(a TABLED root — an unknown root has no verdict), which of
`importRoots` (the ROOTS of the directly imported modules) offend.
Two rules:
1. a project root of a cone-HIGH cone is an offence (cone-low importing
   cone-high — 06 §8's gate failure), unless the importer is a reader
   root (`readerRoots`);
2. for a C0/C1 importer, an unknown root is checked against the external
   ban (`Mathlib`/`Batteries`); a tabled root answers by its cone. -/
def coneOffences (importerRoot : Name) (importRoots : Array Name) :
    Array Name :=
  match coneOfRoot? importerRoot with
  | some importer =>
    let reader := readerRoots.contains importerRoot
    importRoots.filter fun r =>
      match coneOfRoot? r with
      | some c' => !reader && !(c' ≤ importer)
      | none => (importer.bannedRoots.any (·.isPrefixOf r))
  -- The TABLED case only — `coneVerdict` routes an untabled importer to
  -- `.untabled` BEFORE this function runs; this arm is unreachable on
  -- the module test's path (kept for the pure function's totality).
  | none => #[]

/-- The verdict for one importer root (the module test's input):
* `.untabled root` — the LOUD GAP: the root has no cone-table row. A
  landed library that forgot its row is exactly the discipline failure
  the table exists to catch, so this is a FINDING, never a silent pass.
* `.offences roots` — the tabled case: the offending imports (empty =
clean). -/
public inductive ConeVerdict where
  | untabled (root : Name)
  | offences (roots : Array Name)
  deriving Repr, DecidableEq, Inhabited

/-- The full verdict: route the untabled importer to the loud gap, the
tabled importer to `coneOffences`. -/
def coneVerdict (importerRoot : Name) (importRoots : Array Name) :
    ConeVerdict :=
  match coneOfRoot? importerRoot with
  | some _ => .offences (coneOffences importerRoot importRoots)
  | none => .untabled importerRoot

/-- The module-level cone test: the module's DIRECT imports (read from
`env.header`) against its root's cone. Findings are per-MODULE (an
empty module can violate — a per-decl test cannot express this).
Direct imports only — see the header's transitivity note. -/
meta def coneModuleTest (mod : Name) : CoreM (Array MessageData) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod | return #[]
  let some data := env.header.moduleData[idx]? | return #[]
  let importRoots := data.imports.map (·.module.getRoot)
  match coneVerdict mod.getRoot importRoots with
  | .untabled root =>
    return #[m!"cone gap: root `{root}` is not in the cone table — land \
      its row deliberately with the cone its content earns \
      (LintKit.Cone.coneOfRoot?): a landed project root without a row \
      passes the cone rule silently, and a silent pass is the lapse the \
      table exists to prevent (notes/v3/06-lean-rules.md §8)"]
  | .offences offences =>
    if offences.isEmpty then return #[]
    let some importer := coneOfRoot? mod.getRoot | return #[]
    return #[m!"cone violation: root `{mod.getRoot}` is \
      {importer.render} but the module imports cone-high root(s) \
      {String.intercalate ", " (offences.map toString).toList} — a cone-low \
      module importing cone-high is a gate failure \
      (notes/v3/06-lean-rules.md §8); the cone table is \
      LintKit.Cone.coneOfRoot?"]

end LintKit

-- The option, top level (the LintKit.Basic header note's registration
-- contract). Module-level linter: no per-decl snapshot and no
-- `@[nolint]` (a module cannot carry it) — gating is this option plus
-- the runner's CLI override. No `builtin_env_linter` mount: that path is
-- per-declaration; the runner is the consumer.
register_option linter.guestlang.coneImports : Bool := {
  defValue := true
  descr := "flag cone-low modules importing cone-high roots or the C0/C1 \
    external ban (Mathlib/Batteries) — notes/v3/06-lean-rules.md §8"
}
