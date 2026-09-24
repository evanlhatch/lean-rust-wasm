/-
# Inspector.Replay — the lanes' obligation rows, replayed from the env

Owner: the Inspector agent (the mandate tree, `inspector/`).
Driving decisions: notes/v3/03-bidirectional.md §5 (the evidence chain
binds to the exact registered items — the inspector REPLAYS the lanes'
env extensions, it does not re-derive them); notes/v3/09-gates-ops.md
§4 (the demand-set honesty — the replay names its roots); the gates'
`loadPkgEnv` discipline (gates/Gates/Packages.lean — MIRRORED here, not
imported: the inspector must stay a leaf so the gates can consume its
sweep in the next order without a cycle; one writer per artifact path —
Gates.Packages stays the gates' copy).

The discovery mechanism: the lanes' env extensions carry the items
(Kit.Lane's append-only compile-time event log); each lane gets ONE
reader here (`laneReaders` — the registration point for "any others
registered"), which projects the replayed items onto `Inspector.InspRow`.

The check lane's discharge honesty: the env extension carries the
REGISTERED rows, not a table — the decidable-now backend
(`SchemaCore.CheckItem.dischargeOn`) fires per-table at check time, so
the replayed rows' discharge state is the LOUD GAP with that reason.
Nothing is fabricated green.

Host-side: `unsafe` (the replay executes imported initializers).

The five questions (notes/v3/01-core.md):
- root: none — the replay preamble + the lane-reader registry.
- carrier grade: none — the rows are Obligations.lean's.
- spine reading: registration = append (Kit.Lane) → replay = the env
  load → collect = the lane readers' fold → the row list.
- ladder rung: n/a.
- gate row: none — the exe and the tests are the consumers; the gates'
  sweep consumes the rendered report next.
-/

import Lean
import Inspector.Obligations
import SchemaCore.Check

namespace Inspector

/-! ## The lane readers (the discovery mechanism) -/

/-- One replayed lane: its name + the reader that projects its env
    extension's items onto the uniform row. -/
structure LaneReader where
  lane : String
  read : Lean.Environment → List InspRow

/-- The check lane's reader (SchemaCore.Check's registry): one row per
    registered invariant, tier COMPUTED by the lane
    (`CheckItem.obligation`), provenance = the declaring lane. The
    obligation row is Prop-INDEXED by its claim — the replay reads only
    the claim-independent data fields (label/tier/payload/provenance),
    named via the `[]`-table instantiation (the claim's content is a
    Prop and is not read — the inspector reads the row AS DATA). The
    discharge state at replay is the loud gap: the extension carries no
    table; the decidable-now backend fires per-table via
    `SchemaCore.CheckItem.dischargeOn` — never fabricated green. -/
def checkLaneReader : LaneReader :=
  { lane := "check"
    read := fun env =>
      (SchemaCore.getChecks env).map fun c =>
        { lane := "check"
          label := (c.obligation []).label
          tier := .decidableNow
          provenance := (c.obligation []).provenance
          payload := String.intercalate ", " (c.obligation []).payload
          observer := none
          eCode := none
          discharge :=
            .openGap "no table provided at replay — the decidable-now backend \
              fires per-table (SchemaCore.CheckItem.dischargeOn)" } }

/-- The registered lane readers: ONE per lane the inspector replays.
    A new lane lands its reader here (one writer per reader; the
    leftover rule — no reader ahead of its first content). -/
def laneReaders : List LaneReader := [checkLaneReader]

/-- The aggregation: every registered lane reader's rows, in reader
    order (the replay is deterministic — registration order per lane). -/
def collect (env : Lean.Environment) : List InspRow :=
  laneReaders.flatMap (fun r => r.read env)

/-! ## The replay (the gates' loadPkgEnv discipline, mirrored) -/

/-- One replayed package: its report-section key + the root modules
    whose oleans carry the lane registrations. (Mirrors
    `Gates.PkgSpec`; the inspector is a leaf — see the header.) -/
structure PkgSpec where
  dir : String
  roots : Array Lean.Name
  deriving Repr, Inhabited

/-- Load one replayed package's environment: the root build dir
    prepended to the search path, initializers executed, the root
    modules imported at the gates' trust level. MIRRORED from
    `Gates.loadPkgEnv` (the discipline, not the import — the cycle
    note in the header). -/
unsafe def loadPkgEnv (base : Lean.SearchPath) (pkg : PkgSpec) :
    IO (Except String Lean.Environment) := do
  Lean.searchPathRef.set (".lake/build/lib/lean" :: base)
  try
    Lean.enableInitializersExecution
    let env ← Lean.importModules (pkg.roots.map ({ module := · })) {}
      (trustLevel := 1024) (loadExts := true)
    return .ok env
  catch e =>
    return .error (toString e)

/-- The replayed package set: the packages whose lanes' rows the
    inspector collects today. `SchemaCore.CheckSlice` (not the umbrella)
    is the root whose olean carries the `@[check]` entries — the lane's
    fixture module (the KitTests LaneReg → LaneDemo discipline). -/
def replayPkgs : Array PkgSpec :=
  #[{ dir := "SchemaCore"
      roots := #[`SchemaCore, `SchemaCore.CheckSlice] }]

/-- The replayed-roots line (the report's coverage statement — the
    demand-set honesty). -/
def replayPkgsRender : String :=
  let dirs := (replayPkgs.toList.map (·.dir))
  let rootStrs := (replayPkgs.toList.map (·.roots.toList)) |>.flatten
  String.intercalate ", " dirs ++
    " (" ++ String.intercalate ", " (rootStrs.map (·.toString)) ++ ")"

/-- THE REPLAY, environments retained: for the consumers that need the
    loaded env itself, not just the rows — the proof-coverage row's
    citation census (Inspector.Cites) and the trust report's axiom
    cones (Inspector.Trust). First load failure = the loud `.error`. -/
unsafe def replayEnvs :
    IO (Except String (List (PkgSpec × Lean.Environment))) := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  let mut out : List (PkgSpec × Lean.Environment) := []
  for pkg in replayPkgs do
    match ← loadPkgEnv base pkg with
    | .error e => return .error s!"{pkg.dir}: LOAD FAILED — {e}"
    | .ok env => out := out ++ [(pkg, env)]
  return .ok out

/-- THE REPLAY: load every replayed package, collect its rows. The
    first load failure is the loud `.error` (no partial green). -/
unsafe def collectReplayed : IO (Except String (List InspRow)) := do
  match ← replayEnvs with
  | .error e => return .error e
  | .ok envs => return .ok (envs.flatMap fun (_, env) => collect env)

end Inspector
