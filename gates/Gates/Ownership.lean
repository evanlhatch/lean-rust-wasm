/-
Gates.Ownership — the artifact-ownership gate (`gates ownership`;
decisions.md D15: artifact ownership is GLOBAL — cross-emitter
disjointness + declared-vs-actual agreement; 09-gates-ops.md §4-5).

The review-of-record's finding this gate closes: no gate sweeps
committed files NOT declared by any emitter (an orphan squatting in
gen/ is invisible), and `Kit.Emit.outputsDisjoint` was exercised only
on toy emitters. Both faces land here, over the REAL emitter set:

1. DECLARED-VS-ACTUAL, both directions (D15's agreement face):
   - an on-disk file under a generated-artifact root that NO emitter
     declares is an ORPHAN (the invisible squatter);
   - a declared output with no committed file is MISSING (the
     re-baseline's debt).
   The declared set is READ FROM THE EMITTERS (never a hand-copied
   path list — the regen path's knowledge IS the declaration); the
   on-disk set is WALKED from the artifact roots (the disk, not the
   VCS — stricter: it catches uncommitted squatters too).

2. CROSS-EMITTER DISJOINTNESS (D15's disjointness face): the kit's
   `Kit.Emit.outputsDisjoint` over the real emitter set — the
   per-emitter nodup is in the type; the CROSS-emitter one-writer
   rule is a registry-level check, and this is its real-set run (the
   collision rows name the paths; the Bool verdict is the kit's).

Surface (the tree's layout, read honestly): the generated-artifact
roots are `gen/` (whole directory — every file there is artifact
surface, the `.wasm`/`.hdr`/`.wat` wasm slice rows included) and the
generated crate's Rust dirs
(`crates/schema-generated/{src,tests}`, the `.rs` files — the crate
name says generated). The declared set: `SchemaCore.witEmitter` +
`SchemaCore.Emit.Rust.rustEmitter` (the `just gen` write path) +
`SchemaCore.snapshotEmitter` (the snapshot re-baseline's writer) + the
golden module `schemacore/SchemaCore/Goldens.lean` (the `schema`
exe's own write — SchemaMain's golden-body write; its writer
declaration lives there, named here once, provenance-commented) + the
wasm lane's rows `WasmCore.watEmitter` + `WasmCore.wasmSliceEmitter`
(the `just wasmgen` write path — the BINARY lane's first committed
artifact; two spec types, so TWO real-emitter lists, both folded).
The scaffold lane's generated DemoApp modules are NOT in this
surface: their writer declares no `outputs` (they byte-tie in
ScaffoldTests' own lane) — they land here when that lane grows
emitter-declared outputs (the leftover rule).

The ledger read-side (09 §4): `Kit.Ledger`'s committed file does not
exist yet (Emit.lean's own note: it lands with the first driver
wiring), so the gate reads the emitters directly — the honest source;
a committed ledger will REPLACE the emitter read as the declared set
(one consumer swap, the same verdict shape).

The negative control (mandatory, 09 §8): the gate carries a
duplicate-output FIXTURE pair (two toy emitters declaring the same
path — what the per-emitter nodup cannot see) and its run REFUSES to
pass unless the collision verdict fires on them — a broken gate fails
closed.

The five questions (notes/v3/01-core.md): none of its own — the
registry-replay preamble + the one-writer discipline's global face.
Gate row: the ownership row itself (`gates ownership`).
-/
import Lean
import Gates.Packages
import Gates.Common
import SchemaCore
import WasmCore
import Guest.Component

open Lean
open Kit (DataRegistry)
open SchemaCore (Item)

namespace Gates.Ownership

/-! ## The declared set (read from the emitters, never a hand copy) -/

/-- The REAL emitter set: the emitters whose outputs the tree's write
    paths produce — the two `just gen` lanes + the snapshot writer.
    (DemoApp's demo emitter declares NO outputs — empty by
    construction; it contributes nothing to a declared set.) -/
def realEmitters : List (Kit.Emit.Emitter (DataRegistry Item)) :=
  [SchemaCore.witEmitter, SchemaCore.Emit.Rust.rustEmitter,
   SchemaCore.Emit.Rust.commitSliceEmitter,
   SchemaCore.snapshotEmitter]

/-- The wasm lane's REAL emitters (over `WasmCore.Module` — the spec
    type differs from SchemaCore's, so the two real-emitter lists are
    separate and the verdict folds BOTH). `watEmitter` is the landed WAT
    text row (`gen/wasm-slice.wat`); `wasmSliceEmitter` the BINARY row
    (`gen/wasm-slice.wasm` + its `.hdr` sidecar — the first committed
    binary artifact). -/
def wasmEmitters : List (Kit.Emit.Emitter WasmCore.Module) :=
  [WasmCore.watEmitter, WasmCore.wasmSliceEmitter]

/-- The DUEL lane's REAL emitter (over the computed expectation list —
    the third spec type; the `just wasmgen` write path's duel rows: the
    manifest `gen/wasm-duel/manifest.txt` + the six vectors, each with
    its `.hdr` sidecar). -/
def duelEmitters :
    List (Kit.Emit.Emitter (List (String × Kit.Duel.Expect))) :=
  [WasmCore.Duel.duelEmitter]

/-- The COMPONENT lane's REAL emitter (over `Guest.Component.Spec` —
    the fourth spec type; the `just componentgen` write path: the
    world text `gen/component-slice.wit` + the component bytes
    `gen/component-slice.wasm` + its `.hdr` sidecar). The emitter is
    PURE (Guest.Component imports no Lean compiler machinery at its
    own face — the LCNF re-run lives in the driver). -/
def componentEmitters : List (Kit.Emit.Emitter Guest.Component.Spec) :=
  [Guest.Component.componentEmitter, Guest.Component.stringComponentEmitter]

/-- The golden module: the `schema` exe's own write (SchemaMain's
    golden-body write — the byte-tie's theorem face). NOT an emitter
    output; the writer's declaration lives in SchemaMain, named here
    once so the declared-vs-actual agreement covers it too. -/
def goldenModule : String := "schemacore/SchemaCore/Goldens.lean"

/-- The declared output set: the real emitters' declared paths (ALL
    the real sets — SchemaCore's, the wasm lane's, the duel lane's;
    text + binary lanes, ONE path namespace, Emit.lean's rule),
    deduplicated (the collision face is checked SEPARATELY — dedup
    here never hides it), plus the golden module (the exe's own
    write). -/
def declaredOutputs : List String :=
  let fromEmitters :=
    ((realEmitters.map fun e => e.outputs ++ e.binaryOutputs).flatten
      ++ (wasmEmitters.map fun e => e.outputs ++ e.binaryOutputs).flatten
      ++ (duelEmitters.map fun e => e.outputs ++ e.binaryOutputs).flatten
      ++ (componentEmitters.map fun e => e.outputs ++ e.binaryOutputs).flatten)
  let deduped :=
    (List.foldl (fun acc p => if acc.contains p then acc else p :: acc)
      [] fromEmitters).reverse
  deduped ++ [goldenModule]

/-! ## The on-disk set (walked from the artifact roots) -/

/-- One generated-artifact scan root: a directory (relative to the
    repo root) + a required extension (`""` = every file under it). -/
structure ScanRoot where
  dir : String
  ext : String

/-- The scan roots (the tree's layout): the whole `gen/` directory +
    the generated crate's Rust dirs. A committed-or-not file under a
    root is artifact surface either way (the disk is stricter than
    the VCS — it catches the uncommitted squatter before the commit). -/
def scanRoots : List ScanRoot :=
  [ { dir := "gen", ext := "" }
  , { dir := "crates/schema-generated/src", ext := "rs" }
  , { dir := "crates/schema-generated/tests", ext := "rs" } ]

/-- The recursive directory walk, as an explicit worklist loop (the
    linter's noNewPartial rule: no new `partial` — the file-system
    tree is walked by an explicit stack, structurally on the stack's
    own consumption). Absent roots sweep empty. -/
def walk (root : System.FilePath) : IO (List String) := do
  let mut acc : List String := []
  let mut stack : List System.FilePath := [root]
  repeat
    match stack with
    | [] => break
    | dir :: rest =>
      stack := rest
      unless ← dir.pathExists do continue
      let entries ← dir.readDir
      for e in entries do
        if ← e.path.isDir then
          stack := e.path :: stack
        else
          acc := e.path.toString :: acc
  pure acc.reverse

/-- The files a root sweeps (the extension filter applied). -/
def rootFiles (r : ScanRoot) : IO (List String) := do
  let all ← walk r.dir
  pure (if r.ext.isEmpty then all
        else all.filter (·.endsWith ("." ++ r.ext)))

/-! ## The verdict (ctors, never strings — 09 §8) -/

/-- One ownership finding. -/
inductive OwnershipFinding where
  /-- On disk under a generated root, declared by NO emitter. -/
  | orphan (path : String)
  /-- Declared, but no committed file. -/
  | missing (path : String)
  /-- Declared by MORE THAN ONE emitter (the cross-emitter
      one-writer face). -/
  | collision (path : String)
  deriving DecidableEq

/-- The gate's verdict. -/
inductive OwnershipVerdict where
  /-- Clean: the declared/actual agreement holds both directions and
      the emitters' declared outputs are pairwise disjoint. -/
  | clean (declared onDisk : Nat)
  /-- Findings (any nonempty set). -/
  | dirty (fs : List OwnershipFinding)

/-- The paths declared by more than one emitter (the report face of a
    false `Kit.Emit.outputsDisjoint` — the Bool is the kit's; these
    name the paths). -/
def collisionFindings (emitterOutputs : List (List String)) :
    List OwnershipFinding :=
  let all := emitterOutputs.flatten
  let uniq :=
    (List.foldl (fun acc p => if acc.contains p then acc else p :: acc)
      [] all).reverse
  uniq.filterMap fun p =>
    if emitterOutputs.countP (·.contains p) > 1 then some (.collision p)
    else none

/-- The pure ownership verdict: declared-vs-actual both directions
    (`absent` = the declared paths the disk lacks — computed by the
    IO shell) + the cross-emitter collisions. -/
def verdict (declared onDisk absent : List String)
    (emitterOutputs : List (List String)) : OwnershipVerdict :=
  let fs := (onDisk.filter (fun p => !declared.contains p)).map .orphan
    ++ absent.map .missing
    ++ collisionFindings emitterOutputs
  if fs.isEmpty then .clean declared.length onDisk.length
  else .dirty fs

/-! ## The negative control (the gate's own tooth) -/

/-- The fixture pair: two toy emitters declaring the SAME output — the
    cross-emitter collision the per-emitter nodup cannot see. -/
def fixtureA : Kit.Emit.Emitter (List String) where
  name := "ownership-fixture-a"
  style := .lean
  specSource := "-"
  outputs := ["gen/shared-fixture.txt"]
  run := fun _ => []

def fixtureB : Kit.Emit.Emitter (List String) where
  name := "ownership-fixture-b"
  style := .lean
  specSource := "-"
  outputs := ["gen/shared-fixture.txt"]
  run := fun _ => []

/-- The negative control: the collision verdict MUST fire on the
    fixture pair, and the kit's `outputsDisjoint` MUST be false there.
    The gate's run refuses to pass if not — fail closed. -/
def selfCheck : Bool :=
  !(Kit.Emit.outputsDisjoint [fixtureA, fixtureB])
    && collisionFindings [fixtureA.outputs, fixtureB.outputs]
      == [.collision "gen/shared-fixture.txt"]

/-! ## The gate -/

/-- `gates ownership` — the declared-vs-actual agreement (both
    directions) over the generated-artifact roots + the real emitter
    set's cross-emitter disjointness. Exit 1 on any finding or a
    failed self-check. -/
unsafe def run : IO UInt32 := do
  unless selfCheck do
    IO.eprintln "ownership: SELF-CHECK FAILED — the duplicate-output \
      fixture did not fire (the gate's tooth is broken; fail closed)"
    return 1
  let declared := declaredOutputs
  -- the on-disk set, walked from the roots
  let mut onDisk : List String := []
  for r in scanRoots do
    onDisk := onDisk ++ (← rootFiles r)
  onDisk := onDisk.toArray.qsort (fun a b => a <= b) |>.toList
  -- the declared paths the disk lacks
  let mut absent : List String := []
  for p in declared do
    unless ← (p : System.FilePath).pathExists do
      absent := p :: absent
  -- BOTH real sets fold the verdict; the cross-set disjointness is the
  -- flattened Nodup (outputsDisjoint is per-spec-list — the two sets'
  -- spec types differ — so the cross-set face is the explicit fold).
  let realOutputs := realEmitters.map fun e => e.outputs ++ e.binaryOutputs
  let wasmOutputs := wasmEmitters.map fun e => e.outputs ++ e.binaryOutputs
  let duelOutputs := duelEmitters.map fun e => e.outputs ++ e.binaryOutputs
  let componentOutputs := componentEmitters.map fun e => e.outputs ++ e.binaryOutputs
  let v := verdict declared onDisk absent.reverse
    (realOutputs ++ wasmOutputs ++ duelOutputs ++ componentOutputs)
  -- the kits' cross-emitter verdicts over the REAL sets (exercised,
  -- not assumed; the collision rows above name the paths) + the
  -- cross-set one-writer face.
  let disjoint := Kit.Emit.outputsDisjoint realEmitters
    && Kit.Emit.outputsDisjoint wasmEmitters
    && Kit.Emit.outputsDisjoint duelEmitters
    && Kit.Emit.outputsDisjoint componentEmitters
    && decide ((realOutputs ++ wasmOutputs ++ duelOutputs ++ componentOutputs).flatten.Nodup)
  match v with
  | .clean d o =>
      unless disjoint do
        IO.eprintln "ownership: outputsDisjoint = false over the real \
          emitter set with no collision row — the report and the kit \
          disagree (a gate bug; fail closed)"
        return 1
      IO.println s!"ownership: clean — {d} declared output(s), {o} \
        on-disk artifact(s) under the roots, declared-vs-actual agrees \
        both ways, emitters pairwise disjoint (Kit.Emit.outputsDisjoint \
        = true over ALL real sets — SchemaCore + the wasm lane + the \
        duel lane + the component lane — cross-set flatten nodup); \
        collision negative control: fired"
      return 0
  | .dirty fs =>
      for f in fs do
        match f with
        | .orphan p =>
            IO.eprintln s!"ownership: ORPHAN {p} — on disk under a \
              generated root but declared by NO emitter (the invisible \
              squatter); delete it or declare it in an emitter's outputs"
        | .missing p =>
            IO.eprintln s!"ownership: MISSING {p} — declared but absent; \
              run `just gen` (or the artifact's own re-baseline) and commit"
        | .collision p =>
            IO.eprintln s!"ownership: COLLISION {p} — declared by more \
              than one emitter (the one-writer rule's cross-emitter face)"
      unless disjoint do
        IO.eprintln s!"ownership: Kit.Emit.outputsDisjoint = false over \
          the real emitter sets ({realEmitters.length} SchemaCore + \
          {wasmEmitters.length} wasm + {duelEmitters.length} duel + \
          {componentEmitters.length} component)"
      return 1

end Gates.Ownership
