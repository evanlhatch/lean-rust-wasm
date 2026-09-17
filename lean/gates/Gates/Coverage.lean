/-
# Gates.Coverage — the coverage matrix as data (`gates coverage`)

Closes the "no coverage gate" gap (notes/review-2026-09-16). The matrix:
the boundary universe's `Ty` constructors (SchemaLang.Ty — the CLOSED
universe; a new ctor breaks every emitter by exhaustiveness, and this
table's rows are the ctors) × the registered emitters
(`SchemaLang.Emit.emitters`, read from the registry — never a hand copy)
× the oracle's replay surface (wasm-backend's `Oracle.schemaSigs`).

How a cell is classified (measured, not assumed):

- EMITTER cells are PROBE-DIFFERENTIAL. For each ctor, a probe item (a
  record field AND a func signature carrying the ctor — funcs only for
  `future`/`stream`, which record fields ban) is added to the replayed
  Demo+flags registry (the same ctx gen-check uses) and each emitter is
  re-run IN PROCESS over the extended ctx. Output bytes changed =
  exercised (the emitter has a live code path for the ctor on a real
  spec); identical = quiet (the ctor never reaches the artifact).
  Emitters are pure `GenCtx → List GeneratedFile` (the emitter
  contract), so this is exact, not sampling.
- The ORACLE column: two evidence sources, kept distinct because the tree
  has TWO demo worlds (measured, 2026-09-17 — see FINDING below):
  (i) the schema-registered gateway world (`Demo`-root func items) — a
      replayed fn matching a registry item contributes its signature's
      ctors (typed link, exact);
  (ii) the wasm-backend demo world (`demo-world.wit` + `DemoFn`'s
      `@[guest]` fns — HAND-MAINTAINED, not schema-registered): its 14
      replayed fns have no registry items, so the evidence is the
      PROJECTION `featureTyTags` of the oracle's own `featuresOf` tags
      (`u64-scalar` → `u64`, `stream-record` → `stream`,`ty`, …).
  FINDING (the two-worlds gap): the differential oracle's surface is
  mostly the hand-written wasm demo world; the coverage gate cannot
  check those signatures against the boundary universe. Unifying the
  wasm demo world with the schema registry is the fix — a separate
  order, not a fake column here.

Findings: a ctor quiet across EVERY emitter AND absent from the oracle
surface is an unexercised member of the closed universe — printed as a
finding. `--strict` fails on any such ctor. Default mode diffs the
rendered matrix against the committed `notes/coverage-matrix.md`
(`--write` updates it; the diff is the CI gate — a coverage REGRESSION
or a new ctor's arrival fails even while today's absolute coverage has
honest gaps). A replayed oracle fn with no matching registry item is
structural drift and always fails.

LEGACY (non-module) file: meta env-extension access via Gates.Common
(constraint 12, notes/w5-4-module-migration.md).
-/
import Gates.Common
import Oracle

open Lean
open SchemaLang (Item Ty)
open SchemaLang.Emit (GenCtx)
open CodegenCore.Emit (Emitter GeneratedFile kebab)

namespace Gates.Coverage

/-- The closed boundary universe, one row per `Ty` ctor: tag name + a
    minimal sample instance (probes carry it into the registry). The
    universe is closed (doctrine §1): a new ctor must extend this table
    AND every emitter — the exhaustiveness compile errors land first, so
    this table cannot silently lag. -/
def tyUniverse : List (String × Ty) :=
  [ ("bool",   .bool)
  , ("u8",     .u8), ("u16", .u16), ("u32", .u32), ("u64", .u64)
  , ("i8",     .i8), ("i16", .i16), ("i32", .i32), ("i64", .i64)
  , ("f32",    .f32), ("f64", .f64)
  , ("string", .string)
  , ("bytes",  .bytes)
  , ("option", .option .bool)
  , ("result", .result .bool .bool)
  , ("list",   .list .string)
  , ("map",    .map .string .u64)  -- W8.1: scalar key (the KeyTy gate)
  , ("set",    .set .string)
  , ("future", .future .u64)
  , ("stream", .stream .u64)
  , ("tensor", .tensor [2] .u64)
  , ("ty",     .ty "User")   -- the demo registry's record — refs must resolve
  ]

/-- The ctor tags of a type, transitively (the tag strings of
    `tyUniverse`). -/
def tagsOf : Ty → List String
  | .bool => ["bool"]
  | .u8 => ["u8"] | .u16 => ["u16"] | .u32 => ["u32"] | .u64 => ["u64"]
  | .i8 => ["i8"] | .i16 => ["i16"] | .i32 => ["i32"] | .i64 => ["i64"]
  | .f32 => ["f32"] | .f64 => ["f64"]
  | .string => ["string"] | .bytes => ["bytes"]
  | .option a => "option" :: tagsOf a
  | .result ok err => "result" :: tagsOf ok ++ tagsOf err
  | .list a => "list" :: tagsOf a
  -- the key is a `KeyTy` scalar: its tag rides the row name (the
  -- sample's own tag); only the VALUE's tags are transitive
  | .map _ v => "map" :: tagsOf v
  | .set _ => ["set"]
  | .future a => "future" :: tagsOf a
  | .stream a => "stream" :: tagsOf a
  | .tensor _ a => "tensor" :: tagsOf a
  | .ty _ => ["ty"]

/-- The probe items for one ctor: a func carrying the sample in its
    signature, plus (for the ctors record fields may carry — async types
    are banned there by `universeCheck`) a record field. -/
def probesOf (cname : String) (sample : Ty) : List Item :=
  let fn : Item := .func { name := s!"gates-probe-{cname}"
                         , params := [("x", sample)], ret := sample }
  if cname == "future" || cname == "stream" then [fn]
  else [fn, .record s!"GatesProbe-{cname}" [{ name := "f", ty := sample }]]

/-- The ctx with probe items routed into the `Demo` root (the world
    emitters fold `ctx.rootItems `Demo`; the item-universe emitters read
    `ctx.items`). -/
def withProbes (ctx : GenCtx) (probes : List Item) : GenCtx :=
  { ctx with
    items := ctx.items ++ probes
    roots := ctx.roots.map fun (r, its) =>
      if r == `Demo then (r, its ++ probes) else (r, its) }

/-- An emitter's output as comparable data (path × content pairs; the
    BEq compare forces the strings — the pure fold is fully evaluated). -/
def outsOf (e : Emitter GenCtx) (ctx : GenCtx) : List (String × String) :=
  (e.run ctx).map fun f => (f.path, f.contents)

/-- The full matrix: rows = Ty ctors (tyUniverse's order), columns =
    emitters + the oracle. -/
structure Matrix where
  emitterNames : Array String
  /-- `cells[r][c]` — ctor r is exercised by emitter c. -/
  cells : Array (Array Bool)
  /-- Oracle coverage per ctor row. -/
  oracle : Array Bool
  /-- Replayed oracle fns with no schema-registry item (the hand-written
      wasm demo world — informational; see the header's FINDING). -/
  wasmWorldOnlyFns : List String
  /-- Gateway-world funcs the oracle never replays (informational). -/
  unreplayedExports : List String

/-- The type-bearing oracle feature tags → the Ty ctors they exercise.
    A PROJECTION of wasm-backend `Oracle.featuresOf` (consumed, not
    re-encoded: the tags come from `featuresOf` at runtime; this table
    only names which tags carry a type-ctor claim). Tags not listed make
    no type-ctor claim (`wrapping-arith`, `closure-pap`, the validator
    gates, …). -/
def featureTyTags : List (String × List String) :=
  [ ("u64-scalar", ["u64"])
  , ("bool-arg", ["bool"]), ("bool-result", ["bool"])
  , ("string-result", ["string"]), ("string-intrinsic", ["string"])
  , ("record-arg", ["ty"]), ("record-result", ["ty"]), ("variant-arg", ["ty"])
  , ("option-result", ["option"])
  , ("list-of-string", ["list", "string"])
  , ("stream-u64", ["stream", "u64"]), ("stream-record", ["stream", "ty"])
  , ("f64-payload-arm", ["f64"]) ]

/-- Compute the matrix over the replayed registry: one baseline run per
    emitter, then one probe run per (ctor × emitter). -/
unsafe def computeMatrix : IO Matrix := do
  let ctx ← Gates.loadGenCtx
  let es := SchemaLang.Emit.emitters
  let bases := es.map fun e => outsOf e ctx
  let mut cells : Array (Array Bool) := #[]
  for (cname, sample) in tyUniverse do
    let ctx' := withProbes ctx (probesOf cname sample)
    let row := (es.zip bases).map fun (e, base) => outsOf e ctx' != base
    cells := cells.push row.toArray
  -- the oracle axis: (i) registry-linked rows + (ii) the featuresOf
  -- projection for the hand-written wasm demo world's rows
  let demoItems := ctx.rootItems `Demo
  let replayed := schemaSigs.map (·.1)
  let sigTys := replayed.flatMap fun fn =>
    match demoItems.find? (fun it => it.name == fn || kebab it.name == fn) with
    | some (.func sig) => sig.params.map (·.2) ++ [sig.ret]
    | _ => []
  let featureTags := (replayed.flatMap featuresOf).eraseDups
  let projected := featureTags.flatMap fun t =>
    (featureTyTags.find? (·.1 == t)).map (·.2) |>.getD []
  let oracleTags := (sigTys.flatMap tagsOf ++ projected).eraseDups
  let oracleCov := tyUniverse.toArray.map fun (cname, _) => oracleTags.contains cname
  let wasmOnly := replayed.filter fun fn =>
    !demoItems.any (fun it => it.name == fn || kebab it.name == fn)
  let unreplayed := demoItems.filterMap fun it =>
    match it with
    | .func sig =>
      if replayed.contains sig.name || replayed.contains (kebab sig.name) then none
      else some sig.name
    | _ => none
  return { emitterNames := es.toArray.map (·.name), cells, oracle := oracleCov
         , wasmWorldOnlyFns := wasmOnly, unreplayedExports := unreplayed }

/-- A row's fully-quiet verdict: no emitter exercises the ctor and the
    oracle doesn't cover it. -/
def Matrix.quietCtors (m : Matrix) : List String :=
  ((tyUniverse.zip m.cells.toList).zip m.oracle.toList).filterMap
    fun (((cname, _), row), oc) =>
      if row.all (!·) && !oc then some cname else none

def render (m : Matrix) (quiet : List String) : String := Id.run do
  let cols := m.emitterNames.toList
  let mut lines : List String :=
    [ "# Coverage matrix — the boundary universe's exercise surface"
    , ""
    , "GENERATED by `lake exe gates coverage --write` (lean/gates) — do not hand-edit."
    , "CI runs `gates coverage`; a diff against this file = a coverage-surface change (the gate)."
    , ""
    , "Rows: the closed `Ty` universe (SchemaLang.Ty). Columns: the registered emitters"
    , "(probe-differential: a probe item carrying the ctor is added to the replayed"
    , "registry and the emitter re-run — `x` = output bytes changed, `.` = quiet) plus"
    , "`oracle` (the ctor is exercised by a replayed oracle row — via a registry-linked"
    , "signature where one exists, else the featureTyTags projection of the oracle's"
    , "own featuresOf tags; see the two-worlds finding below)."
    , "" ]
  lines := lines ++
    [ "| Ty ctor | " ++ String.intercalate " | " cols ++ " | oracle |"
    , "| --- |" ++ String.intercalate "" (cols.map fun _ => " --- |") ++ " --- |" ]
  for (((cname, _), row), oc) in (tyUniverse.zip m.cells.toList).zip m.oracle.toList do
    let cell (b : Bool) := if b then "x" else "."
    lines := lines ++
      [ "| `" ++ cname ++ "` | "
        ++ String.intercalate " | " (row.toList.map cell)
        ++ " | " ++ cell oc ++ " |" ]
  lines := lines ++ [""]
  lines := lines ++
    [ "## Fully-quiet ctors (no emitter exercises them; the oracle never sees them)"
    , "" ]
  if quiet.isEmpty then
    lines := lines ++ ["(none)"]
  else
    lines := lines ++ (quiet.map fun c => s!"- `{c}`")
  lines := lines ++ [""]
  if m.unreplayedExports.isEmpty then
    lines := lines ++ ["Every gateway-world export has ≥1 oracle row."]
  else
    lines := lines ++
      [ "## Gateway-world exports the oracle never replays (informational)"
      , "" ]
      ++ (m.unreplayedExports.map fun f => s!"- `{f}`")
  lines := lines ++
    [ ""
    , "## The two demo worlds (the two-worlds finding)"
    , ""
    , "The schema-registered gateway world (this registry) and the wasm-backend demo"
    , "world (`demo-world.wit` + `DemoFn`, hand-maintained) are DISJOINT surfaces. The"
    , "differential oracle replays the wasm demo world; the oracle column's evidence"
    , "for those rows is the `featureTyTags` projection of the oracle's own"
    , "`featuresOf`, not a typed registry link. Replayed fns with no registry item:"
    , "" ]
    ++ (m.wasmWorldOnlyFns.map fun f => s!"- `{f}`")
  return String.intercalate "\n" lines

/-- The committed baseline this gate diffs against. -/
def baselinePath : System.FilePath := "../../notes/coverage-matrix.md"

unsafe def run (write strict : Bool) : IO UInt32 := do
  let m ← computeMatrix
  let quiet := m.quietCtors
  let text := render m quiet
  -- stdout: the matrix + the findings (the gate's log is the report)
  IO.println text
  let mut failed := false
  if !quiet.isEmpty then
    IO.println ""
    IO.println s!"coverage: {quiet.length} fully-quiet ctor(s) — unexercised members \
      of the closed universe (findings, not failures; `--strict` promotes): \
      {String.intercalate ", " quiet}"
  if strict && !quiet.isEmpty then failed := true
  if write then
    IO.FS.writeFile baselinePath (text ++ "\n")
    IO.println s!"wrote {baselinePath}"
  else
    if ← baselinePath.pathExists then
      let committed ← IO.FS.readFile baselinePath
      if committed != text ++ "\n" then
        IO.println s!"coverage: matrix DRIFTED from {baselinePath} — \
          the coverage surface changed; run `lake exe gates coverage --write` and commit"
        failed := true
    else
      IO.println s!"coverage: {baselinePath} absent — run `lake exe gates coverage --write` and commit"
      failed := true
  if failed then return 1
  IO.println "coverage: matrix in sync with the committed baseline"
  return 0

end Gates.Coverage
