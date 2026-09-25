/-
Gates.Coverage — the Ty-ctor × emitter coverage matrix
(`gates coverage [--write] [--accept-drift] [--strict]`; mined from
legacy/lean/gates/Gates/Coverage.lean, ported fresh at the slice's
scale).

The matrix: the closed universe's `Ty` constructors (SchemaCore.Ty — a
new ctor breaks every fold's exhaustiveness, and this table's rows are
the ctors) × the registered emitters (`SchemaCore.witEmitter` +
`SchemaCore.Emit.Rust.rustEmitter` — read from the emitters themselves,
never a hand copy).

How a cell is MEASURED, not assumed — the probe-differential, pairwise
form: for each ctor a probe item (`GatesProbe.Ref { f : <sample> }`, the
SAME probe name for every ctor) is added to the replayed registry and
each emitter re-run IN PROCESS (the emitters are pure folds — this is
exact, not sampling). A ctor's cell is `x` iff its probe output differs
from EVERY other ctor's probe output — i.e. the emitter renders the ctor
with bytes of its own. A `.` means the ctor's rendering byte-collides
with some sibling ctor's in that emitter: the declared
retraction-with-note rows surface here (the WIT lane's `set` → `list<K>`
collision is measured, not remembered).

The `registry` column: the ctor's tag occurs (transitively, keys
counted) in the COMMITTED registry's field types — the slice's
exercised ctors. A ctor quiet across the registry is an unexercised
member of the closed universe — printed as a FINDING (the slice's `set`
ctor, whose authoring gap SchemaCore.Slice names); `--strict` promotes
the findings to a failure.

The rendered matrix is baseline-committed (`notes/coverage-matrix.md`);
without `--write` a diff against the baseline IS the CI gate — a
coverage regression, a new ctor's arrival, or a rendering change fails
even while today's absolute coverage has honest gaps. The loud
re-baseline discipline rides `Driver.reportGate`.

The five questions (notes/v3/01-core.md):
- root: Universe coverage — the closed `Ty` ctor set × the emitter set.
- carrier grade: none — measured output differentials, not a crossing.
- spine reading: the interpretation stage's coverage face (every ctor
  reaches the artifact, or the gap is NAMED in the committed matrix).
- ladder rung: n/a.
- gate row: the coverage row itself (`gates coverage`).
-/
import Lean
import Gates.Packages
import Gates.Common
import SchemaCore

open Lean
open Kit (DataRegistry)
open SchemaCore (Ty KeyTy Item)

namespace Gates.Coverage

/-! ## The closed universe's rows + the tag walk -/

/-- The closed boundary universe, one row per `Ty` ctor: tag name + a
    minimal sample instance (the probe carries it into the registry).
    The universe is closed (doctrine §1): a new ctor must extend this
    table AND every emitter — the exhaustiveness compile errors land
    first, so this table cannot silently lag. -/
def tyUniverse : List (String × Ty) :=
  [ ("bool", .bool)
  , ("u64", .u64)
  , ("i64", .i64)
  , ("string", .string)
  , ("option", .option .bool)
  , ("list", .list .string)
  , ("result", .result .bool .string)
  , ("map", .map .string .u64)   -- scalar key (the KeyTy gate)
  , ("set", .set .bool)
  , ("bounded", .bounded 3) ]

/-- A `KeyTy` key's scalar tag (the same strings the `Ty` scalars use —
    the key sub-universe's ctors are Ty ctors via `toTy`). -/
def keyTags : KeyTy → List String
  | .bool => ["bool"] | .u64 => ["u64"] | .i64 => ["i64"]
  | .string => ["string"]

/-- The ctor tags of a type, transitively (the tag strings of
    `tyUniverse`). -/
def tagsOf : Ty → List String
  | .bool => ["bool"]
  | .u64 => ["u64"]
  | .i64 => ["i64"]
  | .string => ["string"]
  | .option a => "option" :: tagsOf a
  | .list a => "list" :: tagsOf a
  | .result ok err => "result" :: tagsOf ok ++ tagsOf err
  -- the key is a `KeyTy` scalar: the key contributes its scalar tag
  -- (the map's key slot is real wire surface), the value transitively
  | .map k v => "map" :: (keyTags k ++ tagsOf v)
  | .set k => "set" :: keyTags k
  | .bounded _ => ["bounded"]

/-! ## The probe-differential -/

/-- The probe item's fixed shape: the SAME name for every ctor, so two
    probe runs' outputs differ ONLY in the sample type's rendering. -/
def probeItem (sample : Ty) : Item :=
  { name := "GatesProbe.Ref", fields := [{ name := "f", ty := sample }] }

/-- The registry with one probe item appended (the nodup is decided —
    a probe colliding with a registered name refuses loudly). -/
def withProbe (items : List Item) (sample : Ty) :
    Except String (DataRegistry Item) :=
  SchemaCore.registryOfItems (items ++ [probeItem sample])

/-- An emitter's output as comparable data (path × content pairs). -/
def outsOf (e : Kit.Emit.Emitter (DataRegistry Item))
    (reg : DataRegistry Item) : List (String × String) :=
  (e.run reg).map fun f => (f.path, f.contents)

/-- The measured matrix: per ctor, per emitter, the probe output; plus
    the committed registry's ctor-tag set (the registry column). -/
structure Matrix where
  emitterNames : Array String
  /-- `probeOuts[r][c]` — ctor r's probe output under emitter c. -/
  probeOuts : Array (Array (List (String × String)))
  /-- The committed registry's ctor tags (the registry column). -/
  registryTags : List String

/-- Compute the matrix over the replayed registry: one probe run per
    (ctor × emitter). -/
def computeMatrix (items : List Item) : Except String Matrix := do
  let es : List (Kit.Emit.Emitter (DataRegistry Item)) :=
    [SchemaCore.witEmitter, SchemaCore.Emit.Rust.rustEmitter]
  let mut probeOuts : Array (Array (List (String × String))) := #[]
  for (_, sample) in tyUniverse do
    match withProbe items sample with
    | .error e => throw e
    | .ok reg =>
      probeOuts := probeOuts.push (es.map (fun e => outsOf e reg)).toArray
  let registryTags :=
    (items.flatMap fun it => it.fields.map (·.ty)).flatMap tagsOf
  return { emitterNames := (es.map (·.name)).toArray
         , probeOuts
         , registryTags }

/-- The cell measurement: ctor r's probe output under emitter c differs
    from EVERY sibling ctor's (r' ≠ r) — the ctor renders with bytes of
    its own. A false here is a byte-collision with some sibling. -/
def cellDistinct (m : Matrix) (r c : Nat) : Bool :=
  if r < m.probeOuts.size then
    let mine := m.probeOuts[r]![c]!
    (List.range m.probeOuts.size).all fun r' =>
      r' == r || m.probeOuts[r']![c]! != mine
  else false

/-- The registry-absent ctors (the findings). -/
def Matrix.quietInRegistry (m : Matrix) : List String :=
  tyUniverse.filterMap fun (cname, _) =>
    if m.registryTags.contains cname then none else some cname

/-! ## The render -/

def render (m : Matrix) (quiet : List String) : String := Id.run do
  let cols := m.emitterNames.toList
  let mut lines : List String :=
    [ "# Coverage matrix — the closed Ty universe's exercise surface"
    , ""
    , "GENERATED by `lake exe gates coverage --write` — do not hand-edit."
    , "CI runs `gates coverage`; a diff against this file = a coverage-surface change (the gate)."
    , ""
    , "Rows: the closed `Ty` universe (SchemaCore.Ty). Emitter columns are PROBE-DIFFERENTIAL:"
    , "a probe item carrying the ctor is added to the replayed registry and the emitter re-run —"
    , "`x` = the ctor renders with bytes of its own (distinct from every sibling ctor's probe),"
    , "`.` = byte-collides with some sibling ctor in that emitter (the declared"
    , "retraction-with-note rows surface here). `registry` = the ctor's tag occurs in the"
    , "committed registry's field types."
    , "" ]
  lines := lines ++
    [ "| Ty ctor | " ++ String.intercalate " | " cols ++ " | registry |"
    , "| --- |" ++ String.intercalate "" (cols.map fun _ => " --- |") ++ " --- |" ]
  for r in List.range tyUniverse.length do
    let (cname, _) := tyUniverse[r]!
    let cell (b : Bool) := if b then "x" else "."
    let row := (List.range m.emitterNames.size).map fun c =>
      cell (cellDistinct m r c)
    let regCell := cell (m.registryTags.contains cname)
    lines := lines ++
      [ "| `" ++ cname ++ "` | " ++ String.intercalate " | " row
        ++ " | " ++ regCell ++ " |" ]
  lines := lines ++ [""]
  lines := lines ++
    [ "## Registry-quiet ctors (absent from the committed registry —"
    , "unexercised members of the closed universe; findings, not failures;"
    , "`--strict` promotes)"
    , "" ]
  if quiet.isEmpty then
    lines := lines ++ ["(none)"]
  else
    lines := lines ++ (quiet.map fun c => s!"- `{c}`")
  return String.intercalate "\n" lines

/-! ## The gate -/

/-- The committed baseline this gate diffs against. -/
def baselinePath : System.FilePath := "notes/coverage-matrix.md"

/-- `gates coverage` — compute the matrix, print the findings, run the
    write-or-diff baseline tail. Exit 1 on drift/absent baseline, a
    regen failure, or (with `--strict`) any registry-quiet ctor. -/
unsafe def run (write acceptDrift strict : Bool) : IO UInt32 := do
  let pkg : PkgSpec := { dir := "SchemaCore", srcDir := "schemacore", roots := #[`SchemaCore.Slice] }
  Gates.withPkgEnv "coverage" pkg fun env => do
    match SchemaCore.regen env with
    | .error e =>
      IO.eprintln s!"coverage: REGEN FAILED — {e}"
      return 1
    | .ok r =>
      match computeMatrix r.reg.items with
      | .error e =>
        IO.eprintln s!"coverage: PROBE REFUSED — {e}"
        return 1
      | .ok m =>
        let quiet := m.quietInRegistry
        let text := render m quiet
        let mut failed := false
        unless quiet.isEmpty do
          IO.println s!"coverage: {quiet.length} registry-quiet ctor(s) — \
            unexercised members of the closed universe (findings, not \
            failures; `--strict` promotes): {String.intercalate ", " quiet}"
        if strict && !quiet.isEmpty then failed := true
        Driver.reportGate "coverage" "matrix" "the coverage surface changed"
          baselinePath text write acceptDrift failed
          "coverage: matrix in sync with the committed baseline"

end Gates.Coverage
