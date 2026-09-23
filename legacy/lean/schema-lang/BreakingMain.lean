/-
# SchemaLang.BreakingMain — `just breaking` (the buf breaking analog)

Diffs the CURRENT demo registry against the committed baseline
`goldens/universe.snapshot` (`SchemaLang.Snapshot` is the codec).
Breaking findings (`Change.removed` / `Change.changed`, the latter with
field-level evidence) print to stderr. The verdict is three-way
(6.5.2, `SchemaLang.Migration.verdictOf` + `CompatVerdict.exitCode` —
the ONLY exit-code mapping):

- `clean` (additions only) → exit 0
- `remedied` (every breaking change has sound remedy evidence) →
  exit 2, a loud warning: apply the migration, then re-baseline
- `unremedied` → exit 1

The remedy evidence is `Demo.registeredMigrations` (the authoring
surface): a migration lands there with its soundness theorem, and the
gate folds it into `verdictOf`. `--update` rewrites the baseline (the
deliberate-change path — it
REFUSES to write names the line format can't round-trip).

Runs from the package root (the justfile recipe `cd`s there), like the
golden checks in Tests.
-/
import Lean
import Cli
import SchemaLang
import Demo

open Lean SchemaLang SchemaLang.Meta

/-- W5.4 hygiene batch: `--update` is a Cli flag now (the hand
    `args.contains "--update"` check is gone); SchemaMain wires this
    handler in as the `breaking` subcommand. -/
unsafe def runBreaking (p : Cli.Parsed) : IO UInt32 := do
  let items := (← CodegenCore.loadRegisteredItems schemaItemExt #[`Demo]).map (·.2)
  let path : System.FilePath := "goldens/universe.snapshot"
  if p.hasFlag "update" then
    if Snapshot.namesEncodable items then
      CodegenCore.Emit.createParentDirs path
      IO.FS.writeFile path (Snapshot.render items)
      IO.println s!"wrote {path} ({items.length} items)"
      return 0
    else
      IO.eprintln "breaking --update: FAIL — a name the snapshot format cannot round-trip:"
      for n in Snapshot.allNames items do
        if !Snapshot.nameOk n then IO.eprintln s!"  `{n}`"
      return 1
  if !(← path.pathExists) then
    IO.eprintln s!"breaking: FAIL — no baseline at {path}; commit one via `lake exe schema breaking --update`"
    return 1
  match Snapshot.parse (← IO.FS.readFile path) with
  | .error e =>
      IO.eprintln s!"breaking: FAIL — baseline {path} is corrupt: {e}"
      return 1
  | .ok baseline =>
      let changes := diff baseline items
      -- 6.5.2: the authoring surface — Demo.registeredMigrations is the
      -- remedy evidence (a migration lands there with its soundness
      -- theorem); `just breaking` reports remedied (exit 2) when it covers
      let migrations := registeredMigrations
      let verdict := verdictOf changes migrations
      let breaking := SchemaLang.breakingOf changes
      for c in changes do
        IO.println s!"  {c}"
      match verdict with
      | .clean =>
          IO.println s!"breaking: clean ({changes.length} safe change(s), {items.length} items)"
          return verdict.exitCode
      | .remedied =>
          IO.eprintln s!"breaking: REMEDIED — {breaking.length} breaking change(s) vs {path}, all with sound remedy evidence:"
          for c in breaking do
            IO.eprintln s!"  {c}"
          IO.eprintln "action required: apply the migration(s) to the event log, then re-baseline (--update)"
          return verdict.exitCode
      | .unremedied =>
          IO.eprintln s!"breaking: FAIL — {breaking.length} unremedied breaking change(s) vs {path}:"
          for c in breaking do
            IO.eprintln s!"  {c}"
          return verdict.exitCode