/-
# SnapshotFixturesMain — the snapshot-codec differential fixture writer

Emits the seeded (snapshot-text, expected-item-dump) pairs that
`crates/steel-host/tests/snapshot_differential.rs` replays through
`hostgen::parse_snapshot` (the fuzz-gap audit's gap #2: the snapshot
format's two hand-ported parsers had ZERO agreement testing). The
generator, the dump spelling, and the file format live in
`Tests/SnapshotRT.lean` (ONE copy, shared with the Lean-side PropSpec);
this driver is only the write path.

Byte-tie law: the fixture file is GENERATED with a pinned seed — a
regen is byte-identical (regen: `just snapshot-fixtures`; drift is a
reviewable diff, silence is a bug). The writer refuses (exit 1) if any
generated universe fails the Lean-authority round-trip
(`parse ∘ render = id`) — a fixture that doesn't round-trip on the
authority's own parser is a finding, not an artifact.

Usage:
  lake exe snapshot-fixtures              — write the default path
  lake exe snapshot-fixtures <path>       — write a given path
  lake exe snapshot-fixtures --stdout     — print to stdout (debug)
-/
import Tests.SnapshotRT

open SnapshotRT

unsafe def main (args : List String) : IO UInt32 := do
  let out? : Option String :=
    if args.contains "--stdout" then none
    else match args with
      | p :: _ => some p
      | [] => some "../../crates/steel-host/tests/fixtures/snapshot_fixtures.txt"
  match fixtureUniverses with
  | .error e => IO.eprintln e; return 1
  | .ok us =>
    match fixtureFile us with
    | .error e => IO.eprintln e; return 1
    | .ok contents =>
      match out? with
      | none => IO.print contents
      | some out =>
        IO.FS.createDirAll "../../crates/steel-host/tests/fixtures"
        IO.FS.writeFile out contents
        IO.println s!"snapshot-fixtures: wrote {us.length} pairs to {out} \
          ({contents.length} bytes, seed {fixtureSeed})"
    return 0
