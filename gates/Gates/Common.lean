/-
Gates.Common — the shared registry-replay preamble + the gate-tail
combinators (mined from legacy/lean/gates/Gates/Common.lean's
`Gates.Driver` tails).

`Gates.withPkgEnv`: the single-package env-load prelude (sysroot init +
loadPkgEnv + the LOAD FAILED exit) shared by the gates that load ONE
package environment and hand it to their body. Gates whose load failure
is a report row rather than a gate exit (Axioms' per-package loadError,
DocsCheck's collected loadErrors) keep their own prelude — the combinator
absorbs only the first-failure-exit shape.

`Gates.Driver.reportGate`: the write-or-diff baseline tail shared by the
baseline-report gates. `--write` writes `fresh ++ "\n"` and prints
`wrote <path>` — EXCEPT a non-empty diff (a drifted baseline) is REFUSED
unless `acceptDrift` (a re-baseline must not pre-authorize future taint;
in-sync writes and the absent-file bootstrap stay free); the refusal
names `--write --accept-drift`. Otherwise the committed file is diffed
and the gate's drift/absent line printed. Returns the exit code: 1 on
drift/absent, else 0 after the gate's clean line.

Deliberate exclusion: the legacy `selectPackages` shard filter — the
fresh tree's gates have no `--package` sharding yet (one environment per
gate run; the shard/child machinery arrives with the first gated package
heavy enough to need it — the legacy lesson: peak RSS).

The five questions (notes/v3/01-core.md):
- root: none — the baseline-tail combinator (write-or-diff + the loud
re-baseline discipline).
- carrier grade: none — driver machinery over rendered reports.
- spine reading: the artifact stage's check face (committed baseline
vs fresh render).
- ladder rung: n/a.
- gate row: the shared tail of the report gates (the axiom report's
baseline discipline is its first consumer).
-/
import Lean
import Gates.Packages

namespace Gates

/-- The single-package env-load prelude: init the search path from the
    sysroot, `loadPkgEnv`, and on failure print the gate-named LOAD
    FAILED line to stderr and exit 1; on success hand the environment to
    `k`. (Unsafe: `loadPkgEnv` runs initializers.) Deliberately NOT for
    the gates that fold several packages with per-package load-error
    rows — Axioms/DocsCheck keep their own prelude (the honest-partiality
    rule: absorb only the sites that fit). -/
unsafe def withPkgEnv (gate : String) (pkg : PkgSpec)
    (k : Lean.Environment → IO UInt32) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  match ← loadPkgEnv base pkg with
  | .error e => do
    IO.eprintln s!"{gate}: LOAD FAILED — {e}"
    return 1
  | .ok env => k env

namespace Driver

/-- Verdict of comparing the fresh render against the committed
    baseline (the on-disk contract is `render ++ "\n"` — the final
    newline is the file's, not the render's). -/
inductive Baseline where
  | inSync | drifted | absent

def diffBaseline (path : System.FilePath) (fresh : String) : IO Baseline := do
  unless ← path.pathExists do return .absent
  let committed ← IO.FS.readFile path
  return if committed == fresh ++ "\n" then .inSync else .drifted

/-- The write-or-diff baseline tail shared by the baseline-report gates.
    `what` names the artifact in the drift line ("report" / "matrix"),
    `why` is the gate's reason fragment. -/
def reportGate (gate what why : String) (baseline : System.FilePath)
    (fresh : String) (write acceptDrift failed : Bool) (cleanMsg : String) :
    IO UInt32 := do
  let mut failed := failed
  if write then
    match ← diffBaseline baseline fresh with
    | .drifted =>
      unless acceptDrift do
        IO.println s!"{gate}: --write REFUSED — non-empty diff against {baseline} \
          (a re-baseline is a deliberate act; review the diff, then rerun with --write --accept-drift)"
        return 1
      IO.FS.writeFile baseline (fresh ++ "\n")
      IO.println s!"wrote {baseline} (re-baseline accepted)"
    | _ =>
      IO.FS.writeFile baseline (fresh ++ "\n")
      IO.println s!"wrote {baseline}"
  else
    match ← diffBaseline baseline fresh with
    | .inSync => pure ()
    | .drifted =>
      IO.println s!"{gate}: {what} DRIFTED from {baseline} — {why}; \
        run `lake exe gates {gate} --write` and commit"
      failed := true
    | .absent =>
      IO.println s!"{gate}: {baseline} absent — run `lake exe gates {gate} --write` and commit"
      failed := true
  if failed then return 1
  IO.println cleanMsg
  return 0

/-- The write-or-diff core of the byte-tie gates whose committed file IS
    the artifact (SnapshotCheck, CodeRegistryCheck): an exact-bytes
    compare — unlike `reportGate`, no `fresh ++ "\\n"` newline convention
    and no accept-drift gate, because the `--write` here re-renders the
    SAME data (there is no rendered-report baseline being re-baselined).
    In sync: optionally announce the in-sync write (`inSyncWrite`; an
    in-sync write is free) then the clean line, exit 0. Drifted: with
    `--write` the deliberate, commit-visible re-render (`driftWriteMsg`,
    then the clean line too when `cleanAfterWrite` — CodeRegistryCheck
    canonicalizes and still reports clean, SnapshotCheck's re-baseline
    ends at the write line), exit 0; without, `driftMsg`, exit 1. The
    callers keep their pre-tie teeth (SnapshotCheck's parse refusal, the
    absent-file bootstraps) — they do not fit the core. -/
def byteTieGate (committed fresh : String) (write : Bool)
    (writeFile : String → IO Unit) (inSyncWrite : Option String)
    (driftWriteMsg : String) (cleanAfterWrite : Bool)
    (cleanMsg : String) (driftMsg : String) : IO UInt32 := do
  if committed == fresh then
    if write then
      if let some m := inSyncWrite then IO.println m
    IO.println cleanMsg
    return 0
  if write then
    writeFile fresh
    IO.println driftWriteMsg
    if cleanAfterWrite then IO.println cleanMsg
    return 0
  IO.println driftMsg
  return 1

end Driver
