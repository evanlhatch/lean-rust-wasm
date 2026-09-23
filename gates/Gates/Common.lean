/-
Gates.Common — the shared registry-replay preamble + the report-gate
combinator (mined from legacy/lean/gates/Gates/Common.lean's
`Gates.Driver` tails).

The combinator's contract: the write-or-diff baseline tail shared by the
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

namespace Gates

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

end Driver

end Gates
