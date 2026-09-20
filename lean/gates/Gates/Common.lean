/- # Gates.Common — the shared registry-replay preamble

The demo+flags `GenCtx` assembly now lives in SchemaLang.GenCtxIO
(`loadGenCtx` — the former byte-duplicate of SchemaGenMain.runGen's
preamble, deduped); this is the gates-side NAME the two consumers
(`GenCheck`, `Coverage`) already call.

Also home of the shared DRIVER tails (R4, namespace `Gates.Driver`):
the two tails the gate modules verifiably duplicate are (a) the
`--package X` shard filter (Axioms, NativePolicy, KernelCheck) and (b)
the write-or-diff baseline tail (Axioms whole-file mode, Coverage).
The modules WITHOUT a committed baseline (GenCheck compares in-memory;
NativePolicy/KernelCheck verdicts are computed, never stored) and
KernelCheck's lean4lean spawning (subprocess, different verdict shape)
do NOT fit `reportGate` — they keep their tails and reuse only the
filter. `reportGate` composes its drift/absent lines from the gate name
+ two gate-specific fragments so the printed text stays byte-identical
to the pre-combinator output the justfile and humans parse.

LEGACY (non-module) file BY DESIGN: it (transitively) calls the meta
env-extension accessors (`registeredItems` etc.) — constraint 12 of
notes/w5-4-module-migration.md (drivers touching meta env extensions
stay legacy).

Paths: every recipe runs this exe from `lean/gates` (`cd lean/gates &&
lake exe gates …`), the same depth as `lean/schema-lang`, so GenMain's
`../feature-flags/…` extra-path convention worked unchanged (and its
death with the SINGLE-LAKE absorb hit both copies identically).
-/
import Lean
import Gates.Packages
import SchemaLang.Emit.Registry
import SchemaLang.GenCtxIO

open Lean SchemaLang.Meta

namespace Gates

/-- The full registry state (demo + flags worlds), replayed from oleans.
    The emitters stay pure; this is the one IO preamble. -/
unsafe def loadGenCtx : IO SchemaLang.Emit.GenCtx :=
  SchemaLang.Emit.loadGenCtx

/-! ## The shared gate-driver tails (R4) -/

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

/-- The write-or-diff baseline tail shared by the baseline-report gates
    (Axioms whole-file mode, Coverage). `--write` writes `fresh ++ "\n"`
    and prints `wrote <path>`; otherwise the committed file is diffed
    and the gate's drift/absent line printed. `what` names the artifact
    in the drift line ("report" / "matrix"), `why` is the gate's reason
    fragment — both composed so the message is byte-identical to the
    pre-combinator text. Returns the exit code: 1 on drift/absent/`failed`,
    else 0 after the gate's clean line. -/
def reportGate (gate what why : String) (baseline : System.FilePath)
    (fresh : String) (write failed : Bool) (cleanMsg : String) :
    IO UInt32 := do
  let mut failed := failed
  if write then
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

/-- The `--package X` shard filter: `none` = every gated package (the
    caller's whole-file mode), `some d` = that one package. An unknown
    name prints the standard error line (stderr) and returns `none` —
    the call site exits 1. -/
def selectPackages (gate : String) (name : Option String) :
    IO (Option (Array PkgSpec)) := do
  match name with
  | none => return some gatedPackages
  | some d =>
    match gatedPackages.find? (fun p : PkgSpec => p.dir == d) with
    | some p => return some #[p]
    | none =>
      IO.eprintln s!"{gate}: unknown --package '{d}' — gated: \
        {String.intercalate ", " (gatedPackages.map (·.dir)).toList}"
      return none

end Driver

end Gates
