/-
KitTests.Cli — the ONE exe-driver's teeth (design-wave-30 C7)

The pins: the verdict→exit mapping (one mapping, the closed three),
the shared-flag parse (the shared three + the extras + the rest), the
UNKNOWN-FLAG curated failure (the closed-world Diag — the did-you-mean
is filled by the ONE engine, a miss cannot render bare), the multi-word
subcommand dispatch (longest row wins), and the help-from-table
generation (every row's name + summary render — a help that drifts from
the table is impossible by construction, the pin that proves the
construction). Negative controls: a drifted help admits a non-table
row (must fail), a loose dispatch accepts an unknown subcommand (must
fail), a loose flag parse accepts an unknown flag (must fail).

Evidence, not architecture — the five-question block lives in Kit.Cli's
header.
-/

import Kit.Cli
import TestingKit.Harness

open Kit.Cli
open TestingKit

@[expose] public section

/-! ## fixtures -/

/-- The demo table: one multi-word row (the `ledger backward` shape) +
two singles. -/
def demoSubs : List Sub :=
  [ { name := "ledger backward"
      summary := "the artifact's demand surface"
      run := fun _ => return 0 }
  , { name := "ledger", summary := "the ledger state report",
      run := fun _ => return 0 }
  , { name := "trust", summary := "the tree's trust surface",
      run := fun _ => return 0 } ]

/-- The demo driver's exit over argv (the IO pins ride it). -/
def demoRun (args : List String) : IO UInt32 :=
  run "demo" "the demo driver" demoSubs none args

/-! ## the driver's IO half (the emitSpec pattern: the IO pins run in
the exe's `main`; their verdict folds into the spec) -/

/-- The IO faces: the unknown subcommand exits 1 through the curated
Diag; the help faces exit 0. -/
def cliDriverPins : IO Bool := do
  let miss ← demoRun ["chek"]
  let helpExit ← demoRun ["--help"]
  let bare ← demoRun []
  return miss == 1 && helpExit == 0 && bare == 0

/-! ## the spec -/

def cliSpec (driverOk : Bool) : Spec :=
  Spec.ofList "Kit.Cli — the ONE driver discipline's pins"
    (fun _ => do
      -- the exit-code discipline: ONE mapping, the closed three
      assert (Verdict.ok.exit == 0 && Verdict.finding.exit == 1 &&
          Verdict.unremedied.exit == 2) "cli.verdictExitMapping"
      -- the shared flags: the shared three parse into their slots
      match parseFlags [] ["--write", "--accept-drift", "--package=gen"] with
      | .ok f =>
          assert (f.write && f.acceptDrift && f.pkg == some "gen")
            "cli.sharedFlags"
      | .error _ => assert false "cli.sharedFlags"
      -- positionals land in `rest` (lintkit's module face)
      match parseFlags [] ["--write", "Mod.A", "Mod.B"] with
      | .ok f => assert (f.rest == ["Mod.A", "Mod.B"]) "cli.rest"
      | .error _ => assert false "cli.rest"
      -- the driver-local extras: bare + `=value` faces, has/val
      match parseFlags ["strict", "paths"] ["--strict", "--paths=a,b", "m"] with
      | .ok f =>
          assert (f.has "strict" && f.val "paths" == some "a,b") "cli.extras"
      | .error _ => assert false "cli.extras"
      -- the UNKNOWN flag: the curated failure — the did-you-mean is
      -- filled by the ONE engine, never bare
      match parseFlags [] ["--wriet"] with
      | .ok _ => assert false "cli.unknownFlagRefused"
      | .error d =>
          assert (d.got == some "--wriet" &&
              d.suggest == some " — did you mean: --write?")
            "cli.unknownFlagDidYouMean"
      -- `--package` without its value refuses (the loud miss)
      match parseFlags [] ["--package"] with
      | .ok _ => assert false "cli.packageNeedsValue"
      | .error _ => assert true "cli.packageNeedsValue"
      -- the multi-word dispatch: the longest row wins, the row gets
      -- its remaining args
      match longestMatch demoSubs ["ledger", "backward", "gen/x.wit"] with
      | some (s, n) =>
          assert (s.name == "ledger backward" && n == 2)
            "cli.longestRowWins"
      | none => assert false "cli.longestRowWins"
      -- the driver's IO half (the pins above): the unknown subcommand
      -- exits 1 through the curated Diag, the help faces exit 0
      assert driverOk "cli.driverIoFaces"
      -- the help FROM THE TABLE: every row's name + summary render
      let h := help "demo" "the demo driver" demoSubs
      assert (demoSubs.all fun s => h.contains s.name && h.contains s.summary)
        "cli.helpGeneratedFromTable"
      -- the usage line names the program
      assert (h.startsWith "usage: lake exe demo <subcommand> [flags...]")
        "cli.usageLine")
    [ ("the help admits a non-table row (drift)",
        fun _ =>
          -- MUST FAIL: a summary absent from the table cannot render
          assert ((help "demo" "" demoSubs).contains "a drifted summary")
            "control fired: the help admitted a row absent from the table")
    , ("the dispatch accepts an unknown subcommand",
        fun _ =>
          -- MUST FAIL: the closed world is the table
          assert (longestMatch demoSubs ["nosuch"] |>.isSome)
            "control fired: the dispatch accepted an unknown subcommand")
    , ("the flag parse accepts an unknown flag",
        fun _ =>
          -- MUST FAIL: the closed world is the flag spellings
          assert ((parseFlags [] ["--unheard"]).toOption |>.isSome)
            "control fired: the flag parse accepted an unknown flag") ]
    4 42
