/-
# SchemaLang.SchemaMain — unified driver: schema gen|check|breaking

Dispatches to SchemaGenMain, CheckMain, or BreakingMain through the Cli
package (the gates-exe house pattern — W5.4 hygiene batch retired the
hand-rolled subcommand match). All three share the CodegenCore
registry-load preamble (`importModulesReplayed` / `loadRegisteredItems`),
which lives in each submodule's `run` rather than duplicated inline.

Usage:
  lake exe schema gen       — regenerate all artifacts (SchemaGenMain)
  lake exe schema check     — type-check the demo universe (CheckMain)
  lake exe schema breaking  — compat diff vs baseline (BreakingMain)
  lake exe schema breaking --update  — rewrite baseline
-/
import Cli
import SchemaGenMain
import CheckMain
import BreakingMain

open Cli

unsafe def runGenCli (_p : Parsed) : IO UInt32 := runGen []

unsafe def runCheckCli (_p : Parsed) : IO UInt32 := runCheck []

/-- `--update` is BreakingMain's flag; the Parsed form lands there. -/
unsafe def runBreakingCli (p : Parsed) : IO UInt32 := runBreaking p

/-- Missing subcommand: help to stdout, exit 1 (the old matcher's
    usage-error behavior; `-h` still exits 0 via Cli.validate). -/
unsafe def schemaRoot (_p : Parsed) : IO UInt32 := do
  IO.eprintln "schema: missing subcommand"
  IO.eprintln "Usage: schema gen | check | breaking [--update]"
  return 1

unsafe def genCmd : Cmd := `[Cli|
  "gen" VIA runGenCli; ["0.1.0"]
  "Regenerate all artifacts (SchemaGenMain)."
]

unsafe def checkCmd : Cmd := `[Cli|
  "check" VIA runCheckCli; ["0.1.0"]
  "Type-check the demo universe (CheckMain)."
]

unsafe def breakingCmd : Cmd := `[Cli|
  "breaking" VIA runBreakingCli; ["0.1.0"]
  "Compat diff vs the committed baseline goldens/universe.snapshot \
   (BreakingMain)."

  FLAGS:
    update; "Rewrite the baseline (the deliberate-change path)."
]

unsafe def schemaCmd : Cmd := `[Cli|
  "schema" VIA schemaRoot; ["0.1.0"]
  "The schema language's unified driver."

  SUBCOMMANDS: genCmd; checkCmd; breakingCmd
]

unsafe def main (args : List String) : IO UInt32 :=
  schemaCmd.validate args
