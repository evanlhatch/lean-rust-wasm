/-
# SchemaLang.SchemaMain — unified driver: schema gen|check|breaking

Dispatches to SchemaGenMain, CheckMain, or BreakingMain based on the first
CLI argument. All three share the CodegenCore registry-load preamble
(`importModulesReplayed` / `loadRegisteredItems`), now lives in each
submodule's `run` rather than duplicated inline.

Usage:
  lake exe schema gen       — regenerate all artifacts (SchemaGenMain)
  lake exe schema check     — type-check the demo universe (CheckMain)
  lake exe schema breaking  — compat diff vs baseline (BreakingMain)
  lake exe schema breaking --update  — rewrite baseline
-/
import SchemaGenMain
import CheckMain
import BreakingMain

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | subcommand :: rest =>
    match subcommand with
    | "gen"      => runGen rest
    | "check"    => runCheck rest
    | "breaking" => runBreaking rest
    | _ =>
      IO.eprintln s!"schema: unknown subcommand '{subcommand}'"
      IO.eprintln "Usage: schema gen | check | breaking [--update]"
      return 1
  | _ =>
    IO.eprintln "schema: missing subcommand"
    IO.eprintln "Usage: schema gen | check | breaking [--update]"
    return 1