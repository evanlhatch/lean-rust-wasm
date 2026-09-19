/-
# SchemaLang.SchemaGenMain — the artifact writer (the buf driver)

Imports the demo module (running `@[schema]` reflection), reads ALL
THREE registries from the elaborated environment into one `GenCtx` (the
emitter contract's state: items + invariants + updates), and runs every
emitter over it. The one-writer discipline: every path is claimed by
exactly one emitter (audited in Tests), and this driver is the only
code that writes.

The runtime-registry preamble (search path + extension replay) and the
write path (parent dirs + writeFile) are CodegenCore's
(`importModulesReplayed` / `writeFileCreatingDirs`) — one copy, every
driver. The replayed modules: `Demo` (the gateway world) AND
`FeatureFlags` (the flags world) — the emitters' root-namespace
partition routes each universe to its artifact.
-/
import Lean
import SchemaLang.Emit.Registry
import SchemaLang.GenCtxIO
-- Demo stays a DIRECT import (not just the replay's runtime target): it
-- keeps the exe's build closure carrying the Demo lib, which
-- `importModulesReplayed #[`Demo]` loads from oleans at run time.
import Demo

open Lean SchemaLang.Meta

open SchemaLang.Emit (emitters)
open CodegenCore.Emit (header runEmitters)

unsafe def runGen (_args : List String) : IO UInt32 := do
  -- The registry replay (TWO environments, not one: both spec modules
  -- define the root-level `Async.Future`/`Async.Stream` boundary markers
  -- — a joint import fails on the duplicate constant; the merger is the
  -- registry concatenation, demo first) is SchemaLang.GenCtxIO's ONE
  -- copy — this driver consumed the GenCtx (the byte-duplicate that
  -- lived here and in Gates.Common was deduped there).
  let ctx ← SchemaLang.Emit.loadGenCtx
  -- The generation metadata: ONE assembly (the clock + git), shared by
  -- every artifact this run writes. The emitters stay pure.
  let gm ← CodegenCore.Emit.genMeta ctx.items.length 0
  runEmitters "schema-lang" (emitters.map (λ e => (e, ctx)))
    (λ _ f => pure { gm with contentHash := f.contents.hash })
  return 0