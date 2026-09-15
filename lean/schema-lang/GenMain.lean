/-
# SchemaLang.GenMain — the artifact writer (the buf driver)

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
import Demo

open Lean SchemaLang.Meta

open SchemaLang.Emit (emitters)
open CodegenCore.Emit (header runEmitters)

unsafe def main : IO Unit := do
  -- Replay BOTH spec modules' registrations (loadExts; `lake exe`
  -- supplies LEAN_PATH for the package's own deps — the flags package
  -- joins via the extra search path, its oleans built by `just
  -- lean-build` BEFORE the gen driver runs, the gates' order). TWO
  -- environments, not one: both spec modules define the root-level
  -- `Async.Future`/`Async.Stream` boundary markers (the reifier matches
  -- them BY NAME — one copy in SchemaLang.Meta is the tracked fix, and
  -- Demo.lean is not this driver's to edit), so a joint import fails on
  -- the duplicate constant. Each env replays its own registry; the
  -- merger is the registry concatenation (demo first — the extension's
  -- append order), the partition still DERIVED (`rootPartitionOf` per
  -- env: the declaring module per item — never a hand list).
  let paths : List System.FilePath :=
    [("../feature-flags/.lake/build/lib" : System.FilePath),
     ("../feature-flags/.lake/build/lib/lean" : System.FilePath)]
  let demoEnv ← CodegenCore.importModulesReplayed #[`Demo]
  let flagsEnv ← CodegenCore.importModulesReplayed #[`FeatureFlags] paths
  let named := SchemaLang.Emit.namedByModule demoEnv (registeredItems demoEnv)
    ++ SchemaLang.Emit.namedByModule flagsEnv (registeredItems flagsEnv)
  let ctx : SchemaLang.Emit.GenCtx :=
    { items := named.map (·.2)
    , roots := SchemaLang.Emit.groupByRoot named
      -- the invariant/update lanes stay demo-only (the flags package
      -- registers none yet); the concat keeps the merger total when
      -- the flags lane lands its rows
    , invariants := registeredInvariants demoEnv ++ registeredInvariants flagsEnv
    , updates := registeredUpdates demoEnv ++ registeredUpdates flagsEnv }
  -- The generation metadata: ONE assembly (the clock + git), shared by
  -- every artifact this run writes. The emitters stay pure.
  let gm ← CodegenCore.Emit.genMeta ctx.items.length 0
  runEmitters "schema-lang" (emitters.map (λ e => (e, ctx)))
    (λ _ f => pure { gm with contentHash := f.contents.hash })
