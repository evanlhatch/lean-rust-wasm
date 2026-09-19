/-
# SchemaLang.GenCtxIO — the driver-side registry replay (the one IO preamble)

The two-environment replay + `GenCtx` build that was byte-duplicated in
`SchemaGenMain.runGen` and `Gates.Common.loadGenCtx` (whose header
admitted the copy). ONE copy here; both drivers consume.

LEGACY (non-module) file BY DESIGN: it calls the meta env-extension
accessors (`registeredItems`/`registeredInvariants`/`registeredUpdates`)
from IO code — constraint 12 of notes/w5-4-module-migration.md (drivers
touching meta env extensions stay legacy); a module-hosted version would
also trip constraint 7's meta checker at the seam between the meta
accessors and `importModulesReplayed`'s non-meta `unsafe` body. The
guestlang-lint precedent covers the consumer side: legacy exes over meta
module code build and run green.

Why TWO environments: both spec modules declare the root-level
`Async.Future`/`Async.Stream` boundary markers (the reifier matches them
BY NAME — one copy in SchemaLang.Meta is the tracked fix, and Demo.lean
is not this file's to edit), so a joint import fails on the duplicate
constant. Each env replays its own registry; the merger is the registry
concatenation (demo first — the extension's append order), the
provenance partition still DERIVED (`groupByRoot` over the per-env
`namedByModule` — the declaring module per item, never a hand list).
-/
import Lean
import SchemaLang.Emit.Registry

open Lean SchemaLang.Meta

namespace SchemaLang.Emit

/-- The full registry state (demo + flags worlds), replayed from oleans.
    The emitters stay pure; this is the one IO preamble. -/
unsafe def loadGenCtx : IO GenCtx := do
  -- SINGLE-LAKE: the exes run under `lake`, which supplies LEAN_PATH for
  -- the package's own deps — the flags package's oleans are built by
  -- `just lean-build` BEFORE the drivers run (the gates' order). No
  -- extra search-path entries: the old `../feature-flags/.lake` paths
  -- died with the packages' own .lake dirs (passing nonexistent dirs
  -- was the byte-duplicated copies' residue).
  let demoEnv ← CodegenCore.importModulesReplayed #[`Demo]
  let flagsEnv ← CodegenCore.importModulesReplayed #[`FeatureFlags]
  let named := namedByModule demoEnv (registeredItems demoEnv)
    ++ namedByModule flagsEnv (registeredItems flagsEnv)
  pure { items := named.map (·.2)
       , roots := groupByRoot named
       , invariants := registeredInvariants demoEnv ++ registeredInvariants flagsEnv
       , updates := registeredUpdates demoEnv ++ registeredUpdates flagsEnv }

end SchemaLang.Emit
