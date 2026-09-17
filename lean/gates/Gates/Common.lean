/-
# Gates.Common — the shared registry-replay preamble

The demo+flags `GenCtx` assembly, byte-identical to
`SchemaLang.GenMain.runGen`'s (the two-environment replay: `Demo` and
`FeatureFlags` both declare the root-level `Async.Future`/`Async.Stream`
markers, so they replay into SEPARATE environments and merge at the
registry-concat level — see GenMain's header for why a joint import
fails). Shared by `GenCheck` (the byte-tie) and `Coverage` (the matrix)
so the two gates can never disagree about what the spec of record is.

LEGACY (non-module) file BY DESIGN: it calls the meta env-extension
accessors (`registeredItems` etc.) — constraint 12 of
notes/w5-4-module-migration.md (drivers touching meta env extensions
stay legacy).

Paths: every recipe runs this exe from `lean/gates` (`cd lean/gates &&
lake exe gates …`), the same depth as `lean/schema-lang`, so GenMain's
`../feature-flags/…` extra-path convention works unchanged.
-/
import Lean
import SchemaLang.Emit.Registry

open Lean SchemaLang.Meta

namespace Gates

/-- The full registry state (demo + flags worlds), replayed from oleans.
    The emitters stay pure; this is the one IO preamble. -/
unsafe def loadGenCtx : IO SchemaLang.Emit.GenCtx := do
  let paths : List System.FilePath :=
    [("../feature-flags/.lake/build/lib" : System.FilePath),
     ("../feature-flags/.lake/build/lib/lean" : System.FilePath)]
  let demoEnv ← CodegenCore.importModulesReplayed #[`Demo]
  let flagsEnv ← CodegenCore.importModulesReplayed #[`FeatureFlags] paths
  let named := SchemaLang.Emit.namedByModule demoEnv (registeredItems demoEnv)
    ++ SchemaLang.Emit.namedByModule flagsEnv (registeredItems flagsEnv)
  pure { items := named.map (·.2)
       , roots := SchemaLang.Emit.groupByRoot named
       , invariants := registeredInvariants demoEnv ++ registeredInvariants flagsEnv
       , updates := registeredUpdates demoEnv ++ registeredUpdates flagsEnv }

end Gates
