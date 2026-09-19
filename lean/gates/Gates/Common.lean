/- # Gates.Common — the shared registry-replay preamble

The demo+flags `GenCtx` assembly now lives in SchemaLang.GenCtxIO
(`loadGenCtx` — the former byte-duplicate of SchemaGenMain.runGen's
preamble, deduped); this is the gates-side NAME the two consumers
(`GenCheck`, `Coverage`) already call.

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
import SchemaLang.Emit.Registry
import SchemaLang.GenCtxIO

open Lean SchemaLang.Meta

namespace Gates

/-- The full registry state (demo + flags worlds), replayed from oleans.
    The emitters stay pure; this is the one IO preamble. -/
unsafe def loadGenCtx : IO SchemaLang.Emit.GenCtx :=
  SchemaLang.Emit.loadGenCtx

end Gates
