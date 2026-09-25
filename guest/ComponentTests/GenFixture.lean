/-
# ComponentTests.GenFixture — the manifest discipline's growth surface

The teeth fixture: the module whose guest MARKS are the registered
project surface the manifest fold consumes. Three shapes, one per
tooth:

- `genInc` — MARKED + ABI-mappable (`UInt64 → UInt64`): lands in the
  compile set AND the world AND the component bytes (the growth
  tooth's positive face: registration → artifact).
- `genQuiet` — UNMARKED: compiled normally (the package builds it),
  but OUTSIDE the manifest's surface — absent from the compile set,
  the world, and the bytes (the negative control: no mark, no lane).
- `genNarrow` — MARKED + ABI-outside (`UInt32` result; `Wit.Scalar`
  carries no u32 atom): in the compile set, EXCLUDED from the world —
  the honest-surface discipline (compiled-but-unexported is REPORTED,
  never silently exported with a lying type).

The bodies are deliberately pairwise-distinct (the dup-body linter's
census stays quiet) and root-level (the lowered module exports the
decl's own name — the world's derived func names agree byte-for-byte).

Import note: `LintKit.GuestGate` provides the `@[guest]` mark (the
elaboration-time gate + the registry write; LintKit is core-only —
any package may import it, the Guest lane's convention).
-/

import LintKit.GuestGate

/-- The REGISTERED fn: the mark is the registration. -/
@[guest]
def genInc (n : UInt64) : UInt64 := n + 3

/-- The UNREGISTERED fn: no mark — outside the manifest's surface. -/
def genQuiet (n : UInt64) : UInt64 := n + 2

/-- The REGISTERED-but-ABI-outside fn: compiled, never exported. -/
@[guest]
def genNarrow (n : UInt64) : UInt32 := n.toUInt32
