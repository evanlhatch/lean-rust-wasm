/-
# LeanSubstrait

A general-purpose Lean 4 model of [Substrait] plans: a wire-faithful record
of the protobuf surface (`LeanSubstrait.Proto`), a schema-indexed typed layer
(`LeanSubstrait.Typed`) for authoring well-typed plans, an evaluator over the
read side (`LeanSubstrait.Eval`), a canonical text emitter matching the
substrait-explain grammar (`LeanSubstrait.Emit.Text`).

This package is public and engine-neutral: it knows Substrait, not any
particular engine's semantics.  Flatland-specific extension YAML and payloads
are data consumed through the extension declarations — they never appear in
this package.

The wire story: `Typed` → `Proto` → text or binary.  The text is
byte-identical to the canonical substrait-explain output.  The binary wire
lives in `LeanSubstrait.ProtoGen` (generated protobuf codec + hand-written
bridge), deliberately kept out of this umbrella so the default surface stays
dependency-light — import it explicitly when wire I/O is needed.

[Substrait]: https://substrait.io/

## Quick start

```lean
import LeanSubstrait

abbrev units : LeanSubstrait.Typed.Schema :=
  [("health", .i32, true), ("regen", .i32, true)]

open LeanSubstrait.Typed

def plan : Rel units units :=
  .filter (Rel.read "units" units)
    ((col "health" .i32 true) >. litI32 0)

#eval LeanSubstrait.Emit.Text.emit plan.toPlan
```
-/
import LeanSubstrait.Proto
import LeanSubstrait.Typed
import LeanSubstrait.Eval
import LeanSubstrait.Emit
import LeanSubstrait.Decode
import LeanSubstrait.Substrait.Grammar
import LeanSubstrait.Vortex
