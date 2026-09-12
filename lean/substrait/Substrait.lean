/-
# Substrait

A general-purpose Lean 4 model of [Substrait] plans: a wire-faithful record
of the protobuf surface (`Substrait.Proto`), a schema-indexed typed layer
(`Substrait.Typed`) for authoring well-typed plans, an evaluator over the
read side (`Substrait.Eval`), a canonical text emitter matching the
substrait-explain grammar (`Substrait.Emit.Text`).

This package is public and engine-neutral: it knows Substrait, not any
particular engine's semantics.  Flatland-specific extension YAML and payloads
are data consumed through the extension declarations — they never appear in
this package.

The wire story: `Typed` → `Proto` → text.  The text is byte-identical to
the canonical substrait-explain output.  This umbrella is text-only: the
binary protobuf codec (`Substrait.ProtoGen`, generated codec + hand-written
bridge, on the Lean-zh/protobuf dep) is EXCLUDED from this package — the
documented add-back seam (git rev + moreLeanArgs) lives in `lakefile.toml`.

[Substrait]: https://substrait.io/

## Quick start

```lean
import Substrait

abbrev units : Substrait.Typed.Schema :=
  [("health", .i32, true), ("regen", .i32, true)]

open Substrait.Typed

def plan : Rel units units :=
  .filter (Rel.read "units" units)
    ((col "health" .i32 true) >. litI32 0)

#eval Substrait.Emit.Text.emit plan.toPlan
```
-/
import Substrait.Proto
import Substrait.Typed
import Substrait.Eval
import Substrait.Emit
import Substrait.Decode
import Substrait.Grammar
