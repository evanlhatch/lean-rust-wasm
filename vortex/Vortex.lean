/-
# Vortex — the umbrella module

One import point for the library. Submodules:

- `Vortex.Encoding` — the encoding vocabulary (the vortex layout's
  honest fragment), the static shape facts, THE selection function
  (a pure total function from static facts — never a runtime search)
  + its laws (applicability; the retention exemplars ported from the
  legacy lane).
- `Vortex.Emit` — the emitter row: the schema registry → the generated
  layout-spec artifact, the law discharged, the in-test byte-tie
  golden.

Named exclusions (each lands with its first consumer — the leftover
rule): the physical block-format codecs (dict/run-end bit layouts —
the wire lane), the data-dependent half of the design's tree
(runEnd/actual-cardinality — the obligation ladder's `oracleSwept`
tier), ALP (no float in the boundary `Ty`), Sparse/frame codecs, the
nested-array layouts (list/map/result columns fall back to
`identity`), the write path (the regen driver + the GenCheck/Ownership
gate rows).
-/

import Vortex.Encoding
import Vortex.Emit
