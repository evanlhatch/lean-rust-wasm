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
- `Vortex.Codecs` — the array-level encodings APPLIED: the real byte
  codecs per selected encoding (the bitPacked/foR/dict/constant/
  sequence/identity disciplines), the append-form law per codec
  (15-patterns #2), the round-trip theorem per encoding on its
  ADMISSIBLE SUBDOMAIN, and the column-data emitter the layout drives
  (`emitColumnData`/`readColumnData`) — the emission law in the type.
- `Vortex.DTypeProto` — the DType proto face (the wire message layer):
  the 13-variant oneof at `DType.dtypeWireTag`'s numbers (the seam's
  registry IS the wire's kind tag), the Field/variant reps, the
  append-form round-trip law on the `inDomainDType` subdomain
  (patterns #2/#18; the honest conditionalRetraction grade in the
  `dtypeWireTarget` row), and the off-domain ASCII controls.
- `Vortex.Compute` — COMPUTE-ON-COMPRESSED: evaluation OVER the
  encoded form (the point of the encodings) — per (encoding, op) the
  direct evaluator + its law `evalEncoded op enc ≡ decode enc |>
  eval op` (the retention discipline at the compute grade), the
  predicate fragment as data (eq/thresholds/complement; `.raw` the
  off-fragment refusal), the `computeOk` gate (the fragment boundary +
  the corruption refusal), and the probe account (the fusion teeth:
  dict = the distinct-value count, constant = one probe).

Named exclusions (each lands with its first consumer — the leftover
rule): the vortex FILE CONTAINER (the flatbuffers metadata, the
Arrow-IPC record-batch framing, the layouts/chunking — the write
path's consumer), the data-dependent half of the design's tree
(runEnd/actual-cardinality — the obligation ladder's `oracleSwept`
tier), ALP (no float in the boundary `Ty`), Sparse/frame codecs, the
nested-array DATA lanes (list/map/result columns fall back to
`identity`; their data rides `SchemaCore.Codec`'s proven wire), the
regen driver + the GenCheck/Ownership gate rows (the write path).
-/
module

public import Vortex.Encoding
public import Vortex.Emit
public import Vortex.Codecs
public import Vortex.Compute
public import Vortex.DTypeProto
@[expose] public section

end -- public section
