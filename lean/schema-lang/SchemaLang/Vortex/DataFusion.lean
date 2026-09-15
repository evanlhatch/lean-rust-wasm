/-
# SchemaLang.Vortex.DataFusion — the DataFusion verdict (no port)

The honest verdict on the flatland's DataFusion-related code:

- **The Rust runtime is NOT ours.** DataFusion is the flatland's query
  EXECUTION runtime (the Rust side): physical plans, scalar-UDF
  bindings, the `batch_expr` catalog. None of that is a Lean artifact
  and none of it ports — the schema-language package models SPEC, not
  the executor. The template's relationship to DataFusion is
  TARGET-not-source: our emitters may emit FOR a DataFusion consumer;
  we do not model its internals.

- **The logical-plan model already EXISTS.** What is portable about a
  logical plan — the typed expression/relation algebra — is the
  Substrait layer, which this repo ships (`lean/substrait`, the wire
  algebra; `SchemaLang.VExpr`, the schema-indexed validator
  expressions; `Subschema.vortexSelect`, the field-mask-shaped
  projection over DTypes). A DataFusion logical plan in Lean would be
  a third spelling of that algebra — not built, by the one-writer rule.

- **The scalar-UDF binding surface.** A UDF binding is (name, arg
  DTypes, return DType) plus an evaluator. The DTypes exist
  (`SchemaLang.Vortex.DType`); the evaluator lane is the guestlang
  wasm story, not this one. When a consumer needs the binding record,
  it is one structure over `DType` — added THEN, with its consumer.

Nothing in this module is code BY DESIGN: an empty model would be a
stub, and the zero-sorry discipline applies to designs too. The
encodings (the Vortex-central capability) live in `Encoding.lean`; the
batch reads live in `Batch.lean`.
-/
