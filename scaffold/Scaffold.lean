/-
# Scaffold — the umbrella module

One import point for the library (root-module imports are NOT
re-exported — this module re-exports by importing):

- `Scaffold.Spec` — the AppSpec (the declarative VALUE describing a
  consumer app/lane) + the closed capability/root/rung enums + the
  closed gate-row vocabulary + the curated validation (`validate` —
  every refusal rides the ONE Diag envelope, the closed-world
  constructor filling the valid space + the did-you-mean).
- `Scaffold.Generate` — the interpreter: the total generator from a
  validated AppSpec to the consumer's skeleton AS LEAN SOURCE (the
  generative engine's Lean-syntax target reading, notes/v3/01-core.md
  §5) — the lane registration riding `Kit.Lane.register_lane`, the
  obligation view, the test suite WITH the mandatory negative
  controls, the five-questions headers filled from the spec.
- `Scaffold.Specs` — the adopted skeletons' spec registry (the writer
  driver's input; one home per spec value).

The five questions (notes/v3/01-core.md): answered per submodule (the
list above); the umbrella itself answers none — it is the import point.
Gate row: ScaffoldTests (the golden byte-tie + the in-process
elaboration of the generated registration module + the curated-failure
teeth + the mandatory negative controls).
-/

import Scaffold.Spec
import Scaffold.Generate
import Scaffold.Specs
