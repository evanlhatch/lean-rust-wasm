/-
# CodegenCore.Emit.Certified — proof-carrying emission (refactor-guide 5.5.2)

Doctrine: for law-governed data, the emitter takes the DISCHARGED proof
term of the law over the CONCRETE spec data. If the law fails on the data,
the call fails to elaborate — the artifact is unemittable. Byte-tie says
reproducible; this says reproducible-AND-correct. Provenance: flatland
`Tests/SpawnGate.lean` (`emitRanges` taking
`cert : (allocRanges rs counts).Pairwise …` — "the artifact is false if
we proved it wrong").

Convention, not framework: a `CertifiedEmitter` is the `Emitter` metadata
(name/style/specSource/outputs — the registry-audit surface) plus the law
and a proof-carrying `run`. Drivers call `run spec cert`; registries audit
`toEmitter` (one-writer over `outputs`, jobs coverage) exactly as today.
-/

import CodegenCore.Emit.Core

namespace CodegenCore.Emit

/-- An emitter whose emission path requires a certificate: a proof of
    `Law` over the concrete input. `Law` is a field (not an index) so the
    structure stays first-order; the caller supplies the discharged term
    at the emission site. -/
structure CertifiedEmitter (Spec : Type) where
  /-- Plugin name (as `Emitter.name`). -/
  name : String
  /-- Comment prefix for the generated header. -/
  style : CommentStyle
  /-- The spec module the artifacts derive from (audit provenance). -/
  specSource : String
  /-- Declared output paths, repo-root-relative. MUST be unique across
      the registry (the one-writer discipline, checked in Tests). -/
  outputs : List String
  /-- The law the spec data must satisfy before anything may be emitted. -/
  Law : Spec → Prop
  /-- Proof-carrying emission. Uncallable without a discharged
      certificate — that is the whole point. -/
  run : (spec : Spec) → Law spec → List GeneratedFile

/-- Registry-audit view of a certified emitter. Metadata identical; the
    plain `run` reports no files BY CONSTRUCTION — the only real emission
    path is the certified one, so an uncertified caller can byte-tie
    nothing. -/
def CertifiedEmitter.toEmitter (ce : CertifiedEmitter Spec) : Emitter Spec :=
  { name := ce.name, style := ce.style, specSource := ce.specSource,
    outputs := ce.outputs, run := fun _ => [] }

/-! ### Compile-time demo

One file per item; the law is item-name `Nodup` (two items sharing a name
would write the same path — the one-writer law). The demo emitter consumes
the discharged certificate; drop the `by decide` and the module stops
elaborating, which is the discipline in miniature. -/

/-- The demo's concrete spec data. -/
def demoItems : List String := ["alpha", "beta"]

/-- Demo certified emitter: one text file per item, `gen/<item>.txt`.
    `outputs` is stated for the demo's concrete item list. -/
def demoCertified : CertifiedEmitter (List String) where
  name := "certified-demo"
  style := .doubleSlash
  specSource := "CodegenCore.Emit.Certified.demoItems"
  outputs := ["gen/alpha.txt", "gen/beta.txt"]
  Law := List.Nodup
  run items _cert := items.map fun i =>
    { path := s!"gen/{i}.txt", contents := s!"// {i}\n" }

/-- The discharged certificate over the CONCRETE data (SpawnGate shape). -/
theorem demoCert : demoCertified.Law demoItems :=
  show List.Nodup demoItems from by decide

/-- The emitter consumes the certificate: emission succeeds, and the
    emitted paths are exactly the declared outputs. -/
example : (demoCertified.run demoItems demoCert).map (·.path)
    = demoCertified.outputs := rfl

end CodegenCore.Emit
