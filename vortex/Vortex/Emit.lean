/-
# Vortex.Emit — the vortex layout-spec emitter (the emitter row)

Owner: the Vortex agent (the mandate tree, `vortex/`).
Driving decisions: notes/v3/05-codegen.md §2 (the emitter spine — the
ONE plugin model, outputs nodup in the type, the optional law, the
driver owns IO) + notes/v3/07-extensibility.md R1 step 4 (the Emitter
row: the law or the honest note) + notes/design-vortex-encodings.md's
wire contract (the layout plan emitted per column, the encoding hint
the host applies at write time).

THE ARTIFACT: `gen/vortex-layout.txt` — the generated LAYOUT
DESCRIPTION: one row per schema field, naming the selected encoding +
the validity layer (the design's step 4: the emitter emits the PLAN;
the host applies the hints at write time; a measured-drift hook
re-derives loudly — that hook is the write path's consumer, not this
seed's).

THE BYTE-TIE, honestly stated: the emitter's declared output path is
committed by the lane's write path when it lands (a regen driver +
the GenCheck/Ownership rows — the named follow-up; a generator with no
driver writes nothing). AT THIS SIZE the tie is exercised IN-TEST: the
golden pins in `VortexTests.Main` prove `layoutEmitter.run fixtureReg`
IS the pinned byte string, kernel-discharged (`rfl`) — the emitter's
correspondence law (15-patterns #10) with the committed-file face
deferred to the write path, exactly the ScaffoldDemo precedent (the
generated modules byte-tie in the test lane until the driver wiring).

THE LAW: `layoutLaw` — every field of every registered item selects an
encoding APPLICABLE to its static facts (the design's per-rule
applicability, one theorem over the whole artifact). Discharged by
`layoutOf_applicable`'s citation — the selection law does the work,
never a re-proof.

Core-only (imports Kit + SchemaCore.Item + Vortex.Encoding — the cone
rule; the SchemaCore import is READ-ONLY).

The five questions (notes/v3/01-core.md): root = Crossing (the
registry → the layout-spec artifact); carrier = the law field —
`layoutLaw` (the applicability of every emitted row, in the type);
spine reading = Registry → Interpretation (`select`) → artifact (the
emitter IS an interpretation — 01 §5); ladder rung = the fold is
structural/total, the law is a cited instance; gate row = the
in-test golden (above) + the axiom report.
-/

import Kit
import SchemaCore.Item
import Vortex.Encoding

open Kit

namespace Vortex

/-! ## The rendering -/

/-- The encoding's spec spelling (the host hint's vocabulary). -/
def renderEncoding : EncodingSpec → String
  | .identity => "identity"
  | .bitPacked w => s!"bitpacked<{w}>"
  | .foR w => s!"for+bitpacked<{w}>"
  | .dict => "dict"
  | .sequence => "sequence"
  | .constant => "constant"

/-- The column layout's spelling: the validity layer (when the field
    is nullable) OUTER of the encoding — kernels peel layers, so the
    outer layer names first (the design's nesting discipline). -/
def renderLayout (l : ColumnLayout) : String :=
  if l.validity then s!"validity+{renderEncoding l.encoding}"
  else renderEncoding l.encoding

/-- One field's row: the wire path, the boundary type (the schema's
    ONE renderer — never a parallel spelling), the selected layout. -/
def fieldRow (item : String) (f : SchemaCore.Field) : String :=
  s!"{item}.{f.name}: {SchemaCore.renderTy f.ty} -> {renderLayout (layoutOf f.ty)}"

/-- The artifact body: one row per field, registration order. -/
def renderLayoutSpec (items : List SchemaCore.Item) : String :=
  "-- vortex layout spec — the encoding plan per column\n"
    ++ "-- selected by Vortex.select from the static shape facts (pure, total;\n"
    ++ "-- never a runtime search — notes/design-vortex-encodings.md)\n"
    ++ String.intercalate "\n"
      (items.flatMap fun it => it.fields.map (fieldRow it.name))
    ++ "\n"

/-! ## The law -/

/-- The emission law: every field of every registered item selects an
    encoding applicable to its static facts — the design's
    per-rule applicability over the WHOLE artifact. -/
def layoutLaw (reg : DataRegistry SchemaCore.Item) : Prop :=
  ∀ it ∈ reg.items, ∀ f ∈ it.fields,
    applicable (layoutOf f.ty).encoding (columnOf f.ty).1
      (factsOfColumn f.ty) = true

/-- THE DISCHARGE: one citation per row — `layoutOf_applicable` is
    `select_applicable` at the layout's own arguments; the registry
    quantifiers add nothing to discharge. -/
theorem layoutLaw_discharged (reg : DataRegistry SchemaCore.Item) :
    layoutLaw reg :=
  fun _ _ _ _ => layoutOf_applicable _

/-! ## The emitter -/

/-- The vortex lane's emitter: the layout spec per column. The
    outputs-nodup is IN THE TYPE (Kit.Emit — a colliding literal fails
    to elaborate); the law is POPULATED and discharged (the certified
    lane is the emission route). -/
def layoutEmitter : Kit.Emit.Emitter (DataRegistry SchemaCore.Item) where
  name := "vortex-layout"
  style := .lean
  specSource := "SchemaCore.Slice"
  outputs := ["gen/vortex-layout.txt"]
  run reg :=
    [{ path := "gen/vortex-layout.txt"
       contents := renderLayoutSpec reg.items }]
  law := some layoutLaw

end Vortex
