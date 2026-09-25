/- # SchemaTests.RustEmit — the Rust emitter's growth pins

The Rust emitter's grown API surface (the builder, the 02 §3 lookups,
the serde face, the migration lane's Rust face) rides TWO pinned
fixtures this suite holds to the LIVE lane:

1. THE KEYS-FACE TOOTH: the emitter renders the key-indexed lookup
   from the PINNED `keysFace` rows (a pure run — the live keys
   registry is a different extension state; KeysSlice cannot join the
   replay chain: it would cycle through CheckSlice). This tooth ties
   the pin to the LIVE `@[key]` registration — a key change without
   the pin's update FAILS HERE (loud, never silent).
2. THE MIGRATION FACE'S DERIVATION PIN: the Rust upcaster renders the
   PINNED plan (`examplePlan12` — the wf-recursive derivation is
   kernel-opaque, so the agreement is RUNTIME-pinned here; 06 §2).

Positive pins + the MANDATORY negative controls (15-patterns #5).
Evidence, not architecture — the five-question block lives in the
modules under test (SchemaCore.Emit.Rust / SchemaCore.Migrate /
SchemaCore.Keys).
-/

import TestingKit.Harness
import SchemaCore
import SchemaCore.Keys
import SchemaCore.KeysSlice
import SchemaTests.Events

open SchemaCore TestingKit

/-! ## The fixtures -/

/-- A v1 row (the versioned fixture's old face): ready true, count
    300, label "hi". -/
def rustV1Row : RowVals SchemaCore.Emit.Rust.exampleV1.fields :=
  .cons (.bool true) (.cons (.u64 300) (.cons (.string "hi") .nil))

/-- The upcast expectation, v2-typed: the SAME row + the filled
    default (delta 0). -/
def rustV2Row : RowVals SchemaCore.Emit.Rust.exampleV2.fields :=
  .cons (.bool true) (.cons (.u64 300) (.cons (.string "hi")
    (.cons (.i64 0) .nil)))

structure RustPlanFixture where
  plan : FieldPlan SchemaCore.Emit.Rust.exampleV1.fields
    SchemaCore.Emit.Rust.exampleV2.fields

/-- The DERIVED plan (runtime — the derivation is wf-recursive). -/
def rustPlanFixture? : Option RustPlanFixture :=
  match deriveUpcaster "label" [] SchemaCore.Emit.Rust.exampleV1
      SchemaCore.Emit.Rust.exampleV2 with
  | .ok p => some { plan := p }
  | .error _ => none

/-! ## The suite -/

def rustEmitSpec : Spec :=
  Spec.ofList "the Rust emitter's grown surface: keys tooth, migration pin"
    (fun _ => do
      match rustPlanFixture? with
      | some fx =>
          -- THE KEYS-FACE TOOTH: the pinned rows ARE the live
          -- registration (the emitter cannot see the live registry —
          -- this tooth is the glue)
          assert (SchemaCore.Emit.Rust.keysFace
              == [(exampleKey.record, exampleKey.key)])
            "the keys face drifted from the live @[key] registration"
          -- THE DERIVATION AGREEMENT: the derived plan IS the pinned
          -- plan (upcast behavior, value level)
          assert (fx.plan.stableKey "label")
            "the derived plan's key stability drifted"
          assert (renderTable [fx.plan.upcast rustV1Row]
              == renderTable [SchemaCore.Emit.Rust.examplePlan12.upcast rustV1Row])
            "the derived plan drifted from the pinned plan"
          assert (renderTable [SchemaCore.Emit.Rust.examplePlan12.upcast rustV1Row]
              == renderTable [rustV2Row])
            "the upcast row drifted (carry verbatim + the filled default)"
      | none => assert false "the fixture derivation must succeed")
    [ ("the keys face names a different record",
        fun _ =>
          assert (SchemaCore.Emit.Rust.keysFace
              == [(exampleKey.record, "count")])
            "control fired: the pin names the LIVE key — a moved key \
              breaks the tooth, never the emitted lookup silently")
    , ("the added field can host the key",
        fun _ =>
          assert (match deriveUpcaster "delta" []
                    SchemaCore.Emit.Rust.exampleV1
                    SchemaCore.Emit.Rust.exampleV2 with
            | .ok _ => true | _ => false)
            "control fired: stable identities are ENFORCED — the ADDED \
              field cannot become the key (a migrated key is a \
              different entity set, 08 §19)")
    , ("the version chain's reverse direction derives",
        fun _ =>
          assert (match deriveUpcaster "label" []
                    SchemaCore.Emit.Rust.exampleV2
                    SchemaCore.Emit.Rust.exampleV1 with
            | .ok _ => true | _ => false)
            "control fired: the REMOVAL refuses loudly — the Rust face \
              never renders a plan the derivation refused (no partial \
              migration)")
    , ("the pinned plan's fill invents data",
        fun _ =>
          assert (match RowVals.project? SchemaCore.Emit.Rust.exampleV2.fields
                    (SchemaCore.Emit.Rust.examplePlan12.upcast rustV1Row)
                    "delta" with
            | some fv => toString fv.val != "0"
            | none => true)
            "control fired: the fill is the type's DEFAULT — exactly 0, \\
              never garbage (the emitted literal is the rendered value)") ]
    4 42
