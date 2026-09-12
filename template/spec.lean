/-
# Thing spec — the authoring surface (THE source of truth)

DO-NOT-DELETE header: every attribute here has a role in the codegen
pipeline. This module is the SSOT — the WIT world, the Rust types, the
observe spans, and the fault surfaces are all generated from the
registrations BELOW (the `schema-gen` driver replays them from the
oleans). Delete an attribute and the artifact loses the surface
silently; the byte-tie gate catches it only after the fact.

Attribute roles:

- `@[schema]` on a structure/inductive → registers a record/variant in
  the schema registry. Fields must live in the CLOSED boundary universe
  (`Ty`): UInt64/String/List/Option/… — anything else fails at
  elaboration with the fragment enumerated. The generated Rust/WIT type
  is derived from the field list; renaming a field IS a breaking change
  (`just breaking` gates it).
- `@[schema_fn]` on a def → registers a func SIGNATURE. The body is a
  STUB — the signature is the spec (`_id` is the parameter's spec-name,
  underscore-silenced for the dead body). The real body lives in the
  impl module (ThingFn.lean). Optional semantic args: `@[schema_fn
  strict]` / `volatile` / `stream` (the FuncSem axes).
- `@[schema_resource]` on an opaque def → an opaque handle type (not
  used in this minimal skeleton; see schema-lang/Demo.lean).

Registration order matters (v1 limitation): the referenced type must be
registered before the referencing declaration — keep the record above
the functions that mention it.
-/

import SchemaLang.Meta.Reflect

/-! ## Records -/

@[schema]
structure Thing where
  id : UInt64
  label : String

/-! ## Function signatures (the bodies are NOT part of the spec) -/

/-- u64 → option<thing>. The body is a stub — the SIGNATURE is the spec. -/
@[schema_fn]
def thing_get (_id : UInt64) : Option Thing :=
  none
