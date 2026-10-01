/-
# SchemaCore.Emit.Profiles — the semantic-profiles lane's CODEGEN face

Owner: the semantic-profiles agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/16-surface.md §4.5 (the ACTIVATED lane) +
D24/D38 (semantic profiles as PHANTOM metadata — "phantom
indices/refinements often erase without storage cost"; the review's
"transport them through codegen") + the scope lock (units are the
phantom INDEX, never a money TYPE).

THE FACE (E2's codegen row): the generated Rust/TS carry the profile
as the PHANTOM index —

- RUST: the const-generic parameter over `u8` tags (the LEAN ctor
  order: 0 = plain, 1 = deterministic, 2 = fast) +
  `#[repr(transparent)]` — the zero-sized type-level metadata whose
  LAYOUT IS T's. The erasure is Rust's own compile-time guarantee
  (a size/ABI fact, never a convention); `erase` is the consumption
  point where the phantom dies.
- TS: the branded-type face reusing the ONE `brand` symbol (the key
  materials' construction-point discipline — never a second brand
  table). TS erases types at runtime wholesale, so the wire sees T
  alone BY the language's own semantics; the brand is compile-time
  only.

At the WIRE both faces are the base scalar's: the profile is
compile-time-only, the bytes never mention it — the model's
`Profiled.erase` / `Profiled.iso` (SchemaCore.Profile) are the Lean
face of the same discipline, and the generated consumers' size pins
(the profile-fast suite) hold the runtime face to it.

The tags ride the model's tag discipline: the LEAN ctor names,
snake_case — ONE enum, two renderings (the Spine's one-writer rule;
this module is the face's text, the emitters concatenate it — the
kernel pins in SchemaTests hold both renderings to the contract).

The five questions (notes/v3/01-core.md): root = Universe (the
profile lane's metadata over the closed scalars); carrier = the
zero-sized phantom index (Rust const-generic / TS brand); spine
reading = the SECOND consumer of the ONE Profile enum (the tags are
the LEAN ctor names); ladder rung = kernel pins over the rendered
text (the chunk discipline — no rope cracks); gate row = SchemaTests'
profile-fast suite + gen-check (the byte-tie covers the generated
faces once regen commits them).

Core-only (imports SchemaCore.Profile — the cone rule).
-/

import SchemaCore.Profile
import Kit.Text

open Kit

namespace SchemaCore.Emit.Profiles

/-- The Rust phantom face (the honest per-target spelling). -/
def profilePhantomRust : String :=
"/// The PROFILED SCALAR (SchemaCore.Profiled — the semantic-profiles\n" ++
"/// lane's codegen face): the profile rides as the CONST-GENERIC\n" ++
"/// PHANTOM index — zero-sized, compile-time-only; the runtime\n" ++
"/// representation is T alone (`repr(transparent)` — the layout IS\n" ++
"/// T's; the erasure is Rust's own guarantee, never a convention).\n" ++
"/// Tags (the LEAN ctor order): 0 = plain, 1 = deterministic,\n" ++
"/// 2 = fast (the hardware-float trade — its forfeits are named in\n" ++
"/// the model, never hidden).\n" ++
"#[rustfmt::skip]\n" ++
"#[repr(transparent)]\n" ++
"#[derive(Clone, Debug, PartialEq, Eq, Hash)]\n" ++
"pub struct Profiled<T, const P: u8>(pub T);\n" ++
"\n" ++
"#[rustfmt::skip]\n" ++
"impl<T, const P: u8> Profiled<T, P> {\n" ++
"    /// The raw scalar (the wire/storage face — the profile is\n" ++
"    /// nowhere in it).\n" ++
"    pub fn raw(&self) -> &T { &self.0 }\n" ++
"\n" ++
"    /// THE ERASURE: consume the wrapper, keep the scalar — the\n" ++
"    /// phantom dies here (compile-time only; the wire bytes are\n" ++
"    /// the base scalar's, byte-for-byte).\n" ++
"    pub fn erase(self) -> T { self.0 }\n" ++
"}\n"

/-- The TS brand face (the ONE brand symbol reused — the
    construction-point discipline; TS erases types at runtime
    wholesale, so the wire sees T alone). -/
def profilePhantomTs : Text :=
  .str "\n\n/// The PROFILED SCALAR (SchemaCore.Profiled's TS face): the\n/// profile rides as the BRAND — compile-time only; TS erases types\n/// at runtime, so the wire sees T alone. The brand REUSES the ONE\n/// `brand` symbol (the key materials' construction-point discipline\n/// — never a second brand table).\nexport type Profiled<T, P extends Profile> = T & { readonly [brand]: P };"

end SchemaCore.Emit.Profiles
