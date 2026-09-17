/-
# SchemaLang.Emit.GenRust — Rust VALUE-GENERATOR emission (W6.4 phase 1)

Emit Rust generators FROM the schema registry: one `gen_<record>` fn
per `@[schema]` record, `arbitrary::Unstructured`-driven (the bolero/
arbitrary style crates/wire already tests against). The target shape is
the cedar-proven one (notes/studies/cedar-study.md "Generators"):

- explicit depth budget (`max_depth`), FORCED LEAF at 0 (composites
  collapse: option → `None`, list → `vec![]`);
- collision pools for string fields (90% an existing name from
  `STRING_POOL` / 10% fresh) — joins and refs can't fire without shared
  referents;
- no `derive(Arbitrary)` on recursive shapes — the budget threads
  through every composite arm.

Ownership: the generator EMISSION lane. The Lean-side generators
(`SchemaLang/Gen.lean`) stay the semantic reference — this module emits
the Rust mirror of that discipline, it does not re-derive it.

Deliberate exclusions (scope honesty):
- The v1 Ty fragment is: scalars (bool/ints/floats), `string`, `bytes`,
  `option`, `list`, and `.ty` refs that resolve (transitively, fuel-
  bounded) to GENERATABLE records. `result`/`future`/`stream`/`tensor`
  and variant/resource refs are a LOUD SKIP: the record's gen fn is
  replaced by a comment naming the field and the reason (never silent
  partial output). The closed-universe rule holds: `unsupported?` and
  `genExpr` match EVERY `Ty` ctor — a new ctor fails this module's
  compilation, not the emitted Rust's.
- Variants get NO generator yet (the demo's gen-reachable universe is
  record-only; weighted case-choice lands with the variant arm).
- Adversarial knobs (cedar's type-mismatch/string-mutation arms) are
  NOT emitted — they belong to fault-injection generation, not the
  well-typed value lane.
- The `SchemaGen`-style registry trait + derived indexes (cedar's
  `&dyn` surface) land when a CONSUMER needs cross-record lookup at
  runtime; phase 1 emits free fns, which the smoke test threads by name.

Driving decision: the string pool is DERIVED from the registry (the
record names themselves) — shape-FILLED like every other emitter: the
pool's contents are the spec's data, the generator only chooses
indices into it. `gen!`-style weighted choice is inlined per arm
(option/list/pool), not a macro — three arms don't pay for a macro.

Rust lint surface: no `as` casts (`char::from`), no `unwrap()` (the
`arbitrary::Result` alias + `?` everywhere), no `unsafe`, no
TODO/FIXME/dbg! — the emitter self-audit rules
(`Emit.Registry.emitterAuditRules`) scan this output like every
other's.
-/

module

public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Emit.GenCtx

@[expose] public section

namespace SchemaLang.Emit.GenRust

open CodegenCore.Emit (pascal snake rustIdent)

/-- The support-check fuel (ref chains through records; the demo's
    deepest chain is 1). -/
def refFuel : Nat := 8

/-- The fragment gate: `some reason` = this `Ty` is OUTSIDE the emitted
    fragment; `none` = generatable. Refs resolve against the item
    universe, fuel-bounded (the `floatRefs` discipline): a ref to a
    SKIPPED record is itself unsupported — the referencing record's fn
    would call a fn that was never emitted. EXHAUSTIVE over the closed
    `Ty` (a new ctor fails HERE, at compile time). -/
def unsupported? (items : List Item) : Nat → Ty → Option String
  | _, .bool | _, .u8 | _, .u16 | _, .u32 | _, .u64
  | _, .i8 | _, .i16 | _, .i32 | _, .i64
  | _, .f32 | _, .f64 | _, .string | _, .bytes => none
  | fuel, .option a => unsupported? items fuel a
  | fuel, .list a => unsupported? items fuel a
  | 0, .ty n => some s!"ref '{n}': support-check fuel exhausted (ref cycle?)"
  | fuel + 1, .ty n =>
      match items.find? (·.name == n) with
      | some (.record _ fields) =>
          (fields.findSome? fun f =>
            (unsupported? items fuel f.ty).map
              fun r => s!"ref '{n}' skipped: field '{f.name}': {r}")
      | some _ => some s!"ref '{n}': variant/resource refs have no generator yet"
      | none => some s!"ref '{n}': unresolvable"
  | _, .result .. => some "result: not in the v1 fragment"
  | _, .map .. => some "map: no Rust-side generator yet (W8.1 — the Lean lane's genVal has one)"
  | _, .set .. => some "set: no Rust-side generator yet (W8.1 — the Lean lane's genVal has one)"
  | _, .future _ => some "future: no value generator (Gen.lean mirrors this)"
  | _, .stream _ => some "stream: no value generator"
  | _, .tensor .. => some "tensor: shape-filled generation not emitted yet"

/-- The Rust expression producing ONE value of type `t` (an expression
    OF the field's type — it may use `?`, valid in every context the
    emitter places it: the gen fn bodies and the `gen_list`/`gen_option`
    closures, all `arbitrary::Result`-returning). `depth` is the depth
    VARIABLE's spelling at the emission site (`max_depth` at fn level,
    `d` inside the composite closures). Exhaustive over the closed `Ty`;
    the non-fragment arms are UNREACHABLE (`unsupported?` skips the
    record first) — their marker text is loud on purpose. -/
def genExpr (depth : String) : Ty → String
  | .bool | .u8 | .u16 | .u32 | .u64 | .i8 | .i16 | .i32 | .i64
  | .f32 | .f64 => "u.arbitrary()?"
  | .string => "gen_string(u)?"
  | .bytes => "gen_bytes(u)?"
  | .option a => s!"gen_option(u, {depth}, |u, d| Ok({genExpr "d" a}))?"
  | .list a => s!"gen_list(u, {depth}, |u, d| Ok({genExpr "d" a}))?"
  | .ty n => s!"gen_{snake n}(u, {depth}.saturating_sub(1))?"
  | .result .. => "/* UNREACHED: result outside the v1 fragment */ u.arbitrary()?"
  | .map .. => "/* UNREACHED: map gated by unsupported? */ u.arbitrary()?"
  | .set .. => "/* UNREACHED: set gated by unsupported? */ u.arbitrary()?"
  | .future _ => "/* UNREACHED: future */ u.arbitrary()?"
  | .stream _ => "/* UNREACHED: stream */ u.arbitrary()?"
  | .tensor .. => "/* UNREACHED: tensor */ u.arbitrary()?"

/-- One record → its gen fn item, or — when a field falls outside the
    fragment — the LOUD skip comment naming every blocking field. The
    fn body is a `String` leaf (the boring-template concession, counted
    with the AST's other leaves): struct-literal fields, one `genExpr`
    per field in SCHEMA order (shape-FILLED — the same rule the Lean
    lane's `genRowVals` obeys). -/
def recordGenItem (items : List Item) (n : String) (fields : List Field) :
    CodegenCore.Emit.Rust.Item :=
  let blocked := fields.filterMap fun f =>
    (unsupported? items refFuel f.ty).map fun r => s!"'{f.name}': {r}"
  match blocked with
  | b :: bs =>
      .comment s!"gen_{snake n} SKIPPED — {String.intercalate "; " (b :: bs)}"
  | [] =>
      let fieldLines := fields.map fun f =>
        s!"    {rustIdent f.name}: {genExpr "max_depth" f.ty},"
      .fn
        s!"fn gen_{snake n}(u: &mut Unstructured<'_>, max_depth: usize) -> arbitrary::Result<{pascal n}>"
        (s!"Ok({pascal n} \{" ++ "\n" ++ String.intercalate "\n" fieldLines ++ "\n  })")

/-- The collision pool: the registry's RECORD names (derived, never
    hand-listed — the spec's data fills the pool). 90% of generated
    strings come from it so cross-record joins/refs can fire; 10% are
    fresh short lowercase strings. The fallback keeps `u.choose` total
    on an empty universe. -/
def stringPool (items : List Item) : List String :=
  let names := items.filterMap fun it =>
    match it with | .record n _ => some n | _ => none
  if names.isEmpty then ["alpha", "beta"] else names

/-- The fixed prelude: the import, the pool, and the three composite
    helpers (string/bytes/list/option share them across every gen fn).
    Emitted as `raw` leaves — AUDITED and counted like every raw leaf
    (see CodegenCore.Emit.Rust.Item.raw). -/
def preludeItems (items : List Item) : List CodegenCore.Emit.Rust.Item :=
  [ .comment "Rust VALUE GENERATORS emitted from the schema registry (W6.4 phase 1)."
  , .comment "Shape: cedar-proven (cedar-study.md Generators) — explicit max_depth"
  , .comment "budget with forced leaf at 0, a collision pool on strings (90/10),"
  , .comment "no derive(Arbitrary) on recursive shapes. Consume with"
  , .comment "arbitrary::Unstructured (bolero's with_arbitrary works too)."
  , .raw "use arbitrary::Unstructured;"
  , .raw ""
  , .raw "// The generated domain types (the sibling artifact — schema_generated.rs)."
  , .raw "use crate::schema_generated::*;"
  , .raw ""
  , .raw "/// The collision pool: the registry's record names. 90% of generated"
  , .raw "/// strings are pool members (shared referents — joins/refs can fire);"
  , .raw "/// 10% are fresh. Derived from the spec, never hand-listed."
  , .raw ("pub const STRING_POOL: &[&str] = &[" ++
      String.intercalate ", " ((stringPool items).map fun n =>
        "\"" ++ n ++ "\"") ++ "];")
  , .raw ""
  , .raw "/// A string: 90% a pool member, 10% fresh (<= 8 lowercase chars —"
  , .raw "/// small supplies shrink well, the Gen.lean `genChar` discipline)."
  , .raw "pub fn gen_string(u: &mut Unstructured<'_>) -> arbitrary::Result<String> {"
  , .raw "    if u.ratio(9, 10)? {"
  , .raw "        return Ok(u.choose(STRING_POOL)?.to_string());"
  , .raw "    }"
  , .raw "    let len = u.int_in_range(0..=8usize)?;"
  , .raw "    let mut s = String::with_capacity(len);"
  , .raw "    for _ in 0..len {"
  , .raw "        s.push(char::from(b'a' + u.int_in_range(0..=25u8)?));"
  , .raw "    }"
  , .raw "    Ok(s)"
  , .raw "}"
  , .raw ""
  , .raw "/// Bytes: a short bounded vec (the byte guard is Unstructured's own `len`)."
  , .raw "pub fn gen_bytes(u: &mut Unstructured<'_>) -> arbitrary::Result<Vec<u8>> {"
  , .raw "    let len = u.int_in_range(0..=8usize)?;"
  , .raw "    let mut v = Vec::with_capacity(len);"
  , .raw "    for _ in 0..len {"
  , .raw "        v.push(u.arbitrary()?);"
  , .raw "    }"
  , .raw "    Ok(v)"
  , .raw "}"
  , .raw ""
  , .raw "/// A list: forced EMPTY at depth 0, else <= 3 elements at depth - 1."
  , .raw "pub fn gen_list<T>("
  , .raw "    u: &mut Unstructured<'_>,"
  , .raw "    max_depth: usize,"
  , .raw "    elem: impl Fn(&mut Unstructured<'_>, usize) -> arbitrary::Result<T>,"
  , .raw ") -> arbitrary::Result<Vec<T>> {"
  , .raw "    let len = if max_depth == 0 { 0 } else { u.int_in_range(0..=3usize)? };"
  , .raw "    let mut v = Vec::with_capacity(len);"
  , .raw "    for _ in 0..len {"
  , .raw "        v.push(elem(u, max_depth - 1)?);"
  , .raw "    }"
  , .raw "    Ok(v)"
  , .raw "}"
  , .raw ""
  , .raw "/// An option: forced `None` at depth 0, else a coin flip (the Some arm"
  , .raw "/// spends the depth)."
  , .raw "pub fn gen_option<T>("
  , .raw "    u: &mut Unstructured<'_>,"
  , .raw "    max_depth: usize,"
  , .raw "    inner: impl Fn(&mut Unstructured<'_>, usize) -> arbitrary::Result<T>,"
  , .raw ") -> arbitrary::Result<Option<T>> {"
  , .raw "    if max_depth == 0 || u.ratio(1, 2)? {"
  , .raw "        return Ok(None);"
  , .raw "    }"
  , .raw "    Ok(Some(inner(u, max_depth - 1)?))"
  , .raw "}"
  , .raw "" ]

/-- The full universe → the generator module's items: the prelude, then
    one item per RECORD (variants/funcs/resources contribute nothing —
    the variant arm lands with weighted case-choice). -/
def genRustItems (items : List Item) : List CodegenCore.Emit.Rust.Item :=
  preludeItems items ++ items.filterMap fun it =>
    match it with
    | .record n fields => some (recordGenItem items n fields)
    | _ => none

end SchemaLang.Emit.GenRust

/-- The generator emitter plugin (W6.4): `gen_<record>` fns over the
    schema universe, consumed by the root crate's `gen_generated`
    module (feature-gated on `arbitrary`, the wire pattern). -/
def genRustEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx where
  name := "gen-rust"
  style := .doubleSlash
  specSource := "Demo.lean + FeatureFlags.lean (@[schema] records; cedar-study.md Generators)"
  outputs := ["../../src/gen_generated.rs"]
  run ctx := [
    { path := "../../src/gen_generated.rs"
      contents := CodegenCore.Emit.Rust.renderModule
        (SchemaLang.Emit.GenRust.genRustItems ctx.items) }
  ]
