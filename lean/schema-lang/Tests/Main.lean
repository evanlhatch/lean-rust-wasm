/-
# SchemaLang Tests

Resolution wellFormed (accept/reject), EqAns direction, compat diff,
WIT golden emission.
-/
import SchemaLang
import TestKit

open SchemaLang TestKit

/-! ## The linen patterns, exercised -/

/-- Schema-indexed field resolution (abbrev list — the reducibility rule). -/
abbrev userFields : List Field :=
  [ ⟨"id", .u64⟩, ⟨"name", .string⟩, ⟨"email", .string⟩ ]

def fieldResolutionChecks : CheckResult := do
  _ ← assertEq "id at 0" (fieldIndex userFields "id" .u64) 0
  _ ← assertEq "email at 2" (fieldIndex userFields "email" .string) 2
  .ok ()

def codecChecks : CheckResult := do
  -- the theorems, executed
  _ ← assertEq "bool roundtrip" (Codec.decodeBool (Codec.encodeBool true)) (some true)
  _ ← assertEq "bool reject" (Codec.decodeBool [5]) none
  _ ← assertEq "u8 roundtrip" (Codec.decodeU8 (Codec.encodeU8 42)) (some 42)
  _ ← assertEq "u8 reject len" (Codec.decodeU8 [1, 2]) none
  -- exhaustive byte sweep for Bool's 2-byte domain
  let allBytes : List UInt8 := (List.range 256).map (·.toUInt8)
  _ ← assertEq "bool exhaustive"
    (allBytes.all fun b =>
      let d := Codec.decodeBool [b]
      if b == 0 || b == 1 then d.isSome else d.isNone)
    true
  .ok ()

def resolutionChecks : CheckResult := do
  -- demo universe: all refs resolve, names unique (Bool projection)
  _ ← assertEq "demo wellFormed" (universeWellFormed Spec.demo) true
  -- the DIAGNOSTIC authority: empty diags = well formed
  _ ← assertEq "demo check clean" (universeCheck Spec.demo) []
  -- a ref to a missing type: rejected WITH did-you-mean + valid space
  let broken : List Item :=
    [ .record "a" [{ name := "x", ty := .ty "usr" }], .record "user" [] ]
  _ ← assertEq "unknown ref rejected" (universeWellFormed broken) false
  let diags := universeCheck broken
  match diags with
  | [SchemaDiag.unknownRef got cands valid] => do
    _ ← assertEq "got" got "usr"
    _ ← assertEq "didYouMean finds user" (cands.contains "user") true
    _ ← assertEq "valid space enumerated" (valid.contains "user") true
  | ds => throw s!"unexpected diagnostics: {ds}"
  -- duplicate names rejected
  let dup : List Item :=
    [ .record "user" [], .variant "user" [] ]
  _ ← assertEq "dup names rejected" (universeWellFormed dup) false
  -- forward reference is FINE (resolution is universe-wide)
  let fwd : List Item :=
    [ .record "a" [{ name := "x", ty := .ty "b" }], .record "b" [] ]
  _ ← assertEq "forward ref accepted" (universeWellFormed fwd) true
  .ok ()

def eqAnsChecks : CheckResult := do
  -- yes carries the proof (composable); no is proof-free by design
  match Ty.eqAns (.option .u64) (.option .u64) with
  | .yes _ => pure ()
  | .no => throw "same types should be .yes"
  match Ty.eqAns (.option .u64) (.option .u32) with
  | .no => pure ()
  | .yes _ => throw "different types should be .no"
  -- nested: result through option
  match Ty.eqAns (.result (.ty "a") .string) (.result (.ty "a") .string) with
  | .yes _ => pure ()
  | .no => throw "nested same should be .yes"
  .ok ()

def diffChecks : CheckResult := do
  let v1 : List Item :=
    [ .record "user" [{ name := "id", ty := .u64 }]
    , .variant "role" [("admin", none)] ]
  -- identical → no changes
  _ ← assertEq "identical" (diff v1 v1) []
  -- backward compatible: addition only
  let v2 : List Item :=
    [ .record "user" [{ name := "id", ty := .u64 }]
    , .variant "role" [("admin", none)]
    , .record "order" [] ]
  _ ← assertEq "addition safe" (backwardCompatible v1 v2) true
  -- removal is breaking
  let v3 : List Item := [ .variant "role" [("admin", none)] ]
  _ ← assertEq "removal breaking" (backwardCompatible v1 v3) false
  _ ← assertEq "removal reported" (diff v1 v3).head? (some (.removed "user"))
  -- reshape (same name, different shape) is breaking
  let v4 : List Item :=
    [ .record "user" [{ name := "id", ty := .string }]
    , .variant "role" [("admin", none)] ]
  _ ← assertEq "reshape breaking" (backwardCompatible v1 v4) false
  _ ← assertEq "reshape reported" ((diff v1 v4).any (· == .changed "user")) true
  .ok ()

def witChecks : CheckResult := do
  let out := Emit.Wit.worldOf "demo:gateway" "gateway" Spec.demo
  -- determinism: same input, same bytes
  _ ← assertEq "deterministic" out (Emit.Wit.worldOf "demo:gateway" "gateway" Spec.demo)
  -- structure pins
  _ ← assertEq "package" (out.contains "package demo:gateway;") true
  _ ← assertEq "world" (out.contains "world gateway {") true
  _ ← assertEq "types iface" (out.contains "interface gateway-types {") true
  _ ← assertEq "use clause" (out.contains "use gateway-types.{user, order-error};") true
  _ ← assertEq "record" (out.contains "record user {") true
  _ ← assertEq "kebab field" (out.contains "  id: u64,") true
  _ ← assertEq "list field" (out.contains "  tags: list<string>,") true
  _ ← assertEq "variant payload" (out.contains "  invalid-item(u64),") true
  _ ← assertEq "resource" (out.contains "resource db;") true
  _ ← assertEq "exports iface" (out.contains "interface gateway-exports {") true
  _ ← assertEq "func sig" (out.contains "get-user: func(id: u64) -> option<user>;") true
  _ ← assertEq "future/stream" (out.contains "future<list<user>>") true
  -- kebab mangle: an import header line never appears
  _ ← assertEq "no import kw" (out.contains "\nimport ") false
  .ok ()

def rustChecks : CheckResult := do
  let items := Emit.Rust.schemaItems Emit.Rust.defaultDerives Spec.demo
  let out := CodegenCore.Emit.Rust.renderModule items
  -- determinism: same input, same bytes
  _ ← assertEq "deterministic" out (CodegenCore.Emit.Rust.renderModule items)
  _ ← assertEq "struct" (out.contains "pub struct User {") true
  _ ← assertEq "derive" (out.contains "#[derive(Clone, Debug, PartialEq, Eq)]") true
  _ ← assertEq "vec field" (out.contains "Vec<String>") true
  _ ← assertEq "enum" (out.contains "pub enum OrderError {") true
  _ ← assertEq "payload variant" (out.contains "InvalidItem(u64),") true
  _ ← assertEq "no funcs" (out.contains "get_user") false
  .ok ()

/-! ## Bridge: Ty → SType -/

open LeanSubstrait.Typed in
def bridgeChecks : CheckResult := do
  -- scalars round-trip 1:1 (signed, floats, bool, string)
  _ ← assert (Ty.toSType? .bool == some .bool) "bool"
  _ ← assert (Ty.toSType? .i8 == some .i8) "i8"
  _ ← assert (Ty.toSType? .i32 == some .i32) "i32"
  _ ← assert (Ty.toSType? .i64 == some .i64) "i64"
  _ ← assert (Ty.toSType? .f32 == some .fp32) "f32"
  _ ← assert (Ty.toSType? .f64 == some .fp64) "f64"
  _ ← assert (Ty.toSType? .string == some .string) "string"
  -- unsigned narrowing: u-lossy by design
  _ ← assert (Ty.toSType? .u8 == some .i8) "u8 narrows"
  _ ← assert (Ty.toSType? .u64 == some .i64) "u64 narrows"
  -- nesting
  _ ← assert (Ty.toSType? (.list .string) == some (.list .string)) "list"
  _ ← assert (Ty.toSType? (.ty "user") == some (.userDefined "" "user" [])) "ty ref"
  -- not queryable
  _ ← assert (Ty.toSType? (.future .u64) == none) "future none"
  _ ← assert (Ty.toSType? (.stream .string) == none) "stream none"
  _ ← assert (Ty.toSType? (.result .u64 .string) == none) "result none"
  _ ← assert (Ty.toSType? .bytes == none) "bytes none"
  -- option does not lower outside a column context
  _ ← assert (Ty.toSType? (.option .string) == none) "option none"
  -- the congruence proof instantiates; equal types lower equally
  let _pf := Ty.toSType?_congr (show Ty.i32 = Ty.i32 from rfl)
  _ ← assert (Ty.toSType? .i32 == Ty.toSType? .i32) "congr"
  .ok ()

open LeanSubstrait.Typed in
def bridgeSchemaChecks : CheckResult := do
  -- required field: nullable=false, u64 narrows
  _ ← assert (SchemaCol.ofField ⟨"id", .u64⟩ == some ("id", .i64, false)) "required field"
  -- option field: unwrapped into nullable=true
  _ ← assert (SchemaCol.ofField ⟨"email", .option .string⟩
    == some ("email", .string, true)) "option field"
  -- nested options stay flat-nullable
  _ ← assert (SchemaCol.ofField ⟨"x", .option (.option .u32)⟩
    == some ("x", .i32, true)) "nested option"
  -- non-queryable field type
  _ ← assert (SchemaCol.ofField ⟨"job", .future .u64⟩ == none) "future field none"
  -- ofItems: records only, option fields become nullable columns
  let items : List Item :=
    [ .record "user" [⟨"id", .u64⟩, ⟨"email", .option .string⟩]
    , .variant "role" [("admin", none)]
    , .resource "db" ]
  let expect : List (String × Schema) :=
    [("user", [("id", .i64, false), ("email", .string, true)])]
  _ ← assert (Schema.ofItems items == expect) "ofItems"
  .ok ()

/-! ## Vortex emitter -/

def vortexChecks : CheckResult := do
  let files := SchemaLang.Vortex.Emit.vortexEmitter.run Spec.demo
  _ ← assertEq "one file" files.length 1
  -- output path is declared, exactly
  _ ← assertEq "path" (files.head?.map (·.path) |>.getD "") "src/vortex_generated.rs"
  let out := files.head?.map (·.contents) |>.getD ""
  -- determinism: same input, same bytes
  _ ← assertEq "deterministic" out
    ((SchemaLang.Vortex.Emit.vortexEmitter.run Spec.demo).head?.map (·.contents) |>.getD "")
  -- dtype pins
  _ ← assertEq "primitive pin" (out.contains "DType::Primitive(PType::U64") true
  _ ← assertEq "nullability pin" (out.contains "Nullability::NonNullable") true
  _ ← assertEq "impl pin" (out.contains "impl IntoVortex for User") true
  -- list<string> field lowers to Arc-wrapped Utf8
  _ ← assertEq "list pin"
    (out.contains "DType::List(std::sync::Arc::new(DType::Utf8(Nullability::NonNullable))") true
  -- const naming: snake + upper + _DTYPE
  _ ← assertEq "const pin" (out.contains "pub const USER_DTYPE") true
  .ok ()

def main : IO UInt32 :=
  mainOfChecks "SchemaLang"
    [ ("resolution", resolutionChecks)
    , ("fieldRes", fieldResolutionChecks)
    , ("codec", codecChecks)
    , ("eqAns", eqAnsChecks)
    , ("diff", diffChecks)
    , ("wit", witChecks)
    , ("rust", rustChecks)
    , ("bridge", bridgeChecks)
    , ("bridgeSchema", bridgeSchemaChecks)
    , ("vortex", vortexChecks)
    ]
