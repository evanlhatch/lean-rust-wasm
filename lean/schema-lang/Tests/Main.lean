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
  -- demo universe: all refs resolve, names unique
  _ ← assertEq "demo wellFormed" (universeWellFormed Spec.demo) true
  -- a ref to a missing type is rejected
  let broken : List Item :=
    [ .record "a" [{ name := "x", ty := .ty "usr" }], .record "user" [] ]
  _ ← assertEq "unknown ref rejected" (universeWellFormed broken) false
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
  _ ← assertEq "record" (out.contains "record user {") true
  _ ← assertEq "kebab field" (out.contains "  id: u64,") true
  _ ← assertEq "list field" (out.contains "  tags: list<string>,") true
  _ ← assertEq "variant payload" (out.contains "  invalid-item(u64),") true
  _ ← assertEq "resource" (out.contains "resource db;") true
  _ ← assertEq "exports iface" (out.contains "export interface gateway-exports {") true
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

def main : IO UInt32 :=
  mainOfChecks "SchemaLang"
    [ ("resolution", resolutionChecks)
    , ("fieldRes", fieldResolutionChecks)
    , ("codec", codecChecks)
    , ("eqAns", eqAnsChecks)
    , ("diff", diffChecks)
    , ("wit", witChecks)
    , ("rust", rustChecks)
    ]
