/-
# SchemaLang.Emit.WitFixture — the WIT inversion fixtures (item: parse∘emit)

The Stage F gate parses ONE generated WIT (the demo universe). This
emitter generalizes it toward a theorem shape: a DETERMINISTIC SET of
universes (scalars / nesting / variants / async) is emitted as WIT
fixtures plus a JSON manifest of each universe's structure. The Rust
side (`wit_fixture_sweep.rs`) parses every fixture with wit-parser — an
INDEPENDENT parser, not our printer — and asserts the resolved
structure equals the manifest: `parse (emit u) ≅ u` over generated
universes, not just the demo.

Everything here is byte-tied like any emitter output (drift fails CI);
the fixtures are emitted, never hand-edited.
-/

import CodegenCore
import SchemaLang.Item
import SchemaLang.Emit.Wit

namespace SchemaLang.Emit.WitFixture

open CodegenCore.Emit (jsonStr)

/-! ## The fixture universes (deterministic — no RNG, full coverage) -/

/-- Scalar coverage: every scalar `Ty` constructor as a record field.
    Field NAMES dodge WIT keywords (`u8`/`u16`/… are RESERVED in WIT —
    the sweep caught a field literally named `u8` failing wit-parser;
    the demo universe's author-named fields never hit it). The TYPE
    coverage is what matters: each field's TYPE is the scalar. -/
def scalarUniverse : List Item :=
  [ .record "scalars"
      [ { name := "v-bool", ty := .bool }
      , { name := "v-u8", ty := .u8 }, { name := "v-u16", ty := .u16 }
      , { name := "v-u32", ty := .u32 }, { name := "v-u64", ty := .u64 }
      , { name := "v-i8", ty := .i8 }, { name := "v-i16", ty := .i16 }
      , { name := "v-i32", ty := .i32 }, { name := "v-i64", ty := .i64 }
      , { name := "v-f32", ty := .f32 }, { name := "v-f64", ty := .f64 }
      , { name := "v-string", ty := .string }, { name := "v-bytes", ty := .bytes } ] ]

/-- Nesting: option/list/result tower (result is WIT `result<ok, err>`). -/
def nestedUniverse : List Item :=
  [ .record "nested"
      [ { name := "opt", ty := .option .u32 }
      , { name := "lst", ty := .list .string }
      , { name := "res", ty := .result .u64 .string } ] ]

/-- Variants: bare cases + payload cases (the WIT variant grammar). -/
def variantUniverse : List Item :=
  [ .variant "shape"
      [ ("unit", none)
      , ("radius", some .f64)
      , ("label", some .string) ] ]

/-- Async: future return (WASI 0.3 — async lives in the FUNCTION TYPE). -/
def asyncUniverse : List Item :=
  [ .func { name := "watch", params := [("id", .u64)]
          , ret := .future (.list (.option .u64)) } ]

/-- The fixtures: (fixture name, universe). -/
def fixtures : List (String × List Item) :=
  [ ("scalars", scalarUniverse)
  , ("nested", nestedUniverse)
  , ("variants", variantUniverse)
  , ("async", asyncUniverse) ]

/-! ## The manifest (Lean's view of each universe, as JSON) -/

/-- One type entry → JSON. Kinds are wit-parser's `TypeDefKind` names so
    the Rust side compares directly. `none` for non-types (filterMap's
    shape). -/
def typeJson (it : Item) : Option String :=
  match it with
  | .record n fields =>
      some ("{\"name\": " ++ jsonStr n ++ ", \"kind\": \"record\", \"fields\": ["
        ++ String.intercalate ", " (fields.map (fun f => jsonStr f.name)) ++ "]}")
  | .variant n cases =>
      some ("{\"name\": " ++ jsonStr n ++ ", \"kind\": \"variant\", \"cases\": ["
        ++ String.intercalate ", " (cases.map (fun c => jsonStr c.1)) ++ "]}")
  | _ => none

/-- One func entry → JSON (name + param names). `none` for non-funcs
    (filterMap's shape). -/
def funcJson (it : Item) : Option String :=
  match it with
  | .func sig =>
      some ("{\"name\": " ++ jsonStr sig.name ++ ", \"params\": ["
        ++ String.intercalate ", " (sig.params.map (fun p => jsonStr p.1)) ++ "]}")
  | _ => none

/-- One fixture → the manifest object text. -/
def fixtureJson (name : String) (items : List Item) : String :=
  "  { \"fixture\": " ++ jsonStr name ++ ", \"package\": "
    ++ jsonStr ("demo:fixture-" ++ name)
    ++ ", \"types\": [" ++ String.intercalate ", " (items.filterMap typeJson) ++ "]"
    ++ ", \"funcs\": [" ++ String.intercalate ", " (items.filterMap funcJson) ++ "] }"

/-- The full manifest document (no header — the driver prepends). -/
def manifestJson : String :=
  "[\n" ++ String.intercalate ",\n" (fixtures.map fun (n, items) => fixtureJson n items) ++ "\n]\n"

/-! ## The emitters -/

def manifestEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "wit-fixture-manifest"
  style := .doubleSlash
  specSource := "SchemaLang.Emit.WitFixture (fixtures)"
  outputs := ["../../crates/steel-host/tests/fixtures/wit_manifest.json"]
  run _ :=
    [{ path := "../../crates/steel-host/tests/fixtures/wit_manifest.json"
       contents := manifestJson }]

/-- One emitter outputting ALL fixture WIT files (one emitter, many
    files — the outputs list is the one-writer claim). -/
def fixtureEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "wit-fixtures"
  style := .doubleSlash
  specSource := "SchemaLang.Emit.WitFixture (fixtures)"
  outputs := fixtures.map fun (n, _) => "../../crates/steel-host/tests/fixtures/wit_fixture_" ++ n ++ ".wit"
  run _ :=
    fixtures.map fun (n, items) =>
      { path := "../../crates/steel-host/tests/fixtures/wit_fixture_" ++ n ++ ".wit"
      , contents := SchemaLang.Emit.Wit.worldOf ("demo:fixture-" ++ n) ("fixture-" ++ n) items }

end SchemaLang.Emit.WitFixture
