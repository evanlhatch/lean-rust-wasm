/-
# SchemaLang Tests

Resolution wellFormed (accept/reject), EqAns direction, compat diff,
WIT golden emission.
-/
import Lean
import SchemaLang
import Demo
import TestKit

open SchemaLang TestKit

/-! ## Item-algebra fixtures (test data, not spec)

The items below reproduce the old `SchemaLang.Spec.Demo` hand-list verbatim.
They exercise the Item ALGEBRA (resolution, diff, delta shapes) without
depending on the reflection registry — which the golden checks load live
from `Demo` via `importModules`. The names are deliberately lowercase
(`user`, `role`, …) as the hand-list wrote them; the reflection emits
Pascal names and the emitters kebab at emission, so nothing drifts. -/

/-- Record fixture: `user`. -/
def demoUser : Item :=
  .record "user"
    [ { name := "id", ty := .u64 }
    , { name := "name", ty := .string }
    , { name := "email", ty := .string }
    , { name := "tags", ty := .list .string } ]

/-- Variant fixture: `role`. -/
def demoRole : Item :=
  .variant "role" [("admin", none), ("editor", none), ("viewer", none)]

/-- Variant fixture: `order-error`. -/
def demoOrderError : Item :=
  .variant "order-error"
    [ ("empty-cart", none)
    , ("invalid-item", some .u64)
    , ("insufficient-funds", some .f64) ]

/-- Func fixture: `get-user`. -/
def demoGetUser : Item :=
  .func { name := "get-user"
        , params := [("id", .u64)]
        , ret := .option (.ty "user") }

/-- Func fixture: `watch-orders`. -/
def demoWatchOrders : Item :=
  .func { name := "watch-orders"
        , params := [("into", .ty "order-error")]
        , ret := .future (.list (.ty "user")) }

/-- Resource fixture: `db`. -/
def demoDb : Item := .resource "db"

/-- The full demo universe fixture (the old Spec.demo). -/
def demoItems : List Item :=
  [ demoUser, demoRole, demoOrderError, demoGetUser, demoWatchOrders, demoDb ]

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
  _ ← assertEq "demo wellFormed" (universeWellFormed demoItems) true
  -- the DIAGNOSTIC authority: empty diags = well formed
  _ ← assertEq "demo check clean" (universeCheck demoItems) []
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
  _ ← assertEq "reshape reported" ((diff v1 v4).any
      (· == .changed "user" [.fieldTypeChanged "id" .u64 .string])) true
  -- field-level evidence: WHICH field moved (EqAns-based compat)
  let u1 : List Item := [ .record "user" [{ name := "id", ty := .u64 }] ]
  let u2 : List Item :=
    [ .record "user" [{ name := "name", ty := .string }
                    , { name := "id", ty := .u64 }] ]
  _ ← assertEq "field added" (diff u1 u2)
      [.changed "user" [.fieldAdded "name"]]
  _ ← assertEq "field removed" (diff u2 u1)
      [.changed "user" [.fieldRemoved "name"]]
  let u3 : List Item := [ .record "user" [{ name := "id", ty := .u32 }] ]
  _ ← assertEq "field retyped" (diff u1 u3)
      [.changed "user" [.fieldTypeChanged "id" .u64 .u32]]
  -- mixed: retype + addition, old-order evidence then additions
  let u4 : List Item :=
    [ .record "user" [{ name := "id", ty := .u64 }
                    , { name := "email", ty := .string }] ]
  _ ← assertEq "field mix" (diff u3 u4)
      [.changed "user" [.fieldTypeChanged "id" .u32 .u64, .fieldAdded "email"]]
  .ok ()

/-! ## Golden byte-tie: registry emitters vs committed goldens -/

open Lean SchemaLang.Meta in
/-- The reflected Demo registry, loaded at runtime (GenMain's pattern).
    `importModules` resolves oleans at RUNTIME — initialize the search
    path, then add the package build dir (a direct binary run lacks
    LEAN_PATH; the tests run from the package root). -/
unsafe def loadDemoItems : IO (List SchemaLang.Item) := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.searchPathRef.modify fun sp =>
    sp ++ [(".lake/build/lib" : System.FilePath), (".lake/build/lib/lean" : System.FilePath)]
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[`Demo] (opts := {}) (loadExts := true)
  pure ((registeredItems env).map (·.2))

/-- Run every registry emitter over the CURRENT reflected Demo registry
    and byte-compare each output (header prepended, matching `schema-gen`'s
    write) against the committed golden under `goldens/<emitter>/`.
    `update = true` regenerates (the deliberate-change path). -/
unsafe def goldenChecks (update : Bool) : IO (List (String × CheckResult)) := do
  let items ← loadDemoItems
  let mut results : List (String × CheckResult) := []
  for e in SchemaLang.Emit.emitters do
    for f in e.run items do
      let file := ((f.path : String).splitOn "/").getLast!
      let golden : System.FilePath := s!"goldens/{e.name}/{file}"
      let dir := String.intercalate "/" ((golden.toString.splitOn "/").dropLast)
      IO.FS.createDirAll dir
      let out := CodegenCore.Emit.header e.style "schema-lang" "Demo.lean"
        ++ CodegenCore.Emit.GeneratedFile.contents f
      let r ← TestKit.Golden.checkAgainstGolden e.name out golden update
      results := results ++ [(s!"{e.name}/{file}", r)]
  return results

/-! ## Bridge: Ty → SType -/

open Substrait.Typed in
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

open Substrait.Typed in
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

/-! ## Delta emitter (the event-sourcing shape) -/

def deltaChecks : CheckResult := do
  -- the change-shape functions, per record
  _ ← assertEq "changeTypeName" (Item.changeTypeName demoUser) "UserChange"
  _ ← assert (Item.changeTy demoUser == some (.ty "user")) "changeTy is the record ref"
  _ ← assert (Item.changeTy demoGetUser == none) "func has no change ty"
  _ ← assert (Item.changeTy (.record "empty" []) == none) "key-less record has no change ty"
  -- WIT change variant: name, insert/update payloads, remove carries the key type
  let wit := String.intercalate "\n" (Item.changeWitDecl demoUser)
  _ ← assert (wit.contains "variant user-change {") "variant name kebab+mangled"
  _ ← assert (wit.contains "insert(user)") "wit insert"
  _ ← assert (wit.contains "update(user)") "wit update"
  _ ← assert (wit.contains "remove(u64)") "wit remove carries key ty"
  _ ← assert (Item.changeWitDecl demoRole == []) "variant item: no change decl"
  -- Rust: enum + ChangeSpec impl
  let out := CodegenCore.Emit.Rust.renderModule (demoItems.flatMap Item.changeRustItems)
  _ ← assertEq "deterministic" out
    (CodegenCore.Emit.Rust.renderModule (demoItems.flatMap Item.changeRustItems))
  _ ← assert (out.contains "pub enum UserChange {") "change enum"
  _ ← assert (out.contains "#[derive(Clone, Debug, PartialEq, Eq)]") "derives"
  _ ← assert (out.contains "Insert(User),") "insert payload"
  _ ← assert (out.contains "Remove(u64),") "remove payload"
  _ ← assert (out.contains "impl dbsp::Change<User> for UserChange") "ChangeSpec impl"
  -- the emitters: declared paths, determinism
  let files := deltaEmitter.run demoItems
  _ ← assertEq "delta path" (files.head?.map (·.path)) (some "../../src/delta_generated.rs")
  _ ← assertEq "delta deterministic" (files.map (·.contents))
    ((deltaEmitter.run demoItems).map (·.contents))
  let wfiles := deltaWitEmitter.run demoItems
  _ ← assertEq "deltaWit path" (wfiles.head?.map (·.path)) (some "../../wit/delta.wit")
  let wout := wfiles.head?.map (·.contents) |>.getD ""
  _ ← assertEq "deltaWit deterministic" wout
    ((deltaWitEmitter.run demoItems).head?.map (·.contents) |>.getD "")
  _ ← assert (wout.contains "insert(user)") "deltaWit insert pin"
  _ ← assert (wout.contains "remove(u64)") "deltaWit remove pin"
  .ok ()

/-! ## Vortex ExtVTable emitter (ext dtypes, spec-as-data) -/

def extDTypeChecks : CheckResult := do
  -- the registry: wellFormed over every entry
  _ ← assertEq "ext wellFormed" (SchemaLang.Vortex.Emit.extDTypes.all (·.wellFormed)) true
  let out := CodegenCore.Emit.Rust.renderModule
    (SchemaLang.Vortex.Emit.extDTypeModule SchemaLang.Vortex.Emit.extDTypes)
  -- the ExtVTable impl is present, with the correct id
  _ ← assert (out.contains "impl ExtVTable for PositionExt") "vtable impl present"
  _ ← assert (out.contains "ExtId::new(\"flatland.position\")") "id correct"
  _ ← assert (out.contains "type Metadata = PositionMetadata;") "metadata assoc type"
  _ ← assert (out.contains "impl ExtVTable for TensorExt") "tensor impl present"
  _ ← assert (out.contains "ExtId::new(\"vortex.fixedshape.tensor\")") "tensor id correct"
  -- external (fork-owned) entries are registered but NOT emitted
  _ ← assert (!out.contains "GeoExt") "external skipped"
  -- determinism
  _ ← assertEq "ext deterministic" out
    (CodegenCore.Emit.Rust.renderModule
      (SchemaLang.Vortex.Emit.extDTypeModule SchemaLang.Vortex.Emit.extDTypes))
  -- the emitter: declared path + zero-input (ignores schema items)
  let files := SchemaLang.Vortex.Emit.extVortexEmitter.run []
  _ ← assertEq "ext path" (files.head?.map (·.path))
    (some "../../src/ext_dtypes_generated.rs")
  .ok ()

/-! ## Pipeline machine (Machines conformance battery) -/

/-- The positive battery: all three checks must pass over the full
    6-state space. -/
def pipelineConformanceChecks : CheckResult := do
  let rs := pipelineConformance
  for (name, r) in rs do
    match r with
    | .ok () => pure ()
    | .error msg => throw s!"pipeline conformance {name}: {msg}"
  -- named pins: the battery ran all three checks
  _ ← assert (rs.any (·.1 == "deadlock-freedom")) "deadlock-freedom ran"
  _ ← assert (rs.any (·.1 == "guard-coverage")) "guard-coverage ran"
  _ ← assert (rs.any (·.1 == "invariant-non-vacuous")) "invariant-non-vacuous ran"
  .ok ()

/-- The negative control: `pipelineDead` (a never-enabled event) must FAIL
    guard coverage — the battery is not vacuous. -/
def pipelineGuardControl : CheckResult :=
  match Machines.Testing.guardCoverage pipelineDead pipelineDead.labels [0, 1, 2] pipelineDead.labels_complete with
  | .error _ => .ok ()
  | .ok () => .error "dead event not caught — the battery is vacuous"

/-- The happy path executes end-to-end and out-of-order firing is
    rejected; acyclicity is `rank_advances_tr` (compile-time, above). -/
def pipelineRunChecks : CheckResult := do
  match pipeline.run .idle [.reflect, .check, .emit, .tie] with
  | none => throw "happy path rejected"
  | some (_, fin) =>
      if fin == .tied then pure ()
      else throw s!"happy path ended in {repr fin}"
  match pipeline.run .idle [.check] with
  | none => pure ()
  | some _ => throw "out-of-order check accepted"
  match pipeline.run (.failed "check" ["dup"]) [.reset] with
  | none => throw "reset from failed rejected"
  | some (_, fin) =>
      if fin == .idle then pure ()
      else throw s!"reset ended in {repr fin}"
  .ok ()

/-- The one-writer audit: no two emitters claim the same output path.
    The advertised discipline (`Emit.Registry.pathsUnique`) is ASSERTED
    here, not just stated in a header. -/
def emitterAuditChecks : CheckResult := do
  _ ← assertEq "emitter paths unique" SchemaLang.Emit.pathsUnique true
  -- the forge-driver audit: every registered emitter's output is in the
  -- job manifest forge consumes — no artifact silently outside byte-tie
  _ ← assertEq "jobs cover emitters" SchemaLang.Emit.jobsCoverEmitters true
  -- the GENERATED ChangeSpec trait: emitted from `Dbsp.ChangeSpec`'s
  -- class fields (`patch`/`valid`) — the method names ARE the class
  -- field names, pinned here so the emitter and the Lean class cannot
  -- drift apart (the Rust side re-exports the generated trait)
  let traitText := (changeSpecEmitter.run []).head?.map (·.contents)
    |>.getD ""
  _ ← assert (traitText.contains "pub trait Change<Row>") "generated Change trait"
  _ ← assert (traitText.contains "fn patch(&self, base: &Row) -> Row;") "trait patch = ChangeSpec field"
  _ ← assert (traitText.contains "fn valid(&self, base: &Row) -> bool;") "trait valid = ChangeSpec field"
  .ok ()

unsafe def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let goldens ← goldenChecks update
  mainOfChecks "SchemaLang"
    ([ ("resolution", resolutionChecks)
     , ("fieldRes", fieldResolutionChecks)
     , ("codec", codecChecks)
     , ("eqAns", eqAnsChecks)
     , ("diff", diffChecks)
     ] ++ goldens ++
     [ ("bridge", bridgeChecks)
     , ("bridgeSchema", bridgeSchemaChecks)
     , ("delta", deltaChecks)
     , ("extDType", extDTypeChecks)
     , ("pipelineConformance", pipelineConformanceChecks)
     , ("pipelineGuardControl", pipelineGuardControl)
     , ("pipelineRun", pipelineRunChecks)
     , ("emitterAudit", emitterAuditChecks)
     ])
