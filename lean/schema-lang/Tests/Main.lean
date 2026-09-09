/-
# SchemaLang Tests

Resolution wellFormed (accept/reject), EqAns direction, compat diff,
WIT golden emission.
-/
import Lean
import SchemaLang
import Demo
import TestKit
import LSpec

open SchemaLang TestKit
open SchemaLang.Session (toWire tdual gatewayTyped)

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
  | ds => throw s!"unexpected diagnostics: {SchemaDiag.renderList ds}"
  -- duplicate names rejected
  let dup : List Item :=
    [ .record "user" [], .variant "user" [] ]
  _ ← assertEq "dup names rejected" (universeWellFormed dup) false
  -- forward reference is FINE (resolution is universe-wide)
  let fwd : List Item :=
    [ .record "a" [{ name := "x", ty := .ty "b" }], .record "b" [] ]
  _ ← assertEq "forward ref accepted" (universeWellFormed fwd) true
  -- 0.6: variant payloads are inside the async ban (a `variant v
  -- { c(future<u8>) }` emits WIT the canonical parser rejects)
  let asyncVariant : List Item := [.variant "v" [("c", some (.future .u8))]]
  _ ← assertEq "variant async payload rejected" (universeCheck asyncVariant)
    [.asyncField "v" "c"]
  _ ← assertEq "variant async not wellFormed" (universeWellFormed asyncVariant) false
  -- positive control: async in a FUNC signature stays legal
  let asyncFunc : List Item := [.func { name := "f", params := [], ret := .future .u8 }]
  _ ← assertEq "func async accepted" (universeCheck asyncFunc) []
  -- 0.7: a non-boundary field type names the FIELD and appends the
  -- boundary fragment (not an unknown-TYPE did-you-mean)
  let nb := SchemaDiag.render (.nonBoundaryType "count" "Nat")
  _ ← assert (nb.contains "`count`") "nonBoundaryType names the field"
  _ ← assert (nb.contains "boundary types are")
    "nonBoundaryType appends the boundary fragment"
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

/-! ## Codec combinators (5.5.1 + 5.5.7): append-form composition

A composite wire structure exercising EVERY combinator — bool tag,
length-prefixed list of option nats, closed enum, length-prefixed
bytes — plus the theorem that the per-field append lemmas compose into
the whole-structure round trip by `simp` alone. -/

/-- Tiny closed enum for the enum-combinator pin. -/
inductive Direction | north | south deriving Repr, BEq, DecidableEq

def Direction.tag : Direction → Nat
  | .north => 0 | .south => 1

def Direction.ofTag? : Nat → Option Direction
  | 0 => some .north | 1 => some .south | _ => none

@[simp] theorem Direction.ofTag_tag? (d : Direction) :
    Direction.ofTag? d.tag = some d := by cases d <;> rfl

/-- The composite structure: one field per combinator. -/
structure Composite where
  flag : Bool
  nums : List (Option Nat)
  dir : Direction
  payload : List UInt8
deriving Repr, BEq, DecidableEq

-- test-local rendering (assertEq wants ToString; core gives Prod only Repr)
instance : ToString Direction := ⟨fun d => match d with | .north => "north" | .south => "south"⟩
instance : ToString Composite := ⟨fun c => toString (repr c)⟩
instance : ToString Codec.Envelope := ⟨fun e => toString (repr e)⟩
instance [ToString α] [ToString β] : ToString (α × β) := ⟨fun (a, b) => s!"({a}, {b})"⟩

/-- The composite wire: positional concatenation of self-delimiting
    fields, one per combinator. -/
def encComposite (c : Composite) : List UInt8 :=
  Codec.encodeBool c.flag
    ++ Codec.encList (Codec.encOpt Codec.encVarNat) c.nums
    ++ Codec.encEnum c.dir.tag
    ++ Codec.encBytes c.payload

def decComposite? (bs : List UInt8) : Option (Composite × List UInt8) :=
  match Codec.decBool? bs with
  | none => none
  | some (flag, r1) =>
      match Codec.decList? (Codec.decOpt? Codec.decNat?) r1 with
      | none => none
      | some (nums, r2) =>
          match Codec.decEnum? Direction.ofTag? r2 with
          | none => none
          | some (dir, r3) =>
              match Codec.decBytes? r3 with
              | none => none
              | some (payload, r4) => some (⟨flag, nums, dir, payload⟩, r4)

/-- The payoff (5.5.1): per-field append lemmas compose into the
    whole-structure round trip by `simp` ALONE — no manual rewriting. -/
theorem composite_decode_encode (c : Composite) (rest : List UInt8) :
    decComposite? (encComposite c ++ rest) = some (c, rest) := by
  obtain ⟨flag, nums, dir, payload⟩ := c
  simp [encComposite, decComposite?, List.append_assoc,
    Codec.decList_encList_append, Codec.decOpt_encOpt_append,
    Codec.decEnum_encEnum_append, Direction.ofTag_tag?]

def codecCombinatorChecks : CheckResult := do
  let c : Composite := ⟨true, [some 1, none, some 300], .south, [9, 8, 7]⟩
  let wire := encComposite c
  -- whole-structure round trip over every combinator
  _ ← assertEq "composite roundtrip" (decComposite? wire) (some (c, []))
  -- self-delimiting: trailing junk survives the decode untouched
  _ ← assertEq "composite append form" (decComposite? (wire ++ [42, 43]))
    (some (c, [42, 43]))
  -- truncation rejection: empty input fails the FIRST field's tag check
  _ ← assertEq "truncated to empty" (decComposite? []) none
  -- truncation inside the length-prefixed tail fails the byte count check
  _ ← assertEq "truncated payload" (decComposite? (wire.take (wire.length - 1))) none
  -- the varint base: multi-byte digit round trip
  _ ← assertEq "varnat 300" (Codec.decVarNat (Codec.encVarNat 300)) (300, [])
  _ ← assertEq "varnat 300 append"
    (Codec.decVarNat (Codec.encVarNat 300 ++ [1, 2])) (300, [1, 2])
  -- enum rejection: out-of-range tag is `none`, not garbage
  _ ← assertEq "enum bad tag" (Codec.decEnum? Direction.ofTag? [7]) none
  -- pair combinator round trip
  _ ← assertEq "prod roundtrip"
    (Codec.decProd? Codec.decNat? Codec.decU8?
      (Codec.encProd Codec.encVarNat Codec.encodeU8 (5, (7 : UInt8)) ++ [0]))
    (some ((5, (7 : UInt8)), [0]))
  -- bytes combinator rejects a lying length prefix
  _ ← assertEq "bytes overrun" (Codec.decBytes? [3, 1, 2]) none
  .ok ()

/-- The versioned envelope (5.5.7): round trip, wrong-version rejection
    (theorem `Codec.decEnvelope_wrong_version`, executed here), and
    truncation rejection. -/
def envelopeChecks : CheckResult := do
  let wire := Codec.encEnvelope 1 42 [1, 2, 3]
  _ ← assertEq "envelope roundtrip" (Codec.decEnvelope? 1 wire)
    (some ⟨1, 42, [1, 2, 3]⟩)
  -- wrong version rejects BEFORE the payload is touched
  _ ← assertEq "envelope wrong version" (Codec.decEnvelope? 2 wire) none
  -- truncated payload rejects (the length prefix overruns)
  _ ← assertEq "envelope truncated"
    (Codec.decEnvelope? 1 (wire.take (wire.length - 1))) none
  -- trailing garbage after the payload rejects
  _ ← assertEq "envelope trailing junk" (Codec.decEnvelope? 1 (wire ++ [0])) none
  .ok ()

/-! ## Golden byte-tie: registry emitters vs committed goldens -/

open Lean in
/-- The Demo environment, loaded at runtime via the CodegenCore driver
    preamble (GenMain's pattern). `importModules` resolves oleans at
    RUNTIME — the package build dirs are passed explicitly (a direct
    binary run lacks LEAN_PATH; the tests run from the package root). -/
unsafe def loadDemoEnv : IO Environment :=
  CodegenCore.importModulesReplayed #[`Demo]
    [(".lake/build/lib" : System.FilePath), (".lake/build/lib/lean" : System.FilePath)]

open SchemaLang.Meta in
/-- The reflected Demo registry, loaded at runtime. -/
unsafe def loadDemoItems : IO (List SchemaLang.Item) := do
  pure ((registeredItems (← loadDemoEnv)).map (·.2))

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
      CodegenCore.Emit.createParentDirs golden
      -- the header cites the emitter's OWN specSource — the goldens
      -- byte-tie what production (`schema-gen`) actually writes
      let out := CodegenCore.Emit.header e.style "schema-lang" e.specSource
        ++ CodegenCore.Emit.GeneratedFile.contents f
      let r ← TestKit.Golden.checkAgainstGolden e.name out golden update
      results := results ++ [(s!"{e.name}/{file}", r)]
  return results

/-! ## Vortex lowering pins (0.1) -/

/-- 0.1: nullability composition + refusal of `.result`. -/
def lowerChecks : CheckResult := do
  let semNone : SchemaLang.Vortex.VortexSem := fun _ => none
  -- option's nullability lands on the OUTER dtype only:
  -- option<list<u8>> → a NULLABLE list of NON-NULLABLE u8
  _ ← assert (
    SchemaLang.Vortex.Ty.lower semNone .nonNullable (.option (.list .u8))
      == some (.list (.primitive .u8 .nonNullable) .nullable))
    "option<list<u8>>: nullable list of non-nullable u8"
  -- a nullable named ref THREADS the requested nullability onto the
  -- resolved dtype (was: `.ty n => sem n` dropped it)
  let rec1 : Item := .record "r" [{ name := "id", ty := .u64 }]
  let semR := SchemaLang.Vortex.Emit.refSem [rec1] 8
  _ ← assert (
    SchemaLang.Vortex.Ty.lower semR .nullable (.ty "r")
      == some (.struct [("id", .primitive .u64 .nonNullable)] .nullable))
    "nullable ref: requested nullability stamped"
  -- non-nullable ref stays non-nullable
  _ ← assert (
    SchemaLang.Vortex.Ty.lower semR .nonNullable (.ty "r")
      == some (.struct [("id", .primitive .u64 .nonNullable)] .nonNullable))
    "non-nullable ref unchanged"
  -- `.result` refuses (the promised tag+payload union has not landed;
  -- the header must not ship a wrong artifact that succeeds)
  _ ← assert (
    SchemaLang.Vortex.Ty.lower semNone .nonNullable (.result .u64 .string) == none)
    "result lowers to none"
  _ ← assert (
    SchemaLang.Vortex.Ty.lower semNone .nullable (.result .u64 .string) == none)
    "nullable result still none"
  .ok ()

/-! ## Eq-eligibility (0.3 + 4.5): `derivesFor`, refs resolved -/

/-- 0.3: a float behind a NAMED REF blocks `Eq` on the referencing type
    (was: `.ty n` treated as float-free → `#[derive(Eq)]` on a struct
    whose ref'd type doesn't implement Eq → generated Rust didn't
    compile). 4.5: one `derivesFor` fold is the single fix site. -/
def derivesChecks : CheckResult := do
  let inner : Item := .record "inner" [{ name := "x", ty := .f64 }]
  let outer : Item := .record "outer" [{ name := "i", ty := .ty "inner" }]
  let clean : Item := .record "clean" [{ name := "n", ty := .u32 }]
  let viaClean : Item := .record "via-clean" [{ name := "c", ty := .ty "clean" }]
  let uni : List Item := [inner, outer, clean, viaClean]
  _ ← assertEq "float behind ref blocks Eq"
    (SchemaLang.Emit.Rust.derivesFor uni [.ty "inner"])
    ["Clone", "Debug", "PartialEq"]
  _ ← assertEq "resolvable-clean ref keeps Eq"
    (SchemaLang.Emit.Rust.derivesFor uni [.ty "clean"])
    ["Clone", "Debug", "PartialEq", "Eq"]
  _ ← assertEq "unresolvable ref conservative"
    (SchemaLang.Emit.Rust.derivesFor uni [.ty "ghost"])
    ["Clone", "Debug", "PartialEq"]
  _ ← assertEq "direct float blocks Eq"
    (SchemaLang.Emit.Rust.derivesFor uni [.f64])
    ["Clone", "Debug", "PartialEq"]
  -- the emitted struct carries the verdict
  let outerOut := CodegenCore.Emit.Rust.renderModule
    [SchemaLang.Emit.Rust.recordItem
      (SchemaLang.Emit.Rust.derivesFor uni [.ty "inner"]) outer]
  _ ← assert (outerOut.contains "#[derive(Clone, Debug, PartialEq)]")
    "outer derive line drops Eq"
  _ ← assert (!outerOut.contains ", Eq)]") "outer has no Eq derive"
  let cleanOut := CodegenCore.Emit.Rust.renderModule
    [SchemaLang.Emit.Rust.recordItem
      (SchemaLang.Emit.Rust.derivesFor uni [.ty "clean"]) viaClean]
  _ ← assert (cleanOut.contains "#[derive(Clone, Debug, PartialEq, Eq)]")
    "via-clean keeps Eq"
  .ok ()

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
  let out := CodegenCore.Emit.Rust.renderModule
    (demoItems.flatMap (Item.changeRustItems demoItems))
  _ ← assertEq "deterministic" out
    (CodegenCore.Emit.Rust.renderModule
      (demoItems.flatMap (Item.changeRustItems demoItems)))
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
  -- 0.2: a SECOND u8Enum shape binds its OWN suffix in
  -- `deserialize_metadata` (was: hardcoded "position" — the second
  -- enum would emit the first's metadata type)
  let lvl : SchemaLang.Vortex.ExtDTypeItem :=
    { rustName := "LevelExt", id := "test.level"
    , metadata := .u8Enum [1, 2] "level", storage := .free, external := false }
  let lvlOut := CodegenCore.Emit.Rust.renderModule
    [SchemaLang.Vortex.Emit.extVTableImpl lvl]
  _ ← assert (lvlOut.contains "type Metadata = LevelMetadata;")
    "assoc type from the shape's suffix"
  _ ← assert (lvlOut.contains "Some(LevelMetadata(bytes[0]))")
    "deserialize binds the shape's own suffix"
  _ ← assert (!lvlOut.contains "PositionMetadata") "no hardcoded suffix"
  -- determinism
  _ ← assertEq "ext deterministic" out
    (CodegenCore.Emit.Rust.renderModule
      (SchemaLang.Vortex.Emit.extDTypeModule SchemaLang.Vortex.Emit.extDTypes))
  -- the emitter: declared path + zero-input (ignores schema items)
  let files := SchemaLang.Vortex.Emit.extVortexEmitter.run []
  _ ← assertEq "ext path" (files.head?.map (·.path))
    (some "../../src/ext_dtypes_generated.rs")
  .ok ()

/-! ## Vortex well-formedness gate (3.5): every emitted dtype is wellFormed -/

/-- EVERY dtype the Vortex emitter emits for the demo universe
    satisfies the fork's construction-time well-formedness
    (`DType.wellFormed`, previously dead spec surface). An emitter
    emitting an ill-formed dtype while the spec says it can't is a REAL
    bug — this check is where it surfaces. -/
unsafe def vortexWellFormedChecks : IO (String × CheckResult) := do
  let items ← loadDemoItems
  let rds := SchemaLang.Vortex.Emit.recordDTypes items
  let nRecords := items.filter (fun it => match it with
    | .record _ _ => true | _ => false) |>.length
  let r : CheckResult := do
    -- non-vacuous: every demo record produced a dtype (the emitter's
    -- defensive skip would silently drop one)
    _ ← assert (rds.length > 0) "demo universe has records"
    _ ← assertEq "dtype count = record count" rds.length nRecords
    -- the gate: the exact dtype `recordItems` emits, well-formed
    for (n, fs) in rds do
      _ ← assert ((SchemaLang.Vortex.DType.struct fs .nonNullable).wellFormed)
        s!"{n}: emitted dtype well-formed"
    -- negative controls: the predicate CATCHES ill-formedness (incl. nested)
    _ ← assert (!(SchemaLang.Vortex.DType.decimal ⟨0, 3⟩ .nullable).wellFormed)
      "decimal precision 0 caught"
    _ ← assert (!(SchemaLang.Vortex.DType.decimal ⟨77, 0⟩ .nonNullable).wellFormed)
      "decimal precision 77 caught"
    _ ← assert (!(SchemaLang.Vortex.DType.list (.decimal ⟨0, 0⟩ .nonNullable) .nullable).wellFormed)
      "nested ill-formed caught"
    _ ← assert ((SchemaLang.Vortex.DType.decimal ⟨38, 2⟩ .nullable).wellFormed)
      "valid decimal accepted"
  pure ("vortexWellFormed", r)

/-! ## PType byteWidth / engineName wiring (3.5) -/

def ptypeChecks : CheckResult := do
  let all : List SchemaLang.Vortex.PType :=
    [.u8, .u16, .u32, .u64, .i8, .i16, .i32, .i64, .f16, .f32, .f64]
  -- the exact width table the Rust side assumes (the proved
  -- `PType.byteWidth_pos` is the invariant; this pins the VALUES)
  _ ← assertEq "byteWidth table" (all.map (·.byteWidth)) [1, 2, 4, 8, 1, 2, 4, 8, 2, 4, 8]
  _ ← assertEq "byteWidth > 0 (theorem, executed)" (all.all (·.byteWidth > 0)) true
  -- engineName: total + collision-free (the `engineName_inj` theorem,
  -- executed). No Rust-side name mapping exists in the tree yet
  -- (no crate consumes vortex), so this is the wiring for now.
  _ ← assertEq "engineName distinct" (decide ((all.map (·.engineName)).Nodup)) true
  _ ← assertEq "discriminant round-trip"
    (all.all fun p => SchemaLang.Vortex.PType.ofDiscriminant p.toDiscriminant == some p) true
  .ok ()

/-! ## EqAns routing (3.6): the diff's verdicts ARE the eqAns verdicts -/

/-- Reference shape equality built from `Ty.eqViaAns` ONLY (no derived
    `BEq` on the item structure) — the pin that the diff's item-level
    gate (`prev == it`, derived BEq) cannot drift from the EqAns-routed
    field comparison inside `fieldDiffsOf`. -/
def refShapeEq (a b : Item) : Bool :=
  a.name == b.name &&
    match a, b with
    | .record _ af, .record _ bf =>
        af.length == bf.length &&
          (af.zip bf).all fun (x, y) => x.name == y.name && x.ty.eqViaAns y.ty
    | .variant _ ac, .variant _ bc =>
        ac.length == bc.length &&
          (ac.zip bc).all fun ((cn, ct), (dn, dt)) =>
            cn == dn && match ct, dt with
            | some t, some s => t.eqViaAns s
            | none, none => true
            | _, _ => false
    | .func sigA, .func sigB =>
        sigA.params.length == sigB.params.length &&
          (sigA.params.zip sigB.params).all (fun ((n, t), (m, s)) =>
            n == m && t.eqViaAns s)
            && sigA.ret.eqViaAns sigB.ret
    | .resource _, .resource _ => true
    | _, _ => false

def eqAnsRoutingChecks : CheckResult := do
  -- eqViaAns verdicts on fixture types
  _ ← assert (Ty.eqViaAns (.option .u64) (.option .u64)) "eqViaAns yes"
  _ ← assert (!Ty.eqViaAns (.option .u64) (.option .u32)) "eqViaAns no"
  _ ← assert (!Ty.eqViaAns (.ty "a") (.ty "b")) "eqViaAns ty refs no"
  -- agreement over the whole demo universe squared (the `eqViaAns_beq`
  -- theorem, executed on the item gate)
  _ ← assertEq "BEq agrees with eqAns reference (demo²)"
    (demoItems.all fun a => demoItems.all fun b => (a == b) == refShapeEq a b) true
  -- same-name shape drift: both verdicts false, both ways
  let userRetyped : Item := .record "user" [{ name := "id", ty := .u32 }]
  _ ← assert (!(userRetyped == demoUser) && !refShapeEq userRetyped demoUser)
    "retyped field: both false"
  let rolePayload : Item := .variant "role" [("admin", some .u8)]
  _ ← assert (!(rolePayload == demoRole) && !refShapeEq rolePayload demoRole)
    "variant payload drift: both false"
  let retChanged : Item :=
    .func { name := "get-user", params := [("id", .u64)], ret := .ty "user" }
  _ ← assert (!(retChanged == demoGetUser) && !refShapeEq retChanged demoGetUser)
    "func ret drift: both false"
  -- positive: identical items, both true
  _ ← assert (demoUser == demoUser && refShapeEq demoUser demoUser) "identical: both true"
  .ok ()

/-! ## Snapshot codec (3.7): round-trip + malformed rejection -/

private def isErr (e : Except String α) : Bool :=
  match e with | .error _ => true | .ok _ => false

def snapshotChecks : CheckResult := do
  -- codec round-trip over the item-algebra fixture
  _ ← assert (match Snapshot.parse (Snapshot.render demoItems) with
    | .ok parsed => parsed == demoItems | .error _ => false) "fixture round-trip"
  -- ty codec pins (paren encoding, nesting, named refs)
  _ ← assertEq "ty encode"
    (Ty.toSnapshot (.option (.result (.ty "user") .string)))
    "option(result(ty(user),string))"
  _ ← assert (match Snapshot.parseTyText "option(result(ty(user),string))" with
    | .ok t => t == .option (.result (.ty "user") .string) | .error _ => false)
    "ty parse"
  -- malformed input is LOUD, never a silent skip
  _ ← assert (isErr (Snapshot.parse "field id u64\n"))
    "member without open item rejected"
  _ ← assert (isErr (Snapshot.parse "record a\nfield id option(u8\n"))
    "unbalanced paren rejected"
  _ ← assert (isErr (Snapshot.parse "record a\nbogus x\n"))
    "unknown line rejected"
  _ ← assert (isErr (Snapshot.parseTyText "u8x")) "unknown ty token rejected"
  _ ← assert (isErr (Snapshot.parseTyText "u8 u16")) "trailing garbage rejected"
  -- write-side gate: the fixture's names all round-trip
  _ ← assert (Snapshot.namesEncodable demoItems) "fixture names encodable"
  _ ← assert (!Snapshot.nameOk "has space") "nameOk rejects spaces"
  _ ← assert (!Snapshot.nameOk "has(paren") "nameOk rejects parens"
  .ok ()

/-- The `breaking` gate, replayed inside `lake test`: parse the
    COMMITTED baseline, diff against the live registry, and show the
    detector CATCHES sabotage (the negative-control discipline — a
    breaking-change detector that can't fire is vacuous). -/
unsafe def snapshotGateChecks : IO (String × CheckResult) := do
  let items ← loadDemoItems
  let text ← IO.FS.readFile "goldens/universe.snapshot"
  let r : CheckResult := do
    let baseline ← match Snapshot.parse text with
      | .ok b => .ok b
      | .error e => .error s!"committed snapshot unparsable: {e}"
    -- the gate itself: no breaking changes vs the committed baseline
    _ ← assertEq "no breaking vs snapshot"
      ((diff baseline items).all fun | .added _ => true | _ => false) true
    _ ← assert (backwardCompatible baseline items) "positive control: baseline compatible"
    -- round-trip on the LIVE registry (names as reflected, not the fixture)
    _ ← assert (match Snapshot.parse (Snapshot.render items) with
      | .ok parsed => parsed == items | .error _ => false)
      "snapshot round-trip (live registry)"
    _ ← assert (Snapshot.namesEncodable items) "live names encodable"
    -- negative controls against the REAL baseline
    let retyped := baseline.map fun it => match it with
      | .record "User" _ => Item.record "User" [{ name := "id", ty := .u32 }]
      | _ => it
    _ ← assert (!(backwardCompatible retyped items)) "retype sabotage caught"
    -- removal = the CURRENT universe missing an item the baseline has
    let shrunk := items.filter (·.name != "User")
    _ ← assert (!(backwardCompatible baseline shrunk)) "removal sabotage caught"
    -- sabotage realism: the controls actually changed the inputs
    _ ← assert (retyped != baseline && shrunk != items) "sabotage non-vacuous"
  pure ("snapshotGate", r)

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
  -- 1.6: every file `run` produces is a DECLARED output — `run` cannot
  -- re-state a path the one-writer audit doesn't know about
  _ ← assertEq "run outputs ⊆ declared outputs"
    (SchemaLang.Emit.emitters.all fun e =>
      (e.run demoItems).all fun f => e.outputs.contains f.path) true
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

/-! ## Property sweep (5.3): generated universes never yield unknownRef

`Ty` is a CLOSED universe — the generator emits only constructible
types over a fixed name supply, and the universe always anchors one
record/variant per supply name, so every generated `.ty` ref resolves.
The property: `universeCheck` over an anchored generated universe
reports ZERO `unknownRef` diagnostics. Other findings are legitimate
and NOT the property's subject: item names are drawn from the same
supply (so `dupName` fires) and generated record fields may carry
future/stream (so `asyncField` fires) — the property isolates NAME
RESOLUTION only.

The negative control (TestKit.PropSpec discipline): the sabotaged
sibling injects a `.ty "ghost"` ref into every sample — `universeCheck`
MUST flag it. A control that passes proves `noUnknownRef` vacuous and
the suite FAILS. -/
namespace PropSweep

open Plausible LSpec

/-- The fixed name supply: every generated `.ty` ref resolves against
    the anchors. -/
def nameSupply : List String := ["alpha", "beta", "gamma"]

/-- The anchors: one record/variant per supply name, so EVERY `.ty` ref
    drawn from the supply resolves no matter what the generator adds
    (duplicates only add `dupName` findings; they never remove
    resolvability). -/
def anchors : List Item :=
  [ .record "alpha" [], .record "beta" [], .variant "gamma" [] ]

/-- Small field/case/param name supply (not the property's subject). -/
def fieldSupply : List String := ["id", "name", "data"]

/-- Pick a name from a supply. -/
def pickName (supply : List String) : Gen String := do
  let n ← Gen.chooseNat
  pure (supply[n % supply.length]?.getD "alpha")

/-- Leaf types: the closed scalars plus a named ref from the supply.
    `oneOfWithDefault`, NOT `chooseNat % 14` — `chooseNat` ranges over
    [0, size], so a modulo with more branches than the size silently
    starves the tail branches (the 2026-11 `.ty`-leaf starvation: the
    coverage witness caught a generator that never emitted named refs). -/
def genTyLeaf (supply : List String) : Gen Ty :=
  Gen.oneOfWithDefault (pure .bool)
    [pure .u8, pure .u16, pure .u32, pure .u64,
     pure .i8, pure .i16, pure .i32, pure .i64,
     pure .f32, pure .f64, pure .string, pure .bytes,
     do pure (.ty (← pickName supply))]

/-- Sized random `Ty` over the closed universe: option/result/list/
    future/stream wrap smaller types; leaves are scalars or a named ref
    drawn from the supply. -/
def genTy (supply : List String) : Nat → Gen Ty
  | 0 => genTyLeaf supply
  | fuel + 1 => do
    let branch ← Gen.chooseNat
    match branch % 9 with
    | 0 => pure (.option (← genTy supply fuel))
    | 1 => pure (.result (← genTy supply fuel) (← genTy supply fuel))
    | 2 => pure (.list (← genTy supply fuel))
    | 3 => pure (.future (← genTy supply fuel))
    | 4 => pure (.stream (← genTy supply fuel))
    | _ => genTyLeaf supply

/-- The plausible instances: fueled generation driven by the size
    parameter. -/
instance : ArbitraryFueled Ty where
  arbitraryFueled := genTy nameSupply

instance : Arbitrary Ty where
  arbitrary := Gen.sized (ArbitraryFueled.arbitraryFueled ·)

/-- Shrink toward subterms — a failing nested type minimizes to the
    smallest failing fragment. -/
partial def shrinkTy : Ty → List Ty
  | .option a => a :: shrinkTy a
  | .result a b => a :: b :: (shrinkTy a ++ shrinkTy b)
  | .list a => a :: shrinkTy a
  | .future a => a :: shrinkTy a
  | .stream a => a :: shrinkTy a
  | t => [t]

instance : Shrinkable Ty where
  shrink t := (shrinkTy t).filter (· != t)

/-- A short list combinator (bounded length) over the small supplies. -/
def genShortList (g : Gen α) (maxLen : Nat) : Gen (List α) := do
  let len ← Gen.chooseNat
  let rec go : Nat → Gen (List α)
    | 0 => pure []
    | k + 1 => do pure ((← g) :: (← go k))
  go (len % (maxLen + 1))

/-- A generated field: name from the field supply, type from the fueled
    type generator. -/
def genField (supply : List String) (fuel : Nat) : Gen Field := do
  pure { name := (← pickName fieldSupply), ty := (← genTy supply fuel) }

/-- Sized random item over the closed vocabulary: record / variant /
    func / resource, all names from the supply, all types constructible. -/
def genItem (supply : List String) (fuel : Nat) : Gen Item := do
  let branch ← Gen.chooseNat
  match branch % 4 with
  | 0 => pure (.record (← pickName supply) (← genShortList (genField supply fuel) 3))
  | 1 => do
    let genCase : Gen VariantCase := do
      let c ← pickName fieldSupply
      let p ← Gen.chooseNat
      if p % 2 == 0 then pure (c, none)
      else pure (c, some (← genTy supply fuel))
    pure (.variant (← pickName supply) (← genShortList genCase 3))
  | 2 => do
    let genParam : Gen (String × Ty) := do
      pure (← pickName fieldSupply, ← genTy supply fuel)
    pure (.func { name := (← pickName supply)
                , params := (← genShortList genParam 2)
                , ret := (← genTy supply fuel) })
  | _ => pure (.resource (← pickName supply))

instance : ArbitraryFueled Item where
  arbitraryFueled := genItem nameSupply

instance : Arbitrary Item where
  arbitrary := Gen.sized (ArbitraryFueled.arbitraryFueled ·)

/-- Shrink an item: drop fields/cases/params. Names never shrink — the
    property is about name resolution, and shrinking names would only
    move a counterexample sideways. -/
def shrinkItem : Item → List Item
  | .record n fs => .record n [] :: fs.mapIdx fun i _ => .record n (fs.eraseIdx i)
  | .variant n cs => .variant n [] :: cs.mapIdx fun i _ => .variant n (cs.eraseIdx i)
  | .func s => [.func { s with params := [] }]
  | .resource _ => []

instance : Shrinkable Item where
  shrink := shrinkItem

/-- A generated universe TAIL (the anchors are fixed separately):
    bounded item count so `universeCheck` stays fast at 1000 instances. -/
structure UniverseTail where
  items : List Item
deriving Repr

instance : Arbitrary UniverseTail where
  arbitrary := Gen.sized fun fuel => do
    pure ⟨← genShortList (genItem nameSupply fuel) 5⟩

instance : Shrinkable UniverseTail where
  shrink u := (Shrinkable.shrink u.items).map UniverseTail.mk

/-- The property predicate: the universe's `universeCheck` reports NO
    `unknownRef` — every generated ref resolved. -/
def noUnknownRef (items : List Item) : Bool :=
  (universeCheck items).all fun d =>
    match d with | .unknownRef .. => false | _ => true

/-- The suite: 1000 instances, PINNED SEED — a CI failure replays
    byte-identically, and plausible's shrinker minimizes any
    counterexample. -/
def suite : TestSeq :=
  checkPlausibleIO "generated universes: zero unknownRef diagnostics"
    (∀ tail : UniverseTail, noUnknownRef (anchors ++ tail.items) = true)
    .done { numInst := 1000, randomSeed := some 20261104 }

/-- The negative control: a `.ty "ghost"` ref injected into EVERY
    sample — `universeCheck` MUST flag it (deterministic catch: the
    empty tail alone fails). If this suite passes, `noUnknownRef` is
    vacuous and the sweep proves nothing. -/
def controlSuite : TestSeq :=
  checkPlausibleIO "sabotaged: ghost ref injected (must be caught)"
    (∀ tail : UniverseTail,
      noUnknownRef (anchors ++ [.record "zz-saboteur" [{ name := "x", ty := .ty "ghost" }]]
        ++ tail.items) = true)
    .done { numInst := 1000, randomSeed := some 20261104 }

/-- The property spec: sweep + its mandatory negative control. -/
def spec : TestKit.PropSpec :=
  { name := "universeCheck: no unknownRef on generated universes"
  , suite := suite
  , control := controlSuite
  , controlName := "inject-ghost-ref" }

/-- Run a generator deterministically, purely (fixed seed and size) —
    the coverage witness below needs samples WITHOUT IO. -/
def runGenPure (g : Gen α) (seed : Nat) (size : Nat) : Except Plausible.GenError α :=
  (ReaderT.run (StateT.run g (ULift.up (mkStdGen seed))) ⟨size⟩).map (·.1)

/-- All types appearing in an item, constructors included (the coverage
    witness flattens generated universes with this). -/
partial def tysOf (t : Ty) : List Ty :=
  t :: match t with
  | .option a | .list a | .future a | .stream a => tysOf a
  | .result a b => tysOf a ++ tysOf b
  | _ => []

def itemTys : Item → List Ty
  | .record _ fs => fs.flatMap fun f => tysOf f.ty
  | .variant _ cs => (cs.filterMap (·.2)).flatMap tysOf
  | .func s => (s.params.map (·.2)).flatMap tysOf ++ tysOf s.ret
  | .resource _ => []

/-- The COVERAGE witness (deterministic, pinned seeds): across 20 fixed
    seeds the generator MUST emit named refs from the supply AND reach
    every recursive `Ty` constructor — otherwise the sweep is
    generator-vacuous even though the control bites (the control
    catches predicate vacuity, not generator silence). Also pins the
    property predicate on hand-built cases. -/
def propCoverageChecks : CheckResult := do
  let tails := (List.range 20).filterMap fun s =>
    match runGenPure (Arbitrary.arbitrary (α := UniverseTail)) (20261104 + s) 8 with
    | .ok t => some t.items
    | .error _ => none
  _ ← assertEq "generator produced samples" tails.isEmpty false
  let allTys := tails.flatten.flatMap itemTys
  let refs := tails.flatten.flatMap Item.tyRefs
  _ ← assert (refs.any fun r => nameSupply.contains r)
    "generator emits named refs from the supply"
  _ ← assert (allTys.any fun t => match t with | .option _ => true | _ => false)
    "generator reaches option"
  _ ← assert (allTys.any fun t => match t with | .result .. => true | _ => false)
    "generator reaches result"
  _ ← assert (allTys.any fun t => match t with | .list _ => true | _ => false)
    "generator reaches list"
  _ ← assert (allTys.any fun t => match t with | .future _ => true | _ => false)
    "generator reaches future"
  _ ← assert (allTys.any fun t => match t with | .stream _ => true | _ => false)
    "generator reaches stream"
  -- the predicate, pinned: a resolving ref passes, a bogus ref fails
  _ ← assertEq "predicate accepts resolving ref"
    (noUnknownRef (anchors ++ [.record "extra" [{ name := "x", ty := .ty "beta" }]])) true
  _ ← assertEq "predicate flags bogus ref"
    (noUnknownRef (anchors ++ [.record "extra" [{ name := "x", ty := .ty "ghost" }]])) false
  .ok ()

end PropSweep

/-! ## Typed session choreography (SchemaLang.Session) -/

def typedSessionChecks : CheckResult := do
  -- the gateway conversation: real Tys; wire names from the ONE renderer
  _ ← assertEq "gateway wire view" (toWire gatewayTyped).length 4
  _ ← assertEq "get-user payload on the wire"
      ((toWire gatewayTyped)[1].2) "option<user>"
  _ ← assertEq "watch-orders payload on the wire"
      ((toWire gatewayTyped)[3].2) "stream<user>"
  -- the bridge: the typed dual's wire view IS the wire dual (the
  -- string-layer guarantees transfer — Machines.Session proved them once)
  _ ← assert ((toWire (tdual gatewayTyped)) ==
      (Machines.Session.dual (toWire gatewayTyped))) "typed dual bridge"
  -- the typed dual keeps the schema types (payloads survive dualing)
  _ ← assert (((tdual gatewayTyped).map (·.2)) == (gatewayTyped.map (·.2)))
      "dual keeps types"
  -- directions oppose pairwise (lockstep)
  _ ← assertEq "directions oppose"
      (List.all (List.zip (gatewayTyped.map (·.1)) ((tdual gatewayTyped).map (·.1)))
        (fun x => x.1 != x.2)) true
  .ok ()

/-- 0.7 end-to-end: the reifier diagnoses a non-boundary FIELD TYPE as
    `nonBoundaryType` (naming the field, appending the boundary
    fragment) — not an unknown-type did-you-mean against TYPE names.
    `SchemaLang.Field` (in the Demo-imported env) has a `ty : Ty` field;
    `Ty` is not in the boundary fragment. -/
unsafe def reflectChecks : IO (String × CheckResult) := do
  let env ← loadDemoEnv
  let r ← match SchemaLang.Meta.checkStruct env ``SchemaLang.Field with
    | .inl [SchemaDiag.nonBoundaryType nm _] =>
        pure (assertEq "reifier names the field" nm "ty")
    | other => pure (.error s!"unexpected reifier diagnostics: {repr other}")
  pure ("reflect", r)

unsafe def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let goldens ← goldenChecks update
  let reflect ← reflectChecks
  let vortexWf ← vortexWellFormedChecks
  let snapGate ← snapshotGateChecks
  let code ← mainOfChecks "SchemaLang"
    ([ ("resolution", resolutionChecks)
     , ("fieldRes", fieldResolutionChecks)
     , ("codec", codecChecks)
     , ("codecCombinators", codecCombinatorChecks)
     , ("envelope", envelopeChecks)
     , ("eqAns", eqAnsChecks)
     , ("diff", diffChecks)
     , ("ptype", ptypeChecks)
     , ("eqAnsRouting", eqAnsRoutingChecks)
     , ("snapshot", snapshotChecks)
     ] ++ goldens ++
     [ ("lower", lowerChecks)
     , ("derives", derivesChecks)
     , reflect
     , vortexWf
     , snapGate
     , ("bridge", bridgeChecks)
     , ("bridgeSchema", bridgeSchemaChecks)
     , ("delta", deltaChecks)
     , ("extDType", extDTypeChecks)
     , ("pipelineConformance", pipelineConformanceChecks)
     , ("pipelineGuardControl", pipelineGuardControl)
     , ("pipelineRun", pipelineRunChecks)
     , ("emitterAudit", emitterAuditChecks)
     , ("typedSession", typedSessionChecks)
     , ("propCoverage", PropSweep.propCoverageChecks)
     ])
  if code != 0 then return code
  -- the property sweep WITH its mandatory negative control
  -- (TestKit.PropSpec: the property must pass AND the sabotaged sibling
  -- must be caught — a vacuous sweep fails the gate)
  TestKit.runSpecs [PropSweep.spec]
