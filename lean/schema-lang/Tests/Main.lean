/-
# SchemaLang Tests

Resolution wellFormed (accept/reject), EqAns direction, compat diff,
WIT golden emission.
-/
import Lean
import SchemaLang
import SchemaLang.Emit.GenCtx
import SchemaLang.Emit.Invariant
import SchemaLang.Emit.Update
import SchemaLang.Bridge
import Demo
import SchemaLang.Trace
import TestKit

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

open SchemaLang.Meta SchemaLang.Emit in
/-- The FULL demo GenCtx — all three registry lanes (items +
    invariants + updates), replayed from Demo's oleans (GenMain's
    pattern, v2 contract). -/
unsafe def loadDemoCtx : IO SchemaLang.Emit.GenCtx := do
  let env ← loadDemoEnv
  pure { items := (registeredItems env).map (·.2)
       , roots := SchemaLang.Emit.rootPartitionOf env (registeredItems env)
       , invariants := registeredInvariants env
       , updates := registeredUpdates env }

/-- Run every registry emitter over the CURRENT reflected Demo registry
    and byte-compare each output (header prepended, matching `schema-gen`'s
    write) against the committed golden under `goldens/<emitter>/`.
    `update = true` regenerates (the deliberate-change path). -/
unsafe def goldenChecks (update : Bool) : IO (List (String × CheckResult)) := do
  let ctx ← loadDemoCtx
  let mut results : List (String × CheckResult) := []
  for e in SchemaLang.Emit.emitters do
    for f in e.run ctx do
      let file := ((f.path : String).splitOn "/").getLast!
      let golden : System.FilePath := s!"goldens/{e.name}/{file}"
      CodegenCore.Emit.createParentDirs golden
      -- the CONTENT-only byte-tie: the header = the driver's metadata
      -- (the timestamp/git state change per regen); the content = the
      -- authority. The production header = `Emit.header`'s contract
      -- (codegen-core's headerCheck pins it).
      let out := CodegenCore.Emit.GeneratedFile.contents f
      let r ← TestKit.Golden.checkAgainstGolden e.name out golden update
      results := results ++ [(s!"{e.name}/{file}", r)]
  return results

/-! ## The root-namespace partition (the multi-world lane) -/

/-- The provenance partition pins: a demo-only ctx partitions under the
    ONE root (`Demo`, the declaring module — both packages declare at
    Lean's TRUE root, so the driver's module resolution is the provenance
    adapter); the gateway emitter folds the Demo partition (the same list
    the pre-partition fold saw — byte-identical gateway.wit), and the
    flags emitter over a demo-only replay renders the BARE flags world. -/
def partitionChecks (ctx : SchemaLang.Emit.GenCtx) : CheckResult := do
  _ ← assertEq "demo ctx: one root" ctx.roots.length 1
  _ ← assertEq "demo ctx: Demo root" (ctx.roots.head?.map (·.1)) (some `Demo)
  _ ← assert ((ctx.roots.head?.map (·.2)) == some ctx.items)
    "demo ctx: Demo partition = the items"
  -- the gateway emitter's fold input = the Demo partition (unchanged bytes)
  _ ← assert ((witEmitter.run ctx).head?.map (·.contents) ==
    some (SchemaLang.Emit.Wit.worldOf "demo:gateway" "gateway" ctx.items))
    "gateway folds the Demo partition"
  -- the flags emitter: declared path + the empty-partition world
  let some ff := SchemaLang.Emit.emitters.find? fun e => e.name == "flags-wit" |
    throw "flags-wit emitter not registered"
  let files := ff.run ctx
  _ ← assertEq "flags path" (files.head?.map (·.path)) (some "../../wit/flags.wit")
  _ ← assert ((files.head?.map (·.contents) |>.getD "").contains "world flags {")
    "flags world rendered (empty partition = the bare world)"
  -- the lookup is total over the roots the ctx names
  _ ← assert (ctx.rootItems `NoSuchRoot == [])
    "rootItems misses are empty"
  .ok ()

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
  let files := deltaEmitter.run (SchemaLang.Emit.GenCtx.itemsOnly demoItems)
  _ ← assertEq "delta path" (files.head?.map (·.path)) (some "../../src/delta_generated.rs")
  _ ← assertEq "delta deterministic" (files.map (·.contents))
    ((deltaEmitter.run (SchemaLang.Emit.GenCtx.itemsOnly demoItems)).map (·.contents))
  let wfiles := deltaWitEmitter.run (SchemaLang.Emit.GenCtx.itemsOnly demoItems)
  _ ← assertEq "deltaWit path" (wfiles.head?.map (·.path)) (some "../../wit/delta.wit")
  let wout := wfiles.head?.map (·.contents) |>.getD ""
  _ ← assertEq "deltaWit deterministic" wout
    ((deltaWitEmitter.run (SchemaLang.Emit.GenCtx.itemsOnly demoItems)).head?.map (·.contents) |>.getD "")
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
  let files := SchemaLang.Vortex.Emit.extVortexEmitter.run
    (SchemaLang.Emit.GenCtx.itemsOnly [])
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
    -- round-trip on the LIVE registry (names as reflected, not the fixture);
    -- the spec-surface comparison — `body` is registry metadata, the wire
    -- format doesn't carry it, parse reconstructs it anonymous
    _ ← assert (match Snapshot.parse (Snapshot.render items) with
      | .ok parsed => (parsed.zip items).all fun (p, l) => p.specEq l
      | .error _ => false)
      "snapshot round-trip (live registry, spec surface)"
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

-- The order lifecycle machine (the FIRST DOMAIN machine): the
-- conformance battery sweeps its state space; the replay theorems
-- (`lifecycle_happy_path`, `terminal_only_reset`, ...) are
-- compile-time; the emitted Rust is replay-tested host-side
-- (steel-host's order_machine.rs).
def orderMachineChecks : CheckResult := do
  let rs := orderConformance
  for (name, r) in rs do
    match r with
    | .ok () => pure ()
    | .error msg => throw s!"order-machine conformance {name}: {msg}"
  _ ← assert (rs.any (·.1 == "deadlock-freedom")) "deadlock-freedom ran"
  _ ← assert (rs.any (·.1 == "guard-coverage")) "guard-coverage ran"
  -- the executable discipline (the theorems' run-level shadows)
  match orderMachine.run .cart [.place, .ship, .deliver] with
  | some (_, .delivered) => pure ()
  | _ => throw "order happy path rejected"
  match orderMachine.run .cart [.ship] with
  | none => pure ()
  | some _ => throw "ship-before-place accepted"
  match orderMachine.step? .delivered .ship with
  | none => pure ()
  | some _ => throw "delivered reopened"
  .ok ()

/-- The happy path executes end-to-end and out-of-order firing is
    rejected; acyclicity is `pipeline_rank_advances_tr` (compile-time, above). -/
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
def emitterAuditChecks (ctx : SchemaLang.Emit.GenCtx) : CheckResult := do
  _ ← assertEq "emitter paths unique" SchemaLang.Emit.pathsUnique true
  -- the forge-driver audit: every registered emitter's output is in the
  -- job manifest forge consumes — no artifact silently outside byte-tie
  _ ← assertEq "jobs cover emitters" SchemaLang.Emit.jobsCoverEmitters true
  -- 1.6: every file `run` produces is a DECLARED output — `run` cannot
  -- re-state a path the one-writer audit doesn't know about
  _ ← assertEq "run outputs ⊆ declared outputs"
    (SchemaLang.Emit.emitters.all fun e =>
      (e.run ctx).all fun f => e.outputs.contains f.path) true
  -- 6.5.3: emitter-output SELF-AUDIT — every registered emitter's output
  -- (raw, pre-driver-header) is swept for banned constructs. GuestGate
  -- bans constructs in guest SOURCE; this audits the EMITTED text, so a
  -- generator regression that starts emitting one fails CI even though
  -- the generator compiles. (The GENERATED banner is NOT audited here:
  -- headers are the DRIVER's prepend — gen-check's byte-tie owns that.)
  _ ← assert
    (SchemaLang.Emit.emitters.all fun e =>
      (e.run ctx).all fun f =>
        GateKit.auditFindings SchemaLang.Emit.emitterAuditRules f.contents
          |>.isEmpty)
    "emitter self-audit (banned constructs)"
  -- the GENERATED ChangeSpec trait: emitted from `Dbsp.ChangeSpec`'s
  -- class fields (`patch`/`valid`) — the method names ARE the class
  -- field names, pinned here so the emitter and the Lean class cannot
  -- drift apart (the Rust side re-exports the generated trait)
  let traitText :=
    (changeSpecEmitter.run (SchemaLang.Emit.GenCtx.itemsOnly [])).head?
      |>.map (·.contents)
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

open Plausible

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

/-! ## Value codec (CodecValue): the schema-typed wire round trip

`encodeValue`/`decodeValue` connect the `Value t` GADT to the wire. The
sweep generates `(Ty, Value t)` packs from the PROVED sub-universe
(`CodecClosed`) and checks the executable image of the kernel theorem
`decode_encodeValue`. The negative control corrupts bool/u8 payloads —
`decodeValue (encodeValue (corrupt v))` can never equal v at those
leaves, so any sample of them bites. -/

namespace CodecValueSweep

open Plausible

/-- A sample: a codec-closed type, its proof, and a value at it. -/
structure Pack where
  t : Ty
  h : CodecClosed t
  val : Value t

/-! ### the executable equality on `Value t` (the theorem's witness) -/

-- Size measure for the mutual structural recursion.
mutual

def sizeV : (t : Ty) → Value t → Nat
  | .bool, _ => 1
  | .u8, _ => 1
  | .u16, _ => 1
  | .u32, _ => 1
  | .u64, _ => 1
  | .i8, _ => 1
  | .i16, _ => 1
  | .i32, _ => 1
  | .i64, _ => 1
  | .f32, _ => 1
  | .f64, _ => 1
  | .string, _ => 1
  | .bytes, _ => 1
  | .option _, .none => 1
  | .option a, .some x => sizeV a x + 1
  | .result ok _, .ok x => sizeV ok x + 1
  | .result _ err, .err x => sizeV err x + 1
  | .future a, .future x => sizeV a x + 1
  | .list a, .list vl => sizeL a vl + 1
  | .stream a, .stream vl => sizeL a vl + 1

def sizeL : (t : Ty) → VList t → Nat
  | _, .nil => 0
  | t, .cons v vl => sizeV t v + sizeL t vl + 1

end

-- Structural equality on `Value t` (Bool-valued — the sweep and the
-- checks compare decoded against encoded through it).
-- (plain comment: `mutual` cannot follow a doc comment)

-- Structural equality on `Value t`, THROUGH the codec: two values are
-- equal iff their encodings are byte-equal. NOT a GADT match — the
-- three-arg GADT match's unfold equations are underivable (the
-- catch-all-vs-refined splitter limit); the codec route is total,
-- reflexive (byte equality), and faithful on the codec-closed universe
-- (the round-trip theorem: equal bytes decode equal). The sweep and
-- the checks consume this.
def valueEq (t : Ty) (a b : Value t) : Bool :=
  encodeValue t a == encodeValue t b

-- the refl pin, kernel-checked (the sweep's equality is not vacuous):
theorem valueEq_refl (t : Ty) (v : Value t) : valueEq t v v = true :=
  beq_self_eq_true _

-- Debug rendering of a `Value t` (Plausible counterexample output).
mutual

def valueReprStr : (t : Ty) → Value t → String
  | .bool, .bool b => s!"bool {b}"
  | .u8, .u8 x => s!"u8 {x}"
  | .u16, .u16 x => s!"u16 {x}"
  | .u32, .u32 x => s!"u32 {x}"
  | .u64, .u64 x => s!"u64 {x}"
  | .i8, .i8 x => s!"i8 {x.toInt}"
  | .i16, .i16 x => s!"i16 {x.toInt}"
  | .i32, .i32 x => s!"i32 {x.toInt}"
  | .i64, .i64 x => s!"i64 {x.toInt}"
  | .f32, .f32 x => s!"f32 {x}"
  | .f64, .f64 x => s!"f64 {x}"
  | .string, .string s => s!"string \"{s}\""
  | .bytes, .bytes bs => s!"bytes {bs}"
  | .option _, .none => "none"
  | .option t, .some x => s!"some ({valueReprStr t x})"
  | .result ok _, .ok x => s!"ok ({valueReprStr ok x})"
  | .result _ err, .err x => s!"err ({valueReprStr err x})"
  | .future t, .future x => s!"future ({valueReprStr t x})"
  | .list t, .list vl => s!"list [{vListReprStr t vl}]"
  | .stream t, .stream vl => s!"stream [{vListReprStr t vl}]"
  termination_by t v => sizeV t v
decreasing_by all_goals (simp [sizeV, sizeL] <;> omega)

def vListReprStr : (t : Ty) → VList t → String
  | _, .nil => ""
  | t, .cons v vl =>
      let rest := vListReprStr t vl
      if rest == "" then valueReprStr t v else s!"{valueReprStr t v}, {rest}"
  termination_by t vl => sizeL t vl
decreasing_by all_goals (simp [sizeV, sizeL] <;> omega)

end

-- (the checks consuming these renderings follow)

instance : Repr Pack where
  reprPrec p _ := s!"⟨{repr p.t}, {valueReprStr p.t p.val}⟩"

instance : Shrinkable Pack where
  shrink p :=
    if valueEq p.t p.val (defaultValue p.t p.h) then []
    else [⟨p.t, p.h, defaultValue p.t p.h⟩]

/-! ### the generators -/

/-- Short bounded list. -/
def genShortList (g : Gen α) (maxLen : Nat) : Gen (List α) := do
  let len ← Gen.chooseNat
  let rec go : Nat → Gen (List α)
    | 0 => pure []
    | k + 1 => do pure ((← g) :: (← go k))
  go (len % (maxLen + 1))

def genChar : Gen Char := do
  let n ← Gen.chooseNat
  pure (Char.ofNat ('a'.toNat + n % 3))

def genU8 : Gen UInt8 := do
  pure ((← Gen.chooseNat) % 256).toUInt8

/-- One value of type `t` (must be codec-closed), size-bounded by fuel. -/
def genVal : (t : Ty) → CodecClosed t → Nat → Gen (Value t)
  | .bool, _, _ => do pure (.bool ((← Gen.chooseNat) % 2 == 0))
  | .u8, _, _ => do pure (.u8 (← genU8))
  | .u16, _, _ => do pure (.u16 ((← Gen.chooseNat) % 65536).toUInt16)
  | .u32, _, _ => do pure (.u32 ((← Gen.chooseNat) % 4294967296).toUInt32)
  | .u64, _, _ => do
      pure (.u64 ((← Gen.chooseNat) % 18446744073709551616).toUInt64)
  | .i8, _, _ => do pure (.i8 (Int8.ofInt (unzigzag ((← Gen.chooseNat) % 200))))
  | .i16, _, _ => do
      pure (.i16 (Int16.ofInt (unzigzag ((← Gen.chooseNat) % 40000))))
  | .i32, _, _ => do
      pure (.i32 (Int32.ofInt (unzigzag ((← Gen.chooseNat) % 4000000000))))
  | .i64, _, _ => do
      pure (.i64 (Int64.ofInt (unzigzag ((← Gen.chooseNat) % 1000000000000000000))))
  | .string, _, _ => do pure (.string (String.ofList (← genShortList genChar 4)))
  | .bytes, _, _ => do pure (.bytes (← genShortList genU8 4))
  | .option t, .option h, fuel + 1 => do
      let b ← Gen.chooseNat
      if b % 2 == 0 then pure .none else pure (.some (← genVal t h fuel))
  | .result ok err, .result hok herr, fuel + 1 => do
      let b ← Gen.chooseNat
      if b % 2 == 0 then pure (.ok (← genVal ok hok fuel))
      else pure (.err (← genVal err herr fuel))
  | .list t, .list h, fuel + 1 => do
      pure (.list (listToVList (← genShortList (genVal t h fuel) 3)))
  | .future t, .future h, fuel + 1 => do pure (.future (← genVal t h fuel))
  | .stream t, .stream h, fuel + 1 => do
      pure (.stream (listToVList (← genShortList (genVal t h fuel) 3)))
  -- fuel 0: composites fall back to the default value (u8 is the
  -- oneOfWithDefault default leaf below, so the control still bites)
  | t, h, 0 => pure (defaultValue t h)
  termination_by _ _ fuel => fuel

def genLeafPack : Gen Pack :=
  Gen.oneOfWithDefault
    (do pure ⟨.u8, .u8, .u8 (← genU8)⟩)
    [ do pure ⟨.bool, .bool, .bool ((← Gen.chooseNat) % 2 == 0)⟩
    , do pure ⟨.u16, .u16, .u16 ((← Gen.chooseNat) % 65536).toUInt16⟩
    , do pure ⟨.u32, .u32, .u32 ((← Gen.chooseNat) % 4294967296).toUInt32⟩
    , do
        pure ⟨.u64, .u64, .u64 ((← Gen.chooseNat) % 18446744073709551616).toUInt64⟩
    , do pure ⟨.i8, .i8, .i8 (Int8.ofInt (unzigzag ((← Gen.chooseNat) % 200)))⟩
    , do
        pure ⟨.i16, .i16, .i16 (Int16.ofInt (unzigzag ((← Gen.chooseNat) % 40000)))⟩
    , do
        pure ⟨.i32, .i32,
          .i32 (Int32.ofInt (unzigzag ((← Gen.chooseNat) % 4000000000)))⟩
    , do
        pure ⟨.i64, .i64,
          .i64 (Int64.ofInt (unzigzag ((← Gen.chooseNat) % 1000000000000000000)))⟩
    , do pure ⟨.string, .string, .string (String.ofList (← genShortList genChar 3))⟩
    , do pure ⟨.bytes, .bytes, .bytes (← genShortList genU8 3)⟩ ]

def genPack : Nat → Gen Pack
  | 0 => genLeafPack
  | fuel + 1 => do
    let branch ← Gen.chooseNat
    match branch % 6 with
    | 0 => genLeafPack
    | 1 => do
      let p ← genPack fuel
      let b ← Gen.chooseNat
      if b % 2 == 0 then pure ⟨.option p.t, .option p.h, .none⟩
      else pure ⟨.option p.t, .option p.h, .some p.val⟩
    | 2 => do
      let p ← genPack fuel
      let q ← genPack fuel
      let b ← Gen.chooseNat
      if b % 2 == 0 then pure ⟨.result p.t q.t, .result p.h q.h, .ok p.val⟩
      else pure ⟨.result p.t q.t, .result p.h q.h, .err q.val⟩
    | 3 => do
      let p ← genPack fuel
      let vs ← genShortList (genVal p.t p.h fuel) 3
      pure ⟨.list p.t, .list p.h, .list (listToVList vs)⟩
    | 4 => do
      let p ← genPack fuel
      pure ⟨.future p.t, .future p.h, .future p.val⟩
    | _ => do
      let p ← genPack fuel
      let vs ← genShortList (genVal p.t p.h fuel) 3
      pure ⟨.stream p.t, .stream p.h, .stream (listToVList vs)⟩
  termination_by fuel => fuel

instance : ArbitraryFueled Pack where
  arbitraryFueled := genPack

instance : Arbitrary Pack where
  arbitrary := Gen.sized genPack

/-! ### the property, its control, and the coverage pins -/

/-- The executable image of `decode_encodeValue`: decode (encode p) = p. -/
def valueRoundtrip (p : Pack) : Bool :=
  match decodeValue p.t (encodeValue p.t p.val) with
  | some v => valueEq p.t v p.val
  | none => false

/-- Negative-control corruption: flip bool payloads, bump u8 payloads. -/
def corrupt : (t : Ty) → Value t → Value t
  | .bool, .bool b => .bool (!b)
  | .u8, .u8 x => .u8 (x + 1)
  | _, v => v

/-- The corrupted sibling: round-trips the corrupted value but checks it
    against the ORIGINAL — a bool/u8 sample can never pass. -/
def controlRoundtrip (p : Pack) : Bool :=
  match decodeValue p.t (encodeValue p.t (corrupt p.t p.val)) with
  | some v => valueEq p.t v p.val
  | none => false

/-- The suite: 1000 instances, pinned seed. -/
def suite : TestSeq :=
  checkPlausibleIO "Value codec: decodeValue ∘ encodeValue = some over generated packs"
    (∀ p : Pack, valueRoundtrip p = true)
    .done { numInst := 1000, randomSeed := some 20261105 }

/-- The negative control: corrupted bool/u8 payloads MUST be caught. If
    this suite passes, `valueRoundtrip` is vacuous and proves nothing. -/
def controlSuite : TestSeq :=
  checkPlausibleIO "sabotaged: bool/u8 payload corruption (must be caught)"
    (∀ p : Pack, controlRoundtrip p = true)
    .done { numInst := 1000, randomSeed := some 20261105 }

/-- The property spec: sweep + its mandatory negative control. -/
def spec : TestKit.PropSpec :=
  { name := "decode_encodeValue: Value round trip over the CodecClosed universe"
  , suite := suite
  , control := controlSuite
  , controlName := "corrupt-bool-u8" }

/-- Deterministic pins: every covered `Ty` shape round-trips by hand-built
    value (the theorem, executed), and malformed wire is rejected. -/
def coverageChecks : CheckResult := do
  let packs : List Pack :=
    [ ⟨.bool, .bool, .bool true⟩
    , ⟨.u8, .u8, .u8 42⟩
    , ⟨.u16, .u16, .u16 65535⟩
    , ⟨.u32, .u32, .u32 4000000000⟩
    , ⟨.u64, .u64, .u64 18000000000000000000⟩
    , ⟨.i8, .i8, .i8 (Int8.ofInt (-128))⟩
    , ⟨.i16, .i16, .i16 (Int16.ofInt (-30000))⟩
    , ⟨.i32, .i32, .i32 (Int32.ofInt (-2000000000))⟩
    , ⟨.i64, .i64, .i64 (Int64.ofInt (-9000000000000000000))⟩
    , ⟨.string, .string, .string "hello"⟩
    , ⟨.bytes, .bytes, .bytes [1, 2, 3]⟩
    , ⟨.option .u8, .option .u8, .none⟩
    , ⟨.option .u8, .option .u8, .some (.u8 7)⟩
    , ⟨.result .u8 .string, .result .u8 .string, .ok (.u8 1)⟩
    , ⟨.result .u8 .string, .result .u8 .string, .err (.string "no")⟩
    , ⟨.list .u8, .list .u8, .list (listToVList [.u8 1, .u8 2, .u8 3])⟩
    , ⟨.future .u8, .future .u8, .future (.u8 9)⟩
    , ⟨.stream .u8, .stream .u8, .stream (listToVList [.u8 4])⟩
    , ⟨.option (.list .u8), .option (.list .u8),
        .some (.list (listToVList [.u8 1, .u8 2]))⟩ ]
  for p in packs do
    _ ← assert (valueRoundtrip p) s!"roundtrip {valueReprStr p.t p.val}"
  -- the refl pin: the sweep's equality is reflexive (kernel-checked
  -- `valueEqRefl`, executed on a composite)
  _ ← assertEq "valueEq refl (composite)"
    (valueEq (.list .u8) (.list (listToVList [.u8 1, .u8 2]))
      (.list (listToVList [.u8 1, .u8 2]))) true
  -- rejection: truncation and empty wire (no BEq on GADT Options —
  -- the isNone projection is the Bool reading)
  _ ← assert (decodeValue .u8 []).isNone "u8 truncation rejected"
  _ ← assert (decodeValue (.option .u8) []).isNone "option truncation rejected"
  _ ← assert (decodeValue (.list .u8) [2]).isNone "list truncation rejected"
  -- ([1, 2] is NOT malformed: one element + remainder — decodeValue
  -- discards the remainder; [2] = length-2 prefix with no elements IS)
  -- the theorem's object, EXECUTED: decode ∘ encode lands the value
  -- (GADT pattern match, not BEq — there is no decidable-eq on Value)
  let pin : Bool :=
    match decodeValue .u8 (encodeValue .u8 (.u8 42)) with
    | some (.u8 42) => true
    | _ => false
  _ ← assert pin "theorem pin: decode ∘ encode lands the value"
  .ok ()

end CodecValueSweep

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

/-! ## 6.5.1: func semantic fields as DATA (nullSem + determinism)

The `@[schema_fn]` probes below pin the REFLECTION round trip at
compile time (a reflection failure fails this module's build); the
`funcSemChecks` suite pins the data at runtime. -/

/-- Probe: one ident arg sets the determinism axis only. -/
@[schema_fn volatile]
def probeVolatileFn (x : UInt32) : UInt32 := x

/-- Probe: the dot-joined pair sets BOTH axes (either order). -/
@[schema_fn strict.volatile]
def probeBothAxesFn (x : Option UInt32) : Option UInt32 := x

/-- Probe: no args — the defaults. (Two params: bodies of the one-param
probes must stay distinct — dupDefBodies clusters body-identical defs.) -/
@[schema_fn]
def probeDefaultFn (x _y : UInt32) : UInt32 := x

-- Compile-time reflection pin: the attribute's optional ident args
-- land in the registry as `FuncSem` DATA.
open Lean Elab Command in
run_cmd do
  let items := SchemaLang.Meta.registeredItems (← getEnv)
  let semOf (n : Name) : CommandElabM FuncSem := do
    match items.find? (fun (ln, _) => ln == n) with
    | some (_, .func sig) => pure sig.sem
    | _ => throwError "{n}: not registered as a func item"
  unless (← semOf ``probeVolatileFn) == ⟨.propagate, .volatile, .once⟩ do
    throwError "probeVolatileFn: determinism arg not reflected"
  unless (← semOf ``probeBothAxesFn) == ⟨.strict, .volatile, .once⟩ do
    throwError "probeBothAxesFn: dot-joined axes not reflected"
  unless (← semOf ``probeDefaultFn) == ({} : FuncSem) do
    throwError "probeDefaultFn: defaults not preserved"
  -- 6.5.1 `body`: the attr auto-fills the declaring constant's name —
  -- the executable-semantics pointer downstream consumers fold over
  let bodyOf (n : Name) : CommandElabM Name := do
    match (SchemaLang.Meta.registeredItems (← getEnv)).find? (fun (ln, _) => ln == n) with
    | some (_, .func sig) => pure sig.body
    | _ => throwError "{n}: not registered"
  unless (← bodyOf ``probeVolatileFn) == ``probeVolatileFn do
    throwError "probeVolatileFn: body not auto-filled"
  unless (← bodyOf ``getUser) == ``getUser do
    throwError "getUser: body not auto-filled"

def funcSemChecks : CheckResult := do
  -- defaults on constructed items: existing fixtures need no changes
  match demoGetUser with
  | .func sig =>
      _ ← assert (sig.sem == ({} : FuncSem)) "constructed func defaults (propagate, pure)"
  | _ => throw "demoGetUser is not a func"
  -- a volatile fn CAN be constructed and validates clean (no
  -- pure-context role exists yet, so nothing fires on it)
  let volFn : Item := .func { name := "f", params := [("x", .option .u32)]
                            , ret := .u64, sem := ⟨.strict, .volatile, .once⟩ }
  _ ← assertEq "volatile fn validates" (universeCheck [volFn]) []
  -- the armed diag ctor: render names the fn + the context and
  -- enumerates the valid space (the full-valid-space diag style)
  let d := SchemaDiag.render (.volatileInPureContext "clock" "aggregator")
  _ ← assert (d.contains "`clock`") "diag names the fn"
  _ ← assert (d.contains "aggregator") "diag names the context"
  _ ← assert (d.contains "pure, stable") "diag enumerates the valid space"
  -- the attr-arg parser's error paths (positive paths are the probes
  -- above — attribute errors are elaboration errors, untestable in-build)
  let mkSimple (arg : String) : Lean.Syntax :=
    Lean.mkNode `Lean.Parser.Attr.simple
      #[Lean.mkIdent `schema_fn, Lean.mkNullNode #[Lean.mkIdent arg.toName]]
  _ ← assert (match SchemaLang.Meta.funcSemOfStx (mkSimple "bogus") with
    | .error e => e.contains "valid: strict, propagate, custom"
    | .ok _ => false) "unknown arg rejected with valid space"
  _ ← assert (match SchemaLang.Meta.funcSemOfStx (mkSimple "volatile.stable") with
    | .error e => e.contains "duplicate determinism"
    | .ok _ => false) "duplicated axis rejected"
  _ ← assert (match SchemaLang.Meta.funcSemOfStx (mkSimple "strict.volatile.pure.stream.once") with
    | .error e => e.contains "too many"
    | .ok _ => false) ">3 parts rejected"
  -- the delivery axis: stream parses (alone and dot-joined); once = default
  _ ← assert (match SchemaLang.Meta.funcSemOfStx (mkSimple "stream") with
    | .ok sem => sem.delivery == (.stream : SchemaLang.Delivery)
    | .error _ => false) "stream delivery parses"
  _ ← assert (match SchemaLang.Meta.funcSemOfStx (mkSimple "strict.stream") with
    | .ok sem => sem == ⟨.strict, .pure, .stream⟩
    | .error _ => false) "dot-joined delivery parses"
  _ ← assert (match SchemaLang.Meta.funcSemOfStx (mkSimple "stream.once") with
    | .error e => e.contains "duplicate delivery"
    | .ok _ => false) "duplicated delivery rejected"
  _ ← assert (match SchemaLang.Meta.funcSemOfStx (mkSimple "custom.pure") with
    | .ok sem => sem == ⟨.custom, .pure, .once⟩
    | .error _ => false) "dot-joined pair parses"
  -- snapshot codec: the sem line round-trips; defaults stay byte-compatible
  let text := Snapshot.render [volFn]
  _ ← assert (text.contains "sem strict volatile") "non-default sem line emitted"
  _ ← assert (match Snapshot.parse text with
    | .ok parsed => parsed == [volFn] | .error _ => false) "sem round-trip"
  let defText := Snapshot.render [demoGetUser]
  _ ← assert (!defText.contains "sem ") "default sem emits no sem line"
  _ ← assert (match Snapshot.parse defText with
    | .ok parsed => parsed == [demoGetUser] | .error _ => false) "default round-trip"
  -- legacy format (no sem line) parses to the defaults
  _ ← assert (match Snapshot.parse "func f\nret u64\n" with
    | .ok [.func sig] => sig.sem == ({} : FuncSem)
    | _ => false) "legacy snapshot → defaults"
  -- malformed sem lines are LOUD
  _ ← assert (isErr (Snapshot.parse "func f\nret u64\nsem bogus pure\n"))
    "unknown nullSem token rejected"
  _ ← assert (isErr (Snapshot.parse "func f\nsem strict volatile\n"))
    "sem before ret rejected"
  _ ← assert (isErr (Snapshot.parse "record r\nsem strict volatile\n"))
    "sem outside a func rejected"
  -- diff evidence: sem-only drift is `changed` WITH evidence
  let f1 : Item := .func { name := "f", params := [], ret := .u64 }
  let f2 : Item := .func { name := "f", params := [], ret := .u64
                         , sem := ⟨.strict, .volatile, .once⟩ }
  _ ← assertEq "sem-only drift reported with evidence" (diff [f1] [f2])
    [.changed "f" [.semChanged {} ⟨.strict, .volatile, .once⟩]]
  .ok ()

/-- Live-registry pin: the reflected Demo funcs carry the defaults
    (existing items unchanged — 6.5.1 requirement 3). -/
unsafe def funcSemReflectChecks : IO (String × CheckResult) := do
  let items ← loadDemoItems
  let r : CheckResult := do
    match items.find? (·.name == "getUser") with
    | some (.func sig) =>
        _ ← assert (sig.sem == ({} : FuncSem)) "getUser: defaults"
    | _ => throw "getUser not in the reflected registry"
    match items.find? (·.name == "watchOrders") with
    | some (.func sig) =>
        _ ← assert (sig.sem == ({} : FuncSem)) "watchOrders: defaults"
    | _ => throw "watchOrders not in the reflected registry"
  pure ("funcSemReflect", r)

/-! ## 6.5.2: migration soundness (the REMEDY half of the breaking gate) -/

def migrationChecks : CheckResult := do
  -- the demo: `OrderItem.qty` retyped u32 → u64, remedied by widening
  let v1 : List Item := [.record "OrderItem" [⟨"id", .u64⟩, ⟨"qty", .u32⟩]]
  let v2 : List Item := [.record "OrderItem" [⟨"id", .u64⟩, ⟨"qty", .u64⟩]]
  let changes := diff v1 v2
  _ ← assertEq "demo change detected" changes
    [.changed "OrderItem" [.fieldTypeChanged "qty" .u32 .u64]]
  let m : Migration := { item := "OrderItem", fields := [widenU32U64 "qty"] }
  -- the soundness theorem, executed (applyMigration old = new shape):
  -- the widened value IS the same number
  _ ← assert (((widenU32U64 "qty").apply (42 : UInt32)).toNat == 42)
    "widen sound at 42"
  _ ← assert (((widenU32U64 "qty").apply (4294967295 : UInt32)).toNat == 4294967295)
    "widen sound at u32 max"
  -- the verdict distinguishes remedied from unremedied
  _ ← assertEq "remedied verdict" (verdictOf changes [m]) .remedied
  _ ← assertEq "unremedied without evidence" (verdictOf changes []) .unremedied
  let v3 := v1 ++ [.record "New" []]
  _ ← assertEq "clean on additions" (verdictOf (diff v1 v3) []) .clean
  -- negative controls: the remedy match is not vacuous
  let wrongItem : Migration := { item := "Other", fields := [widenU32U64 "qty"] }
  _ ← assertEq "wrong item name: unremedied" (verdictOf changes [wrongItem]) .unremedied
  let wrongTy : Migration :=
    { item := "OrderItem"
    , fields := [{ field := "qty", oldTy := .u16, newTy := .u64
                 , apply := fun v => v.toUInt64 }] }
  _ ← assertEq "wrong old type: unremedied" (verdictOf changes [wrongTy]) .unremedied
  -- removals are honestly unremedied (no value-map target)
  let vShrink : List Item := [.record "OrderItem" [⟨"id", .u64⟩]]
  _ ← assertEq "field removal: unremedied even with evidence"
    (verdictOf (diff v1 vShrink) [m]) .unremedied
  _ ← assertEq "item removal: unremedied" (verdictOf (diff v1 []) [m]) .unremedied
  -- semChanged drift is unremedied in v1
  let f1 : Item := .func { name := "f", params := [], ret := .u64 }
  let f2 : Item := .func { name := "f", params := [], ret := .u64
                         , sem := ⟨.propagate, .volatile, .once⟩ }
  _ ← assertEq "sem drift: unremedied" (verdictOf (diff [f1] [f2]) []) .unremedied
  -- the exit-code mapping (the ONLY mapping — BreakingMain consumes it)
  _ ← assertEq "clean exit" CompatVerdict.clean.exitCode 0
  _ ← assertEq "unremedied exit" CompatVerdict.unremedied.exitCode 1
  _ ← assertEq "remedied exit (distinct — action required)"
    CompatVerdict.remedied.exitCode 2
  -- the AUTHORING SURFACE: Demo.registeredMigrations is what `just
  -- breaking` consumes — the registered row remedies exactly the qty
  -- retype (and nothing else), and its presence cannot fake a clean
  -- verdict on an unrelated diff
  _ ← assertEq "registered surface remedies the qty retype"
    (verdictOf changes registeredMigrations) .remedied
  _ ← assertEq "registered surface: clean diff stays clean"
    (verdictOf (diff v1 v3) registeredMigrations) .clean
  _ ← assert (registeredMigrations.any fun mig =>
      mig.item == "OrderItem"
      && mig.fields.any fun fm => fm.field == "qty" && fm.oldTy == .u32
        && fm.newTy == .u64)
    "registered surface: qty row present"
  .ok ()

/-! ## SchemaLang.Validate — the schema-INDEXED validator lane -/

/-- The user schema, as the validator tests see it (abbrev — the
    reducibility rule; mirror of GuestImpl.userSchema's first three
    fields). -/
abbrev valUserFields : List Field :=
  [ ⟨"id", .u64⟩, ⟨"name", .string⟩, ⟨"email", .string⟩ ]

/-- A row with the id filled and the strings dummy (the validator only
    reads the scalar — the strings ride along unopened). -/
def valRowId (n : UInt64) : RowVals valUserFields :=
  .cons (.u64 n) (.cons (.string "n") (.cons (.string "e") .nil))

def valPositive : VExpr valUserFields .bool := .gt (.colOf "id") (.lit 0)
def valEq : VExpr valUserFields .bool := .eq (.colOf "id") (.lit 7)
def valAnd : VExpr valUserFields .bool := .and valPositive valEq

/-- The boxed evaluator's Bool projection (the SPEC reading). -/
def evalVBool (e : VExpr s .bool) (row : RowVals s) : Bool :=
  match evalV e row with
  | .bool b => b
  | _ => false

def validateChecks : CheckResult := do
  -- the driving example: `id > 0` — the duel's VALID/INVALID rows
  _ ← assertEq "valid row (id=5) passes" (validates valPositive (valRowId 5)) true
  _ ← assertEq "invalid row (id=0) REFUSED" (validates valPositive (valRowId 0)) false
  -- == and &&
  _ ← assertEq "eq matches (id=7)" (validates valEq (valRowId 7)) true
  _ ← assertEq "eq misses (id=5)" (validates valEq (valRowId 5)) false
  _ ← assertEq "and both (id=7)" (validates valAnd (valRowId 7)) true
  _ ← assertEq "and half (id=5)" (validates valAnd (valRowId 5)) false
  -- the readings TIE: boxed evalV ≡ raw evalB on every row (the
  -- compiled path is not a different semantics)
  for n in [0, 1, 5, 7, 42] do
    let row := valRowId n.toUInt64
    _ ← assertEq s!"spec≡compiled id={n}" (evalVBool valPositive row)
      (validates valPositive row)
    _ ← assertEq s!"spec≡compiled and id={n}" (evalVBool valAnd row)
      (validates valAnd row)
  -- the field extraction: the path reads the RIGHT slot
  _ ← assertEq "u64 operand via evalU" (evalU (.colOf "id") (valRowId 42)) 42
  _ ← assertEq "literal via evalU" (evalU (.lit 7) (valRowId 0)) 7
  -- the SPEC evaluator's u64 reading agrees with the raw one
  _ ← assertEq "spec u64 ≡ raw u64"
    (match evalV (.colOf "id") (valRowId 42) with
      | .u64 x => x | _ => 0)
    (evalU (.colOf "id") (valRowId 42))
  -- non-vacuity: the check ran on REAL distinct rows
  _ ← assert (validates valPositive (valRowId 0) != validates valPositive (valRowId 1))
    "the verdict distinguishes the rows"
  .ok ()

/-- The name row: the id filled AND the name controllable (the strlen
    node's operand — the boxed `Value .string` carries the Lean
    `String`, so the spec eval reads the length in place). -/
def valRowName (id : UInt64) (nm : String) : RowVals valUserFields :=
  .cons (.u64 id) (.cons (.string nm) (.cons (.string "e") .nil))

/-- The strlen node (SPEC-level — Validate.lean's Phase 2) over the
    name column, and the name-length validator built on it. -/
def valStrlen : VExpr valUserFields .u64 := .strlen (.colOf "name")
def valNameLong : VExpr valUserFields .bool := .gt valStrlen (.lit 3)

def strlenChecks : CheckResult := do
  -- the boxed eval: the length IS the value (chars — the std
  -- `$string_len` byte count agrees on ASCII)
  _ ← assertEq "strlen boxed (abcd → 4)"
    (match evalV valStrlen (valRowName 5 "abcd") with | .u64 n => n | _ => 0) 4
  _ ← assertEq "strlen boxed (empty → 0)"
    (match evalV valStrlen (valRowName 5 "") with | .u64 n => n | _ => 0) 0
  -- the SPEC verdict: name-length > 3 — true on the long name
  _ ← assertEq "spec verdict true (abcd)" (evalVBool valNameLong (valRowName 5 "abcd")) true
  -- the negative: the same validator REFUSES the short name
  _ ← assertEq "spec verdict false (ab)" (evalVBool valNameLong (valRowName 5 "ab")) false
  _ ← assertEq "spec verdict boundary (abc... exactly 3 fails)"
    (evalVBool valNameLong (valRowName 5 "abc")) false
  -- the COMPILED-BOUNDARY pin, FLIPPED (the flip condition the old pin
  -- named arrived): the backend wired the `len@+8` load and evalU's
  -- `.strlen` arm now reads the row's boxed string — the RAW verdict
  -- agrees with the spec verdict (the divergence is closed; the
  -- readings were PROVEN different when the raw level had no strings,
  -- and the proof updated with the lane that wired the load).
  _ ← assertEq "compiled boundary: raw verdict true (abcd)"
    (validates valNameLong (valRowName 5 "abcd")) true
  -- both readings still refuse the short name (the validator itself
  -- is not vacuous on either level)
  _ ← assertEq "raw verdict false (ab)"
    (validates valNameLong (valRowName 5 "ab")) false
  .ok ()

-- The TYPING's negative control: the MISSPELLED field-ref (`"iid"`)
-- must FAIL to elaborate — the `HasCol` instance search is the gate.
-- `#guard_msgs` pins the EXACT failure (the instance goal names the
-- typo — the instance miss, not some unrelated crash); a mismatched
-- message fails this module's BUILD. The positive half (the correct
-- spelling elaborates) is `valPositive`/`valEq`/`valAnd` above — a
-- gate that rejects everything is as vacuous as one that accepts
-- everything.
/-- error: failed to synthesize instance of type class
  HasCol valUserFields "iid" Ty.u64

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
#check (SchemaLang.VExpr.colOf "iid" : SchemaLang.VExpr valUserFields .u64)

-- The strlen node rides the SAME `HasCol` gate: a misspelled operand
-- (`"nane"`) fails at ELABORATION — the second access route is not a
-- second gate to forget.
/-- error: failed to synthesize instance of type class
  HasCol valUserFields "nane" Ty.string

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
info: sorry.strlen : VExpr valUserFields Ty.u64 -/
#guard_msgs in
#check (SchemaLang.VExpr.strlen (SchemaLang.VExpr.colOf "nane") :
  SchemaLang.VExpr valUserFields .u64)

/-! ## The variant family (SchemaLang.Validate's Phase 3) -/

/-- order-error's cases, as the variant-validator tests see them
    (abbrev — the reducibility rule; mirror of
    `GuestImpl.orderErrorCases`). -/
abbrev valOrderErrorCases : List VariantCase :=
  [ ("empty-cart", none)
  , ("invalid-item", some .u64)
  , ("insufficient-funds", some .f64) ]

/-- The rows: the fired tag's POSITION + the payload at it (one row
    per demo case). -/
def valRowEmpty : VRow valOrderErrorCases := .here ()
def valRowInvalid (id : UInt64) : VRow valOrderErrorCases :=
  .there (.here (.u64 id))
def valRowFunds (a : Float) : VRow valOrderErrorCases :=
  .there (.there (.here (.f64 a)))

/-- The spec form of the demo's order-error validator: NOT empty-cart,
    AND NOT (invalid-item with a 0 payload) — the mirror of
    `GuestImpl.orderErrorSpecValid`. -/
def valOrderError : VCase valOrderErrorCases .bool :=
  .and
    (.not (.isCase "empty-cart"))
    (.not
      (.and
        (.isCase "invalid-item")
        (.not (.gt (.payload "invalid-item") (.litU 0)))))

/-- The second evaluator's Bool projection (the `evalVBool` analog). -/
def evalCaseBool (e : VCase cs .bool) (row : VRow cs) : Bool :=
  match evalCase e row with
  | .bool b => b
  | _ => false

def variantChecks : CheckResult := do
  -- EACH CASE (the demo's three — the orderErrorValid semantics):
  _ ← assertEq "empty-cart REFUSED" (validatesCase valOrderError valRowEmpty) false
  _ ← assertEq "invalid-item 0 REFUSED (the absent-item sentinel)"
    (validatesCase valOrderError (valRowInvalid 0)) false
  _ ← assertEq "invalid-item 5 accepted"
    (validatesCase valOrderError (valRowInvalid 5)) true
  _ ← assertEq "insufficient-funds accepted (the f64 payload unread)"
    (validatesCase valOrderError (valRowFunds 100.0)) true
  -- the tag test, per arm:
  _ ← assertEq "isCase fires at its arm"
    (evalCaseBool (.isCase "invalid-item") (valRowInvalid 5)) true
  _ ← assertEq "isCase misses shallower arms"
    (evalCaseBool (.isCase "invalid-item") valRowEmpty) false
  _ ← assertEq "isCase misses deeper arms"
    (evalCaseBool (.isCase "empty-cart") (valRowFunds 100.0)) false
  -- the arm-typed payload access:
  _ ← assertEq "payload reads the fired arm's u64"
    (match evalCase (.payload "invalid-item") (valRowInvalid 5) with
      | .u64 v => v | _ => 0) 5
  _ ← assertEq "payload is arm-typed (the f64 arm)"
    (match evalCase (.payload "insufficient-funds") (valRowFunds 100.0) with
      | .f64 v => v | _ => 0) 100.0
  -- the MISS = the 0-analog (an unfired slot's read is meaningless —
  -- the guarded-usage pattern discards it)
  _ ← assertEq "payload miss = the 0-analog"
    (match evalCase (.payload "invalid-item") valRowEmpty with
      | .u64 v => v | _ => 42) 0
  -- the case-soundness pin, EXECUTED (theorem `evalCase_here_sound`
  -- is the general u64 shape, compile-checked): isCase true ⟹ the
  -- accessor = the row's own payload, never the 0-analog
  _ ← assertEq "case-soundness executed (isCase)"
    (evalCaseBool (.isCase "invalid-item") (valRowInvalid 7)) true
  _ ← assertEq "case-soundness executed (payload = the row's own)"
    (match evalCase (.payload "invalid-item") (valRowInvalid 7) with
      | .u64 v => v | _ => 0) 7
  -- the negative control: a trivially-true expression ACCEPTS the
  -- empty-cart row — the refusals above are real verdicts, not dead
  -- constants (the vacuity-checker discipline)
  _ ← assertEq "harness control: trivially-true accepts empty-cart"
    (validatesCase (.not (.gt (.litU 0) (.litU 0))) valRowEmpty) true
  -- and the SABOTAGED spec form flips the verdict (the suite catches
  -- a wrong validator, not just a right one)
  _ ← assertEq "sabotaged spec form accepts the row orderErrorValid refuses"
    (validatesCase (.not valOrderError) valRowEmpty) true
  .ok ()

-- The VARIANT family's gate: a MISSPELLED CASE NAME fails to
-- elaborate — the `HasCase` instance search is the gate (the case
-- list, not a runtime scan). The positive half is `valOrderError`
-- above — a gate that rejects everything is as vacuous as one that
-- accepts everything.
/-- error: failed to synthesize instance of type class
  HasCase valOrderErrorCases "emtpy-cart"

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
#check (SchemaLang.VCase.isCase "emtpy-cart" :
  SchemaLang.VCase valOrderErrorCases .bool)

-- The NONE-PAYLOAD control: a payload-less case has NO accessor (BY
-- CONSTRUCTION — `CasePath.here` exists only over `some t` heads);
-- the empty-cart read fails at ELABORATION, never at runtime.
/-- error: failed to synthesize instance of type class
  HasPayload valOrderErrorCases "empty-cart" Ty.u64

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
#check (SchemaLang.VCase.payload "empty-cart" :
  SchemaLang.VCase valOrderErrorCases .u64)

/-! ## Invariants (SPEC-core §5): the schema_invariant lane

The happy registrations below run the `schema_invariant` command
against the REFLECTED Demo registry (the elaboration-time gate: a
misspelled column fails the `HasCol` search, an unknown record is a
did-you-mean error). The run_cmd pin checks the registered rows' DATA
and evaluates the STORED term end-to-end; the runtime group pins the
verdicts on demo rows and the emitter's discipline; the golden
group byte-ties the emitted Rust.
-/

/-- The User schema, as the invariant lane sees it (the registered
    record's fields — abbrev, the reducibility rule). -/
abbrev invUserFields : List Field :=
  [ ⟨"id", .u64⟩, ⟨"name", .string⟩, ⟨"email", .string⟩
  , ⟨"tags", .list .string⟩ ]

/-- A User row: id + name controllable, the rest default (the
    valRowName style — one Value per field, in schema order). -/
def invRow (id : UInt64) (nm : String) : RowVals invUserFields :=
  .cons (.u64 id) (.cons (.string nm)
    (.cons (.string "e") (.cons (.list .nil) .nil)))

/-- Rows the end-to-end pin evaluates (constants, so the run_cmd can
    name them). -/
def invRowHappy : RowVals invUserFields := invRow 5 "abcd"
def invRowZero : RowVals invUserFields := invRow 0 "abcd"

-- The happy registrations MOVED to Demo.lean (spec data lives in the
-- spec module — the emitters replay the registry). The pins below read
-- the Demo-registered rows ("id-positive", "name-min-length").

-- The registration pins: row data + tier computation + the stored
-- term's end-to-end verdicts.
open Lean Elab Command in
run_cmd do
  let items := SchemaLang.Meta.registeredInvariants (← getEnv)
  let fetch (n : String) : CommandElabM SchemaLang.InvariantItem :=
    match items.find? (·.name == n) with
    | some it => pure it
    | none => throwError s!"invariant `{n}` not registered"
  let pos ← fetch "id-positive"
  unless pos.schemaRef == "User" do throwError "id-positive: wrong schemaRef"
  unless pos.tier == (SchemaLang.tierOf none : SchemaLang.Tier) do
    throwError "id-positive: tier not computed (boundaryCheck)"
  unless pos.inv.fields.length == 4 do
    throwError "id-positive: fields are not the User schema"
  let minl ← fetch "name-min-length"
  unless minl.tier == (SchemaLang.tierOf (some `userNameLenProved) : SchemaLang.Tier) do
    throwError "name-min-length: proved tier not computed"
  unless minl.proofName == (some `userNameLenProved) do
    throwError "name-min-length: citation not stored"
  -- the stored term IS the predicate (head = the .gt ctor), and its
  -- registered value executes END-TO-END: printed back to syntax,
  -- re-elaborated against the registered fields, composed with
  -- `validates`, evaluated on the demo rows (happy passes, zero refuses)
  unless pos.exprTerm.getAppFn.isConstOf `SchemaLang.VExpr.gt do
    throwError "id-positive: the stored term is not the predicate"
  let verdict (it : SchemaLang.InvariantItem) (row : Name) : CommandElabM Bool :=
    liftTermElabM do
      let fsList ← SchemaLang.Meta.fieldsToExpr it.inv.fields
      let expected := mkApp2 (mkConst `SchemaLang.VExpr) fsList
        (mkConst `SchemaLang.Ty.bool)
      let stx ← Lean.Elab.Term.exprToSyntax it.exprTerm
      let term ← Lean.Elab.Term.elabTerm stx (some expected)
      Term.synthesizeSyntheticMVarsNoPostponing
      let e := Lean.mkApp3 (Lean.mkConst `SchemaLang.validates) fsList term
        (Lean.mkConst row)
      Lean.Meta.evalExpr Bool (Lean.mkConst `Bool) e
  let happyVerdict ← verdict pos `invRowHappy
  unless happyVerdict do
    throwError "id-positive: the happy row must pass"
  let zeroVerdict ← verdict pos `invRowZero
  unless !zeroVerdict do
    throwError "id-positive: the zero row must FAIL"

-- The NEGATIVE controls (the command's gates): a misspelled column
-- fails the term's `HasCol` instance search, and an unknown record is
-- a did-you-mean error. Both fail THIS module's build if they stop
-- failing (the gate's non-vacuity).
/-- error: failed to synthesize instance of type class
  HasCol
    [{ name := "id", ty := Ty.u64 }, { name := "name", ty := Ty.string }, { name := "email", ty := Ty.string },
      { name := "tags", ty := Ty.string.list }]
    "iid" Ty.u64

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors -/
#guard_msgs in
schema_invariant invTypo for User := VExpr.gt (VExpr.colOf "iid") (VExpr.lit 0)

/-- error: schema_invariant `invBogus`: `Usr` is not a registered record — did you mean: User? -/
#guard_msgs in
schema_invariant invBogus for Usr := VExpr.gt (VExpr.colOf "id") (VExpr.lit 0)

/-- The hand mirrors of the registered predicates (the runtime verdict
    pins evaluate THESE — the same terms the command elaborated). -/
def invIdPositiveMirror : VExpr invUserFields .bool := .gt (.colOf "id") (.lit 0)
def invNameMinLengthMirror : VExpr invUserFields .bool :=
  .gt (.strlen (.colOf "name")) (.lit 3)

def invariantChecks (invs : List SchemaLang.InvariantItem) : CheckResult := do
  -- the tier computation (the enforcement ladder's v1 rungs)
  _ ← assertEq "tierOf none = boundaryCheck" (SchemaLang.tierOf none) .boundaryCheck
  _ ← assertEq "tierOf some = proved" (SchemaLang.tierOf (some `t)) .proved
  _ ← assertEq "tier render" (SchemaLang.Tier.render .boundaryCheck) "boundary-check"
  -- the happy registration's verdicts, on demo rows (the hand mirrors)
  _ ← assertEq "inv-id-positive: happy row passes"
    (validates invIdPositiveMirror (invRow 5 "abcd")) true
  _ ← assertEq "inv-id-positive: zero row REFUSED"
    (validates invIdPositiveMirror (invRow 0 "abcd")) false
  _ ← assertEq "inv-name-min-length: long name passes"
    (validates invNameMinLengthMirror (invRow 5 "abcd")) true
  _ ← assertEq "inv-name-min-length: short name REFUSED"
    (validates invNameMinLengthMirror (invRow 5 "ab")) false
  -- non-vacuity: the verdicts distinguish the rows
  _ ← assert (validates invIdPositiveMirror (invRow 0 "") !=
      validates invIdPositiveMirror (invRow 1 ""))
    "the verdict distinguishes the rows"
  -- the emitter: declared path + determinism (the emitter discipline);
  -- the lane runs over the EXT-REPLAYED rows (the v2 contract — the
  -- committed mirror is gone)
  let files := SchemaLang.Emit.Invariant.invariantEmitter.run
    { items := [], invariants := invs, updates := [] }
  _ ← assertEq "invariant path" (files.head?.map (·.path))
    (some "../../src/invariants_generated.rs")
  _ ← assertEq "invariant deterministic" (files.map (·.contents))
    ((SchemaLang.Emit.Invariant.invariantEmitter.run
        { items := [], invariants := invs, updates := [] }).map (·.contents))
  let out := files.head?.map (·.contents) |>.getD ""
  _ ← assert (out.contains "pub fn check_id_positive(v: &User) -> bool")
    "check fn emitted (snake — Rust identifiers cannot carry kebab)"
  _ ← assert (out.contains "pub fn validate_user(v: &User) -> bool")
    "the record's folding validator emitted"
  _ ← assert (out.contains "(v.id > 0u64)") "the evalB discipline: raw u64 ops"
  _ ← assert (out.contains ".len() as u64") "strlen = .len() on strings"
  _ ← assert (out.contains "#[cfg(test)]") "the test module emitted"
  -- the Lean-computed default-row verdicts, replayed as Rust asserts:
  -- a FAILING row must fail (id=0 and the empty name both refuse)
  _ ← assertEq "default-row verdicts (both refuse)"
    (invs.map SchemaLang.Emit.Invariant.defaultVerdict)
    [some false, some false]
  _ ← assert (out.contains "assert_eq!(check_id_positive(&v), false);")
    "the failing row's assert is pinned"
  -- the emitter self-audit (the banned-construct sweep)
  _ ← assert
    (files.all fun f =>
      GateKit.auditFindings SchemaLang.Emit.emitterAuditRules f.contents |>.isEmpty)
    "invariant emitter self-audit (banned constructs)"
  .ok ()

/-- The golden byte-tie for the invariant lane (the same contract as
    `goldenChecks` — which covers this emitter automatically once it
    joins the registry; this pin stands independent of the wiring). -/
unsafe def invariantGoldenChecks (update : Bool) : IO (String × CheckResult) := do
  let ctx ← loadDemoCtx
  let files := SchemaLang.Emit.Invariant.invariantEmitter.run ctx
  let out := files.head?.map (·.contents) |>.getD ""
  let golden : System.FilePath := "goldens/invariants/invariants_generated.rs"
  CodegenCore.Emit.createParentDirs golden
  let r ← TestKit.Golden.checkAgainstGolden "invariant" out golden update
  pure ("invariantGolden", r)

/-! ## Proved-tier citation resolution (the cert pattern, made real)

`Tier.proved` stores a `proofName : Option Name`; the registration
command leaves it UNRESOLVED ("CI's job later"). This IS that job:
`citationDiag?` walks the registered invariants, `Environment.find?`
resolves every cited name, and the resolved decl must be a theorem or
def whose axiom footprint (Lean's `collectAxioms`) contains no
`sorryAx` — an axiom-cited (or sorry-cited) invariant fails. The check
runs at build time (run_cmd): an unresolvable citation fails THIS
module's build.
-/

/-- The theorem the proved-tier invariant `invNameMinLength` cites —
    previously a dangling name ("resolution is CI's job later"), now a
    resolvable, kernel-checked decl: the executable mirror's verdict on
    the long name, proved. -/
theorem userNameLenProved :
    validates invNameMinLengthMirror (invRow 5 "abcd") = true := by
  unfold validates invNameMinLengthMirror invRow
  simp only [evalB, evalU, VExpr.colOf, hasColHead, ColPath.get,
    _root_.string_len]
  rfl

/-- Resolve ONE proved-tier citation. `none` = resolved clean; `some`
    = the diagnostic (unresolvable, not a theorem/def, or `sorryAx`-
    tainted). `collectAxioms` is Lean's own axiom-checking. -/
def citationDiag? (env : Lean.Environment)
    (it : SchemaLang.InvariantItem) : Lean.Elab.Command.CommandElabM (Option String) := do
  match it.proofName with
  | none => pure none
  | some pn =>
    match env.find? pn with
    | none =>
        pure (some s!"invariant `{it.name}`: cited proof `{pn}` does not resolve")
    | some (.thmInfo _) | some (.defnInfo _) =>
        let axs ← Lean.collectAxioms pn
        if axs.contains `sorryAx then
          pure (some s!"invariant `{it.name}`: cited proof `{pn}` depends on `sorryAx`")
        else
          pure none
    | some _ =>
        pure (some s!"invariant `{it.name}`: cited proof `{pn}` is not a theorem or def — an axiom citation is rejected")

-- The citation-resolution gate: every registered proved-tier
-- invariant resolves clean, and the resolver CATCHES a bogus name and
-- an axiom citation (the negative controls — a resolver that accepts
-- everything is vacuous). (No doc comment here: run_cmd's parser does
-- not take one after `open … in`.)
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let provedRows := (SchemaLang.Meta.registeredInvariants env).filter
    (fun it => it.proofName.isSome)
  unless provedRows.any (·.name == "name-min-length") do
    throwError "citation check: no proved-tier invariant registered"
  for it in provedRows do
    match ← citationDiag? env it with
    | some d => throwError d
    | none => pure ()
  -- negative control 1: a bogus name does not resolve
  let bogus : SchemaLang.InvariantItem :=
    { name := "negctl-bogus", schemaRef := "User", tier := .proved
    , proofName := some `noSuchTheoremAnywhere, inv := default }
  match ← citationDiag? env bogus with
  | some _ => pure ()
  | none => throwError "citation check: bogus name NOT caught — the resolver is vacuous"
  -- negative control 2: an AXIOM citation is rejected (kind gate)
  let axiomCtl : SchemaLang.InvariantItem :=
    { name := "negctl-axiom", schemaRef := "User", tier := .proved
    , proofName := some `propext, inv := default }
  match ← citationDiag? env axiomCtl with
  | some _ => pure ()
  | none => throwError "citation check: axiom citation NOT caught — the resolver is vacuous"

/-! ## Docs emitter (DOCS-SITE lane): the markdown API page -/

def docsChecks : CheckResult := do
  let md := SchemaLang.Docs.docsOf demoItems
  -- structure: one section per item kind, in registration order
  _ ← assert (md.contains "# demo:gateway — API reference") "title"
  _ ← assert (md.contains "## Records") "records heading"
  _ ← assert (md.contains "## Variants") "variants heading"
  _ ← assert (md.contains "## Functions") "functions heading"
  _ ← assert (md.contains "## Resources") "resources heading"
  -- records: GFM field table, tyWit-rendered types
  _ ← assert (md.contains "### `user`") "record heading"
  _ ← assert (md.contains "| `id` | `u64` |") "scalar field row"
  _ ← assert (md.contains "| `tags` | `list<string>` |") "list field row"
  -- variants: payload-less case renders an em dash, payload case the ty
  _ ← assert (md.contains "### `order-error`") "variant heading"
  _ ← assert (md.contains "| `empty-cart` | — |") "payload-less case row"
  _ ← assert (md.contains "| `invalid-item` | `u64` |") "payload case row"
  -- funcs: the WIT signature (ONE lowering — funcDecl, async included)
  -- + the semantic contract fields as data
  _ ← assert (md.contains "### `get-user`") "func heading"
  _ ← assert (md.contains "get-user: func(id: u64) -> option<user>") "signature block"
  _ ← assert (md.contains "null: `propagate`") "nullSem pin"
  _ ← assert (md.contains "determinism: `pure`") "determinism pin"
  _ ← assert (md.contains "delivery: `once`") "delivery pin"
  _ ← assert (md.contains "### `watch-orders`") "async func heading"
  _ ← assert (md.contains "watch-orders: async func(into: order-error) -> list<user>")
    "async signature block"
  -- resources
  _ ← assert (md.contains "### `db`") "resource heading"
  -- determinism (the emitter discipline, asserted not stated)
  _ ← assertEq "docs deterministic" md (SchemaLang.Docs.docsOf demoItems)
  -- the emitter: declared path + registered in the registry (the golden
  -- loop runs it automatically; these pins stand independent of the golden)
  let files := SchemaLang.Docs.docsEmitter.run (SchemaLang.Emit.GenCtx.itemsOnly demoItems)
  _ ← assertEq "docs path" (files.head?.map (·.path)) (some "../../docs/api.md")
  _ ← assert (SchemaLang.Emit.emitters.any fun e => e.name == "docs")
    "docs emitter registered"
  .ok ()

/-! ## Updates (SPEC-core §3, demoted): the schema_update lane

The happy registrations MOVED to Demo.lean (spec data lives in the
spec module — the emitters replay the registry; this file keeps the
negative controls + the `updPureCall` determinism probe). The `where`
clause is REQUIRED — `VExpr .bool` has no literal-true; the
unconditional idiom is `VExpr.eq (VExpr.lit 0) (VExpr.lit 0)` (pinned
by `updSelfBumpMirror`). The run_cmd pin checks the Demo-registered
rows' DERIVED data (reads/writes/selfReading — never hand-listed) AND
the emitter's rows (which now READ the registry — the v2 contract); the
runtime group pins `applyRow` semantics on demo rows; the golden group
byte-ties the emitted Rust.
-/

/-- The User schema, as the update lane sees it (abbrev — the
    reducibility rule; the same list the invariant lane mirrors). -/
abbrev updUserFields : List Field :=
  [ ⟨"id", .u64⟩, ⟨"name", .string⟩, ⟨"email", .string⟩
  , ⟨"tags", .list .string⟩ ]

-- The row builder is the invariant lane's `invRow` REUSED (same schema
-- shape — the dupDefBodies lint enforces the dedup); the extractors are
-- the update lane's own (the evalU / boxed-eval routes — no hand path).

/-- The row's id (the `evalU` route — no hand path). -/
def updRowId (row : RowVals updUserFields) : UInt64 :=
  evalU (.colOf "id") row

/-- The row's email (the boxed eval — no hand path). -/
def updRowEmail (row : RowVals updUserFields) : String :=
  match evalV (.colOf "email") row with | .string s => s | _ => ""

-- The registration pins: row data + the DERIVED reads/writes/
-- selfReading (EXACT lists) + the emitter's rows (registry-read).
open Lean Elab Command in
run_cmd do
  let ups := SchemaLang.Meta.registeredUpdates (← getEnv)
  unless ups.length == 3 do
    throwError s!"expected 3 registered updates, got {ups.length}"
  let fetch (n : String) : CommandElabM SchemaLang.SomeUpdate :=
    match ups.find? (·.update.name == n) with
    | some u => pure u
    | none => throwError s!"update `{n}` not registered"
  let rid ← fetch "reset_id"
  unless rid.update.reads == ["id"] do
    throwError s!"updResetId: reads not derived (got {rid.update.reads})"
  unless rid.update.writes == ["id"] do throwError "updResetId: wrong writes"
  unless rid.update.selfReading == false do
    throwError "updResetId: misclassified as self-reading"
  let echo ← fetch "echo_email"
  unless echo.update.reads == ["name"] do
    throwError s!"updEchoEmail: reads not derived (got {echo.update.reads})"
  unless echo.update.writes == ["email"] do throwError "updEchoEmail: wrong writes"
  unless echo.update.selfReading == false do
    throwError "updEchoEmail: misclassified as self-reading"
  let sb ← fetch "self_bump"
  unless sb.update.reads == ["id"] do
    throwError s!"updSelfBump: reads not derived (got {sb.update.reads})"
  unless sb.update.selfReading == true do
    throwError "updSelfBump: the self-reading classification missed"
  -- the emitter's rows ARE the registry now (the v2 contract — the
  -- two sides converged; the committed mirror is gone). The remaining
  -- content: the recName re-derivation (`recNameOf?`'s shape match)
  -- resolves every row's record ref.
  let em := SchemaLang.Emit.Update.ctxRows
    { items := (SchemaLang.Meta.registeredItems (← getEnv)).map (·.2)
    , invariants := [], updates := ups }
  unless (em.map (fun u => u.u.update.name)) == (ups.map (·.update.name)) do
    throwError "Emit.Update.ctxRows: names out of sync with the registry"
  unless (em.map (·.recName)) == ["User", "User", "User"] do
    throwError "Emit.Update.ctxRows: record refs out of sync"

-- The NEGATIVE controls (the command's gates): a value expr of the
-- WRONG TYPE for the column fails the GADT-index gate (a u64 literal
-- on the string `name` column); a misspelled column is the did-you-mean
-- error from the command's own field lookup. Both fail THIS module's
-- build if they stop failing (the gate's non-vacuity).
/-- error: schema_update `updWrongType`: the value expression has type SchemaLang.Ty.u64 — the written column `name` is SchemaLang.Ty.string — the value expression must have the COLUMN'S OWN TYPE (the GADT gate) -/
#guard_msgs in
schema_update updWrongType for User name := VExpr.lit 0
  where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

/-- error: schema_update `updTypo`: `iid` is not a column of `User` — did you mean: id? -/
#guard_msgs in
schema_update updTypo for User iid := VExpr.lit 0
  where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

/-! ### The determinism gate: `volatileInPureContext` FIRES

The update lane is the FIRST pure-context consumer of the armed diag:
the value/guard VExpr terms may reference REGISTERED `@[schema_fn]`
constants (the lit operand is a Lean `UInt64` computation), and a
`volatile` fn referenced there fails elaboration (only `pure` may
fuse/reorder). The negative controls below fail THIS module's build if
they stop failing; the positives register through the SAME gates (the
registrations land after the emitter-sync run_cmd above, which pins the
first three rows). The schema fns live HERE (Demo.lean is untouched —
Tests imports the Meta machinery and applies the attributes directly).
-/

/-- The volatile probe: a clock-reading fn (the volatilities probe
    above register its SIGNATURE; this one is REFERENCED from an
    update's value term — the diag's firing condition). -/
@[schema_fn volatile]
def updClockFn (seed : UInt64) : UInt64 := seed + 17

/-- The pure probe: same shape, default determinism — registers clean
    and is REFERENCED from an update's value term. -/
@[schema_fn]
def updPureFn (x : UInt64) : UInt64 := x * 2

-- POSITIVE: a `pure` schema fn in the value term registers (the gate
-- fires on `volatile` only).
schema_update updPureCall for User id := VExpr.lit (updPureFn 3)
  where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

-- NEGATIVE: a `volatile` fn in the VALUE term — the armed diag fires,
-- naming the fn (`updClockFn`) and the update.
/-- error: schema_update `updVolatileValue`: func `updClockFn` is volatile but `schema_update updVolatileValue` requires purity — valid determinisms in a pure context: pure, stable -/
#guard_msgs in
schema_update updVolatileValue for User id := VExpr.lit (updClockFn 5)
  where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

-- NEGATIVE: a `volatile` fn in the GUARD term — same gate, same diag.
/-- error: schema_update `updVolatileGuard`: func `updClockFn` is volatile but `schema_update updVolatileGuard` requires purity — valid determinisms in a pure context: pure, stable -/
#guard_msgs in
schema_update updVolatileGuard for User id := VExpr.lit 0
  where VExpr.gt (VExpr.lit (updClockFn 1)) (VExpr.lit 0)

-- The determinism-gate pins: the pure-fn update registered (4 rows
-- now — after the emitter-sync pin), the volatile updates did NOT.
open Lean Elab Command in
run_cmd do
  let ups := SchemaLang.Meta.registeredUpdates (← getEnv)
  unless ups.length == 4 do
    throwError s!"expected 4 registered updates (3 sync-pinned + updPureCall), got {ups.length}"
  unless ups.any (·.update.name == "updPureCall") do
    throwError "updPureCall: the pure-fn update did not register"
  if ups.any (·.update.name == "updVolatileValue") then
    throwError "updVolatileValue: the volatile update REGISTERED — the gate did not fire"
  if ups.any (·.update.name == "updVolatileGuard") then
    throwError "updVolatileGuard: the volatile update REGISTERED — the gate did not fire"

/-! ### The composable law classes: `UpdatePure` / `NonInterfering`

The second layer: the registration's scan emits an `UpdatePure`
INSTANCE per registered update (its proof is `rfl` against the STORED
`volatileRefs` — the scan's decided fact), and the consumers
(`UpdateItem.cascade2`) take legality as instance binders — a composite
assembled from a volatile or interfering part is UNCONSTRUCTIBLE.
Pins here: the emitted instances' presence, ONE composite construction
(positive), the class-level negative (no instance can exist for a
dirty update), and the composite's order-freedom law.
-/

-- the registration-emitted instances: Demo's three + the pure-fn probe
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in ["reset_id", "echo_email", "self_bump", "updPureCall"] do
    let base := ((`SchemaLang).str "instUpdatePure").str n
    unless env.contains base do
      throwError s!"instUpdatePure_{n}: the registration-emitted "
        ++ "UpdatePure instance is missing"

#check @UpdatePure
#check @NonInterfering

-- THE CLASS-LEVEL NEGATIVE: a hand-built update whose STORED
-- volatile-ref set is nonempty (the shape the scan would have stored
-- had the gate not failed it) admits NO `UpdatePure` instance — any
-- one would contradict the data. The registration never produces this
-- shape (the scan fires first); this pins the lock's non-vacuity.
def updDirty : UpdateItem updUserFields ⟨"id", .u64⟩ :=
  { name := "dirty", guard := .eq (.lit 0) (.lit 0), value := .lit 0
  , writePath := .here, volatileRefs := ["clock"] }

example : ¬ UpdatePure updUserFields ⟨"id", .u64⟩ updDirty := by
  intro h
  have hf := h.volatileFree
  simp [updDirty] at hf

-- THE COMPOSITE CONSTRUCTION (the positive): two pure, non-interfering
-- updates over the User schema. The `UpdatePure` instances are `⟨rfl⟩`
-- against the stored (default-empty) data; `NonInterfering` is decided
-- over the DERIVED reads/writes (the folds — no hand lists).
def updCompA : UpdateItem updUserFields ⟨"id", .u64⟩ :=
  { name := "comp-a", guard := .eq (.lit 0) (.lit 0), value := .lit 0
  , writePath := .here }

def updCompB : UpdateItem updUserFields ⟨"email", .string⟩ :=
  { name := "comp-b", guard := .eq (.lit 0) (.lit 0), value := .colOf "name"
  , writePath := .there (.there .here) }

instance : UpdatePure updUserFields ⟨"id", .u64⟩ updCompA := ⟨rfl⟩
instance : UpdatePure updUserFields ⟨"email", .string⟩ updCompB := ⟨rfl⟩

instance : NonInterfering updUserFields ⟨"id", .u64⟩ ⟨"email", .string⟩
    updCompA updCompB := ⟨by
  simp only [UpdateItem.reads, VExpr.reads, UpdateItem.writes, updCompA, updCompB]
  decide⟩

-- the legal composite CONSTRUCTS (the instances assemble the legality)
def compCascade : List (RowVals updUserFields) → List (RowVals updUserFields) :=
  UpdateItem.cascade2 updCompA updCompB

-- the composite's runtime pin: comp-a resets the id, comp-b copies
-- name → email (both guards unconditional)
example :
    (compCascade [invRow 150 "abcd"]).map updRowId = [0] := by
  simp [compCascade, UpdateItem.cascade2, UpdateItem.applyRow, validates,
    evalB, evalU, evalV, updRowId, invRow, updCompA, updCompB, boolToU64]
  rfl

-- THE LAW: the legal composite is order-free — `cascade_two_commute`
-- recovered STRUCTURALLY (the swap needs only the `symm` instance; the
-- four non-interference hypotheses come from the class field alone).
-- Stated HERE: `cascade_two_commute` lives in `TickCascade`, which
-- imports Update — the theorem cannot sit next to `cascade2` without
-- an import cycle (Update.lean's doc note).
theorem cascade2_commutes {fs : List Field} {f₁ f₂ : Field}
    (u₁ : UpdateItem fs f₁) (u₂ : UpdateItem fs f₂)
    [_hP₁ : UpdatePure fs f₁ u₁] [_hP₂ : UpdatePure fs f₂ u₂]
    [hNI : NonInterfering fs f₁ f₂ u₁ u₂]
    (rows : List (RowVals fs)) :
    UpdateItem.cascade2 u₁ u₂ rows = UpdateItem.cascade2 u₂ u₁ rows := by
  show (rows.map u₂.applyRow).map u₁.applyRow
     = (rows.map u₁.applyRow).map u₂.applyRow
  obtain ⟨hg₁, hv₁, hg₂, hv₂, hne⟩ := hNI.cascadeHyps
  exact cascade_two_commute u₁ u₂ hg₁ hv₁ hg₂ hv₂ hne rows

example :
    UpdateItem.cascade2 updCompB updCompA [invRow 150 "abcd"]
      = UpdateItem.cascade2 updCompA updCompB [invRow 150 "abcd"] :=
  cascade2_commutes updCompB updCompA [invRow 150 "abcd"]

/-- The hand mirrors of the registered updates (the runtime pins
    evaluate THESE — the same data the command registered; the run_cmd
    above pins the mirror). -/
def updResetIdMirror : UpdateItem updUserFields ⟨"id", .u64⟩ :=
  { name := "reset-id", guard := .gt (.colOf "id") (.lit 100)
  , value := .lit 0, writePath := .here }

def updEchoEmailMirror : UpdateItem updUserFields ⟨"email", .string⟩ :=
  { name := "echo-email", guard := .gt (.strlen (.colOf "name")) (.lit 3)
  , value := .colOf "name", writePath := .there (.there .here) }

def updSelfBumpMirror : UpdateItem updUserFields ⟨"id", .u64⟩ :=
  { name := "self-bump", guard := .eq (.lit 0) (.lit 0)
  , value := .colOf "id", writePath := .here }

def updateChecks (ctx : SchemaLang.Emit.GenCtx) : CheckResult := do
  let ups := ctx.updates
  -- the DERIVED read/write sets + the linearity classification
  _ ← assertEq "reset-id: reads derived" updResetIdMirror.reads ["id"]
  _ ← assertEq "reset-id: writes derived" updResetIdMirror.writes ["id"]
  _ ← assertEq "reset-id: linear" updResetIdMirror.selfReading false
  _ ← assertEq "echo-email: reads derived" updEchoEmailMirror.reads ["name"]
  _ ← assertEq "echo-email: writes derived" updEchoEmailMirror.writes ["email"]
  _ ← assertEq "echo-email: linear" updEchoEmailMirror.selfReading false
  _ ← assertEq "self-bump: reads derived" updSelfBumpMirror.reads ["id"]
  _ ← assertEq "self-bump: SELF-READING" updSelfBumpMirror.selfReading true
  -- applyRow semantics on demo rows: a GUARDED row changes
  _ ← assertEq "reset-id: guarded row (id=150) resets"
    (updRowId (updResetIdMirror.applyRow (invRow 150 "abcd"))) 0
  -- ... a REFUSED row passes through untouched
  _ ← assertEq "reset-id: refused row (id=50) unchanged"
    (updRowId (updResetIdMirror.applyRow (invRow 50 "abcd"))) 50
  -- the GUARD reads the ORIGINAL row: on [150, 50], the 150-row's guard
  -- saw 150 (> 100) BEFORE the write → [0, 50]. A guard re-read after
  -- the write would see 0 ≤ 100 and leave [150, 50].
  _ ← assertEq "reset-id: guard reads the original row (batch)"
    ((updResetIdMirror.apply [invRow 150 "a", invRow 50 "b"]).map updRowId)
    [0, 50]
  -- the VALUE reads the ORIGINAL row too: self-bump writes the id it
  -- read pre-write (7 → 7); a post-write read would differ once the
  -- write landed first
  _ ← assertEq "self-bump: value reads the original row"
    (updRowId (updSelfBumpMirror.applyRow (invRow 7 "x"))) 7
  -- the string write: the guarded row's email BECOMES the row's name
  _ ← assertEq "echo-email: guarded row copies name into email"
    (updRowEmail (updEchoEmailMirror.applyRow (invRow 5 "abcd"))) "abcd"
  _ ← assertEq "echo-email: refused row keeps its email"
    (updRowEmail (updEchoEmailMirror.applyRow (invRow 5 "ab"))) "e"
  -- the SomeUpdate cast discipline: a row whose field list MATCHES the
  -- registered fields executes; a foreign row refuses (passes through)
  let su : SomeUpdate :=
    { fields := updUserFields, field := ⟨"id", .u64⟩, update := updResetIdMirror }
  _ ← assertEq "SomeUpdate.applyRow: matching row executes"
    (updRowId (su.applyRow (invRow 150 "abcd"))) 0
  _ ← assert
    (match su.applyRow RowVals.nil with | .nil => true)
    "SomeUpdate.applyRow: foreign row passes through"
  -- the emitter: declared path + determinism (the emitter discipline);
  -- the lane runs over the EXT-REPLAYED rows (the v2 contract)
  let files := SchemaLang.Emit.Update.updateEmitter.run ctx
  _ ← assertEq "update path" (files.head?.map (·.path))
    (some "../../src/updates_generated.rs")
  _ ← assertEq "update deterministic" (files.map (·.contents))
    ((SchemaLang.Emit.Update.updateEmitter.run ctx).map (·.contents))
  let out := files.head?.map (·.contents) |>.getD ""
  _ ← assert (out.contains "pub fn apply_reset_id(rows: &mut Vec<User>)")
    "apply fn emitted (snake — Rust identifiers cannot carry kebab)"
  _ ← assert (out.contains "r.id = 0u64;") "the constant u64 write lowered"
  _ ← assert (out.contains "r.email = (r.name).clone();")
    "the string write: .col-of-string → .clone()"
  _ ← assert (out.contains "pub fn tick_user(rows: &mut Vec<User>)")
    "the record's folding tick emitted"
  _ ← assert (out.contains "apply_reset_id(rows); apply_echo_email(rows); apply_self_bump(rows);")
    "the tick folds the record's updates in registration order"
  -- the emitter self-audit (the banned-construct sweep)
  _ ← assert
    (files.all fun f =>
      GateKit.auditFindings SchemaLang.Emit.emitterAuditRules f.contents |>.isEmpty)
    "update emitter self-audit (banned constructs)"
  .ok ()

/-- The golden byte-tie for the update lane (the same contract as
    `invariantGoldenChecks` — the Registry wiring will fold this
    emitter into `goldenChecks` automatically; this pin stands
    independent of the wiring). -/
unsafe def updateGoldenChecks (update : Bool) : IO (String × CheckResult) := do
  let ctx ← loadDemoCtx
  let files := SchemaLang.Emit.Update.updateEmitter.run ctx
  let out := files.head?.map (·.contents) |>.getD ""
  let golden : System.FilePath := "goldens/update/updates_generated.rs"
  CodegenCore.Emit.createParentDirs golden
  let r ← TestKit.Golden.checkAgainstGolden "update" out golden update
  pure ("updateGolden", r)

/-! ## Trace (SPEC-core §11): the scenario/trace spec item -/

/-- The scenario's batches ride the registered demo updates' SHAPE —
    the SAME `UpdateItem`s the update lane registered (the mirrors),
    wrapped as `SomeUpdate` rows over the User fields. -/
def trResetId : SomeUpdate :=
  { fields := updUserFields, field := ⟨"id", .u64⟩
  , update := updResetIdMirror }
def trEchoEmail : SomeUpdate :=
  { fields := updUserFields, field := ⟨"email", .string⟩
  , update := updEchoEmailMirror }
def trSelfBump : SomeUpdate :=
  { fields := updUserFields, field := ⟨"id", .u64⟩
  , update := updSelfBumpMirror }

/-- The scenario: User, 2 rows, 3 ticks (reset-id → echo-email →
    self-bump). Rows reuse the update lane's `invRow` (id, name, "e",
    []). -/
def trScenario : Scenario :=
  { fields := updUserFields
  , init := [invRow 1 "a", invRow 200 "bobby"]
  , ticks := [ [trResetId], [trEchoEmail], [trSelfBump] ] }

def traceChecks : CheckResult := do
  let oracle := runScenario trScenario
  -- tick-by-tick pins (Lean's semantics = THE ORACLE):
  -- tick 0 = init
  _ ← assertEq "trace: tick count" oracle.length 4
  _ ← assertEq "tick 0 = init" (oracle[0].map updRowId) [1, 200]
  -- tick 1: reset-id fires ONLY on the guarded row (id > 100)
  _ ← assertEq "tick 1: reset-id resets the 200 row"
    (oracle[1].map updRowId) [1, 0]
  -- tick 2: echo-email copies name into email (strlen(name) > 3)
  _ ← assertEq "tick 2: echo-email copies the name"
    (oracle[2].map updRowEmail) ["e", "bobby"]
  -- tick 3: self-bump reads the ORIGINAL id — a no-op on the value
  _ ← assertEq "tick 3: self-bump keeps the ids"
    (oracle[3].map updRowId) [1, 0]
  -- the fold view and the trace agree on the final state
  _ ← assertEq "finalState = last tick (ids)"
    (trScenario.finalState.map updRowId) (oracle.getLast!.map updRowId)
  _ ← assertEq "finalState = last tick (emails)"
    (trScenario.finalState.map updRowEmail)
    (oracle.getLast!.map updRowEmail)
  -- CONFORMANCE (positive): the oracle's own output conforms
  _ ← assertEq "conforms: oracle output"
    (trScenario.conforms oracle.getLast!) true
  -- order-independence: the rows' order is not observable
  _ ← assertEq "conforms: reversed rows"
    (trScenario.conforms oracle.getLast!.reverse) true
  -- NEGATIVE CONTROL: a corrupted final state — "engine accepted what
  -- the spec rejects" is the bug class. The verdict flips AND the
  -- divergence is LOCALIZED: tick 3 + the row mismatch.
  let corrupted : List (RowVals updUserFields) :=
    [invRow 1 "a",
     .cons (.u64 0) (.cons (.string "bobby") (.cons (.string "x")
       (.cons (.list .nil) .nil)))]
  _ ← assertEq "conforms: corrupted final"
    (trScenario.conforms corrupted) false
  match diverge trScenario corrupted with
  | some report =>
      _ ← assert (report.contains "tick 3") "diverge names the final tick"
      _ ← assert (report.contains "expected row")
        "diverge reports the row mismatch"
  | none => throw "diverge: corrupted final reported NO divergence"
  -- the STALL bug class: engine rows stuck at init — named tick 0
  match diverge trScenario trScenario.init with
  | some report =>
      _ ← assert (report.contains "tick 0") "diverge names the stall tick"
      _ ← assert (report.contains "stalled") "diverge names the stall"
  | none => throw "diverge: stalled engine reported NO divergence"
  -- clean run: no divergence
  _ ← assertEq "diverge: clean run" (diverge trScenario oracle.getLast!) none
  -- THE CODEC (the observation half, closed User fields): the trace
  -- round-trips the wire (theorem `decTrace_encTrace_append`, executed)
  let wire := encTrace updUserFields oracle
  match decTrace? updUserFields (wire ++ [9, 9]) with
  | some (trace', rest) =>
      _ ← assertEq "codec: append form" rest [9, 9]
      _ ← assertEq "codec: trace survives the wire"
        (trace'.map (fun rows => rows.map (rowKey updUserFields)))
        (oracle.map (fun rows => rows.map (rowKey updUserFields)))
  | none => throw "codec: the trace did NOT decode"
  -- per-tick codec round trip on the final state
  match decRows? updUserFields (encRows updUserFields trScenario.finalState ++ []) with
  | some (rows, rest) =>
      _ ← assertEq "codec: final-state rows"
        (rows.map (rowKey updUserFields))
        (trScenario.finalState.map (rowKey updUserFields))
      _ ← assertEq "codec: no remainder" rest []
  | none => throw "codec: the final state did NOT decode"
  .ok ()

/-! ## Error goldens: the exact `SchemaDiag` renders (the API docs)

The LLM contract (Part 11): the diagnostic renders ARE the agents'
API documentation — the text is regression-tested. One golden row per
ctor: the rendered string must equal the pinned text EXACTLY (an
assertEq per row — a wording drift, a lost did-you-mean, a dropped
valid-space enumeration all fail the suite). The ctor lists ride
too: ten ctors, ten goldens.
-/

/-- The golden inputs: one representative diag per ctor (the ctor
    names are the golden labels, in ctor-declaration order). -/
def diagGoldenInputs : List SchemaDiag :=
  [ .unknownRef "usr" ["user"] ["user", "org"]
  , .dupName "user"
  , .asyncField "user" "email"
  , .nonBoundaryType "count" "Nat"
  , .notAStructure "X"
  , .noCtor "X"
  , .binderMismatch "X"
  , .multiPayload "X"
  , .reservedWord "type" "field of `user`"
  , .volatileInPureContext "clock" "aggregator" ]

/-- The goldens: ctor → the EXACT rendered text (the API docs). -/
def diagGolden : List (String × String) :=
  [ ("unknownRef", "unknown type `usr` — valid types: user, org — did you mean: user?")
  , ("dupName", "duplicate name `user` — names must be unique")
  , ("asyncField", "field `email` on `user`: future/stream cannot appear in field position (WIT grammar) — move it to a function signature")
  , ("nonBoundaryType", "`count`: `Nat` is not a boundary type — boundary types are: Bool, UInt8..UInt64, Int8..Int64, Float32, Float, String, ByteArray, List, Option, Sum (as result), Async.Future, Async.Stream, or another `@[schema]` declaration")
  , ("notAStructure", "`X` is not a structure — v1 reflects structures only")
  , ("noCtor", "`X`: no constructor found")
  , ("binderMismatch", "`X`: field/binder count mismatch — flat structures without typeclass fields only (v1)")
  , ("multiPayload", "`X`: variant cases carry at most one payload type (v1 — WIT case shape)")
  , ("reservedWord", "`type` is a reserved word in field of `user` — rename it (WIT/Rust would reject the emitted identifier)")
  , ("volatileInPureContext", "func `clock` is volatile but `aggregator` requires purity — valid determinisms in a pure context: pure, stable") ]

def diagGoldenChecks : CheckResult := do
  _ ← assertEq "diagGolden covers every ctor" diagGolden.length 10
  let actual := diagGoldenInputs.map SchemaDiag.render
  for (a, (label, golden)) in actual.zip diagGolden do
    _ ← assertEq s!"diagGolden[{label}]" a golden
  -- the renderList projection renders the SAME text per element
  let two := SchemaDiag.renderList [.dupName "a", .dupName "b"]
  _ ← assert (two.contains "duplicate name `a` — names must be unique;; duplicate name `b` — names must be unique")
    "renderList joins with ;;"
  .ok ()

/-! ## Subschema — the typed-query lane (FP-lean §7.3) -/

/-- The full user record (the validator lane's schema, REUSED — the
    old consumer's view). -/
abbrev subUserOld : List Field :=
  [ ⟨"id", .u64⟩, ⟨"name", .string⟩, ⟨"email", .string⟩ ]

/-- The NEW user record: the old schema plus a nickname (the safe
    change — additions only). -/
abbrev subUserNew : List Field :=
  [ ⟨"id", .u64⟩, ⟨"name", .string⟩, ⟨"email", .string⟩
  , ⟨"nickname", .string⟩ ]

/-- The book's travelDiary-style evidence over OUR schema: the
    id-only and the (id, name) subschema of the full record — BOTH
    built by the book's `by repeat constructor` ergonomics (the
    documented pattern; `by decide` does NOT apply — the family is
    Type-valued data, see the pinned negative controls below). -/
def subId : Subschema [⟨"id", .u64⟩] subUserOld := by repeat constructor
def subIdName : Subschema [⟨"id", .u64⟩, ⟨"name", .string⟩] subUserOld :=
  by repeat constructor

/-- Transitivity, term-level: the chained evidence composes — the
    THREE-rung chain [id] ⊆ [id, name] ⊆ subUserOld (the §7.3
    `trans` shape over concrete schemas). -/
def subStep : Subschema [⟨"id", .u64⟩] [⟨"id", .u64⟩, ⟨"name", .string⟩] :=
  by repeat constructor

def subChain : Subschema [⟨"id", .u64⟩] subUserOld :=
  Subschema.trans subStep subIdName

/-- The safe-change lemma, executed as a term: the old record embeds
    into the nickname-augmented one (`addColumn_sub` generalizes —
    here built by the book's ergonomics). -/
def subFullEmbed : Subschema subUserOld subUserNew := by repeat constructor

/-- concrete-index accessors (the nested-GADT patterns need the
    schema fixed by the SIGNATURE, not by the match) -/
def subHeadU64 : RowVals ({ name := n, ty := .u64 } :: fs) → UInt64
  | .cons (.u64 v) _ => v

def subHead2U64String :
    RowVals ({ name := "id", ty := .u64 } ::
             { name := nm, ty := .string } :: fs) → UInt64 × String
  | .cons (.u64 v) (.cons (.string s) _) => (v, s)

/-- A full OLD-schema row (the valRow shape plus a filled email). -/
def subRowOld (n : UInt64) : RowVals subUserOld :=
  .cons (.u64 n) (.cons (.string "Evan") (.cons (.string "e@x") .nil))

/-- A full NEW-schema row (the nickname field filled). -/
def subRowNew (n : UInt64) : RowVals subUserNew :=
  .cons (.u64 n) (.cons (.string "Evan") (.cons (.string "e@x")
    (.cons (.string "ev") .nil)))

/-- Record fixtures for the migration-tie checks (V1 → V2 adds an
    email; the retype and the shrink are the breaking controls). -/
def subItemV1 : Item := .record "user" [⟨"id", .u64⟩, ⟨"name", .string⟩]
def subItemV2 : Item :=
  .record "user" [⟨"id", .u64⟩, ⟨"name", .string⟩, ⟨"email", .string⟩]
def subItemRetype : Item := .record "user" [⟨"id", .u64⟩, ⟨"name", .u32⟩]
def subItemShrink : Item := .record "user" [⟨"id", .u64⟩]

/-- The composite's showable form (assertEq needs ToString; the
    Vortex types derive Repr, not ToString — one local bridge). -/
instance : ToString (Option (List (Vortex.FieldName × Vortex.DType))) :=
  ⟨reprStr⟩

def subschemaChecks : CheckResult := do
  -- §7.3 demo, executed: the projections read the RIGHT columns —
  -- and CANNOT fail (no failure value exists to return)
  _ ← assertEq "project id-only"
    (subHeadU64 (subRowOld 42 |>.project subId)) 42
  _ ← assertEq "project id,name"
    (subHead2U64String (subRowOld 42 |>.project subIdName))
    (42, "Evan")
  -- trans, executed: the chained evidence projects identically
  _ ← assertEq "trans chain projects the same"
    (subHeadU64 (subRowOld 42 |>.project subChain)) 42
  -- THE MIGRATION RUNNER, executed: the OLD validator (`id > 0`,
  -- valPositive over valUserFields = subUserOld) runs UNCHANGED on
  -- the NEW rows through the projection — the embedding evidence IS
  -- the backward-compat certificate, `RowVals.project` is its runner.
  _ ← assertEq "old validator on new rows (id=42)"
    (validates valPositive (subRowNew 42 |>.project subFullEmbed)) true
  _ ← assertEq "old validator refuses bad new row (id=0)"
    (validates valPositive (subRowNew 0 |>.project subFullEmbed)) false
  -- the constructive migration search, executed: additions construct
  -- the evidence; a retype or a removal is `none` = breaking
  _ ← assert (subschemaOfItem? subItemV1 subItemV2).isSome
    "added field: embedding exists"
  _ ← assert (subschemaViaDiff? subItemV1 subItemV2).isSome
    "diff-gated: all-added → evidence"
  _ ← assert ((subschemaOfItem? subItemV1 subItemRetype).isNone)
    "retyped field: breaking (no embedding)"
  _ ← assert ((subschemaOfItem? subItemV1 subItemShrink).isNone)
    "removed field: breaking (no embedding)"
  -- the diff gate really says all-added on V1→V2 (the gate's verdict,
  -- executed — the gate⟹evidence link is test-pinned, see the header)
  _ ← assert ((fieldDiffsOf subItemV1 subItemV2).all fun
      | .fieldAdded _ => true | _ => false) "diff verdict: additions only"
  -- the Vortex tie: the dtype-level field selection (field-mask shape;
  -- the batch-level read is the Rust executor's)
  let lowered : List (Vortex.FieldName × Vortex.DType) :=
    [ ("id", .primitive .u64 .nonNullable)
    , ("name", .utf8 .nonNullable)
    , ("email", .utf8 .nonNullable) ]
  _ ← assertEq "vortexSelect id-only"
    (subId.vortexSelect lowered)
    (some [("id", .primitive .u64 .nonNullable)])
  _ ← assertEq "vortexSelect drifted list = none"
    (subId.vortexSelect [("only", .null)]) none
  .ok ()

-- THE ERGONOMICS' NEGATIVE CONTROLS (the misspelled-field gate, the
-- same shape the `HasCol` gate gives VExpr): a NOT-subschema has NO
-- evidence — `repeat constructor` runs out of constructors and the
-- residual `ColPath … []` goal fails the build. `by decide` is the
-- WRONG tool by type: the family is Type-valued data, not a Prop.
/-- error: unsolved goals
case a
⊢ ColPath { name := "iid", ty := Ty.u64 }.name { name := "iid", ty := Ty.u64 }.ty []

case a
⊢ Subschema [] subUserOld -/
#guard_msgs in
example : Subschema [⟨"iid", .u64⟩] subUserOld := by repeat constructor

/-- error: unsolved goals
case a
⊢ ColPath { name := "id", ty := Ty.string }.name { name := "id", ty := Ty.string }.ty []

case a
⊢ Subschema [] subUserOld -/
#guard_msgs in
example : Subschema [⟨"id", .string⟩] subUserOld := by repeat constructor

/-- error: Application type mismatch: The argument
  Subschema [{ name := "id", ty := Ty.u64 }] subUserOld
has type
  Type
of sort `Type 1` but is expected to have type
  Prop
of sort `Type` in the application
  @decide (Subschema [{ name := "id", ty := Ty.u64 }] subUserOld) -/
#guard_msgs in
example : Subschema [⟨"id", .u64⟩] subUserOld := by decide

/-! ## The `[inv| …]` DSL — the VExpr surface syntax (the ch. 8 embedding)

The Metaprogramming-in-Lean book's chapter-8 pattern, landed in
SchemaLang.Validate: `declare_syntax_cat vexpr` + the recursive
`elabVExpr` into the VExpr constructors + the `[inv| … ]` term quoter.
This section pins the EMBEDDING: the syntax-elaborated validators eval
EXACTLY as the hand ones (compile = the same VExpr), the precedence
parses the right tree, the misspelled field is the elaboration error
(through the syntax now), and every VExpr pretty-prints BACK to the
`[inv| … ]` spelling (the unexpanders — the book's Pretty Printing
mini-project).

GuestlangStd is READ-ONLY in this lane — the `userCompleteCheck`
MIGRATION is demonstrated on the mirror schema (the std module's
`VExpr.and userCheck userNameLenCheck` reads like the syntax spelling
below once it lands). -/

/-- The user schema, as the DSL tests see it — the 4-field mirror of
    `GuestImpl.userSchema` (abbrev — the reducibility rule). -/
abbrev dslUserSchema : List Field :=
  [ ⟨"id", .u64⟩, ⟨"name", .string⟩, ⟨"email", .string⟩
  , ⟨"tags", .list .string⟩ ]

/-- THE DEMO: `userCompleteCheck`'s spelling through the syntax — the
    id gate AND the name-length gate in ONE `[inv| … ]` term. -/
def userCompleteCheckDsl : VExpr dslUserSchema .bool :=
  [inv| id > 0 && strlen(name) > 3]

/-- The hand-spelled SAME tree (the pin's oracle). -/
def userCompleteCheckHand : VExpr dslUserSchema .bool :=
  VExpr.and
    (VExpr.gt (VExpr.colOf "id") (VExpr.lit 0))
    (VExpr.gt (VExpr.strlen (VExpr.colOf "name")) (VExpr.lit 3))

-- COMPILE = THE SAME VEXPR: the syntax elaborates to exactly the hand
-- constructor tree (definitional, not just eval-equal).
example : userCompleteCheckDsl = userCompleteCheckHand := rfl

def dslPositive : VExpr dslUserSchema .bool := [inv| id > 0]
def dslPositiveHand : VExpr dslUserSchema .bool :=
  VExpr.gt (VExpr.colOf "id") (VExpr.lit 0)
def dslEq : VExpr dslUserSchema .bool := [inv| id == 7]
def dslAnd : VExpr dslUserSchema .bool := [inv| id > 0 && id == 7]
def dslNameLong : VExpr dslUserSchema .bool := [inv| strlen(name) > 3]
-- the precedence pins: `&&` parses TIGHTER — `||` is the top node
def dslOrTop : VExpr dslUserSchema .bool :=
  [inv| id == 7 && id == 5 || id == 9]
def dslAndTight : VExpr dslUserSchema .bool :=
  [inv| id == 7 || id == 5 && id == 9]

/-- The full 4-field row (the tags list rides empty — the check does
    not read it). -/
def dslRow (id : UInt64) (nm : String) : RowVals dslUserSchema :=
  .cons (.u64 id) (.cons (.string nm)
    (.cons (.string "e") (.cons (.list .nil) .nil)))

def dslChecks : CheckResult := do
  -- the eval pins: the syntax-elaborated validators eval EXACTLY as
  -- the hand ones (both readings — the SPEC evalVBool and the raw
  -- `validates`)
  for n in [0, 1, 5, 7, 9, 42] do
    let row := dslRow n.toUInt64 "bobby"
    _ ← assertEq s!"dsl: positive ≡ hand id={n}"
      (validates dslPositive row) (validates dslPositiveHand row)
    _ ← assertEq s!"dsl: positive spec≡compiled id={n}"
      (evalVBool dslPositive row) (validates dslPositive row)
  -- the driving example's rows
  _ ← assertEq "dsl: id=5 passes" (validates dslPositive (dslRow 5 "bobby")) true
  _ ← assertEq "dsl: id=0 refused" (validates dslPositive (dslRow 0 "bobby")) false
  _ ← assertEq "dsl: eq hit" (validates dslEq (dslRow 7 "bobby")) true
  _ ← assertEq "dsl: eq miss" (validates dslEq (dslRow 5 "bobby")) false
  _ ← assertEq "dsl: and both" (validates dslAnd (dslRow 7 "bobby")) true
  _ ← assertEq "dsl: and half" (validates dslAnd (dslRow 5 "bobby")) false
  _ ← assertEq "dsl: strlen pass" (validates dslNameLong (dslRow 5 "bobby")) true
  _ ← assertEq "dsl: strlen short" (validates dslNameLong (dslRow 5 "ab")) false
  -- the DEMO's verdicts (the userCompleteCheck spelling)
  _ ← assertEq "dsl: userCompleteCheck complete row"
    (validates userCompleteCheckDsl (dslRow 5 "bobby")) true
  _ ← assertEq "dsl: userCompleteCheck zero id"
    (validates userCompleteCheckDsl (dslRow 0 "bobby")) false
  _ ← assertEq "dsl: userCompleteCheck short name"
    (validates userCompleteCheckDsl (dslRow 5 "ab")) false
  -- PRECEDENCE: `a && b || c` = `(a && b) || c` — the || fires on the
  -- id=9 row (the C disjunct); the misparse `a && (b || c)` would say
  -- false there
  _ ← assertEq "dsl: || is the top node (id=9)"
    (validates dslOrTop (dslRow 9 "bobby")) true
  _ ← assertEq "dsl: || top, A-side false (id=7)"
    (validates dslOrTop (dslRow 7 "bobby")) false
  -- and the mirror: `a || b && c` = `a || (b && c)` — the A disjunct
  -- fires on id=7 (the misparse `(a || b) && c` would say false)
  _ ← assertEq "dsl: && tighter (id=7)"
    (validates dslAndTight (dslRow 7 "bobby")) true
  _ ← assertEq "dsl: && tighter, miss (id=9)"
    (validates dslAndTight (dslRow 9 "bobby")) false
  .ok ()

-- The MISSPELLING's negative control, THROUGH the syntax: the
-- field-ref's `HasCol` instance search happens at the elaboration
-- site, so the typo fails the BUILD (the same gate the hand `colOf`
-- has — pinned at the syntax's site now). The strlen operand rides
-- the SAME gate (its index is forced to .string before the postponed
-- instance synth runs — the error names the CONCRETE type).
/-- error: failed to synthesize instance of type class
  HasCol dslUserSchema "iid" Ty.u64

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
info: [inv| iid > 0 ] : VExpr dslUserSchema Ty.bool -/
#guard_msgs in
#check ([inv| iid > 0] : VExpr dslUserSchema .bool)

/-- error: failed to synthesize instance of type class
  HasCol dslUserSchema "nane" Ty.string

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
info: [inv| strlen(nane) > 3 ] : VExpr dslUserSchema Ty.bool -/
#guard_msgs in
#check ([inv| strlen(nane) > 3] : VExpr dslUserSchema .bool)

/-! ### The unexpander pins — a VExpr pretty-prints back to `[inv| … ]`

The book's Pretty Printing pattern: per-ctor `@[app_unexpander]`, the
match-inside-the-pattern (children arrive already unembedded), and the
parenthesization that keeps the re-parse tree-exact. `#check` renders
the elaborated term — the pins ARE the pp output. -/

/-- info: [inv| id > 0 ] : VExpr dslUserSchema Ty.bool -/
#guard_msgs in
#check ([inv| id > 0] : VExpr dslUserSchema .bool)

/-- info: [inv| id > 0 && strlen(name) > 3 ] : VExpr dslUserSchema Ty.bool -/
#guard_msgs in
#check ([inv| id > 0 && strlen(name) > 3] : VExpr dslUserSchema .bool)

-- the numeral literal renders
/-- info: [inv| 42 > 0 ] : VExpr dslUserSchema Ty.bool -/
#guard_msgs in
#check ([inv| 42 > 0] : VExpr dslUserSchema .bool)

-- the || ROUND TRIP: the syntax → the De Morgan tree → back to the
-- SAME spelling (the De Morgan unexpander strips the `!`s)
/-- info: [inv| (id == 7 && id == 5) || (id == 9) ] : VExpr dslUserSchema Ty.bool -/
#guard_msgs in
#check ([inv| id == 7 && id == 5 || id == 9] : VExpr dslUserSchema .bool)

/-- info: [inv| (id > 0 && id == 7) || (id == 9 && id == 1) ] : VExpr dslUserSchema Ty.bool -/
#guard_msgs in
#check ([inv| id > 0 && id == 7 || id == 9 && id == 1] : VExpr dslUserSchema .bool)

-- the plain `not` renders as `!` (the operand parenthesized when
-- compound — the re-parse is the SAME tree)
/-- info: [inv| !(id > 0) ] : VExpr dslUserSchema Ty.bool -/
#guard_msgs in
#check ([inv| !(id > 0)] : VExpr dslUserSchema .bool)

/-- info: [inv| !(id > 0 && id == 7) ] : VExpr dslUserSchema Ty.bool -/
#guard_msgs in
#check ((VExpr.not (VExpr.and (VExpr.gt (VExpr.colOf "id") (VExpr.lit 0))
  (VExpr.eq (VExpr.colOf "id") (VExpr.lit 7)))) : VExpr dslUserSchema .bool)

-- the right-nested hand tree: the && splice parenthesizes the RIGHT
-- child (a left-assoc re-parse would be a DIFFERENT tree)
/-- info: [inv| id > 0 && (id == 7 && id == 7) ] : VExpr dslUserSchema Ty.bool -/
#guard_msgs in
#check ((VExpr.and (VExpr.gt (VExpr.colOf "id") (VExpr.lit 0))
  (VExpr.and (VExpr.eq (VExpr.colOf "id") (VExpr.lit 7))
    (VExpr.eq (VExpr.colOf "id") (VExpr.lit 7)))) :
  VExpr dslUserSchema .bool)

unsafe def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let ctx ← loadDemoCtx
  let goldens ← goldenChecks update
  let reflect ← reflectChecks
  let invGolden ← invariantGoldenChecks update
  let updGolden ← updateGoldenChecks update
  let vortexWf ← vortexWellFormedChecks
  let snapGate ← snapshotGateChecks
  let funcSemReflect ← funcSemReflectChecks
  let code ← mainOfChecks "SchemaLang"
    ([ ("resolution", resolutionChecks)
     , ("fieldRes", fieldResolutionChecks)
     , ("codec", codecChecks)
     , ("codecCombinators", codecCombinatorChecks)
     , ("envelope", envelopeChecks)
     , ("codecValue", CodecValueSweep.coverageChecks)
     , ("eqAns", eqAnsChecks)
     , ("diff", diffChecks)
     , ("ptype", ptypeChecks)
     , ("eqAnsRouting", eqAnsRoutingChecks)
     , ("snapshot", snapshotChecks)
     ] ++ goldens ++
     [ invGolden
     , updGolden
     , ("lower", lowerChecks)
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
     , ("orderMachine", orderMachineChecks)
     , ("emitterAudit", emitterAuditChecks ctx)
     , ("partition", partitionChecks ctx)
     , ("typedSession", typedSessionChecks)
     , ("propCoverage", PropSweep.propCoverageChecks)
     , ("funcSem", funcSemChecks)
     , funcSemReflect
     , ("validate", validateChecks)
     , ("strlen", strlenChecks)
     , ("dsl", dslChecks)
     , ("variant", variantChecks)
     , ("invariantChecks", invariantChecks ctx.invariants)
     , ("updateChecks", updateChecks ctx)
     , ("trace", traceChecks)
     , ("migration", migrationChecks)
     , ("subschema", subschemaChecks)
     , ("docs", docsChecks)
     , ("diagGolden", diagGoldenChecks)
     ])
  if code != 0 then return code
  -- the property sweep WITH its mandatory negative control
  -- (TestKit.PropSpec: the property must pass AND the sabotaged sibling
  -- must be caught — a vacuous sweep fails the gate)
  TestKit.runSpecs [PropSweep.spec, CodecValueSweep.spec]

/-! ## Debug commands (the author's REPL) — #guard_msgs smokes

The `#assertType` pattern's info-pins: each command's logged output is
pinned EXACTLY against the elab-time registry (Demo's rows, replayed
via import). `#guard_msgs (info)` fails elaboration on any drift, and —
because these commands only LOG — a misspelled-world pin also pins
GRACEFULNESS: if `#world gatway` ever threw, the build fails here.
No registry side effects: the pins are deterministic replays.
-/

/-- info: registered schema items (13):
  User : record user (4 fields)
  OrderItem : record order-item (3 fields)
  Order : record order (3 fields)
  Role : variant role (3 cases)
  OrderError : variant order-error (3 cases)
  getUser : func get-user(id: u64) -> option<user> delivery=once
  watchOrders : func watch-orders(into: order-error) -> future<list<user>> delivery=once
  Db : resource db
  probeVolatileFn : func probe-volatile-fn(x: u32) -> u32 delivery=once
  probeBothAxesFn : func probe-both-axes-fn(x: option<u32>) -> option<u32> delivery=once
  probeDefaultFn : func probe-default-fn(x: u32, y: u32) -> u32 delivery=once
  updClockFn : func upd-clock-fn(seed: u64) -> u64 delivery=once
  updPureFn : func upd-pure-fn(x: u64) -> u64 delivery=once -/
#guard_msgs in
#schema

/-- info: package guestlang;

interface gateway-types {
record user {
  id: u64,
  name: string,
  email: string,
  tags: list<string>,
}
record order-item {
  id: u64,
  qty: u32,
  price: f64,
}
record order {
  id: u64,
  items: list<order-item>,
  total: f64,
}
variant role {
  admin,
  editor,
  viewer,
}
variant order-error {
  empty-cart,
  invalid-item(u64),
  insufficient-funds(f64),
}
resource db;
}

interface gateway-exports {
  use gateway-types.{user, order-error};
    get-user: func(id: u64) -> option<user>;
    watch-orders: async func(into: order-error) -> list<user>;
    probe-volatile-fn: func(x: u32) -> u32;
    probe-both-axes-fn: func(x: option<u32>) -> option<u32>;
    probe-default-fn: func(x: u32, y: u32) -> u32;
    upd-clock-fn: func(seed: u64) -> u64;
    upd-pure-fn: func(x: u64) -> u64;
}

world gateway {
  export gateway-exports;
} -/
#guard_msgs in
#world gateway

/-- info: package guestlang;

interface gatway-types {
record user {
  id: u64,
  name: string,
  email: string,
  tags: list<string>,
}
record order-item {
  id: u64,
  qty: u32,
  price: f64,
}
record order {
  id: u64,
  items: list<order-item>,
  total: f64,
}
variant role {
  admin,
  editor,
  viewer,
}
variant order-error {
  empty-cart,
  invalid-item(u64),
  insufficient-funds(f64),
}
resource db;
}

interface gatway-exports {
  use gatway-types.{user, order-error};
    get-user: func(id: u64) -> option<user>;
    watch-orders: async func(into: order-error) -> list<user>;
    probe-volatile-fn: func(x: u32) -> u32;
    probe-both-axes-fn: func(x: option<u32>) -> option<u32>;
    probe-default-fn: func(x: u32, y: u32) -> u32;
    upd-clock-fn: func(seed: u64) -> u64;
    upd-pure-fn: func(x: u64) -> u64;
}

world gatway {
  export gatway-exports;
} -/
#guard_msgs in
#world gatway

/-- info: span rows (7):
  SpanSpec { name: "get-user", delivery: "once", fields: &[("id", "u64")] }
  SpanSpec { name: "watch-orders", delivery: "once", fields: &[("into", "order-error")] }
  SpanSpec { name: "probe-volatile-fn", delivery: "once", fields: &[("x", "u32")] }
  SpanSpec { name: "probe-both-axes-fn", delivery: "once", fields: &[("x", "option<u32>")] }
  SpanSpec { name: "probe-default-fn", delivery: "once", fields: &[("x", "u32"), ("y", "u32")] }
  SpanSpec { name: "upd-clock-fn", delivery: "once", fields: &[("seed", "u64")] }
  SpanSpec { name: "upd-pure-fn", delivery: "once", fields: &[("x", "u64")] } -/
#guard_msgs in
#spans
