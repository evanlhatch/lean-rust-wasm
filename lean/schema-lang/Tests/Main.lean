/-
# SchemaLang Tests

Resolution wellFormed (accept/reject), EqAns direction, compat diff,
WIT golden emission.
-/
import Lean
import SchemaLang
import SchemaLang.Emit.GenCtx
import SchemaLang.Emit.GenRust
import SchemaLang.Emit.Expr
import SchemaLang.Emit.Invariant
import SchemaLang.Emit.Update
import SchemaLang.Bridge
import SchemaLang.Witness
import SchemaLang.WitnessCheck
import SchemaLang.Meta.WireCodec
import SchemaLang.TableInvariant
import SchemaLang.Meta.TableInvariant
import SchemaLang.Update2
import Demo
import SchemaLang.Trace
import Machines
import TestKit

-- the Tests' own `schema_update` probe (updPureCall) emits its instance
-- into SchemaLang by the framework's construction — same as Demo
set_option linter.guestlang.packageNamespace false -- because the framework's registration command emits the instance into SchemaLang by construction; no source-site attribute exists

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

/-! ## W3.5 — `WellFormed` (the reasoning authority) via the checker bridge -/

/-- The broken-universe fixture at top level (the bridge's negative
    control quantifies over it in a theorem). -/
def wfBrokenItems : List Item :=
  [ .record "a" [{ name := "x", ty := .ty "usr" }], .record "user" [] ]

/-- The demo universe is well-formed, VIA the sound bridge: the checker
    discharges (`rfl`), the relation receives. -/
theorem demoItems_wellFormed : WellFormed demoItems :=
  universeCheck_sound rfl

/-- The complete direction on the same fixture: the relation certifies
    the clean run. -/
theorem demoItems_universeCheck_nil : universeCheck demoItems = [] :=
  universeCheck_complete demoItems_wellFormed

/-- NEGATIVE CONTROL (non-vacuity): a universe with an unresolvable ref
    is NOT well-formed — the complete bridge would certify a clean run,
    but the checker finds one diag. A vacuous `WellFormed` (inhabited
    for every list) breaks this proof. -/
theorem broken_not_wellFormed : ¬ WellFormed wfBrokenItems := by
  intro hwf
  have hnil := universeCheck_complete hwf
  have hlen : (universeCheck wfBrokenItems).length = 1 := rfl
  rw [hnil] at hlen
  exact absurd hlen (by decide)

/-! ## The linen patterns, exercised -/

/-- Schema-indexed field resolution (abbrev list — the reducibility rule). -/
abbrev userFields : List Field :=
  [ ⟨"id", .u64⟩, ⟨"name", .string⟩, ⟨"email", .string⟩ ]

def fieldResolutionChecks : CheckResult := do
  _ ← assertEq "id at 0" (fieldIndex userFields "id" .u64) 0
  _ ← assertEq "email at 2" (fieldIndex userFields "email" .string) 2
  .ok ()

def codecChecks : CheckResult := do
  -- the round trips are PROVED (Codec.decode_encodeBool/decode_encodeU8 —
  -- axiom-gated); what needs executing is the REJECTION surface
  _ ← assertEq "bool reject" (Codec.decodeBool [5]) none
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
  let broken : List Item := wfBrokenItems
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

/-! ## Generator emitter (W6.4): Rust gen fns from the registry -/

/-- The W6.4 phase-1 pins: the fragment gate (what generates, what
    SKIPS LOUDLY), the emitted fn shape (budget-threaded, pool-fed,
    field-wise), and the demo-universe sweep (EVERY record gets a fn —
    the non-vacuity control: a fragment that skipped everything would
    still pass the shape pins). -/
def genRustChecks (ctx : SchemaLang.Emit.GenCtx) : CheckResult := do
  -- the fragment gate: scalars/string/bytes/option/list generate;
  -- tensor/result/future/stream skip
  _ ← assert (SchemaLang.Emit.GenRust.unsupported? [] 8 .u64 == none) "u64 supported"
  _ ← assert (SchemaLang.Emit.GenRust.unsupported? [] 8 (.option (.list .string)) == none)
    "option<list<string>> supported"
  _ ← assert ((SchemaLang.Emit.GenRust.unsupported? [] 8 (.tensor [2] .f32)).isSome)
    "tensor skipped"
  _ ← assert ((SchemaLang.Emit.GenRust.unsupported? [] 8 (.result .u64 .string)).isSome)
    "result skipped"
  _ ← assert ((SchemaLang.Emit.GenRust.unsupported? [] 8 (.future .u64)).isSome)
    "future skipped"
  _ ← assert ((SchemaLang.Emit.GenRust.unsupported? [] 8 (.stream .u8)).isSome)
    "stream skipped"
  -- refs: resolvable records generate; variants/ghosts/cycles skip
  let inner : Item := .record "inner" [{ name := "x", ty := .u64 }]
  let outer : Item := .record "outer" [{ name := "i", ty := .ty "inner" }]
  let uni := [inner, outer, demoRole]
  _ ← assert (SchemaLang.Emit.GenRust.unsupported? uni 8 (.ty "inner") == none)
    "record ref supported"
  _ ← assert ((SchemaLang.Emit.GenRust.unsupported? uni 8 (.ty "role")).isSome)
    "variant ref skipped"
  _ ← assert ((SchemaLang.Emit.GenRust.unsupported? uni 8 (.ty "ghost")).isSome)
    "ghost ref skipped"
  let cycA : Item := .record "cyc-a" [{ name := "b", ty := .ty "cyc-b" }]
  let cycB : Item := .record "cyc-b" [{ name := "a", ty := .ty "cyc-a" }]
  _ ← assert ((SchemaLang.Emit.GenRust.unsupported? [cycA, cycB] 8 (.ty "cyc-a")).isSome)
    "ref cycle skipped (fuel-bounded)"
  -- the skip is LOUD: a comment names the record, the field, the reason
  let tensored : Item := .record "tensored" [{ name := "t", ty := .tensor [2] .f32 }]
  let skipOut := CodegenCore.Emit.Rust.renderModule
    [SchemaLang.Emit.GenRust.recordGenItem [tensored] "tensored"
      [{ name := "t", ty := .tensor [2] .f32 }]]
  _ ← assert (skipOut.contains "gen_tensored SKIPPED") "skip marker"
  _ ← assert (skipOut.contains "'t'") "skip names the field"
  _ ← assert (!skipOut.contains "pub fn gen_tensored") "no fn for a skipped record"
  -- the emitted fn shape: budget-threaded, pool-fed, field-wise
  let out := CodegenCore.Emit.Rust.renderModule
    (SchemaLang.Emit.GenRust.genRustItems uni)
  _ ← assert (out.contains "pub fn gen_inner(") "inner gen fn"
  _ ← assert (out.contains "pub fn gen_outer(") "outer gen fn"
  _ ← assert (out.contains "gen_inner(u, max_depth.saturating_sub(1))?")
    "ref recursion spends the budget"
  _ ← assert (out.contains "STRING_POOL") "collision pool emitted"
  _ ← assert (out.contains "\"inner\"") "pool carries the record names"
  _ ← assert (out.contains "u.ratio(9, 10)?") "90/10 pool discipline"
  _ ← assert (out.contains "if max_depth == 0") "forced leaf at 0"
  _ ← assert (!out.contains "gen_role(") "variants get no gen fn (v1)"
  -- the emitter: declared path, determinism, and EVERY ctx record gets
  -- a fn (the non-vacuity sweep)
  let files := genRustEmitter.run ctx
  _ ← assertEq "gen-rust path" (files.head?.map (·.path))
    (some "../../src/gen_generated.rs")
  _ ← assertEq "gen-rust deterministic" (files.map (·.contents))
    ((genRustEmitter.run ctx).map (·.contents))
  let demoOut := files.head?.map (·.contents) |>.getD ""
  let records := ctx.items.filter fun it =>
    match it with | .record .. => true | _ => false
  _ ← assert (!records.isEmpty) "ctx carries records (the sweep is non-vacuous)"
  for r in records do
    _ ← assert (demoOut.contains s!"pub fn gen_{CodegenCore.Emit.snake r.name}(")
      s!"gen fn for record '{r.name}'"
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

/-- CITATION (W7.3 phase 2): the checked/unchecked byte-agreement
    theorem's only prior evidence was existence — it is referenced
    here so it cannot silently vanish. (The three impossibility
    theorems' citation is the vortex emitter's populated `law`; the
    certified-lane execution pins live in `emitterAuditChecks`.) -/
theorem recordDTypesChecked_eq_cited
    (cu : SchemaLang.CheckedUniverse) (fuel : Nat := 8) :
    SchemaLang.Vortex.Emit.recordDTypesChecked cu fuel =
      SchemaLang.Vortex.Emit.recordDTypes cu.val fuel :=
  SchemaLang.Vortex.Emit.recordDTypesChecked_eq cu fuel

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
  _ ← assert (rs.any (·.1 == "invariant-non-vacuity")) "invariant-non-vacuity ran"
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
    The advertised discipline (codegen-core's `Emitter.checkNodup` —
    W7.3 phase 2 deduped schema-lang's inline `pathsUnique` copy) is
    ASSERTED here, not just stated in a header. -/
def emitterAuditChecks (ctx : SchemaLang.Emit.GenCtx) : CheckResult := do
  _ ← assertEq "emitter paths unique"
    (CodegenCore.Emit.Emitter.checkNodup SchemaLang.Emit.emitters) true
  -- W7.3 phase 2: the emission laws are POPULATED (the phase-1 `none`
  -- default would leave the impossibility theorems uncited), and the
  -- certified lane executes — discharging the cert changes no bytes
  -- (`runCertified = run` by definition; asserted over this ctx).
  _ ← assert (SchemaLang.Vortex.Emit.vortexEmitter.law.isSome)
    "vortex law populated"
  _ ← assert (SchemaLang.Emit.Circuit.circuitEmitter.law.isSome)
    "circuit law populated"
  _ ← assertEq "vortex certified run = run"
    ((SchemaLang.Vortex.Emit.vortexEmitter.runCertified ctx
      (SchemaLang.Vortex.Emit.vortexLaw_discharged ctx)).map (·.contents))
    ((SchemaLang.Vortex.Emit.vortexEmitter.run ctx).map (·.contents))
  _ ← assertEq "circuit certified run = run"
    ((SchemaLang.Emit.Circuit.circuitEmitter.runCertified ctx
      (SchemaLang.Emit.Circuit.circuitLaw_discharged ctx)).map (·.contents))
    ((SchemaLang.Emit.Circuit.circuitEmitter.run ctx).map (·.contents))
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
  | .map k _, .map m => sizeM k m + 1
  | .set k, .set vl => sizeL k.toTy vl + 1
  | .stream a, .stream vl => sizeL a vl + 1
  | .tensor _ a, .tensor tv => sizeT a tv + 1

def sizeL : (t : Ty) → VList t → Nat
  | _, .nil => 0
  | t, .cons v vl => sizeV t v + sizeL t vl + 1

def sizeM : (k : KeyTy) → {v : Ty} → VMap k v → Nat
  | _, _, .nil => 0
  | k, _, .cons kv vv m => sizeV k.toTy kv + sizeV _ vv + sizeM k m + 1

-- every wrapper +1: the repr chain (valueReprStr ⇄ valueTReprStr ⇄
-- slicesReprStr) needs each cross-function call to STRICTLY decrease
def sizeT : (t : Ty) → {dims : List Nat} → TVal t dims → Nat
  | t, _, .scalar v => sizeV t v + 1
  | t, _, .dim ss => sizeS t ss + 1

def sizeS : (t : Ty) → {dims : List Nat} → {m : Nat} → TSlices t dims m → Nat
  | _t, _, _, .nil => 0
  | t, _, _, .cons x ss => sizeT t x + sizeS t ss + 1

end

-- Structural equality on `Value t`: LIFTED to SchemaLang.Gen (the
-- library's `valueEq`/`valueEq_refl` — same bodies; the sweep consumes
-- the library versions via `open SchemaLang`).

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
  | .map k _, .map m => s!"map [{vMapReprStr k m}]"
  | .set k, .set vl => s!"set [{vListReprStr k.toTy vl}]"
  | .stream t, .stream vl => s!"stream [{vListReprStr t vl}]"
  | .tensor _ a, .tensor tv => s!"tensor [{valueTReprStr a tv}]"
  termination_by t v => sizeV t v
decreasing_by all_goals (simp [sizeV])

def valueTReprStr : (t : Ty) → {dims : List Nat} → TVal t dims → String
  | t, _, .scalar v => valueReprStr t v
  | t, _, .dim ss => slicesReprStr t ss
  termination_by t _ tv => sizeT t tv
decreasing_by all_goals (simp [sizeT])

def slicesReprStr : (t : Ty) → {dims : List Nat} → {m : Nat} → TSlices t dims m → String
  | _, _, _, .nil => ""
  | t, _, _, .cons x ss =>
      let rest := slicesReprStr t ss
      let head := valueTReprStr t x
      if rest == "" then head else s!"{head}, {rest}"
  termination_by t _ _ ss => sizeS t ss
decreasing_by all_goals (simp [sizeS]; omega)

def vListReprStr : (t : Ty) → VList t → String
  | _, .nil => ""
  | t, .cons v vl =>
      let rest := vListReprStr t vl
      if rest == "" then valueReprStr t v else s!"{valueReprStr t v}, {rest}"
  termination_by t vl => sizeL t vl
decreasing_by all_goals (simp [sizeL]; omega)

def vMapReprStr : (k : KeyTy) → {v : Ty} → VMap k v → String
  | _, _, .nil => ""
  | k, _, .cons kv vv m =>
      let rest := vMapReprStr k m
      let head := s!"{valueReprStr k.toTy kv} => {valueReprStr _ vv}"
      if rest == "" then head else s!"{head}, {rest}"
  termination_by k _ m => sizeM k m
decreasing_by all_goals (simp [sizeM]; omega)

end

/-! ### the TENSOR round trip (the shape gate, pinned both ways) -/

-- the 2×3 u64 tensor, row-major (2 rows of 3)
def demoDims : List Nat := [2, 3]

def demoRow (a b c : UInt64) : TVal .u64 [3] :=
  .dim (.cons (.scalar (.u64 a)) (.cons (.scalar (.u64 b))
    (.cons (.scalar (.u64 c)) .nil)))

def demoTv : TVal .u64 demoDims :=
  .dim (.cons (demoRow 0 1 2) (.cons (demoRow 3 4 5) .nil))

def demoVal : Value (.tensor demoDims .u64) := .tensor demoTv

-- the flatten's length = the product (the count gate's input)
#guard (TVal.toList demoTv).length = 6

-- THE LAYOUT TIE, executed (Layout.toList_get): the flatten (the wire
-- order) at the typed offset IS the coordinate's element — coordinate
-- (1,0) in [2,3] sits at flat 1·3+0 = 3, holding the value 3. The
-- ingress route (Coords.ofList?) validates once; the read is total.
-- (Bool form via valueEq — the GADT has no DecidableEq.)
#guard (match Coords.ofList? demoDims [1, 0] with
  | some cs =>
      match (TVal.toList demoTv)[(flatIdxT demoDims cs : Nat)]? with
      | some v => valueEq .u64 v (TVal.get demoTv cs)
      | none => false
  | none => false) = true
#guard (match Coords.ofList? demoDims [1, 0] with
  | some cs =>
      match (TVal.toList demoTv)[(flatIdxT demoDims cs : Nat)]? with
      | some v => valueEq .u64 v (.u64 3)
      | none => false
  | none => false) = true
#guard (match Coords.ofList? demoDims [1, 3] with
  | none => true | some _ => false) = true  -- the boundary check bites

-- THE ROUND TRIP, executed: encode → decode = the same value (the
-- byte-equality — the GADT has no DecidableEq, the valueEq route)
#guard (match decodeValue (.tensor demoDims .u64)
      (encodeValue (.tensor demoDims .u64) demoVal) with
  | some v => valueEq (.tensor demoDims .u64) v demoVal
  | none => false) = true

-- THE NEGATIVE CONTROL: the wire's dims ([2,3]) against a [2,4]-typed
-- decode — the FIRST shape gate (wireDims = the type's dims) refuses;
-- the corruption is a decode failure, never a mis-shaped TVal
-- (unconstructible). (A TRUNCATION control is NOT the shape gate's:
-- the varint's documented totality — empty input reads (0, []) —
-- makes a truncated ELEMENT stream decode with a zero-padded last
-- element; the count prefix there is intact.)
#guard (match decodeValue (.tensor [2, 4] .u64)
      (encodeValue (.tensor demoDims .u64) demoVal) with
  | none => true
  | some _ => false) = true


-- (the checks consuming these renderings follow)

instance : Repr Pack where
  reprPrec p _ := s!"⟨{repr p.t}, {valueReprStr p.t p.val}⟩"

instance : Shrinkable Pack where
  shrink p :=
    if valueEq p.t p.val (defaultValue p.t p.h) then []
    else [⟨p.t, p.h, defaultValue p.t p.h⟩]

/-! ### the generators (LIFTED to SchemaLang.Gen — the sweep consumes
the library's `genShortList`/`genChar`/`genU8`/`genVal` via
`open SchemaLang`; the test-side verbatim copies are gone) -/

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

/-- A key-type choice (the `KeyTy` sub-universe, uniformly). -/
def genKeyTy : Gen KeyTy := do
  let n ← Gen.chooseNat
  pure (match n % 10 with
    | 0 => .bool | 1 => .u8 | 2 => .u16 | 3 => .u32 | 4 => .u64
    | 5 => .i8 | 6 => .i16 | 7 => .i32 | 8 => .i64 | _ => .string)

def genPack : Nat → Gen Pack
  | 0 => genLeafPack
  | fuel + 1 => do
    let branch ← Gen.chooseNat
    match branch % 8 with
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
    | 5 => do
      let p ← genPack fuel
      let vs ← genShortList (genVal p.t p.h fuel) 3
      pure ⟨.stream p.t, .stream p.h, .stream (listToVList vs)⟩
    -- W8.1: map/set packs (the new `CodecClosed` arms ride the SAME
    -- sweep — the master theorem's executable image covers them)
    | 6 => do
      let p ← genPack fuel
      let k ← genKeyTy
      let ks ← genShortList (genKey k) 3
      let vs ← genShortList (genVal p.t p.h fuel) 3
      pure ⟨.map k p.t, .map p.h, .map (listToVMap (ks.zip vs))⟩
    | _ => do
      let k ← genKeyTy
      let es ← genShortList (genKey k) 3
      pure ⟨.set k, .set, .set (listToVList es)⟩
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

/-! ## The ROW generators (derive_row_gen — the registry-driven lane) -/

-- DERIVED at elaboration from the registry (`SchemaLang.Meta.derive_row_gen`):
-- Demo's `@[schema]` record User → the row generator + the shape (the
-- fields abbrev). Not hand mirrors: renaming a field or changing a
-- field's type in Demo.lean fails THIS module's elaboration. The
-- refusal discipline: a non-closed field (f32/f64/.ty — OrderItem's
-- Float, say) throws here, so an ungeneratable row is UNWRITABLE, not
-- a runtime `none`.
derive_row_gen for User

-- The generated row round-trips through the ROW codec (Trace's
-- decRowVals_encRowVals_append law, executed on a GENERATED row — the
-- generator feeds the proved law; pinned seed, deterministic).
def rowGenChecks : CheckResult := do
  match PropSweep.runGenPure (userRowGen 3) 20261105 5 with
  | .ok row =>
      -- decode (encode row) = some (r, []) with r re-encoding to the
      -- same bytes (the valueEq discipline at row level — RowVals has
      -- no BEq; the codec's bytes are the equality, as proved)
      _ ← assert (match decRowVals? userRowGenFields
              (encRowVals userRowGenFields row) with
        | some (r, []) => encRowVals userRowGenFields r
            == encRowVals userRowGenFields row
        | _ => false)
        "rowGen: generated User row round-trips"
  | .error e => assert false s!"rowGen: generator errored: {repr e}"

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
      (Machines.Session.tdual (toWire gatewayTyped))) "typed dual bridge"
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

/-! ## Provenance (W7.5) — doc strings follow items through the parallel registry -/

/-- The provenance extension (schemaItemDocsExt) replayed from the Demo
    olean: documented items carry their doc string; undocumented ones
    return empty. -/
unsafe def provenanceChecks : IO (String × CheckResult) := do
  let env ← loadDemoEnv
  let r : CheckResult := do
    -- getUser has a doc string ("u64 \u2192 option<user>. The body is a stub...")
    let getUserDoc := SchemaLang.Meta.itemDoc? env ``getUser
    _ ← assert (getUserDoc.contains "u64") "getUser doc contains 'u64'"
    _ ← assert (getUserDoc.contains "option") "getUser doc contains 'option'"
    -- Db has a doc string ("An opaque handle type...")
    let dbDoc := SchemaLang.Meta.itemDoc? env ``Db
    _ ← assert (dbDoc.contains "opaque") "Db doc contains 'opaque'"
    _ ← assert (dbDoc.contains "handle") "Db doc contains 'handle'"
    -- User has no doc string (the `-- ## Records` is a section comment, not a doc comment)
    _ ← assertEq "User doc is empty" (SchemaLang.Meta.itemDoc? env ``User) ""
    -- provenanceOf format: "declName: first line" or just "declName" when undocumented
    let p1 := SchemaLang.Meta.provenanceOf env ``getUser
      (Item.func { name := "get-user", params := [("id", .u64)], ret := .option (.ty "user") })
    _ ← assert (p1.contains "getUser") "provenanceOf getUser: contains name"
    _ ← assert (p1.contains "u64") "provenanceOf getUser: contains doc fragment"
    let p2 := SchemaLang.Meta.provenanceOf env ``User (Item.record "user" [])
    _ ← assert (p2.contains "User") "provenanceOf User: contains name"
    _ ← assert (p2.contains ":" == false) "provenanceOf User: no doc = no colon"
  pure ("provenance", r)

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

/-! ## W7.2 — the ExprLang interface: TWO readings, written once -/

/-- The probe expression, exercising EVERY bool ctor and every u64
    leaf shape the interface exposes: `(id == 7) && !((id > 0) &&
    (strlen name > 3))` — eq/and/not over gt/lit/col/strlenCol. -/
def probeExpr : VExpr valUserFields .bool :=
  .and valEq (.not (.and valPositive valNameLong))

/-- The two EVALUATION readings behind the interface agree with the
    GADT's own evaluators on the probe (the theorems
    `evalSpecI_vexpr`/`evalRawI_vexpr`/`validatesI_vexpr` are the
    proof half; these executed pins are the behavior half — the
    interface is not emission-shaped-only). -/
def exprLangChecks : CheckResult := do
  let L := vexprLang valUserFields
  for (id, nm) in [(0, "ab"), (1, "abcd"), (7, "ab"), (7, "abcd"), (42, "xyz")] do
    let row := valRowName id.toUInt64 nm
    -- reading #1: the BOXED reading through the fold ≡ evalV
    _ ← assertEq s!"boxed reading ≡ evalV (id={id}, name={nm})"
      (evalSpecI L probeExpr row) (evalVBool probeExpr row)
    -- reading #2: the RAW (0/1-word) reading through the fold ≡ evalB
    _ ← assertEq s!"raw reading ≡ evalB (id={id}, name={nm})"
      (evalRawI L probeExpr row) (evalB probeExpr row)
    -- the validator projection through the interface ≡ validates
    _ ← assertEq s!"validatesI ≡ validates (id={id}, name={nm})"
      (validatesI L probeExpr row) (validates probeExpr row)
  -- non-vacuity: the probe DISTINGUISHES rows under both readings
  _ ← assert (evalSpecI L probeExpr (valRowName 7 "ab")
        != evalSpecI L probeExpr (valRowName 0 "ab"))
    "boxed reading distinguishes rows (non-vacuous)"
  _ ← assert (evalRawI L probeExpr (valRowName 7 "ab")
        != evalRawI L probeExpr (valRowName 0 "ab"))
    "raw reading distinguishes rows (non-vacuous)"
  .ok ()

/-! ## W7.2 phase 2 — the emission consumers ride the interface

Phase 2 ported Emit.Update's guard/value lowering onto
`Emit.Expr.u64RustI`/`boolRustI` at the `vexprLang` instance (phase 1
was the invariant lane; the COMPAT spellings are gone) and ported
Emit.Invariant's `defaultVerdict` to `validatesI`. The golden
byte-ties (`invariantGoldenChecks`/`updateGoldenChecks`) pin the whole
artifacts; these pins are the PER-EXPRESSION half: the exact Rust
text the fold produces for a guard exercising every bool ctor over
every u64 leaf shape, and the ported `valueRust` arms (the interface
u64 arm, the justified GADT-direct string arm, the honest skip). -/

/-- The probe guard's emission text at the update lane's `r.<field>`
    ref — the exact bytes `applyFn` splices into the `if`. -/
def probeGuardText : String :=
  SchemaLang.Emit.Expr.boolRustI (vexprLang valUserFields)
    SchemaLang.Emit.Update.refOf probeExpr

/-- The probe's u64 leaves' emission texts (lit / col / strlenCol —
    the `HasU64` view's three shapes). -/
def probeU64Texts : List String :=
  [ SchemaLang.Emit.Expr.u64RustI (vexprLang valUserFields)
      SchemaLang.Emit.Update.refOf (.lit 0)
  , SchemaLang.Emit.Expr.u64RustI (vexprLang valUserFields)
      SchemaLang.Emit.Update.refOf (.colOf "id")
  , SchemaLang.Emit.Expr.u64RustI (vexprLang valUserFields)
      SchemaLang.Emit.Update.refOf valStrlen ]

def exprEmitChecks : CheckResult := do
  -- the fold at the emission algebra, BYTE-PINNED: eq/and/not over
  -- gt/lit/col/strlenCol (the probe's full ctor coverage)
  _ ← assertEq "guard text through the interface fold (byte-pin)"
    probeGuardText
    "((r.id == 7u64) && (!(((r.id > 0u64) && ((r.name).len() as u64 > 3u64)))))"
  -- the u64 leaf texts (the ported value lane's building blocks)
  _ ← assertEq "u64 leaf texts through the view (byte-pin)"
    probeU64Texts ["0u64", "r.id", "(r.name).len() as u64"]
  -- the ported `valueRust`: the u64 arm rides the interface
  _ ← assertEq "valueRust: u64 arm via HasU64.view"
    (SchemaLang.Emit.Update.valueRust (fs := valUserFields) (.lit 0))
    (some "0u64")
  -- the string-write arm stays GADT-direct (justified: no HasString
  -- capability — syntax-directed at the `.string` index)
  _ ← assertEq "valueRust: string .col arm (GADT-direct, justified)"
    (SchemaLang.Emit.Update.valueRust (fs := valUserFields) (.colOf "name"))
    (some "(r.name).clone()")
  -- the honest skip: a bool-typed value has no lowering
  _ ← assertEq "valueRust: non-lowerable shape skips honestly"
    (SchemaLang.Emit.Update.valueRust (fs := valUserFields) valPositive)
    (none : Option String)
  -- non-vacuity: the byte-pins are LIVE text — a sabotaged algebra
  -- (here: the guard under a different ref) yields different bytes
  _ ← assert
    (SchemaLang.Emit.Expr.boolRustI (vexprLang valUserFields)
        (fun n => s!"v.{n}") probeExpr != probeGuardText)
    "emission reading depends on the ref (non-vacuous byte-pin)"
  .ok ()

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
@[nolint linter.guestlang.dupDefBodies "deliberate mirror: the hand spelling vs the [inv| ...] spelling — the alpha-equality IS the test (the rfl pin below each pair)"]
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
      let fsList := SchemaLang.Meta.fieldsToExpr it.inv.fields
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

-- The WIRED proved-tier citation gate (the elaboration-time resolver,
-- `SchemaLang.checkCitation?`): a dangling, non-theorem, or
-- wrong-shaped citation fails ELABORATION — the stored-but-unchecked
-- hole is closed. Negative controls (the positive one is Demo.lean's
-- `name-min-length` registration, which resolves `userNameLenProved`
-- at every build).
/-- error: schema_invariant `invCiteDangling`: cited proof `noSuchTheoremAnywhere` does not resolve -/
#guard_msgs in
schema_invariant invCiteDangling for User proved noSuchTheoremAnywhere :=
  VExpr.gt (VExpr.colOf "id") (VExpr.lit 0)

/-- error: schema_invariant `invCiteNotAThm`: cited proof `invRow` is not a theorem — a proved-tier citation cites a proof -/
#guard_msgs in
schema_invariant invCiteNotAThm for User proved invRow :=
  VExpr.gt (VExpr.colOf "id") (VExpr.lit 0)

theorem citationWrongShape : 1 = 1 := rfl

/-- error: schema_invariant `invCiteWrongShape`: cited proof `citationWrongShape` has type `Eq.{1} Nat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))` — not the proved-invariant shape `validates <the registered predicate> <row> = true` -/
#guard_msgs in
schema_invariant invCiteWrongShape for User proved citationWrongShape :=
  VExpr.gt (VExpr.colOf "id") (VExpr.lit 0)

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
  -- W7.1: the obligation view — the registered rows enumerate as
  -- obligations, the ladder's rungs map to discharge tiers, and every
  -- computed-tier obligation DISCHARGES (the theorem, witnessed)
  let obs := invs.map SchemaLang.InvariantItem.obligation
  _ ← assertEq "obligation labels enumerate" (obs.map (·.label))
    ["id-positive", "name-min-length"]
  _ ← assertEq "obligation tiers map"
    (obs.map (·.tier))
    [CodegenCore.Obligation.Tier.generatedCheck, .provedAtElab]
  _ ← assertEq "computed-tier obligations discharge"
    (obs.map (fun o => (SchemaLang.SchemaObligation.discharge o).isSome)) [true, true]
  _ ← assertEq "proved row's evidence is the citation"
    (SchemaLang.SchemaObligation.discharge obs[1]!)
    (some (.citedProof `userNameLenProved))
  _ ← assertEq "boundary row's evidence is the emitted check fn"
    (SchemaLang.SchemaObligation.discharge obs[0]!)
    (some (.generatedCheck "../../src/invariants_generated.rs" "check_id_positive"))
  -- negative control: a hand-set proved tier WITHOUT the citation is
  -- the loud gap — discharge refuses, it does not fabricate evidence
  let bogus := { obs[0]! with tier := CodegenCore.Obligation.Tier.provedAtElab }
  _ ← assertEq "citation-less proved tier discharges to NONE (the loud gap)"
    (SchemaLang.SchemaObligation.discharge bogus) none
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

/-! ## Proved-tier citation resolution (the cert pattern, MADE REAL)

`Tier.proved` stores a `proofName : Option Name`; the registration
command now RESOLVES it at elaboration (`SchemaLang.checkCitation?` in
SchemaLang.Invariant — the `Dbsp.Certs.#check_cert` pattern): the cited
decl must exist, be a theorem, have a clean axiom footprint (no
`sorryAx`), and carry the expected SHAPE — `validates <the registered
predicate> <row> = true` for some row. A bad citation fails the
REGISTRATION — Demo.lean's `userNameLenProved` (moved here-to-spec:
the citation must live where it's cited) is the positive control that
rides every build. This module keeps the row-level sweep + its
negative controls (the resolver CATCHES a bogus name and an axiom
citation — a resolver that accepts everything is vacuous). -/

-- The theorem the proved-tier invariant `invNameMinLength` cites now
-- lives in Demo.lean (the citation resolves at the registration, so
-- the theorem must be declared there — this module imports it). -/

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

/-! ## W7.1 phase 2 — the decidableNow obligation backend

The backend (`SchemaLang.SchemaObligation.discharge`'s `decidableNow`
arm) runs `decide` over the obligation's `decidableClaim` — the
registered predicate's verdict on the ALL-DEFAULT row (the same row
the emitted `#[test]` pins, so the decide discharge and the Rust CI
replay decide the SAME fact). A true claim discharges to
`.decided true`; a false claim or a default-less record REFUSES
(`none`, loudly — no fabricated evidence). The soundness theorem
(`discharge_decidableNow_sound`, axiom-pinned in Tests/Axioms.lean)
is CITED by `decNowTrue_holds` below: the demo obligation's
discharge yields the `validates` verdict AS a theorem. -/

/-- The demo item: the empty-schema invariant `lit 1 > lit 0` — TRUE
    on the (only) default row. -/
def decNowTrueItem : SchemaLang.InvariantItem :=
  { name := "dec-now-true", schemaRef := "User", tier := .boundaryCheck
  , proofName := none, inv := ⟨[], .gt (.lit 1) (.lit 0)⟩ }

/-- The demo obligation, hand-tiered decidableNow (no invariant-lane
    rung computes it — the tier is a backend ASSIGNMENT, registration
    computes only the three invariant rungs). -/
def decNowTrueObligation : SchemaLang.SchemaObligation :=
  { decNowTrueItem.obligation with tier := .decidableNow }

/-- The soundness theorem, CITED: the `.decided true` discharge IS the
    claim — here the denotation `validates (lit 1 > lit 0) nil = true`
    (the claim reduces to it: the empty schema's default row IS
    `RowVals.nil`). -/
theorem decNowTrue_holds :
    validates (.gt (.lit 1) (.lit 0) : VExpr [] .bool) .nil = true :=
  decNowTrueObligation.discharge_decidableNow_sound rfl rfl

/-- Negative control 1: `lit 0 > lit 0` — FALSE on the default row. -/
def decNowFalseItem : SchemaLang.InvariantItem :=
  { name := "dec-now-false", schemaRef := "User", tier := .boundaryCheck
  , proofName := none, inv := ⟨[], .gt (.lit 0) (.lit 0)⟩ }

def decNowFalseObligation : SchemaLang.SchemaObligation :=
  { decNowFalseItem.obligation with tier := .decidableNow }

/-- The false claim's `decide` IS false — pinned. -/
theorem decNowFalse_decide : decide decNowFalseObligation.decidableClaim = false := rfl

/-- ... and the discharge REFUSES: `none`, loudly. A `decide = false`
    verdict is a refusal, not evidence. -/
theorem decNowFalse_refused : decNowFalseObligation.discharge = none := rfl

/-- Negative control 2: a record with a non-literal default (a
    nonzero-dims tensor field) has NO default row — no claim to
    decide, the backend refuses. -/
def decNowNoRowItem : SchemaLang.InvariantItem :=
  { name := "dec-now-no-row", schemaRef := "User", tier := .boundaryCheck
  , proofName := none
  , inv := ⟨[⟨"t", .tensor [2] .u8⟩], .gt (.lit 1) (.lit 0)⟩ }

def decNowNoRowObligation : SchemaLang.SchemaObligation :=
  { decNowNoRowItem.obligation with tier := .decidableNow }

theorem decNowNoRow_refused : decNowNoRowObligation.discharge = none := rfl

def decidableNowChecks : CheckResult := do
  -- the demo obligation's data: label + tier + evidence shape
  _ ← assertEq "decNow: label" decNowTrueObligation.label "dec-now-true"
  _ ← assertEq "decNow: tier" decNowTrueObligation.tier .decidableNow
  _ ← assertEq "decNow: true claim discharges to .decided true"
    decNowTrueObligation.discharge (some (.decided true))
  -- the evidence's tier IS the obligation's (no mis-wiring)
  _ ← assertEq "decNow: evidence tier matches"
    (decNowTrueObligation.discharge.map (·.tier)) (some .decidableNow)
  -- negative control 1: a FALSE claim refuses, loudly
  _ ← assertEq "decNow: FALSE claim discharges to NONE (loud)"
    decNowFalseObligation.discharge none
  _ ← assertEq "decNow: false claim's decide = false"
    (decide decNowFalseObligation.decidableClaim) false
  -- negative control 2: a default-less record has no claim — refusal
  _ ← assertEq "decNow: default-less record refuses (loud)"
    decNowNoRowObligation.discharge none
  -- non-vacuity: decide DISTINGUISHES the two demo claims
  _ ← assert (decide decNowTrueObligation.decidableClaim !=
      decide decNowFalseObligation.decidableClaim)
    "decide distinguishes true from false claims"
  .ok ()

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

/-! ## Module-docs emitter (DOCSTRING-EXTRACTION lane): lean-internals.md -/

def moduleDocsChecks : CheckResult := do
  let md := SchemaLang.ModuleDocs.internalsPage
  -- the extraction probe (the eval's question), pinned: module docstrings
  -- ARE visible cross-import and the page carries REAL prose
  _ ← assert (md.contains "# Lean internals — module documentation") "title"
  _ ← assert (md.contains "## SchemaLang.Item") "Item section"
  _ ← assert (md.contains "## Items") "Item's `## Items` docstring, verbatim"
  _ ← assert (md.contains "## SchemaLang.Diff") "Diff section"
  _ ← assert (md.contains "## SchemaLang.Validate") "Validate section"
  _ ← assert (md.contains "## SchemaLang.Session") "schema-lang Session section"
  _ ← assert (md.contains "## Machines.Session") "Machines Session section"
  _ ← assert (md.contains "## Machines.Sim") "Machines Sim section"
  -- every manifest entry renders its heading (the manifest and the page
  -- cannot drift — the page is folded FROM the manifest)
  for m in SchemaLang.ModuleDocs.internalsModules do
    _ ← assert (md.contains s!"## {m}") s!"manifest heading {m}"
  -- no gap markers today: every manifest module has docstrings (a gap
  -- marker would mean a plain-comment header landed on the manifest)
  _ ← assert (!md.contains "no module docstrings in the environment")
    "no gap markers over today's manifest"
  -- negative control 1: the EMPTY manifest → intro only, no sections
  let empty := SchemaLang.ModuleDocs.pageOf []
  _ ← assert (empty.contains "# Lean internals") "empty control: intro present"
  _ ← assert (!empty.contains "## ") "empty control: no sections"
  -- negative control 2: a doc-less module → heading + explicit gap
  -- marker (missing documentation is information, not silence)
  let gap := SchemaLang.ModuleDocs.pageOf [(`Foo.Bar, none)]
  _ ← assert (gap.contains "## Foo.Bar") "gap control: heading present"
  _ ← assert (gap.contains "no module docstrings in the environment")
    "gap control: explicit marker"
  -- the emitter: declared path + registered in the registry + covered by
  -- the DERIVED forge-jobs manifest (the golden loop's auto-pickup)
  let files := SchemaLang.ModuleDocs.internalsEmitter.run (SchemaLang.Emit.GenCtx.itemsOnly [])
  _ ← assertEq "internals path" (files.head?.map (·.path)) (some "../../docs/lean-internals.md")
  _ ← assert (SchemaLang.Emit.emitters.any fun e => e.name == "internals-docs")
    "internals emitter registered"
  _ ← assert (SchemaLang.Emit.forgeJobs.any fun (_, _, outs) =>
    outs.contains "../../docs/lean-internals.md")
    "internals output in the byte-tie manifest"
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
  simp only [VExpr.reads, updCompA, updCompB]
  decide⟩

-- the legal composite CONSTRUCTS (the instances assemble the legality)
def compCascade : List (RowVals updUserFields) → List (RowVals updUserFields) :=
  UpdateItem.cascade2 updCompA updCompB

-- the composite's runtime pin: comp-a resets the id, comp-b copies
-- name → email (both guards unconditional)
example :
    (compCascade [invRow 150 "abcd"]).map updRowId = [0] := by
  simp [compCascade, UpdateItem.cascade2, UpdateItem.applyRow, validates,
    evalB, evalU, evalRaw, evalV, updRowId, invRow, updCompA, updCompB, boolToU64]
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

-- THE N-UPDATE ORDER-FREEDOM (W4.3), EXECUTED on the composite pair:
-- the influence-disjoint batch computes the same table in either
-- order — `cascade_applySeq_perm` (= dbsp's `applySeq_perm` read off
-- the `cascadeSystem` instance); the pairwise premise is DECIDED over
-- the derived influence sets (never hand-listed).
example :
    Dbsp.applySeq (cascadeSystem updUserFields)
        [⟨⟨"id", .u64⟩, updCompA⟩, ⟨⟨"email", .string⟩, updCompB⟩]
        [invRow 150 "abcd"]
      = Dbsp.applySeq (cascadeSystem updUserFields)
        [⟨⟨"email", .string⟩, updCompB⟩, ⟨⟨"id", .u64⟩, updCompA⟩]
        [invRow 150 "abcd"] :=
  cascade_applySeq_perm (List.Perm.swap _ _ _) (by
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr
      ⟨fun y hy => (List.not_mem_nil hy).elim, List.Pairwise.nil⟩⟩
    intro y hy
    obtain rfl := List.mem_singleton.mp hy
    intro x hx₁ hx₂
    have h1 : x = "id" := by
      simpa [cascadeInfluence, updCompA, UpdateItem.reads, UpdateItem.writes,
        VExpr.reads, VExpr.colOf] using hx₁
    have h2 : x = "name" ∨ x = "email" := by
      simpa [cascadeInfluence, updCompB, UpdateItem.reads, UpdateItem.writes,
        VExpr.reads, VExpr.colOf] using hx₂
    subst h1
    cases h2 with
    | inl h => exact absurd h (by decide)
    | inr h => exact absurd h (by decide)) _

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

/-! ## Vortex Batch + EnumWire: the retention theorems, executed

Batch.lean's theorems (`project_weaken`/`project_self`, `col_project`,
`u64col_rle_roundtrip`) are compile-time — these checks EXECUTE them on
concrete batches (a theorem that compiles but reads the wrong column
still compiles; the executed pin cannot). The EnumWire half runs the
generated enums' codecs (token + binary) and their PropSpecs with the
MANDATORY negative controls (`runSpecs` at the bottom).
-/
section
open SchemaLang.Vortex

/-- The id column path over `subUserOld` (the head field IS id —
    `.here` by the abbrev's reducibility). -/
def batchColId : ColPath "id" .u64 subUserOld := .here

/-- The name column path (one `there` deep). -/
def batchColName : ColPath "name" .string subUserOld := .there .here

/-- A two-row batch over the OLD user schema. -/
def batchOld : Vortex.Batch subUserOld :=
  [subRowOld 42, subRowOld 7]

/-- The weakened schema: the NEW user schema with a nick field
    PREPENDED (the shape `Subschema.weaken` produces). -/
abbrev subUserWeakened : List Field := ⟨"nick", .string⟩ :: subUserNew

/-- A batch over the weakened schema (the nick column first). -/
def batchWeakened : Vortex.Batch subUserWeakened :=
  [ .cons (.string "n1") (subRowNew 42)
  , .cons (.string "n2") (subRowNew 7) ]

/-- The scalar readings the executed pins compare (the Value GADT has
    no BEq — compare the UNBOXED columns). -/
def batchStrUnbox : Value .string → String | .string s => s

/-- The id column path over the PROJECTED (id-only) schema. -/
def batchColIdSmall : ColPath "id" .u64 [⟨"id", .u64⟩] := .here

def batchChecks : CheckResult := do
  -- column extraction reads the RIGHT values, in batch order
  _ ← assertEq "col id"
    ((Batch.col batchColId batchOld).map u64Unbox) [42, 7]
  _ ← assertEq "col name"
    ((Batch.col batchColName batchOld).map batchStrUnbox) ["Evan", "Evan"]
  -- project_self, executed: the reflexive projection IS the identity
  _ ← assertEq "project_self: id column survives"
    (Batch.col batchColId
      (Batch.project batchOld (Subschema.reflexive subUserOld)) |>.map u64Unbox)
    (Batch.col batchColId batchOld |>.map u64Unbox)
  -- col_project, executed: reading a column of the projected batch =
  -- reading the widened path off the original
  _ ← assertEq "col_project: id through the id-only projection"
    (Batch.col batchColIdSmall (Batch.project batchOld subId) |>.map u64Unbox)
    (Batch.col (subId.widen batchColIdSmall) batchOld |>.map u64Unbox)
  -- weaken, executed: prepending the nick field to the big schema AND
  -- its rows leaves the projection's reads unchanged (the theorem's
  -- per-row shape, executed over a two-row batch)
  let projTails := [subRowNew 42, subRowNew 7].map
    (fun r => u64Unbox (batchColId.get (r.project subFullEmbed)))
  _ ← assertEq "project_weaken: nick prepended, reads unchanged"
    (Batch.col batchColId
      (Batch.project batchWeakened
        (subFullEmbed.weaken (f := ⟨"nick", .string⟩))) |>.map u64Unbox)
    projTails
  -- u64col + the RLE tie, executed: the batch's u64 column
  -- RLE-round-trips EXACTLY (the retention theorem, consumed)
  _ ← assertEq "u64col" (Batch.u64col batchColId batchOld) [42, 7]
  _ ← assertEq "u64col rle roundtrip"
    (rleDecode (rleEncode (Batch.u64col batchColId batchOld)))
    (Batch.u64col batchColId batchOld)
  -- the run-heavy shape (RLE's actual use): a constant column
  _ ← assertEq "u64col rle constant column"
    (rleDecode (rleEncode (Batch.u64col batchColId
      [subRowOld 5, subRowOld 5, subRowOld 5])))
    [5, 5, 5]
  -- the other exact encodings' laws, executed on batch-shaped columns
  _ ← assertEq "const encoding" (constRead (constEncode [5, 5, 5])) [5, 5, 5]
  _ ← assertEq "FoR encoding" (forRead (forEncode [100, 103, 99])) [100, 103, 99]
  _ ← assertEq "dict encoding" (dictRead (dictEncode ["b", "a", "b"]))
    ["b", "a", "b"]
  .ok ()

def enumWireChecks : CheckResult := do
  -- the token spelling (the ONE spelling the snapshot codec consumes)
  _ ← assertEq "toToken" (NullSem.toToken .propagate) "propagate"
  _ ← assert (Delivery.ofToken? "stream" == some .stream) "ofToken?"
  _ ← assert (NullSem.ofToken? "nonsense" |>.isNone) "ofToken? reject"
  -- the PROVED binary round trip, executed (incl. the append form)
  _ ← assert (Delivery.decode? (Delivery.encode .once) == some (.once, []))
      "decode_encode"
  _ ← assert (NullSem.decode? (NullSem.encode .strict ++ [9]) == some (.strict, [9]))
      "decode_encode_append"
  -- the sabotage control's predicate, executed: tag+1 NEVER decodes
  -- back (the negative controls in `wirePropSpec` run in `runSpecs`)
  _ ← assertEq "sabotage caught (strict)" (NullSem.wireSabotage .strict) false
  _ ← assertEq "sabotage caught (custom)" (NullSem.wireSabotage .custom) false
  _ ← assertEq "sabotage caught (once)" (Delivery.wireSabotage .once) false
  _ ← assertEq "sabotage caught (stream)" (Delivery.wireSabotage .stream) false
  _ ← assertEq "sabotage caught (determinism)"
    (Determinism.wireSabotage .volatile) false
  .ok ()

end

/-! ## W7.14 — `deriving WireCodec` (SchemaLang.Meta.WireCodec)

Per-structure wire codec, generated: the `WireCodec` instance (encoder/
decoder over the Codec.lean combinators + the append-form law PROVED —
the class-law simp rule covers every field shape carrying an instance),
the EnumWire-parity wrappers, and the `RoundTripSpec` assembly (the
review-2026-09-16 F2/F3 graduation — the kit `PartialIso` gets its codec
consumer via `WireCodec.toPartialIso`, and the sweep + mandatory
byte-sabotage control ride the spec's PropSpec bridge in `runSpecs`
below). The fixture spans the codec-supported shapes (UInt64/Bool/Nat
atoms, Option, List) plus a NESTED struct (composition through the inner
instance). The refusal surface is pinned by `#guard_msgs`: an
unsupported field type is an elaboration error naming the field — never
a sorry, never a silent skip. -/

/-- Fixture across the codec-supported field shapes. -/
structure WireCodecFixture where
  id : UInt64
  active : Bool
  nick : Option String
  tags : List String
  score : Nat
deriving WireCodec

/-- Composition fixture: a field of another `deriving WireCodec`
    structure (the inner instance carries the wire). -/
structure WireCodecOuter where
  inner : WireCodecFixture
  n : Nat
deriving WireCodec

/-- The generated instance's append-form law, cited. -/
example (v : WireCodecFixture) (rest : List UInt8) :
    WireCodec.dec? (WireCodec.enc v ++ rest) = some (v, rest) :=
  WireCodec.decode_encode_append v rest

/-- The plain round trip through the kit PartialIso law shape, cited
    (F2: `WireCodec.toPartialIso` is PartialIso's codec consumer). -/
example (v : WireCodecOuter) :
    WireCodec.decode WireCodecOuter (WireCodec.enc v) = some v :=
  WireCodec.decode_encode _ v

/- The refusal: a field with no `WireCodec` instance is an elaboration
error NAMING the offending field (the pinned behavior — the wire family
widens in Codec.lean, not per call site). -/
/--
error: deriving WireCodec: field `price : Float` of `BadWireFixture` has no `SchemaLang.WireCodec` instance — codec-supported field types: Bool / UInt8 / Nat / UInt64 / String, Option and List over them, and other `deriving WireCodec` structures (the wire family widens in Codec.lean, not per call site)
-/
#guard_msgs in
structure BadWireFixture where
  price : Float
deriving WireCodec

def wireCodecChecks : CheckResult := do
  let v : WireCodecFixture := ⟨42, true, some "ada", ["x", "y"], 7⟩
  -- the round trip, executed (plain + append form)
  _ ← assert (WireCodecFixture.decode? (WireCodecFixture.encode v) == some (v, []))
    "decode_encode (unit)"
  _ ← assert (WireCodecFixture.decode? (WireCodecFixture.encode v ++ [9]) == some (v, [9]))
    "decode_encode_append (unit)"
  -- the none/nil corners
  let corners : WireCodecFixture := ⟨0, false, none, [], 0⟩
  _ ← assert (WireCodecFixture.decode (WireCodecFixture.encode corners) == some corners)
    "none/nil corners round trip"
  -- nested composition, executed (the outer codec rides the inner instance)
  let o : WireCodecOuter := ⟨⟨1, false, none, [], 0⟩, 3⟩
  _ ← assert (WireCodecOuter.decode (WireCodecOuter.encode o) == some o)
    "nested struct round trip"
  -- the spec assembly IS a RoundTripSpec over the kit PartialIso (F3):
  -- the iso's law executes through the spec's own fields
  _ ← assertEq "spec name" WireCodecFixture.roundTripSpec.name "WireCodecFixture"
  _ ← assert (WireCodecFixture.roundTripSpec.iso.decode
      (WireCodecFixture.roundTripSpec.iso.encode v) == some v)
    "PartialIso law, executed through the spec"
  .ok ()

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
@[nolint linter.guestlang.dupDefBodies "deliberate mirror: the hand spelling vs the [inv| ...] spelling — the alpha-equality IS the test (the rfl pin below each pair)"]
def userCompleteCheckDsl : VExpr dslUserSchema .bool :=
  [inv| id > 0 && strlen(name) > 3]

/-- The hand-spelled SAME tree (the pin's oracle). -/
@[nolint linter.guestlang.dupDefBodies "deliberate mirror: the hand spelling vs the [inv| ...] spelling — the alpha-equality IS the test (the rfl pin below each pair)"]
def userCompleteCheckHand : VExpr dslUserSchema .bool :=
  VExpr.and
    (VExpr.gt (VExpr.colOf "id") (VExpr.lit 0))
    (VExpr.gt (VExpr.strlen (VExpr.colOf "name")) (VExpr.lit 3))

-- COMPILE = THE SAME VEXPR: the syntax elaborates to exactly the hand
-- constructor tree (definitional, not just eval-equal).
example : userCompleteCheckDsl = userCompleteCheckHand := rfl

@[nolint linter.guestlang.dupDefBodies "deliberate mirror: the hand spelling vs the [inv| ...] spelling — the alpha-equality IS the test (the rfl pin below each pair)"]
def dslPositive : VExpr dslUserSchema .bool := [inv| id > 0]
@[nolint linter.guestlang.dupDefBodies "deliberate mirror: the hand spelling vs the [inv| ...] spelling — the alpha-equality IS the test (the rfl pin below each pair)"]
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
@[nolint linter.guestlang.dupDefBodies "deliberate mirror: the hand spelling vs the [inv| ...] spelling — the alpha-equality IS the test (the rfl pin below each pair)"]
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

/-! ## W6.11 — check-eliminates-error (SchemaLang/Error.lean)

Each Error.lean theorem is CITED against a concrete fixture; drift on
either side fails this build. `by decide`/`rfl` negative controls pin
the failure surface the checks eliminate, and the two documented
INSUFFICIENCY witnesses pin what the checks do NOT cover (reported
per the order; the checkers are deliberately not patched). -/

/-- A total semantics for the lowering fixtures (every ref resolves —
    the dtype choice is irrelevant to the guard). -/
def elimSem : Vortex.VortexSem := fun _ => some (.bool .nonNullable)

-- Lane 1 (Layout): the bounds check eliminates the coordinate parse's none
example : (Coords.ofList? [2, 3] [1, 2]).isSome = true :=
  Option.isSome_iff_exists.mpr (Coords.ofList?_isSome_of_inB [2, 3] [1, 2] (by decide))
example : flatIdx [2, 3] [1, 2] = some 5 :=
  flatIdx_eq_some_of_inB (by decide)
-- negative control: out of bounds, the parse fails (the check is exact)
example : (Coords.ofList? [2, 3] [1, 3]).isNone = true := by decide

-- Lane 2 (Vortex lowering): the exact guard is the banAsync / noResult /
-- refs-resolve triple.
example : (Vortex.Ty.lower elimSem .nonNullable (.list (.ty "x"))).isSome = true :=
  (Vortex.Ty.lower_isSome_iff _ _ _).mpr ⟨by decide, by decide, fun n hn => by
    rw [show Ty.tyRefs (.list (.ty "x")) = ["x"] from rfl, List.mem_singleton] at hn
    subst n; rfl⟩
-- INSUFFICIENCY witness: `banAsync` ALONE does not eliminate the
-- lowering's `none` — the check passes on `.result`, the deliberate
-- refusal arm still fires. Reported, not patched.
example : Ty.banAsync (.result .u64 .string) = true ∧
    (Vortex.Ty.lower elimSem .nonNullable (.result .u64 .string)).isNone = true :=
  ⟨rfl, rfl⟩
-- negative control: an unresolvable ref fails even async-free/result-free
example : (Vortex.Ty.lower (fun _ => none) .nonNullable (.ty "ghost")).isNone = true := rfl

-- Lane 3 (migration): the exact checker, both directions cited
example : (Subschema.ofMem? [⟨"id", .u64⟩, ⟨"n", .string⟩]
      [⟨"id", .u64⟩]).isSome = true :=
  Subschema.ofMem?_isSome_iff_forall_mem.mpr (fun f hf => by
    rw [List.mem_singleton] at hf; subst f; exact List.mem_cons_self)
-- negative control: a RETYPED old field is breaking (name match is not enough)
example : (Subschema.ofMem? [⟨"id", .string⟩] [⟨"id", .u64⟩]).isNone = true := by decide
-- the CheckedProp consumption (the canon row's first consumer): the
-- executable check agrees with the Prop on a fixture, completeness loud
example : subschemaChecked.check ([⟨"id", .u64⟩], [⟨"id", .u64⟩, ⟨"n", .string⟩]) = true := rfl
example : subschemaChecked.isComplete = true := rfl

-- Lane 4 (delta): the first-field key convention
example : (Item.changeTy (.record "r" [⟨"id", .u64⟩])).isSome = true :=
  Item.changeTy_isSome_of_fields_ne_nil (by simp)
example : (Item.changeTy (.record "empty" [])).isNone = true := rfl  -- negative control

-- Lane 5 (snapshot close-out): a `ret`-bearing func always closes
example : (Snapshot.Open.close (.func "f" [] (some .u64) none)).isOk = true :=
  Snapshot.Open.close_isOk_of_ret
example : (Snapshot.Open.close (.func "f" [] none none)).isOk = false := rfl  -- negative control

-- Lane 6 (variant access): under unique case names the tag check is exact
example : (CasePath.payloadOf
      (CasePath.here : CasePath "a" .u64 [("a", some .u64), ("b", some .bool)])
      (VRow.here (.u64 7))).isSome = true :=
  CasePath.payloadOf_isSome_of_isName _ (by decide) _ (by decide)
-- INSUFFICIENCY witness: with DUPLICATE case names the check passes but
-- the read misses (the deeper `a` fired; the first-`a` path finds none).
-- Reported, not patched.
example :
    let cs : List VariantCase := [("a", some .u64), ("a", some .u64)]
    let path : CasePath "a" .u64 cs := .here
    let row : VRow cs := .there (.here (.u64 7))
    row.isName "a" = true ∧ (path.payloadOf row).isNone = true :=
  ⟨rfl, rfl⟩

-- Lane 7: the Bool gate IS the relation (demo fixture, via the bridge)
example : universeWellFormed demoItems = true :=
  universeWellFormed_iff.mpr demoItems_wellFormed

/-! ## W9.1 — the witness codec: RoundTripSpec's FIRST PRODUCTION consumer

`SchemaLang.Witness`'s codec assembled ONCE as a `RoundTripSpec` (the
review-2026-09-16 F3 graduation — the spec's `iso` field gets its first
real inhabitant: `SchemaLang.Witness.witnessIso`). The sweep rides the
spec's PropSpec bridge (`decode ∘ encode` over generated witnesses) with
the MANDATORY byte-sabotage control: the default first-byte increment
corrupts the envelope VERSION byte (version 1 → 2), which
`decEnvelope?` rejects — a decoder that accepted it would fail its own
gate, and a vacuous control fails the run. The golden byte-tie over
fixed samples pins the WIRE FORMAT itself: a reordered `WProp`/`WProof`
ctor changes the bytes and fails the tie (the EnumWire wire-breaking
rule, enforced here for a hand-written wire).

Field resolution (design §2.1) is pinned both ways: a known field
resolves, a misspelled or wrongly-typed field rejects with `none`. -/

namespace WitnessSweep

open Plausible SchemaLang.Witness

/-- The suite's fixed envelope pair (W9.4 derives per-record pairs from
    the schema fingerprints; the suite pins ONE — the golden ties the
    format). Version 1 keeps byte 0 a single byte the default sabotage
    corrupts into a version mismatch. -/
def version : Nat := 1
def fingerprint : Nat := 9001

/-- Column-name supply for the generators. -/
def nameSupply : List String := ["id", "amount", "note"]

/-- Pick a name from the supply. -/
def pickWName : Gen String := do
  let n ← Gen.chooseNat
  pure (nameSupply[n % nameSupply.length]?.getD "id")

/-- `WU64` leaves: literals, column refs, strlen refs. -/
def genWU64 : Gen WU64 :=
  Gen.oneOfWithDefault (pure (.lit 0))
    [ do pure (.lit ((← Gen.chooseNat) % 1000).toUInt64)
    , do pure (.col (← pickWName))
    , do pure (.strlenCol (← pickWName)) ]

/-- The boolean fragment, depth-bounded by fuel. -/
def genWBoolExpr : Nat → Gen WBoolExpr
  | 0 => do pure (.gt (← genWU64) (← genWU64))
  | fuel + 1 => do
      let branch ← Gen.chooseNat
      match branch % 4 with
      | 0 => pure (.gt (← genWU64) (← genWU64))
      | 1 => pure (.eq (← genWU64) (← genWU64))
      | 2 => pure (.and (← genWBoolExpr fuel) (← genWBoolExpr fuel))
      | _ => pure (.not (← genWBoolExpr fuel))

/-- Claims across all three ctors (v1 scope: valid / eqU / chain). -/
def genWProp (fuel : Nat) : Gen WProp := do
  let branch ← Gen.chooseNat
  match branch % 3 with
  | 0 => pure (.valid (← genWBoolExpr fuel))
  | 1 => pure (.eqU (← genWU64) (← genWU64))
  | _ => pure (.chain
      (← genShortList (do pure ⟨(← Gen.chooseNat) % 16⟩) 3)
      (← genWBoolExpr fuel))

/-- Proof terms, depth-bounded by fuel. -/
def genWProof : Nat → Gen WProof
  | 0 => pure .byValidEval
  | fuel + 1 => do
      let branch ← Gen.chooseNat
      match branch % 3 with
      | 0 => pure (.byEval ((← Gen.chooseNat) % 1000).toUInt64)
      | 1 => pure .byValidEval
      | _ => pure (.steps (← genShortList (genWProof fuel) 2))

/-- Whole witnesses. -/
def genWitness : Gen Witness := do
  let n ← Gen.chooseNat
  let label := (["inv-a", "mig-v1-v2", "step-ok"][n % 3]?.getD "inv-a")
  pure ⟨label, ← genWProp 2, ← genWProof 2, (← Gen.chooseNat) % 512⟩

instance : Shrinkable WU64 := {}
instance : Shrinkable WBoolExpr := {}
instance : Shrinkable WStep := {}
instance : Shrinkable WProp := {}
instance : Shrinkable WProof := {}
instance : Shrinkable Witness := {}

instance : Arbitrary WU64 where arbitrary := genWU64
instance : Arbitrary WProp where arbitrary := Gen.sized genWProp
instance : Arbitrary Witness where arbitrary := genWitness

/-- THE SUITE (the F3 graduation): the witness codec's law stated once
    as a RoundTripSpec — sweep + default byte-sabotage control +
    golden byte-tie at `goldens/witness.golden`. -/
def witnessSpec : CodegenCore.RoundTripSpec Witness where
  name := "witness"
  iso := SchemaLang.Witness.witnessIso version fingerprint
  samples :=
    [ ⟨"inv-a", .valid (.gt (.col "amount") (.lit 0)), .byValidEval, 64⟩
    , ⟨"mig-v1-v2", .chain [⟨0⟩, ⟨1⟩] (.not (.eq (.strlenCol "note") (.lit 5))),
        .steps [.byValidEval, .byValidEval], 128⟩
    , ⟨"eq-pin", .eqU (.lit 7) (.lit 7), .byEval 7, 8⟩ ]
  goldenDir := some "goldens"

/-- Deterministic pins: the theorems' objects EXECUTED, the envelope's
    wrong-version rejection, truncation/trailing-garbage rejection, and
    the field-resolution verdicts (design §2.1) both ways. -/
def witnessChecks : CheckResult := do
  let w : Witness := ⟨"inv-a", .valid (.gt (.col "amount") (.lit 0)), .byValidEval, 64⟩
  -- the round-trip theorem, executed
  _ ← assert (decWitness? version (encWitness version fingerprint w) == some w)
    "decWitness? ∘ encWitness = some (theorem, executed)"
  -- the envelope rejects a version mismatch before touching the payload
  _ ← assert (decWitness? 2 (encWitness version fingerprint w)).isNone
    "wrong version rejected (decEnvelope?_wrong_version, executed)"
  -- truncation MID-PAYLOAD rejects (the length prefix overruns; a
  -- 3-byte truncation is NOT a rejection case — it is a valid shorter
  -- envelope for a degenerate witness: decVarNat is total on empty
  -- input, Codec.lean's documented discipline)
  let bs := encWitness version fingerprint w
  _ ← assert (decWitness? version (bs.take (bs.length - 1))).isNone
    "truncated witness rejected (payload length-prefix overrun)"
  -- trailing garbage rejects (the payload's no-trailing rule)
  _ ← assert (decWitness? version (encWitness version fingerprint w ++ [0])).isNone
    "trailing garbage rejected"
  -- field resolution: the known field resolves
  let fields : List Field := [⟨"amount", .u64⟩, ⟨"note", .string⟩]
  _ ← assert (decWitnessFor? fields version (encWitness version fingerprint w)).isSome
    "known field resolves"
  -- a misspelled field is `none`, loud
  let bad : Witness := ⟨"inv-b", .valid (.gt (.col "amoutn") (.lit 0)), .byValidEval, 64⟩
  _ ← assert (decWitnessFor? fields version (encWitness version fingerprint bad)).isNone
    "misspelled field rejected (design §2.1)"
  -- a wrongly-typed field (a string column at a u64 position) rejects
  let badTy : Witness := ⟨"inv-c", .valid (.gt (.col "note") (.lit 0)), .byValidEval, 64⟩
  _ ← assert (decWitnessFor? fields version (encWitness version fingerprint badTy)).isNone
    "wrongly-typed field rejected"
  .ok ()

end WitnessSweep

/-! ## W9.2 — the guest witness checker: sound, fuel-bounded, refusal-total

`SchemaLang.WitnessCheck`'s pins: positive witnesses (hand-built AND via
W9.1's codec round trip — encode, decode+resolve, then check), the
negative controls (tampered proof term / wrong claim-proof pairing /
false claim / misspelled field / insufficient fuel / out-of-range
offset / length mismatch / wrong per-step proof shape — each REFUSED,
pinned), the soundness theorem APPLIED (an accepting check transports
to `WHolds`), and the design §2.4 grounding executed end to end:
checker → `WHolds` → the compiled `validates` verdict. -/

namespace WitnessCheckSweep

open SchemaLang.Witness SchemaLang.WitnessCheck

/-- The fixture record: `amount : u64`, `note : string`. -/
def wcFields : List Field := [⟨"amount", .u64⟩, ⟨"note", .string⟩]

/-- The certified row: `amount = 7`, `note = "hello"`. -/
def wcRow : RowVals wcFields := .cons (.u64 7) (.cons (.string "hello") .nil)

/-- The chain lane's guest-held log segment (offsets 0 and 1). -/
def wcLog : List (RowVals wcFields) :=
  [.cons (.u64 1) (.cons (.string "hi") .nil),
   .cons (.u64 2) (.cons (.string "yo") .nil)]

/-- The chain fixture's invariant: `strlen note ≠ 4` (holds of the row
    and both log rows). -/
def wcChainInv : WBoolExpr := .not (.eq (.strlenCol "note") (.lit 4))

-- positive: `valid` + `byValidEval` accepts (amount 7 > 0)
example : checkWitness 4 (.valid (.gt (.col "amount") (.lit 0))) .byValidEval
    wcFields wcRow [] = true := by decide

-- positive: `eqU` + `byEval` (strlen "hello" = 5, both sides)
example : checkWitness 4 (.eqU (.strlenCol "note") (.lit 5)) (.byEval 5)
    wcFields wcRow [] = true := by decide

-- positive: the migration chain — init holds, both steps certify
example : checkWitness 3 (.chain [⟨0⟩, ⟨1⟩] wcChainInv)
    (.steps [.byValidEval, .byValidEval]) wcFields wcRow wcLog = true := by decide

-- fuel monotone, executed: the same chain accepts at a larger cap
example : checkWitness 64 (.chain [⟨0⟩, ⟨1⟩] wcChainInv)
    (.steps [.byValidEval, .byValidEval]) wcFields wcRow wcLog = true := by decide

-- NEGATIVE CONTROL: insufficient fuel REFUSES (2 steps need fuel ≥ 3)
example : checkWitness 2 (.chain [⟨0⟩, ⟨1⟩] wcChainInv)
    (.steps [.byValidEval, .byValidEval]) wcFields wcRow wcLog = false := by decide

-- NEGATIVE CONTROL: fuel 0 refuses even a true claim (exhaustion = refusal)
example : checkWitness 0 (.valid (.gt (.col "amount") (.lit 0))) .byValidEval
    wcFields wcRow [] = false := by decide

-- NEGATIVE CONTROL: tampered proof term (wrong expected literal)
example : checkWitness 4 (.eqU (.strlenCol "note") (.lit 5)) (.byEval 6)
    wcFields wcRow [] = false := by decide

-- NEGATIVE CONTROL: wrong claim/proof pairing, both directions
example : checkWitness 4 (.valid (.gt (.col "amount") (.lit 0))) (.byEval 1)
    wcFields wcRow [] = false := by decide
example : checkWitness 4 (.eqU (.lit 1) (.lit 1)) .byValidEval
    wcFields wcRow [] = false := by decide

-- NEGATIVE CONTROL: a FALSE claim's proof does not check (amount 7 ≯ 9)
example : checkWitness 4 (.valid (.gt (.col "amount") (.lit 9))) .byValidEval
    wcFields wcRow [] = false := by decide

-- NEGATIVE CONTROL: a misspelled field evaluates to none → refused
example : checkWitness 4 (.valid (.gt (.col "amoutn") (.lit 0))) .byValidEval
    wcFields wcRow [] = false := by decide

-- NEGATIVE CONTROL: chain step offset out of range (the log has 2 rows)
example : checkWitness 4 (.chain [⟨5⟩] wcChainInv)
    (.steps [.byValidEval]) wcFields wcRow wcLog = false := by decide

-- NEGATIVE CONTROL: proof/step length mismatch
example : checkWitness 4 (.chain [⟨0⟩, ⟨1⟩] wcChainInv)
    (.steps [.byValidEval]) wcFields wcRow wcLog = false := by decide

-- NEGATIVE CONTROL: tampered per-step proof shape (v1 steps are
-- `byValidEval` exactly — the header's deviation 3)
example : checkWitness 4 (.chain [⟨0⟩] wcChainInv)
    (.steps [.steps []]) wcFields wcRow wcLog = false := by decide

-- SOUNDNESS, APPLIED: accepting checks transport to the denotation
example : WHolds (.valid (.gt (.col "amount") (.lit 5))) wcRow [] :=
  checkWitness_sound 4 (.valid (.gt (.col "amount") (.lit 5))) .byValidEval wcRow []
    (by decide)

example : WHolds (.chain [⟨0⟩, ⟨1⟩] wcChainInv) wcRow wcLog :=
  checkWitness_sound 3 (.chain [⟨0⟩, ⟨1⟩] wcChainInv)
    (.steps [.byValidEval, .byValidEval]) wcRow wcLog (by decide)

/-- The resolution evidence: `amount` is the head field, `note` one
    deeper (the `ColPath` data the mirror relation cites). -/
def wcAmountPath : ColPath "amount" .u64 wcFields := .here

def wcNotePath : ColPath "note" .string wcFields := .there .here

/-- The mirror for the fixture invariant `amount > 5`. -/
theorem wcMirror : WBMirror (.gt (.col "amount") (.lit 5))
    (VExpr.gt (VExpr.col "amount" wcAmountPath) (VExpr.lit 5)) :=
  WBMirror.gt (WUMirror.col "amount" wcAmountPath) (WUMirror.lit 5)

/-- The mirror for the chain invariant `strlen note ≠ 4`. -/
theorem wcChainMirror : WBMirror wcChainInv
    (VExpr.not (VExpr.eq (VExpr.strlen (VExpr.col "note" wcNotePath)) (VExpr.lit 4))) :=
  WBMirror.not (WBMirror.eq (WUMirror.strlenCol "note" wcNotePath) (WUMirror.lit 4))

-- THE GROUNDING (design §2.4), executed end to end: checker → WHolds →
-- the compiled `validates` verdict on the VExpr the claim mirrors
example : validates (VExpr.gt (VExpr.col "amount" wcAmountPath) (VExpr.lit 5)) wcRow = true :=
  (WHolds.valid_iff_validates wcMirror (by decide) wcRow []).mp
    (checkWitness_sound 4 (.valid (.gt (.col "amount") (.lit 5))) .byValidEval wcRow []
      (by decide))

-- the chain grounding: the compiled invariant certified at the initial
-- row AND at every referenced log row
example : validates
      (VExpr.not (VExpr.eq (VExpr.strlen (VExpr.col "note" wcNotePath)) (VExpr.lit 4)))
      wcRow = true ∧
    ∀ s ∈ ([⟨0⟩, ⟨1⟩] : List WStep), ∃ r, wcLog[s.offset]? = some r ∧ validates
      (VExpr.not (VExpr.eq (VExpr.strlen (VExpr.col "note" wcNotePath)) (VExpr.lit 4)))
      r = true :=
  WHolds.chain_validates wcChainMirror (by decide)
    (checkWitness_sound 3 (.chain [⟨0⟩, ⟨1⟩] wcChainInv)
      (.steps [.byValidEval, .byValidEval]) wcRow wcLog (by decide))

-- the CheckedProp pack: sound, completeness LOUD-missing (pinned)
example : witnessChecked.isComplete = false := witnessChecked_incomplete

example : WHolds (.valid (.gt (.col "amount") (.lit 5))) wcRow [] :=
  witnessChecked.sound ⟨⟨wcFields, wcRow, []⟩, .valid (.gt (.col "amount") (.lit 5)),
    .byValidEval, 64⟩ (by decide)

/-- The positive witness THROUGH W9.1's codec: encode → decode+resolve
    → check (the §4 consumer flow's guest half, minus the transport). -/
def wcWitness : Witness :=
  ⟨"w92-inv", .valid (.gt (.col "amount") (.lit 0)), .byValidEval, 64⟩

-- the codec round trip, theorem-level (no kernel evaluation — the
-- kernel does not reduce the u64 codec's `Fin.Internal` path; the
-- EXECUTED pin is the runtime assert below, W9.1's own pattern)
example : decWitness? 7 (encWitness 7 99 wcWitness) = some wcWitness :=
  decWitness?_encWitness 7 99 wcWitness

example : checkWitnessArtifact wcWitness ⟨wcFields, wcRow, []⟩ = true := by decide

/-- The executed pin: the full §4 guest flow over the wire bytes —
    encode, decode+resolve, check — run by the test exe (the WitnessSweep
    discipline: codec behavior is pinned by runtime asserts). -/
def witnessCheckChecks : CheckResult := do
  let w := wcWitness
  let ok := match decWitnessFor? wcFields 7 (encWitness 7 99 w) with
    | some w' => w' == w && checkWitnessArtifact w' ⟨wcFields, wcRow, []⟩
    | none => false
  _ ← assert ok "witness: encode → decWitnessFor? → checkWitnessArtifact accepts"
  .ok ()

-- artifact-level soundness, applied to the codec round trip's witness
example : WHolds (.valid (.gt (.col "amount") (.lit 0))) wcRow [] :=
  checkWitnessArtifact_sound wcWitness ⟨wcFields, wcRow, []⟩ (by decide)

end WitnessCheckSweep

/-! ## W9.3 — the fifth obligation tier: guestVerified discharges

`SchemaObligation.discharge`'s guestVerified arm (design-guest-verified
§3): the host PROVIDES a `WitnessRef` (certificate + decoded context +
the artifact name W9.4 will emit it under); the arm fires
`.guestWitness` evidence ONLY when the certificate's label IS the
obligation's AND W9.2's checker accepts the certificate at its own
shipped fuel. The end-to-end miniature: a hand-tiered guestVerified
obligation + a hand-built valid witness → discharge FIRES, and
`discharge_guestVerified_sound` transports the verdict to `WHolds`
(then through the §2.4 grounding to the compiled `validates` verdict).
Negative controls: a tampered claim, exhaustion fuel (owner decision 2
— refusal, NO retry: the same obligation fires at the shipped fuel and
refuses at fuel 0), a label mismatch, and no witness provided (the
armed-but-unfired gap) — all `none`, LOUD. -/

namespace GuestVerifiedSweep

open SchemaLang.Witness SchemaLang.WitnessCheck

/-- The fixture item: `amount > 0` over the W9.2 sweep's record — the
    invariant the witness certifies (the payload the tier is assigned
    to). -/
def gvItem : SchemaLang.InvariantItem :=
  { name := "gv-amount-positive", schemaRef := "User", tier := .boundaryCheck
  , proofName := none
  , inv := ⟨WitnessCheckSweep.wcFields,
      VExpr.gt (VExpr.col "amount" WitnessCheckSweep.wcAmountPath) (VExpr.lit 0)⟩ }

/-- The hand-tiered guestVerified obligation (no invariant-lane rung
    computes the fifth tier — registration is W9.4; the tier is a
    backend ASSIGNMENT). -/
def gvObligation : SchemaLang.SchemaObligation :=
  { gvItem.obligation with tier := .guestVerified }

/-- A VALID witness for the obligation: the claim mirrors the
    invariant (`amount > 0`), the certified row (amount = 7) satisfies
    it, the shipped fuel (64) dwarfs the 1 the checker consumes. -/
def gvRef : SchemaLang.SchemaObligation.WitnessRef :=
  { artifact := "witnesses/user-gv-amount-positive.wtn"
  , witness := ⟨"gv-amount-positive", .valid (.gt (.col "amount") (.lit 0)), .byValidEval, 64⟩
  , ctx := ⟨WitnessCheckSweep.wcFields, WitnessCheckSweep.wcRow, []⟩ }

-- END TO END: obligation at tier guestVerified + a hand-built valid
-- witness → discharge FIRES, the evidence naming the artifact + the
-- certified label
example : gvObligation.discharge (some gvRef) =
    some (.guestWitness "witnesses/user-gv-amount-positive.wtn" "gv-amount-positive") := by decide

-- the evidence's tier IS the obligation's (the kit's mis-wire check,
-- discharged for this lane)
example : (gvObligation.discharge (some gvRef)).map (·.tier) =
    some .guestVerified := by decide

-- SOUNDNESS CITED: the fired discharge IS the claim's denotation
example : WHolds (.valid (.gt (.col "amount") (.lit 0))) WitnessCheckSweep.wcRow [] :=
  gvObligation.discharge_guestVerified_sound gvRef rfl (by decide)

/-- The mirror for the fixture claim `amount > 0`. -/
theorem gvMirror : WBMirror (.gt (.col "amount") (.lit 0))
    (VExpr.gt (VExpr.col "amount" WitnessCheckSweep.wcAmountPath) (VExpr.lit 0)) :=
  WBMirror.gt (WUMirror.col "amount" WitnessCheckSweep.wcAmountPath) (WUMirror.lit 0)

-- ... and through the §2.4 grounding: the discharged witness certifies
-- the COMPILED `validates` verdict on the VExpr the claim mirrors
example : validates (VExpr.gt (VExpr.col "amount" WitnessCheckSweep.wcAmountPath) (VExpr.lit 0))
    WitnessCheckSweep.wcRow = true :=
  (WHolds.valid_iff_validates gvMirror (by decide) WitnessCheckSweep.wcRow []).mp
    (gvObligation.discharge_guestVerified_sound gvRef rfl (by decide))

-- the completeness disjunct, EXERCISED: the witness-backed row is a
-- computed-tier discharge
example : (gvObligation.discharge (some gvRef)).isSome = true :=
  SchemaLang.SchemaObligation.discharge_isSome_of_computed gvObligation (some gvRef)
    (.inr ⟨rfl, gvRef, rfl, rfl, by decide⟩)

/-- NEGATIVE CONTROL fixture: the tampered certificate — the claim
    strengthened to `amount > 9`, FALSE on the row (amount = 7). -/
def gvTamperedRef : SchemaLang.SchemaObligation.WitnessRef :=
  { gvRef with witness :=
      ⟨"gv-amount-positive", .valid (.gt (.col "amount") (.lit 9)), .byValidEval, 64⟩ }

/-- NEGATIVE CONTROL fixture: exhaustion — the same certificate with
    fuel 0 (owner decision 2: exhaustion = refusal, NO retry). -/
def gvFuelZeroRef : SchemaLang.SchemaObligation.WitnessRef :=
  { gvRef with witness :=
      ⟨"gv-amount-positive", .valid (.gt (.col "amount") (.lit 0)), .byValidEval, 0⟩ }

/-- NEGATIVE CONTROL fixture: a certificate for ANOTHER obligation
    (label mismatch — the mis-wire check as data). -/
def gvWrongLabelRef : SchemaLang.SchemaObligation.WitnessRef :=
  { gvRef with witness :=
      ⟨"gv-other", .valid (.gt (.col "amount") (.lit 0)), .byValidEval, 64⟩ }

-- the tampered claim REFUSES (the checker's verdict, not fabricated evidence)
example : gvObligation.discharge (some gvTamperedRef) = none := by decide

-- DECISION 2 PINNED: fuel exhaustion refuses — the SAME obligation +
-- claim that fires at fuel 64 refuses at fuel 0, and nothing retries
example : gvObligation.discharge (some gvFuelZeroRef) = none := by decide

-- the label mismatch REFUSES (a certificate for another obligation
-- cannot discharge this one)
example : gvObligation.discharge (some gvWrongLabelRef) = none := by decide

-- NO witness provided: the armed-but-unfired gap, `none`, LOUD
example : gvObligation.discharge = none := by decide

-- non-vacuity: acceptance DISTINGUISHES the valid certificate from
-- the exhausted one
def guestVerifiedChecks : CheckResult := do
  _ ← assertEq "gv: valid witness FIRES" (gvObligation.discharge (some gvRef))
    (some (.guestWitness "witnesses/user-gv-amount-positive.wtn" "gv-amount-positive"))
  _ ← assertEq "gv: evidence tier is guestVerified"
    ((gvObligation.discharge (some gvRef)).map (·.tier)) (some .guestVerified)
  _ ← assertEq "gv: tampered claim REFUSED (loud)"
    (gvObligation.discharge (some gvTamperedRef)) none
  _ ← assertEq "gv: fuel 0 REFUSED — exhaustion = refusal, no retry"
    (gvObligation.discharge (some gvFuelZeroRef)) none
  _ ← assertEq "gv: label mismatch REFUSED (loud)"
    (gvObligation.discharge (some gvWrongLabelRef)) none
  _ ← assertEq "gv: no witness provided = the loud gap"
    gvObligation.discharge none
  _ ← assert ((gvObligation.discharge (some gvRef)).isSome !=
      (gvObligation.discharge (some gvFuelZeroRef)).isSome)
    "non-vacuity: the discharge distinguishes acceptance from refusal"
  .ok ()

end GuestVerifiedSweep

/-! ## W9.4 — host-side witness generation + self-check + the artifact

`SchemaLang.Emit.Witness`'s pins: the generated certificate (the
claim-matched proof term, the `consumed × 4` pinned fuel), the
ARTIFACT-BYTES round trip (the encoded payload the artifact carries,
decoded + resolved + re-checked — the in-memory value is not the
evidence), the tamper controls (a semantically tampered row REFUSED;
a truncated payload REFUSED), the doctored-generator negative control
(generation WITHOUT the self-check ships a certificate the checker
refuses — the self-check is the gate), the discharge end-to-end
(generated certificate → `.guestWitness` evidence), and the emitter's
`law` field (populated, discharged). The FILE half of the round trip
(`artifactFileChecks`, IO over the committed artifact) runs from
`main`. -/

namespace WitnessEmitSweep

open SchemaLang.Witness SchemaLang.WitnessCheck SchemaLang.Emit.Witness

/-- The generated certificate, via the emitter's CHECKED path — the
    `.get` proof IS the self-check pin (an uncheckable demo spec fails
    THIS elaboration). -/
def generatedCert : Witness :=
  (selfChecked? demoWitnessSpecUserV1V2).get (by decide)

-- the certificate is the spec's claim with the claim-matched proof
example : generatedCert.label = "user-v1-v2-id-positive" := by decide
example : generatedCert.claim = .chain [⟨0⟩, ⟨1⟩] (.gt (.col "id") (.lit 0)) := by decide

/-- The proof-shape predicate (a kernel-reducible match — the derived
    `BEq WProof` is NOT reducible, the nested-`List` trap W9.1's header
    documents; the whole-certificate BEq pin lives in the RUNTIME
    checks below, where compiled evaluation handles it). -/
def isStepsOfTwoValidEvals : WProof → Bool
  | .steps [.byValidEval, .byValidEval] => true
  | _ => false

-- the generated proof is the claim-matched shape: one `byValidEval`
-- per chain step (W9.2's deviation 3)
example : isStepsOfTwoValidEvals generatedCert.proof = true := by decide

-- the pinned fuel is consumed × 4 (owner decision 2): the 2-step chain
-- consumes 3 (1 node + 2 steps — W9.2's deviation 2), ships 12
example : fuelConsumed demoWitnessSpecUserV1V2.claim = 3 := by decide
example : generatedCert.fuel = 12 := by decide

-- soundness, applied: the generated certificate's acceptance IS the
-- claim's denotation (W9.2's `checkWitnessArtifact_sound`, cited)
example : WHolds generatedCert.claim demoWitnessSpecUserV1V2.ctx.row
    demoWitnessSpecUserV1V2.ctx.log :=
  checkWitnessArtifact_sound generatedCert demoWitnessSpecUserV1V2.ctx (by decide)

-- completeness, applied: the semantic premise regenerates an accepting
-- certificate (the module's `selfChecked?_of_WHolds` at the demo spec)
example : (selfChecked? demoWitnessSpecUserV1V2).isSome = true :=
  selfChecked?_of_WHolds _ demoWitnessSpec_holds

/-- The bytes the artifact carries for the demo row (the emitter's own
    encoding path: version + surface-hash fingerprint + payload). -/
def artifactBytes : List UInt8 :=
  encWitness witnessVersion (surfaceHash demoWitnessSpecUserV1V2.ctx.fs).toNat generatedCert

-- THE ROUND TRIP, theorem half: the artifact's bytes decode back to the
-- generated certificate (W9.1's assembled law CITED — the kernel does
-- not evaluate the u64 codec, the law does the work)
example : decWitness? witnessVersion artifactBytes = some generatedCert :=
  decWitness?_encWitness _ _ _

-- the claim's field names resolve against the demo record's surface
-- (design §2.1: a misspelled field is a decode failure — pinned in W9.1's
-- sweep; here the POSITIVE pin for the demo surface)
example : (demoWitnessSpecUserV1V2.claim.resolve?
    demoWitnessSpecUserV1V2.ctx.fs).isSome = true := by decide

/-- The obligation the demo spec certifies (hand-tiered at the kit
    level — the W9.3 deviation: no invariant-lane rung computes the
    fifth tier). The payload's invariant is the `id-positive` mirror
    over User's DERIVED fields. -/
def demoIdPath : ColPath "id" .u64 userNameLenFields := .here

def demoIdPositiveItem : SchemaLang.InvariantItem :=
  { name := "user-v1-v2-id-positive", schemaRef := "User", tier := .boundaryCheck
  , proofName := none
  , inv := ⟨userNameLenFields, VExpr.gt (VExpr.col "id" demoIdPath) (VExpr.lit 0)⟩ }

def demoObligation : SchemaLang.SchemaObligation :=
  { demoIdPositiveItem.obligation with tier := .guestVerified }

/-- The discharge's provided witness: the GENERATED certificate + the
    spec's decoded context + the artifact name. -/
def demoRef : SchemaLang.SchemaObligation.WitnessRef :=
  { artifact := demoWitnessSpecUserV1V2.artifact
  , witness := generatedCert
  , ctx := demoWitnessSpecUserV1V2.ctx }

-- END TO END: the registered obligation + the GENERATED certificate →
-- the discharge FIRES, the evidence naming the artifact + the label
example : demoObligation.discharge (some demoRef) =
    some (.guestWitness "witnesses/user-v1-v2-id-positive.wtn" "user-v1-v2-id-positive") := by decide

-- and the fired evidence IS the claim's denotation (W9.3's
-- `discharge_guestVerified_sound`, cited — the §4 flow's host half
-- closed: generate → self-check → discharge → WHolds)
example : WHolds generatedCert.claim demoWitnessSpecUserV1V2.ctx.row
    demoWitnessSpecUserV1V2.ctx.log :=
  demoObligation.discharge_guestVerified_sound demoRef rfl (by decide)

/-- NEGATIVE CONTROL fixture: the doctored-claim spec — `id > 99` is
    FALSE on the spec's own initial row (id 1). -/
def falseSpec : SchemaLang.WitnessSpec :=
  { demoWitnessSpecUserV1V2 with claim := .valid (.gt (.col "id") (.lit 99)) }

-- the RAW generator still builds a certificate — THIS is what a
-- doctored generator (skipping the self-check) would ship
example : (generateWitness falseSpec).isSome = true := by decide

-- …and the self-check REFUSES it: emission fails, the artifact cannot
-- carry the false certificate (the gate the doctored generator skips)
example : (selfChecked? falseSpec).isNone = true := by decide

-- non-vacuity: the self-check DISTINGUISHES the true spec from the
-- false one
example : ((selfChecked? demoWitnessSpecUserV1V2).isSome !=
    (selfChecked? falseSpec).isSome) = true := by decide

-- SHIPPED-FUEL tamper: the SAME certificate at fuel 0 refuses
-- (exhaustion = refusal, owner decision 2 — no retry)
example : checkWitnessArtifact { generatedCert with fuel := 0 }
    demoWitnessSpecUserV1V2.ctx = false := by decide

-- a certificate re-labeled for ANOTHER obligation refuses the discharge
-- (the mis-wire check, on the generated artifact row)
example : demoObligation.discharge
    (some { demoRef with witness := { generatedCert with label := "user-v9-other" } }) =
    none := by decide

-- the emitter's `law` field is POPULATED (W7.3p2) and discharged for
-- every ctx (the registry is module data — the `circuitLaw` precedent)
example : witnessEmitter.law.isSome = true := rfl
example (ctx : SchemaLang.Emit.GenCtx) : witnessEmitter.Cert ctx := witnessLaw_discharged ctx
example : witnessEmitter.outputs = ["../../src/witnesses_generated.rs"] := rfl

/-- The executed pins: the artifact's byte payload decoded + resolved +
    re-checked at RUNTIME (the codec's kernel path is un-evaluable —
    W9.1's note — so the round trip's executable half lives here), the
    tamper controls, and the emitted content's shape. -/
def witnessEmitChecks : CheckResult := do
  let spec := demoWitnessSpecUserV1V2
  let fs := spec.ctx.fs
  match decWitnessFor? fs witnessVersion artifactBytes with
  | none => .error "artifact bytes did not decode+resolve (the round trip FAILED)"
  | some w' => do
    _ ← assert (w' == generatedCert) "artifact bytes decode to the generated certificate"
    _ ← assert (checkWitnessArtifact w' spec.ctx)
      "the decoded certificate passes the checker (from the BYTES, not the in-memory value)"
    -- TAMPER CONTROL (semantic): the claim strengthened to `id > 99` —
    -- the tampered row decodes fine and the checker REFUSES it
    let tampered : Witness := { w' with claim := .valid (.gt (.col "id") (.lit 99)) }
    let tamperedBytes := encWitness witnessVersion (surfaceHash fs).toNat tampered
    let refused := match decWitnessFor? fs witnessVersion tamperedBytes with
      | none => true
      | some w'' => !checkWitnessArtifact w'' spec.ctx
    _ ← assert refused "tampered artifact row REFUSED (a doctored row cannot pass)"
    -- TAMPER CONTROL (raw): a truncated payload never decodes (the
    -- envelope's length-prefix overrun — W9.1's pinned discipline)
    _ ← assert (decWitnessFor? fs witnessVersion
        (artifactBytes.take (artifactBytes.length - 1))).isNone
      "truncated artifact payload refused at decode"
    -- the emitted artifact's content: the registry, the row, THE BYTES
    match witnessFiles demoWitnesses with
    | [f] => do
      _ ← assertEq "artifact path" f.path "../../src/witnesses_generated.rs"
      _ ← assertContains "artifact declares the registry" f.contents "pub static WITNESS_REGISTRY"
      _ ← assertContains "artifact row: the obligation label" f.contents "user-v1-v2-id-positive"
      _ ← assertContains "artifact row: the pinned fuel" f.contents "fuel: 12u64"
      _ ← assertContains "artifact row carries the exact wire bytes" f.contents
          (s!"bytes: &[{renderBytes artifactBytes}]")
      .ok ()
    | _ => .error "witnessFiles must emit exactly one artifact"

/-- Parse the `bytes: &[…]` payload out of the artifact's first row
    (the file's own rendering — the round trip through the FILE is the
    point). -/
def parseRowBytes? (text : String) : Option (List UInt8) := do
  let after ← (text.splitOn "bytes: &[")[1]?
  let payload ← (after.splitOn "]")[0]?
  (payload.splitOn ", ").mapM fun s => do
    let n ← s.toNat?
    if n < 256 then some n.toUInt8 else none

/-- The FILE half of the round trip: read the COMMITTED byte-tied
    artifact (what the host ships), parse the row's bytes back out,
    decode + resolve, re-check. IO; run from `main`. -/
def artifactFileChecks : IO UInt32 := do
  let path : System.FilePath := "../../src/witnesses_generated.rs"
  unless ← path.pathExists do
    IO.println "W9.4 artifact-file check FAILED: witnesses_generated.rs absent — run `lake exe schema gen`"
    return 1
  let text ← IO.FS.readFile path
  let spec := demoWitnessSpecUserV1V2
  match parseRowBytes? text with
  | none =>
    IO.println "W9.4 artifact-file check FAILED: no parseable `bytes: &[…]` row"
    return 1
  | some bytes =>
    match decWitnessFor? spec.ctx.fs witnessVersion bytes with
    | none =>
      IO.println "W9.4 artifact-file check FAILED: the file's row bytes did not decode+resolve"
      return 1
    | some w =>
      if w == generatedCert && checkWitnessArtifact w spec.ctx then
        IO.println "W9.4 artifact-file check: the committed artifact's row decodes + passes the checker"
        return 0
      else
        IO.println "W9.4 artifact-file check FAILED: the file's row disagrees with generation or fails the checker"
        return 1

end WitnessEmitSweep

/-! ## W9.5 — the witness-gated migration checkpoint (the apply-gate)

`SchemaLang.EventSourced.replayMigrated?` (design-guest-verified §4
steps 3–5) + the `WitnessCheck.verifyWitness` seam: the seam IS
`checkWitnessArtifact` (W9.6's swap point — one definition), the fuel
classifier is EXACT (`fuelNeed`: below it the check always refuses,
at/above it the verdict is fuel-free — both theorems, both executed
here), and the gate applies the migrated segment ONLY on acceptance —
refusal names the obligation's label + the class (`diverged` /
`fuelExhausted`). The END-TO-END dogfood (a real v1→v2 field migration
over a registered record) is the ledger package's (LedgerES); this
sweep pins the gate's semantics over a synthetic fixture. -/

namespace MigrationGateSweep

open SchemaLang.Witness SchemaLang.WitnessCheck SchemaLang.EventSourced

/-- The fixture record: one u64 column (the migrated segment's rows). -/
def mgFields : List Field := [⟨"amount", .u64⟩]

/-- The row builder. -/
def mgRowOf (n : UInt64) : RowVals mgFields := .cons (.u64 n) .nil

/-- The identity upcast, explicitly typed (the implicit key type
    cannot be synthesized from a bare lambda). -/
def mgUpcast : Delta UInt64 UInt64 → Delta UInt64 UInt64 := fun e => e

/-- The derived decoded context the gate checks against (init row 7,
    the segment's one insert payload 1). -/
def mgCtx : RowValsP := migrationCtx mgRowOf mgUpcast 7 [.insert 1]

/-- A VALID witness for the gate fixture: `amount > 0` holds of the
    init row (7) and the segment row (1); fuel 8 dwarfs the need (2). -/
def mgWitness : Witness :=
  ⟨"mg-amount-positive", .chain [⟨0⟩] (.gt (.col "amount") (.lit 0)),
    .steps [.byValidEval], 8⟩

/-- The gate call under test (fixture-shaped: identity upcast, state =
    the base row's table). -/
def mgGate (w : Witness) : Except MigrationRefusal (List UInt64) :=
  replayMigrated? (fun (n : UInt64) => n) mgRowOf mgUpcast w 7 [.insert 1] [7]

/-- NEGATIVE CONTROL fixture: the tampered certificate — the claim
    strengthened to `amount > 5`, FALSE on the segment row (1). -/
def mgTampered : Witness :=
  { mgWitness with claim := .chain [⟨0⟩] (.gt (.col "amount") (.lit 5)) }

/-- NEGATIVE CONTROL fixture: the corrupted certificate — one chain
    step, zero step proofs (the length mismatch). -/
def mgCorrupt : Witness := { mgWitness with proof := .steps [] }

/-- NEGATIVE CONTROL fixture: exhaustion — the SAME certificate with
    fuel 1, below the need (2) (§7.3: refusal, NO retry). -/
def mgFuelLow : Witness := { mgWitness with fuel := 1 }

-- the seam IS the checker's artifact entry (the W9.6 swap point)
example : verifyWitness mgWitness mgCtx = checkWitnessArtifact mgWitness mgCtx := rfl

-- the seam, executed both ways
example : verifyWitness mgWitness mgCtx = true := by decide
example : verifyWitness mgTampered mgCtx = false := by decide
example : verifyWitness mgFuelLow mgCtx = false := by decide

-- the seam's soundness wrapper, APPLIED
example : WHolds mgWitness.claim mgCtx.row mgCtx.log :=
  verifyWitness_sound mgWitness mgCtx (by decide)

-- the fuel need, pinned
example : fuelNeed mgWitness.claim = 2 := rfl
example : fuelNeed (.valid (.gt (.col "amount") (.lit 0))) = 1 := rfl

-- the classifier, exact, EXECUTED: below the need the check refuses …
example : checkWitness 1 mgWitness.claim mgWitness.proof mgFields mgCtx.row mgCtx.log
    = false := by decide
-- … and at/above the need the verdict is fuel-free (no retry could help)
example : checkWitness 2 mgWitness.claim mgWitness.proof mgFields mgCtx.row mgCtx.log =
    checkWitness 64 mgWitness.claim mgWitness.proof mgFields mgCtx.row mgCtx.log := by decide

-- `Delta.row?`: insert/update carry the row, remove carries none
example : Delta.row? (.insert 7 : Delta UInt64 UInt64) = some 7 := rfl
example : Delta.row? (.remove 3 : Delta UInt64 UInt64) = none := rfl

-- POSITIVE: the valid witness ACCEPTS and the migrated segment replays
example : mgGate mgWitness = .ok [7, 1] := by decide

-- NEGATIVE CONTROL: the tampered claim REFUSES — `diverged`, label named
example : mgGate mgTampered = .error (.diverged "mg-amount-positive") := by decide

-- NEGATIVE CONTROL: the corrupted proof REFUSES — `diverged`
example : mgGate mgCorrupt = .error (.diverged "mg-amount-positive") := by decide

-- NEGATIVE CONTROL (§7.3): the exhausted certificate REFUSES —
-- `fuelExhausted`, label named, BEFORE any checking
example : mgGate mgFuelLow = .error (.fuelExhausted "mg-amount-positive") := by decide
example : mgGate { mgWitness with fuel := 0 } =
    .error (.fuelExhausted "mg-amount-positive") := by decide

-- the refusal-class theorems, APPLIED (not just the decide'd verdicts)
example : mgGate mgFuelLow = .error (.fuelExhausted "mg-amount-positive") :=
  replayMigrated?_fuelExhausted (fun (n : UInt64) => n) mgRowOf mgUpcast
    mgFuelLow 7 [.insert 1] [7] (by decide)

example : mgGate mgTampered = .error (.diverged "mg-amount-positive") :=
  replayMigrated?_diverged (fun (n : UInt64) => n) mgRowOf mgUpcast
    mgTampered 7 [.insert 1] [7] (by decide) (by decide)

-- THE ACCEPTANCE THEOREM, APPLIED: acceptance returns the replay AND
-- the claim's denotation over the derived context
example : WHolds mgWitness.claim (mgRowOf 7)
    (migrationCtx mgRowOf mgUpcast 7 [.insert 1]).log :=
  (replayMigrated?_ok (fun (n : UInt64) => n) mgRowOf mgUpcast
    mgWitness 7 [.insert 1] [7] [7, 1] (by decide)).2

/-- The executed pins + non-vacuity (the gate DISTINGUISHES acceptance
    from refusal — a suite whose sabotage passes fails here). -/
def migrationGateChecks : CheckResult := do
  _ ← assert (mgGate mgWitness == .ok [7, 1])
    "gate: valid witness ACCEPTS + replays the migrated segment"
  _ ← assert (mgGate mgTampered == .error (.diverged "mg-amount-positive"))
    "gate: tampered claim REFUSED (diverged, label named)"
  _ ← assert (mgGate mgCorrupt == .error (.diverged "mg-amount-positive"))
    "gate: corrupted proof REFUSED (diverged)"
  _ ← assert (mgGate mgFuelLow == .error (.fuelExhausted "mg-amount-positive"))
    "gate: exhausted fuel REFUSED (fuelExhausted — §7.3, no retry)"
  _ ← assert (mgGate mgWitness != mgGate mgTampered)
    "non-vacuity: the gate distinguishes acceptance from refusal"
  -- the refusal render names the obligation's label (LOUD, not silent) —
  -- String.splitOn does not kernel-reduce, so this pin runs compiled
  _ ← assert (((MigrationRefusal.diverged "mg-x").render.splitOn "mg-x").length == 2)
    "refusal render: `diverged` names the obligation's label"
  _ ← assert (((MigrationRefusal.fuelExhausted "mg-x").render.splitOn "mg-x").length == 2)
    "refusal render: `fuelExhausted` names the obligation's label"
  .ok ()

end MigrationGateSweep

/-! ## W8.1 — `map`/`set` in `Ty` (the closed-universe rule, exercised)

The new ctors' pins over SYNTHETIC universes (the demo is UNCHANGED —
the byte-tie): the `KeyTy` scalar sub-universe (a non-scalar key is
unrepresentable — the gate pins live at the snapshot format boundary),
the wire round trips (the `decode_encodeValue` theorem's executable
image, concrete + swept via `genPack`'s new arms), the RowVals row
round trip, and every emitter's rendering. -/

namespace MapSetSweep

/-- The fixture types: a string-keyed map, a string set, a composite
    VALUE (maps nest values freely — only KEYS are gated). -/
def scoresTy : Ty := .map .string .u64
def tagsTy : Ty := .set .string
def nestedTy : Ty := .map .u32 (.list (.option .string))

/-- The fixture payloads (insertion-ordered association/element lists
    — the `list` discipline). -/
def scoresVal : Value scoresTy :=
  .map (.cons (.string "a") (.u64 1) (.cons (.string "b") (.u64 2) .nil))
def tagsVal : Value tagsTy :=
  .set (.cons (.string "x") (.cons (.string "y") .nil))

/-- A synthetic universe exercising both ctors in field position. -/
def mapSetUniverse : List Item :=
  [.record "mapset-rec" [⟨"scores", scoresTy⟩, ⟨"tags", tagsTy⟩]]

/-- The Wf bridge lane, discharged through the checker (the reasoning
    authority ADMITS map/set fields — a stub would not elaborate). -/
example : WellFormed mapSetUniverse := universeCheck_sound rfl

def mapSetChecks : CheckResult := do
  -- the wire round trips (decode_encodeValue's executable image)
  _ ← assert (match decodeValue scoresTy (encodeValue scoresTy scoresVal) with
    | some v => valueEq scoresTy v scoresVal | none => false)
    "map wire round trip"
  _ ← assert (match decodeValue tagsTy (encodeValue tagsTy tagsVal) with
    | some v => valueEq tagsTy v tagsVal | none => false)
    "set wire round trip"
  -- the RowVals row round trip (re-encode stable — the row codec's pin)
  let fields : List Field := [⟨"scores", scoresTy⟩, ⟨"tags", tagsTy⟩]
  let row : RowVals fields := .cons scoresVal (.cons tagsVal .nil)
  let wire := encRowVals fields row
  _ ← assert (match decRowVals? fields wire with
    | some (row', []) => encRowVals fields row' == wire | _ => false)
    "map+set row wire round trip"
  -- NEGATIVE CONTROLS, wire level (malformed payloads reject). The
  -- varint leaves are TOTAL on empty input (decVarNat [] = (0, [])),
  -- so count-only/truncated wires decode — the REJECTING shape in
  -- this codec family is the bounded-int gate, firing here THROUGH
  -- the entry/element decoder:
  let mapU16 : Ty := .map .u16 .u16
  _ ← assert (decVal? mapU16 ([1] ++ Codec.encVarNat (2^16)
      ++ Codec.encVarNat 0)).isNone
    "map wire: an out-of-range KEY rejects (the u16 gate fires through the entry pair)"
  _ ← assert (decVal? mapU16 ([1] ++ Codec.encVarNat 7
      ++ Codec.encVarNat (2^16))).isNone
    "map wire: an out-of-range VALUE rejects"
  _ ← assert (decVal? mapU16 ([1] ++ Codec.encVarNat 7
      ++ Codec.encVarNat 9)).isSome
    "map wire: an in-range entry decodes"
  let setU16 : Ty := .set .u16
  _ ← assert (decVal? setU16 ([1] ++ Codec.encVarNat (2^16))).isNone
    "set wire: an out-of-range element rejects"
  _ ← assert (decVal? tagsTy [0]).isSome
    "set wire: the empty set decodes (the count-0 pin)"
  -- NEGATIVE CONTROLS, type level (the key gate at the snapshot
  -- boundary — in the TYPE the bad keys are unrepresentable):
  _ ← assert (Snapshot.parseTyText "map(f32,u64)").toOption.isNone
    "snapshot key gate: a float key rejects (NaN breaks the order)"
  _ ← assert (Snapshot.parseTyText "set(list(u8))").toOption.isNone
    "snapshot key gate: a composite element rejects"
  _ ← assert (Snapshot.parseTyText "map(ty(User),u64)").toOption.isNone
    "snapshot key gate: a named-ref key rejects"
  _ ← assert (Ty.toKeyTy? .f32 == none) "toKeyTy? float"
  _ ← assert (Ty.toKeyTy? (.list .u8) == none) "toKeyTy? composite"
  _ ← assert (Ty.toKeyTy? .string == some .string) "toKeyTy? string"
  -- the snapshot round trips (ty-level and universe-level)
  _ ← assert ((Snapshot.parseTyText scoresTy.toSnapshot).toOption == some scoresTy)
    "map snapshot round trip"
  _ ← assert ((Snapshot.parseTyText tagsTy.toSnapshot).toOption == some tagsTy)
    "set snapshot round trip"
  _ ← assert ((Snapshot.parseTyText nestedTy.toSnapshot).toOption == some nestedTy)
    "nested-value snapshot round trip"
  _ ← assert
    ((Snapshot.parse (Snapshot.render mapSetUniverse)).toOption == some mapSetUniverse)
    "universe snapshot round trip"
  -- the emitters (the rendering table, pinned):
  _ ← assertEq "WIT map" (Emit.Wit.tyWit scoresTy) "list<tuple<string, u64>>"
  _ ← assertEq "WIT set" (Emit.Wit.tyWit tagsTy) "list<string>"
  _ ← assertContains "WIT record member"
    (Emit.Wit.typeDecl (.record "mapset-rec"
      [⟨"scores", scoresTy⟩, ⟨"tags", tagsTy⟩])).pretty
    "scores: list<tuple<string, u64>>,"
  _ ← assertEq "Rust map (BTree — deterministic)"
    (Emit.Rust.tyRust scoresTy) "BTreeMap<String, u64>"
  _ ← assertEq "Rust set (BTree — deterministic)"
    (Emit.Rust.tyRust tagsTy) "BTreeSet<String>"
  _ ← assertEq "a float VALUE blocks Eq through the map"
    (Emit.Rust.hasFloat [] (.map .string .f32)) true
  _ ← assertEq "scalar map is Eq-clean" (Emit.Rust.hasFloat [] scoresTy) false
  _ ← assertEq "set is Eq-clean (KeyTy is float-free)"
    (Emit.Rust.hasFloat [] tagsTy) false
  _ ← assert
    (Vortex.Ty.lower (fun _ => none) .nonNullable scoresTy ==
      some (.list (.struct [("key", .utf8 .nonNullable),
          ("value", .primitive .u64 .nonNullable)] .nonNullable) .nonNullable))
    "vortex map lowers (the parquet list-of-entries convention)"
  _ ← assert
    (Vortex.Ty.lower (fun _ => none) .nonNullable tagsTy ==
      some (.list (.utf8 .nonNullable) .nonNullable))
    "vortex set lowers (list of elements)"
  _ ← assert
    (Vortex.Ty.lowerChecked (fun _ => none) .nonNullable scoresTy rfl ==
      Vortex.Ty.lower (fun _ => none) .nonNullable scoresTy)
    "the checked lowering agrees (map)"
  _ ← assert (Ty.toSType? scoresTy).isNone
    "substrait bridge: maps not queryable (the refusal precedent)"
  _ ← assert (Ty.toSType? tagsTy).isNone
    "substrait bridge: sets not queryable"
  -- the guard lanes reach THROUGH the new ctors:
  _ ← assertEq "async in a map VALUE is banned in field position"
    (Ty.banAsync (.map .string (.future .u8))) false
  _ ← assertEq "set is async-free (KeyTy)" (Ty.banAsync tagsTy) true
  _ ← assertEq "refs resolve through the map value"
    (Ty.tyRefs (.map .string (.ty "user"))) ["user"]
  _ ← assertEq "set carries no refs" (Ty.tyRefs tagsTy) []
  _ ← assertEq "result in a map value trips the vortex guard"
    (Ty.noResult (.map .string (.result .u8 .u8))) false
  _ ← assert (universeCheck mapSetUniverse == [])
    "universeCheck is clean over map/set fields"
  -- the secondary emitters' deliberate arms:
  _ ← assert (Emit.GenRust.unsupported? [] 8 scoresTy).isSome
    "genRust: maps gated out of the v1 fragment (loud, named)"
  _ ← assert (Emit.GenRust.unsupported? [] 8 tagsTy).isSome
    "genRust: sets gated out of the v1 fragment (loud, named)"
  _ ← assert (litTy? scoresTy).isNone
    "delta: no self-contained map literal (the tensor rule)"
  _ ← assert (SchemaLang.defaultValue? scoresTy).isSome
    "invariant: the empty map is a Lean-side default"
  _ ← assert (Emit.Invariant.rustDefault? scoresTy).isNone
    "invariant: no Rust map literal (the import is not pinned)"
  .ok ()

end MapSetSweep

/-! ## W8.2 — declared keys + foreign keys (SchemaLang.Keys)

The pure lane: the fixture universe + declaration set below exercise
the checker (positive + EVERY rejection mode as a negative control),
the relation via the bridge (the W3.5 discharge shape), the obligation
view's enumeration + discharge (the decidableNow backend), and the
`Item.keyOfWith` migration (declared = conventional on first-field
declarations; declared WINS otherwise). The command/attribute surface
and the `@[event_sourced]` key migration pin live at the end of the
file (the meta lane). -/

namespace KeySweep

/-- The fixture universe: two records (user keyed by `id`; order keyed
    by `id`, FK `userId → user`), a keyless record (`plain` — the
    target-keyless control), and a variant (`role` — the
    not-a-record control). -/
def keyItems : List Item :=
  [ .record "user" [⟨"id", .u64⟩, ⟨"name", .string⟩]
  , .record "order"
      [⟨"id", .u64⟩, ⟨"userId", .u64⟩, ⟨"userName", .string⟩, ⟨"total", .f64⟩]
  , .record "plain" [⟨"x", .u64⟩]
  , .variant "role" [("admin", none), ("viewer", none)] ]

def userFields : List Field := [⟨"id", .u64⟩, ⟨"name", .string⟩]
def orderFields : List Field :=
  [⟨"id", .u64⟩, ⟨"userId", .u64⟩, ⟨"userName", .string⟩, ⟨"total", .f64⟩]

/-- The well-formed fixture declarations. -/
def userKeys : KeyDecl :=
  { record := "user", fields := userFields, key := "id" }
def orderKeys : KeyDecl :=
  { record := "order", fields := orderFields, key := "id"
  , foreign := [{ field := "userId", target := "user" }] }
def keyDecls : List KeyDecl := [userKeys, orderKeys]

/-- The fixture declaration set is well-formed, VIA the sound bridge
    (the checker discharges — `rfl`; the relation receives). -/
theorem keyDecls_wellFormed : KeysWellFormed keyItems keyDecls :=
  keyDeclsCheck_sound rfl

/-- NEGATIVE CONTROL (non-vacuity), the missing-key-field mode: the
    relation REJECTS what the checker rejects (a vacuous
    `KeysWellFormed` breaks this proof — the W3.5 pin's shape). -/
theorem keyDeclsMissingField_not_wf :
    ¬ KeysWellFormed keyItems [userKeys, { orderKeys with key := "uid" }] := by
  intro hwf
  have hnil := keyDeclsCheck_complete hwf
  have hlen : (keyDeclsCheck keyItems
      [userKeys, { orderKeys with key := "uid" }]).length = 1 := by decide
  rw [hnil] at hlen
  exact absurd hlen (by decide)

/-- NEGATIVE CONTROL, the foreign-key type-mismatch mode (a `string`
    field referencing a `u64` key — both are scalars; the TYPES must
    agree). -/
theorem keyDeclsFkMismatch_not_wf :
    ¬ KeysWellFormed keyItems
      [userKeys, { orderKeys with foreign := [⟨"userName", "user"⟩] }] := by
  intro hwf
  have hnil := keyDeclsCheck_complete hwf
  have hlen : (keyDeclsCheck keyItems
      [userKeys, { orderKeys with foreign := [⟨"userName", "user"⟩] }]).length
        = 1 := by decide
  rw [hnil] at hlen
  exact absurd hlen (by decide)

/-- A user row (id controllable, name default). -/
def userRow (i : UInt64) : RowVals userFields :=
  .cons (.u64 i) (.cons (.string "") .nil)

/-- An order row (id + userId controllable, the rest default). -/
def orderRow (i uid : UInt64) : RowVals orderFields :=
  .cons (.u64 i) (.cons (.u64 uid) (.cons (.string "") (.cons (.f64 0) .nil)))

/-- The demo obligations, hand-assembled (the enumeration pin below
    checks the VIEW against these). -/
def userUniqueObligation : KeyObligation :=
  { label := "user.key-unique(id)"
  , tier := KeyClaim.tierOf (.unique userKeys)
  , payload := .unique userKeys
  , provenance := "user".toName }

/-- The FK row for the fixtures. -/
def orderFk : ForeignKey := { field := "userId", target := "user" }

def orderReferencesObligation : KeyObligation :=
  { label := "order.userId-references-user(id)"
  , tier := KeyClaim.tierOf (.references orderKeys orderFk userKeys)
  , payload := .references orderKeys orderFk userKeys
  , provenance := "order".toName }

/-- The soundness theorem, CITED at the key lane (the
    `decNowTrue_holds` pattern): the `.decided true` discharge IS the
    claim — here the `user` declaration's uniqueness on the pinned
    all-default singleton table. -/
theorem userKeyUnique_holds :
    userKeys.uniqueOn [.cons (.u64 0) (.cons (.string "") .nil)] = true :=
  userUniqueObligation.discharge_decidableNow_sound rfl rfl

/-- The completeness theorem, CITED: the true claim FIRES the backend
    (discharge = the decided evidence). -/
theorem userKeyUnique_discharges :
    userUniqueObligation.discharge = some (.decided true) :=
  userUniqueObligation.discharge_decidableNow_of_claim rfl userKeyUnique_holds

/-- A broken declaration (key field not on the record): the projection
    fails, the claim decides FALSE, the backend REFUSES. -/
def orderKeysBroken : KeyDecl := { orderKeys with key := "uid" }
def brokenUniqueObligation : KeyObligation :=
  { label := "order.key-unique(uid)", tier := .decidableNow
  , payload := .unique orderKeysBroken, provenance := "order".toName }

/-- The refusal, pinned (no fabricated evidence). -/
theorem brokenUnique_refused : brokenUniqueObligation.discharge = none := rfl

/-- A type-mismatched FK (`userName : string` → user's `id : u64`
    key): referential integrity can never hold across types — the
    claim decides FALSE, the backend REFUSES. -/
def orderKeysMismatch : KeyDecl :=
  { orderKeys with foreign := [{ field := "userName", target := "user" }] }
def mismatchReferencesObligation : KeyObligation :=
  { label := "order.userName-references-user(id)", tier := .decidableNow
  , payload := .references orderKeysMismatch ⟨"userName", "user"⟩ userKeys
  , provenance := "order".toName }

/-- The refusal, pinned. -/
theorem mismatchReferences_refused :
    mismatchReferencesObligation.discharge = none := rfl

/-- The `keyOfWith` fixtures: a record whose DECLARED key is NOT the
    first field. -/
def rekeyedItem : Item :=
  .record "rekeyed" [⟨"label", .string⟩, ⟨"code", .u64⟩]
def rekeyedDecl : KeyDecl :=
  { record := "rekeyed", fields := [⟨"label", .string⟩, ⟨"code", .u64⟩]
  , key := "code" }

/-- The migration equivalence, APPLIED to the fixture: the `user`
    declaration names the FIRST field, so declared = conventional (the
    ledger/Demo shape — `keyOfWith_eq_keyOf_of_decl_head`). -/
theorem keyOfWith_user_eq_keyOf :
    Item.keyOfWith keyDecls (.record "user" userFields) =
      Item.keyOf (.record "user" userFields) :=
  Item.keyOfWith_eq_keyOf_of_decl_head (kd := userKeys) rfl rfl

def keyChecks : CheckResult := do
  -- positive: the fixture declaration set, both readings
  _ ← assertEq "keys: the fixture declaration set checks clean"
    (keyDeclsCheck keyItems keyDecls) []
  _ ← assert (keyDeclsWellFormed keyItems keyDecls)
    "keys: the Bool gate agrees"
  _ ← assert (keysChecked.check (keyItems, keyDecls))
    "keys: the CheckedProp pack fires"
  _ ← assert keysChecked.isComplete
    "keys: completeness is PROVED (not .missing — the loud flag)"
  -- NEGATIVE CONTROLS — one per rejection mode (the diag ctor is the pin)
  _ ← assert (match keyDeclsCheck keyItems
      [userKeys, { orderKeys with key := "uid" }] with
    | [.keyFieldMissing "order" "uid" _] => true | _ => false)
    "keys: missing key field rejected (keyFieldMissing)"
  _ ← assert (match keyDeclsCheck keyItems
      [userKeys, { orderKeys with key := "total" }] with
    | [.keyNotScalar "order" "total" _] => true | _ => false)
    "keys: non-scalar key rejected (keyNotScalar — f64 is not KeyTy)"
  _ ← assert (match keyDeclsCheck keyItems
      [{ userKeys with record := "usr" }] with
    | [.keyRecordMissing "usr" _] => true | _ => false)
    "keys: unknown record rejected (keyRecordMissing)"
  _ ← assert (match keyDeclsCheck keyItems
      [{ record := "role", fields := [], key := "id" }] with
    | [.keyRecordNotRecord "role"] => true | _ => false)
    "keys: a variant cannot take keys (keyRecordNotRecord)"
  _ ← assert (match keyDeclsCheck keyItems
      [{ userKeys with fields := [⟨"id", .u64⟩] }] with
    | [.keyFieldsMismatch "user"] => true | _ => false)
    "keys: stale field snapshot rejected (keyFieldsMismatch)"
  _ ← assert (match keyDeclsCheck keyItems
      [userKeys, { orderKeys with foreign := [⟨"uid", "user"⟩] }] with
    | [.foreignFieldMissing "order" "uid" _] => true | _ => false)
    "keys: missing FK field rejected (foreignFieldMissing)"
  _ ← assert (match keyDeclsCheck keyItems
      [userKeys, { orderKeys with foreign := [⟨"userId", "usr"⟩] }] with
    | [.foreignTargetMissing "order" "userId" "usr" _] => true | _ => false)
    "keys: unknown FK target rejected (foreignTargetMissing)"
  _ ← assert (match keyDeclsCheck keyItems
      [userKeys, { orderKeys with foreign := [⟨"userId", "role"⟩] }] with
    | [.foreignTargetNotRecord "order" "userId" "role"] => true | _ => false)
    "keys: variant FK target rejected (foreignTargetNotRecord)"
  _ ← assert (match keyDeclsCheck keyItems
      [userKeys, { orderKeys with foreign := [⟨"userId", "plain"⟩] }] with
    | [.foreignTargetKeyless "order" "userId" "plain"] => true | _ => false)
    "keys: keyless FK target rejected (foreignTargetKeyless)"
  _ ← assert (match keyDeclsCheck keyItems
      [userKeys, { orderKeys with foreign := [⟨"userName", "user"⟩] }] with
    | [.foreignTypeMismatch "order" "userName" "user" _ _] => true | _ => false)
    "keys: FK type mismatch rejected (foreignTypeMismatch)"
  _ ← assert (match keyDeclsCheck keyItems [userKeys, userKeys, orderKeys] with
    | [.dupKeyDecl "user"] => true | _ => false)
    "keys: duplicate declaration rejected (dupKeyDecl)"
  -- the obligation VIEW: enumeration, labels, computed tiers, provenance
  _ ← assertEq "keyObligations: one unique per decl + one per FK"
    ((keyObligations keyDecls).map (·.label))
    ["user.key-unique(id)", "order.key-unique(id)",
      "order.userId-references-user(id)"]
  _ ← assertEq "keyObligations: the computed tier is decidableNow"
    ((keyObligations keyDecls).map (·.tier))
    [.decidableNow, .decidableNow, .decidableNow]
  _ ← assertEq "keyObligations: provenance is the record"
    ((keyObligations keyDecls).map (·.provenance))
    [("user".toName), ("order".toName), ("order".toName)]
  -- the discharge: computed-tier obligations FIRE on the pinned table
  _ ← assertEq "keyObl: unique discharges (.decided true)"
    userUniqueObligation.discharge (some (.decided true))
  _ ← assertEq "keyObl: references discharges (.decided true)"
    orderReferencesObligation.discharge (some (.decided true))
  _ ← assertEq "keyObl: the evidence's tier IS the obligation's"
    (userUniqueObligation.discharge.map (·.tier)) (some .decidableNow)
  -- NEGATIVE CONTROLS (the loud refusal — no fabricated evidence)
  _ ← assertEq "keyObl: a broken projection REFUSES (none, loud)"
    brokenUniqueObligation.discharge none
  _ ← assertEq "keyObl: a type-mismatched FK REFUSES (none, loud)"
    mismatchReferencesObligation.discharge none
  _ ← assert (userUniqueObligation.discharge != brokenUniqueObligation.discharge)
    "keyObl: discharge DISTINGUISHES sound from broken (non-vacuity)"
  -- the table checks themselves, beyond the pinned singleton
  _ ← assert (userKeys.uniqueOn [userRow 1, userRow 2])
    "uniqueOn: distinct keys pass"
  _ ← assert (!userKeys.uniqueOn [userRow 1, userRow 1])
    "uniqueOn: duplicate keys FAIL — the row-set is a FUNCTION from key to row"
  _ ← assert (orderKeys.referencesOn orderFk userKeys [orderRow 1 7] [userRow 7])
    "referencesOn: a resolving FK passes"
  _ ← assert (!orderKeys.referencesOn orderFk userKeys [orderRow 1 7] [userRow 9])
    "referencesOn: a dangling FK FAILS"
  -- the one "which key?" answer
  _ ← assert (Item.keyOfWith [] rekeyedItem == Item.keyOf rekeyedItem)
    "keyOfWith: no declarations = the convention"
  _ ← assert (Item.keyOfWith [rekeyedDecl] rekeyedItem == some ⟨"code", .u64⟩)
    "keyOfWith: the declared key WINS"
  _ ← assert (Item.keyOf rekeyedItem == some ⟨"label", .string⟩)
    "keyOf: the convention alone would pick the first field"
  _ ← assert (Item.keyOfWith keyDecls (.record "user" userFields) ==
      Item.keyOf (.record "user" userFields))
    "keyOfWith: declared = conventional on first-field decls"
  .ok ()

end KeySweep

/-! ## W8.8 — table-level invariants (the pure lane)

Uniqueness / conservation / cardinality as aggregation predicates over
the whole row-set (`TableAgg.check`); the obligation view discharges at
the computed `decidableNow` rung over a PROVIDED materialized table —
the aggregate check RUNS where the table is materialized (the module
header's tier answer). The ledger-shaped fixture is the conservation
dogfood: ledger's `total_post_conserves` is the PRESERVATION half (the
update lane's obligation); here the invariant itself, checked pre/post
transfer, with the one-legged posting as the sabotage. -/

namespace TableInvSweep

/-- The fixture universe: `acct` (the ledger's Account shape — `id`
    key, a string column, the u64 `balance` stock), a keyless record,
    and a variant (the not-a-record control). -/
def tiItems : List Item :=
  [ .record "acct" [⟨"id", .u64⟩, ⟨"nick", .string⟩, ⟨"balance", .u64⟩]
  , .record "plain" [⟨"x", .string⟩]
  , .variant "role" [("admin", none), ("viewer", none)] ]

def acctFields : List Field := [⟨"id", .u64⟩, ⟨"nick", .string⟩, ⟨"balance", .u64⟩]

/-- An account row (id + balance controllable, nick default). -/
def acctRow (i b : UInt64) : RowVals acctFields :=
  .cons (.u64 i) (.cons (.string "") (.cons (.u64 b) .nil))

/-- The pre-transfer table: alice 100, bob 50 — the stock total is 150. -/
def acctPre : List (RowVals acctFields) := [acctRow 1 100, acctRow 2 50]

/-- The post-transfer table (alice → bob, 30): the total SURVIVES the
    update — conservation's whole point. -/
def acctPost : List (RowVals acctFields) := [acctRow 1 70, acctRow 2 80]

/-- The sabotaged table: a ONE-LEGGED posting (the debit leg without
    the credit) — the total moved; conservation must REFUSE. -/
def acctSabotaged : List (RowVals acctFields) := [acctRow 1 70, acctRow 2 50]

/-- The declared invariants: uniqueness of `id`, conservation of
    `balance` at 150, the cardinality bound, the exact cardinality. -/
def acctUnique : TableInvItem :=
  { name := "acct-ids-unique", schemaRef := "acct", fields := acctFields
  , agg := .unique "id" }
def acctConservation : TableInvItem :=
  { name := "acct-conserves", schemaRef := "acct", fields := acctFields
  , agg := .sum "balance" 150 }
def acctBounded : TableInvItem :=
  { name := "acct-bounded", schemaRef := "acct", fields := acctFields
  , agg := .countLe 2 }
def acctExact : TableInvItem :=
  { name := "acct-exact", schemaRef := "acct", fields := acctFields
  , agg := .countEq 2 }

def tiDecls : List TableInvItem := [acctUnique, acctConservation, acctBounded, acctExact]

/-- CONSERVATION, the dogfood's positive leg: the pre-transfer table
    conserves 150, kernel-checked. -/
theorem conservation_pre : acctConservation.agg.check acctPre = true := rfl

/-- The transfer PRESERVES the invariant (posting moves stock, the
    total stays). -/
theorem conservation_post : acctConservation.agg.check acctPost = true := rfl

/-- NEGATIVE CONTROL: the one-legged posting VIOLATES conservation (a
    vacuous check would pass it). -/
theorem conservation_sabotaged :
    acctConservation.agg.check acctSabotaged = false := rfl

/-- The obligation row + the CITED soundness (the `userKeyUnique_holds`
    pattern): the `.decided true` discharge IS the claim over the
    provided table. -/
def acctConsObligation : TableObligation := acctConservation.obligation

theorem acctCons_holds : acctConsObligation.holdsOn acctPre :=
  acctConsObligation.discharge_decidableNow_sound acctPre rfl rfl

/-- The completeness theorem, CITED: the true claim FIRES the backend. -/
theorem acctCons_discharges :
    acctConsObligation.discharge (some acctPre) = some (.decided true) :=
  acctConsObligation.discharge_decidableNow_of_holds acctPre rfl acctCons_holds

/-- The sabotaged table REFUSES (no fabricated evidence). -/
theorem acctCons_sabotage_refused :
    acctConsObligation.discharge (some acctSabotaged) = none := rfl

/-- No provided table = the loud gap. -/
theorem acctCons_no_table_refused : acctConsObligation.discharge = none := rfl

/-- A hand-set tier the lane cannot serve REFUSES — the unwired
    oracleSwept, and the design-doc's guestVerified refusal (§7.1:
    table-level aggregations get no v1 witness). -/
def acctConsOracle : TableObligation :=
  { acctConsObligation with tier := .oracleSwept }
def acctConsGuest : TableObligation :=
  { acctConsObligation with tier := .guestVerified }

theorem acctCons_oracle_refused :
    acctConsOracle.discharge (some acctPre) = none := rfl
theorem acctCons_guest_refused :
    acctConsGuest.discharge (some acctPre) = none := rfl

/-- The existential executor at the item's own fields IS the check
    (the `checkOn_self` interface — no unfolding the irreducible). -/
theorem acctCons_checkOn : acctConservation.checkOn acctPre = true :=
  (TableInvItem.checkOn_self acctConservation acctPre).trans conservation_pre

def plainFields : List Field := [⟨"x", .string⟩]

/-- The cross-schema refusal, APPLIED: a `plain`-shaped table against
    the acct item refuses (type mismatch = refusal, never a misread). -/
theorem acctCons_checkOn_refuses (r : RowVals plainFields) :
    acctConservation.checkOn [r] = false :=
  TableInvItem.checkOn_of_ne (fs := plainFields) (ti := acctConservation) (by decide) [r]

def tableInvChecks : CheckResult := do
  -- the checker, positive
  _ ← assertEq "tableInv: the fixture declaration set checks clean"
    (tableInvCheck tiItems tiDecls) []
  _ ← assert (tableInvWellFormed tiItems tiDecls) "tableInv: the Bool gate agrees"
  -- NEGATIVE CONTROLS — one per rejection mode
  _ ← assert (tableInvCheck tiItems [{ acctUnique with schemaRef := "zz" }] != [])
    "tableInv: unknown record rejected"
  _ ← assert (tableInvCheck tiItems [{ acctUnique with schemaRef := "role" }] != [])
    "tableInv: a variant cannot take a table invariant"
  _ ← assert (tableInvCheck tiItems
      [{ acctUnique with fields := [⟨"id", .u64⟩] }] != [])
    "tableInv: stale field snapshot rejected"
  _ ← assertEq "tableInv: missing aggregation field rejected (exact diag)"
    (tableInvCheck tiItems [{ acctUnique with agg := .unique "zz" }])
    ["field `zz` is not on record `acct` — did you mean: id?"]
  _ ← assertEq "tableInv: non-u64 sum column rejected (exact diag)"
    (tableInvCheck tiItems [{ acctConservation with agg := .sum "nick" 150 }])
    ["field `nick` has type `SchemaLang.Ty.string` — the conservation sum reads a u64 column (v1)"]
  _ ← assertEq "tableInv: duplicate name rejected (exact diag)"
    (tableInvCheck tiItems [acctUnique, acctUnique])
    ["duplicate table-invariant name `acct-ids-unique`"]
  -- the obligation VIEW: enumeration, labels, computed tiers, provenance
  _ ← assertEq "tableObligations: one obligation per declaration"
    ((tableObligations tiDecls).map (·.label))
    ["acct-ids-unique", "acct-conserves", "acct-bounded", "acct-exact"]
  _ ← assertEq "tableObligations: the computed tier is decidableNow"
    ((tableObligations tiDecls).map (·.tier))
    [.decidableNow, .decidableNow, .decidableNow, .decidableNow]
  _ ← assertEq "tableObligations: provenance is the name"
    ((tableObligations tiDecls).map (·.provenance))
    [("acct-ids-unique".toName), ("acct-conserves".toName),
      ("acct-bounded".toName), ("acct-exact".toName)]
  -- the discharge: the computed tier FIRES on a provided table
  _ ← assertEq "tableObl: conservation discharges on the pre-transfer table"
    (acctConsObligation.discharge (some acctPre)) (some (.decided true))
  _ ← assertEq "tableObl: the evidence's tier IS the obligation's"
    ((acctConsObligation.discharge (some acctPre)).map (·.tier))
    (some .decidableNow)
  -- NEGATIVE CONTROLS (the loud refusal — no fabricated evidence)
  _ ← assertEq "tableObl: the sabotaged table REFUSES (loud)"
    (acctConsObligation.discharge (some acctSabotaged)) none
  _ ← assertEq "tableObl: no provided table REFUSES (loud)"
    (acctConsObligation.discharge none) none
  _ ← assertEq "tableObl: oracleSwept REFUSES (unwired, loud)"
    (acctConsOracle.discharge (some acctPre)) none
  _ ← assertEq "tableObl: guestVerified REFUSES (no v1 witness — design §7.1)"
    (acctConsGuest.discharge (some acctPre)) none
  _ ← assert (acctConsObligation.discharge (some acctPre)
      != acctConsObligation.discharge (some acctSabotaged))
    "tableObl: discharge DISTINGUISHES sound from sabotaged (non-vacuity)"
  -- the checks themselves, beyond the pinned fixture
  _ ← assert (acctUnique.agg.check acctPre) "unique: distinct ids pass"
  _ ← assert (!acctUnique.agg.check [acctRow 1 100, acctRow 1 999])
    "unique: duplicate ids FAIL — the row-set is a FUNCTION from key to row"
  _ ← assert (acctBounded.agg.check acctPre) "count ≤ 2: holds at 2 rows"
  _ ← assert (!acctBounded.agg.check (acctPre ++ [acctRow 3 0]))
    "count ≤ 2: 3 rows FAIL"
  _ ← assert (acctExact.agg.check acctPre) "count = 2: holds"
  _ ← assert (!acctExact.agg.check [acctRow 1 100]) "count = 2: 1 row FAILS"
  _ ← assert (acctConservation.checkOn acctPre)
    "checkOn: the guarded executor fires at the item's own fields"
  _ ← assert (!acctConservation.checkOn acctSabotaged)
    "checkOn: sabotage refuses through the guard too"
  _ ← assert (!acctConservation.checkOn ([.cons (.string "s") .nil] : List (RowVals plainFields)))
    "checkOn: a table for another schema REFUSES (never misreads)"
  .ok ()

end TableInvSweep

/-! ## The update language v2 (W8.3): multi-SET, INSERT, DELETE

The surface: `schema_update` grew the clause list — multi-column SET
(`c₁ := e₁, c₂ := e₂`), INSERT of a full row (`+ (e₁, …, eₙ)`, in field
order, expressions read the guarded row — the INSERT-SELECT reading),
DELETE (`-`). Insert/delete need the record's DECLARED key (W8.2 —
resolved from the keys registry at elaboration; a keyless record is an
elaboration error). The key column is not writable (a key change is a
delete + insert). The v1 surface (one SET clause, no insert/delete)
ALSO registers the v1 row — `updateItemExt` stays the emitters' source
(the byte-tie holds; the v1 count pins above re-assert it).

The laws (SchemaLang.Update2, all kernel-checked):
- `applySets_perm` — clause-order freedom (distinct names),
- `apply2_comm` / `apply2_comm_perm` — the two-update order-freedom
  under `Update2Compat` (the honest disjoint-keys premise), equality
  for insert-free pairs, permutation in general;
- `apply2_eq_foldDeltas` — the effect = the delta fold (Delta.lean's
  change shape), under `KeyCoherent`;
- the obligation view: keyed updates carry a key-uniqueness
  PRESERVATION obligation at `decidableNow`; a duplicate-key insert
  REFUSES (no fabricated evidence).
-/

-- The fixture record + the v2 registrations live at TOP LEVEL (the
-- registries key on FULL Lean names — inside a namespace the command's
-- ident would not resolve). The mirrors/laws/checks ride the namespace.

/-- The fixture record: registered, with a DECLARED key (the v2 gates'
    subject). -/
@[schema]
structure Upd2Entry where
  id : UInt64
  email : String
  age : UInt64

schema_keys for Upd2Entry := primary id

-- the v2 registrations (the positive lane)

-- multi-SET, guarded: bump age, echo email (the second clause reads
-- the column it writes — the batch law reads the ORIGINAL row)
schema_update upd2Promote for Upd2Entry
  age := VExpr.lit 1, email := VExpr.colOf "email"
  where VExpr.gt (VExpr.colOf "age") (VExpr.lit 0)

-- INSERT: a full row per guarded row (the key from the template's `id`
-- position — the declared key)
schema_update upd2DupAsNine for Upd2Entry
  + (VExpr.lit 9, VExpr.colOf "email", VExpr.colOf "age")
  where VExpr.gt (VExpr.colOf "age") (VExpr.lit 100)

-- DELETE by guard
schema_update upd2Retire for Upd2Entry
  - where VExpr.gt (VExpr.colOf "id") (VExpr.lit 150)

-- DELETE + INSERT (the upsert reading — a same-key replace: the row
-- leaves and the fresh row lands, deterministically)
schema_update upd2Rekey for Upd2Entry
  -, + (VExpr.lit 7, VExpr.colOf "email", VExpr.lit 0)
  where VExpr.eq (VExpr.colOf "id") (VExpr.lit 7)

-- the NEGATIVE controls (the command's gates — each fails THIS
-- module's build if it stops failing)

/-- error: schema_update `upd2BadKey`: insert/delete updates need `User`'s DECLARED key (W8.2) — register it first (`schema_keys for User := primary <field>`) -/
#guard_msgs in
schema_update upd2BadKey for User - where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

/-- error: schema_update `upd2DupInsert`: duplicate insert clause — one `+ (…)` per update -/
#guard_msgs in
schema_update upd2DupInsert for Upd2Entry
  + (VExpr.lit 1, VExpr.colOf "email", VExpr.lit 0),
    + (VExpr.lit 2, VExpr.colOf "email", VExpr.lit 0)
  where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

/-- error: schema_update `upd2DupCol`: duplicate set column `age` — the multi-write's columns must be distinct (the clause order is unobservable under that premise) -/
#guard_msgs in
schema_update upd2DupCol for Upd2Entry
  age := VExpr.lit 1, age := VExpr.lit 2
  where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

/-- error: schema_update `upd2WritesKey`: `id` is `Upd2Entry`'s declared key — the key column cannot be written (a key change is a delete + insert) -/
#guard_msgs in
schema_update upd2WritesKey for Upd2Entry id := VExpr.lit 0
  where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

/-- error: schema_update `upd2ShortRow`: the insert row has 1 fields — `Upd2Entry` has 3 (a FULL row, in field order) -/
#guard_msgs in
schema_update upd2ShortRow for Upd2Entry
  + (VExpr.lit 1)
  where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

/-- error: schema_update `upd2WrongInsert`: the insert row's field `email` has type SchemaLang.Ty.u64 — the field is SchemaLang.Ty.string — each insert expression must have the FIELD'S OWN TYPE (the GADT gate) -/
#guard_msgs in
schema_update upd2WrongInsert for Upd2Entry
  + (VExpr.lit 1, VExpr.lit 0, VExpr.lit 0)
  where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

/-- error: schema_update `upd2VolatileInsert`: func `updClockFn` is volatile but `schema_update upd2VolatileInsert` requires purity — valid determinisms in a pure context: pure, stable -/
#guard_msgs in
schema_update upd2VolatileInsert for Upd2Entry
  + (VExpr.lit (updClockFn 1), VExpr.colOf "email", VExpr.lit 0)
  where VExpr.eq (VExpr.lit 0) (VExpr.lit 0)

-- the registration pins: the v2 registry accumulates EVERY
-- `schema_update` (Demo's three, the Tests' determinism probe, the
-- four v2 rows above); the v1 registry holds EXACTLY the v1-shaped
-- rows (the byte-tie)
open Lean Elab Command in
run_cmd do
  let ups := SchemaLang.Meta.registeredUpdates2 (← getEnv)
  unless ups.length == 8 do
    throwError s!"expected 8 registered v2 updates, got {ups.length}"
  unless (ups.map (·.update.name)) == ["reset_id", "echo_email", "self_bump",
      "updPureCall", "upd2Promote", "upd2DupAsNine", "upd2Retire", "upd2Rekey"] do
    throwError s!"v2 registry names out of sync: {ups.map (·.update.name)}"
  -- the key adoption: Demo's rows are keyless (User has no declared
  -- keys); the Upd2Entry rows carry the DECLARED key
  unless (ups.map (·.update.key?)) == [none, none, none, none,
      some "id", some "id", some "id", some "id"] do
    throwError "v2 registry: the declared-key adoption is wrong"
  -- the v1 registry (the emitters' source): EXACTLY the v1-shaped four
  let ups1 := SchemaLang.Meta.registeredUpdates (← getEnv)
  unless ups1.length == 4 do
    throwError s!"v1 registry drifted: expected 4 rows, got {ups1.length}"
  -- the registration-emitted `Update2Pure` instances exist
  for n in ["reset_id", "upd2Promote", "upd2Rekey"] do
    let base := ((`SchemaLang).str "instUpdate2Pure").str n
    unless (← getEnv).contains base do
      throwError s!"instUpdate2Pure.{n}: the emitted instance is missing"

namespace Update2Sweep

/-- The fixture schema (the mirrors' index — `abbrev`, the
    reducibility rule). -/
abbrev upd2Fields : List Field := [⟨"id", .u64⟩, ⟨"email", .string⟩, ⟨"age", .u64⟩]

/-- A fixture row. -/
def upd2Row (i : UInt64) (e : String) (a : UInt64) : RowVals upd2Fields :=
  .cons (.u64 i) (.cons (.string e) (.cons (.u64 a) .nil))

def upd2Id (row : RowVals upd2Fields) : UInt64 := evalU (.colOf "id") row
def upd2Age (row : RowVals upd2Fields) : UInt64 := evalU (.colOf "age") row
def upd2Email (row : RowVals upd2Fields) : String :=
  match evalV (.colOf "email") row with | .string s => s | _ => ""

/-- The SET clauses, standalone (the Law-1 fixture needs them
    reorderable). -/
def upd2SetAge : SetClause upd2Fields :=
  { field := ⟨"age", .u64⟩, path := .there (.there .here), value := .lit 1 }
def upd2SetEmail : SetClause upd2Fields :=
  { field := ⟨"email", .string⟩, path := .there .here, value := .colOf "email" }

/-- The mirrors of the registered v2 rows (the runtime pins evaluate
    THESE; the run_cmd above pins the registration). -/
def upd2PromoteMirror : Update2Item upd2Fields :=
  { name := "upd2Promote", record := "Upd2Entry"
  , guard := .gt (.colOf "age") (.lit 0)
  , sets := [upd2SetAge, upd2SetEmail], key? := some "id" }

def upd2DupMirror : Update2Item upd2Fields :=
  { name := "upd2DupAsNine", record := "Upd2Entry"
  , guard := .gt (.colOf "age") (.lit 100), sets := [], key? := some "id"
  , insert? := some (.cons (.lit 9)
      (.cons (.colOf "email") (.cons (.colOf "age") .nil))) }

def upd2RetireMirror : Update2Item upd2Fields :=
  { name := "upd2Retire", record := "Upd2Entry"
  , guard := .gt (.colOf "id") (.lit 150), sets := [], key? := some "id"
  , delete := true }

def upd2RekeyMirror : Update2Item upd2Fields :=
  { name := "upd2Rekey", record := "Upd2Entry"
  , guard := .eq (.colOf "id") (.lit 7), sets := [], key? := some "id"
  , insert? := some (.cons (.lit 7)
      (.cons (.colOf "email") (.cons (.lit 0) .nil)))
  , delete := true }

/-- A duplicate-key inserter (the obligation REFUSAL fixture): the
    unconditional guard fires on the default row and the template's
    key is the default's OWN key (0) — the post-update table has a
    duplicate key. -/
def upd2DupKeyMirror : Update2Item upd2Fields :=
  { name := "dup-key", record := "Upd2Entry"
  , guard := .eq (.lit 0) (.lit 0), sets := [], key? := some "id"
  , insert? := some (.cons (.lit 0)
      (.cons (.colOf "email") (.cons (.colOf "age") .nil))) }

/-! ### The laws, exercised -/

/-- LAW 1, exercised: the SET clause order is unobservable. -/
theorem upd2_clause_order_free (r : RowVals upd2Fields) :
    applySets [upd2SetAge, upd2SetEmail] r
      = applySets [upd2SetEmail, upd2SetAge] r :=
  applySets_perm (List.Perm.swap _ _ []) (by decide) r

/-- The promote/retire fixture: two rows (one retired). -/
def upd2TablePR : List (RowVals upd2Fields) :=
  [upd2Row 1 "a" 5, upd2Row 200 "b" 7]

/-- The compat pack for the fixture, DECIDED field by field (every
    premise is decidable over the concrete table; the `insertSep`
    fields' antecedents are false — no inserts here). -/
def upd2CompatPR : Update2Compat upd2PromoteMirror upd2RetireMirror upd2TablePR where
  ni₁₂ := by decide
  ni₂₁ := by decide
  setDisj := by decide
  refuse₁₂ := by decide
  refuse₂₁ := by decide
  insertSep₁₂ := fun h => absurd h (by decide)
  insertSep₂₁ := fun h => absurd h (by decide)

/-- LAW 5b, exercised: the two updates compute the SAME table in
    either order (plain equality — no inserts). -/
theorem upd2_order_free_eq :
    upd2PromoteMirror.apply (upd2RetireMirror.apply upd2TablePR)
      = upd2RetireMirror.apply (upd2PromoteMirror.apply upd2TablePR) :=
  apply2_comm upd2CompatPR rfl rfl

/-- The two-insert fixtures (disjoint key-guards). -/
def upd2InsAMirror : Update2Item upd2Fields :=
  { name := "insA", record := "Upd2Entry"
  , guard := .eq (.colOf "id") (.lit 1), sets := [], key? := some "id"
  , insert? := some (.cons (.lit 10)
      (.cons (.colOf "email") (.cons (.lit 0) .nil))) }
def upd2InsBMirror : Update2Item upd2Fields :=
  { name := "insB", record := "Upd2Entry"
  , guard := .eq (.colOf "id") (.lit 2), sets := [], key? := some "id"
  , insert? := some (.cons (.lit 20)
      (.cons (.colOf "email") (.cons (.lit 0) .nil))) }

def upd2Table12 : List (RowVals upd2Fields) :=
  [upd2Row 1 "a" 5, upd2Row 2 "b" 6]

/-- The two-insert compat pack (each side's guard refuses the other's
    inserted row — the inserted keys are 10/20, the guards read 1/2). -/
def upd2CompatIns : Update2Compat upd2InsAMirror upd2InsBMirror upd2Table12 where
  ni₁₂ := by decide
  ni₂₁ := by decide
  setDisj := by decide
  refuse₁₂ := by decide
  refuse₂₁ := by decide
  insertSep₁₂ := fun _ h => absurd h (by decide)
  insertSep₂₁ := fun _ h => absurd h (by decide)

/-- LAW 5a, exercised: two insert updates PERMUTE the final table (the
    insert blocks swap — the tick's row-order invariance). -/
theorem upd2_order_free_perm :
    (upd2InsAMirror.apply (upd2InsBMirror.apply upd2Table12)).Perm
      (upd2InsBMirror.apply (upd2InsAMirror.apply upd2Table12)) :=
  apply2_comm_perm upd2CompatIns

/-- The same-key conflict fixtures: an inserter whose fresh rows carry
    key 7, and a delete of id-7 rows. -/
def upd2Ins7Mirror : Update2Item upd2Fields :=
  { name := "ins7", record := "Upd2Entry"
  , guard := .gt (.colOf "age") (.lit 0), sets := [], key? := some "id"
  , insert? := some (.cons (.lit 7)
      (.cons (.colOf "email") (.cons (.colOf "age") .nil))) }
def upd2Del7Mirror : Update2Item upd2Fields :=
  { name := "del7", record := "Upd2Entry"
  , guard := .eq (.colOf "id") (.lit 7), sets := [], key? := some "id"
  , delete := true }

def upd2Tab1 : List (RowVals upd2Fields) := [upd2Row 1 "a" 5]

/-- NEGATIVE (the premise's non-vacuity): the inserter's fresh row
    CARRIES key 7 — the deleter's guard does NOT refuse it — the
    `refuse` premise decides FALSE. -/
theorem upd2_sameKey_refuse_fails :
    ¬ (∀ r ∈ upd2Tab1, (upd2Ins7Mirror.newRow r).elim true
        (fun new => !validates upd2Del7Mirror.guard new) = true) := by decide

/-- The same-key conflict is ORDER-DEPENDENT (the truth the law
    states — later-wins is NOT reachable here; the row order
    observably differs). Insert-then-delete drops the fresh row;
    delete-then-insert keeps it. -/
theorem upd2_sameKey_order_matters :
    (upd2Ins7Mirror.apply (upd2Del7Mirror.apply upd2Tab1)).map upd2Id = [1, 7]
      ∧ (upd2Del7Mirror.apply (upd2Ins7Mirror.apply upd2Tab1)).map upd2Id = [1] :=
  ⟨rfl, rfl⟩

/-- THE ROW-LEVEL LOWERING, exercised (the keep channel IS the patch
    fold): on the rekey mirror (delete + insert). -/
theorem upd2_keepRow_is_deltaFold (r : RowVals upd2Fields) :
    upd2RekeyMirror.keepRow r
      = (upd2RekeyMirror.lowerRow r).foldl (fun acc d => d.patchKeep acc)
          (some r) :=
  keepRow_eq_fold_patchKeep upd2RekeyMirror "id" rfl r
    (fun _ _ => by cases r with | cons v vs => exact ⟨_, rfl⟩)

/-- The insert channel's row-level correspondence. -/
theorem upd2_newRow_is_deltaFold (r : RowVals upd2Fields) :
    upd2RekeyMirror.newRow r
      = (upd2RekeyMirror.lowerRow r).foldl (fun acc d => d.patchNew acc) none :=
  newRow_eq_fold_patchNew upd2RekeyMirror "id" rfl r

/-- The correspondence fixture: the insert mirror over a two-row table
    (one guarded row; keys 1 and 200 distinct; the fresh key 9 free). -/
def upd2TableAB : List (RowVals upd2Fields) :=
  [upd2Row 1 "a" 5, upd2Row 200 "b" 150]

/-- The coherence pack, discharged: `keyOf`/`proj`/`nodup2` by
    computation; `fresh` by the per-row case split (the insert fires
    only on the guarded row). -/
def upd2CohDup : KeyCoherent upd2DupMirror "id" upd2TableAB where
  keyOf := rfl
  keyImmutable := by decide
  proj := by decide
  -- (`decide` cannot evaluate `FieldVal.beq` — the encoder's
  -- `encVarNat` is wf-recursive, opaque to the kernel's whnf — so the
  -- distinctness rides `FieldVal.beq_u64_ne`, the module's own
  -- u64-key specialisation. `keyImgs` itself reduces by rfl.)
  nodup2 := by
    have himgs : keyImgs upd2Fields "id" upd2TableAB
        = [⟨.u64, .u64 1⟩, ⟨.u64, .u64 200⟩] := rfl
    rw [himgs]
    have h₁ : FieldVal.beq ⟨.u64, .u64 1⟩ ⟨.u64, .u64 200⟩ = false :=
      FieldVal.beq_u64_ne (by decide)
    have h₂ : FieldVal.beq ⟨.u64, .u64 200⟩ ⟨.u64, .u64 1⟩ = false :=
      FieldVal.beq_u64_ne (by decide)
    simp [FieldVal.nodup2, h₁, h₂]
  fresh := by
    intro r hr new hnew
    have hr' : r = upd2Row 1 "a" 5 ∨ r = upd2Row 200 "b" 150 := by
      simpa [upd2TableAB] using hr
    cases hr' with
    | inl h =>
        subst h
        have hn : upd2DupMirror.newRow (upd2Row 1 "a" 5) = none := rfl
        rw [hn] at hnew
        nomatch hnew
    | inr h =>
        subst h
        have hn : upd2DupMirror.newRow (upd2Row 200 "b" 150)
            = some (upd2Row 9 "b" 150) := rfl
        rw [hn] at hnew
        cases hnew
        intro k' hpk wk hwk
        have hp : RowVals.project? upd2Fields (upd2Row 9 "b" 150) "id"
            = some ⟨.u64, .u64 9⟩ := rfl
        rw [hp] at hpk
        cases hpk
        have himgs : keyImgs upd2Fields "id" upd2TableAB
            = [⟨.u64, .u64 1⟩, ⟨.u64, .u64 200⟩] := rfl
        rw [himgs] at hwk
        have hwk' : wk = ⟨.u64, .u64 1⟩ ∨ wk = ⟨.u64, .u64 200⟩ := by
          simpa using hwk
        cases hwk' with
        | inl hw1 =>
            subst hw1
            exact ⟨FieldVal.beq_u64_ne (by decide),
              FieldVal.beq_u64_ne (by decide)⟩
        | inr hw2 =>
            subst hw2
            exact ⟨FieldVal.beq_u64_ne (by decide),
              FieldVal.beq_u64_ne (by decide)⟩

/-- LAW 6, exercised: the update's table effect IS the fold of its
    per-row deltas through the keyed table semantics. -/
theorem upd2_lowering :
    upd2DupMirror.apply upd2TableAB
      = (upd2TableAB.flatMap upd2DupMirror.lowerRow).foldl
          (fun t d => applyRowDelta "id" d t) upd2TableAB :=
  apply2_eq_foldDeltas upd2DupMirror "id" upd2TableAB upd2CohDup

/-! ### The obligation view -/

/-- upd2Promote's obligation, hand-assembled (the enumeration pin). -/
def promoteObligation : Update2Obligation :=
  { label := "Upd2Entry.upd2Promote-preserves-unique(id)"
  , tier := .decidableNow
  , payload := .keyUnique upd2Fields upd2PromoteMirror "id"
  , provenance := "Upd2Entry".toName }

/-- The pinned-table claim HOLDS (the default row's guard refuses —
    the antecedent fires, the consequent is the untouched singleton) —
    the `.decided true` discharge IS the claim (the soundness theorem,
    CITED — the `userKeyUnique_holds` pattern). -/
theorem promoteObligation_holds : promoteObligation.decidableClaim :=
  promoteObligation.discharge_decidableNow_sound rfl rfl

/-- The completeness theorem, CITED: the true claim FIRES the backend. -/
theorem promoteObligation_discharges :
    promoteObligation.discharge = some (.decided true) :=
  promoteObligation.discharge_decidableNow_of_claim rfl promoteObligation_holds

/-- The duplicate-key insert's obligation: the claim decides FALSE
    (the pinned table gains a second key-0 row) and the backend
    REFUSES — no fabricated evidence. -/
def dupKeyObligation : Update2Obligation :=
  { label := "Upd2Entry.dup-key-preserves-unique(id)"
  , tier := .decidableNow
  , payload := .keyUnique upd2Fields upd2DupKeyMirror "id"
  , provenance := "Upd2Entry".toName }

-- the claim decides FALSE: the post-update table's key images are
-- [0, 0] — `nodup` refuses them (the refl beq is kernel-computable;
-- the DISTINCT-value beq is not — the wf-recursive encoder — which is
-- why this cannot be `rfl`/`decide` like the promote pin above)
theorem dupKey_claim_false : ¬ dupKeyObligation.decidableClaim := by
  unfold Update2Obligation.decidableClaim dupKeyObligation
  intro hc
  have hc' : (if KeyDecl.uniqueOn ⟨"Upd2Entry", upd2Fields, "id", []⟩
                [upd2Row 0 "" 0] = true then
              KeyDecl.uniqueOn ⟨"Upd2Entry", upd2Fields, "id", []⟩
                (upd2DupKeyMirror.apply [upd2Row 0 "" 0])
            else true) = true := hc
  have hant : KeyDecl.uniqueOn ⟨"Upd2Entry", upd2Fields, "id", []⟩
      [upd2Row 0 "" 0] = true := rfl
  rw [if_pos hant] at hc'
  have hkeys : KeyDecl.keyImages? ⟨"Upd2Entry", upd2Fields, "id", []⟩
      (upd2DupKeyMirror.apply [upd2Row 0 "" 0])
      = some [⟨.u64, .u64 0⟩, ⟨.u64, .u64 0⟩] := rfl
  simp only [KeyDecl.uniqueOn] at hc'
  rw [hkeys] at hc'
  have hc'' : FieldVal.nodup [⟨.u64, .u64 0⟩, ⟨.u64, .u64 0⟩] = true := hc'
  have hnd : FieldVal.nodup [⟨.u64, .u64 0⟩, ⟨.u64, .u64 0⟩] = false := by
    simp [FieldVal.nodup, FieldVal.beq_refl]
  rw [hnd] at hc''
  exact absurd hc'' (by decide)

theorem dupKey_refused : dupKeyObligation.discharge = none := by
  unfold Update2Obligation.discharge
  cases hd : decide dupKeyObligation.decidableClaim with
  | true => exact absurd (of_decide_eq_true hd) dupKey_claim_false
  | false => rfl

/-! ### The runtime lane -/

def update2Checks : CheckResult := do
  -- the multi-SET: the guarded row takes BOTH writes (values read the
  -- ORIGINAL row — the email echo reads the pre-write email)
  _ ← assertEq "v2 multi-set: ids"
    ((upd2PromoteMirror.apply upd2TablePR).map upd2Id) [1, 200]
  _ ← assertEq "v2 multi-set: ages written"
    ((upd2PromoteMirror.apply upd2TablePR).map upd2Age) [1, 1]
  _ ← assertEq "v2 multi-set: emails self-read (batch)"
    ((upd2PromoteMirror.apply upd2TablePR).map upd2Email) ["a", "b"]
  -- the guard refuses: age 0 fails `age > 0`, the row passes through
  _ ← assertEq "v2 multi-set: refused row untouched"
    ((upd2PromoteMirror.apply [upd2Row 1 "a" 0]).map upd2Age) [0]
  -- LAW 1 at runtime: the swapped clause list computes the same rows
  _ ← assertEq "v2 law-1: clause order unobservable (ages)"
    (([upd2Row 1 "a" 5].map (applySets [upd2SetAge, upd2SetEmail])).map upd2Age)
    (([upd2Row 1 "a" 5].map (applySets [upd2SetEmail, upd2SetAge])).map upd2Age)
  -- INSERT: the fresh row is APPENDED; its non-key fields are read
  -- from the GUARDED row (the INSERT-SELECT batch read)
  _ ← assertEq "v2 insert: appended (ids)"
    ((upd2DupMirror.apply upd2TableAB).map upd2Id) [1, 200, 9]
  _ ← assertEq "v2 insert: the fresh row reads the guarded row"
    ((upd2DupMirror.apply upd2TableAB).map upd2Email) ["a", "b", "b"]
  _ ← assertEq "v2 insert: the fresh row reads the guarded row (age)"
    ((upd2DupMirror.apply upd2TableAB).map upd2Age) [5, 150, 150]
  -- DELETE: the guarded row leaves
  _ ← assertEq "v2 delete: the id-200 row retires"
    ((upd2RetireMirror.apply upd2TablePR).map upd2Id) [1]
  -- DELETE + INSERT, same key (the upsert reading): the row leaves,
  -- the fresh row lands — deterministically; the template read the
  -- ORIGINAL row's email
  _ ← assertEq "v2 rekey: the row is replaced"
    ((upd2RekeyMirror.apply [upd2Row 7 "x" 3]).map upd2Id) [7]
  _ ← assertEq "v2 rekey: the fresh row's email came from the deleted row"
    ((upd2RekeyMirror.apply [upd2Row 7 "x" 3]).map upd2Email) ["x"]
  _ ← assertEq "v2 rekey: the fresh row's age is the template's"
    ((upd2RekeyMirror.apply [upd2Row 7 "x" 3]).map upd2Age) [0]
  -- LAW 5b at runtime: the two orders agree (ids)
  _ ← assertEq "v2 order-free (set+delete): both orders agree"
    ((upd2PromoteMirror.apply (upd2RetireMirror.apply upd2TablePR)).map upd2Id)
    ((upd2RetireMirror.apply (upd2PromoteMirror.apply upd2TablePR)).map upd2Id)
  -- LAW 5a at runtime: the insert orders PERMUTE
  let insAB := (upd2InsAMirror.apply (upd2InsBMirror.apply upd2Table12)).map upd2Id
  let insBA := (upd2InsBMirror.apply (upd2InsAMirror.apply upd2Table12)).map upd2Id
  _ ← assertEq "v2 perm: B-then-A's ids" insAB [1, 2, 20, 10]
  _ ← assertEq "v2 perm: A-then-B's ids" insBA [1, 2, 10, 20]
  _ ← assert (insAB != insBA)
    "v2 perm: the orders differ as LISTS (the law is a permutation)"
  -- the same-key negative: order-dependence, executed
  _ ← assertEq "v2 same-key: delete-then-insert keeps the fresh row"
    ((upd2Ins7Mirror.apply (upd2Del7Mirror.apply upd2Tab1)).map upd2Id) [1, 7]
  _ ← assertEq "v2 same-key: insert-then-delete drops the fresh row"
    ((upd2Del7Mirror.apply (upd2Ins7Mirror.apply upd2Tab1)).map upd2Id) [1]
  -- LAW 6 at runtime: the delta fold reproduces the table effect
  _ ← assertEq "v2 lowering: the delta fold = the update (ids)"
    (((upd2TableAB.flatMap upd2DupMirror.lowerRow).foldl
        (fun t d => applyRowDelta "id" d t) upd2TableAB).map upd2Id)
    [1, 200, 9]
  -- the lowering's delta SHAPE (Delta.lean's contract): remove carries
  -- the KEY image, insert the full row
  _ ← assert (match upd2RekeyMirror.lowerRow (upd2Row 7 "x" 3) with
    | [.remove ⟨.u64, .u64 7⟩, .insert _] => true | _ => false)
    "v2 lowering: rekey lowers to [remove ⟨key⟩, insert ⟨row⟩]"
  _ ← assert (match upd2DupMirror.lowerRow (upd2Row 1 "a" 5) with
    | [] => true | _ => false)
    "v2 lowering: a guard-refused row lowers to NO deltas"
  -- the registered-row cast discipline: a matching table executes, a
  -- foreign one passes through untouched
  let su : SomeUpdate2 := { fields := upd2Fields, update := upd2RetireMirror }
  _ ← assertEq "SomeUpdate2.apply: matching table executes"
    ((su.apply upd2TablePR).map upd2Id) [1]
  _ ← assert (match su.apply [RowVals.nil] with | [_] => true | _ => false)
    "SomeUpdate2.apply: a foreign table passes through"
  -- the obligation view: enumeration + computed tiers (over the
  -- mirrors — the run_cmd above pins the registry)
  let obs := update2Obligations
    [ { fields := upd2Fields, update := upd2PromoteMirror }
    , { fields := upd2Fields, update := upd2DupMirror }
    , { fields := upd2Fields, update := upd2RetireMirror }
    , { fields := upd2Fields, update := upd2RekeyMirror } ]
  _ ← assertEq "v2 obligations: one per keyed update"
    (obs.map (·.label))
    [ "Upd2Entry.upd2Promote-preserves-unique(id)"
    , "Upd2Entry.upd2DupAsNine-preserves-unique(id)"
    , "Upd2Entry.upd2Retire-preserves-unique(id)"
    , "Upd2Entry.upd2Rekey-preserves-unique(id)" ]
  _ ← assertEq "v2 obligations: the computed tier"
    (obs.map (·.tier))
    [.decidableNow, .decidableNow, .decidableNow, .decidableNow]
  -- a KEYLESS update carries NO obligation (the key? = none shape —
  -- the Demo rows' shape)
  _ ← assertEq "v2 obligations: keyless updates have none"
    ((Update2Item.obligations { upd2PromoteMirror with key? := none }).map
      (·.label)) []
  -- the discharge: fires on the preservation claim, REFUSES the
  -- duplicate-key insert (the loud gap — no fabricated evidence)
  _ ← assertEq "v2 obligation: promote discharges"
    promoteObligation.discharge (some (.decided true))
  _ ← assertEq "v2 obligation: promote's evidence tier"
    (promoteObligation.discharge.map (·.tier)) (some .decidableNow)
  _ ← assertEq "v2 obligation: the duplicate-key insert REFUSES"
    dupKeyObligation.discharge none
  _ ← assert (promoteObligation.discharge != dupKeyObligation.discharge)
    "v2 obligation: discharge DISTINGUISHES sound from broken"
  .ok ()

end Update2Sweep

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
  let provenance ← provenanceChecks
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
     , ("genRust", genRustChecks ctx)
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
     , provenance
     , ("validate", validateChecks)
     , ("strlen", strlenChecks)
     , ("exprLang", exprLangChecks)
     , ("exprEmit", exprEmitChecks)
     , ("dsl", dslChecks)
     , ("variant", variantChecks)
     , ("invariantChecks", invariantChecks ctx.invariants)
     , ("decidableNow", decidableNowChecks)
     , ("updateChecks", updateChecks ctx)
     , ("trace", traceChecks)
     , ("migration", migrationChecks)
     , ("subschema", subschemaChecks)
     , ("batch", batchChecks)
     , ("enumWire", enumWireChecks)
     , ("wireCodec", wireCodecChecks)
     , ("rowGen", rowGenChecks)
     , ("docs", docsChecks)
    , ("moduleDocs", moduleDocsChecks)
     , ("diagGolden", diagGoldenChecks)
     , ("witness", WitnessSweep.witnessChecks)
     , ("witnessCheck", WitnessCheckSweep.witnessCheckChecks)
     , ("guestVerified", GuestVerifiedSweep.guestVerifiedChecks)
     , ("witnessEmit", WitnessEmitSweep.witnessEmitChecks)
     , ("migrationGate", MigrationGateSweep.migrationGateChecks)
     , ("mapSet", MapSetSweep.mapSetChecks)
     , ("keys", KeySweep.keyChecks)
     , ("tableInv", TableInvSweep.tableInvChecks)
     , ("update2", Update2Sweep.update2Checks)
     ])
  if code != 0 then return code
  -- the property sweep WITH its mandatory negative control
  -- (TestKit.PropSpec: the property must pass AND the sabotaged sibling
  -- must be caught — a vacuous sweep fails the gate)
  -- the generated enum wires' PropSpecs (Item.lean's three enums:
  -- the round-trip sweep + the mandatory tag+1 sabotage control)
  let specCode ← TestKit.runSpecs [PropSweep.spec, CodecValueSweep.spec,
    NullSem.wirePropSpec, Determinism.wirePropSpec, Delivery.wirePropSpec,
    -- W7.14: the derived wire codecs' RoundTripSpecs (the PropSpec bridge
    -- carries the sweep AND the mandatory byte-sabotage control)
    WireCodecFixture.roundTripSpec.propSpec, WireCodecOuter.roundTripSpec.propSpec]
  if specCode != 0 then return specCode
  -- W9.4: the witness artifact round trip THROUGH THE FILE — the
  -- committed byte-tied artifact's own row bytes, parsed back out,
  -- decoded + re-checked (the in-memory value is not the evidence)
  let witnessFileCode ← WitnessEmitSweep.artifactFileChecks
  if witnessFileCode != 0 then return witnessFileCode
  -- W9.1: the witness RoundTripSpec — the PropSpec bridge (sweep +
  -- mandatory byte-sabotage control) + the golden byte-tie
  WitnessSweep.witnessSpec.runIO (update := update)

/-! ## Debug commands (the author's REPL) — #guard_msgs smokes

The `#assertType` pattern's info-pins: each command's logged output is
pinned EXACTLY against the elab-time registry (Demo's rows, replayed
via import). `#guard_msgs (info)` fails elaboration on any drift, and —
because these commands only LOG — a misspelled-world pin also pins
GRACEFULNESS: if `#world gatway` ever threw, the build fails here.
No registry side effects: the pins are deterministic replays.
-/

/-- info: registered schema items (14):
  User : record user (4 fields)
  OrderItem : record order-item (3 fields)
  Order : record order (3 fields)
  Role : variant role (3 cases)
  OrderError : variant order-error (3 cases)
  getUser : func get-user(id: u64) -> option<user> delivery=once — u64 → option<user>. The body is a stub — the SIGNATURE is the spec;
  watchOrders : func watch-orders(into: order-error) -> future<list<user>> delivery=once — an order-error stream in, a user list out (async).
  Db : resource db — An opaque handle type: the schema records it as a resource.
  probeVolatileFn : func probe-volatile-fn(x: u32) -> u32 delivery=once — Probe: one ident arg sets the determinism axis only.
  probeBothAxesFn : func probe-both-axes-fn(x: option<u32>) -> option<u32> delivery=once — Probe: the dot-joined pair sets BOTH axes (either order).
  probeDefaultFn : func probe-default-fn(x: u32, y: u32) -> u32 delivery=once — Probe: no args — the defaults. (Two params: bodies of the one-param
  updClockFn : func upd-clock-fn(seed: u64) -> u64 delivery=once — The volatile probe: a clock-reading fn (the volatilities probe
  updPureFn : func upd-pure-fn(x: u64) -> u64 delivery=once — The pure probe: same shape, default determinism — registers clean
  Upd2Entry : record upd2-entry (3 fields) — The fixture record: registered, with a DECLARED key (the v2 gates' -/
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
record upd2-entry {
  id: u64,
  email: string,
  age: u64,
}
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
record upd2-entry {
  id: u64,
  email: string,
  age: u64,
}
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

/-! ## The circuit certificate pin (moved from `SchemaLang.Emit.Circuit`, W5.4)

Under the module system an imported theorem's `ConstantInfo` is not
`isTheorem` during a module file's elaboration, so the `#check_cert` pin
runs here (this file is not a module; drift = test build error). -/

#check_cert Dbsp.incrementalize_ok :
  ∀ {Func : (a b : Type) → [AddCommGroup a] → [AddCommGroup b] → Type}
    {a b : Type} [AddCommGroup a] [AddCommGroup b]
    {denoteF : Dbsp.CktDenote Func} (isLinear : Dbsp.IsLinearOracle Func)
    (_isLinearOk : ∀ {a b : Type} [AddCommGroup a] [AddCommGroup b] (f : Func a b),
      isLinear _ _ f = true → ∀ x y : a,
        denoteF _ _ f (x + y) = denoteF _ _ f x + denoteF _ _ f y)
    (f : Dbsp.Ckt Func a b),
    Dbsp.Ckt.denote denoteF (Dbsp.incrementalize isLinear f) =
      Dbsp.incremental (Dbsp.Ckt.denote denoteF f)

/-! ## W5.1 — `@[event_sourced]` (the event-log row: delta variant +
journal codec + replay + upcaster + laws + RewindableMachine, derived)

The attribute's own pin (the ledger package carries the full dogfood);
each generated surface exercised with its sabotaged negative control. -/

/-- The fixture: a flat-scalar record (the v1 fragment). -/
@[schema, event_sourced]
structure EsFixture where
  id : UInt64
  note : String
  amount : Int64
deriving BEq, Repr, DecidableEq

-- the delta variant + replay (positive): upsert by key, remove by key
#guard EsFixture.replay [.insert ⟨1, "a", 5⟩, .insert ⟨2, "b", 1⟩, .update ⟨1, "a", 9⟩, .remove 2] []
  == [⟨1, "a", 9⟩]

-- replay (negative control): a sabotaged log (the update dropped) does
-- NOT reconstruct the state — replay is faithful to the log
#guard EsFixture.replay [.insert ⟨1, "a", 5⟩, .insert ⟨2, "b", 1⟩, .remove 2] [] != [⟨1, "a", 9⟩]

-- the journal codec (positive): the log round-trips the wire
#guard EsFixture.esDecodeJournal?
    (EsFixture.esEncodeJournal [.insert ⟨1, "a", 5⟩, .remove 1])
  == some ([.insert ⟨1, "a", 5⟩, .remove 1], [])

-- the journal codec (negative control): a corrupted tag byte (9) does
-- not decode to the original event
#guard (match EsFixture.esDecodeEvent? (9 :: EsFixture.esEncodeEvent (.insert ⟨1, "a", 5⟩)) with
        | some (e, _) => e != .insert ⟨1, "a", 5⟩
        | none => true)

-- the machine (positive): the logged run's journal rewinds to the
-- initial table (rewind = the inverse deltas, the ChangeInversion row)
#guard (Machines.RewindableMachine.runLogged EsFixture.esMachine [⟨7, "m", 1⟩]
    [.insert ⟨1, "a", 5⟩, .update ⟨1, "a", 9⟩]).map
  (fun (_, ds, fin) => EsFixture.esMachine.rewind ds.reverse fin) == some [⟨7, "m", 1⟩]

-- the laws land as theorems (checked types — a stub would not elaborate)
#check @EsFixture.replay_snoc
#check @EsFixture.esJournal_roundtrip
#check @EsFixture.esDelta_inverse
#check @EsFixture.upcast_id

-- the fragment gate (negative control): a float field is a LOUD
-- elaboration error naming the field (no codec-closed round trip exists)
/-- error: @[event_sourced] `EsBadFloat`: field `x` has type SchemaLang.Ty.f64, outside the v1 event-sourcing fragment (flat scalars: Bool/UInt8–UInt64/Int8–Int64/String) — the journal codec needs the codec-closed round trip and the native↔row boxing needs a one-level `Value` ctor -/
#guard_msgs in
@[schema, event_sourced]
structure EsBadFloat where
  id : UInt64
  x : Float

/-! ## W8.2 — the `schema_keys` command + the `@[schema key.<field>]`
attr arg + the `@[event_sourced]` key migration (the meta lane)

The pure lane (checker/bridge/obligation pins) is `KeySweep` above.
Here: the declaration surfaces against the LIVE registry, and the
event-sourced lane's key read (`Item.keyOfWith` — the declared key
WINS when the attr arg declares it at registration time). -/

-- the command dogfood: declared = first field on the existing
-- event-sourced fixture (the ledger shape — the migration equivalence
-- says NOTHING changes)
schema_keys for EsFixture := primary id

-- the foreign-key surface: target declared FIRST (the
-- forward-reference rule)
@[schema]
structure KeyAuthor where
  id : UInt64
  nick : String

schema_keys for KeyAuthor := primary id

@[schema]
structure KeyPost where
  id : UInt64
  authorId : UInt64
  title : String

schema_keys for KeyPost := primary id, authorId → KeyAuthor

-- the registration pin: the command stored the DECLARED keys (the
-- registry read, not a hand mirror)
open Lean Elab Command in
run_cmd do
  let keys := SchemaLang.Meta.registeredKeys (← getEnv)
  let get (r : String) : CommandElabM SchemaLang.KeyDecl :=
    match keys.find? (·.record == r) with
    | some kd => pure kd
    | none => throwError s!"key declaration for `{r}` not registered"
  let es ← get "EsFixture"
  unless es.key == "id" && es.foreign.isEmpty do
    throwError "EsFixture: wrong declared key"
  let ka ← get "KeyAuthor"
  unless ka.key == "id" && ka.fields.map (·.name) == ["id", "nick"] do
    throwError "KeyAuthor: wrong declaration"
  let kp ← get "KeyPost"
  unless kp.key == "id"
      && kp.foreign == [{ field := "authorId", target := "KeyAuthor" }] do
    throwError "KeyPost: wrong declaration"

/-- The attr-arg dogfood: the primary key declared AT REGISTRATION
    (`@[schema key.code]`), so the event-sourced lane — which runs at
    declaration time — sees the DECLARED key, and it WINS over the
    first-field convention (`code` is the SECOND field). -/
@[schema key.code, event_sourced]
structure RekeyedFixture where
  note : String
  code : UInt64
deriving BEq, Repr, DecidableEq

-- the declared key WINS: esKey projects `code` (the second field; the
-- first-field convention would project `note` — a type error, so the
-- projection's TYPE is itself the pin)
#guard RekeyedFixture.esKey ⟨"a", 7⟩ = 7

-- the event semantics ride the declared key: two inserts with the
-- same CODE upsert (the note is payload, not identity)
#guard RekeyedFixture.replay [.insert ⟨"a", 1⟩, .insert ⟨"b", 1⟩] [] == [⟨"b", 1⟩]

-- NEGATIVE CONTROL: under the first-field convention the two inserts
-- would NOT upsert (distinct notes) — the replay above is the
-- declared key's behavior, not the convention's
#guard RekeyedFixture.replay [.insert ⟨"a", 1⟩, .insert ⟨"b", 1⟩] [] != [⟨"a", 1⟩, ⟨"b", 1⟩]

-- the lane's laws still land with a non-first-field key (checked
-- types — a stub would not elaborate)
#check @RekeyedFixture.replay_snoc
#check @RekeyedFixture.esJournal_roundtrip
#check @RekeyedFixture.esDelta_inverse

-- the conventional fixture is unchanged (the command declared the
-- first field — `keyOfWith_eq_keyOf_of_decl_head`)
#guard EsFixture.esKey ⟨1, "a", 5⟩ = 1

-- the elaboration gate, negative controls (the tightest tier — the
-- pure checker's diagnostics as ELABORATION errors):

/-- error: @[schema key.score] `KeyBadScalar`: key declaration for `KeyBadScalar`: key field `score` has type `SchemaLang.Ty.f64` — a key must inject from the KeyTy scalar sub-universe (W8.1): bool, u8, u16, u32, u64, i8, i16, i32, i64, string -/
#guard_msgs in
@[schema key.score]
structure KeyBadScalar where
  id : UInt64
  score : Float

/-- error: schema_keys for `EsFixture`: duplicate key declaration for `EsFixture` — one declaration per record -/
#guard_msgs in
schema_keys for EsFixture := primary id

/-- error: schema_keys: `KeyAuthorTypo` is not a registered record -/
#guard_msgs in
schema_keys for KeyPost := primary id, authorId → KeyAuthorTypo

/-! ## W8.8 — the `schema_table_invariant` command (the meta lane)

The pure lane (checker/obligation/discharge pins) is `TableInvSweep`
above. Here: the declaration surface against the LIVE registry — the
ledger-shaped fixture (the conservation surface's canonical client
shape), the registration pin, and the elaboration gate's negative
controls. -/

/-- The ledger-shaped fixture: accounts with a u64 stock. -/
@[schema]
structure AcctFixture where
  id : UInt64
  nick : String
  balance : UInt64

schema_table_invariant "acct-ids-unique" for AcctFixture := unique id
schema_table_invariant "acct-conserves" for AcctFixture := sum balance = 0
schema_table_invariant "acct-bounded" for AcctFixture := count ≤ 4
schema_table_invariant "acct-exact" for AcctFixture := count = 2

-- the registration pin: the command stored the declarations (the
-- registry read, not a hand mirror)
open Lean Elab Command in
run_cmd do
  let tis := SchemaLang.Meta.registeredTableInvariants (← getEnv)
  let get (n : String) : CommandElabM SchemaLang.TableInvItem :=
    match tis.find? (·.name == n) with
    | some ti => pure ti
    | none => throwError s!"table invariant `{n}` not registered"
  let u ← get "acct-ids-unique"
  unless u.schemaRef == "AcctFixture" && u.agg == .unique "id"
      && u.fields.map (·.name) == ["id", "nick", "balance"] do
    throwError "acct-ids-unique: wrong registration"
  let c ← get "acct-conserves"
  unless c.agg == .sum "balance" 0 do
    throwError "acct-conserves: wrong registration"
  let b ← get "acct-bounded"
  unless b.agg == .countLe 4 do throwError "acct-bounded: wrong registration"
  let e ← get "acct-exact"
  unless e.agg == .countEq 2 do throwError "acct-exact: wrong registration"

-- the elaboration gate, negative controls (the tightest tier — the
-- pure checker's diagnostics as ELABORATION errors):

/-- error: schema_table_invariant `acct-ids-unique`: duplicate table-invariant name `acct-ids-unique` -/
#guard_msgs in
schema_table_invariant "acct-ids-unique" for AcctFixture := unique id

/-- error: schema_table_invariant: `ZzzNope` is not a registered record -/
#guard_msgs in
schema_table_invariant "bad-record" for ZzzNope := unique id

/-- error: schema_table_invariant `bad-field`: field `zz` is not on record `AcctFixture` — did you mean: id? -/
#guard_msgs in
schema_table_invariant "bad-field" for AcctFixture := unique zz

/-- error: schema_table_invariant `bad-sum`: field `nick` has type `SchemaLang.Ty.string` — the conservation sum reads a u64 column (v1) -/
#guard_msgs in
schema_table_invariant "bad-sum" for AcctFixture := sum nick = 3
