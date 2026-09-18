/-
# SchemaLang.Emit.WitSweep — the SEEDED-random WIT fixtures (fuzz gap #3)

`WitFixture` emits 4 hand-pinned universes. The fuzz-gap audit's finding:
random ctor combinations (map/set assoc-list rendering under option
payloads, tensor flattening under async funcs, kebab collisions like
`FooBar` vs `foo-bar`, deep nesting, empty records/variants) are never
parse-checked — an emitter bug on an UNTRIED combination is invisible.
This module seeds N universes from a PINNED LCG seed (`TestKit.lcg`'s
recurrence, inlined) plus pinned corner universes, emits each as a WIT
fixture + a manifest entry recording the LOWERED shape (what
wit-parser must resolve, not the lossy Lean `Ty`), and lets the Rust
sweep (`wit_fixture_sweep.rs`) assert `parse (emit u) ≅ manifest u`.

Byte-tie: same law as every emitter — the fixtures under
`crates/steel-host/tests/fixtures/wit_sweep/` are committed, additive,
never hand-edited; drift fails `just gen-check`.

Deliberate exclusions: NO `.ty` named refs in the SEEDED corpus (a ref
needs anchored records per universe — the pinned universe check owns
name resolution; here the subject is STRUCTURAL rendering); NO
`delivery = stream` funcs (the universe check refuses list-shaped rets
under stream — the func generator keeps the default `once`); NO
future/stream in field position (`Ty.banAsync` — a WIT grammar law).
The `corner-kebab` universe was the audit's collision PROBE: three
distinct names that mangle to one WIT identifier — wit-parser rejected
the fixture, and that catch MOVED INTO the WF gate: the post-mangle
uniqueness rule (`Item.mangleCollDiags` ↔ `WellFormed`'s mangled nodup,
the bridge `mangleCollDiags_eq_nil_iff`) now refuses the universe at
ELABORATION, naming the colliding preimages (Tests pins the refusal).
The emitted corpus carries the gate's over-breadth controls instead:
`corner-kebab-near` (`foo-bar` vs `foo-bar2` — distinct post-mangle)
and `corner-min-variant` (the one-case variant; the zero-case sibling
refuses via `Item.check`'s `emptyVariant` arm).
-/

module

public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Emit.GenCtx
public import SchemaLang.Emit.Wit

@[expose] public section

namespace SchemaLang.Emit.WitSweep

open CodegenCore.Emit (jsonStr kebab)

/-! ## The seeded RNG — `TestKit.lcg`'s recurrence, INLINED

Importing TestKit here would publicly drag its LSpec surface into every
Emit consumer (the module-migration constraint-14 leak rule) — one
copied line, cited, beats one public dependency. -/

def lcgStep (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

/-- Advance the LCG and draw a value in `[0, bound)`. -/
def nextDraw (s : UInt64) (bound : Nat) : UInt64 × Nat :=
  let s' := lcgStep s
  (s', (s' % UInt64.ofNat bound).toNat)

/-! ## The seeded type generator (the audit's corner menu) -/

/-- Scalar leaf pick over the 13 closed scalars. -/
def leafOf (s : UInt64) : Ty × UInt64 :=
  let (s', d) := nextDraw s 13
  (match d with
    | 0 => .bool | 1 => .u8 | 2 => .u16 | 3 => .u32 | 4 => .u64
    | 5 => .i8 | 6 => .i16 | 7 => .i32 | 8 => .i64
    | 9 => .f32 | 10 => .f64 | 11 => .string | _ => .bytes, s')

/-- Key pick over the `KeyTy` scalars (10). -/
def keyOf (s : UInt64) : KeyTy × UInt64 :=
  let (s', d) := nextDraw s 10
  (match d with
    | 0 => .bool | 1 => .u8 | 2 => .u16 | 3 => .u32 | 4 => .u64
    | 5 => .i8 | 6 => .i16 | 7 => .i32 | 8 => .i64 | _ => .string, s')

/-- Tensor dims menu (outermost first — the row-major convention). -/
def dimsOf (s : UInt64) : List Nat × UInt64 :=
  let (s', d) := nextDraw s 3
  ((match d with
    | 0 => [2, 3] | 1 => [1] | _ => [4, 2]), s')

/-- Sized seeded `Ty` over the closed universe. Menu (each arm a
    probability share of the draw): leaves; option; list; result;
    MAP WITH AN OPTION PAYLOAD (the assoc-list rendering corner); set;
    tensor. NO future/stream — async is a FUNCTION-TYPE corner
    (fields cannot carry it), the func generator owns it. -/
def genTy : Nat → UInt64 → Ty × UInt64
  | 0, s => leafOf s
  | fuel + 1, s =>
    let (s1, d) := nextDraw s 10
    match d with
    | 0 | 1 | 2 | 3 => leafOf s1
    | 4 => let (t, s2) := genTy fuel s1; (.option t, s2)
    | 5 | 6 => let (t, s2) := genTy fuel s1; (.list t, s2)
    | 7 =>
        let (ok, s2) := genTy fuel s1
        let (err, s3) := genTy fuel s2
        (.result ok err, s3)
    | 8 =>
        -- THE corner: a map whose payload is an OPTION (the
        -- `list<tuple<K, option<V>>>` rendering under option)
        let (k, s2) := keyOf s1
        let (v, s3) := genTy fuel s2
        (.map k (.option v), s3)
    | _ =>
        -- sets, plus a tensor under the corner mask (every 2nd set draw)
        let (k, s2) := keyOf s1
        if (d : Nat) % 2 == 0 then
          (.set k, s2)
        else
          let (dims, s3) := dimsOf s2
          let (t, s4) := genTy fuel s3
          (.tensor dims t, s4)

/-- A seeded field: draw the type, name it by index (f0, f1, … — legal
    kebab, collision-free within the record). -/
def genField (fuel : Nat) (i : Nat) (s : UInt64) : Field × UInt64 :=
  let (t, s') := genTy fuel s
  ({ name := "f" ++ toString i, ty := t }, s')

/-- `n` fields in order, threading the RNG. -/
def genFields (fuel : Nat) (n : Nat) (s : UInt64) : List Field × UInt64 :=
  (List.range n).foldl (fun (acc, st) i =>
      let (f, st') := genField fuel i st
      (acc ++ [f], st')) ([], s)

/-- A seeded record: 1–4 fields. -/
def genRecord (name : String) (fuel : Nat) (s : UInt64) : Item × UInt64 :=
  let (s1, d) := nextDraw s 4
  let (fs, s2) := genFields fuel (d + 1) s1
  (.record name fs, s2)

/-- `n` seeded variant cases: every 3rd case payload-less (the bare
    `case` grammar), the rest payload-carrying. -/
def genCases (fuel : Nat) (n : Nat) (s : UInt64) : List VariantCase × UInt64 :=
  (List.range n).foldl (fun (acc, st) i =>
      let (s1, d) := nextDraw st 3
      if d == 0 then
        (acc ++ [("c" ++ toString i, none)], s1)
      else
        let (t, s2) := genTy fuel s1
        (acc ++ [("c" ++ toString i, some t)], s2)) ([], s)

/-- A seeded variant: 1–4 cases. -/
def genVariant (name : String) (fuel : Nat) (s : UInt64) : Item × UInt64 :=
  let (s1, d) := nextDraw s 4
  let (cs, s2) := genCases fuel (d + 1) s1
  (.variant name cs, s2)

/-- A seeded func: 0–2 params, and every other func is ASYNC (a
    `.future` ret — the WASI 0.3 function-type corner, with the seeded
    type — tensors included — as the unwrapped payload). -/
def genFunc (name : String) (fuel : Nat) (s : UInt64) : Item × UInt64 :=
  let (s1, dAsync) := nextDraw s 2
  let (s2, dN) := nextDraw s1 3
  let (ps, s3) := (List.range dN).foldl (fun (acc, st) i =>
      let (t, st') := genTy fuel st
      (acc ++ [("p" ++ toString i, t)], st')) ([], s2)
  let (t, s4) := genTy fuel s3
  let ret : Ty := if dAsync == 0 then .future t else t
  (.func { name := name, params := ps, ret := ret }, s4)

/-! ## The corpus: 12 seeded universes + 4 pinned corner universes -/

/-- The pinned sweep seed (any failure replays byte-identically). -/
def sweepSeed : UInt64 := 20260919

/-- Seeded universe count (`sweep-01` … `sweep-12`). -/
def seededCount : Nat := 12

/-- One seeded universe: two records, a variant, a func — the shapes a
    schema world actually ships, drawn from the pinned seed. -/
def seededUniverse (i : Nat) : String × List Item :=
  let name := "sweep-" ++ (if i < 10 then "0" else "") ++ toString i
  let s0 := sweepSeed + (i.toUInt64 * 7919)
  let (recA, s1) := genRecord "order" 3 s0
  let (recB, s2) := genRecord "summary" 2 s1
  let (v, s3) := genVariant "shape" 2 s2
  let (f, _s4) := genFunc "watch" 2 s3
  (name, [recA, recB, v, f])

def seededFixtures : List (String × List Item) :=
  (List.range seededCount).map (fun i => seededUniverse (i + 1))

/-- Corner 1: map/set assoc-list rendering UNDER OPTION PAYLOADS —
    option-valued maps at every position (field, inside list, inside
    option, nested map value), plus a plain set. -/
def cornerMapset : List Item :=
  [ .record "mapset"
      [ { name := "m-opt", ty := .map .u64 (.option .string) }
      , { name := "m-in-list", ty := .list (.map .string (.option (.list .u32))) }
      , { name := "s-plain", ty := .set .string }
      , { name := "opt-of-map", ty := .option (.map .u32 .u64) }
      , { name := "m-in-map", ty := .map .u32 (.map .u64 (.option .bool)) } ] ]

/-- Corner 2: TENSOR FLATTENING UNDER ASYNC — tensor fields (flat list
    rendering, dims dropped) and async funcs whose unwrapped payloads
    are tensors (`async func(...) -> list<...>`). -/
def cornerTensorAsync : List Item :=
  [ .record "tensors"
      [ { name := "t-2x3", ty := .tensor [2, 3] .u64 }
      , { name := "t-1d", ty := .tensor [1] (.list (.option .u8)) }
      , { name := "t-nested", ty := .tensor [2] (.tensor [3] .f64) } ]
  , .func { name := "watch-tensor", params := [("id", .u32)]
          , ret := .future (.tensor [2, 3] .u64) }
  , .func { name := "stream-tensor", params := []
          , ret := .stream (.tensor [4] .f32) } ]

/-- Corner 3: DEEP NESTING — a 16-deep option/list tower and a wide
    result over map/set/list compositions. The tower helper (not in
    the emitter surface) alternates option/list 8 times over `u64`. -/
def cornerTower : Ty :=
  let rec tower (fuel : Nat) (t : Ty) : Ty :=
    match fuel with
    | 0 => t
    | k + 1 => .option (.list (tower k t))
  tower 8 .u64

def cornerDeep : List Item :=
  [ .record "deep"
      [ { name := "tower", ty := cornerTower }
      , { name := "wide", ty := .result
            (.list (.option (.result (.map .u64 (.option .string)) (.set .u16))))
            (.list .bytes) } ] ]

/-- Corner 4: EMPTY records — zero-member braces are legal WIT
    (`record empty { }`); the emitter's `blockBody` degrades to a bare
    line, and the sweep asks wit-parser to agree. (The zero-case
    VARIANT — the caught sibling bug — is refused by the WF gate now;
    `cornerMinVariant` is its legal one-case control, and the refusal
    itself is pinned in Tests.) -/
def cornerEmpty : List Item :=
  [ .record "empty-record" [] ]

/-- Corner 5 (the caught kebab-collision bug, the audit's original
    PROBE): three distinct universe names that mangle to the SAME WIT
    identifier (`kebab` is not injective: "FooBar", "foo-bar", "foo_bar"
    → "foo-bar"). The emitter used to ship `record foo-bar` three times
    and wit-parser rejected it — the fix is the WF lane's POST-MANGLE
    uniqueness rule (`Item.mangleCollDiags` ↔ `WellFormed`, the bridge
    `mangleCollDiags_eq_nil_iff`), so this universe now refuses at
    ELABORATION (Tests pins the named diagnostic). NOT emitted — it is
    illegal by the gate; `cornerKebabNear` is its legal control. -/
def cornerKebab : List Item :=
  [ .record "FooBar" [{ name := "v", ty := .u8 }]
  , .record "foo-bar" [{ name := "v", ty := .u16 }]
  , .record "foo_bar" [{ name := "v", ty := .u32 }] ]

/-- Corner 6 (the kebab gate's over-breadth control): names that are
    NEAR collisions but legal — `foo-bar` and `foo-bar2` mangle to
    DISTINCT identifiers, so the post-mangle gate passes them (the
    byte-tie pins the emitted pair). -/
def cornerKebabNear : List Item :=
  [ .record "foo-bar" [{ name := "v", ty := .u8 }]
  , .record "foo-bar2" [{ name := "v", ty := .u16 }] ]

/-- Corner 7 (the empty-variant gate's over-breadth control): the
    MINIMAL legal variant — one case. The zero-case sibling refuses at
    elaboration (`Item.check`'s `emptyVariant` arm); the one-case form
    is the smallest universe that must stay legal. -/
def cornerMinVariant : List Item :=
  [ .variant "one-case" [("only", some .u8)] ]

/-- The pinned corner universes (each isolates ONE audit corner so a
    failure names it). The two caught-bug universes (`cornerKebab`, the
    zero-case variant) are NOT in the emitted corpus — they refuse at
    elaboration; Tests pins both refusals with their named diagnostics. -/
def cornerFixtures : List (String × List Item) :=
  [ ("corner-mapset", cornerMapset)
  , ("corner-tensor-async", cornerTensorAsync)
  , ("corner-deep", cornerDeep)
  , ("corner-empty", cornerEmpty)
  , ("corner-kebab-near", cornerKebabNear)
  , ("corner-min-variant", cornerMinVariant) ]

/-- The full corpus: seeded universes first, corners after. -/
def sweepFixtures : List (String × List Item) :=
  seededFixtures ++ cornerFixtures

/-! ## The manifest — the LOWERED shape each universe must parse back to

The Rust sweep compares wit-parser's resolved types against these
shape objects (`serde_json::Value` equality). The shapes are the
EMITTER's own lowering contract — map/set → list(-of-tuple), tensor →
list, bytes → list<u8> — because the Lean `Ty` is deliberately lossy
at the WIT boundary (the four lossy corners, `Emit.Wit`'s header). -/

def keyShape : KeyTy → String
  | .bool => "{\"kind\": \"bool\"}" | .u8 => "{\"kind\": \"u8\"}"
  | .u16 => "{\"kind\": \"u16\"}" | .u32 => "{\"kind\": \"u32\"}"
  | .u64 => "{\"kind\": \"u64\"}" | .i8 => "{\"kind\": \"s8\"}"
  | .i16 => "{\"kind\": \"s16\"}" | .i32 => "{\"kind\": \"s32\"}"
  | .i64 => "{\"kind\": \"s64\"}" | .string => "{\"kind\": \"string\"}"

def shapeJson : Ty → String
  | .bool => "{\"kind\": \"bool\"}" | .u8 => "{\"kind\": \"u8\"}"
  | .u16 => "{\"kind\": \"u16\"}" | .u32 => "{\"kind\": \"u32\"}"
  | .u64 => "{\"kind\": \"u64\"}"
  | .i8 => "{\"kind\": \"s8\"}" | .i16 => "{\"kind\": \"s16\"}"
  | .i32 => "{\"kind\": \"s32\"}" | .i64 => "{\"kind\": \"s64\"}"
  | .f32 => "{\"kind\": \"f32\"}" | .f64 => "{\"kind\": \"f64\"}"
  | .string => "{\"kind\": \"string\"}"
  | .bytes => "{\"kind\": \"list\", \"elem\": {\"kind\": \"u8\"}}"
  | .option a => "{\"kind\": \"option\", \"elem\": " ++ shapeJson a ++ "}"
  | .result ok err =>
      "{\"kind\": \"result\", \"ok\": " ++ shapeJson ok
        ++ ", \"err\": " ++ shapeJson err ++ "}"
  | .list a => "{\"kind\": \"list\", \"elem\": " ++ shapeJson a ++ "}"
  | .map k v =>
      -- the association-list lowering: list<tuple<K, V>>
      "{\"kind\": \"list\", \"elem\": {\"kind\": \"tuple\", \"elems\": ["
        ++ keyShape k ++ ", " ++ shapeJson v ++ "]}}"
  | .set k => "{\"kind\": \"list\", \"elem\": " ++ keyShape k ++ "}"
  | .future a => "{\"kind\": \"future\", \"elem\": " ++ shapeJson a ++ "}"
  | .stream a => "{\"kind\": \"stream\", \"elem\": " ++ shapeJson a ++ "}"
  -- the tensor lowering: dims dropped, the flat list form
  | .tensor _ a => "{\"kind\": \"list\", \"elem\": " ++ shapeJson a ++ "}"
  | .ty n => "{\"kind\": \"ref\", \"name\": " ++ jsonStr (kebab n) ++ "}"

/-- One type item → the manifest's expected-shape entry. -/
def typeEntryJson : Item → Option String
  | .record n fields =>
      some ("{\"name\": " ++ jsonStr (kebab n) ++ ", \"kind\": \"record\", \"fields\": ["
        ++ String.intercalate ", " (fields.map fun f =>
              "{\"name\": " ++ jsonStr (kebab f.name)
                ++ ", \"shape\": " ++ shapeJson f.ty ++ "}") ++ "]}")
  | .variant n cases =>
      some ("{\"name\": " ++ jsonStr (kebab n) ++ ", \"kind\": \"variant\", \"cases\": ["
        ++ String.intercalate ", " (cases.map fun (c, p) =>
              "{\"name\": " ++ jsonStr (kebab c) ++ ", \"payload\": "
                ++ (match p with | some t => shapeJson t | none => "null") ++ "}")
        ++ "]}")
  | _ => none

/-- One func item → the manifest's expected-signature entry. A `.future`
    ret is the ASYNC func corner: the wire result is the UNWRAPPED
    payload (async-ness recorded separately — the Rust sweep checks
    `FunctionKind::AsyncFreestanding`). -/
def funcEntryJson : Item → Option String
  | .func s =>
      let ret := match s.ret with | .future a => a | t => t
      some ("{\"name\": " ++ jsonStr (kebab s.name) ++ ", \"async\": "
        ++ (match s.ret with | .future _ => "true" | _ => "false")
        ++ ", \"params\": [" ++ String.intercalate ", " (s.params.map fun (p, t) =>
              "{\"name\": " ++ jsonStr (kebab p)
                ++ ", \"shape\": " ++ shapeJson t ++ "}") ++ "]"
        ++ ", \"result\": " ++ shapeJson ret ++ "}")
  | _ => none

/-- One universe → the manifest's entry text. -/
def sweepEntryJson (name : String) (items : List Item) : String :=
  "  { \"fixture\": " ++ jsonStr name ++ ", \"package\": "
    ++ jsonStr ("demo:" ++ name)
    ++ ", \"types\": [" ++ String.intercalate ", " (items.filterMap typeEntryJson) ++ "]"
    ++ ", \"funcs\": [" ++ String.intercalate ", " (items.filterMap funcEntryJson) ++ "] }"

/-- The full manifest document (no header — the driver prepends). -/
def sweepManifestJson : String :=
  "[\n"
    ++ String.intercalate ",\n" (sweepFixtures.map fun (n, items) => sweepEntryJson n items)
    ++ "\n]\n"

/-! ## The emitters -/

def sweepManifestOutput : String :=
  "../../crates/steel-host/tests/fixtures/wit_sweep/manifest.json"

/-- The sweep's output FILE NAMES, LITERAL. The kernel's decide over
    `jobsCoverEmitters_true` must normalize every emitter's `outputs`
    — re-deriving them from `sweepFixtures` would drag the seeded
    generator's UInt64 LCG into kernel reduction (the known
    kernel-expensive trap); the literals keep the proof cheap. The
    sync with `run` is audited at runtime: Tests' "run outputs ⊆
    declared outputs" + goldenChecks (a generator-added universe
    without a literal entry fails BOTH). -/
def sweepFixtureFiles : List String :=
  [ "sweep-01", "sweep-02", "sweep-03", "sweep-04", "sweep-05", "sweep-06"
  , "sweep-07", "sweep-08", "sweep-09", "sweep-10", "sweep-11", "sweep-12"
  , "corner-mapset", "corner-tensor-async", "corner-deep", "corner-empty"
  , "corner-kebab-near", "corner-min-variant" ]

/-- One emitter outputting ALL sweep WIT files (one writer, many files —
    the outputs list is the one-writer claim). -/
def sweepFixtureEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "wit-sweep-fixtures"
  style := .doubleSlash
  specSource := "SchemaLang.Emit.WitSweep (seeded sweep fixtures)"
  outputs := sweepFixtureFiles.map fun n =>
    "../../crates/steel-host/tests/fixtures/wit_sweep/" ++ n ++ ".wit"
  run _ctx :=
    sweepFixtures.map fun (n, items) =>
      { path := "../../crates/steel-host/tests/fixtures/wit_sweep/" ++ n ++ ".wit"
      , contents := SchemaLang.Emit.Wit.worldOf ("demo:" ++ n) n items }

def sweepManifestEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "wit-sweep-manifest"
  style := .doubleSlash
  specSource := "SchemaLang.Emit.WitSweep (seeded sweep fixtures)"
  outputs := [sweepManifestOutput]
  run _ctx :=
    [{ path := sweepManifestOutput, contents := sweepManifestJson }]

end SchemaLang.Emit.WitSweep
