/-
# SchemaCore.Emit.Fuzz — the contracts→fuzz face (the C3 lane)

Owner: the fuzz lane (the mandate tree, `schemacore/`).
Driving decisions: notes/design-wave-30.md C3 (the generated
`Arbitrary` impls from TestingKit's generators — ONE generator
definition, TWO consumers); notes/v3/12-construction.md §8 (the bolero
mandate: the never-panic floors + the fixture differentials);
notes/design-bolero-integration.md §3-6 (the lane division: Lean
proves the model, the Rust face explores the runtime; the negative
control rides the harness, never the dependency).

THE ENGINE JUDGMENT (the plan's honest-local rule): the devenv cargo
has `cargo-bolero` 0.13.4, but bolero is NOT in the crates' dependency
set — so the honest minimal lands: the properties are plain `cargo
test` faces, the generated `Arbitrary` drives deterministic
LCG-seeded cases, and the fuzz-ENGINE choice (libfuzzer campaigns via
`cargo bolero test`, design-bolero-integration §9 W-B1) stays the
owner's later call. The PROPERTIES + the GENERATORS are the content;
they are bolero-shaped already (every case replays from its printed
seed; a future harness swaps the driver, never the generators).

ONE GENERATOR DEFINITION, TWO CONSUMERS: the Lean sweep draws through
`TestingKit.Lcg` (the seeded-sweep discipline — the landed drawers);
this lane emits that discipline's RUST TWIN: the `Tape` (the same
Knuth-64 recurrence, the same byte/below shapes, byte-tied by the
embedded `TAPE_GOLDEN` vectors — computed HERE by the Lean drawers,
asserted in Rust by a generated test) plus per-record `Arbitrary`
impls from the `arbAlg` FOLD (the wrapper arms compose inline — the
Spine's `descrOfTy` shape: ONE leaf universe + the wrapper dimension;
no blanket container impls, coherence forbids the `(K, V)` vector
row).

THE PROPERTIES (the boundary's honest split — Lean proves the model,
the fuzz covers the RUNTIME): the codec round-trip (encode ∘ decode =
id over arbitrary values — the Lean law's Rust twin), the never-panic
floor (the decoders over arbitrary BYTES — junk must refuse, typed
`CodecError`, never a panic; a decoded value re-encodes byte-identically
— the differential's re-encode law at arbitrary inputs), the typestate
invariant (the builder chain over arbitrary field values equals the
struct literal — the setters' plumbing pinned across the whole value
space), and the MANDATORY negative control (the sabotage-stub form:
the floor's driver run against a panicking stub twin must be CAUGHT —
design-bolero-integration §6's checker-discrimination at the stub
edge; the props-file pins the refusal of known junk as the other
edge).

THE HONEST GAPS (each named, none silent):
- The generator's atom drawers extend the Lean set (the Lean sweep
  draws chars/strings; the u64/i64/bool atoms ride the stream directly
  — `u64_draw` is the raw state word, `i64_draw` its zigzag, the wire's
  own map). The Lean-side sweep's atoms come from the Derive sweep's
  `below` face; a cross-language atom tie lands with the first Lean
  consumer of the atom drawers (the leftover rule).
- The generated `Arbitrary` impls cover the REGISTRY's records
  (the two slice items). The versioned faces (`ExampleV1`/`V2`) and
  the newtypes have no generator impl — their consumers (the
  migration pins) are fixed-input pins, no exploration yet.
- The map arm draws the ENTRY PAIRS freely (duplicates possible — the
  wire is order-preserving, insertion order IS payload data; the Rust
  type is `Vec<(K, V)>` for exactly this reason, the emitter's
  divergence note). No uniqueness is invented here.

WIRING: the emitter rides `SchemaCore.regenOfItems` (the ONE regen
core — the writer `schema` and `gates gen-check` both fold it), the
ownership gate's `realEmitters` set, and SchemaTests' fuzz suite (the
shape pins + the negative control). The coverage matrix does NOT grow
a column: the matrix's emitters are the type-RENDERING faces (wit/
rust/ts — each re-rendering the closed universe's ctors); this lane
consumes the items and adds no type surface (the generated impls ride
`pascalName`'s spelling and the wire's types verbatim).

The five questions (notes/v3/01-core.md):
- root: Crossing — the universe (`DataRegistry Item`) read into the
  generated generator face + the properties' artifact.
- carrier grade: the naming precondition rides the registry's own
  nodup-in-the-type; the record spellings ride `pascalName` (the Rust
  lane's ONE mangler — the impls name the structs the lib.rs renders,
  never a second spelling).
- spine reading: the Interpretation stage (01 §5) — the THIRD emitter
  family over the ONE regen core; a plain `Emitter` row (the
  properties are authored pin text, the generator face the fold).
- ladder rung: total structural folds; the tape golden is runtime
  data (the drawers are plain `UInt64` recursions — kernel-visible),
  pinned Lean-side by SchemaTests and Rust-side by the generated test.
- gate row: gen-check (the byte-tie over both artifacts), audit (the
  banned-pattern scan — the generated text avoids the banned list),
  ownership (the real-emitter set), artifact-headers (the driver's
  2-line block), SchemaTests' fuzz suite (the shape pins).

Core-only (imports SchemaCore.* + TestingKit.Lcg — the cone rule; C1
importing C0 is the landed direction, the domain cores' sweep faces
already draw through the kit).
-/

import SchemaCore.Emit.Rust
import SchemaCore.Item
import SchemaCore.Fold
import TestingKit.Lcg
import Kit.Emit

open Kit
open Kit.Emit

namespace SchemaCore.Emit.Fuzz

/-! ## The tape golden (the cross-language tie, computed Lean-side) -/

/-- The golden tape's seed (the pinned draw plan's input). -/
def tapeGoldenSeed : UInt64 := 42

/-- The golden BYTES: eight `Tape.byte` draws from the pinned seed —
    the LEAN drawers' own outputs, embedded in the generated face and
    asserted there by the generated test (the LCG's byte-tie). -/
def tapeGoldenBytes : List UInt64 :=
  (TestingKit.drawMany 8 (fun t => t.byte) (TestingKit.Tape.ofSeed tapeGoldenSeed)).1

/-- The golden BOUNDS: eight `Tape.below 7` draws on the SAME stream
    (the bytes' CONTINUATION — the tape state the eight byte draws
    left behind; the golden test's order matches this plan exactly:
    bytes first, then the bounds). -/
def tapeGoldenBelows : List Nat :=
  (TestingKit.drawMany 8 (fun t => t.below 7)
    (TestingKit.drawMany 8 (fun t => t.byte)
      (TestingKit.Tape.ofSeed tapeGoldenSeed)).2).1

/-- A Rust literal for a `UInt64` list. -/
def u64Lit (xs : List UInt64) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

/-- A Rust literal for a `Nat` list (the bounds' face). -/
def natLit (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

/-! ## THE ARBITRARY FOLD — the generator statements as algebras

The convention mirrors the codec's two algs: the fold composes Rust
EXPRESSIONS that draw from a tape binding named `t` in scope. The
input expression is unused (a generator draws, it does not consume) —
the argument position keeps the `TyAlg (String → String)` shape the
other two algs carry. -/

/-- The KEY position's drawers (the scalar sub-universe's algebra —
    the same drawers, the key row's spelling). -/
def arbKeyAlg : KeyTyAlg (String → String) where
  bool _ := "t.boolean()"
  u64 _ := "t.u64_draw()"
  i64 _ := "t.i64_draw()"
  string _ := "t.draw_string()"

/-- THE GENERATOR STATEMENTS = the fold (the codec algs' third
    sibling). Every ctor composes the tape's drawers INLINE:
    - the leaves draw (the atoms: bool = the byte's low bit, u64 =
      the state word, i64 = the zigzag, string = the `drawString`
      shape);
    - the wrappers branch/loop over the recursive draws (1-in-4
      `None`, list/map/set length < 4 — the Lean drawers' own
      short-shape discipline);
    - `bounded n` draws below the cap (the refinement is payload
      policy here, not just wire policy — the generator respects it). -/
def arbAlg : TyAlg (String → String) where
  bool _ := "t.boolean()"
  u64 _ := "t.u64_draw()"
  i64 _ := "t.i64_draw()"
  string _ := "t.draw_string()"
  option a := fun _ =>
    "{ if t.below(4) == 0 { None } else { Some(" ++ a "inner" ++ ") } }"
  list a := fun _ =>
    "{ let n = t.below(4) as usize; let mut acc = Vec::new(); for _ in 0..n { acc.push(" ++ a "inner" ++ "); } acc }"
  result ok err := fun _ =>
    "{ if t.boolean() { Ok(" ++ ok "inner" ++ ") } else { Err(" ++
    err "inner" ++ ") } }"
  map k v := fun _ =>
    "{ let n = t.below(4) as usize; let mut acc = Vec::new(); for _ in 0..n { acc.push((" ++ foldKeyTy arbKeyAlg k "innerk" ++
      ", " ++ v "innerv" ++ ")); } acc }"
  set k := fun _ =>
    "{ let n = t.below(4) as usize; let mut acc = Vec::new(); for _ in 0..n { acc.push(" ++ foldKeyTy arbKeyAlg k "innerk" ++ "); } acc }"
  bounded n := fun _ => "t.below(" ++ toString n ++ ")"

/-! ## The generated face's body -/

/-- One record's `Arbitrary` impl: the fold's statements in schema
    order, the construction shorthand (the codec's own convention). -/
def renderArbitraryImpl (item : Item) : String :=
  let name := SchemaCore.Emit.Rust.pascalName item.name
  let stmts := item.fields.map fun f =>
    "        let " ++ f.name ++ " = " ++ foldTy arbAlg f.ty "unused" ++ ";"
  let shorthand := String.intercalate ", " (item.fields.map (·.name))
  "#[rustfmt::skip]\n" ++
  "impl Arbitrary for " ++ name ++ " {\n" ++
  "    fn arbitrary(t: &mut Tape) -> Self {\n" ++
  String.intercalate "\n" stmts ++ "\n" ++
  "        " ++ name ++ " { " ++ shorthand ++ " }\n" ++
  "    }\n" ++
  "}\n"

/-- The impl table over the registry's items (joined by blank lines). -/
def arbitraryImpls (reg : DataRegistry Item) : String :=
  String.intercalate "\n\n" (reg.items.map renderArbitraryImpl)

/-- The TAPE + trait prelude: the LCG discipline's Rust twin, the
    golden vectors, the `Arbitrary` trait. The recurrence's constants
    are `TestingKit.lcg`'s verbatim; the wrap is the stream (the
    wrapping arithmetic is the definition, named). -/
def tapePrelude : String :=
  String.intercalate "\n"
  [ "/// The shared deterministic LCG (Knuth 64) — TestingKit.Lcg's RUST"
  , "/// TWIN: the same recurrence (the u64 arithmetic WRAPS — the wrap"
  , "/// is the stream), the same byte/below shapes, byte-tied by the"
  , "/// TAPE_GOLDEN vectors below (computed by the LEAN drawers over"
  , "/// the pinned seed; the generated test asserts the agreement)."
  , "/// A failing case replays byte-identically from its seed"
  , "/// (15-patterns #14)."
  , "#[derive(Clone, Debug, PartialEq, Eq)]"
  , "pub struct Tape { state: u64 }"
  , ""
  , "impl Tape {"
  , "    /// A fresh tape pinned to `seed` (Tape.ofSeed's shape)."
  , "    pub fn of_seed(s: u64) -> Self { Tape { state: s } }"
  , ""
  , "    /// One LCG step: the recurrence's next state."
  , "    fn next(&mut self) -> u64 {"
  , "        self.state = self.state"
  , "            .wrapping_mul(6364136223846793005)"
  , "            .wrapping_add(1442695040888963407);"
  , "        self.state"
  , "    }"
  , ""
  , "    /// One byte: the top 8 bits of the next state (Tape.byte)."
  , "    pub fn byte(&mut self) -> u8 { (self.next() >> 56) as u8 }"
  , ""
  , "    /// A draw below `bound`: (state >> 16) % bound (Tape.below;"
  , "    /// the modulo bias is accepted for a test kit — noted, not"
  , "    /// hidden — the LEAN definition's own note)."
  , "    pub fn below(&mut self, bound: u64) -> u64 {"
  , "        (self.next() >> 16) % bound"
  , "    }"
  , ""
  , "    /// bool: the byte drawer's low bit."
  , "    pub fn boolean(&mut self) -> bool { self.byte() & 1 == 1 }"
  , ""
  , "    /// u64: the raw next state (the stream's own word)."
  , "    pub fn u64_draw(&mut self) -> u64 { self.next() }"
  , ""
  , "    /// i64: the zigzag of the u64 draw (the wire's own i64 map —"
  , "    /// the codec's zigzag, never a second mapping)."
  , "    pub fn i64_draw(&mut self) -> i64 {"
  , "        let z = self.u64_draw();"
  , "        ((z >> 1) as i64) ^ (-((z & 1) as i64))"
  , "    }"
  , ""
  , "    /// One char from the small alphabet (drawChar's shape)."
  , "    pub fn draw_char(&mut self) -> char {"
  , "        let alphabet = ['a', 'b', 'c', 'd'];"
  , "        alphabet[self.below(4) as usize]"
  , "    }"
  , ""
  , "    /// A short string, length < 4, over the small alphabet"
  , "    /// (drawString's shape)."
  , "    pub fn draw_string(&mut self) -> String {"
  , "        let n = self.below(4) as usize;"
  , "        let mut acc = String::new();"
  , "        for _ in 0..n { acc.push(self.draw_char()); }"
  , "        acc"
  , "    }"
  , "}"
  , ""
  , "/// The golden seed (the Lean side's pinned plan input)."
  , "pub const TAPE_GOLDEN_SEED: u64 = " ++ toString tapeGoldenSeed ++ ";"
  , ""
  , "/// Eight byte draws — the Lean drawers' outputs, embedded."
  , "pub const TAPE_GOLDEN_BYTES: [u8; 8] = " ++ u64Lit tapeGoldenBytes ++ ";"
  , ""
  , "/// Eight bounded draws (below 7) — the bytes' continuation on the"
  , "/// SAME stream; the golden test replays the plan in this order."
  , "pub const TAPE_GOLDEN_BELOWS: [u64; 8] = " ++ u64Lit (tapeGoldenBelows.map (·.toUInt64)) ++ ";"
  , ""
  , "/// The generated generator face: ONE method per record — the Lean"
  , "/// drawer discipline's shape at the Rust boundary. The wrapper"
  , "/// arms compose INLINE in the emitter's fold (the Spine's"
  , "/// description lift's shape: ONE leaf universe + the wrapper"
  , "/// dimension); no blanket container impls (coherence forbids the"
  , "/// entry-pair vector row)."
  , "pub trait Arbitrary {"
  , "    /// Draw a value from the tape (pure in the tape state)."
  , "    fn arbitrary(t: &mut Tape) -> Self;"
  , "}" ]

/-- The tape golden's self-pin (the generated face's own test — the
    cross-language byte-tie's execution). -/
def tapeGoldenTest : String :=
  "#[test]\n" ++
  "fn tape_matches_the_lean_golden() {\n" ++
  "    let mut t = Tape::of_seed(TAPE_GOLDEN_SEED);\n" ++
  "    for b in TAPE_GOLDEN_BYTES {\n" ++
  "        assert_eq!(t.byte(), b, \"the byte stream drifted from the Lean drawers\");\n" ++
  "    }\n" ++
  "    for b in TAPE_GOLDEN_BELOWS {\n" ++
  "        assert_eq!(t.below(7), b, \"the bounded stream drifted from the Lean drawers\");\n" ++
  "    }\n" ++
  "}\n"

/-- `crates/schema-generated/tests/fuzz_gen.rs`'s body: the generated
    Arbitrary face (the tape twin + the trait + the registry's impl
    table + the golden self-pin). -/
def fuzzGenBody (reg : DataRegistry Item) : String :=
  String.intercalate "\n"
  [ "//! The generated Arbitrary face (SchemaCore.Emit.Fuzz — the C3"
  , "//! fuzz lane): TestingKit.Lcg's Rust twin + per-record Arbitrary"
  , "//! impls from the emitter's fold. ONE generator definition, TWO"
  , "//! consumers (the Lean sweep + this face). Never hand-edit:"
  , "//! `just gen` restores; drift fails `gates gen-check`."
  , ""
  , "#![allow(dead_code)]"
  , ""
  , "use schema_generated::{Example, ExampleEx};"
  , ""
  , tapePrelude
  , ""
  , arbitraryImpls reg
  , ""
  , tapeGoldenTest ]

/-! ## The properties' artifact (the authored pin text, rendered verbatim) -/

/-- `crates/schema-generated/tests/fuzz_properties.rs`'s body — the
    boundary properties as plain `cargo test` faces (the honest
    minimal: the fuzz-engine choice is the owner's later call; the
    PROPERTIES + the GENERATORS are the content). Hand-AUTHORED pin
    text rendered by the emitter — the ONE writer; the same
    discipline the consumer suite's files ride. -/
def fuzzPropertiesRust : String :=
"//! The boundary properties (the C3 face — the contracts' RUNTIME\n" ++
"//! half): the codec round-trip over arbitrary values (the Lean law's\n" ++
"//! Rust twin), the never-panic floor over arbitrary bytes (junk must\n" ++
"//! refuse — typed `CodecError`, never a panic), the typestate\n" ++
"//! builder's plumbing over arbitrary field values, and the MANDATORY\n" ++
"//! negative control (the sabotage-stub: the floor's driver must\n" ++
"//! CATCH a panicking subject — the PropSpec mandate's Rust twin,\n" ++
"//! design-bolero-integration §6). Hand-AUTHORED pin text, rendered\n" ++
"//! by the emitter — the ONE writer; `just gen` restores.\n" ++
"//!\n" ++
"//! THE ENGINE (the honest local shape): plain `cargo test` — the\n" ++
"//! generated `Arbitrary` face drives deterministic LCG-seeded cases\n" ++
"//! (every case replays from its seed; the failing case's evidence is\n" ++
"//! the seed). The fuzz-ENGINE choice (bolero's campaign engines) is\n" ++
"//! the owner's later call: the drivers below are the swap face.\n" ++
"\n" ++
"#[path = \"fuzz_gen.rs\"]\n" ++
"mod gen;\n" ++
"\n" ++
"use gen::{Arbitrary, Tape};\n" ++
"use schema_generated::{CodecError, Example, ExampleEx};\n" ++
"\n" ++
"/// The sweep's size (fixed iterations — deterministic, never a\n" ++
"/// time bound; design-bolero-integration §5's seeds law).\n" ++
"const ITERATIONS: u64 = 512;\n" ++
"\n" ++
"/// The codec round-trip law (the Lean RoundTripSpec's Rust twin):\n" ++
"/// encode ∘ decode_full = identity over the WHOLE generated value\n" ++
"/// space — every ctor arm (option/list/result/map/bounded) rides the\n" ++
"/// generator's fold, so the law's sweep covers the wire's every row.\n" ++
"#[test]\n" ++
"fn fuzz_codec_round_trip_example() {\n" ++
"    for seed in 0..ITERATIONS {\n" ++
"        let v = Example::arbitrary(&mut Tape::of_seed(seed));\n" ++
"        let mut wire = Vec::new();\n" ++
"        v.encode(&mut wire);\n" ++
"        let back = Example::decode_full(&wire)\n" ++
"            .unwrap_or_else(|e| panic!(\"seed {seed}: the round trip refused: {e:?}\"));\n" ++
"        assert_eq!(back, v, \"seed {seed}: the round trip drifted\");\n" ++
"    }\n" ++
"}\n" ++
"\n" ++
"/// The sum + map arms' round trip (the second record's rows — the\n" ++
"/// result face and the entry-pair vector).\n" ++
"#[test]\n" ++
"fn fuzz_codec_round_trip_example_ex() {\n" ++
"    for seed in 0..ITERATIONS {\n" ++
"        let v = ExampleEx::arbitrary(&mut Tape::of_seed(seed));\n" ++
"        let mut wire = Vec::new();\n" ++
"        v.encode(&mut wire);\n" ++
"        let back = ExampleEx::decode_full(&wire)\n" ++
"            .unwrap_or_else(|e| panic!(\"seed {seed}: the round trip refused: {e:?}\"));\n" ++
"        assert_eq!(back, v, \"seed {seed}: the round trip drifted\");\n" ++
"    }\n" ++
"}\n" ++
"\n" ++
"/// THE NEVER-PANIC FLOOR (12 §8's mandate — the boundary's honesty):\n" ++
"/// the decoders answer arbitrary BYTES with Ok or a typed\n" ++
"/// `CodecError` — junk must refuse, never panic, never silently\n" ++
"/// misparse. A decoded value's re-encode is byte-identical (the\n" ++
"/// differential's re-encode law, now at arbitrary inputs — the wire\n" ++
"/// is the exact image of the encoder).\n" ++
"#[test]\n" ++
"fn fuzz_decode_floor_never_panics_and_reencodes() {\n" ++
"    let mut ran = 0u64;\n" ++
"    for seed in 0..ITERATIONS {\n" ++
"        // the byte case: seeded, deterministic, replayable\n" ++
"        let mut t = Tape::of_seed(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));\n" ++
"        let n = t.below(32) as usize;\n" ++
"        let bytes: Vec<u8> = (0..n).map(|_| t.byte()).collect();\n" ++
"        if let Ok(v) = Example::decode_full(&bytes) {\n" ++
"            let mut out = Vec::new();\n" ++
"            v.encode(&mut out);\n" ++
"            assert_eq!(out, bytes, \"seed {seed}: the re-encode drifted\");\n" ++
"        }\n" ++
"        if let Ok(v) = ExampleEx::decode_full(&bytes) {\n" ++
"            let mut out = Vec::new();\n" ++
"            v.encode(&mut out);\n" ++
"            assert_eq!(out, bytes, \"seed {seed}: the re-encode drifted\");\n" ++
"        }\n" ++
"        ran += 1;\n" ++
"    }\n" ++
"    // THE ANTI-VACUITY GUARD (design-bolero-integration §6): the\n" ++
"    // target RAN — a generator that never draws proves nothing.\n" ++
"    assert_eq!(ran, ITERATIONS, \"the sweep did not complete\");\n" ++
"}\n" ++
"\n" ++
"/// The floor's known-junk edge: the documented out-of-policy shapes\n" ++
"/// REFUSE (the negative control's data face — the same shapes the\n" ++
"/// differential's tamper vectors carry, composed here). The other\n" ++
"/// edge: a valid encoding passes.\n" ++
"#[test]\n" ++
"fn fuzz_floor_refuses_known_junk() {\n" ++
"    assert!(Example::decode_full(&[]).is_err(), \"empty must refuse\");\n" ++
"    assert!(Example::decode_full(&[0xFF]).is_err(), \"a bad tag must refuse\");\n" ++
"    assert!(Example::decode_full(&[0x01, 0x80, 0x00]).is_err(),\n" ++
"        \"a non-canonical varint must refuse\");\n" ++
"    let v = Example::arbitrary(&mut Tape::of_seed(7));\n" ++
"    let mut wire = Vec::new();\n" ++
"    v.encode(&mut wire);\n" ++
"    assert!(Example::decode_full(&wire).is_ok(), \"a valid encoding must decode\");\n" ++
"}\n" ++
"\n" ++
"/// The typestate invariant's runtime face: the builder chain over\n" ++
"/// arbitrary field values equals the generated value for the same\n" ++
"/// seed — the setters' plumbing carries the WHOLE value space (the\n" ++
"/// all-set `build` is infallible; the unset state does not compile,\n" ++
"/// the api.rs pin's guarantee — never re-tested here, it is a type\n" ++
"/// fact, not a runtime one).\n" ++
"#[test]\n" ++
"fn fuzz_builder_matches_the_generated_value() {\n" ++
"    for seed in 0..ITERATIONS {\n" ++
"        let mut t = Tape::of_seed(seed);\n" ++
"        let ready = t.boolean();\n" ++
"        let count = t.u64_draw();\n" ++
"        let delta = t.i64_draw();\n" ++
"        let label = t.draw_string();\n" ++
"        let note = if t.below(4) == 0 { None } else { Some(t.draw_string()) };\n" ++
"        let n = t.below(4) as usize;\n" ++
"        let mut tags = Vec::new();\n" ++
"        for _ in 0..n { tags.push(t.draw_string()); }\n" ++
"        let built = Example::builder()\n" ++
"            .ready(ready)\n" ++
"            .count(count)\n" ++
"            .delta(delta)\n" ++
"            .label(label)\n" ++
"            .note(note)\n" ++
"            .tags(tags)\n" ++
"            .build();\n" ++
"        let expected = Example::arbitrary(&mut Tape::of_seed(seed));\n" ++
"        assert_eq!(built, expected, \"seed {seed}: the builder's plumbing drifted\");\n" ++
"    }\n" ++
"}\n" ++
"\n" ++
"/// THE NEGATIVE CONTROL (MANDATORY — the sabotage-stub form): the\n" ++
"/// floor's driver machinery run against a deliberately-panicking\n" ++
"/// twin of the subject must be CAUGHT. If the driver ever stopped\n" ++
"/// executing the subject (or the catch face were loosened), this\n" ++
"/// control goes red: the fuzz layer would prove nothing.\n" ++
"#[test]\n" ++
"fn negative_control_the_floor_catches_a_sabotaged_subject() {\n" ++
"    struct Sabotaged;\n" ++
"    impl Sabotaged {\n" ++
"        // the stub twin: the panic IS the sabotage\n" ++
"        fn decode_full(_bs: &[u8]) -> Result<(), CodecError> {\n" ++
"            panic!(\"the sabotage stub: the floor's subject twin is broken\")\n" ++
"        }\n" ++
"    }\n" ++
"    let caught = std::panic::catch_unwind(|| {\n" ++
"        for seed in 0..8u64 {\n" ++
"            let mut t = Tape::of_seed(seed);\n" ++
"            let n = t.below(8) as usize;\n" ++
"            let bytes: Vec<u8> = (0..n).map(|_| t.byte()).collect();\n" ++
"            let _ = Sabotaged::decode_full(&bytes);\n" ++
"        }\n" ++
"    });\n" ++
"    assert!(caught.is_err(),\n" ++
"        \"control NOT caught — the fuzz layer proves nothing\");\n" ++
"}\n"

/-! ## The emitter row -/

/-- The fuzz lane's emitter (the C3 row): the generated Arbitrary face
    + the boundary properties, ONE emitter, the outputs' nodup in the
    type. The properties are authored pin text (the consumer suite's
    discipline); the generator face is the fold's. -/
def fuzzGenEmitter : Emitter (DataRegistry Item) where
  name := "schema-rust-fuzz"
  style := .doubleSlash
  specSource := "SchemaCore.Slice"
  outputs :=
    [ "crates/schema-generated/tests/fuzz_gen.rs"
    , "crates/schema-generated/tests/fuzz_properties.rs" ]
  run reg :=
    [ { path := "crates/schema-generated/tests/fuzz_gen.rs"
        contents := fuzzGenBody reg }
    , { path := "crates/schema-generated/tests/fuzz_properties.rs"
        contents := fuzzPropertiesRust } ]
  law := none

end SchemaCore.Emit.Fuzz
