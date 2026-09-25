/-
# SchemaCore.Emit.Rust — the Rust target (the codec's consumer lane)

Owner: the Rust-consumer lane (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/03-bidirectional.md (Lean owns meaning —
THE WIRE IS `SchemaCore.Codec`'s; Rust owns implementation; generated
Rust is never a second spec); notes/v3/12-construction.md §3 (the
emitter recipe: pure total run, outputs nodup in the type, the law or
an honest note) + §8 (the Rust host discipline: typed errors, never
panics on real error paths); notes/v3/01-core.md §6 (the relational
engine: the Lean↔Rust agreement is a correspondence row — its evidence
level is the DIFFERENTIAL, landed as the generated test vectors).

THE SHAPE: the emitter lifts each registered item's fields through the
DESCRIPTION layer (`descrOfTy` — option/list become the `Descr`
wrappers, every closed `Ty` ctor stays a `.prim` leaf), renders the
record as a Rust struct, and generates the codec impls whose bytes are
`SchemaCore.Codec`'s wire EXACTLY (the differential over that wire is
the test artifact). The wire line-per-shape lives in `SchemaCore.Codec`
— one owner, cited, never re-encoded here.

DELIBERATE DIVERGENCE from legacy `SchemaLang.Emit.Rust` (mined intent,
fresh write): map/set render as `Vec<(K, V)>` / `Vec<K>`, NOT
`BTreeMap`/`BTreeSet` — the wire is order-preserving (Codec.lean's
map-canonicality note: insertion order IS payload data), and a tree
container would break the re-encode-byte-identically guarantee on
unsorted payloads. The canonical key-sorted rendering is the
Normalization-grade row when its consumer lands. Derives: Clone,
Debug, PartialEq, Eq (no floats in the slice's universe — the legacy
`hasFloat` fold has no consumer here). Identifiers: field names are
emitted AS-IS (the slice fixture's are Rust-clean); the mangle lane
(`rustIdent`/`pascal` in the legacy emitter) ports with the first
non-clean consumer — the honest gap, named.

THE GROWN API SURFACE (the general-Rust use case — the honest first
set, each row a discipline at the Rust surface):
- The 02 §3 determinacy discipline: every field gets the CONSERVATIVE
  collection query (`find_by_*`, `Vec`-shaped — no uniqueness claim),
  and the declared primary key ALSO gets the key-indexed lookup
  (`get_by_*`, `Option`-shaped — `SchemaCore.Keys`'
  `lookup?_atMostOne` is the theorem). The keys face is the PINNED
  `keysFace` rows (the emitter's run is pure over pinned data — the
  live keys registry is a different extension state, and importing
  KeysSlice into the replay chain would cycle through CheckSlice);
  the tooth tying the pin to the LIVE registry is SchemaTests'
  RustEmit spec. No key declared → NO lookup is invented (the
  conservative inference, at the emitter too).
- The builder discipline: a per-record TYPESTATE builder (the bon
  discipline, the honest MANUAL version — no dep): the set-ness of
  each field is a TYPE PARAMETER over the `Set`/`Unset` markers; the
  chained setters move the state index; `build` is implemented ONLY
  in the all-set state — a field never set means the wrong
  construction DOES NOT COMPILE (the guarantee rides Rust's types,
  never a test; the runtime `BuilderError` lane was the honest first
  set, and the typestate's arrival REMOVED it — no default is ever
  smuggled, not even an error path).
- The closed enums + the validated newtypes (the universe's own
  faces): `Profile`/`KeyTy` emit as Rust enums with the `strum`
  derives (`EnumIter`/`EnumCount`/`Display`/`EnumString` — the
  iteration + the string discipline; the tags are the LEAN ctor
  names, snake_case); the key materials + the deterministic carrier
  (`Fixed<SCALE>`) emit as newtypes with validation at construction
  (`try_new` — the ONE construction point, the gate's extension
  lane). Dep judgments: `strum` (derive) is the ONE dependency the
  enums' faces need (a hand iterator + parser per enum would be a
  parallel table over the derives' lawfulness); the newtypes are
  MANUAL (no nutype — a proc-macro lane to buy what a five-line
  generated newtype gives; no bon — the typestate builder above is
  the same guarantee without the dependency).
- The serde face: generated `Serialize`/`Deserialize` impls (JSON
  interop). HONEST ABOUT THE TWO: the schema's canonical codec is
  `SchemaCore.Codec`'s wire (the duel vectors are its differential);
  the serde impls are the ECOSYSTEM INTEROP face — a different byte
  encoding with its own conventions (missing field refuses, unknown
  field ignored as forward-compat, the field names as-is). Never a
  second wire spec: the wire of record stays the codec's.
  Dep judgment: `serde` (std feature, NO derive — the impls are hand-
  templated, no proc-macro lane) is the ONE added dependency;
  `serde_json` is dev-only (the round-trip tests).
- The migration lane's Rust face: the versioned types + the derived
  upcaster emitted as Rust (the migration lane landed Lean-side —
  SchemaCore.Migrate). The plan is DERIVED Lean-side; the pinned
  `examplePlan12` is what the Rust face renders, and SchemaTests'
  runtime pin ties `deriveUpcaster` to it (the wf-recursive
  derivation is kernel-opaque — runtime-pin, never rfl; 06 §2). A
  retype step has NO rendering (the remedy registry is Lean-side —
  the named gap); the emitted face covers carry + fill.

THE HONEST GAPS (each named, none silent):
- The emitter's naming precondition is the registry's own
  nodup-in-the-type (the same face the WIT lane carries; the old law
  literal was the proof field restated — the audit's
  vacuous-certificate finding, `law := none`). Identifier
  CLEANLINESS is NOT in that invariant (it is decidable but not a
  registry invariant; the fixture carries it) — a non-Rust-clean name
  lands as uncompilable generated code, caught by `cargo build`, not
  silently.
- The Rust varint caps at 10 continuation groups (2^70): every
  in-policy use — the u64/i64 atoms — fits in 10 groups, and Lean's
  unbounded-Nat decoder refuses the same longer bytes downstream
  (the 2^64 range gate, or truncation for counts). Different typed
  reasons, same refusal verdict; the differential pins the agreement.
- The differential vectors are the SLICE fixture's (the pinned Example
  row + per-shape atoms); a registry change that moves the fixture's
  shapes surfaces as a failing `cargo test`, not a silent pass.

The five questions (notes/v3/01-core.md):
- root: Crossing — the universe (`DataRegistry Item`) read into the
  Rust target grammar (structs + codecs + the differential vectors).
- carrier grade: the naming precondition is `DataRegistry`'s
  nodup-in-the-type (the certificate face retired — the audit's
  vacuous-certificate finding); the artifacts ride plain `run`. The
  Rust-side agreement is the correspondence's differential row (03 §3's
  evidence table).
- spine reading: the Interpretation stage (01 §5) — the SECOND emitter
  over the ONE regen core.
- ladder rung: total structural folds; the goldens are kernel-checked
  (the SchemaTests pins over `goldens`/`goldenExample` are `rfl`).
- gate row: gen-check byte-ties BOTH artifacts; `cargo test` is the
  differential's runner.

Core-only (imports SchemaCore.Describe, SchemaCore.Codec,
SchemaCore.Item — the cone rule).
-/

import SchemaCore.Emit.Spine
import SchemaCore.Describe
import SchemaCore.Codec
import SchemaCore.Item
import SchemaCore.Commit
import SchemaCore.Snapshot
import SchemaCore.Migrate
import Kit.Duel
import Kit.Mangle
import Kit.Text

open Kit
open Kit.Emit

namespace SchemaCore.Emit.Rust

/-! ## The description lift — the items ride the Describe layer in
     (MOVED to `Emit/Spine.lean` — the census's GENERIC band: the lift
     is target-independent; the delegating aliases keep this lane's
     spelling) -/

/-- The field-type lift (the SPINE's one copy; this alias is the
    lane's spelling of it). -/
abbrev descrOfTy := SchemaCore.Emit.Spine.descrOfTy

/-- The item's description (the SPINE's one copy; this alias is the
    lane's spelling of it). -/
abbrev itemDescr := SchemaCore.Emit.Spine.itemDescr

/-! ## The Rust rendering — types through the description, codecs
     through the boundary's wire folds -/

/- The closed universe's Rust text: MIGRATED to the ONE fold —
    `SchemaCore.tyRustPrim = foldTy rustAlg` (SchemaCore.Fold; 01-core
    §1's initial-algebra side, 07 R1's lowering instance). The algebra's
    rows are verbatim from this module's pre-fold hand walk; the
    wf-recursion machinery that walk needed (`tyNodeCount` +
    `termination_by` + the `keyTy_toTy_nodeCount` leg) is GONE — the
    fold is structural, so the kernel SEES the reduction (06 §2's
    opacity trap: the wf form blocked the golden theorems' kernel
    discharge). The codec template folds below are algebras too now
    (`encAlg`/`decAlg` over `String → String`), rows verbatim. The
    migration's proof is the byte-tie: `gates gen-check` holds the
    generated crate byte-identical. -/

/-- The description's Rust text: wrappers nest, leaves delegate. A
    nested PRODUCT cannot reach field position (the registry's rows are
    flat — the SD0006 refusal is upstream's guarantee); the arm is the
    honest dead branch, never a fabricated type. -/
def tyRust : Descr → String
  | .prim t => tyRustPrim t
  | .option d => "Option<" ++ tyRust d ++ ">"
  | .list d => "Vec<" ++ tyRust d ++ ">"
  | .product _ _ =>
      "() /* unreachable: the registry's rows are flat (SD0006) */"

/-- The record's Rust spelling: the last component of the Lean name,
    Pascal-cased — the ONE mangler's `Kit.pascal` (the hand walk
    is gone; byte-equality on the registry's names is the gen-check's
    byte-tie). -/
def pascalName (s : String) : String :=
  Kit.pascal (lastName s)

/-! ## The codec generation — the wire's Rust face

The LEAF templates are `++` concatenations (the interpolation braces do
not survive this Lean's format strings; the plain-concat form is also
the mechanically safer one — every Rust brace is literal). The
STRUCTURE above the leaves — statement sequences, blocks, the file
itself — rides `Kit.Text` (the rope rule, 06 §7b): O(1) `cat`/`sepBy`
assembly, ONE render at the consumer. The byte-exactness is the
`Kit.Text.render_cat_strs` / `render_sepBy_strs` bridge laws, proved
tree-side; `gates gen-check` is the artifact-side proof the rewire
moved no bytes. -/

/-- The KEY position's encode statements: the scalar templates as the
    key fold's algebra (one template table — the rows are `encAlg`'s
    scalars verbatim). -/
def keyEncAlg : KeyTyAlg (String → String) where
  bool e := "out.push(if *" ++ e ++ " { 1u8 } else { 0u8 });"
  u64 e := "enc_varint(*" ++ e ++ ", out);"
  i64 e := "enc_varint(zigzag_i64(*" ++ e ++ "), out);"
  string e := "enc_str(" ++ e ++ ".as_str(), out);"

/-- THE ENCODE STATEMENTS = the fold (migrated from wf-recursion to the
    ONE walk — the rows verbatim, the recursion structural and
    kernel-visible). `e` is the Rust expression HOLDING A REFERENCE to
    the value (`e : &T` throughout — the uniform convention lets the
    recursion compose). The bytes are `SchemaCore.Codec`'s wire, arm by
    arm. -/
def encAlg : TyAlg (String → String) where
  bool := keyEncAlg.bool
  u64 := keyEncAlg.u64
  i64 := keyEncAlg.i64
  string := keyEncAlg.string
  option a := fun e =>
      "match " ++ e ++ " { None => out.push(0u8), Some(inner) => " ++
      "{ out.push(1u8); " ++ a "inner" ++ " } };"
  list a := fun e =>
      "enc_varint((" ++ e ++ ").len() as u64, out); " ++
      "for inner in (" ++ e ++ ").iter() { " ++ a "inner" ++ " }"
  result ok err := fun e =>
      "match " ++ e ++ " { Ok(inner) => { out.push(0u8); " ++
      ok "inner" ++ " }, Err(inner) => { out.push(1u8); " ++
      err "inner" ++ " } };"
  map k v := fun e =>
      "enc_varint((" ++ e ++ ").len() as u64, out); " ++
      "for (innerk, innerv) in (" ++ e ++ ").iter() { " ++
      foldKeyTy keyEncAlg k "innerk" ++ " " ++ v "innerv" ++ " }"
  set k := fun e =>
      "enc_varint((" ++ e ++ ").len() as u64, out); " ++
      "for innerk in (" ++ e ++ ").iter() { " ++
      foldKeyTy keyEncAlg k "innerk" ++ " }"
  bounded _ := fun e => "enc_varint(*" ++ e ++ ", out);"

/-- The KEY position's decode statements: the scalar templates as the
    key fold's algebra (one template table, mirroring `keyEncAlg`). -/
def keyDecAlg : KeyTyAlg (String → String) where
  bool n := "let " ++ n ++ " = dec_bool(bs)?;"
  u64 n := "let " ++ n ++ " = dec_u64(bs)?;"
  i64 n := "let " ++ n ++ " = dec_i64(bs)?;"
  string n := "let " ++ n ++ " = dec_string(bs)?;"

/-- THE DECODE STATEMENTS = the fold (the encode side's migration
    mirrored). For a schema type `t` binding the Rust identifier `n`:
    after them, `n : T` is in scope and the cursor `bs` (a `&mut &[u8]`)
    has consumed exactly the value's bytes. Every out-of-policy shape
    refuses through the helpers' typed errors — never a silent misparse,
    never a panic. -/
def decAlg : TyAlg (String → String) where
  bool := keyDecAlg.bool
  u64 := keyDecAlg.u64
  i64 := keyDecAlg.i64
  string := keyDecAlg.string
  option a := fun n =>
      "let " ++ n ++ " = { let tag = dec_byte(bs)?; match tag " ++
      "{ 0u8 => None, 1u8 => { " ++ a "inner" ++
      " Some(inner) }, _ => return Err(CodecError::InvalidTag(tag)) } };"
  list a := fun n =>
      "let " ++ n ++ " = { let count = dec_varint(bs)?; " ++
      "let mut acc = Vec::new(); for _ in 0..count { " ++
      a "inner" ++ " acc.push(inner); } acc };"
  result ok err := fun n =>
      "let " ++ n ++ " = { let tag = dec_byte(bs)?; match tag " ++
      "{ 0u8 => { " ++ ok "inner" ++ " Ok(inner) }, " ++
      "1u8 => { " ++ err "inner" ++
      " Err(inner) }, _ => return Err(CodecError::InvalidTag(tag)) } };"
  map k v := fun n =>
      "let " ++ n ++ " = { let count = dec_varint(bs)?; " ++
      "let mut acc = Vec::new(); for _ in 0..count { " ++
      foldKeyTy keyDecAlg k "innerk" ++ " " ++ v "innerv" ++
      " acc.push((innerk, innerv)); } acc };"
  set k := fun n =>
      "let " ++ n ++ " = { let count = dec_varint(bs)?; " ++
      "let mut acc = Vec::new(); for _ in 0..count { " ++
      foldKeyTy keyDecAlg k "innerk" ++ " acc.push(innerk); } acc };"
  bounded cap := fun n =>
      "let " ++ n ++ " = dec_bounded(" ++ toString cap ++ "u64, bs)?;"

/- The per-field statement computation (the former `encStmts`/
`decStmts` local folds) is the SPINE's walk now — `spineRecordFacts`
composes THIS target's algs + conventions once per item; the record
template below consumes the facts. -/

/-! ## The generated runtime (the helpers the codecs call) -/

/-- The generated crate's prelude: the wire comment block, the typed
    error, and the shared runtime helpers. `pub` (a used-or-not helper
    is API, never dead code). Every item carries the item-level
    `#[rustfmt::skip]` (the crate-level inner form is unstable; the
    generated code is never hand-formatted). -/
def libPrelude : String :=
"//
// THE WIRE (SchemaCore.Codec — the byte contract, ONE owner, cited):
//   bool     one byte, 0 = false, 1 = true (any other byte refuses);
//   u64      the canonical minimal LEB128 varint;
//   i64      the varint of the zigzag of the value;
//   string   varint length + one varint code point per char (NOT UTF-8);
//   option   tag 0 = none, 1 = some + payload;
//   result   tag 0 = ok + payload, 1 = err + payload;
//   list/map/set  varint count + elements/entries in payload order;
//   bounded  the varint of the value (the cap gates at decode).
// The Rust varint caps at 10 continuation groups (see dec_varint):
// every in-policy atom fits; longer forms refuse on BOTH sides.

/// The typed refusal — every out-of-policy byte shape maps to a ctor
/// (SchemaCore.Codec's accepted-byte policy: the exact image of the
/// encoder). Never a panic, never a silent misparse.
#[derive(Debug, Clone, PartialEq, Eq)]
#[rustfmt::skip]
pub enum CodecError {
    Truncated,
    InvalidTag(u8),
    NonCanonicalVarint,
    VarintOverflow,
    U64Range,
    I64Range,
    InvalidChar(u64),
    CapViolation { cap: u64, got: u64 },
    TrailingBytes,
}

/// The canonical minimal LEB128 varint (the u64 atom's wire form).
#[rustfmt::skip]
pub fn enc_varint(mut n: u64, out: &mut Vec<u8>) {
    loop {
        if n < 128 {
            out.push(n as u8);
            return;
        }
        out.push((128 + n % 128) as u8);
        n /= 128;
    }
}

/// Read one byte off the cursor.
#[rustfmt::skip]
pub fn dec_byte(bs: &mut &[u8]) -> Result<u8, CodecError> {
    if bs.is_empty() {
        return Err(CodecError::Truncated);
    }
    let b = bs[0];
    *bs = &bs[1..];
    Ok(b)
}

/// The canonical minimal varint: a continuation group whose remaining
/// value is zero refuses (0x80 0x00 is NEVER accepted); beyond 10
/// groups the value refuses (see the header note — Lean's unbounded-Nat
/// decoder refuses the same bytes downstream).
#[rustfmt::skip]
pub fn dec_varint(bs: &mut &[u8]) -> Result<u128, CodecError> {
    let mut result: u128 = 0;
    let mut groups = 0u32;
    loop {
        if groups >= 10 {
            return Err(CodecError::VarintOverflow);
        }
        let b = dec_byte(bs)?;
        result |= ((b & 0x7f) as u128) << (7 * groups);
        if b < 128 {
            if groups > 0 && (result >> 7) == 0 {
                return Err(CodecError::NonCanonicalVarint);
            }
            return Ok(result);
        }
        groups += 1;
    }
}

/// Bool: one byte, 0 = false, 1 = true; any other byte refuses.
#[rustfmt::skip]
pub fn dec_bool(bs: &mut &[u8]) -> Result<bool, CodecError> {
    match dec_byte(bs)? {
        0u8 => Ok(false),
        1u8 => Ok(true),
        other => Err(CodecError::InvalidTag(other)),
    }
}

/// u64: the varint, range-gated at 2^64 (never a silent wrap).
#[rustfmt::skip]
pub fn dec_u64(bs: &mut &[u8]) -> Result<u64, CodecError> {
    let n = dec_varint(bs)?;
    if n <= u64::MAX as u128 {
        Ok(n as u64)
    } else {
        Err(CodecError::U64Range)
    }
}

/// The zigzag map (0 -> 0, -1 -> 1, 1 -> 2, ...): signed over varint.
#[rustfmt::skip]
pub fn zigzag_i64(v: i64) -> u64 {
    ((v << 1) ^ (v >> 63)) as u64
}

/// i64: the zigzag varint, re-checked (a zigzag outside the Int64
/// range refuses — never a silent wrap).
#[rustfmt::skip]
pub fn dec_i64(bs: &mut &[u8]) -> Result<i64, CodecError> {
    let n = dec_varint(bs)?;
    let m = n >> 1;
    let i: i128 = if n % 2 == 0 { m as i128 } else { -(m as i128 + 1) };
    if i >= i64::MIN as i128
        && i <= i64::MAX as i128
        && zigzag_i64(i as i64) as u128 == n
    {
        Ok(i as i64)
    } else {
        Err(CodecError::I64Range)
    }
}

/// String: varint length + one varint code point per char (NOT UTF-8 —
/// the char-varint wire is the provable atom; see SchemaCore.Codec).
#[rustfmt::skip]
pub fn enc_str(s: &str, out: &mut Vec<u8>) {
    enc_varint(s.chars().count() as u64, out);
    for c in s.chars() {
        enc_varint(c as u64, out);
    }
}

/// String, decode half: each code point validated (a value that is not
/// a Unicode scalar value refuses).
#[rustfmt::skip]
pub fn dec_string(bs: &mut &[u8]) -> Result<String, CodecError> {
    let count = dec_varint(bs)?;
    if count > usize::MAX as u128 {
        return Err(CodecError::VarintOverflow);
    }
    let mut acc = String::new();
    for _ in 0..(count as usize) {
        let n = dec_varint(bs)?;
        match u32::try_from(n).ok().and_then(char::from_u32) {
            Some(c) => acc.push(c),
            None => {
                return Err(CodecError::InvalidChar(
                    u64::try_from(n).unwrap_or(u64::MAX),
                ))
            }
        }
    }
    Ok(acc)
}

/// Bounded: the varint, gated at the cap (a cap-violating value
/// refuses — never a silent wrap).
#[rustfmt::skip]
pub fn dec_bounded(cap: u64, bs: &mut &[u8]) -> Result<u64, CodecError> {
    let n = dec_varint(bs)?;
    if n < cap as u128 {
        Ok(n as u64)
    } else {
        Err(CodecError::CapViolation {
            cap,
            got: u64::try_from(n).unwrap_or(u64::MAX),
        })
    }
}

/// The builder's state markers (the typestate's set-ness index —
/// the builder discipline carried in RUST's types: `build` exists
/// ONLY in the all-`Set` state, so a field never set means a wrong
/// construction does not COMPILE — never a runtime refusal).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[rustfmt::skip]
pub struct Set;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[rustfmt::skip]
pub struct Unset;

/// The closed enums + the newtype faces (the block after the runtime
/// helpers — the universe's own types, below)."

/-! ## The record rendering — the codec block + the grown API surface
     (the builder, the 02 §3 lookups, the serde face) -/
-- The Rust string literal is `Spine.strLit` (the shared C-family escape —
-- the enforcement wave's dedupe; the field-name spellings ride as-is,
-- the mangle gap — the header's note).

/-! ## The closed universe's Rust faces — the closed enums (strum) +
     the newtype construction discipline -/

/-- The closed enums + the validated newtypes (NOT registry-dependent
    — the universe's own faces, emitted once):

- THE CLOSED ENUMS (`Profile`, `KeyTy`) ride the `strum` derives:
  `EnumIter`/`EnumCount` (the iteration + the count discipline),
  `Display`/`EnumString` (the string discipline) — the tag strings
  are the LEAN ctor names, snake_case (the model's tag discipline).
  Dep judgment: `strum` (derive feature) is the ONE dependency the
  iteration/string faces need — a hand-written iterator + parser per
  enum would be a parallel table over the derives' lawfulness.
- THE NEWTYPES are MANUAL (the honest judgment: NO nutype dep — a
  proc-macro lane to buy what a five-line generated newtype gives):
  the key materials + the deterministic carrier enter through
  `try_new` — validation at construction, ONE point, never raw tuple
  exports, never checked after the fact. -/
def universeTypesRust : String :=
"// THE CLOSED UNIVERSE'S RUST FACES (the schema's closed enums + the\n" ++
"// scalar sub-universe + the deterministic carrier — the model's\n" ++
"// guarantees carried in RUST's types, not tests).\n//\n" ++
"// The closed enums ride the strum derives (the iteration + the\n" ++
"// string discipline: the tag strings are the LEAN ctor names,\n" ++
"// snake_case — the model's tag discipline). The newtypes are\n" ++
"// MANUAL (the dep judgment: no nutype/bon proc-macro lane — the\n" ++
"// honest manual version is the smaller, auditable one).\n\n" ++
"/// The closed Profile enum (SchemaCore.Profile — WHICH semantic a\n/// scalar carries). CLOSED: the `fast` slot (the hardware-float\n/// trade, its forfeits named) extends with its full fold — the\n/// compiler drives every consumer's match — when its consumer lands.\n#[derive(Clone, Debug, PartialEq, Eq, Hash,\n  strum::EnumIter, strum::EnumCount, strum::Display, strum::EnumString)]\n#[strum(serialize_all = \"snake_case\")]\npub enum Profile {\n    /// The bare scalar's own semantics (the default).\n    Plain,\n    /// The fixed-point discipline (`Fixed` — the carrier below):\n    /// exact checked addition, named floor rounding, total order,\n    /// codec-legal on the u64 wire row.\n    Deterministic,\n}\n\n" ++
"/// The closed scalar sub-universe (SchemaCore.Ty's KeyTy — the\n/// map/set keys + the declared keys' admitted materials).\n#[derive(Clone, Debug, PartialEq, Eq, Hash,\n  strum::EnumIter, strum::EnumCount, strum::Display, strum::EnumString)]\n#[strum(serialize_all = \"snake_case\")]\npub enum KeyTy {\n    Bool,\n    U64,\n    I64,\n    String,\n}\n\n" ++
"/// The key MATERIAL newtypes (the keys lane's admission gate\n/// `keyOfTy`: only scalars are key material — these wrappers ARE\n/// that gate's Rust face). Values enter through `try_new` —\n/// validation at construction, ONE point; the model's next key\n/// invariant lands HERE, never at the consumers.\n#[rustfmt::skip]\n#[derive(Clone, Debug, PartialEq, Eq, Hash)]\npub struct KeyBool(bool);\n\n#[rustfmt::skip]\nimpl KeyBool {\n    /// The admitted key material (the gate's extension point).\n    pub fn try_new(b: bool) -> Option<KeyBool> { Some(KeyBool(b)) }\n    /// The carried scalar (the read face — the wire codecs take it).\n    pub fn get(&self) -> bool { self.0 }\n}\n\n#[rustfmt::skip]\n#[derive(Clone, Debug, PartialEq, Eq, Hash)]\npub struct KeyU64(u64);\n\n#[rustfmt::skip]\nimpl KeyU64 {\n    pub fn try_new(n: u64) -> Option<KeyU64> { Some(KeyU64(n)) }\n    pub fn get(&self) -> u64 { self.0 }\n}\n\n#[rustfmt::skip]\n#[derive(Clone, Debug, PartialEq, Eq, Hash)]\npub struct KeyI64(i64);\n\n#[rustfmt::skip]\nimpl KeyI64 {\n    pub fn try_new(n: i64) -> Option<KeyI64> { Some(KeyI64(n)) }\n    pub fn get(&self) -> i64 { self.0 }\n}\n\n#[rustfmt::skip]\n#[derive(Clone, Debug, PartialEq, Eq, Hash)]\npub struct KeyString(String);\n\n#[rustfmt::skip]\nimpl KeyString {\n    pub fn try_new(s: String) -> Option<KeyString> { Some(KeyString(s)) }\n    pub fn get(&self) -> &str { &self.0 }\n}\n\n" ++
"/// The deterministic carrier (SchemaCore.Profile's `Fixed scale` —\n/// the `Money Cents` shape): the value IS `units`, an integer of the\n/// scale's units; the rational reading is `units / SCALE`. The scale\n/// lives in the TYPE (erases at runtime); the u64 wire capacity\n/// lives in the type too (out-of-contract values unconstructible).\n///\n/// The PROMISES (each the model's law, never a hope): EXACT checked\n/// addition (the overflow refuses — never a silent wrap), NAMED\n/// floor rounding for multiplication (error strictly under one\n/// unit), TOTAL order (no NaN hole). The FORFEITS (named, honesty\n/// cuts both ways): hardware-float speed, dynamic range (magnitudes\n/// past 2^64 / SCALE units refuse).\n#[rustfmt::skip]\n#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]\npub struct Fixed<const SCALE: u64>(u64);\n\n#[rustfmt::skip]\nimpl<const SCALE: u64> Fixed<SCALE> {\n    /// The validated constructor: the scale-positivity gate lives\n    /// HERE (a `Fixed<0>` is never constructible — a zero scale\n    /// divides by zero; the model refuses at the ONE construction\n    /// point, never after the fact).\n    pub fn try_new(units: u64) -> Option<Fixed<SCALE>> {\n        if SCALE == 0 {\n            return None;\n        }\n        Some(Fixed(units))\n    }\n\n    /// The units (the raw carrier — the wire face + the arithmetic\n    /// read it; the rational reading is `units / SCALE`).\n    pub fn units(&self) -> u64 { self.0 }\n\n    /// EXACT addition: the units' sum, no rounding; the wire\n    /// capacity's overflow REFUSES (never a silent wrap).\n    pub fn add_checked(&self, other: &Fixed<SCALE>) -> Option<Fixed<SCALE>> {\n        self.0.checked_add(other.0).and_then(Fixed::try_new)\n    }\n\n    /// The named rounding for multiplication: the exact rational\n    /// product, FLOORED (the truncating division — the error is\n    /// strictly under one unit); the capacity's overflow refuses.\n    /// (Unreachable for a zero scale: a `Fixed<0>` is unconstructible.)\n    pub fn mul_floor(&self, other: &Fixed<SCALE>) -> Option<Fixed<SCALE>> {\n        let p = (self.0 as u128) * (other.0 as u128);\n        let q = p / (SCALE as u128);\n        if q <= u64::MAX as u128 {\n            Fixed::try_new(q as u64)\n        } else {\n            None\n        }\n    }\n\n    /// CODEC LEGALITY (the model's promise): the carrier rides the\n    /// EXISTING u64 wire row — the bytes are the bare u64 varint's,\n    /// byte-for-byte, both directions.\n    pub fn encode(&self, out: &mut Vec<u8>) {\n        enc_varint(self.0, out);\n    }\n\n    /// The wire face, decode half (append-form; the exact-image form\n    /// is the caller's `decode_full` discipline over the cursor).\n    pub fn decode(bs: &mut &[u8]) -> Option<Fixed<SCALE>> {\n        dec_u64(bs).ok().and_then(Fixed::try_new)\n    }\n}\n"

/-- The field list's (name, Rust type) pairs (the API templates'
    shared walk — the descr lift is ONE lift). -/
def fieldRustTys (item : Item) : List (String × String) :=
  item.fields.map fun f => (f.name, tyRust (descrOfTy f.ty))

/-- The pinned keys face: `(record, key field)` rows. The emitter's
    run is pure over THIS pin — the live keys registry is a different
    extension state (KeysSlice is not in the replay chain: importing
    it under Slice would cycle through CheckSlice); the tooth tying
    the pin to the LIVE registry (`exampleKey`) is SchemaTests'
    RustEmit spec. A record absent here gets NO key-indexed lookup —
    the conservative inference, at the emitter too (02 §3). -/
def keysFace : List (String × String) := [("Example", "label")]

/-- The key-lookup row for an item: the (field, `KeyTy`) when the
    pinned keys face declares a SCALAR key on the record (the
    `keyOfTy` gate — Snapshot's ONE `Ty` → `KeyTy` gate, reused, never
    a parallel table). -/
def keyRowOfItem (item : Item) : Option (String × KeyTy) :=
  (keysFace.find? fun p => p.1 == item.name).bind fun p =>
    (item.fields.find? fun f => f.name == p.2).bind fun f =>
      (keyOfTy f.ty).map fun k => (f.name, k)

/-- The scalar key's Rust parameter type (`&str` at the boundary — the
    key universe's slice; the other scalars spell as themselves). -/
def keyParamRust : KeyTy → String
  | .string => "&str"
  | k => tyRustPrim k.toTy

/-- The key-indexed lookup's text: `some` when the pinned keys face
    declares a scalar key on this record — the Option shape (02 §3:
    `lookup?_atMostOne` is the theorem, the shape is its Rust face);
    `none` = no declared scalar key, so NO lookup is invented. -/
def renderKeyLookup (item : Item) : Option String :=
  let name := pascalName item.name
  keyRowOfItem item |>.map fun p =>
    "    /// The key-indexed lookup (notes/v3/02-data-plane.md §3): the\n" ++
    "    /// declared primary key's determinacy makes the query\n" ++
    "    /// Option-shaped — at most one row (SchemaCore.Keys'\n" ++
    "    /// `lookup?_atMostOne` is the theorem; this is its Rust shape).\n" ++
    "    pub fn get_by_" ++ p.1 ++ "<'a>(rows: &'a [" ++ name ++
      "], key: " ++ keyParamRust p.2 ++ ") -> Option<&'a " ++ name ++ "> {\n" ++
    "        rows.iter().find(|r| r." ++ p.1 ++ " == key)\n" ++
    "    }\n"

/-- One field's conservative query: the collection shape (02 §3 — NO
    uniqueness claim, every match returns; the discipline, not an
    oversight). -/
def renderFinder (name : String) (p : String × String) : String :=
  "    /// The conservative field query (02 §3): NO uniqueness claim —\n" ++
  "    /// every match returns (the collection shape is the surface\n" ++
  "    /// without a declared key; the determinacy discipline).\n" ++
  "    pub fn find_by_" ++ p.1 ++ "<'a>(rows: &'a [" ++ name ++
    "], value: &" ++ p.2 ++ ") -> Vec<&'a " ++ name ++ "> {\n" ++
  "        rows.iter().filter(|r| &r." ++ p.1 ++ " == value).collect()\n" ++
  "    }\n"

/-- One record's builder block — the BON-style discipline, the honest
    MANUAL version (the dep judgment: no bon dep — the typestate is
    fully expressible as a plain generated generic; a proc-macro lane
    would add a dependency to buy nothing the template doesn't
    already give). The set-ness of each field is a TYPE PARAMETER
    (`Set`/`Unset`, the markers): the chained setters move the state
    index field by field, and `build` is implemented ONLY in the
    all-set state — a field never set means the wrong construction
    does not COMPILE (the guarantee in the types, not a test; the
    runtime `BuilderError` lane is GONE — no default is ever
    smuggled, not even an error path). -/
def renderBuilder (item : Item) : String :=
  let name := pascalName item.name
  let fts := fieldRustTys item
  let n := fts.length
  let params := (List.range n).map fun i => "F" ++ toString i
  let allUnset := String.intercalate ", " (params.map fun _ => "Unset")
  let allSet := String.intercalate ", " (params.map fun _ => "Set")
  let generics := String.intercalate ", " params
  let decls := String.intercalate "\n"
    (fts.map fun p => "    " ++ p.1 ++ ": Option<" ++ p.2 ++ ">,")
  let inits := String.intercalate ", " (fts.map fun p => p.1 ++ ": None")
  -- the setter i: the impl fixes Fi to Unset, the return to Set
  let setters := String.intercalate "\n\n" ((fts.zip (List.range n)).map fun p =>
    let i := p.2
    let implArgs := String.intercalate ", " ((params.zip (List.range n)).map fun q =>
      if q.2 == i then "Unset" else "F" ++ toString q.2)
    let retArgs := String.intercalate ", " ((params.zip (List.range n)).map fun q =>
      if q.2 == i then "Set" else "F" ++ toString q.2)
    let moves := String.intercalate ", "
      ((fts.zip (List.range n)).filterMap fun q =>
        if q.2 == i then none else some (q.1.1 ++ ": self." ++ q.1.1))
    let implVars := String.intercalate ", "
      ((params.zip (List.range n)).filter (fun q => q.2 != i)
        |>.map fun q => "F" ++ toString q.2)
    "impl" ++ (if implVars.isEmpty then "" else "<" ++ implVars ++ ">") ++ " " ++
      name ++ "Builder<" ++ implArgs ++ "> {\n" ++
    "    /// Set `" ++ p.1.1 ++ "` (the state index moves Unset -> Set).\n" ++
    "    pub fn " ++ p.1.1 ++ "(self, " ++ p.1.1 ++ ": " ++ p.1.2 ++
      ") -> " ++ name ++ "Builder<" ++ retArgs ++ "> {\n" ++
    "        " ++ name ++ "Builder {\n" ++
    "            " ++ p.1.1 ++ ": Some(" ++ p.1.1 ++ "),\n" ++
    (if moves.isEmpty then "" else "            " ++ moves ++ ",\n") ++
    "            state: std::marker::PhantomData,\n" ++
    "        }\n" ++
    "    }\n" ++
    "}\n"
    )
  let builds := String.intercalate "\n" (fts.map fun p =>
    "            " ++ p.1 ++ ": self." ++ p.1 ++
    ".expect(\"inhabited by the builder's type index\"),")
  "#[rustfmt::skip]\n" ++
  "pub struct " ++ name ++ "Builder<" ++ generics ++ "> {\n" ++ decls ++ "\n" ++
  "    state: std::marker::PhantomData<(" ++ generics ++ ")>,\n" ++
  "}\n\n" ++
  "#[rustfmt::skip]\n" ++
  "impl " ++ name ++ " {\n" ++
  "    /// The builder's entry: every field unset (and `build` is not\n" ++
  "    /// callable until each setter has moved its state index).\n" ++
  "    pub fn builder() -> " ++ name ++ "Builder<" ++ allUnset ++ "> {\n" ++
  "        " ++ name ++ "Builder {\n" ++
  "            " ++ inits ++ ",\n" ++
  "            state: std::marker::PhantomData,\n" ++
  "        }\n" ++
  "    }\n" ++
  "}\n\n" ++
  setters ++ "\n\n" ++
  "#[rustfmt::skip]\n" ++
  "impl " ++ name ++ "Builder<" ++ allSet ++ "> {\n" ++
  "    /// The disciplined constructor — TOTAL at the type level: it\n" ++
  "    /// exists ONLY in the all-set state (the wrong construction\n" ++
  "    /// does not compile). The `expect` is the type index's\n" ++
  "    /// unreachable arm, never a real error path.\n" ++
  "    pub fn build(self) -> " ++ name ++ " {\n" ++
  "        " ++ name ++ " {\n" ++ builds ++ "\n        }\n" ++
  "    }\n" ++
  "}\n"

/-- One record's serde face (the JSON interop). HONEST ABOUT THE TWO:
    the canonical codec is SchemaCore.Codec's wire (the duel vectors
    are its differential); the serde impls are the ECOSYSTEM INTEROP
    face — a different byte encoding with its own conventions: the
    field names as-is (the mangle gap), a missing field refuses
    (typed serde error), an unknown field is IGNORED (the ecosystem's
    forward-compat convention — an extension is interop, not drift),
    a duplicate field refuses. The impls are hand-templated (no
    derive proc-macro — the dep discipline: minimal; `serde` with the
    std feature is the ONE added dependency). Never a second wire
    spec: the wire of record stays the codec's. -/
def renderSerde (item : Item) : String :=
  let name := pascalName item.name
  let fts := fieldRustTys item
  let ser := String.intercalate "\n" (fts.map fun p =>
    "        st.serialize_field(" ++ Spine.strLit p.1 ++ ", &self." ++ p.1 ++ ")?;")
  let accums := String.intercalate "\n" (fts.map fun p =>
    "                let mut " ++ p.1 ++ ": Option<" ++ p.2 ++ "> = None;")
  let arms := String.intercalate "\n" (fts.map fun p =>
    "                        " ++ Spine.strLit p.1 ++ " => {\n" ++
    "                            if " ++ p.1 ++ ".is_some() {\n" ++
    "                                return Err(serde::de::Error::duplicate_field(" ++
      Spine.strLit p.1 ++ "));\n" ++
    "                            }\n" ++
    "                            " ++ p.1 ++ " = Some(map.next_value()?);\n" ++
    "                        }")
  let builds := String.intercalate "\n" (fts.map fun p =>
    "                    " ++ p.1 ++ ": " ++ p.1 ++
    ".ok_or_else(|| serde::de::Error::missing_field(" ++ Spine.strLit p.1 ++ "))?,")
  let names := String.intercalate ", " (fts.map fun p => Spine.strLit p.1)
  "#[rustfmt::skip]\n" ++
  "impl serde::Serialize for " ++ name ++ " {\n" ++
  "    fn serialize<S: serde::Serializer>(&self, serializer: S)\n" ++
  "        -> Result<S::Ok, S::Error> {\n" ++
  "        use serde::ser::SerializeStruct;\n" ++
  "        let mut st = serializer.serialize_struct(" ++ Spine.strLit name ++ ", " ++
    toString item.fields.length ++ ")?;\n" ++
  ser ++ "\n" ++
  "        st.end()\n" ++
  "    }\n" ++
  "}\n\n" ++
  "#[rustfmt::skip]\n" ++
  "impl<'de> serde::Deserialize<'de> for " ++ name ++ " {\n" ++
  "    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D)\n" ++
  "        -> Result<Self, D::Error> {\n" ++
  "        struct " ++ name ++ "Visitor;\n" ++
  "        impl<'de> serde::de::Visitor<'de> for " ++ name ++ "Visitor {\n" ++
  "            type Value = " ++ name ++ ";\n" ++
  "            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {\n" ++
  "                f.write_str(" ++ Spine.strLit ("struct " ++ name) ++ ")\n" ++
  "            }\n" ++
  "            fn visit_map<A: serde::de::MapAccess<'de>>(\n" ++
  "                self, mut map: A,\n" ++
  "            ) -> Result<" ++ name ++ ", A::Error> {\n" ++
  accums ++ "\n" ++
  "                while let Some(k) = map.next_key::<String>()? {\n" ++
  "                    match k.as_str() {\n" ++
  arms ++ "\n" ++
  "                        _ => {\n" ++
  "                            let _ = map.next_value::<serde::de::IgnoredAny>()?;\n" ++
  "                        }\n" ++
  "                    }\n" ++
  "                }\n" ++
  "                Ok(" ++ name ++ " {\n" ++ builds ++ "\n                })\n" ++
  "            }\n" ++
  "        }\n" ++
  "        deserializer.deserialize_struct(" ++ Spine.strLit name ++ ", &[" ++ names ++
    "], " ++ name ++ "Visitor)\n" ++
  "    }\n" ++
  "}\n"

/-! ## The record block, on the SPINE (the seam's migration)

The record's API faces are `Spine.TargetFace` ROWS (the design note's
"rows + instances" rule — the builder / lookups / serde faces are
data, placed by name); the block's TEMPLATE is this target's
`rustRenderRecord`, consuming the SPINE's per-record facts (the type
lift + the two algs' statements — one shared walk) and placing the
faces by name. The leaf strings are IDENTICAL to the pre-spine form,
in the same order — `gates gen-check` is the byte-identity proof.
    -/

/-- ONE item's observability face (wave-30 C1 — the plan's
    observability TargetFace): ONE dotted-static `scope!` per schema
    operation, the schema's namespace path as the scope-name source
    (`schema.<record>.<op>` — the `ledger.propose`/`ledger.check`/
    `ledger.commit` shapes). The CARDINALITY RULE (fast-observe's,
    surfaced): dotted-static 'static low-cardinality names ONLY — the
    interned name leaks, so a record identity or an op kind is a scope
    NAME and high-cardinality data rides log kv, NEVER scope tags.
    Defined BEFORE `rustFaces` (Lean's def-before-use; the snake spelling
    is `snakeName`'s ONE fold inlined — `Kit.snake ∘ lastName`). -/
def renderObservability (item : Item) : String :=
  let ns := "schema." ++ Kit.snake (lastName item.name)
  String.intercalate "\n"
    ["    /// The operation spans (C1's observability face: the schema's",
     "    /// namespace path as the scope-name source — dotted-static,",
     "    /// 'static low-cardinality ONLY; high-cardinality data rides log",
     "    /// kv, NEVER scope tags — the interned name leaks).",
     "    pub const ENCODE_SPAN: &str = " ++ Spine.strLit (ns ++ ".encode") ++ ";",
     "    pub const DECODE_SPAN: &str = " ++ Spine.strLit (ns ++ ".decode") ++ ";",
     "",
     "    /// Enter the encode operation's span (bind the guard: a dropped",
     "    /// guard is a zero-length span).",
     "    #[inline]",
     "    pub fn encode_scope() -> fast_observe::profiling::ScopeGuard {",
     "        fast_observe::scope!(Self::ENCODE_SPAN)",
     "    }",
     "",
     "    /// Enter the decode operation's span (bind the guard: a dropped",
     "    /// guard is a zero-length span).",
     "    #[inline]",
     "    pub fn decode_scope() -> fast_observe::profiling::ScopeGuard {",
     "        fast_observe::scope!(Self::DECODE_SPAN)",
     "    }"]

/-- The Rust record block's face rows (the opted-in API disciplines,
    as data — the SPINE's `TargetFace` shape at this lane's
    parameters). -/
def rustFaces : List Spine.TargetFace :=
  [ { name := "keyLookup"
      render := fun item =>
        match renderKeyLookup item with
        | some k => .str (k ++ "\n")
        | none => .str "" }
  , { name := "finders"
      render := fun item =>
        Text.sepBy "\n"
          (item.fields.map fun f =>
            .str (renderFinder (pascalName item.name)
              (f.name, tyRust (descrOfTy f.ty)))) }
  , { name := "observability"
      render := fun item => .str (renderObservability item ++ "\n") }
  , { name := "builder"
      render := fun item => .str (renderBuilder item ++ "\n") }
  , { name := "serde"
      render := fun item => .str (renderSerde item) } ]

/-- One item → one Rust struct + its codec impl + its API surface
    (pure, total) — the SPINE's record template at this lane's
    parameters. The item-level `#[rustfmt::skip]` covers struct +
    impl; the codecs are generated code, never hand-formatted. -/
def rustRenderRecord :
    Spine.RecordFacts → (String → Option Text) → Text :=
  fun facts face =>
  let name := facts.name
  let fieldDecls := facts.fields.map fun p =>
    .str ("    pub " ++ p.1 ++ ": " ++ p.2 ++ ",")
  let encLines := facts.enc.map fun e => .str ("        " ++ e)
  let decLines := facts.dec.map fun d => .str ("        " ++ d)
  let shorthand := String.intercalate ", " (facts.fields.map (·.1))
  Text.cat
    [ .str "#[rustfmt::skip]\n#[derive(Clone, Debug, PartialEq, Eq)]\n"
    , .str ("pub struct " ++ name ++ " {\n")
    , Text.sepBy "\n" fieldDecls
    , .str "\n}\n\n"
    , .str ("#[rustfmt::skip]\nimpl " ++ name ++ " {\n")
    , .str "    /// Encode in SchemaCore.Codec's wire form (fields in schema order).\n"
    , .str "    pub fn encode(&self, out: &mut Vec<u8>) {\n"
    , .str "        // the operation's span (C1 — bind the guard: a dropped\n"
    , .str "        // guard is a zero-length span)\n"
    , .str "        let _span = Self::encode_scope();\n"
    , Text.sepBy "\n" encLines
    , .str "\n    }\n\n"
    , .str "    /// Decode in SchemaCore.Codec's wire form (append-form: the\n"
    , .str "    /// unconsumed suffix stays on the cursor). Out-of-policy bytes\n"
    , .str "    /// are a typed CodecError, never a panic, never a silent misparse.\n"
    , .str ("    pub fn decode(bs: &mut &[u8]) -> Result<" ++ name ++ ", CodecError> {\n")
    , .str "        let _span = Self::decode_scope();\n"
    , Text.sepBy "\n" decLines
    , .str ("\n        Ok(" ++ name ++ " { " ++ shorthand ++ " })\n")
    , .str "    }\n\n"
    , .str "    /// The exact-image form: decode and require the whole input.\n"
    , .str ("    pub fn decode_full(bs: &[u8]) -> Result<" ++ name ++ ", CodecError> {\n")
    , .str "        let mut rest = bs;\n"
    , .str "        let value = Self::decode(&mut rest)?;\n"
    , .str "        if !rest.is_empty() {\n"
    , .str "            return Err(CodecError::TrailingBytes);\n"
    , .str "        }\n"
    , .str "        Ok(value)\n"
    , .str "    }\n\n"
    , face "keyLookup" |>.getD .nil
    , face "finders" |>.getD .nil
    , face "observability" |>.getD .nil
    , .str "}\n\n"
    , face "builder" |>.getD .nil
    , face "serde" |>.getD .nil ]

/-! ## The migration lane's Rust face — the versioned types + the
     derived upcaster (SchemaCore.Migrate is the Lean-side owner) -/

mutual
/-- The value's Rust literal (the fill defaults' rendering; total over
    the closed universe — the emitter's discipline). The `fill` step's
    value is the DERIVED plan's data; this renders it — defaultVal?'s
    image (Keys.lean) is what the derivation fills, and the emitted
    literal IS the rendered value, never a re-derived default. -/
def valueRust : (t : Ty) → Value t → String
  | .bool, .bool b => if b then "true" else "false"
  | .u64, .u64 n => toString n ++ "u64"
  | .i64, .i64 n => toString n ++ "i64"
  | .string, .string s => "String::from(" ++ Spine.strLit s ++ ")"
  | .option _, .none => "None"
  | .option t, .some v => "Some(" ++ valueRust t v ++ ")"
  | .result ok _, .ok v => "Ok(" ++ valueRust ok v ++ ")"
  | .result _ err, .err v => "Err(" ++ valueRust err v ++ ")"
  | .list _, .list vl => "vec![" ++ String.intercalate ", " (vListStrings vl) ++ "]"
  | .map _ _, .map vm => "vec![" ++ String.intercalate ", " (vMapStrings vm) ++ "]"
  | .set _, .set vl => "vec![" ++ String.intercalate ", " (vListStrings vl) ++ "]"
  | .bounded _, .bounded f => toString f.val ++ "u64"

/-- The Rust literal's element strings (the comma-join's operand —
    `String.intercalate` IS the hand last-arm case split). -/
def vListStrings : {t : Ty} → VList t → List String
  | _, .nil => []
  | _, .cons v vs => valueRust _ v :: vListStrings vs

/-- The Rust literal's element strings (the map edition: `(k, v)` tuples). -/
def vMapStrings : {k : KeyTy} → {v : Ty} → VMap k v → List String
  | _, _, .nil => []
  | _, _, .cons k v rest =>
      ("(" ++ valueRust _ k ++ ", " ++ valueRust _ v ++ ")") :: vMapStrings rest
end

/-- The plan's step list (the doc line's content — the plan is data;
    the steps render, never re-derive). -/
def planSteps : {old new : List Field} → FieldPlan old new → List String
  | _, _, .nil => []
  | _, _, .carry f p => s!"carry {f.name}" :: planSteps p
  | _, _, .retype fO fN _ _ p => s!"retype {fO.name} -> {fN.name}" :: planSteps p
  | _, _, .fill f _ p => s!"fill {f.name} (the type's default)" :: planSteps p

/-- The upcast body's field inits, from the plan (the derived
    upcaster's Rust face): `field: v.field` per carry, the value's
    Rust literal per fill. `none` = a retype step — the plan's value
    map has NO Rust face yet (the remedy registry is Lean-side; the
    first retyping consumer lands it — the named gap, never a
    fabricated map). -/
def planUpcastInits? : {old new : List Field} →
    FieldPlan old new → Option (List String)
  | _, _, .nil => some []
  | _, _, .carry f p =>
      (planUpcastInits? p).map fun rest => (f.name ++ ": v." ++ f.name) :: rest
  | _, _, .retype _ _ _ _ _ => none
  | _, _, .fill f v p =>
      (planUpcastInits? p).map fun rest =>
        (f.name ++ ": " ++ valueRust f.ty v) :: rest

/-- The versioned fixture (the migration face's spec): v1's fields,
    v2 = v1 + the ADDED `delta` (i64) at the END (the derivation's
    order-aligned discipline — a mid-list addition refuses). -/
def exampleV1 : Item :=
  { name := "ExampleV1"
    fields := [ { name := "ready", ty := .bool }
              , { name := "count", ty := .u64 }
              , { name := "label", ty := .string } ] }

/-- The versioned fixture's NEW face (the migration face's spec). -/
def exampleV2 : Item :=
  { name := "ExampleV2"
    fields := [ { name := "ready", ty := .bool }
              , { name := "count", ty := .u64 }
              , { name := "label", ty := .string }
              , { name := "delta", ty := .i64 } ] }

/-- THE PINNED PLAN: the migration face renders THIS (the Rust face is
    the plan's — never a second derivation). The DERIVATION's agreement
    (`deriveUpcaster` returns exactly this plan for the versioned
    fixture, key `label`, no remedies — the add is remedied by the
    type's default) is pinned at runtime in SchemaTests (the
    kernel-opacity rule: `deriveFieldPlan` is wf-recursive —
    runtime-pin, never rfl; 06 §2). The key `label` is carried
    UNCHANGED — `stableKey` (08 §19). -/
def examplePlan12 : FieldPlan exampleV1.fields exampleV2.fields :=
  .carry { name := "ready", ty := .bool }
    (.carry { name := "count", ty := .u64 }
      (.carry { name := "label", ty := .string }
        (.fill { name := "delta", ty := .i64 } (.i64 0) .nil)))

/-- The versioned fixture's fn-name face: the item's name snake-cased —
    the ONE mangler's `Kit.snake` (the mirror of `pascalName`'s
    delegation; gen-check holds the bytes). -/
def snakeName (s : String) : String :=
  Kit.snake s

/-- One versioned struct's text (the versioned types' face). -/
def versionedStruct (item : Item) : String :=
  let decls := String.intercalate "\n"
    (item.fields.map fun f =>
      "    pub " ++ f.name ++ ": " ++ tyRust (descrOfTy f.ty) ++ ",")
  "#[rustfmt::skip]\n#[derive(Clone, Debug, PartialEq, Eq)]\n" ++
  "pub struct " ++ pascalName item.name ++ " {\n" ++ decls ++ "\n}\n"

/-- The migration face's text: the two versioned structs + the derived
    upcaster's fn (the plan's steps rendered — carry rows ride
    `v.field`, the fill row its default's literal; a retype step would
    render the named gap, never a fabricated map). -/
def renderMigrate : String :=
  let v1 := pascalName exampleV1.name
  let v2 := pascalName exampleV2.name
  let steps := String.intercalate ", " (planSteps examplePlan12)
  let body :=
    match planUpcastInits? examplePlan12 with
    | none =>
        "    // the upcaster's Rust face is the named gap: a retype step has\n" ++
        "    // no rendering yet (the remedy registry is Lean-side)\n"
    | some inits =>
        let lines := String.intercalate ",\n" inits
        "/// The derived upcaster (SchemaCore.Migrate's plan, rendered).\n" ++
        "#[rustfmt::skip]\n" ++
        "pub fn upcast_" ++ snakeName exampleV1.name ++ "_to_" ++
          snakeName exampleV2.name ++ "(v: " ++ v1 ++ ") -> " ++ v2 ++ " {\n" ++
        "    " ++ v2 ++ " {\n" ++ lines ++ "\n    }\n" ++
        "}\n"
  "// THE MIGRATION LANE'S RUST FACE (SchemaCore.Migrate — the migration\n" ++
  "// lane landed Lean-side; this is its Rust surface): the versioned\n" ++
  "// types + the derived upcaster. The plan is DERIVED Lean-side from\n" ++
  "// the diff's change set + the type's defaults; SchemaTests pins the\n" ++
  "// derivation to the plan below (runtime pin — the wf-recursive\n" ++
  "// derivation is kernel-opaque, 06 §2); the fn renders the plan's\n" ++
  "// steps, never a second derivation. The key `label` is carried\n" ++
  "// UNCHANGED (stable identities, notes/v3/08-capabilities.md §19).\n" ++
  "//\n" ++
  "// The plan (v1 -> v2): " ++ steps ++ "\n\n" ++
  versionedStruct exampleV1 ++ "\n" ++
  versionedStruct exampleV2 ++ "\n" ++
  body ++ "\n" ++
  -- the versioned types ride the SAME serde template (one face, never
  -- a second spelling — the interop lane covers the versions too)
  renderSerde exampleV1 ++ "\n" ++
  renderSerde exampleV2

/-! ## The differential — the correspondence's evidence (03 §3)

The vectors' bytes are COMPUTED by `SchemaCore.Codec`'s `encVal` over
the pinned fixture values (never hand-written) and committed through
the byte-tie.

UPDATE (the duel migration — the named follow-up, landed): the vectors
ride `Kit.Duel`'s vector-set convention now — ONE directory per duel,
the vector files as the BINARY lane's artifacts, plus a committed text
manifest (the generator row + one `<path>\t<expectation>` row per
vector: `decode <note>` / `refuse`). The generated Rust test is the
duel's consumer (Kit.Duel's contract: read the manifest, skip the
2-line GENERATED header, split each row on the tab); the vectors'
bytes stay `encVal`'s, and the atoms' value-level pins ride the
manifest's `decode` notes — a drift still fails the
decode-then-compare loudly. The manifest byte-ties through `regen`
(the text lane); the binary lane's byte-tie (`Kit.Emit.tieBytes` wired
into the gen-check gate) is the named follow-up — the first binary
artifacts committed through `just gen` land here. -/

/-- The pinned Example row: the fixture's fields in schema order, each
    field's `encVal` bytes concatenated — the wire contract the
    generated `Example::encode` must reproduce byte-for-byte. -/
def goldenExample : List UInt8 :=
  encVal .bool (.bool true)
    ++ encVal .u64 (.u64 300)
    ++ encVal .i64 (.i64 (-1))
    ++ encVal .string (.string "hi")
    ++ encVal (.option .string) (.some (.string "note"))
    ++ encVal (.list .string)
        (.list (.cons (.string "a") (.cons (.string "b") .nil)))

/-- The ATOM rows: (name, the duel manifest's `decode` note — the
    value-level pin the Rust consumer parses, not a second encoding —
    the `encVal` bytes). The value literal is a deliberate COPY — if
    it drifts from the bytes, the differential's decode-then-compare
    FAILS loudly (that is the check). -/
def atomGoldens : List (String × String × List UInt8) :=
  [ ("bool_false", "atom bool false", encVal .bool (.bool false))
  , ("bool_true", "atom bool true", encVal .bool (.bool true))
  , ("u64_varint", "atom u64 300", encVal .u64 (.u64 300))
  , ("i64_negative", "atom i64 -1", encVal .i64 (.i64 (-1)))
  , ("i64_positive", "atom i64 1", encVal .i64 (.i64 1))
  , ("string_chars", "atom str hi", encVal .string (.string "hi")) ]

/-- The RECORD rows: the full Example value's bytes (the generated
    struct's codec is the consumer). -/
def rowGoldens : List (String × List UInt8) :=
  [("example_row", goldenExample)]

/-- THE NEGATIVE CONTROL's vectors, computed FROM the golden row
    (byte-level splices, each an out-of-policy shape): a truncation, a
    bad bool tag, a non-canonical varint spliced over the count. Each
    must REFUSE in Rust — typed error, no panic. -/
def tamperVectors : List (String × List UInt8) :=
  [ ("truncated", goldenExample.take (goldenExample.length - 1))
  , ("bad_bool_tag", 5 :: goldenExample.drop 1)
  , ("non_canonical_count",
      goldenExample.take 1 ++ [0x80, 0x00] ++ goldenExample.drop 3) ]

/-- The duel's directory: ONE directory per duel (Kit.Duel's
    committed convention — the manifest + the vectors live there). -/
def duelDir : String := "crates/schema-generated/tests/duel"

/-- The duel's vector path for one row name — Kit.Duel.vpath (the ONE
    path convention; the local restatement is deleted, the adoption
    delegate). -/
def duelPath (name : String) : String := Kit.Duel.vpath duelDir name

/-- THE DUEL VECTOR SET (Kit.Duel's convention): the differential's
    vectors as the binary lane's files + the manifest as the text
    lane's. The vectors' bytes are `encVal`'s (the ONE source — the
    same defs the SchemaTests pins ride); the atoms' value-level pins
    are the `decode` notes (parsed by the Rust consumer, never
    re-encoded Lean-side); the record row decodes to the pinned
    Example; the tamper vectors REFUSE. -/
def duelVectors : Kit.Duel.VectorSet where
  dir := duelDir
  name := "schema-codec"
  generator := "SchemaCore.Emit.Rust"
  -- The manifest sits next to the generated Rust surface; the
  -- artifact-headers gate's shape contract checks the `//` spelling
  -- (the DRY sweep: the style is the VectorSet's OWN field).
  style := .doubleSlash
  vectors :=
    (atomGoldens.map fun p =>
      { path := duelPath p.1, contents := p.2.2.toByteArray }) ++
    (rowGoldens.map fun p =>
      { path := duelPath p.1, contents := p.2.toByteArray }) ++
    (tamperVectors.map fun p =>
      { path := duelPath p.1, contents := p.2.toByteArray })
  expects :=
    (atomGoldens.map fun p =>
      (duelPath p.1, Kit.Duel.Expect.decode p.2.1)) ++
    (rowGoldens.map fun p =>
      (duelPath p.1, Kit.Duel.Expect.decode "example")) ++
    (tamperVectors.map fun p => (duelPath p.1, Kit.Duel.Expect.refuse))

/-- THE DUEL EMITTER: the manifest rides the TEXT lane, the vectors
    the BINARY lane — Kit.Duel's ONE emitter body (`emitterWith`) at
    this lane's parameters: the DataRegistry spec (the naming
    invariant rides the registry's own nodup-in-the-type — the audit's
    vacuous-certificate finding retired the law literal; the DRY
    sweep; the style is the VectorSet's own `.doubleSlash` field, the
    artifact-headers gate's shape contract reads it). -/
def duelEmitter : Emitter (DataRegistry Item) :=
  Kit.Duel.emitterWith duelVectors "SchemaCore.Slice"
    (law := none)

/-- The generated integration test's ROPE — the duel's Rust CONSUMER
    (Kit.Duel's contract: the manifest is read, never re-encoded; the
    vector bytes live in the duel directory's committed files). The
    pinned-value fixture (`pinned_example`) is the slice fixture's —
    see the module header's honest gap. The rope is EXPOSED for the
    golden module's chunk literals (libRope's note). -/
def differentialRope : Text :=
  Text.cat
    [ .str "//! GENERATED differential vectors + the Rust half of the Lean<->Rust
//! codec correspondence (notes/v3/03 section 3's differential level).
//! The vectors ride Kit.Duel's vector-set convention: the duel
//! directory tests/duel/ carries the vector files plus manifest.txt
//! (the generator row + one `<path>\t<expectation>` row per vector),
//! all emitted by SchemaCore.Emit.Rust's duel emitter and committed
//! through the byte-tie — never hand-written, never hand-edited.

use schema_generated::{dec_bool, dec_i64, dec_string, dec_u64, enc_str,
  enc_varint, zigzag_i64, Example};

/// The duel manifest, compile-time pinned to the committed artifact.
const MANIFEST: &str = include_str!(\"duel/manifest.txt\");

"
    , .str Kit.Duel.rustCratePrefix
    , .str "/// One parsed manifest row: the vector path + the decode note (None =
/// the row expects a typed refusal).
struct Row {
    path: String,
    note: Option<String>,
}

"
    , .str (Kit.Duel.rustManifestRows "Row"
        "Row { path, note: expect.strip_prefix(\"decode \").map(str::to_string) }")
    , .str Kit.Duel.rustCratePath
    , .str "/// The parsed atom pin (the manifest's `decode atom ...` note IS the
/// value-level pin — a drift from the bytes fails the test loudly).
#[derive(Debug, PartialEq, Eq)]
enum Atom {
    Bool(bool),
    U64(u64),
    I64(i64),
    Str(String),
}

fn parse_atom(note: &str) -> Option<Atom> {
    let rest = note.strip_prefix(\"atom \")?;
    let mut parts = rest.splitn(2, ' ');
    let kind = parts.next()?;
    let value = parts.next()?;
    match kind {
        \"bool\" => Some(Atom::Bool(value == \"true\")),
        \"u64\" => Some(Atom::U64(value.parse().ok()?)),
        \"i64\" => Some(Atom::I64(value.parse().ok()?)),
        \"str\" => Some(Atom::Str(value.to_string())),
        _ => None,
    }
}

/// The pinned Example row (the value the example_row bytes denote).
fn pinned_example() -> Example {
    Example {
        ready: true,
        count: 300,
        delta: -1,
        label: \"hi\".to_string(),
        note: Some(\"note\".to_string()),
        tags: vec![\"a\".to_string(), \"b\".to_string()],
    }
}

/// BOTH directions on every `decode atom ...` row: bytes -> value
/// (decode, against the manifest's parsed pin), value -> bytes
/// (re-encode, byte-identical).
#[test]
fn manifest_atoms_decode_and_reencode() {
    for row in manifest_rows() {
        let note = match &row.note { Some(n) => n, None => continue };
        let pin = match parse_atom(note) { Some(a) => a, None => continue };
        let bytes = std::fs::read(crate_path(&row.path))
            .expect(\"duel vector file present\");
        let mut rest: &[u8] = &bytes;
        let mut out = Vec::new();
        match pin {
            Atom::Bool(v) => {
                let got = dec_bool(&mut rest)
                    .unwrap_or_else(|e| panic!(\"atom {} refused: {e:?}\", row.path));
                assert_eq!(got, v, \"atom {} value drifted\", row.path);
                out.push(if got { 1u8 } else { 0u8 });
            }
            Atom::U64(v) => {
                let got = dec_u64(&mut rest)
                    .unwrap_or_else(|e| panic!(\"atom {} refused: {e:?}\", row.path));
                assert_eq!(got, v, \"atom {} value drifted\", row.path);
                enc_varint(got, &mut out);
            }
            Atom::I64(v) => {
                let got = dec_i64(&mut rest)
                    .unwrap_or_else(|e| panic!(\"atom {} refused: {e:?}\", row.path));
                assert_eq!(got, v, \"atom {} value drifted\", row.path);
                enc_varint(zigzag_i64(got), &mut out);
            }
            Atom::Str(v) => {
                let got = dec_string(&mut rest)
                    .unwrap_or_else(|e| panic!(\"atom {} refused: {e:?}\", row.path));
                assert_eq!(&got, &v, \"atom {} value drifted\", row.path);
                enc_str(got.as_str(), &mut out);
            }
        }
        assert!(rest.is_empty(), \"atom {} left {rest:?} unconsumed\", row.path);
        assert_eq!(out, bytes, \"re-encode drifted for {}\", row.path);
    }
}

/// BOTH directions on the `decode example` row: bytes -> Example
/// (decode), Example -> bytes (re-encode, byte-identical).
#[test]
fn manifest_rows_decode_and_reencode() {
    for row in manifest_rows() {
        if row.note.as_deref() != Some(\"example\") { continue; }
        let bytes = std::fs::read(crate_path(&row.path))
            .expect(\"duel vector file present\");
        let mut rest: &[u8] = &bytes;
        let value = Example::decode(&mut rest)
            .unwrap_or_else(|e| panic!(\"golden vector {} refused: {e:?}\", row.path));
        assert!(
            rest.is_empty(),
            \"golden vector {} left {rest:?} unconsumed\", row.path
        );
        let mut out = Vec::new();
        value.encode(&mut out);
        assert_eq!(out, bytes, \"re-encode drifted for {}\", row.path);
    }
}

/// The example_row's bytes denote the PINNED value (the decode
/// direction at the value level, not just shape).
#[test]
fn example_row_denotes_the_pinned_value() {
    let row = manifest_rows()
        .into_iter()
        .find(|r| r.note.as_deref() == Some(\"example\"))
        .expect(\"the manifest carries the example row\");
    let bytes = std::fs::read(crate_path(&row.path))
        .expect(\"duel vector file present\");
    let mut rest: &[u8] = &bytes;
    let value = Example::decode(&mut rest).expect(\"example_row decodes\");
    assert_eq!(value, pinned_example());
}

/// The append-form law's Rust mirror: the encoding plus ANY suffix
/// decodes to the value plus the suffix (Pattern #2's composition).
#[test]
fn decode_is_append_form() {
    let row = manifest_rows()
        .into_iter()
        .find(|r| r.note.as_deref() == Some(\"example\"))
        .expect(\"the manifest carries the example row\");
    let mut bytes = std::fs::read(crate_path(&row.path))
        .expect(\"duel vector file present\");
    bytes.push(0xFF);
    let mut rest: &[u8] = &bytes;
    let value = Example::decode(&mut rest)
        .unwrap_or_else(|e| panic!(\"append-form failed: {e:?}\"));
    assert_eq!(value, pinned_example());
    assert_eq!(rest, &[0xFFu8]);
}

/// THE NEGATIVE CONTROL: every `refuse` row REFUSES — a typed
/// CodecError, never a panic, never a silent misparse.
#[test]
fn manifest_refuse_rows_refuse() {
    for row in manifest_rows() {
        if row.note.is_some() { continue; }
        let bytes = std::fs::read(crate_path(&row.path))
            .expect(\"duel vector file present\");
        match Example::decode_full(&bytes) {
            Ok(_) => panic!(\"tampered vector {} decoded — the wire gate has a hole\", row.path),
            Err(_) => {} // the typed refusal is the pass
        }
    }
}
"]

/-- The differential's body: ONE render at the file boundary. -/
def renderDifferential : String :=
  Text.render differentialRope

/-! ## The emitter -/

/-! ## THE CODETARGET ROW — the Rust target -/

/-- THE RUST TARGET as a `Spine.CodeTarget` row (the design note §1's
    factoring, landed): the section order, the record-block join, the
    face placement and the emitter row are the SPINE's; the type map,
    the two codec-template algs, the prelude, the universe faces, the
    face rows and the migration lane are this row's. The migration's
    proof is the byte-tie: `gates gen-check` holds the generated crate
    BYTE-IDENTICAL to the pre-spine emitter's. -/
def rustTarget : Spine.CodeTarget where
  name := "rust"
  style := .doubleSlash
  outputPath := "crates/schema-generated/src/lib.rs"
  extraOutputs :=
    [ { path := "crates/schema-generated/tests/differential.rs"
        contents := renderDifferential } ]
  tyText := tyRust
  identTy := pascalName
  encRef := fun f => "&self." ++ f
  decExpr := id
  encAlg := encAlg
  decAlg := decAlg
  prelude := .str libPrelude
  universeTypes := .str universeTypesRust
  faces := rustFaces
  faceNames := ["keyLookup", "finders", "observability", "builder", "serde"]
  lanes := [.str renderMigrate]
  renderRecord := rustRenderRecord

/-- The registry → the lib.rs body's ROPE (pure, total; the fold over
    the universe) — the SPINE's section assembly at this target's row
    (the seam's migration: the hardcoded walk is `spineLibRope` now;
    the sections and their separator are unchanged, and gen-check
    holds the rendered bytes). The record blocks are ONE `sepBy` join —
    O(1) per block. The rope is EXPOSED (not folded into a String):
    the golden module's chunk literals ride `Text.chunks` of THIS —
    the goldens theorems compare chunk-wise (the kernel never executes
    the join; the monolithic-string whnf is quadratic in the body and
    blows the elaboration budget — measured 5min for the differential
    alone). -/
def libRope (reg : DataRegistry Item) : Text :=
  Spine.spineLibRope rustTarget reg

/-- The Rust lane's emitter: the SECOND emitter over the ONE regen
    core — the SPINE's emitter row at this target's `CodeTarget`
    (the name, the style, the outputs and the run are the spine's
    assembly; the differential rides the target's `extraOutputs`).
    `outputs_nodup` is in the type; the naming invariant is the
    registry's own nodup-in-the-type (one naming world, two renderings;
    the old law literal was the proof field restated — the audit's
    vacuous-certificate finding). -/
def rustEmitter : Emitter (DataRegistry Item) :=
  Spine.spineEmitter rustTarget

/-! ## The generated Rust consumers' suite (the commit-slice emitter's
     extension — the ONE emitter for the generated `.rs` consumers: the
     byte-tie's channel is `gates gen-check` per artifact, never a
     golden rope crack; the files are hand-AUTHORED pins rendered
     verbatim — the emitter is the ONE writer, the ownership gate's
     declared set covers them, drift is `just gen`'s). -/

/-- The API surface's behavior pins (the builder + the 02 §3
    lookups + the mandatory negative controls). -/
def apiTestsRust : String :=
"//! The generated API surface's behavior pins (HAND-AUTHORED pin text,\n//! rendered by the emitter — the ONE writer; never hand-edit this\n//! file, `just gen` restores).\n//!\n//! The pins ride the emitter's disciplines:\n//! - the TYPESTATE builder (the bon discipline, manual): the set-ness\n//!   of each field is a type parameter; `build` exists ONLY in the\n//!   all-set state — a wrong construction does not COMPILE;\n//! - the key-indexed lookup (02 §3's Option shape: the declared\n//!   primary key `label`'s determinacy — at most one row);\n//! - the conservative field queries (02 §3's collection shape: NO\n//!   uniqueness claim, every match returns).\n\nuse schema_generated::{Example, ExampleEx};\n\n#[test]\nfn builder_full_chain_builds_the_value() {\n    // `build` is INFALLIBLE (a fn, not a Result): the type index\n    // guarantees every field was set — no default is ever smuggled.\n    let v: Example = Example::builder()\n        .ready(true)\n        .count(300)\n        .delta(-1)\n        .label(\"hi\".to_string())\n        .note(Some(\"note\".to_string()))\n        .tags(vec![\"a\".to_string(), \"b\".to_string()])\n        .build();\n    assert_eq!(v, Example {\n        ready: true,\n        count: 300,\n        delta: -1,\n        label: \"hi\".to_string(),\n        note: Some(\"note\".to_string()),\n        tags: vec![\"a\".to_string(), \"b\".to_string()],\n    });\n}\n\n#[test]\nfn builder_type_state_is_the_guarantee() {\n    // THE NEGATIVE CONTROL (the type level — MANDATORY): a builder\n    // missing a field has NO `build` method; the wrong construction\n    // does not compile:\n    //\n    //     let _ = Example::builder().count(1).build();\n    //     // error[E0599]: `build` is not implemented for\n    //     //               `ExampleBuilder<Unset, Set, Unset, ...>`\n    //\n    // The pin: the all-set state's build IS callable and infallible\n    // (the signature IS the guarantee — a compile-fail harness would\n    // buy the same pin at a dev-dep cost; the dep judgment: none).\n    fn pin(b: schema_generated::ExampleBuilder<\n        schema_generated::Set, schema_generated::Set,\n        schema_generated::Set, schema_generated::Set,\n        schema_generated::Set, schema_generated::Set,\n    >) -> Example {\n        b.build()\n    }\n    let v = pin(Example::builder()\n        .ready(true).count(1).delta(0)\n        .label(\"k\".to_string()).note(None).tags(Vec::new()));\n    assert_eq!(v.count, 1);\n}\n\n#[test]\nfn builder_setters_move_the_state_index_any_order() {\n    // the setters chain in ANY order — each moves its own index from\n    // Unset to Set; the final build fires only at all-Set.\n    let a: Example = Example::builder()\n        .tags(Vec::new())\n        .note(None)\n        .label(String::new())\n        .delta(0)\n        .count(2)\n        .ready(false)\n        .build();\n    let b: Example = Example::builder()\n        .ready(false)\n        .count(2)\n        .delta(0)\n        .label(String::new())\n        .note(None)\n        .tags(Vec::new())\n        .build();\n    assert_eq!(a, b);\n}\n\n#[test]\nfn ex_builder_is_typestate_too() {\n    let v: ExampleEx = ExampleEx::builder()\n        .status(Ok(5))\n        .counts(vec![(\"k\".to_string(), 1)])\n        .small(7)\n        .build();\n    assert_eq!(v.small, 7);\n}\n\n#[test]\nfn key_indexed_lookup_is_option_shaped() {\n    // 02 §3: the declared primary key `label`'s determinacy — the\n    // query returns AT MOST one row, Option-shaped.\n    let mk = |n: u64, label: &str| Example::builder()\n        .ready(true).count(n).delta(0)\n        .label(label.to_string()).note(None).tags(Vec::new())\n        .build();\n    let rows = vec![mk(1, \"a\"), mk(2, \"b\")];\n    assert!(Example::get_by_label(&rows, \"a\").is_some());\n    assert_eq!(Example::get_by_label(&rows, \"a\").expect(\"the pin\\x27s known answer\").count, 1);\n    assert_eq!(Example::get_by_label(&rows, \"b\").expect(\"the pin\\x27s known answer\").count, 2);\n}\n\n#[test]\nfn key_indexed_lookup_absent_key_is_none() {\n    // THE NEGATIVE CONTROL: an absent key is `None` — never a\n    // fabricated row.\n    let rows: Vec<Example> = Vec::new();\n    assert!(Example::get_by_label(&rows, \"a\").is_none());\n}\n\n#[test]\nfn conservative_query_is_collection_shaped() {\n    // 02 §3: NO uniqueness claim on an ordinary field — every match\n    // returns, Vec-shaped (the conservative surface).\n    let mk = |n: u64, label: &str| Example::builder()\n        .ready(true).count(n).delta(0)\n        .label(label.to_string()).note(None).tags(Vec::new())\n        .build();\n    let rows = vec![mk(1, \"dup\"), mk(2, \"dup\"), mk(3, \"one\")];\n    let dups = Example::find_by_label(&rows, &\"dup\".to_string());\n    assert_eq!(dups.len(), 2); // the Option shape is NOT invented here\n    assert_eq!(Example::find_by_label(&rows, &\"one\".to_string()).len(), 1);\n    assert!(Example::find_by_label(&rows, &\"gone\".to_string()).is_empty());\n}\n\n#[test]\nfn conservative_query_option_field_and_ex_fields() {\n    let ex = ExampleEx::builder()\n        .status(Ok(5))\n        .counts(vec![(\"k\".to_string(), 1)])\n        .small(7)\n        .build();\n    let rows = vec![ex];\n    assert_eq!(\n        ExampleEx::find_by_counts(&rows, &vec![(\"k\".to_string(), 1)]).len(),\n        1\n    );\n    assert!(ExampleEx::find_by_small(&rows, &7).len() == 1);\n    // the sum-shaped field queries by its Rust type (the serde face's\n    // Result spelling — the interop convention, not the wire's tag)\n    assert_eq!(rows[0].status, Ok(5));\n}\n"

/-- The serde face's round trips + the two-faces honesty pin. -/
def serdeTestsRust : String :=
"//! The serde face's round trips + the TWO-FACES honesty pin\n//! (HAND-AUTHORED pin text, rendered by the emitter — the ONE writer;\n//! never hand-edit the generated file, `just gen` restores).\n//!\n//! THE DISCIPLINE (the emitter's serde note, cited): the schema's\n//! CANONICAL codec is SchemaCore.Codec's wire (the duel vectors in\n//! tests/duel/ are its differential; the wire of record); the serde\n//! impls are the ECOSYSTEM INTEROP face — a different byte encoding\n//! with its own conventions. These pins hold the two faces APART\n//! (never byte-equal — the honesty row) while each round trips on its\n//! own (the interop face's behavior pin).\n//!\n//! Negative controls are MANDATORY: a missing field refuses, a\n//! duplicate field refuses, an unknown field is ignored\n//! (forward-compat), a wrong-typed value refuses.\n\nuse schema_generated::{Example, ExampleEx};\n\nfn sample() -> Example {\n    Example::builder()\n        .ready(true)\n        .count(300)\n        .delta(-1)\n        .label(\"hi\".to_string())\n        .note(Some(\"note\".to_string()))\n        .tags(vec![\"a\".to_string(), \"b\".to_string()])\n        .build()\n}\n\n#[test]\nfn serde_round_trip_example() {\n    let v = sample();\n    let text = serde_json::to_string(&v).expect(\"serialize\");\n    let back: Example = serde_json::from_str(&text).expect(\"deserialize\");\n    assert_eq!(back, v);\n}\n\n#[test]\nfn serde_round_trip_example_ex_both_sum_faces() {\n    let mk = |status| ExampleEx::builder()\n        .status(status)\n        .counts(vec![(\"k\".to_string(), 1), (\"j\".to_string(), 2)])\n        .small(7)\n        .build();\n    for v in [mk(Ok(5)), mk(Err(\"bad\".to_string()))] {\n        let text = serde_json::to_string(&v).expect(\"serialize\");\n        let back: ExampleEx = serde_json::from_str(&text).expect(\"deserialize\");\n        assert_eq!(back, v);\n    }\n}\n\n#[test]\nfn the_two_faces_are_honest_about_their_bytes() {\n    // THE HONESTY ROW: the canonical wire (SchemaCore.Codec's — the\n    // generated `encode`) and the serde JSON face are DIFFERENT byte\n    // encodings of the same value. The wire of record stays the\n    // codec's; serde is interop. A face that silently became the\n    // other would fail this pin.\n    let v = sample();\n    let mut wire = Vec::new();\n    v.encode(&mut wire);\n    let json = serde_json::to_vec(&v).expect(\"serialize\");\n    assert_ne!(wire, json, \"the wire and the interop face must differ\");\n    // and each decodes on ITS OWN face only\n    assert!(Example::decode_full(&wire).is_ok());\n    assert!(Example::decode_full(&json).is_err()); // the wire refuses JSON\n    let back: Example = serde_json::from_slice(&json).expect(\"json face\");\n    assert_eq!(back, v);\n}\n\n#[test]\nfn serde_missing_field_refuses() {\n    // THE NEGATIVE CONTROL: a missing field is a typed serde refusal\n    // (the same field the JSON carries — dropped here).\n    let missing = r#\"{\"ready\":true,\"count\":1,\"delta\":0,\"label\":\"x\",\"note\":null}\"#;\n    let got: Result<Example, _> = serde_json::from_str(missing);\n    assert!(got.is_err(), \"a missing field must refuse\");\n}\n\n#[test]\nfn serde_duplicate_field_refuses() {\n    // THE NEGATIVE CONTROL: a duplicate field is a typed refusal —\n    // never a silent last-wins.\n    let dup = r#\"{\"ready\":true,\"ready\":false,\"count\":1,\"delta\":0,\"label\":\"x\",\"note\":null,\"tags\":[]}\"#;\n    let got: Result<Example, _> = serde_json::from_str(dup);\n    assert!(got.is_err(), \"a duplicate field must refuse\");\n}\n\n#[test]\nfn serde_wrong_typed_value_refuses() {\n    // THE NEGATIVE CONTROL: a wrong-typed value refuses (never a\n    // silent reinterpretation).\n    let wrong = r#\"{\"ready\":true,\"count\":\"300\",\"delta\":0,\"label\":\"x\",\"note\":null,\"tags\":[]}\"#;\n    let got: Result<Example, _> = serde_json::from_str(wrong);\n    assert!(got.is_err(), \"a wrong-typed value must refuse\");\n}\n\n#[test]\nfn serde_unknown_field_ignored_forward_compat() {\n    // The interop convention: an unknown field is interop, not drift —\n    // ignored (the emitter's serde note).\n    let ext = r#\"{\"ready\":true,\"count\":300,\"delta\":-1,\"label\":\"hi\",\"note\":\"note\",\"tags\":[\"a\",\"b\"],\"future\":{\"x\":1}}\"#;\n    let got: Example = serde_json::from_str(ext).expect(\"unknown fields are ignored\");\n    assert_eq!(got, sample());\n}\n"

/-- The migration face's behavior pins. -/
def migrateTestsRust : String :=
"//! The migration lane's Rust face — the versioned types + the derived\n//! upcaster's behavior pins (HAND-WRITTEN consumer — never a generated\n//! file).\n//!\n//! The emitter renders the PINNED Lean plan (`SchemaCore.Emit.Rust`'s\n//! `examplePlan12` — the DERIVATION's agreement is pinned Lean-side in\n//! SchemaTests; the wf-recursive derivation is kernel-opaque there).\n//! These pins hold the Rust face to the plan's steps: the carry rows\n//! ride verbatim, the fill row gets the type's default, and the key\n//! `label` is carried UNCHANGED (stable identities, 08 §19).\n\nuse schema_generated::{ExampleV1, ExampleV2};\n\nfn v1(ready: bool, count: u64, label: &str) -> ExampleV1 {\n    ExampleV1 { ready, count, label: label.to_string() }\n}\n\n#[test]\nfn upcast_carries_fields_verbatim() {\n    let v = crate_upcast(v1(true, 300, \"hi\"));\n    assert_eq!(v.ready, true);\n    assert_eq!(v.count, 300);\n    assert_eq!(v.label, \"hi\");\n}\n\n#[test]\nfn upcast_fills_the_added_field_with_its_default() {\n    // the plan's fill step: delta (i64) gets the type's default —\n    // exactly 0, never garbage (the negative control: the fill is\n    // PINNED, not incidental).\n    let v = crate_upcast(v1(false, 0, \"\"));\n    assert_eq!(v.delta, 0i64);\n}\n\n#[test]\nfn upcast_carries_the_key_unchanged() {\n    // stable identities (08 §19): the key column's image is identical\n    // before and after — the keyed table's identity survives.\n    let before = v1(true, 7, \"the-key\");\n    let after = crate_upcast(before);\n    assert_eq!(after.label, \"the-key\");\n}\n\n#[test]\nfn upcast_round_trips_through_serde() {\n    // the versioned types ride the interop face too: serde round trip\n    // on BOTH sides of the upcaster.\n    let a = v1(true, 5, \"k\");\n    let text = serde_json::to_string(&a).expect(\"serialize v1\");\n    let b: ExampleV1 = serde_json::from_str(&text).expect(\"deserialize v1\");\n    let c = crate_upcast(b);\n    let text2 = serde_json::to_string(&c).expect(\"serialize v2\");\n    let d: ExampleV2 = serde_json::from_str(&text2).expect(\"deserialize v2\");\n    assert_eq!(d, crate_upcast(a));\n}\n\n#[test]\nfn the_upcaster_is_total() {\n    // the migration face has NO refusal type: the derivation's\n    // refusals (removals, renames, reorders, unstable keys) refuse\n    // LEAN-side, BEFORE the face renders — a plan that reached Rust is\n    // total by construction. Pin the totality shape: a fn, not a\n    // Result.\n    let f = crate_upcast(v1(false, 1, \"x\"));\n    assert_eq!(f.delta, 0i64);\n}\n\n// The emitted upcaster (the generated fn — called through a local alias\n// so the pin reads as the plan's face, not a re-implementation).\nuse schema_generated::upcast_example_v1_to_example_v2 as crate_upcast;\n"

/-- The closed universe's Rust faces' pins (the strum faces + the
    construction discipline + the promises). -/
def universeTestsRust : String :=
"//! The closed universe's Rust faces — the closed enums (strum), the\n//! newtype construction discipline, the deterministic carrier\n//! (HAND-AUTHORED pin text, rendered by the emitter — the ONE writer;\n//! never hand-edit the generated file, `just gen` restores).\n//!\n//! The pins ride the emitter's universe-types notes:\n//! - the closed enums' strum faces (the iteration + the string\n//!   discipline — the tags are the LEAN ctor names, snake_case);\n//! - the key materials' try_new (validation at construction, ONE\n//!   point);\n//! - the deterministic carrier's PROMISES (exact checked addition,\n//!   named floor rounding, total order, codec legality) — each a\n//!   known answer, never a hope.\n//!\n//! Negative controls are MANDATORY: the zero-scale carrier is\n//! UNCONSTRUCTIBLE, the arithmetic overflow refuses, the zero-scale\n//! tag never parses back as a carrier's scale.\n\nuse schema_generated::{Fixed, KeyI64, KeyString, KeyTy, KeyU64, Profile};\nuse strum::EnumCount;\nuse strum::IntoEnumIterator;\n\n// ---- the closed enums: the strum faces ----\n\n#[test]\nfn profile_enum_iterates_and_counts() {\n    // EnumIter + EnumCount: the closed enum's fold surface — the\n    // compiler drives the extension when the `fast` slot lands.\n    assert_eq!(Profile::COUNT, 2);\n    let names: Vec<String> = Profile::iter()\n        .map(|p| p.to_string())\n        .collect();\n    assert_eq!(names, vec![\"plain\".to_string(), \"deterministic\".to_string()]);\n}\n\n#[test]\nfn profile_enum_string_round_trips() {\n    // the string discipline: the tags are the LEAN ctor names —\n    // Display and EnumString agree both directions.\n    for p in Profile::iter() {\n        let s = p.to_string();\n        assert_eq!(s.parse::<Profile>().expect(\"the known answer\"), p);\n    }\n    assert_eq!(\"deterministic\".parse::<Profile>().expect(\"the known answer\"), Profile::Deterministic);\n}\n\n#[test]\nfn keyty_enum_iterates_and_counts() {\n    assert_eq!(KeyTy::COUNT, 4);\n    let names: Vec<String> = KeyTy::iter()\n        .map(|k| k.to_string())\n        .collect();\n    assert_eq!(\n        names,\n        vec![\"bool\".to_string(), \"u64\".to_string(), \"i64\".to_string(), \"string\".to_string()]\n    );\n    // THE NEGATIVE CONTROL: an unknown tag refuses (never a silent\n    // misparse).\n    assert!(\"float\".parse::<KeyTy>().is_err());\n}\n\n// ---- the key materials: try_new (validation at construction) ----\n\n#[test]\nfn key_materials_construct_through_try_new() {\n    let k = KeyString::try_new(\"the-key\".to_string()).expect(\"scalar is key material\");\n    assert_eq!(k.get(), \"the-key\");\n    assert_eq!(KeyU64::try_new(300).expect(\"scalar\").get(), 300);\n    assert_eq!(KeyI64::try_new(-1).expect(\"scalar\").get(), -1);\n}\n\n// ---- the deterministic carrier: the PROMISES ----\n\n/// The Money Cents shape (the model's own example): scale 100.\ntype Cents = Fixed<100>;\ntype Ones = Fixed<1>;\n\n#[test]\nfn fixed_try_new_validates_at_construction() {\n    let c = Cents::try_new(150).expect(\"a positive scale constructs\");\n    assert_eq!(c.units(), 150);\n    // the rational reading: 150 units / 100 = $1.50\n}\n\n#[test]\nfn fixed_zero_scale_is_unconstructible() {\n    // THE NEGATIVE CONTROL (the scale-positivity gate): a zero scale\n    // divides by zero — the model refuses at the ONE construction\n    // point; a `Fixed<0>` value can never exist.\n    assert!(Fixed::<0>::try_new(1).is_none());\n}\n\n#[test]\nfn fixed_add_is_exact_and_overflow_refuses() {\n    let a = Cents::try_new(150).expect(\"the known answer\"); // $1.50\n    let b = Cents::try_new(275).expect(\"the known answer\"); // $2.75\n    let s = a.add_checked(&b).expect(\"in capacity\"); // $4.25 — EXACT\n    assert_eq!(s.units(), 425);\n    // THE NEGATIVE CONTROL: the wire capacity's overflow REFUSES —\n    // never a silent wrap (the hardware +'s forfeited lie).\n    let big = Cents::try_new(u64::MAX).expect(\"the known answer\");\n    assert!(big.add_checked(&Cents::try_new(1).expect(\"the known answer\")).is_none());\n}\n\n#[test]\nfn fixed_mul_floors_the_exact_rational_product() {\n    // $1.50 * $2.00 = $3.00 EXACTLY (150 * 275... the units' product\n    // over the squared scale, floored): 150/100 * 275/100 = 4.125 →\n    // the floor is 412 units ($4.12) — the error is strictly under\n    // one unit.\n    let a = Cents::try_new(150).expect(\"the known answer\");\n    let b = Cents::try_new(275).expect(\"the known answer\");\n    let p = a.mul_floor(&b).expect(\"in capacity\");\n    assert_eq!(p.units(), 412);\n    // THE NEGATIVE CONTROL: a capacity-exceeding product REFUSES\n    // (scale 1: the floored product itself passes 2^64).\n    let big = Ones::try_new(u64::MAX).expect(\"the known answer\");\n    assert!(big.mul_floor(&Ones::try_new(2).expect(\"the known answer\")).is_none());\n}\n\n#[test]\nfn fixed_order_is_total_no_nan_hole() {\n    // TOTAL ordering (the legacy no-floats exclusion's resolution —\n    // no NaN hole; Ord, not a partial guess).\n    let a = Cents::try_new(100).expect(\"the known answer\");\n    let b = Cents::try_new(200).expect(\"the known answer\");\n    assert!(a < b);\n    assert_eq!(a.cmp(&b), std::cmp::Ordering::Less);\n    // every pair compares — totality over the carrier\n    assert_eq!(a.cmp(&a), std::cmp::Ordering::Equal);\n}\n\n#[test]\nfn fixed_is_codec_legal_on_the_u64_wire_row() {\n    // CODEC LEGALITY (the model's promise): the carrier's bytes are\n    // the bare u64 varint's, byte-for-byte, both directions.\n    let c = Cents::try_new(425).expect(\"the known answer\");\n    let mut wire = Vec::new();\n    c.encode(&mut wire);\n    let mut u64wire = Vec::new();\n    schema_generated::enc_varint(425, &mut u64wire);\n    assert_eq!(wire, u64wire);\n    let mut rest: &[u8] = &wire;\n    assert_eq!(Cents::decode(&mut rest).expect(\"the known answer\"), c);\n    assert!(rest.is_empty());\n}\n"
/-- The COMMIT-SLICE consumer's emitter (the bidirectional slice's
    differential — SchemaCore.Commit's duel's Rust side) + the
    generated Rust CONSUMERS' suite (the API pins, the serde round
    trips, the migration face's evidence — hand-AUTHORED pin text the
    emitter renders verbatim: the ONE writer per path, the ownership
    gate's declared set covers them, drift is `just gen`'s). Its OWN
    emitter: the golden-theorem channel stays at the two codec
    artifacts (the three-rope kernel crack exceeded the
    kernel-check's budget — the monolithic-literal whnf's quadratic
    shape; and the API-surface growth made the lib crack worse — the
    runtime-pin note in Emit.lean's goldens channel); this lane's ONE
    tie per artifact is `gates gen-check` (the duel manifest's
    channel — one tie per artifact, 09's rule). -/
def commitSliceEmitter : Emitter (DataRegistry Item) where
  name := "schema-commit-slice"
  style := .doubleSlash
  specSource := "SchemaCore.Commit"
  outputs :=
    [ "crates/schema-generated/tests/commit_slice.rs"
    , "crates/schema-generated/tests/api.rs"
    , "crates/schema-generated/tests/serde_rt.rs"
    , "crates/schema-generated/tests/migrate.rs"
    , "crates/schema-generated/tests/universe.rs" ]
  run _ :=
    [ { path := "crates/schema-generated/tests/commit_slice.rs"
        contents := commitSliceRust }
    , { path := "crates/schema-generated/tests/api.rs"
        contents := apiTestsRust }
    , { path := "crates/schema-generated/tests/serde_rt.rs"
        contents := serdeTestsRust }
    , { path := "crates/schema-generated/tests/migrate.rs"
        contents := migrateTestsRust }
    , { path := "crates/schema-generated/tests/universe.rs"
        contents := universeTestsRust } ]
  law := none

end SchemaCore.Emit.Rust
