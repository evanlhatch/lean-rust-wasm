/-
# SchemaCore.Emit.Rust — the Rust target (the codec's consumer lane)

Owner: the Rust-consumer lane (the macht tree, `schemacore/`).
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

THE HONEST GAPS (each named, none silent):
- The emitter's LAW is the same closed-world naming precondition as the
  WIT lane (`reg.nodup`) — the certified lane's certificate. Identifier
  CLEANLINESS is NOT in the law (it is decidable but not a registry
  invariant; the fixture carries it) — a non-Rust-clean name lands as
  uncompilable generated code, caught by `cargo build`, not silently.
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
- carrier grade: the law is the closed-world naming precondition
  (`reg.nodup`) — a discharged certificate through `runCertified`, the
  same slot the WIT emitter occupies; the Rust-side agreement is the
  correspondence's differential row (03 §3's evidence table).
- spine reading: the Interpretation stage (01 §5) — the SECOND emitter
  over the ONE regen core.
- ladder rung: total structural folds; the goldens are kernel-checked
  (the SchemaTests pins over `goldens`/`goldenExample` are `rfl`).
- gate row: gen-check byte-ties BOTH artifacts; `cargo test` is the
  differential's runner.

Core-only (imports SchemaCore.Describe, SchemaCore.Codec,
SchemaCore.Item — the cone rule).
-/

import SchemaCore.Describe
import SchemaCore.Codec
import SchemaCore.Item

open Kit
open Kit.Emit

namespace SchemaCore.Emit.Rust

/-! ## The description lift — the items ride the Describe layer in -/

/-- The field-type lift INTO the description universe: the wrapper
    shapes (option/list) become the `Descr` wrappers; the closed
    universe's other ctors stay `.prim` leaves (ONE leaf universe —
    the description layer adds the record dimension, it does not
    re-interpret the leaves). -/
def descrOfTy (t : Ty) : Descr :=
  match t with
  | .option t' => .option (descrOfTy t')
  | .list t' => .list (descrOfTy t')
  | _ => .prim t

/-- The item's description (provenance-faithful name, registration
    field order — the same rows `itemOfDescr` flattens back). -/
def itemDescr (item : Item) : Descr :=
  .product item.name (item.fields.map fun f => (f.name, descrOfTy f.ty))

/-! ## The Rust rendering — types through the description, codecs
     through the boundary's wire folds -/

/-- The recursion measure for the text templates: the type's NODE COUNT.
    Every recursive call lands on a smaller count — in particular a
    key's `toTy` injection lands BELOW the map/set node that carried it
    (a key reifies to one of the four scalar nodes). -/
def tyNodeCount : Ty → Nat
  | .bool => 1
  | .u64 => 1
  | .i64 => 1
  | .string => 1
  | .option t => tyNodeCount t + 1
  | .list t => tyNodeCount t + 1
  | .result ok err => tyNodeCount ok + tyNodeCount err + 1
  | .map _ v => tyNodeCount v + 2
  | .set _ => 2
  | .bounded _ => 1

/-- The key injection is a scalar node (the measure's key-slot leg). -/
theorem keyTy_toTy_nodeCount (k : KeyTy) : tyNodeCount k.toTy = 1 := by
  cases k <;> rfl

/-- The closed universe's Rust text (total over `Ty` — the compiler
    drives a new ctor here). The option/list arms are unreachable
    through `descrOfTy` (the lift takes them as wrappers) but kept
    correct for totality. The map/set KEY positions ride the scalar
    sub-universe through the `KeyTy.toTy` injection (Ty.lean's route —
    the same one `renderTy` takes; unlike the codec lane there is no
    structural-recursion break to dodge, so ONE scalar table serves
    both — no parallel key rows). -/
def tyRustPrim : Ty → String
  | .bool => "bool"
  | .u64 => "u64"
  | .i64 => "i64"
  | .string => "String"
  | .option t => "Option<" ++ tyRustPrim t ++ ">"
  | .list t => "Vec<" ++ tyRustPrim t ++ ">"
  | .result ok err =>
      "Result<" ++ tyRustPrim ok ++ ", " ++ tyRustPrim err ++ ">"
  -- order-preserving payload containers (see the module header)
  | .map k v => "Vec<(" ++ tyRustPrim k.toTy ++ ", " ++ tyRustPrim v ++ ")>"
  | .set k => "Vec<" ++ tyRustPrim k.toTy ++ ">"
  | .bounded _ => "u64"
termination_by t => tyNodeCount t
decreasing_by all_goals (simp [tyNodeCount, keyTy_toTy_nodeCount] <;> try omega)

/-- The map/set KEY rendering: the key sub-universe's slice of
    `tyRustPrim` through the `KeyTy.toTy` injection (the coherence
    pattern `renderKeyTy_toTy` proves for the WIT lane — here the
    delegation IS the definition). -/
def keyRust (k : KeyTy) : String := tyRustPrim k.toTy

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
    Pascal-cased (separators `-`/`_` dropped, the following letter
    uppercased, the rest as-is). -/
def pascalName (s : String) : String :=
  let rec go : List Char → Bool → List Char
    | [], _ => []
    | c :: cs, up =>
        if c == '-' || c == '_' then go cs true
        else
          let c' := if up then Char.toUpper c else c
          c' :: go cs false
  String.ofList (go ((s.splitOn ".").getLast!).toList true)

/-! ## The codec generation — the wire's Rust face

The templates are `++` concatenations (the interpolation braces do not
survive this Lean's format strings; the plain-concat form is also the
mechanically safer one — every Rust brace is literal). -/

/-- The ENCODE statements for a value of schema type `t`, where `e` is
    the Rust expression HOLDING A REFERENCE to it (`e : &T` throughout
    — the uniform convention lets the recursion compose). The bytes are
    `SchemaCore.Codec`'s wire, arm by arm. -/
def encStmts : Ty → String → String
  | .bool, e => "out.push(if *" ++ e ++ " { 1u8 } else { 0u8 });"
  | .u64, e => "enc_varint(*" ++ e ++ ", out);"
  | .i64, e => "enc_varint(zigzag_i64(*" ++ e ++ "), out);"
  | .string, e => "enc_str(" ++ e ++ ".as_str(), out);"
  | .option t', e =>
      "match " ++ e ++ " { None => out.push(0u8), Some(inner) => " ++
      "{ out.push(1u8); " ++ encStmts t' "inner" ++ " } };"
  | .list t', e =>
      "enc_varint((" ++ e ++ ").len() as u64, out); " ++
      "for inner in (" ++ e ++ ").iter() { " ++ encStmts t' "inner" ++ " }"
  | .result ok err, e =>
      "match " ++ e ++ " { Ok(inner) => { out.push(0u8); " ++
      encStmts ok "inner" ++ " }, Err(inner) => { out.push(1u8); " ++
      encStmts err "inner" ++ " } };"
  | .map k v, e =>
      "enc_varint((" ++ e ++ ").len() as u64, out); " ++
      "for (innerk, innerv) in (" ++ e ++ ").iter() { " ++
      encStmts k.toTy "innerk" ++ " " ++ encStmts v "innerv" ++ " }"
  | .set k, e =>
      "enc_varint((" ++ e ++ ").len() as u64, out); " ++
      "for innerk in (" ++ e ++ ").iter() { " ++
      encStmts k.toTy "innerk" ++ " }"
  | .bounded _, e => "enc_varint(*" ++ e ++ ", out);"
termination_by t _ => tyNodeCount t
decreasing_by all_goals (simp [tyNodeCount, keyTy_toTy_nodeCount] <;> try omega)

/-- The KEY position's encode statements: the scalar templates through
    the `KeyTy.toTy` injection (one template table — the key rows were
    verbatim copies of `encStmts`' scalars). -/
def keyEncStmts (k : KeyTy) (e : String) : String := encStmts k.toTy e

/-- The DECODE statements for a schema type `t` binding the Rust
    identifier `n`: after them, `n : T` is in scope and the cursor `bs`
    (a `&mut &[u8]`) has consumed exactly the value's bytes. Every
    out-of-policy shape refuses through the helpers' typed errors —
    never a silent misparse, never a panic. -/
def decStmts : Ty → String → String
  | .bool, n => "let " ++ n ++ " = dec_bool(bs)?;"
  | .u64, n => "let " ++ n ++ " = dec_u64(bs)?;"
  | .i64, n => "let " ++ n ++ " = dec_i64(bs)?;"
  | .string, n => "let " ++ n ++ " = dec_string(bs)?;"
  | .option t', n =>
      "let " ++ n ++ " = { let tag = dec_byte(bs)?; match tag " ++
      "{ 0u8 => None, 1u8 => { " ++ decStmts t' "inner" ++
      " Some(inner) }, _ => return Err(CodecError::InvalidTag(tag)) } };"
  | .list t', n =>
      "let " ++ n ++ " = { let count = dec_varint(bs)?; " ++
      "let mut acc = Vec::new(); for _ in 0..count { " ++
      decStmts t' "inner" ++ " acc.push(inner); } acc };"
  | .result ok err, n =>
      "let " ++ n ++ " = { let tag = dec_byte(bs)?; match tag " ++
      "{ 0u8 => { " ++ decStmts ok "inner" ++ " Ok(inner) }, " ++
      "1u8 => { " ++ decStmts err "inner" ++
      " Err(inner) }, _ => return Err(CodecError::InvalidTag(tag)) } };"
  | .map k v, n =>
      "let " ++ n ++ " = { let count = dec_varint(bs)?; " ++
      "let mut acc = Vec::new(); for _ in 0..count { " ++
      decStmts k.toTy "innerk" ++ " " ++ decStmts v "innerv" ++
      " acc.push((innerk, innerv)); } acc };"
  | .set k, n =>
      "let " ++ n ++ " = { let count = dec_varint(bs)?; " ++
      "let mut acc = Vec::new(); for _ in 0..count { " ++
      decStmts k.toTy "innerk" ++ " acc.push(innerk); } acc };"
  | .bounded cap, n =>
      "let " ++ n ++ " = dec_bounded(" ++ toString cap ++ "u64, bs)?;"
termination_by t _ => tyNodeCount t
decreasing_by all_goals (simp [tyNodeCount, keyTy_toTy_nodeCount] <;> try omega)

/-- The KEY position's decode statements: the scalar templates through
    the `KeyTy.toTy` injection (one template table, mirroring
    `keyEncStmts`). -/
def keyDecStmts (k : KeyTy) (n : String) : String := decStmts k.toTy n

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
}"

/-! ## The record rendering -/

/-- One item → one Rust struct + its codec impl (pure, total). The
    item-level `#[rustfmt::skip]` covers struct + impl; the codecs are
    generated code, never hand-formatted. -/
def renderRecord (item : Item) : String :=
  let name := pascalName item.name
  let fieldDecls := item.fields.map fun f =>
    "    pub " ++ f.name ++ ": " ++ tyRust (descrOfTy f.ty) ++ ","
  let encLines := item.fields.map fun f =>
    "        " ++ encStmts f.ty ("&self." ++ f.name)
  let decLines := item.fields.map fun f =>
    "        " ++ decStmts f.ty f.name
  let shorthand := String.intercalate ", " (item.fields.map (·.name))
  "#[rustfmt::skip]\n#[derive(Clone, Debug, PartialEq, Eq)]\n" ++
  "pub struct " ++ name ++ " {\n" ++
  String.intercalate "\n" fieldDecls ++ "\n}\n\n" ++
  "#[rustfmt::skip]\nimpl " ++ name ++ " {\n" ++
  "    /// Encode in SchemaCore.Codec's wire form (fields in schema order).\n" ++
  "    pub fn encode(&self, out: &mut Vec<u8>) {\n" ++
  String.intercalate "\n" encLines ++ "\n" ++
  "    }\n\n" ++
  "    /// Decode in SchemaCore.Codec's wire form (append-form: the\n" ++
  "    /// unconsumed suffix stays on the cursor). Out-of-policy bytes\n" ++
  "    /// are a typed CodecError, never a panic, never a silent misparse.\n" ++
  "    pub fn decode(bs: &mut &[u8]) -> Result<" ++ name ++ ", CodecError> {\n" ++
  String.intercalate "\n" decLines ++ "\n" ++
  "        Ok(" ++ name ++ " { " ++ shorthand ++ " })\n" ++
  "    }\n\n" ++
  "    /// The exact-image form: decode and require the whole input.\n" ++
  "    pub fn decode_full(bs: &[u8]) -> Result<" ++ name ++ ", CodecError> {\n" ++
  "        let mut rest = bs;\n" ++
  "        let value = Self::decode(&mut rest)?;\n" ++
  "        if !rest.is_empty() {\n" ++
  "            return Err(CodecError::TrailingBytes);\n" ++
  "        }\n" ++
  "        Ok(value)\n" ++
  "    }\n" ++
  "}\n"

/-- The registry → the lib.rs body (pure, total; the fold over the
    universe). -/
def renderLib (reg : DataRegistry Item) : String :=
  libPrelude ++ "\n\n" ++
  String.intercalate "\n\n" (reg.items.map renderRecord) ++ "\n"

/-! ## The differential — the correspondence's evidence (03 §3)

The vectors' bytes are COMPUTED by `SchemaCore.Codec`'s `encVal` over
the pinned fixture values (never hand-written) and committed through
the byte-tie; the generated Rust test decodes them, re-encodes
byte-identically (BOTH directions), and the tampered vectors REFUSE
(typed `CodecError`, no panic). -/

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

/-- The ATOM rows: (name, the Rust expected-value constructor, the
    `encVal` bytes). The value literal is a deliberate COPY — if it
    drifts from the bytes, the differential's decode-then-compare
    FAILS loudly (that is the check). -/
def atomGoldens : List (String × String × List UInt8) :=
  [ ("bool_false", "Atom::Bool(false)", encVal .bool (.bool false))
  , ("bool_true", "Atom::Bool(true)", encVal .bool (.bool true))
  , ("u64_varint", "Atom::U64(300)", encVal .u64 (.u64 300))
  , ("i64_negative", "Atom::I64(-1)", encVal .i64 (.i64 (-1)))
  , ("i64_positive", "Atom::I64(1)", encVal .i64 (.i64 1))
  , ("string_chars", "Atom::Str(\"hi\")", encVal .string (.string "hi")) ]

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

/-- The hex byte literal (stable, width-2). -/
def byteLit (b : UInt8) : String :=
  let hexDigit : Nat → String
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
    | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
    | 10 => "a" | 11 => "b" | 12 => "c" | 13 => "d" | 14 => "e" | 15 => "f"
    | _ => "?"
  "0x" ++ hexDigit (b.toNat / 16) ++ hexDigit (b.toNat % 16)

/-- The byte-literal list body. -/
def bytesLit : List UInt8 → String
  | [] => ""
  | [b] => byteLit b
  | b :: bs => byteLit b ++ ", " ++ bytesLit bs

/-- The generated integration test: the differential's Rust half. The
    pinned-value fixture (`pinned_example`) is the slice fixture's —
    see the module header's honest gap. -/
def renderDifferential : String :=
  let atomLines := atomGoldens.map fun p =>
    "    (\"" ++ p.1 ++ "\", " ++ p.2.1 ++ ", &[" ++ bytesLit p.2.2 ++ "]),"
  let rowLines := rowGoldens.map fun p =>
    "    (\"" ++ p.1 ++ "\", &[" ++ bytesLit p.2 ++ "]),"
  let tamperLines := tamperVectors.map fun p =>
    "    (\"" ++ p.1 ++ "\", &[" ++ bytesLit p.2 ++ "]),"
"//! GENERATED differential vectors + the Rust half of the Lean<->Rust
//! codec correspondence (notes/v3/03 section 3's differential level).
//! The vectors' bytes are computed by SchemaCore.Codec's encVal on the
//! pinned fixture values (SchemaCore.Emit.Rust.atomGoldens /
//! .rowGoldens / .tamperVectors) and committed through the byte-tie —
//! never hand-written, never hand-edited.

use schema_generated::{dec_bool, dec_i64, dec_string, dec_u64, enc_str,
  enc_varint, zigzag_i64, Example};

/// The typed expected value per atom vector (the value-level pin — a
/// drift from the bytes fails the decode-then-compare below).
#[derive(Debug, PartialEq, Eq)]
enum Atom {
    Bool(bool),
    U64(u64),
    I64(i64),
    Str(&'static str),
}

// The atom vectors (both directions: decode + re-encode).
static GOLDEN: &[(&str, Atom, &[u8])] = &[
" ++ String.intercalate "\n" atomLines ++ "
];

// The record rows (the generated struct's codec, both directions).
static EXAMPLES: &[(&str, &[u8])] = &[
" ++ String.intercalate "\n" rowLines ++ "
];

// The tamper vectors (every one must REFUSE — typed error, no panic).
static TAMPER: &[(&str, &[u8])] = &[
" ++ String.intercalate "\n" tamperLines ++ "
];

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

/// BOTH directions on every pinned atom: bytes -> value (decode,
/// against the typed pin), value -> bytes (re-encode, byte-identical).
#[test]
fn golden_atoms_decode_and_reencode() {
    for (name, expect, bytes) in GOLDEN {
        let bytes: &[u8] = bytes;
        let mut rest: &[u8] = bytes;
        let mut out = Vec::new();
        match expect {
            Atom::Bool(v) => {
                let got = dec_bool(&mut rest)
                    .unwrap_or_else(|e| panic!(\"atom {name} refused: {e:?}\"));
                assert_eq!(&got, v, \"atom {name} value drifted\");
                out.push(if got { 1u8 } else { 0u8 });
            }
            Atom::U64(v) => {
                let got = dec_u64(&mut rest)
                    .unwrap_or_else(|e| panic!(\"atom {name} refused: {e:?}\"));
                assert_eq!(&got, v, \"atom {name} value drifted\");
                enc_varint(got, &mut out);
            }
            Atom::I64(v) => {
                let got = dec_i64(&mut rest)
                    .unwrap_or_else(|e| panic!(\"atom {name} refused: {e:?}\"));
                assert_eq!(&got, v, \"atom {name} value drifted\");
                enc_varint(zigzag_i64(got), &mut out);
            }
            Atom::Str(v) => {
                let got = dec_string(&mut rest)
                    .unwrap_or_else(|e| panic!(\"atom {name} refused: {e:?}\"));
                assert_eq!(&got, v, \"atom {name} value drifted\");
                enc_str(got.as_str(), &mut out);
            }
        }
        assert!(
            rest.is_empty(),
            \"atom {name} left {rest:?} unconsumed\"
        );
        assert_eq!(out, bytes, \"re-encode drifted for {name}\");
    }
}

/// BOTH directions on every pinned record row: bytes -> Example
/// (decode), Example -> bytes (re-encode, byte-identical).
#[test]
fn golden_rows_decode_and_reencode() {
    for (name, bytes) in EXAMPLES {
        let bytes: &[u8] = bytes;
        let mut rest: &[u8] = bytes;
        let value = Example::decode(&mut rest)
            .unwrap_or_else(|e| panic!(\"golden vector {name} refused: {e:?}\"));
        assert!(
            rest.is_empty(),
            \"golden vector {name} left {rest:?} unconsumed\"
        );
        let mut out = Vec::new();
        value.encode(&mut out);
        assert_eq!(out, bytes, \"re-encode drifted for {name}\");
    }
}

/// The example_row's bytes denote the PINNED value (the decode
/// direction at the value level, not just shape).
#[test]
fn example_row_denotes_the_pinned_value() {
    let mut rest: &[u8] = EXAMPLES[EXAMPLES.len() - 1].1;
    let value = Example::decode(&mut rest).expect(\"example_row decodes\");
    assert_eq!(value, pinned_example());
}

/// The append-form law's Rust mirror: the encoding plus ANY suffix
/// decodes to the value plus the suffix (Pattern #2's composition).
#[test]
fn decode_is_append_form() {
    let suffixed: Vec<u8> = {
        let mut v = EXAMPLES[EXAMPLES.len() - 1].1.to_vec();
        v.push(0xFF);
        v
    };
    let mut rest: &[u8] = &suffixed;
    let value = Example::decode(&mut rest)
        .unwrap_or_else(|e| panic!(\"append-form failed: {e:?}\"));
    assert_eq!(value, pinned_example());
    assert_eq!(rest, &[0xFFu8]);
}

/// THE NEGATIVE CONTROL: every tampered vector REFUSES — a typed
/// CodecError, never a panic, never a silent misparse.
#[test]
fn tampered_vectors_refuse() {
    for (name, bytes) in TAMPER {
        match Example::decode_full(bytes) {
            Ok(_) => panic!(\"tampered vector {name} decoded — the wire gate has a hole\"),
            Err(_) => {} // the typed refusal is the pass
        }
    }
}
"
/-! ## The emitter -/

/-- The Rust lane's emitter: the SECOND emitter over the ONE regen
    core. `outputs_nodup` is in the type; the law is the registry's
    closed-world naming invariant (the same certificate the WIT lane
    discharges — one naming world, two renderings). -/
def rustEmitter : Emitter (DataRegistry Item) where
  name := "schema-rust"
  style := .doubleSlash
  specSource := "SchemaCore.Slice"
  outputs :=
    [ "crates/schema-generated/src/lib.rs"
    , "crates/schema-generated/tests/differential.rs" ]
  run reg :=
    [ { path := "crates/schema-generated/src/lib.rs"
        contents := renderLib reg }
    , { path := "crates/schema-generated/tests/differential.rs"
        contents := renderDifferential } ]
  law := some fun reg => (reg.items.map reg.nameOf).Nodup

end SchemaCore.Emit.Rust
