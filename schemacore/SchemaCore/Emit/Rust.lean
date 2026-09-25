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
import SchemaCore.Commit
import Kit.Duel
import Kit.Text

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

/-- The map/set KEY rendering: the key sub-universe's slice through
    the `KeyTy.toTy` injection (the delegation IS the definition —
    `tyRustPrim` reads the scalar rows via the fold's coherence,
    `keyRustPrim`'s table in SchemaCore.Fold). -/
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
  String.ofList (go (lastName s).toList true)

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

/-- The encode statements for a value of schema type `t`. -/
def encStmts (t : Ty) (e : String) : String := foldTy encAlg t e

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

/-- The decode statements for a schema type `t`. -/
def decStmts (t : Ty) (n : String) : String := foldTy decAlg t n

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
    generated code, never hand-formatted.

    STRUCTURE on the rope (`Kit.Text.cat`/`sepBy` — the leaf templates
    stay string-exact): the leaf strings here are IDENTICAL to the
    `++`-chain form this replaced, in the same order — the
    `render_cat_strs`/`render_sepBy_strs` bridge laws make the rendered
    bytes a theorem-side match for the old template (and gen-check
    proves it on the artifact). -/
def renderRecord (item : Item) : Text :=
  let name := pascalName item.name
  let fieldDecls := item.fields.map fun f =>
    .str ("    pub " ++ f.name ++ ": " ++ tyRust (descrOfTy f.ty) ++ ",")
  let encLines := item.fields.map fun f =>
    .str ("        " ++ encStmts f.ty ("&self." ++ f.name))
  let decLines := item.fields.map fun f =>
    .str ("        " ++ decStmts f.ty f.name)
  let shorthand := String.intercalate ", " (item.fields.map (·.name))
  Text.cat
    [ .str "#[rustfmt::skip]\n#[derive(Clone, Debug, PartialEq, Eq)]\n"
    , .str ("pub struct " ++ name ++ " {\n")
    , Text.sepBy "\n" fieldDecls
    , .str "\n}\n\n"
    , .str ("#[rustfmt::skip]\nimpl " ++ name ++ " {\n")
    , .str "    /// Encode in SchemaCore.Codec's wire form (fields in schema order).\n"
    , .str "    pub fn encode(&self, out: &mut Vec<u8>) {\n"
    , Text.sepBy "\n" encLines
    , .str "\n    }\n\n"
    , .str "    /// Decode in SchemaCore.Codec's wire form (append-form: the\n"
    , .str "    /// unconsumed suffix stays on the cursor). Out-of-policy bytes\n"
    , .str "    /// are a typed CodecError, never a panic, never a silent misparse.\n"
    , .str ("    pub fn decode(bs: &mut &[u8]) -> Result<" ++ name ++ ", CodecError> {\n")
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
    , .str "    }\n"
    , .str "}\n" ]

/-- The registry → the lib.rs body's ROPE (pure, total; the fold over
    the universe). The record blocks are ONE `sepBy` join — O(1) per
    block. The rope is EXPOSED (not folded into a String): the golden
    module's chunk literals ride `Text.chunks` of THIS — the goldens
    theorems compare chunk-wise (the kernel never executes the join;
    the monolithic-string whnf is quadratic in the body and blows the
    elaboration budget — measured 5min for the differential alone). -/
def libRope (reg : DataRegistry Item) : Text :=
  Text.cat
    [ .str libPrelude
    , .str "\n\n"
    , Text.sepBy "\n\n" (reg.items.map renderRecord)
    , .str "\n" ]

/-- The lib.rs body: ONE render at the file boundary. -/
def renderLib (reg : DataRegistry Item) : String :=
  Text.render (libRope reg)

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

/-- The duel's vector path for one row name. -/
def duelPath (name : String) : String := duelDir ++ "/" ++ name ++ ".bin"

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
    this lane's parameters: the DataRegistry spec + the registry law
    (the DRY sweep; the style is the VectorSet's own `.doubleSlash`
    field, the artifact-headers gate's shape contract reads it). -/
def duelEmitter : Emitter (DataRegistry Item) :=
  Kit.Duel.emitterWith duelVectors "SchemaCore.Slice"
    (law := some fun reg => (reg.items.map reg.nameOf).Nodup)

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

/-- The COMMIT-SLICE consumer's emitter (the bidirectional slice's
    differential — SchemaCore.Commit's duel's Rust side). Its OWN
    emitter: the golden-theorem channel stays at the two codec
    artifacts (the three-rope kernel crack exceeded the
    kernel-check's budget — the monolithic-literal whnf's quadratic
    shape); this artifact's ONE tie is `gates gen-check` (the duel
    manifest's channel — one tie per artifact, 09's rule). -/
def commitSliceEmitter : Emitter (DataRegistry Item) where
  name := "schema-commit-slice"
  style := .doubleSlash
  specSource := "SchemaCore.Commit"
  outputs := ["crates/schema-generated/tests/commit_slice.rs"]
  run _ :=
    [ { path := "crates/schema-generated/tests/commit_slice.rs"
        contents := commitSliceRust } ]
  law := some fun reg => (reg.items.map reg.nameOf).Nodup

end SchemaCore.Emit.Rust
