/-
# WasmCore.Encode — the binary byte emission (the wire crossing)

Total, pure byte emission for the module model. The LEB128 varint
atom lives in `Kit.Varint` (the C0 shared home — it was mined here
first and moved down when `SchemaCore.Codec` became the twin's second
copy); this module consumes it as `encVarNat`/`decVarNat?`/`varintCodec`
— the wire grade, 01-core §4, with pattern #2's append-form law
(`decVarNat? (encVarNat n ++ rest) = some (n, rest)`) and the
exact-image accepted-byte policy: the decoder is the canonical
(minimal) one, so non-minimal LEB encodings are the declared
outside-of-policy surface, not folklore. (wasm's spec grammar is more
permissive; tightening lands with the binary decoder order if a
consumer needs it.)

Totality evidence: every encoder is structural — folds/maps/flatMaps
over lists, and `sleb` recurses on an explicit fuel that strictly
decreases (each continuation step divides by ≥ 2). `sleb` is
emission-side only: its decode + law land with the binary-decoder
order (the golden byte-tie pins its bytes meanwhile — honesty note,
not a silent gap).

The five questions (notes/v3/01-core.md):

- **Root**: Crossing (the wire) — bytes are the target grammar, the
  instruction list the source.
- **Carrier grade**: Kit.Codec (decode∘encode = id + the explicit
  accepted-byte policy) — for the varint atom in `Kit.Varint`; the
  append-form law (15-patterns #2) is the stated composition
  discipline on top.
- **Spine reading**: an emitter is an interpretation — this is the
  reading of the universe into the wasm binary grammar; the module
  file emitter (Kit.Emit, the artifact spine) is NOT here — no
  generated-artifact consumer yet (the leftover rule).
- **Ladder rung**: the round-trip law is a hand theorem with named
  content (the canonical-decoder agreement, in `Kit.Varint`); the
  golden vectors are the byte-tie regression.
- **Gate row**: WasmCore's row in Gates.Packages' gated set (the
  per-library axiom sweep covers it) + the golden byte-tie
  suite in WasmCoreTests.

Consumer trail: rides `Kit.Correspondence` (Codec), `Kit.Varint`
(the shared varint atom), `WasmCore.Types`, `WasmCore.Instr`,
`WasmCore.OpTable` (the ONE op table's wire facets),
`WasmCore.Module`. Core-only (the cone rule).
-/

import Kit.Correspondence
import Kit.Varint
import WasmCore.Types
import WasmCore.Instr
import WasmCore.OpTable
import WasmCore.Module

namespace WasmCore

open Kit.Varint

/-! ## The unsigned varint — consumed from `Kit.Varint` -/

-- The unsigned LEB128 varint is the kit's ONE copy (`Kit.Varint`:
-- `encVarNat`/`decVarNat?` + the append-form law + the exact-image
-- policy as `varintCodec`) — the twin copies in this module and
-- `SchemaCore.Codec` were consolidated into the C0 shared home. The
-- encoders below consume it directly; the signed pair (`sleb`) stays
-- emission-side until the binary-decoder order.

/-! ## LEB128 — the signed encoder (emission-side; the pair lands with
     the binary-decoder order) -/

/-- Signed LEB128 of a non-negative value, on an explicit fuel. The
    stop condition emits the sign-extension group (a value whose top
    sign bit would be set takes the extra `0x00` group). -/
def slebGo : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n =>
      if n / 128 == 0 && n % 128 < 64 then [n % 128 |>.toUInt8]
      else (n % 128 + 128).toUInt8 :: slebGo k (n / 128)

/-- The signed encoder: fuel `n + 2` suffices (each non-final step
    divides by 128; the `0`-quotient tail costs one extra group). -/
def sleb (n : Nat) : List UInt8 := slebGo (n + 2) n

/-- Signed LEB128 of an Int (possibly negative), on an explicit fuel
    (each step shifts right by 7; a 64-bit two's-complement value
    costs at most 10 groups). The stop condition emits the final group
    when the remaining value fits a sign-extended 7-bit group. -/
def slebIGo : Nat → Int → List UInt8
  | 0, _ => []
  | k + 1, v =>
      if v ≥ -64 && v ≤ 63 then [(((v % 128) + 128) % 128).toNat.toUInt8]
      else
        -- the continuation group carries the 0x80 more-groups bit
        let b := ((((v % 128) + 128) % 128) + 128).toNat.toUInt8
        b :: slebIGo k ((v - ((b.toNat % 128) : Int)) / 128)

/-- The signed encoder over Int: 12 groups bound any 64-bit value. -/
def slebI (v : Int) : List UInt8 := slebIGo 12 v

/-- The `i32.const` wire value: the AST's Nat carries the BIT PATTERN
    (the executor wraps); the wire's immediate is the SIGNED 32-bit
    two's-complement value — a pattern with the high bit set encodes
    as its negative (the canonical form; wasmtime's decoder refuses
    the unsigned reading with `integer too large`). -/
def i32ConstWire (n : Nat) : Int :=
  let w := n % 4294967296
  if w < 2147483648 then w else w - 4294967296

/-- The `i64.const` wire value (the same fold at 64 bits). -/
def i64ConstWire (n : Nat) : Int :=
  let w := n % 18446744073709551616
  if w < 9223372036854775808 then w else w - 18446744073709551616

/-! ## The wire maps (explicit arms — design doc R7) -/

/-- The value types' byte codes. -/
def encodeValType : ValType → UInt8
  | .i32 => 0x7F | .i64 => 0x7E | .f32 => 0x7D | .f64 => 0x7C
  | .funcref => 0x70 | .externref => 0x6F

/-- The functype wire shape: `0x60 params results`. -/
def encodeFuncType (ft : FuncType) : List UInt8 :=
  0x60 :: (encVarNat ft.params.length ++ (ft.params.map encodeValType)
    ++ (encVarNat ft.results.length ++ ft.results.map encodeValType))

/-! The mem/op facets ride the ONE op table (`WasmCore.OpTable`):
    `memOpcode`/`memAlignDefault`/`opOpcode` are the row's projections
    (07-extensibility R6 — no parallel wire maps). -/

mutual
/-- ONE instruction → its bytes. Total, structural, explicit arms. -/
def encodeInstr : Instr → List UInt8
  | .i32const n => 0x41 :: slebI (i32ConstWire n)
  | .i64const n => 0x42 :: slebI (i64ConstWire n)
  | .localget n => 0x20 :: encVarNat n
  | .localset n => 0x21 :: encVarNat n
  | .localtee n => 0x22 :: encVarNat n
  | .call fn => 0x10 :: encVarNat fn
  | .callindirect ty => 0x11 :: (0x00 :: encVarNat ty)  -- the type index + the ONE table's 0x00
  | .mem op offset align =>
      [memOpcode op] ++ (encVarNat (align.getD (memAlignDefault op)) ++ encVarNat offset)
  | .op o => opOpcode o
  | .br d => 0x0C :: encVarNat d
  | .brif d => 0x0D :: encVarNat d
  | .block b => 0x02 :: (0x40 :: (encodeBody b ++ [0x0B]))
  | .loop b => 0x03 :: (0x40 :: (encodeBody b ++ [0x0B]))
  | .if_ t e =>
      0x04 :: (0x40 :: (encodeBody t ++
        match e with
        | [] => [0x0B]
        | _ => 0x05 :: (encodeBody e ++ [0x0B])))
  | .ret => [0x0F]
  | .drop => [0x1A]
  | .select => [0x1B]
  | .unreach => [0x00]

/-- A body's bytes: each instruction's bytes in order (the `end`
    opcodes are the CALLERS' business — a body's own terminator is a
    property of what encloses it). -/
def encodeBody : List Instr → List UInt8
  | [] => []
  | i :: is => encodeInstr i ++ encodeBody is
end

/-- One code-section entry: the local groups (one per declared local —
    canonical, if not maximally grouped; grouping is an optimization
    the byte-tie re-pins if it ever matters) + the body + the `end`. -/
def encodeFuncEntry (f : Func) : List UInt8 :=
  let localsBytes := encVarNat f.locals.length ++
    (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]) |>.foldl (· ++ ·) [])
  let bodyBytes := localsBytes ++ (encodeBody f.body ++ [0x0B])
  encVarNat bodyBytes.length ++ bodyBytes

/-- One export entry: name (UTF-8, length-prefixed) + kind + index
    (func kind 0x00, memory kind 0x02 — the binary format's). -/def encodeExport (e : Export) : List UInt8 :=
  let nameBytes := e.name.toByteArray.toList
  match e.desc with
  | .func idx => (encVarNat nameBytes.length ++ nameBytes) ++ (0x00 :: encVarNat idx)
  | .memory idx => (encVarNat nameBytes.length ++ nameBytes) ++ (0x02 :: encVarNat idx)

/-- One table entry: the funcref element type (0x70) + the limits
    (no-max form 0x00, min = the entries' length — the table's size IS
    its initialization). -/
def encodeTable (t : Table) : List UInt8 :=
  0x70 :: (0x00 :: encVarNat t.init.length)

/-- One ACTIVE element segment (form 0x00: table 0 implied): the
    offset expression `i32.const 0; end`, then the function indices in
    order — the table's initialization face. -/
def encodeElem (t : Table) : List UInt8 :=
  0x00 :: ([0x41, 0x00, 0x0B]
    ++ (encVarNat t.init.length ++ (t.init.map encVarNat |>.foldl (· ++ ·) [])))

/-- A section: id + length-prefixed content. -/
def encodeSection (id : UInt8) (content : List UInt8) : List UInt8 :=
  id :: (encVarNat content.length ++ content)

/-- The preamble: magic + version. -/
def encodePreamble : List UInt8 :=
  [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]

/-- THE module encoder: the minimal sections in the binary format's
    fixed order (type 1, function 3, table 4, memory 5, export 7,
    element 9, code 10), each elided when empty; `memMin = 0` omits
    memory, `tables = []` omits the table section, and the element
    section covers only the tables WITH entries. Total by
    construction — every fold is structural, every size an encVarNat. -/
def encodeModule (m : Module) : List UInt8 :=
  encodePreamble
    ++ (if m.types.isEmpty then [] else
        encodeSection 1
          (encVarNat m.types.length ++ (m.types.map encodeFuncType |>.foldl (· ++ ·) [])))
    ++ (if m.funcs.isEmpty then [] else
        encodeSection 3 (encVarNat m.funcs.length ++ (m.funcs.map (fun f => encVarNat f.tyIdx)
          |>.foldl (· ++ ·) [])))
    ++ (if m.tables.isEmpty then [] else
        encodeSection 4 (encVarNat m.tables.length
          ++ (m.tables.map encodeTable |>.foldl (· ++ ·) [])))
    ++ (if m.memMin = 0 then [] else
        encodeSection 5 (encVarNat 1 ++ [0x00] ++ encVarNat m.memMin))
    ++ (if m.exports.isEmpty then [] else
        encodeSection 7 (encVarNat m.exports.length
          ++ (m.exports.map encodeExport |>.foldl (· ++ ·) [])))
    ++ (let elems := m.tables.filter (fun t => !t.init.isEmpty)
        if elems.isEmpty then [] else
        encodeSection 9 (encVarNat elems.length
          ++ (elems.map encodeElem |>.foldl (· ++ ·) [])))
    ++ (if m.funcs.isEmpty then [] else
        encodeSection 10 (encVarNat m.funcs.length
          ++ (m.funcs.map encodeFuncEntry |>.foldl (· ++ ·) [])))

end WasmCore
