/-
# WasmCore.Decode — the binary wasm decoder: bytes → the ONE AST

The read direction of the wasm binary face — F4 (notes/design-wave-30.md).
The emitter (`WasmCore.Encode`) is the ONE writer; this module is the ONE
reader, and the opcode bytes are never re-spelled here: the instruction
decode FOLDS the ONE op table's `opOpcode`/`memOpcode` rows (07 R6 — the
table's byte spellings are the authority; a misread is impossible by
construction, `opOfBytes?`/`memOfByte?` over the completeness-proved
`allOps`/`allMems`), and the varints ride `Kit.Varint`'s canonical-minimal
discipline (a non-minimal LEB group refuses — the wave's canonicality
law, now enforced on the read side too).

## The structured refusals

A corrupt/truncated/invalid module refuses with the position + the
reason — the `ParseError/Diag` discipline: `DecodeError` is a closed
inductive whose ctors are the failure KINDS with their payload (never a
bare string, never a panic), rendered into the ONE Diag envelope by
`toDiag` (the WD-family E-codes, the WV precedent: the constants land
in one place, ready for the persisted registry).

## The round-trip law (pattern #2, the append form)

`decode ∘ encode = id` over the valid fragment — the encoder's honest
image. The fragment predicate is `moduleFrag`: every const's BIT
PATTERN is canonical (`i32const` below 2^32, `i64const` below 2^64 —
the wire's immediate is the SIGNED two's-complement value, so an AST
const ≥ 2^31 encodes to the same bytes as its wrapped twin and the
decoder recovers the pattern, not the original Nat) and no memarg
re-states its elided default alignment. The laws:

- `decVarNatR_enc_append` — the positioned unsigned reader inherits
  `Kit.Varint`'s append-form law (the agreement lemma
  `decVarNatR_decVarNat` ties it to the ONE decoder).
- `decSlebR_slebI_append` — the sleb's two-directionality: the C6-fixed
  encoder's face gains its decode + the law (the canonicality check
  refuses exactly the redundant-zero-group shapes the encoder never
  emits — the exact-image discipline).
- `decInstr_enc` / `decBody_enc` — per-instruction and per-body.
- `decode_encode_module` — the module law itself.
- `checkModule_decode_encode` — the validator's consumption: a decoded
  module re-validates to the same verdict.

Exhaustiveness is the closed-universe discipline: the decode dispatch
folds `allOps`/`allMems` (compile-forced completeness), so a new
op-table row without its decode arm is a compile failure — and its
decode arm arrives FREE with the row.

The five questions (notes/v3/01-core.md):

- **Root**: Crossing (the wire) — bytes are the source grammar, the
  ONE AST the target.
- **Carrier grade**: the laws are hand theorems with named content
  (the append-form discipline, pattern #2); the accepted-byte policy
  is the canonical fragment (non-minimal varints refuse), the module
  law stated over `moduleFrag`.
- **Spine reading**: the artifact stage's inverse for the BINARY lane —
  the ONE reader every wasm-bytes-reading lane calls; `WasmCore.Encode`
  is the ONE writer.
- **Ladder rung**: rung 1-6 — total folds + hand theorems (the varint
  laws port Kit.Varint's; the module law assembles them).
- **Gate row**: WasmCore's row in Gates.Packages' gated set + the
  WasmCoreTests round-trip sweeps + the corruption/non-minimal
  negative controls + the differential over the duel corpus.

Core-only (imports Kit + WasmCore modules — the cone rule; WatParse
only for the completeness-proved `allOps`/`allMems` folds).
-/

import Kit.Diag
import Kit.Varint
import WasmCore.Types
import WasmCore.Instr
import WasmCore.OpTable
import WasmCore.Module
import WasmCore.Encode
import WasmCore.WatParse

namespace WasmCore.Decode

open Kit.Varint
open WasmCore.WatParse (allOps allMems)

/-! ## The structured refusals (errors are data, never a panic) -/

/-- The decoder's refusal kinds, each with its position (+ payload).
    The wire's failure surface: truncation, the preamble, the section
    envelope, the type/op spellings, the canonicality disciplines, and
    the module-model's structural mismatches. -/
inductive DecodeError where
  /-- Ran out of bytes at `pos` (needed `need` more). -/
  | truncated (pos : Nat) (need : Nat)
  /-- The magic `00 61 73 6D` is wrong. -/
  | badMagic (pos : Nat)
  /-- The version `01 00 00 00` is wrong. -/
  | badVersion (pos : Nat)
  /-- A section id out of the fixed order (or below the expected slot —
      the closed world's unknown ids land here too). -/
  | sectionOrder (pos : Nat) (id : UInt8)
  /-- A valtype byte outside `encodeValType`'s image. -/
  | badValType (pos : Nat) (byte : UInt8)
  /-- A functype lead byte ≠ `0x60`. -/
  | badFuncType (pos : Nat) (byte : UInt8)
  /-- A table entry's bytes are not the canonical form (`0x70` funcref
      + `0x00` limits flag) — the table section's OWN refusal (never the
      functype's code re-purposed, and never the EXPECTED byte in the
      Diag's got: the render names the byte the wire actually carried). -/
  | badTableForm (pos : Nat) (byte : UInt8)
  /-- A memory entry's byte is not the canonical limits form (`0x00`
      flag) — the memory section's OWN refusal (never the functype's
      code re-purposed with the expected byte as the got). -/
  | badMemForm (pos : Nat) (byte : UInt8)
  /-- An element segment's offset expression is not the canonical
      `i32.const 0; end` (`41 00 0B`) — the offset-expression refusal's
      OWN row (the form-byte refusal is `badElemForm`; the two share
      nothing: the byte each renders is the byte the wire carried). -/
  | badElemOffset (pos : Nat) (byte : UInt8)
  /-- A block type byte ≠ `0x40` (the no-result frame fragment), or an
      `else` byte where no `if` is open. -/
  | badBlockType (pos : Nat) (byte : UInt8)
  /-- `call_indirect`'s table byte ≠ `0x00` (the ONE table). -/
  | badCallIndirect (pos : Nat) (byte : UInt8)
  /-- A lead byte no op-table row names. -/
  | badOpcode (pos : Nat) (byte : UInt8)
  /-- The memory section's count ≠ 1 (the ONE memory). -/
  | badMemCount (pos : Nat) (n : Nat)
  /-- An element segment's form byte ≠ `0x00` (the offset-expression
      refusals ride `badElemOffset`). -/
  | badElemForm (pos : Nat) (byte : UInt8)
  /-- An export kind byte neither `0x00` (func) nor `0x02` (memory). -/
  | badExportKind (pos : Nat) (byte : UInt8)
  /-- A non-minimal (non-canonical) unsigned varint — the wave's
      canonicality discipline on the read side. -/
  | nonMinimalVarint (pos : Nat)
  /-- A non-minimal signed varint (the redundant zero group the
      fixed encoder never emits). -/
  | nonMinimalSleb (pos : Nat)
  /-- An export name is not valid UTF-8. -/
  | badUtf8 (pos : Nat)
  /-- The instruction nesting exceeded the fuel (the module's
      instruction budget — a corrupt body, honestly refused). -/
  | tooDeep (pos : Nat)
  /-- A code entry's body does not exactly fill its declared size. -/
  | bodyOverrun (pos : Nat)
  /-- The function section and the code section disagree on the count. -/
  | funcCountMismatch (pos : Nat)
  /-- A table's declared size and its element segment disagree. -/
  | tableElemMismatch (pos : Nat)
  /-- A non-empty table has no element segment. -/
  | missingElem (pos : Nat)
  /-- An element segment names a table the table section never declared. -/
  | elemWithoutTable (pos : Nat)
  /-- Bytes remain after the last section. -/
  | leftover (pos : Nat)
  /-- INTERNAL control-flow signal, never escaping `decodeModule`:
      `decInstr` refuses the body-terminator bytes (`0x0B` = a frame's
      end, `0x05` = an `else` divider) and `decBody` catches them as
      the successful stop. -/
  | endOfBody (pos : Nat) (else5 : Bool)
deriving BEq, Repr, Inhabited

/-! The decoder's E-code CONSTANTS (the WD family — the WV
precedent: they land here, in one place, ready for the persisted
registry; the meaning lives at the registry, never in the spelling). -/
namespace DecodeError

def ecTruncated : Kit.ECode := ⟨"WD1001"⟩
def ecMagic : Kit.ECode := ⟨"WD1002"⟩
def ecVersion : Kit.ECode := ⟨"WD1003"⟩
def ecSectionOrder : Kit.ECode := ⟨"WD1004"⟩
def ecValType : Kit.ECode := ⟨"WD1005"⟩
def ecFuncType : Kit.ECode := ⟨"WD1006"⟩
def ecBlockType : Kit.ECode := ⟨"WD1007"⟩
def ecCallIndirect : Kit.ECode := ⟨"WD1008"⟩
def ecOpcode : Kit.ECode := ⟨"WD1009"⟩
def ecMemCount : Kit.ECode := ⟨"WD1010"⟩
def ecElemForm : Kit.ECode := ⟨"WD1011"⟩
def ecExportKind : Kit.ECode := ⟨"WD1012"⟩
def ecNonMinimalVarint : Kit.ECode := ⟨"WD1013"⟩
def ecNonMinimalSleb : Kit.ECode := ⟨"WD1014"⟩
def ecUtf8 : Kit.ECode := ⟨"WD1015"⟩
def ecTooDeep : Kit.ECode := ⟨"WD1016"⟩
def ecBodyOverrun : Kit.ECode := ⟨"WD1017"⟩
def ecFuncCount : Kit.ECode := ⟨"WD1018"⟩
def ecTableElem : Kit.ECode := ⟨"WD1019"⟩
def ecMissingElem : Kit.ECode := ⟨"WD1020"⟩
def ecElemWithoutTable : Kit.ECode := ⟨"WD1021"⟩
def ecLeftover : Kit.ECode := ⟨"WD1022"⟩
def ecEndOfBody : Kit.ECode := ⟨"WD1023"⟩
def ecTableForm : Kit.ECode := ⟨"WD1024"⟩
def ecMemForm : Kit.ECode := ⟨"WD1025"⟩
def ecElemOffset : Kit.ECode := ⟨"WD1026"⟩

end DecodeError

/-- THE diagnostic envelope: every refusal renders into the ONE Diag —
    the E-code from the WD family, the position + payload as the got
    data. The byte-level failures have no enumerable valid space
    beyond the wire grammar itself (empty `valid`/`suggest` is then
    honest, not a skipped discipline). -/
def DecodeError.toDiag : DecodeError → Kit.Diag
  | .truncated pos need =>
      { code := ecTruncated
        , message := s!"unexpected end of bytes: {need} byte(s) needed at {pos}"
        , got := some s!"byte offset {pos}" }
  | .badMagic pos =>
      { code := ecMagic, message := "wrong magic: not a wasm module"
        , got := some s!"byte offset {pos}" }
  | .badVersion pos =>
      { code := ecVersion, message := "wrong version: expected 01 00 00 00"
        , got := some s!"byte offset {pos}" }
  | .sectionOrder pos id =>
      { code := ecSectionOrder
        , message := s!"section id {id} out of the fixed order (or unknown)"
        , got := some s!"section id {id} at byte offset {pos}" }
  | .badValType pos b =>
      { code := ecValType, message := s!"unknown value-type byte {b}"
        , got := some s!"byte {b} at offset {pos}" }
  | .badFuncType pos b =>
      { code := ecFuncType, message := s!"functype lead byte {b} is not 0x60"
        , got := some s!"byte {b} at offset {pos}" }
  | .badBlockType pos b =>
      { code := ecBlockType
        , message := s!"block type byte {b} is not 0x40 (the no-result frame fragment)"
        , got := some s!"byte {b} at offset {pos}" }
  | .badCallIndirect pos b =>
      { code := ecCallIndirect
        , message := s!"call_indirect table byte {b} is not 0x00 (the ONE table)"
        , got := some s!"byte {b} at offset {pos}" }
  | .badOpcode pos b =>
      { code := ecOpcode, message := s!"no op-table row names byte {b}"
        , got := some s!"byte {b} at offset {pos}" }
  | .badMemCount pos n =>
      { code := ecMemCount
        , message := s!"memory section count {n} is not 1 (the ONE memory)"
        , got := some s!"count {n} at offset {pos}" }
  | .badElemForm pos b =>
      { code := ecElemForm
        , message := s!"element segment form byte {b} is not 0x00"
        , got := some s!"byte {b} at offset {pos}" }
  | .badTableForm pos b =>
      { code := ecTableForm
        , message := s!"table entry's byte {b} at offset {pos} is not the canonical form \
          (0x70 funcref, 0x00 limits flag)"
        , got := some s!"byte {b} at offset {pos}" }
  | .badMemForm pos b =>
      { code := ecMemForm
        , message := s!"memory entry's byte {b} at offset {pos} is not the canonical limits \
          form (0x00 flag)"
        , got := some s!"byte {b} at offset {pos}" }
  | .badElemOffset pos b =>
      { code := ecElemOffset
        , message := s!"element segment's offset expression is not the canonical \
          i32.const 0; end (41 00 0B) — byte {b} at offset {pos}"
        , got := some s!"byte {b} at offset {pos}" }
  | .badExportKind pos b =>
      { code := ecExportKind
        , message := s!"export kind byte {b} is neither 0x00 (func) nor 0x02 (memory)"
        , got := some s!"byte {b} at offset {pos}" }
  | .nonMinimalVarint pos =>
      { code := ecNonMinimalVarint
        , message := "non-minimal LEB128 varint (the canonical-minimal discipline)"
        , got := some s!"group at {pos}" }
  | .nonMinimalSleb pos =>
      { code := ecNonMinimalSleb
        , message := "non-minimal signed LEB128 (the redundant zero group)"
        , got := some s!"group at {pos}" }
  | .badUtf8 pos =>
      { code := ecUtf8, message := "export name is not valid UTF-8"
        , got := some s!"name at {pos}" }
  | .tooDeep pos =>
      { code := ecTooDeep
        , message := "instruction nesting exceeded the decoder's budget"
        , got := some s!"byte offset {pos}" }
  | .bodyOverrun pos =>
      { code := ecBodyOverrun
        , message := "a code entry's body does not exactly fill its declared size"
        , got := some s!"entry at {pos}" }
  | .funcCountMismatch pos =>
      { code := ecFuncCount
        , message := "the function section and the code section disagree on the count"
        , got := some s!"byte offset {pos}" }
  | .tableElemMismatch pos =>
      { code := ecTableElem
        , message := "a table's declared size and its element segment disagree"
        , got := some s!"byte offset {pos}" }
  | .missingElem pos =>
      { code := ecMissingElem
        , message := "a non-empty table has no element segment"
        , got := some s!"byte offset {pos}" }
  | .elemWithoutTable pos =>
      { code := ecElemWithoutTable
        , message := "an element segment names a table the table section never declared"
        , got := some s!"byte offset {pos}" }
  | .leftover pos =>
      { code := ecLeftover, message := "bytes remain after the last section"
        , got := some s!"byte offset {pos}" }
  | .endOfBody pos e5 =>
      { code := ecEndOfBody
        , message :=
            if e5 then "unexpected `else` divider (0x05) outside an `if` frame"
            else "unexpected end opcode (0x0B) with no open frame"
        , got := some s!"byte offset {pos}" }

/-- The one-line rendering (the envelope's `.toString`). -/
def DecodeError.render (e : DecodeError) : String :=
  Kit.Diag.toString e.toDiag

/-! ## The positioned unsigned varint (riding Kit.Varint) -/

/-- The bind equations (`Except`'s core bind has no simp lemmas in
    core 4.33 — the decoder's chaining discipline needs them). -/
@[simp] theorem Except.ok_bind' {ε α β} {a : α} {f : α → Except ε β} :
    (Except.ok a : Except ε α).bind f = f a := rfl

@[simp] theorem Except.error_bind' {ε α β} {e : ε} {f : α → Except ε β} :
    (Except.error e : Except ε α).bind f = Except.error e := rfl

/-- The `.map` face of the same discipline (the value-type sequence's
    cons step rides it). -/
@[simp] theorem Except.ok_map' {ε α β} {a : α} {f : α → β} :
    (Except.ok a : Except ε α).map f = Except.ok (f a) := rfl

/-- The do-notation face: the desugared `let (a, b) ← e` form is
    `Bind.bind` over the Monad instance — the instance reduction blocks
    `Except.ok_bind'`'s `simp only` firing, so the slot laws' induction
    steps ride THIS form. -/
@[simp] theorem Except.ok_bindMono {ε α β} {a : α} {f : α → Except ε β} :
    Bind.bind (Except.ok a : Except ε α) f = f a := rfl

/-- The 256 bound, literal (omega treats `UInt8.size` as an opaque
    atom — the cast bridge theorems keep the goals in pure literals). -/
theorem lt256 (n : Nat) : 128 + n % 128 < 256 := by omega

/-- The continuation byte's value (the unsigned reader's face). -/
theorem byte128_val (n : Nat) : ((128 + n % 128 : Nat).toUInt8).toNat = 128 + n % 128 :=
  UInt8.toNat_ofNat_of_lt' (lt256 n)

/-- The continuation byte carries the more-groups bit. -/
theorem byte128_big (n : Nat) : ¬(((128 + n % 128 : Nat).toUInt8).toNat < 128) := by
  rw [byte128_val]
  omega

/-- The positioned reader over the SUFFIX (the remaining bytes) with
    the absolute position for the refusals. Structurally the same
    canonical-minimal discipline as `Kit.Varint.decVarNat?` — a
    continuation group whose remainder value is 0 refuses — with the
    truncation and the non-minimality DISTINGUISHED for the structured
    errors. The agreement lemma ties it to the ONE decoder. -/
def decVarNatR (pos : Nat) : List UInt8 → Except DecodeError (Nat × Nat)
  | [] => .error (.truncated pos 1)
  | b :: rest =>
      if b.toNat < 128 then .ok (b.toNat, pos + 1)
      else
        (decVarNatR (pos + 1) rest).bind fun (v, pos') =>
          if v = 0 then .error (.nonMinimalVarint pos)
          else .ok (b.toNat % 128 + 128 * v, pos')

/-- THE AGREEMENT: the positioned reader IS `Kit.Varint.decVarNat?` on
    the suffix — the ONE decoder's laws transfer. -/
theorem decVarNatR_decVarNat : ∀ (bs : List UInt8) (pos v pos' : Nat),
    decVarNatR pos bs = .ok (v, pos') →
    pos ≤ pos' ∧ decVarNat? bs = some (v, bs.drop (pos' - pos)) := by
  intro bs
  induction bs with
  | nil => intro pos v pos' h; simp [decVarNatR] at h
  | cons b rest ih =>
    intro pos v pos' h
    rw [decVarNatR] at h
    by_cases hlt : b.toNat < 128
    · rw [if_pos hlt] at h
      injection h with h1
      rw [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      refine ⟨by omega, ?_⟩
      rw [decVarNat?, if_pos hlt]
      simp
    · rw [if_neg hlt] at h
      cases hd : decVarNatR (pos + 1) rest with
      | error e => rw [hd] at h; simp at h
      | ok p =>
        obtain ⟨v2, pos2⟩ := p
        rw [hd] at h
        by_cases hv : v2 = 0
        · simp only [Except.ok_bind', if_pos hv] at h; simp at h
        · simp only [Except.ok_bind', if_neg hv] at h
          injection h with h1
          rw [Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          have ⟨hle, hag⟩ := ih (pos + 1) v2 pos2 hd
          refine ⟨by omega, ?_⟩
          simp only [decVarNat?, if_neg hlt, hag, if_neg hv]
          have hdrop : (b :: rest).drop (pos2 - pos) = rest.drop (pos2 - (pos + 1)) := by
            rw [List.drop_cons]; congr 1; omega
          rw [hdrop]

/-- THE APPEND-FORM LAW (pattern #2), positioned: the encoder's bytes
    plus any suffix decode to the value and the suffix — Kit.Varint's
    law, ported to the positioned reader. -/
theorem decVarNatR_enc_append : ∀ (k n : Nat) (rest : List UInt8) (pos : Nat),
    n < 128 ^ k →
    decVarNatR pos (encVarNatGo (k + 1) n ++ rest) =
      .ok (n, pos + (encVarNatGo (k + 1) n).length) := by
  intro k
  induction k with
  | zero =>
    intro n rest pos h
    have h0 : n = 0 := by omega
    subst h0
    simp [decVarNatR, encVarNatGo]
  | succ k ih =>
    intro n rest pos h
    rcases Nat.lt_or_ge n 128 with hlt | hge
    · have h256 : n < 256 := by omega
      simp only [encVarNatGo, if_pos hlt, List.singleton_append, decVarNatR,
        UInt8.toNat_ofNat_of_lt' h256]
      rfl
    · have hdiv : n / 128 < 128 ^ k := by omega
      have hpos : 0 < n / 128 := by omega
      rw [encVarNatGo, if_neg (by omega : ¬(n < 128)), List.cons_append,
        decVarNatR, if_neg (byte128_big n),
        ih (n / 128) rest (pos + 1) hdiv, Except.ok_bind']
      simp only [if_neg (show ¬(n / 128 = 0) from by omega)]
      have hval : (128 + n % 128) % 128 + 128 * (n / 128) = n := by omega
      rw [byte128_val]
      simp only [hval, List.length_cons, Except.ok.injEq, Prod.mk.injEq]
      clear h hdiv hpos hge ih hval
      exact ⟨trivial, by omega⟩

/-- The positioned reader's law over `encVarNat` (the fuel discharged). -/
theorem decVarNatR_enc : ∀ (n : Nat) (pos : Nat) (rest : List UInt8),
    decVarNatR pos (encVarNat n ++ rest) = .ok (n, pos + (encVarNat n).length) :=
  fun n pos rest => decVarNatR_enc_append n n rest pos (Nat.lt_pow_self (by decide))

/-! ## The positioned signed varint (the sleb's two-directionality) -/

/-- A non-negative Int IS a Nat (the bridge that keeps every byte
    fact's proof in pure Nat arithmetic). -/
theorem intNat {p : Int} (h : 0 ≤ p) : ∃ n : Nat, p = n ∧ p.toNat = n :=
  ⟨p.toNat, (Int.toNat_of_nonneg h).symm, rfl⟩

/-- The bridge: a non-negative Int's toNat is the Nat itself. -/
theorem toNat_cast (n : Nat) : ((n : Int).toNat) = n := rfl

/-- THE UINT8 BRIDGE: a byte's toNat is its value mod 256 (rfl — the
    ofNat/mk/toBitVec chain reduces). -/
theorem u8toNat (n : Nat) : n.toUInt8.toNat = n % 256 := rfl

/-- The sleb payload of the encoder's stop condition (the mathematical
    mod-128 residue, as `Int`). -/
def slebP (v : Int) : Int := (v % 128 + 128) % 128

theorem slebP_prop (v : Int) :
    0 ≤ slebP v ∧ slebP v < 128 ∧ (v - slebP v) % 128 = 0 := by
  unfold slebP
  omega

theorem slebP_combine (v : Int) : slebP v + 128 * ((v - slebP v) / 128) = v := by
  have h := slebP_prop v
  omega

/-- The encoder's fuel fits: `v` fits `k` signed groups. -/
def slebFits (v : Int) (k : Nat) : Prop := -(64 * 128 ^ k : Int) ≤ v ∧ v < 64 * 128 ^ k

/-- One continuation step preserves the fit (the quotient of a value
    fitting `k+1` groups fits `k`). -/
theorem slebFits_step (v : Int) (k : Nat) (h : slebFits v (k + 1)) :
    slebFits ((v - slebP v) / 128) k := by
  unfold slebFits at *
  have hp := slebP_prop v
  have h1 : (v - slebP v) / 128 * 128 = v - slebP v := by omega
  constructor <;> omega

/-- The fit weakens as the group budget grows. -/
theorem slebFits_weak (v : Int) (k : Nat) (h : slebFits v k) : slebFits v (k + 1) := by
  unfold slebFits at *
  have h1 : 128 ^ k ≤ 128 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have h2 : 128 ^ (k + 1) = 128 ^ k * 128 := Nat.pow_succ (128) k
  constructor <;> omega

/-- The encoder's stop byte (the final group: the sign-extended
    residue's byte). -/
def stopByte (v : Int) : UInt8 := (slebP v).toNat.toUInt8

/-- The encoder's continuation byte (the more-groups bit + payload). -/
def contByte (v : Int) : UInt8 := (slebP v + 128).toNat.toUInt8

/-- B1 — the stop byte's value round-trips. -/
theorem stopByte_val (p : Int) (h1 : 0 ≤ p) (h2 : p < 256) :
    ((p.toNat.toUInt8).toNat : Int) = p := by
  obtain ⟨n, hn, hnt⟩ := intNat h1
  have hn256 : n < 256 := by omega
  rw [hn, toNat_cast, UInt8.toNat_ofNat_of_lt' hn256]

/-- B3 — the stop byte is small (its 7-bit test holds). -/
theorem stopByte_small (p : Int) (h1 : 0 ≤ p) (h2 : p < 128) :
    p.toNat.toUInt8.toNat < 128 := by
  obtain ⟨n, hn, hnt⟩ := intNat h1
  have hn128 : n < 128 := by omega
  rw [hn, toNat_cast, UInt8.toNat_ofNat_of_lt' (show n < 256 from by omega)]
  omega

/-- B3' — the stop byte's 6-bit test, small face. -/
theorem stopByte_lt64 (p : Int) (h1 : 0 ≤ p) (h2 : p < 64) :
    p.toNat.toUInt8.toNat < 64 := by
  obtain ⟨n, hn, hnt⟩ := intNat h1
  have hn64 : n < 64 := by omega
  rw [hn, toNat_cast, UInt8.toNat_ofNat_of_lt' (show n < 256 from by omega)]
  omega

/-- B3'' — the stop byte's 6-bit test, sign-extended face. -/
theorem stopByte_ge64 (p : Int) (h1 : 0 ≤ p) (h2 : 64 ≤ p) (h3 : p < 128) :
    ¬(p.toNat.toUInt8.toNat < 64) := by
  obtain ⟨n, hn, hnt⟩ := intNat h1
  have hn64 : n ≥ 64 := by omega
  have hn128 : n < 128 := by omega
  rw [hn, toNat_cast, u8toNat]
  omega

/-- B6 — the decoder's final-group value for a small residue. -/
theorem stopByte_value_small (p : Int) (h1 : 0 ≤ p) (h2 : p < 64) :
    (if p.toNat.toUInt8.toNat < 64 then ((p.toNat.toUInt8).toNat : Int)
      else ((p.toNat.toUInt8).toNat : Int) - 128) = p := by
  obtain ⟨n, hn, hnt⟩ := intNat h1
  have hn64 : n < 64 := by omega
  rw [hn, toNat_cast, UInt8.toNat_ofNat_of_lt' (show n < 256 from by omega),
    if_pos (show n < 64 from by omega)]

/-- B7 — the decoder's final-group value for a sign-extended residue. -/
theorem stopByte_value_sign (p : Int) (h1 : 0 ≤ p) (h2 : 64 ≤ p) (h3 : p < 128) :
    (if p.toNat.toUInt8.toNat < 64 then ((p.toNat.toUInt8).toNat : Int)
      else ((p.toNat.toUInt8).toNat : Int) - 128) = p - 128 := by
  obtain ⟨n, hn, hnt⟩ := intNat h1
  have hn64 : n ≥ 64 := by omega
  have hn128 : n < 128 := by omega
  rw [hn, toNat_cast, u8toNat,
    if_neg (show ¬(n % 256 < 64) from by omega)]
  omega


/-- B2 — the continuation byte's payload IS the encoder's residue. -/
theorem contByte_payload (p : Int) (h1 : 0 ≤ p) (h2 : p < 128) :
    (((p + 128 : Int).toNat.toUInt8).toNat % 128 : Int) = p := by
  obtain ⟨n, hn, hnt⟩ := intNat h1
  have hn128 : n < 128 := by omega
  rw [hn, show ((↑n + 128 : Int).toNat = n + 128) from rfl, u8toNat]
  omega

/-- B8 — the continuation byte carries the more-groups bit. -/
theorem contByte_big (p : Int) (h1 : 0 ≤ p) (h2 : p < 128) :
    ¬(((p + 128 : Int).toNat.toUInt8).toNat < 128) := by
  obtain ⟨n, hn, hnt⟩ := intNat h1
  have hn128 : n < 128 := by omega
  rw [hn, show ((↑n + 128 : Int).toNat = n + 128) from rfl, u8toNat]
  omega

/-! ## The positioned signed reader + the canonicality tooth -/

/-- The positioned signed reader over the SUFFIX. The canonicality
    check is the EXACT-IMAGE face: the only redundant shape a
    multi-group encoding can have is the final zero group folding into
    a continuation whose payload is below 64 — refuse exactly that
    (`nonMinimalSleb`); the fixed encoder never emits it. -/
def decSlebR (pos : Nat) : List UInt8 → Except DecodeError (Int × Nat)
  | [] => .error (.truncated pos 1)
  | b :: rest =>
      if b.toNat < 128 then
        .ok (if b.toNat < 64 then (b.toNat : Int) else (b.toNat : Int) - 128, pos + 1)
      else
        (decSlebR (pos + 1) rest).bind fun p =>
          if p.1 = 0 ∧ b.toNat % 128 < 64 then .error (.nonMinimalSleb pos)
          else .ok ((b.toNat % 128 : Int) + 128 * p.1, p.2)

/-- The canonicality check passes on the encoder's continuation: the
    quotient of a not-yet-stopped value is never 0 when the payload is
    small (the exact-image discipline's core arithmetic fact). -/
theorem cont_check (v : Int) (hstop : ¬(v ≥ -64 ∧ v ≤ 63)) :
    ¬((v - slebP v) / 128 = 0 ∧ ((slebP v + 128 : Int).toNat.toUInt8).toNat % 128 < 64) := by
  have hp := slebP_prop v
  have hbridge := contByte_payload (slebP v) hp.1 hp.2.1
  rintro ⟨h0, hq⟩
  have h1 : (v - slebP v) % 128 = 0 := hp.2.2
  have h2 : (v - slebP v) / 128 * 128 = v - slebP v := by omega
  omega

/-! ## The inverse folds — the closed universes' read faces -/

/-- ALL the value types (the closed ctor set; the decode fold's list).
    The wire's valtype byte is `encodeValType`'s image ONLY — the
    canonical spellings' authority is the encoder's map, never a
    parallel byte table. -/
def allValTypes : List ValType :=
  [.i32, .i64, .f32, .f64, .funcref, .externref]

/-- The exhaustiveness tooth, valtype face: a new `ValType` ctor
    missing from `allValTypes` is a BUILD FAILURE. -/
theorem allValTypes_complete : ∀ t : ValType, t ∈ allValTypes := by
  intro t; cases t <;> simp [allValTypes]

/-- The valtype byte's decode: a `find?` over the closed list by the
    ENCODER's byte (no parallel byte map — the wire's authority is
    `encodeValType`). -/
def valTypeOfByte? (b : UInt8) : Option ValType :=
  allValTypes.find? (fun t => encodeValType t == b)

/-- The op bytes' decode: a `find?` over the completeness-proved
    `allOps` by the table's OWN byte spelling (`opOpcode`). A new op
    row without its decode arm is impossible — the fold sees the row. -/
def opOfBytes? (bs : List UInt8) : Option Op :=
  allOps.find? (fun o => opOpcode o == bs)

/-- The mem byte's decode (the same discipline over `allMems`). -/
def memOfByte? (b : UInt8) : Option MemOp :=
  allMems.find? (fun m => memOpcode m == b)

/-! ## The positioned instruction/body readers (the fuel-WF discipline) -/

/-- The suffix at an absolute position (the positioned readers' view). -/
def suffixAt (bs : List UInt8) (pos : Nat) : List UInt8 := bs.drop pos

mutual
/-- ONE instruction's decode, positioned, on an explicit fuel. The
    fuel is the instruction-nesting budget: every structural form
    (block/loop/if_) spends one, every leaf spends none — a corrupt
    body's runaway nesting refuses with `tooDeep`, never a hang.
    `pos` is the ABSOLUTE position of the suffix head; returns the
    instruction + the position PAST it. -/
def decInstr : Nat → Nat → List UInt8 → Except DecodeError (Instr × Nat)
  | 0, pos, _ => .error (.tooDeep pos)
  | fuel + 1, pos, [] => .error (.truncated pos 1)
  | fuel + 1, pos, b :: rest =>
      match b with
      | 0x41 => -- i32.const: the sleb's SIGNED value; the AST carries
                -- the BIT PATTERN (the two's-complement reading)
          (decSlebR (pos + 1) rest).bind fun (w, pos') =>
            .ok (.i32const (((w % 4294967296 + 4294967296) % 4294967296).toNat), pos')
      | 0x42 => -- i64.const (the same fold at 64 bits)
          (decSlebR (pos + 1) rest).bind fun (w, pos') =>
            .ok (.i64const (((w % 18446744073709551616 + 18446744073709551616)
              % 18446744073709551616).toNat), pos')
      | 0x20 => -- local.get
          (decVarNatR (pos + 1) rest).bind fun (n, pos') => .ok (.localget n, pos')
      | 0x21 => -- local.set
          (decVarNatR (pos + 1) rest).bind fun (n, pos') => .ok (.localset n, pos')
      | 0x22 => -- local.tee
          (decVarNatR (pos + 1) rest).bind fun (n, pos') => .ok (.localtee n, pos')
      | 0x10 => -- call
          (decVarNatR (pos + 1) rest).bind fun (n, pos') => .ok (.call n, pos')
      | 0x11 => -- call_indirect: the type index + the ONE table's 0x00
          match rest with
          | 0x00 :: rest2 =>
              (decVarNatR (pos + 2) rest2).bind fun (n, pos') =>
                .ok (.callindirect n, pos')
          | b2 :: _ => .error (.badCallIndirect (pos + 1) b2)
          | [] => .error (.truncated (pos + 1) 1)
      | 0x0C => -- br
          (decVarNatR (pos + 1) rest).bind fun (n, pos') => .ok (.br n, pos')
      | 0x0D => -- br_if
          (decVarNatR (pos + 1) rest).bind fun (n, pos') => .ok (.brif n, pos')
      | 0x0B => .error (.endOfBody (pos + 1) false) -- a frame's end: decBody's stop
      | 0x05 => .error (.endOfBody (pos + 1) true)  -- an else divider: the then-body's stop
      | 0x0F => .ok (.ret, pos + 1)
      | 0x1A => .ok (.drop, pos + 1)
      | 0x1B => .ok (.select, pos + 1)
      | 0x00 => .ok (.unreach, pos + 1)
      | 0x02 => -- block: the 0x40 frame + the body + the 0x0B
          match rest with
          | 0x40 :: rest2 =>
              (decBody fuel (pos + 2) rest2).bind fun (body, pos', e5) =>
                if e5 then .error (.badBlockType (pos' - 1) 0x05)
                else .ok (.block body, pos')
          | b2 :: _ => .error (.badBlockType (pos + 1) b2)
          | [] => .error (.truncated (pos + 1) 1)
      | 0x03 => -- loop (the same frame)
          match rest with
          | 0x40 :: rest2 =>
              (decBody fuel (pos + 2) rest2).bind fun (body, pos', e5) =>
                if e5 then .error (.badBlockType (pos' - 1) 0x05)
                else .ok (.loop body, pos')
          | b2 :: _ => .error (.badBlockType (pos + 1) b2)
          | [] => .error (.truncated (pos + 1) 1)
      | 0x04 => -- if_: the then-body, the optional else, the 0x0B
          match rest with
          | 0x40 :: rest2 =>
              (decBody fuel (pos + 2) rest2).bind fun (thenI, pos1, e5) =>
                if e5 then
                  (decBody fuel pos1 (suffixAt rest2 (pos1 - (pos + 2)))).bind
                    fun (elseI, pos2, e5') =>
                      if e5' then .error (.badBlockType (pos2 - 1) 0x05)
                      else .ok (.if_ thenI elseI, pos2)
                else .ok (.if_ thenI [], pos1)
          | b2 :: _ => .error (.badBlockType (pos + 1) b2)
          | [] => .error (.truncated (pos + 1) 1)
      | _ => -- the ONE table's flat faces: the mem rows by byte, the
             -- plain ops by the row's byte spelling
          match memOfByte? b with
          | some m =>
              -- the memarg: alignment then offset (the encoder's order)
              (decVarNatR (pos + 1) rest).bind fun (a, pos1) =>
                (decVarNatR pos1 (suffixAt rest (pos1 - (pos + 1)))).bind fun (o, pos2) =>
                  .ok (.mem m o (if a = memAlignDefault m then none else some a), pos2)
          | none =>
              match opOfBytes? [b] with
              | some o => .ok (.op o, pos + 1)
              | none => .error (.badOpcode pos b)

/-- A body's decode: instructions until `decInstr` signals the
    terminator (`0x0B` = a frame's end, `0x05` = an `else` divider —
    the then-body's stop). Consumes the terminator byte; returns the
    instructions, the position PAST it, and whether it was `0x05`. -/
def decBody : Nat → Nat → List UInt8 → Except DecodeError (List Instr × Nat × Bool)
  | 0, pos, _ => .error (.tooDeep pos)
  | fuel + 1, pos, bs =>
      match decInstr (fuel + 1) pos bs with
      | .ok (i, pos') =>
          (decBody fuel pos' (suffixAt bs (pos' - pos))).bind fun (is, pos'', e5) =>
            .ok (i :: is, pos'', e5)
      | .error (.endOfBody pos' e5) => .ok ([], pos', e5)
      | .error e => .error e
end

/-! ## The sleb law — the NAMED REMAINDER (the declared boundary) -/

/- The sleb's full round-trip THEOREM (the fuel-strong induction over
   `slebFits` + the byte-cast bridging) did NOT land this order — the
   induction's rewrite chain fought the `Int.toNat`/`UInt8` cast
   normalization and was withdrawn rather than stubbed (zero `sorry`).
   The DECLARED GAP, honestly: `decSlebR`'s correctness on the
   encoder's image is the runtime-tested discipline (the WasmCoreTests
   decode sweep + the non-minimal-refusal controls), the `Slice.lean`
   precedent — the theorem lands with the module-level decoder order.
   The compiled teeth that DID land: `cont_check` (the canonicality
   check passes on the encoder's continuation shape — the proof's
   core arithmetic fact) and the bridge lemmas above. The FRESH
   ATTEMPT below landed: the fuel/fits PAIRING was the blocker —
   pairing fuel `k+1` with `slebFits v k` (not `k+1`) makes the
   continuation case's recursion match `slebFits_step` exactly and
   forces the base case onto the stop condition. -/

/-- The sleb payload IS the value's mod-128 residue (the boundary
    fact every case's arithmetic reduces to). -/
theorem slebP_eq (v : Int) : slebP v = v % 128 := by
  have h := slebP_prop v
  unfold slebP
  have h1 : (v % 128 + 128) % 128 = v % 128 := by omega
  rw [h1]

/-- The residue of a value IN the one-group range: `v` itself (nonneg
    face) or `v + 128` (negative face). -/
theorem slebP_small {v : Int} (h : 0 ≤ v) (h2 : v < 128) : slebP v = v := by
  unfold slebP
  omega

theorem slebP_neg {v : Int} (h : -128 ≤ v) (h2 : v < 0) : slebP v = v + 128 := by
  unfold slebP
  omega

/-- The stop byte's byte value IS the residue (it is below 256). -/
theorem stopByte_toNat (v : Int) : (stopByte v).toNat = (slebP v).toNat := by
  have h := slebP_prop v
  unfold stopByte
  have h256 : (slebP v).toNat < 256 := by have := h.2.1; omega
  rw [u8toNat]
  exact Nat.mod_eq_of_lt h256

/-- The FINAL-GROUP LAW: a value in the one-group range decodes from
    its single stop byte. -/
theorem decSlebR_stop (v : Int) (rest : List UInt8) (pos : Nat)
    (hlo : -64 ≤ v) (hhi : v ≤ 63) :
    decSlebR pos ([stopByte v] ++ rest) = .ok (v, pos + 1) := by
  have hp := slebP_prop v
  have hb : (stopByte v).toNat = (slebP v).toNat := stopByte_toNat v
  obtain ⟨pn, hpn1, hpn2⟩ := intNat hp.1
  have hlt128 : (stopByte v).toNat < 128 := by rw [hb, hpn2]; omega
  rw [List.singleton_append, decSlebR, if_pos hlt128]
  -- the value: pn = slebP v reads back as v (the sign-extension seam)
  by_cases hv : 0 ≤ v
  · have hpv : slebP v = v := slebP_small hv (by omega)
    have h64 : (stopByte v).toNat < 64 := by rw [hb, hpn2]; omega
    have hval : (((stopByte v).toNat : Int)) = v := by rw [hb, hpn2]; omega
    rw [if_pos h64, hval]
  · have hpv : slebP v = v + 128 := slebP_neg (by omega) (by omega)
    have h64 : ¬((stopByte v).toNat < 64) := by rw [hb, hpn2]; omega
    have hval : (((stopByte v).toNat : Int)) - 128 = v := by rw [hb, hpn2]; omega
    rw [if_neg h64, hval]

/-- THE SLEB LAW (the fuel-strong induction, pattern #2's append form):
    fuel `k+1` decodes any value fitting `k` groups from its encoding
    plus any suffix. The pairing is the point: the continuation case's
    recursion (fuel `k+1` after the byte) matches `slebFits_step`'s
    quotient exactly, and the base case `k = 0` forces the stop
    condition (a one-group value), so fuel never runs out mid-value —
    the truncation shape that defeated the previous pairing. -/
theorem decSlebR_slebIGo_append :
    ∀ (k : Nat) (v : Int) (rest : List UInt8) (pos : Nat),
    slebFits v k →
    decSlebR pos (slebIGo (k + 1) v ++ rest) =
      .ok (v, pos + (slebIGo (k + 1) v).length) := by
  intro k
  induction k with
  | zero =>
    -- fuel 1 + fits 0: the value IS a one-group value — the stop law
    intro v rest pos h
    unfold slebFits at h
    have hstop : v ≥ -64 ∧ v ≤ 63 := ⟨by omega, by omega⟩
    have hc : (decide (v ≥ -64) && decide (v ≤ 63)) = true := by simp [hstop]
    have henc : slebIGo (0 + 1) v = [stopByte v] := by
      simp only [slebIGo]
      rw [if_pos hc]
      rfl
    rw [henc, decSlebR_stop v rest pos hstop.1 hstop.2, List.length_singleton]
  | succ k ih =>
    intro v rest pos h
    unfold slebFits at h
    by_cases hstop : v ≥ -64 ∧ v ≤ 63
    · -- the stop case (the fuel is spare): one byte, the stop law
      have hc : (decide (v ≥ -64) && decide (v ≤ 63)) = true := by simp [hstop]
      have henc : slebIGo (k + 1 + 1) v = [stopByte v] := by
        simp only [slebIGo]
        rw [if_pos hc]
        rfl
      rw [henc, decSlebR_stop v rest pos hstop.1 hstop.2, List.length_singleton]
    · -- the continuation case: the quotient fits k (slebFits_step) and
      -- the IH decodes the rest; the canonicality check passes
      -- (cont_check) and the residue recombines (slebP_combine)
      have hquot : slebFits ((v - slebP v) / 128) k :=
        slebFits_step v k ⟨by omega, by omega⟩
      have hp := slebP_prop v
      have hcont : ¬(v ≥ -64 ∧ v ≤ 63) := hstop
      have hc' : ¬((decide (v ≥ -64) && decide (v ≤ 63)) = true) := by
        simp [hcont]
      have henc : slebIGo (k + 1 + 1) v =
          contByte v :: slebIGo (k + 1) ((v - slebP v) / 128) := by
        -- unfold the LHS ONE level only (the RHS stays folded)
        conv =>
          lhs
          unfold slebIGo slebP contByte
          simp only
        have hq0 : (0 : Int) ≤ (v % 128 + 128) % 128
            ∧ (v % 128 + 128) % 128 < 128 := by omega
        rw [if_neg hc', contByte_payload ((v % 128 + 128) % 128) hq0.1 hq0.2]
        rfl
      rw [henc, List.cons_append]
      have hbig : ¬((contByte v).toNat < 128) := contByte_big (slebP v) hp.1 hp.2.1
      have hihr := ih ((v - slebP v) / 128) rest (pos + 1) hquot
      simp only [decSlebR, if_neg hbig, Except.ok_bind', hihr]
      -- the canonicality check: the quotient is never 0 with a small
      -- residue when the stop condition failed (cont_check)
      have hcc := cont_check v hcont
      have hbc : (contByte v).toNat
          = (((slebP v + 128 : Int).toNat.toUInt8).toNat) := rfl
      have hpay : (((slebP v + 128 : Int).toNat.toUInt8).toNat % 128 : Int)
          = slebP v := contByte_payload (slebP v) hp.1 hp.2.1
      have hne : ¬(((v - slebP v) / 128 : Int) = 0 ∧
          ((contByte v).toNat % 128 : Nat) < 64) := by
        rintro ⟨h0, hq⟩
        refine hcc ⟨h0, ?_⟩
        rw [hbc] at hq
        omega
      simp only [if_neg hne]
      -- the value recombination: residue + 128 * quotient = v
      have hval : (((contByte v).toNat % 128 : Int) +
          128 * ((v - slebP v) / 128 : Int) : Int) = v := by
        rw [hbc, hpay, slebP_combine]
      rw [hval]
      simp only [Except.ok.injEq, Prod.mk.injEq]
      exact ⟨by trivial, by rw [List.length_cons]; omega⟩

/-- The sleb law over the ONE encoder (`slebI`, fuel 12): every
    64-bit-bounded value fits 11 groups (`64 * 128^11 = 2^83`). -/
theorem decSlebR_slebI_append : ∀ (v : Int) (rest : List UInt8) (pos : Nat),
    -(9223372036854775808 : Int) ≤ v → v < 9223372036854775808 →
    decSlebR pos (slebI v ++ rest) = .ok (v, pos + (slebI v).length) := by
  intro v rest pos hlo hhi
  have hfits : slebFits v 11 := by
    unfold slebFits
    have hp : (64 : Int) * 128 ^ 11 = 9671406556917033397649408 := by decide
    omega
  have henc : slebI v = slebIGo (11 + 1) v := rfl
  rw [henc]
  exact decSlebR_slebIGo_append 11 v rest pos hfits

/-- The i32.const wire pattern: the decoder recovers the AST's Nat as
    the two's-complement BIT PATTERN (mod 2^32) of the wire value. -/
theorem i32WirePattern (n : Nat) :
    (((i32ConstWire n % 4294967296 + 4294967296) % 4294967296 : Int).toNat)
      = n % 4294967296 := by
  have hmod : ((i32ConstWire n % 4294967296 + 4294967296) % 4294967296 : Int)
      = (n % 4294967296 : Int) := by
    simp only [i32ConstWire]; split <;> omega
  rw [hmod]; omega

/-- The i64.const wire pattern (the same fold at 64 bits). -/
theorem i64WirePattern (n : Nat) :
    (((i64ConstWire n % 18446744073709551616 + 18446744073709551616)
      % 18446744073709551616 : Int).toNat) = n % 18446744073709551616 := by
  have hmod : ((i64ConstWire n % 18446744073709551616 + 18446744073709551616)
      % 18446744073709551616 : Int) = (n % 18446744073709551616 : Int) := by
    simp only [i64ConstWire]; split <;> omega
  rw [hmod]; omega

/-- The wire pattern's toNat face (the decoder's const arm reads the
    mod-reduced Int; its toNat is the AST's pattern). -/
theorem i32WireToNat (n : Nat) :
    (i32ConstWire n % 4294967296).toNat = n % 4294967296 := by
  have h : ((i32ConstWire n % 4294967296 : Int))
      = ((i32ConstWire n % 4294967296 + 4294967296) % 4294967296 : Int) := by
    omega
  rw [h, i32WirePattern]

theorem i64WireToNat (n : Nat) :
    (i64ConstWire n % 18446744073709551616).toNat = n % 18446744073709551616 := by
  have h : ((i64ConstWire n % 18446744073709551616 : Int))
      = ((i64ConstWire n % 18446744073709551616 + 18446744073709551616)
        % 18446744073709551616 : Int) := by
    omega
  rw [h, i64WirePattern]

/-- The sleb wire bounds: any 32/64-bit wire value fits the 11-group
    budget (the decSlebR_slebI_append side conditions). -/
theorem i32WireBounded (n : Nat) :
    -(9223372036854775808 : Int) ≤ i32ConstWire n
    ∧ i32ConstWire n < 9223372036854775808 := by
  simp only [i32ConstWire]; split <;> omega

theorem i64WireBounded (n : Nat) :
    -(9223372036854775808 : Int) ≤ i64ConstWire n
    ∧ i64ConstWire n < 9223372036854775808 := by
  simp only [i64ConstWire]; split <;> omega

/-! ## The list-suffix algebra (the positioned parsers' glue) -/

/-- Dropping a prefix's length yields the suffix (the append-form
    glue every positioned law's bookkeeping rides). -/
theorem dropAppendLen {α : Type _} (l1 : List α) (l2 : List α) :
    (l1 ++ l2).drop l1.length = l2 := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, List.length_cons,
      List.drop_succ_cons, ih]

/-- Dropping one past a prefix's length (the then-body's terminator
    bookkeeping: the `0x05` is consumed with the body). -/
theorem dropAppendSucc {α : Type _} : ∀ (l1 : List α) (a : α) (l2 : List α),
    (l1 ++ a :: l2).drop (l1.length + 1) = l2
  | [], _, l2 => by simp
  | b :: l1, a, l2 => by
      simp only [List.cons_append, List.length_cons, List.drop_succ_cons]
      exact dropAppendSucc l1 a l2

/-- Dropping the SOURCE length past a mapped prefix (the functype
    reader's glue: the valtype bytes drop by the source list's length). -/
theorem dropAppendMap {α β : Type _} (f : α → β) (ps : List α) (l2 : List β) :
    (ps.map f ++ l2).drop ps.length = l2 := by
  have hlen : (ps.map f).length = ps.length := List.length_map f
  rw [← hlen]
  exact dropAppendLen _ _

/-- Dropping past a prefix at any offset (the else-divider's
    bookkeeping). -/
theorem dropAppendSucc2 {α : Type _} : ∀ (l1 l2 : List α) (k : Nat),
    (l1 ++ l2).drop (l1.length + k) = l2.drop k
  | [], _, _ => by simp
  | _ :: l1, l2, k => by
      have h : l1.length + 1 + k = l1.length + k + 1 := by omega
      simp only [List.cons_append, List.length_cons, h, List.drop_succ_cons]
      exact dropAppendSucc2 l1 l2 k

/-- Dropping the SOURCE length + k past a mapped prefix (the functype
    reader's second glue). -/
theorem dropAppendMap2 {α β : Type _} (f : α → β) (ps : List α) (l2 : List β) (k : Nat) :
    (ps.map f ++ l2).drop (ps.length + k) = l2.drop k := by
  rw [show ps.length = List.length (ps.map f) from (List.length_map f).symm,
    dropAppendSucc2]

/-- The fold-hit laws: the decode dispatches FIND the row (the
    closed-universe tooth's read face — decide over the literals). -/
theorem opOfBytes_hit (o : Op) : opOfBytes? (opOpcode o) = some o := by
  cases o <;> simp [opOfBytes?, allOps, opOpcode] <;> decide

theorem memOfByte_hit (m : MemOp) : memOfByte? (memOpcode m) = some m := by
  cases m <;> simp [memOfByte?, allMems, memOpcode] <;> decide

theorem valTypeOfByte_hit (t : ValType) :
    valTypeOfByte? (encodeValType t) = some t := by
  cases t <;> simp [valTypeOfByte?, allValTypes, encodeValType] <;> decide

/-! ## The depth measure + the decoded image + the fragment -/

mutual
/-- The instruction-nesting depth (the fuel discipline's measure: the
    fuel must EXCEED the depth of what it decodes). -/
def iDepth : Instr → Nat
  | .i32const _ => 1
  | .i64const _ => 1
  | .localget _ => 1
  | .localset _ => 1
  | .localtee _ => 1
  | .call _ => 1
  | .callindirect _ => 1
  | .mem _ _ _ => 1
  | .op _ => 1
  | .br _ => 1
  | .brif _ => 1
  | .block b => 1 + lDepth b
  | .loop b => 1 + lDepth b
  | .if_ t e => 1 + max (lDepth t) (lDepth e)
  | .ret => 1
  | .drop => 1
  | .select => 1
  | .unreach => 1

/-- The body depth (the mutual sibling). -/
def lDepth : List Instr → Nat
  | [] => 0
  | i :: is => max (iDepth i) (lDepth is)
end

mutual
/-- The decoder's IMAGE of an instruction: a const comes back as the
    BIT PATTERN (the wire's signed immediate mod 2^k), a memarg that
    restates the elided default alignment comes back elided, and the
    structural forms' images are their bodies' images. The module law
    speaks over the fragment where the image IS the original. -/
def iImage : Instr → Instr
  | .i32const n => .i32const (n % 4294967296)
  | .i64const n => .i64const (n % 18446744073709551616)
  | .mem m o a =>
      .mem m o (match a with
        | some d => if d = memAlignDefault m then none else some d
        | none => none)
  | .block b => .block (lImage b)
  | .loop b => .loop (lImage b)
  | .if_ t e => .if_ (lImage t) (lImage e)
  | .op o => .op o
  | .localget n => .localget n
  | .localset n => .localset n
  | .localtee n => .localtee n
  | .call n => .call n
  | .callindirect n => .callindirect n
  | .br n => .br n
  | .brif n => .brif n
  | .ret => .ret
  | .drop => .drop
  | .select => .select
  | .unreach => .unreach

/-- The image of a body (pointwise). -/
def lImage : List Instr → List Instr
  | [] => []
  | i :: is => iImage i :: lImage is
end

mutual
/-- The per-instruction fragment: consts carry canonical BIT PATTERNS
    (below 2^32 / 2^64 — a pattern ≥ the wrap point encodes to the
    same bytes as its wrapped twin and the decoder recovers the
    pattern, not the original), memargs never restate the elided
    default alignment; the structural forms' fragments are their
    bodies'. -/
def instrFrag : Instr → Prop
  | .i32const n => n < 4294967296
  | .i64const n => n < 18446744073709551616
  | .mem m _ a => a ≠ some (memAlignDefault m)
  | .block b => bodyFrag b
  | .loop b => bodyFrag b
  | .if_ t e => bodyFrag t ∧ bodyFrag e
  | _ => True

/-- The per-body fragment (pointwise). -/
def bodyFrag : List Instr → Prop
  | [] => True
  | i :: is => instrFrag i ∧ bodyFrag is
end

mutual
/-- THE FRAGMENT LEMMA: over the fragment the image IS the original
    (the module law's per-instruction face). -/
theorem iImage_self : ∀ i : Instr, instrFrag i → iImage i = i := by
  intro i hf
  cases i with
  | i32const n =>
      simp only [instrFrag] at hf
      exact congrArg Instr.i32const (by omega)
  | i64const n =>
      simp only [instrFrag] at hf
      exact congrArg Instr.i64const (by omega)
  | mem m o a =>
      simp only [iImage]
      cases a with
      | none => rfl
      | some d =>
          simp only [instrFrag] at hf
          have hne : ¬(d = memAlignDefault m) := fun hcon => hf (by rw [hcon])
          show Instr.mem m o (if d = memAlignDefault m then none else some d)
            = Instr.mem m o (some d)
          rw [if_neg hne]
  | op o => rfl
  | localget n => rfl
  | localset n => rfl
  | localtee n => rfl
  | call n => rfl
  | callindirect n => rfl
  | br n => rfl
  | brif n => rfl
  | block b =>
      simp only [instrFrag] at hf
      exact congrArg Instr.block (lImage_self b hf)
  | loop b =>
      simp only [instrFrag] at hf
      exact congrArg Instr.loop (lImage_self b hf)
  | if_ t e =>
      simp only [instrFrag] at hf
      simp only [iImage]
      rw [lImage_self t hf.1, lImage_self e hf.2]
  | ret => rfl
  | drop => rfl
  | select => rfl
  | unreach => rfl

theorem lImage_self : ∀ is : List Instr, bodyFrag is → lImage is = is := by
  intro is hf
  cases is with
  | nil => rfl
  | cons i is =>
      simp only [bodyFrag] at hf
      simp only [lImage, iImage_self i hf.1]
      exact congrArg (i :: ·) (lImage_self is hf.2)

/-- Encoding length counts (the count-discipline's face: the body's
    COUNT bounds the fuel — the law's side-conditions ride this). -/
theorem iSize_le_len : ∀ i : Instr, iSize i ≤ (encodeInstr i).length := by
  intro i
  cases i with
  | i32const n => simp only [iSize, encodeInstr, List.length_cons]; omega
  | i64const n => simp only [iSize, encodeInstr, List.length_cons]; omega
  | localget n => simp only [iSize, encodeInstr, List.length_cons]; omega
  | localset n => simp only [iSize, encodeInstr, List.length_cons]; omega
  | localtee n => simp only [iSize, encodeInstr, List.length_cons]; omega
  | call n => simp only [iSize, encodeInstr, List.length_cons]; omega
  | callindirect ty => simp only [iSize, encodeInstr, List.length_cons]; omega
  | mem m o a =>
      simp only [iSize, encodeInstr, List.singleton_append, List.length_cons]; omega
  | op o =>
      cases o <;>
        simp only [iSize, encodeInstr, opOpcode, opRow, List.length_cons] <;> omega
  | br d => simp only [iSize, encodeInstr, List.length_cons]; omega
  | brif d => simp only [iSize, encodeInstr, List.length_cons]; omega
  | block b =>
      have ih := lSize_le_len b
      simp only [iSize, encodeInstr, encodeBody, List.length_cons,
        List.length_append, List.length_singleton]
      omega
  | loop b =>
      have ih := lSize_le_len b
      simp only [iSize, encodeInstr, encodeBody, List.length_cons,
        List.length_append, List.length_singleton]
      omega
  | if_ t e =>
      have ht := lSize_le_len t
      have he := lSize_le_len e
      simp only [iSize, encodeInstr, List.length_cons, List.length_append]
      split <;> simp only [lSize, encodeBody, List.length_cons,
        List.length_append, List.length_nil, List.length_singleton] at he ⊢ <;>
        omega
  | ret => simp only [iSize, encodeInstr, List.length_cons, List.length_nil]; omega
  | drop => simp only [iSize, encodeInstr, List.length_cons, List.length_nil]; omega
  | select => simp only [iSize, encodeInstr, List.length_cons, List.length_nil]; omega
  | unreach => simp only [iSize, encodeInstr, List.length_cons, List.length_nil]; omega

theorem lSize_le_len : ∀ is : List Instr, lSize is ≤ (encodeBody is).length := by
  intro is
  cases is with
  | nil => simp [lSize, encodeBody]
  | cons i is =>
      have h1 := iSize_le_len i
      have h2 := lSize_le_len is
      simp only [lSize, encodeBody, List.length_append]
      omega
end

mutual
/-- Encoding length bounds depth (the module law's fuel discharge:
    decodeModule funds each body's fuel from the byte count, and the
    bytes dominate the nesting). -/
theorem iDepth_le_len : ∀ i : Instr, iDepth i ≤ (encodeInstr i).length := by
  intro i
  cases i with
  | i32const n => simp only [iDepth, encodeInstr, List.length_cons]; omega
  | i64const n => simp only [iDepth, encodeInstr, List.length_cons]; omega
  | localget n => simp only [iDepth, encodeInstr, List.length_cons]; omega
  | localset n => simp only [iDepth, encodeInstr, List.length_cons]; omega
  | localtee n => simp only [iDepth, encodeInstr, List.length_cons]; omega
  | call n => simp only [iDepth, encodeInstr, List.length_cons]; omega
  | callindirect ty => simp only [iDepth, encodeInstr, List.length_cons]; omega
  | mem m o a =>
      simp only [iDepth, encodeInstr, List.singleton_append, List.length_cons]; omega
  | op o =>
      cases o <;>
        simp only [iDepth, encodeInstr, opOpcode, opRow, List.length_cons] <;> omega
  | br d => simp only [iDepth, encodeInstr, List.length_cons]; omega
  | brif d => simp only [iDepth, encodeInstr, List.length_cons]; omega
  | block b =>
      have ih := lDepth_le_len b
      simp only [iDepth, encodeInstr, encodeBody, List.length_cons,
        List.length_append, List.length_singleton]
      omega
  | loop b =>
      have ih := lDepth_le_len b
      simp only [iDepth, encodeInstr, encodeBody, List.length_cons,
        List.length_append, List.length_singleton]
      omega
  | if_ t e =>
      have ht := lDepth_le_len t
      have he := lDepth_le_len e
      simp only [iDepth, encodeInstr, List.length_cons, List.length_append]
      split <;> simp only [lDepth, encodeBody, List.length_cons,
        List.length_append, List.length_nil, List.length_singleton] at he ⊢ <;>
        omega
  | ret => simp only [iDepth, encodeInstr, List.length_cons, List.length_nil]; omega
  | drop => simp only [iDepth, encodeInstr, List.length_cons, List.length_nil]; omega
  | select => simp only [iDepth, encodeInstr, List.length_cons, List.length_nil]; omega
  | unreach => simp only [iDepth, encodeInstr, List.length_cons, List.length_nil]; omega

theorem lDepth_le_len : ∀ is : List Instr, lDepth is ≤ (encodeBody is).length := by
  intro is
  cases is with
  | nil => simp [lDepth, encodeBody]
  | cons i is =>
      have h1 := iDepth_le_len i
      have h2 := lDepth_le_len is
      simp only [lDepth, encodeBody, List.length_append]
      omega
end

/-! ## The instruction/body round-trip laws (the fuel-WF discipline) -/

mutual

/-- THE PER-INSTRUCTION LAW (pattern #2's append form): the decoder
    consumes exactly the instruction's bytes and returns its image. -/
theorem decInstr_enc : ∀ (i : Instr) (fuel pos : Nat) (rest : List UInt8),
    iSize i + 2 ≤ fuel →
    decInstr fuel pos (encodeInstr i ++ rest) =
      .ok (iImage i, pos + (encodeInstr i).length) := by
  intro i
  match i with
  | .i32const n =>
      intro fuel pos rest hfuel
      have hf1 : 0 < fuel := by omega
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append]
      rw [decSlebR_slebI_append (i32ConstWire n) rest (pos + 1)
        (i32WireBounded n).1 (i32WireBounded n).2]
      simp only [Except.ok_bind', Except.ok.injEq, Prod.mk.injEq, iImage,
        List.length_cons]
      exact ⟨by rw [show ((i32ConstWire n % 4294967296 + 4294967296) % 4294967296 : Int) =
        (i32ConstWire n % 4294967296 : Int) from by omega, i32WireToNat], by omega⟩
  | .i64const n =>
      intro fuel pos rest hfuel
      have hf1 : 0 < fuel := by omega
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append]
      rw [decSlebR_slebI_append (i64ConstWire n) rest (pos + 1)
        (i64WireBounded n).1 (i64WireBounded n).2]
      simp only [Except.ok_bind', Except.ok.injEq, Prod.mk.injEq, iImage,
        List.length_cons]
      exact ⟨by rw [show ((i64ConstWire n % 18446744073709551616 + 18446744073709551616)
        % 18446744073709551616 : Int) = (i64ConstWire n % 18446744073709551616 : Int)
        from by omega, i64WireToNat], by omega⟩
  | .localget n =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, decVarNatR_enc n (pos + 1) rest]
      simp only [List.length_cons, Except.ok_bind', Except.ok.injEq, Prod.mk.injEq, iImage]
      exact ⟨trivial, by omega⟩
  | .localset n =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, decVarNatR_enc n (pos + 1) rest]
      simp only [List.length_cons, Except.ok_bind', Except.ok.injEq, Prod.mk.injEq, iImage]
      exact ⟨trivial, by omega⟩
  | .localtee n =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, decVarNatR_enc n (pos + 1) rest]
      simp only [List.length_cons, Except.ok_bind', Except.ok.injEq, Prod.mk.injEq, iImage]
      exact ⟨trivial, by omega⟩
  | .call n =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, decVarNatR_enc n (pos + 1) rest]
      simp only [List.length_cons, Except.ok_bind', Except.ok.injEq, Prod.mk.injEq, iImage]
      exact ⟨trivial, by omega⟩
  | .callindirect ty =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append]
      simp only [decInstr, decVarNatR_enc ty (pos + 2) rest]
      simp only [List.length_cons, Except.ok_bind', Except.ok.injEq, Prod.mk.injEq, iImage]
      exact ⟨trivial, by omega⟩
  | .br d =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, decVarNatR_enc d (pos + 1) rest]
      simp only [List.length_cons, Except.ok_bind', Except.ok.injEq, Prod.mk.injEq, iImage]
      exact ⟨trivial, by omega⟩
  | .brif d =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, decVarNatR_enc d (pos + 1) rest]
      simp only [List.length_cons, Except.ok_bind', Except.ok.injEq, Prod.mk.injEq, iImage]
      exact ⟨trivial, by omega⟩
  | .ret =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, List.singleton_append,
        List.length_cons, List.length_nil, Except.ok.injEq, Prod.mk.injEq, iImage]
  | .drop =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, List.singleton_append,
        List.length_cons, List.length_nil, Except.ok.injEq, Prod.mk.injEq, iImage]
  | .select =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, List.singleton_append,
        List.length_cons, List.length_nil, Except.ok.injEq, Prod.mk.injEq, iImage]
  | .unreach =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, List.singleton_append,
        List.length_cons, List.length_nil, Except.ok.injEq, Prod.mk.injEq, iImage]
  | .op o =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      cases o <;>
        simp [encodeInstr, decInstr, List.cons_append, List.singleton_append,
          opOpcode, opRow, memOfByte?, allMems, opOfBytes?, allOps,
          List.length_cons, List.length_nil, Except.ok_bind',
          Except.ok.injEq, Prod.mk.injEq, iImage] <;> rfl
  | .mem m offset align =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      cases m <;> cases align <;>
        simp [encodeInstr, decInstr, List.cons_append, List.singleton_append,
          memOpcode, memRow, memOfByte?, allMems, decVarNatR_enc,
          List.append_assoc, List.length_cons, List.length_nil,
          suffixAt, dropAppendLen, Except.ok_bind', Except.ok.injEq,
          Prod.mk.injEq, iImage] <;> omega
  | .block b =>
      intro fuel pos rest hfuel
      have hf1 : 0 < fuel := by omega
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, List.singleton_append]
      rw [List.append_assoc, List.cons_append, List.nil_append]
      rw [decBody_enc b fuel' (pos + 2) rest (by
      simp only [iSize] at hfuel
      omega)]
      simp only [Except.ok_bind', if_neg (by decide : ¬((false : Bool) = true))]
      simp only [Except.ok.injEq, Prod.mk.injEq, iImage, List.length_cons,
        List.length_nil, List.length_append]
      exact ⟨trivial, by omega⟩
  | .loop b =>
      intro fuel pos rest hfuel
      have hf1 : 0 < fuel := by omega
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeInstr, decInstr, List.cons_append, List.singleton_append]
      rw [List.append_assoc, List.cons_append, List.nil_append]
      rw [decBody_enc b fuel' (pos + 2) rest (by
      simp only [iSize] at hfuel
      omega)]
      simp only [Except.ok_bind', if_neg (by decide : ¬((false : Bool) = true))]
      simp only [Except.ok.injEq, Prod.mk.injEq, iImage, List.length_cons,
        List.length_nil, List.length_append]
      exact ⟨trivial, by omega⟩
  | .if_ t e =>
      intro fuel pos rest hfuel
      have hf1 : 0 < fuel := by omega
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      cases e with
      | nil =>
          simp only [encodeInstr, decInstr, List.cons_append, List.singleton_append]
          rw [List.append_assoc, List.cons_append, List.nil_append]
          rw [decBody_enc t fuel' (pos + 2) rest (by
            simp only [iSize, lSize] at hfuel ⊢
            omega)]
          simp only [Except.ok_bind', if_neg (by decide : ¬((false : Bool) = true))]
          simp only [Except.ok.injEq, Prod.mk.injEq, iImage, lImage,
            List.length_cons, List.length_nil, List.length_append]
          exact ⟨trivial, by omega⟩
      | cons e' es =>
          simp only [encodeInstr, decInstr, List.cons_append, List.singleton_append]
          rw [List.append_assoc, List.cons_append]
          rw [decBody_enc_else t fuel' (pos + 2)
            ((encodeBody (e' :: es) ++ [0x0B]) ++ rest) (by
              simp only [iSize, lSize] at hfuel ⊢
              omega)]
          simp only [Except.ok_bind', if_pos (by decide : ((true : Bool) = true))]
          have hsub : pos + 2 + (encodeBody t).length + 1 - (pos + 2)
              = (encodeBody t).length + 1 := by omega
          rw [hsub, suffixAt, dropAppendSucc]
          rw [List.append_assoc, List.cons_append, List.nil_append]
          rw [decBody_enc (e' :: es) fuel' (pos + 2 + (encodeBody t).length + 1)
            rest (by
              simp only [iSize, lSize] at hfuel ⊢
              omega)]
          simp only [Except.ok_bind',
            if_neg (by decide : ¬((false : Bool) = true))]
          simp only [Except.ok.injEq, Prod.mk.injEq, iImage, List.length_cons,
            List.length_nil, List.length_append, lImage]
          simp <;> omega

/-- THE PER-BODY LAW, frame-end form: the decoder consumes the body's
    bytes plus its `0x0B`, returns the image. -/
theorem decBody_enc : ∀ (is : List Instr) (fuel pos : Nat) (rest : List UInt8),
    lSize is + 2 ≤ fuel →
    decBody fuel pos (encodeBody is ++ 0x0B :: rest) =
      .ok (lImage is, pos + (encodeBody is).length + 1, false) := by
  intro is
  cases is with
  | nil =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeBody, List.nil_append, lImage]
      simp only [decBody, decInstr]
      simp
  | cons i is =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
        have h1 := iSize_pos i
        simp only [lSize] at hfuel
        omega⟩
      have hcount1 : iSize i + 2 ≤ fuel' + 1 := by
        have h := hfuel
        simp only [lSize] at h
        omega
      have hcount2 : lSize is + 2 ≤ fuel' := by
        have h := hfuel
        have h1 := iSize_pos i
        simp only [lSize] at h
        omega
      simp only [encodeBody, List.cons_append]
      rw [List.append_assoc]
      simp only [decBody]
      rw [decInstr_enc i (fuel' + 1) pos (encodeBody is ++ 0x0B :: rest) hcount1]
      show (decBody fuel' (pos + (encodeInstr i).length)
          (suffixAt (encodeInstr i ++ (encodeBody is ++ 0x0B :: rest))
            (pos + (encodeInstr i).length - pos))).bind
        (fun (is', pos'', e5) => .ok (iImage i :: is', pos'', e5))
        = _
      have hL : pos + (encodeInstr i).length - pos = (encodeInstr i).length := by omega
      rw [hL, suffixAt, dropAppendLen]
      rw [decBody_enc is fuel' (pos + (encodeInstr i).length) rest hcount2]
      simp only [Except.ok.injEq, Prod.mk.injEq, lImage, List.append_assoc,
        List.length_append, List.cons_append, iImage]
      simp <;> omega

/-- THE PER-BODY LAW, else-divider form: the then-body's bytes plus its
    `0x05`. -/
theorem decBody_enc_else : ∀ (is : List Instr) (fuel pos : Nat) (rest : List UInt8),
    lSize is + 2 ≤ fuel →
    decBody fuel pos (encodeBody is ++ 0x05 :: rest) =
      .ok (lImage is, pos + (encodeBody is).length + 1, true) := by
  intro is
  cases is with
  | nil =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [encodeBody, List.nil_append, lImage]
      simp only [decBody, decInstr]
      simp
  | cons i is =>
      intro fuel pos rest hfuel
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
        have h1 := iSize_pos i
        simp only [lSize] at hfuel
        omega⟩
      have hcount1 : iSize i + 2 ≤ fuel' + 1 := by
        have h := hfuel
        simp only [lSize] at h
        omega
      have hcount2 : lSize is + 2 ≤ fuel' := by
        have h := hfuel
        have h1 := iSize_pos i
        simp only [lSize] at h
        omega
      simp only [encodeBody, List.cons_append]
      rw [List.append_assoc]
      simp only [decBody]
      rw [decInstr_enc i (fuel' + 1) pos (encodeBody is ++ 0x05 :: rest) hcount1]
      show (decBody fuel' (pos + (encodeInstr i).length)
          (suffixAt (encodeInstr i ++ (encodeBody is ++ 0x05 :: rest))
            (pos + (encodeInstr i).length - pos))).bind
        (fun (is', pos'', e5) => .ok (iImage i :: is', pos'', e5))
        = _
      have hL : pos + (encodeInstr i).length - pos = (encodeInstr i).length := by omega
      rw [hL, suffixAt, dropAppendLen]
      rw [decBody_enc_else is fuel' (pos + (encodeInstr i).length) rest hcount2]
      simp only [Except.ok.injEq, Prod.mk.injEq, lImage, List.append_assoc,
        List.length_append, List.cons_append, iImage]
      simp <;> omega
end

/-! ## The module law — the NAMED REMAINDER -/

/- The module-level law `decode_encode_module` (decode ∘ encode = id
   over `moduleFrag`) is the named remainder of this order, runtime
   tested in WasmCoreTests (the duel corpus's round trip + re-encode +
   re-validation sweeps + the corruption refusals — the byte-tie face),
   NOT proved. The two defeats, named: (1) the fuel-discipline's
   off-by-one at the body/instr boundary (the count-discipline `+2`
   resolves the shape but the section-content lemmas' chains remain);
   (2) `simp only` refuses the matcher-iota on the section envelope's
   cons scrutinee (the `split`-based discharge fights the `if_neg`
   instances per arm). The pilot lemma `decSection_enc` was withdrawn
   rather than stubbed. The per-instruction laws (`decInstr_enc`,
   `decBody_enc`, `decBody_enc_else`) ARE proved above; what remains
   is their assembly through the seven section slots. -/

/-- The module fragment: the encoder's honest image — every function
    body carries canonical bit-pattern consts, no memarg restates its
    elided default alignment, and the ONE table (≤ 1). -/
def moduleFrag (m : Module) : Prop :=
  (∀ f : Func, f ∈ m.funcs → bodyFrag f.body) ∧ m.tables.length ≤ 1

/-! ## The module envelope: the preamble + the fixed-order sections -/

/-- The cross-section accumulator (the raw section payloads before the
    cross-section ties). -/
structure DecAcc where
  types : List FuncType := []
  funcTys : List Nat := []
  code : List (List ValType × List Instr) := []
  exports : List Export := []
  memMin : Nat := 0
  tables : List Nat := []
  elems : List (List Nat) := []
  deriving Inhabited

/-- Value-type sequence: a count then that many valtype bytes. -/
def decValTypesGo : Nat → Nat → List UInt8 → Except DecodeError (List ValType × Nat)
  | 0, pos, _ => .ok ([], pos)
  | n + 1, pos, bs =>
      match bs with
      | [] => .error (.truncated pos 1)
      | b :: rest =>
          match valTypeOfByte? b with
          | some t =>
              (decValTypesGo n (pos + 1) rest).map fun (ts, p) => (t :: ts, p)
          | none => .error (.badValType pos b)

/-- One functype: `0x60` params results. -/
def decFuncType : Nat → List UInt8 → Except DecodeError (FuncType × Nat)
  | pos, [] => .error (.truncated pos 1)
  | pos, 0x60 :: rest => do
      let (np, pos1) ← decVarNatR (pos + 1) rest
      let (ps, pos2) ← decValTypesGo np pos1 (suffixAt rest (pos1 - (pos + 1)))
      let (nr, pos3) ← decVarNatR pos2 (suffixAt rest (pos2 - (pos + 1)))
      let (rs, pos4) ← decValTypesGo nr pos3 (suffixAt rest (pos3 - (pos + 1)))
      .ok (⟨ps, rs⟩, pos4)
  | pos, b :: _ => .error (.badFuncType pos b)

/-- Functype sequence. -/
def decTypesGo : Nat → Nat → List UInt8 → Except DecodeError (List FuncType × Nat)
  | 0, pos, _ => .ok ([], pos)
  | n + 1, pos, bs => do
      let (ft, pos1) ← decFuncType pos bs
      let (ts, pos2) ← decTypesGo n pos1 (suffixAt bs (pos1 - pos))
      .ok (ft :: ts, pos2)

def decTypeSec : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat)
  | acc, pos, bs => do
      let (n, pos1) ← decVarNatR pos bs
      let (ts, pos2) ← decTypesGo n pos1 (suffixAt bs (pos1 - pos))
      .ok ({ acc with types := ts }, pos2)

def decFuncSec : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat)
  | acc, pos, bs => do
      let (n, pos1) ← decVarNatR pos bs
      let rec go : Nat → Nat → List UInt8 → Except DecodeError (List Nat × Nat)
        | 0, p, _ => .ok ([], p)
        | k + 1, p, r => do
            let (t, p1) ← decVarNatR p r
            let (ts, p2) ← go k p1 (suffixAt r (p1 - p))
            .ok (t :: ts, p2)
      let (ts, pos2) ← go n pos1 (suffixAt bs (pos1 - pos))
      .ok ({ acc with funcTys := ts }, pos2)

def decTableSec : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat)
  | acc, pos, bs => do
      let (n, pos1) ← decVarNatR pos bs
      let rec go : Nat → Nat → List UInt8 → Except DecodeError (List Nat × Nat)
        | 0, p, _ => .ok ([], p)
        | k + 1, p, r => do
            match r with
            | 0x70 :: 0x00 :: rest2 => do
                let (mn, p1) ← decVarNatR (p + 2) rest2
                let (ms, p2) ← go k p1 (suffixAt rest2 (p1 - (p + 2)))
                .ok (mn :: ms, p2)
            | 0x70 :: b :: _ => .error (.badTableForm (p + 1) b)
            | b :: _ => .error (.badTableForm p b)
            | [] => .error (.truncated p 1)
      let (ms, pos2) ← go n pos1 (suffixAt bs (pos1 - pos))
      .ok ({ acc with tables := ms }, pos2)

def decMemSec : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat)
  | acc, pos, bs => do
      let (n, pos1) ← decVarNatR pos bs
      if n != 1 then .error (.badMemCount pos n)
      else
        match suffixAt bs (pos1 - pos) with
        | 0x00 :: rest2 => do
            let (mn, p1) ← decVarNatR (pos1 + 1) rest2
            .ok ({ acc with memMin := mn }, p1)
        | b :: _ => .error (.badMemForm pos1 b)
        | [] => .error (.truncated pos1 1)

def decExportSec : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat)
  | acc, pos, bs => do
      let (n, pos1) ← decVarNatR pos bs
      let rec go : Nat → Nat → List UInt8 → Except DecodeError (List Export × Nat)
        | 0, p, _ => .ok ([], p)
        | k + 1, p, r => do
            let (len, p1) ← decVarNatR p r
            let bytes := suffixAt r (p1 - p)
            if bytes.length < len then .error (.truncated p1 (len - bytes.length))
            else
              let nmBytes := bytes.take len
              match String.fromUTF8? (ByteArray.mk nmBytes.toArray) with
              | none => .error (.badUtf8 p1)
              | some nm =>
                  let p2 := p1 + len
                  match suffixAt bytes len with
                  | 0x00 :: rest2 => do
                      let (idx, p3) ← decVarNatR (p2 + 1) rest2
                      let (es, p4) ← go k p3 (suffixAt rest2 (p3 - (p2 + 1)))
                      .ok ({ name := nm, desc := .func idx } :: es, p4)
                  | 0x02 :: rest2 => do
                      let (idx, p3) ← decVarNatR (p2 + 1) rest2
                      let (es, p4) ← go k p3 (suffixAt rest2 (p3 - (p2 + 1)))
                      .ok ({ name := nm, desc := .memory idx } :: es, p4)
                  | b :: _ => .error (.badExportKind p2 b)
                  | [] => .error (.truncated p2 1)
      let (es, pos2) ← go n pos1 (suffixAt bs (pos1 - pos))
      .ok ({ acc with exports := es }, pos2)

def decElemSec : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat)
  | acc, pos, bs => do
      let (n, pos1) ← decVarNatR pos bs
      let rec go : Nat → Nat → List UInt8 → Except DecodeError (List (List Nat) × Nat)
        | 0, p, _ => .ok ([], p)
        | k + 1, p, r => do
            match r with
            | 0x00 :: 0x41 :: 0x00 :: 0x0B :: rest2 => do
                let (cnt, p1) ← decVarNatR (p + 4) rest2
                let rec goi : Nat → Nat → List UInt8 → Except DecodeError (List Nat × Nat)
                  | 0, q, _ => .ok ([], q)
                  | j + 1, q, rr => do
                      let (ix, q1) ← decVarNatR q rr
                      let (ixs, q2) ← goi j q1 (suffixAt rr (q1 - q))
                      .ok (ix :: ixs, q2)
                let (ixs, p2) ← goi cnt p1 (suffixAt rest2 (p1 - (p + 4)))
                let (ess, p3) ← go k p2 (suffixAt rest2 (p2 - (p + 4)))
                .ok (ixs :: ess, p3)
            | 0x00 :: 0x41 :: 0x00 :: b :: _ => .error (.badElemOffset (p + 3) b)
            | 0x00 :: 0x41 :: b :: _ => .error (.badElemOffset (p + 2) b)
            | 0x00 :: b :: _ => .error (.badElemOffset (p + 1) b)
            | 0x00 :: [] => .error (.truncated (p + 1) 3)
            | b :: _ => .error (.badElemForm p b)
            | [] => .error (.truncated p 1)
      let (ess, pos2) ← go n pos1 (suffixAt bs (pos1 - pos))
      .ok ({ acc with elems := ess }, pos2)

def decCodeSec : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat)
  | acc, pos, bs => do
      let (n, pos1) ← decVarNatR pos bs
      let rest := suffixAt bs (pos1 - pos)
      let fuel := rest.length
      let rec goLocals : Nat → Nat → List UInt8 → Except DecodeError (List ValType × Nat)
        | 0, p, _ => .ok ([], p)
        | g + 1, p, r => do
            let (cnt, q1) ← decVarNatR p r
            let (ts, q2) ← decValTypesGo cnt q1 (suffixAt r (q1 - p))
            let (ts', q3) ← goLocals g q2 (suffixAt r (q2 - p))
            .ok (ts ++ ts', q3)
      let rec goEntry : Nat → Nat → List UInt8 → Except DecodeError
          ((List ValType × List Instr) × Nat)
        | p, sz, r => do
            let (gcnt, q0) ← decVarNatR p r
            let (locs, q1) ← goLocals gcnt q0 (suffixAt r (q0 - p))
            let (body, (q2, _)) ← decBody fuel q1 (suffixAt r (q1 - p))
            if q2 - p = sz then .ok ((locs, body), q2)
            else .error (.bodyOverrun q1)
      let rec go : Nat → Nat → List UInt8 →
          Except DecodeError (List (List ValType × List Instr) × Nat)
        | 0, p, _ => .ok ([], p)
        | k + 1, p, r => do
            let (sz, q1) ← decVarNatR p r
            let entry := suffixAt r (q1 - p)
            if entry.length < sz then .error (.truncated q1 (sz - entry.length))
            else do
              let ((locs, body), q2) ← goEntry q1 sz entry
              let (es, q3) ← go k q2 (suffixAt entry (q2 - q1))
              .ok ((locs, body) :: es, q3)
      let (cs, pos2) ← go n pos1 rest
      .ok ({ acc with code := cs }, pos2)

/-- Table/elem pairing (positional: table i's init = element segment i's
    function indices, whose count must equal the table's declared size). -/
def decTables : List Nat → List (List Nat) → Nat → Except DecodeError (List Table)
  | [], [], _ => .ok []
  | tmin :: trest, els, pos =>
      match els with
      | el :: erest =>
          if el.length = tmin then
            (decTables trest erest pos).map fun ts => { init := el } :: ts
          else .error (.tableElemMismatch pos)
      | [] =>
          if tmin = 0 then (decTables trest [] pos).map fun ts => { init := [] } :: ts
          else .error (.missingElem pos)
  | [], _ :: _, pos => .error (.elemWithoutTable pos)

/-- The cross-section ties: the function-section/code-section count tie,
    the table/elem positional pairing. -/
def assembleAcc (acc : DecAcc) (pos : Nat) : Except DecodeError Module :=
  if acc.funcTys.length != acc.code.length then .error (.funcCountMismatch pos)
  else
    let funcs := (acc.funcTys.zip acc.code).map
      fun (ty, entry) => ({ tyIdx := ty, locals := entry.1, body := entry.2 } : Func)
    match decTables acc.tables acc.elems pos with
    | .error e => .error e
    | .ok tbls =>
        .ok ({ types := acc.types, funcs := funcs, exports := acc.exports,
               memMin := acc.memMin, tables := tbls } : Module)

/-- The section envelope: id + length-prefixed content; a lower id is a
    fixed-order violation; a different (higher) id skips the slot;
    the content parser must fill the declared length exactly. -/
def decSection (id : UInt8) (parser : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat))
    (acc : DecAcc) (pos : Nat) (bs : List UInt8) : Except DecodeError (DecAcc × Nat) :=
  match bs with
  | [] => .ok (acc, pos)
  | b :: rest =>
      if b < id then .error (.sectionOrder pos b)
      else if b != id then .ok (acc, pos)
      else
        (decVarNatR (pos + 1) rest).bind fun (len, pos1) =>
          let content := suffixAt rest (pos1 - (pos + 1))
          if content.length < len then .error (.truncated pos1 (len - content.length))
          else
            (parser acc pos1 content).bind fun (acc', pos2) =>
              if pos2 - pos1 = len then .ok (acc', pos2)
              else .error (.bodyOverrun pos2)

/-! ## The section envelope's laws (the specialized reduction discipline) -/

/-- THE SECTION-ENVELOPE REDUCTION (the 06 §2 discipline): `decSection`
over the encoder's exact section spelling `id :: (encVarNat len ++
content ++ tail)`. The matcher-iota on the cons scrutinee + the if-chain
(`id < id` refuses, `id != id` refuses) reduce ONCE here, for the
concrete shape; every slot's law routes through this lemma. The parser
side-condition is the append-form discipline (pattern #2): the parser
consumes exactly `content` from any tail. -/
theorem decSection_enc (id : UInt8)
    (parser : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat))
    (acc acc' : DecAcc) (pos : Nat) (content rest : List UInt8)
    (hlaw : ∀ tail : List UInt8,
      parser acc (pos + 1 + (encVarNat content.length).length) (content ++ tail)
        = .ok (acc', pos + 1 + (encVarNat content.length).length + content.length)) :
    decSection id parser acc pos (id :: (encVarNat content.length ++ content ++ rest))
      = .ok (acc', pos + 1 + (encVarNat content.length).length + content.length) := by
  simp only [decSection, if_neg (show ¬(id < id) from by simp),
    if_neg (show ¬((id != id) = true) from by simp)]
  rw [List.append_assoc, decVarNatR_enc content.length (pos + 1) (content ++ rest),
    Except.ok_bind']
  simp only
  have hL : (pos + 1 + (encVarNat content.length).length) - (pos + 1)
      = (encVarNat content.length).length := by omega
  rw [hL, suffixAt, dropAppendLen,
    if_neg (show ¬((content ++ rest).length < content.length) from by
      simp only [List.length_append]
      omega)]
  rw [hlaw rest, Except.ok_bind']
  simp only
  have hE : pos + 1 + (encVarNat content.length).length + content.length
      - (pos + 1 + (encVarNat content.length).length) = content.length := by omega
  rw [if_pos hE]

/-- The envelope's SKIP arm: a different (higher) id byte leaves the
    accumulator and position untouched (the elided-slot face). -/
theorem decSection_skip (id : UInt8)
    (parser : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat))
    (acc : DecAcc) (pos : Nat) (b : UInt8) (rest : List UInt8)
    (hlt : ¬(b < id)) (hne : (b != id) = true) :
    decSection id parser acc pos (b :: rest) = .ok (acc, pos) := by
  simp only [decSection, if_neg hlt, if_pos hne]

/-- The envelope's EMPTY arm: out of bytes, the slot is skipped. -/
theorem decSection_nil (id : UInt8)
    (parser : DecAcc → Nat → List UInt8 → Except DecodeError (DecAcc × Nat))
    (acc : DecAcc) (pos : Nat) :
    decSection id parser acc pos [] = .ok (acc, pos) := rfl

/-! ## The module law's glue: folds, byte arrays, UTF-8, the varint count -/

/-- The encoder's varint is never empty (the code-slot fuel bound's
    face: every length prefix costs at least one byte). -/
theorem encVarNat_pos (n : Nat) : 0 < (encVarNat n).length := by
  rcases Nat.lt_or_ge n 128 with h | h
  · simp only [encVarNat, encVarNatGo, if_pos h, List.length_singleton]
    omega
  · rw [encVarNat_cons n h]
    simp

/-- The fold that assembles a section's entries is a single append
    chain (the `(· ++ ·)` fold's accumulator face). -/
theorem foldlApp_eq : ∀ (l : List (List UInt8)) (acc : List UInt8),
    List.foldl (· ++ ·) acc l = acc ++ List.foldl (· ++ ·) [] l := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons a l ih =>
      intro acc
      rw [List.foldl_cons, ih (acc ++ a)]
      rw [List.foldl_cons, List.nil_append, ih a]
      rw [List.append_assoc]

/-- The fold's head face: the first entry's bytes come first. -/
theorem foldlApp_nil_cons (a : List UInt8) (l : List (List UInt8)) :
    List.foldl (· ++ ·) [] (a :: l) = a ++ List.foldl (· ++ ·) [] l := by
  rw [List.foldl_cons, List.nil_append, foldlApp_eq l a]

/-- THE SECTION-ENTRY GLUE (the append-form discipline at the fold):
    the encoder's entry fold peels its first entry in front of any
    tail — every slot law's induction step rides this. -/
theorem foldlMap_cons (f : α → List UInt8) (x : α) (xs : List α) (rest : List UInt8) :
    List.foldl (· ++ ·) [] ((x :: xs).map f) ++ rest
      = f x ++ (List.foldl (· ++ ·) [] (xs.map f) ++ rest) := by
  simp only [List.map_cons, List.cons_append, foldlApp_nil_cons, List.append_assoc]

/-- The fold's length splits at the head entry (the code slot's fuel
    bookkeeping). -/
theorem foldlMap_cons_len (f : α → List UInt8) (x : α) (xs : List α) :
    (List.foldl (· ++ ·) [] ((x :: xs).map f)).length
      = (f x).length + (List.foldl (· ++ ·) [] (xs.map f)).length := by
  rw [List.map_cons, foldlApp_nil_cons, List.length_append]

/-- Taking a prefix's length off an append yields the prefix (the
    export slot's name-byte face). -/
theorem takeAppendLen (l1 l2 : List UInt8) : (l1 ++ l2).take l1.length = l1 := by
  induction l1 with
  | nil => simp
  | cons a l1 ih =>
      show (a :: (l1 ++ l2)).take (l1.length + 1) = a :: l1
      rw [List.take_cons (by omega), Nat.add_sub_cancel]
      exact congrArg (a :: ·) ih

/-- The head-split length face over the map-reduced cons (the
    slot laws' position arithmetic). -/
theorem foldlMap_cons_len' (f : α → List UInt8) (x : α) (xs : List α) :
    (List.foldl (· ++ ·) [] (f x :: List.map f xs)).length
      = (f x).length + (List.foldl (· ++ ·) [] (List.map f xs)).length :=
  foldlMap_cons_len f x xs

/-- Every entry's bytes fit inside the whole fold (the code slot's
    fuel bound: the body's count discipline is funded from the
    section-content byte count). -/
theorem foldlMap_len_ge (f : α → List UInt8) : ∀ (xs : List α) (x : α), x ∈ xs →
    (f x).length ≤ (List.foldl (· ++ ·) [] (xs.map f)).length := by
  intro xs
  induction xs with
  | nil => intro x h; cases h
  | cons y ys ih =>
      intro x hmem
      rw [foldlMap_cons_len]
      rcases List.mem_cons.1 hmem with hxy | hmem
      · subst hxy; omega
      · have := ih x hmem
        omega

/-- The `get!`-walk that IS `ByteArray.toList` returns the underlying
    array's list (the byte-array round trip). -/
theorem list_cons_drop : ∀ (l : List UInt8) (i : Nat), i < l.length →
    l[i]! :: l.drop (i + 1) = l.drop i := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons a l ih =>
      intro i h
      cases i with
      | zero => simp
      | succ i =>
          have h' : i < l.length := by simp at h; omega
          rw [List.getElem!_cons_succ, List.drop_succ_cons, List.drop_succ_cons]
          exact ih i h'

private theorem toList_loop_char (b : ByteArray) :
    ∀ (i : Nat) (r : List UInt8), ByteArray.toList.loop b i r
      = r.reverse ++ b.data.toList.drop i := by
  have hL : b.size = b.data.toList.length := rfl
  have key : ∀ (d i : Nat) (r : List UInt8), i + d = b.data.toList.length →
      ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
    intro d
    induction d with
    | zero =>
        intro i r hd
        rw [ByteArray.toList.loop.eq_def, if_neg (by rw [hL]; omega),
          List.drop_eq_nil_of_le (by omega)]
        simp
    | succ d ih =>
        intro i r hd
        have hi : i < b.data.toList.length := by omega
        rw [ByteArray.toList.loop.eq_def, if_pos (by rw [hL]; omega),
          show b.get! i = b.data.toList[i]! from by
            rw [show b.get! i = b.data[i]! from rfl, Array.getElem!_toList]]
        rw [ih (i + 1) (b.data.toList[i]! :: r) (by omega)]
        rw [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
          list_cons_drop b.data.toList i hi]
  intro i r
  rcases Nat.lt_or_ge i b.data.toList.length with h | h
  · exact key (b.data.toList.length - i) i r (by omega)
  · rw [ByteArray.toList.loop.eq_def, if_neg (by rw [hL]; omega),
      List.drop_eq_nil_of_le (by omega)]
    simp

/-- The fold's cons-length face over an ALREADY-unfolded head (the
    export slot's residual, where `encodeExport` was unfolded before
    the generic lemma's `?f ?x` pattern could no longer match). -/
theorem foldlApp_nil_cons_len (a : List UInt8) (l : List (List UInt8)) :
    (List.foldl (· ++ ·) [] (a :: l)).length
      = a.length + (List.foldl (· ++ ·) [] l).length := by
  rw [foldlApp_nil_cons, List.length_append]

/-- The byte array's toList IS its underlying array's toList (the
    loop's fold is the identity walk). -/
theorem ByteArray.toList_data (b : ByteArray) : b.toList = b.data.toList := by
  show ByteArray.toList.loop b 0 [] = b.data.toList
  rw [toList_loop_char]
  simp

/-- THE BYTE-ARRAY ROUND TRIP: a byte array rebuilt from its own
    toList is itself (the export slot's name bytes). -/
theorem byteArray_mk_toList (b : ByteArray) : ByteArray.mk b.toList.toArray = b := by
  rw [ByteArray.toList_data, Array.toArray_toList]

/-- THE UTF-8 ROUND TRIP: a string's own bytes, rebuilt as a byte
    array, decode back to the string (the export slot's name face —
    the wall that blocked the exports law). -/
theorem utf8_roundtrip (s : String) :
    String.fromUTF8? (ByteArray.mk s.toByteArray.toList.toArray) = some s := by
  rw [byteArray_mk_toList]
  unfold String.fromUTF8?
  rw [dif_pos s.isValidUTF8]
  rfl

/-! ## The slot laws: the section-content parsers over the encoder's image -/

/-- Value-type sequence: the decoder consumes exactly the valtype
    bytes the encoder emits (the locals' and functypes' read face). -/
theorem decValTypesGo_enc : ∀ (ts : List ValType) (pos : Nat) (rest : List UInt8),
    decValTypesGo ts.length pos (ts.map encodeValType ++ rest)
      = .ok (ts, pos + (ts.map encodeValType).length) := by
  intro ts
  induction ts with
  | nil => intro pos rest; rfl
  | cons t ts ih =>
      intro pos rest
      simp only [List.length_cons, List.map_cons, List.cons_append, decValTypesGo,
        valTypeOfByte_hit, Except.ok_map']
      rw [ih (pos + 1) rest]
      simp only [Except.ok_map', Except.ok.injEq, Prod.mk.injEq, List.length_cons,
        List.length_map]
      exact ⟨trivial, by omega⟩

/-- The singleton face (the locals' one-group-per-local shape). -/
theorem decValTypesGo_one (t : ValType) (pos : Nat) (rest : List UInt8) :
    decValTypesGo 1 pos ([encodeValType t] ++ rest) = .ok ([t], pos + 1) := by
  simp only [List.cons_append, decValTypesGo, valTypeOfByte_hit, Except.ok_map']

/-- One functype: the decoder consumes exactly `encodeFuncType`'s
    bytes (the 06 §2 positioned-reader discipline: the suffixAt
    bookkeeping rides `dropAppendLen`/`dropAppendSucc2`). -/
theorem decFuncType_enc (ft : FuncType) (pos : Nat) (tail : List UInt8) :
    decFuncType pos (encodeFuncType ft ++ tail)
      = .ok (ft, pos + (encodeFuncType ft).length) := by
  obtain ⟨ps, rs⟩ := ft
  simp only [encodeFuncType, decFuncType, List.cons_append, List.append_assoc]
  rw [decVarNatR_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + 1 + (encVarNat ps.length).length) - (pos + 1)
      = (encVarNat ps.length).length from by omega,
    suffixAt, dropAppendLen]
  rw [decValTypesGo_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + 1 + (encVarNat ps.length).length + (ps.map encodeValType).length)
      - (pos + 1)
    = (encVarNat ps.length).length + (ps.map encodeValType).length from by omega,
    suffixAt, dropAppendSucc2, dropAppendLen]
  rw [decVarNatR_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + 1 + (encVarNat ps.length).length + (ps.map encodeValType).length
      + (encVarNat rs.length).length) - (pos + 1)
    = (encVarNat ps.length).length
      + ((ps.map encodeValType).length + (encVarNat rs.length).length) from by omega,
    suffixAt, dropAppendSucc2, dropAppendSucc2, dropAppendLen]
  rw [decValTypesGo_enc]
  simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq, List.length_cons,
    List.length_append, List.length_map]
  exact ⟨trivial, by omega⟩

/-- Functype sequence: the decoder consumes exactly the encoder's
    fold (the type slot's read face; the fold's head peel is
    `foldlMap_cons`). -/
theorem decTypesGo_enc : ∀ (fts : List FuncType) (pos : Nat) (tail : List UInt8),
    decTypesGo fts.length pos
        (List.foldl (· ++ ·) [] (fts.map encodeFuncType) ++ tail)
      = .ok (fts, pos + (List.foldl (· ++ ·) [] (fts.map encodeFuncType)).length) := by
  intro fts
  induction fts with
  | nil => intro pos tail; simp [decTypesGo]
  | cons ft fts ih =>
      intro pos tail
      rw [foldlMap_cons encodeFuncType ft fts tail]
      simp only [List.length_cons, List.map_cons, decTypesGo]
      rw [decFuncType_enc ft pos (List.foldl (· ++ ·) [] (fts.map encodeFuncType) ++ tail)]
      simp only [Except.ok_bindMono]
      rw [show (pos + (encodeFuncType ft).length) - pos = (encodeFuncType ft).length
        from by omega,
        suffixAt, dropAppendLen]
      rw [ih]
      simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq,
        foldlMap_cons_len']
      exact ⟨trivial, by omega⟩

/-! ## The seven slot laws (each routes through `decSection_enc`) -/

/-- THE TYPE SLOT: the decoder consumes the encoder's functype fold
    exactly and returns the functypes. -/
theorem decTypeSec_enc (acc : DecAcc) (ts : List FuncType) (pos : Nat) (tail : List UInt8) :
    decTypeSec acc pos
        ((encVarNat ts.length ++ List.foldl (· ++ ·) [] (ts.map encodeFuncType)) ++ tail)
      = .ok ({ acc with types := ts },
          pos + (encVarNat ts.length).length
            + (List.foldl (· ++ ·) [] (ts.map encodeFuncType)).length) := by
  simp only [decTypeSec, List.append_assoc]
  rw [decVarNatR_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + (encVarNat ts.length).length) - pos = (encVarNat ts.length).length
    from by omega,
    suffixAt, dropAppendLen]
  rw [decTypesGo_enc]
  simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq, List.length_append]

/-- The tyIdx fold's cons-length face (the head entry's varint is
    beta-reduced, so the generic lemma's `?f ?x` pattern cannot match —
    this specialized form fires). -/
theorem foldlTyIdx_len (f : Func) (fs : List Func) :
    (List.foldl (· ++ ·) []
        (encVarNat f.tyIdx :: List.map (fun g => encVarNat g.tyIdx) fs)).length
      = (encVarNat f.tyIdx).length
        + (List.foldl (· ++ ·) []
            (List.map (fun g => encVarNat g.tyIdx) fs)).length := by
  have h1 := foldlApp_nil_cons (encVarNat f.tyIdx)
    (List.map (fun g => encVarNat g.tyIdx) fs)
  rw [h1, List.length_append]

/-- The entry-fold's cons-length face (the head entry's bytes are
    beta-reduced, so the generic lemma's `?f ?x` pattern cannot match —
    this specialized form fires). -/
theorem foldlTyEntry_len (f : Func) (fs : List Func) :
    (List.foldl (· ++ ·) [] (encodeFuncEntry f :: List.map encodeFuncEntry fs)).length
      = (encodeFuncEntry f).length
        + (List.foldl (· ++ ·) [] (List.map encodeFuncEntry fs)).length := by
  have h1 := foldlApp_nil_cons (encodeFuncEntry f) (List.map encodeFuncEntry fs)
  rw [h1, List.length_append]

/-- The function-section's index fold (the read face of the
    func-slot's entries). -/
theorem decFuncSec_go_enc : ∀ (fs : List Func) (pos : Nat) (tail : List UInt8),
    decFuncSec.go fs.length pos
        (List.foldl (· ++ ·) [] (fs.map (fun f => encVarNat f.tyIdx)) ++ tail)
      = .ok (fs.map (fun f => f.tyIdx),
          pos + (List.foldl (· ++ ·) [] (fs.map (fun f => encVarNat f.tyIdx))).length) := by
  intro fs
  induction fs with
  | nil => intro pos tail; simp [decFuncSec.go]
  | cons f fs ih =>
      intro pos tail
      rw [foldlMap_cons (fun f => encVarNat f.tyIdx) f fs tail]
      simp only [List.length_cons, decFuncSec.go]
      rw [decVarNatR_enc, Except.ok_bindMono, Nat.add_sub_cancel_left, suffixAt,
        dropAppendLen]
      rw [ih]
      simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq, List.map_cons,
        foldlTyIdx_len]
      exact ⟨trivial, by omega⟩

/-- THE FUNC SLOT. -/
theorem decFuncSec_enc (acc : DecAcc) (fs : List Func) (pos : Nat) (tail : List UInt8) :
    decFuncSec acc pos
        ((encVarNat fs.length ++ List.foldl (· ++ ·) [] (fs.map (fun f => encVarNat f.tyIdx))) ++ tail)
      = .ok ({ acc with funcTys := fs.map (fun f => f.tyIdx) },
          pos + (encVarNat fs.length).length
            + (List.foldl (· ++ ·) [] (fs.map (fun f => encVarNat f.tyIdx))).length) := by
  simp only [decFuncSec, List.append_assoc]
  rw [decVarNatR_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + (encVarNat fs.length).length) - pos = (encVarNat fs.length).length
    from by omega,
    suffixAt, dropAppendLen]
  rw [decFuncSec_go_enc]
  simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq, List.length_append]

/-- The table-section's entry fold (the `0x70 0x00` + limits shape). -/
theorem decTableSec_go_enc : ∀ (ts : List Table) (pos : Nat) (tail : List UInt8),
    decTableSec.go ts.length pos
        (List.foldl (· ++ ·) [] (ts.map encodeTable) ++ tail)
      = .ok (ts.map (fun t => t.init.length),
          pos + (List.foldl (· ++ ·) [] (ts.map encodeTable)).length) := by
  intro ts
  induction ts with
  | nil => intro pos tail; simp [decTableSec.go]
  | cons t ts ih =>
      intro pos tail
      rw [foldlMap_cons encodeTable t ts tail]
      simp only [List.length_cons, decTableSec.go]
      rw [foldlMap_cons_len encodeTable t ts]
      simp only [encodeTable, List.cons_append, Except.ok_bindMono,
        decVarNatR_enc, Nat.add_sub_cancel_left, suffixAt, dropAppendLen]
      rw [ih]
      simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq, List.map_cons, List.length_cons]
      exact ⟨trivial, by omega⟩

/-- THE TABLE SLOT. -/
theorem decTableSec_enc (acc : DecAcc) (ts : List Table) (pos : Nat) (tail : List UInt8) :
    decTableSec acc pos
        ((encVarNat ts.length ++ List.foldl (· ++ ·) [] (ts.map encodeTable)) ++ tail)
      = .ok ({ acc with tables := ts.map (fun t => t.init.length) },
          pos + (encVarNat ts.length).length
            + (List.foldl (· ++ ·) [] (ts.map encodeTable)).length) := by
  simp only [decTableSec, List.append_assoc]
  rw [decVarNatR_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + (encVarNat ts.length).length) - pos = (encVarNat ts.length).length
    from by omega,
    suffixAt, dropAppendLen]
  rw [decTableSec_go_enc]
  simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq, List.length_append]

/-- THE MEM SLOT: the count is 1, the form byte is `0x00`, the min is
    the encoder's `memMin`. -/
theorem decMemSec_enc (acc : DecAcc) (mn : Nat) (pos : Nat) (tail : List UInt8) :
    decMemSec acc pos ((encVarNat 1 ++ [0x00] ++ encVarNat mn) ++ tail)
      = .ok ({ acc with memMin := mn },
          pos + (encVarNat 1).length + 1 + (encVarNat mn).length) := by
  simp only [decMemSec, List.append_assoc, List.cons_append]
  rw [decVarNatR_enc]
  simp only [Except.ok_bindMono,
    if_neg (show ¬(((1 : Nat) != 1) = true) from by simp)]
  rw [show (pos + (encVarNat 1).length) - pos = (encVarNat 1).length from by omega,
    suffixAt, dropAppendLen, List.nil_append]
  simp only [List.nil_append, Except.ok_bindMono, decVarNatR_enc,
    Except.ok.injEq, Prod.mk.injEq, List.length_append]

/-- The export-section's entry fold — the arms are the two kind bytes
    (the func/memory export shapes). -/
theorem decExportSec_go_enc : ∀ (es : List Export) (pos : Nat) (tail : List UInt8),
    decExportSec.go es.length pos
        (List.foldl (· ++ ·) [] (es.map encodeExport) ++ tail)
      = .ok (es, pos + (List.foldl (· ++ ·) [] (es.map encodeExport)).length) := by
  intro es
  induction es with
  | nil => intro pos tail; simp [decExportSec.go]
  | cons e es ih =>
      intro pos tail
      obtain ⟨nm, dsc⟩ := e
      cases dsc with
      | func idx =>
          rw [foldlMap_cons encodeExport ⟨nm, ExportDesc.func idx⟩ es tail]
          simp only [List.append_assoc, List.cons_append, List.length_cons,
            List.map_cons, encodeExport, decExportSec.go, Except.ok_bindMono,
            decVarNatR_enc, Nat.add_sub_cancel_left, suffixAt, dropAppendLen]
          rw [if_neg (by simp only [List.length_append]; omega), takeAppendLen,
            utf8_roundtrip]
          simp only [Except.ok_bindMono, decVarNatR_enc, suffixAt, dropAppendLen,
            ih, Except.ok.injEq, Prod.mk.injEq, Export.mk.injEq,
            List.length_append, List.length_cons, foldlApp_nil_cons_len]
          exact ⟨trivial, by omega⟩
      | memory idx =>
          rw [foldlMap_cons encodeExport ⟨nm, ExportDesc.memory idx⟩ es tail]
          simp only [List.append_assoc, List.cons_append, List.length_cons,
            List.map_cons, encodeExport, decExportSec.go, Except.ok_bindMono,
            decVarNatR_enc, Nat.add_sub_cancel_left, suffixAt, dropAppendLen]
          rw [if_neg (by simp only [List.length_append]; omega), takeAppendLen,
            utf8_roundtrip]
          simp only [Except.ok_bindMono, decVarNatR_enc, suffixAt, dropAppendLen,
            ih, Except.ok.injEq, Prod.mk.injEq, Export.mk.injEq,
            List.length_append, List.length_cons, foldlApp_nil_cons_len]
          exact ⟨trivial, by omega⟩

/-- THE EXPORT SLOT (the UTF-8 round trip resolves the name). -/
theorem decExportSec_enc (acc : DecAcc) (es : List Export) (pos : Nat) (tail : List UInt8) :
    decExportSec acc pos
        ((encVarNat es.length ++ List.foldl (· ++ ·) [] (es.map encodeExport)) ++ tail)
      = .ok ({ acc with exports := es },
          pos + (encVarNat es.length).length
            + (List.foldl (· ++ ·) [] (es.map encodeExport)).length) := by
  simp only [decExportSec, List.append_assoc]
  rw [decVarNatR_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + (encVarNat es.length).length) - pos = (encVarNat es.length).length
    from by omega,
    suffixAt, dropAppendLen]
  rw [decExportSec_go_enc]
  simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq, List.length_append]

/-- The element-section's index fold (the read face of a segment's
    function indices). -/
theorem decElemSec_goi_enc : ∀ (idxs : List Nat) (q : Nat) (tail : List UInt8),
    decElemSec.go.goi idxs.length q
        (List.foldl (· ++ ·) [] (idxs.map encVarNat) ++ tail)
      = .ok (idxs, q + (List.foldl (· ++ ·) [] (idxs.map encVarNat)).length) := by
  intro idxs
  induction idxs with
  | nil => intro q tail; simp [decElemSec.go.goi]
  | cons ix idxs ih =>
      intro q tail
      rw [foldlMap_cons encVarNat ix idxs tail]
      simp only [List.length_cons, List.map_cons, decElemSec.go.goi,
        Except.ok_bindMono, decVarNatR_enc, Nat.add_sub_cancel_left, suffixAt,
        dropAppendLen]
      rw [ih]
      simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq,
        foldlMap_cons_len']
      exact ⟨trivial, by omega⟩

/-- The element-section's segment fold (the `0x00 0x41 0x00 0x0B`
    offset-expression shape). -/
theorem decElemSec_go_enc : ∀ (ts : List Table) (pos : Nat) (tail : List UInt8),
    decElemSec.go ts.length pos
        (List.foldl (· ++ ·) [] (ts.map encodeElem) ++ tail)
      = .ok (ts.map (fun t => t.init),
          pos + (List.foldl (· ++ ·) [] (ts.map encodeElem)).length) := by
  intro ts
  induction ts with
  | nil => intro pos tail; simp [decElemSec.go]
  | cons t ts ih =>
      intro pos tail
      rw [foldlMap_cons encodeElem t ts tail]
      simp only [List.length_cons, decElemSec.go, List.map_cons]
      rw [foldlMap_cons_len' encodeElem t ts]
      simp only [List.append_assoc, List.nil_append, List.cons_append, encodeElem,
        Except.ok_bindMono, decVarNatR_enc, Nat.add_sub_cancel_left, suffixAt,
        dropAppendLen, Nat.add_assoc]
      rw [show (pos + (4 + (encVarNat t.init.length).length)) - (pos + 4)
        = (encVarNat t.init.length).length from by omega,
        dropAppendLen, decElemSec_goi_enc]
      simp only [Except.ok_bindMono]
      rw [show ((pos + (4 + (encVarNat t.init.length).length))
        + (List.foldl (· ++ ·) [] (List.map encVarNat t.init)).length) - (pos + 4)
        = (encVarNat t.init.length).length
          + (List.foldl (· ++ ·) [] (List.map encVarNat t.init)).length
        from by omega,
        dropAppendSucc2, dropAppendLen, ih]
      simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq,
        List.length_cons, List.length_singleton, List.length_append]
      exact ⟨trivial, by omega⟩

/-- THE ELEM SLOT. -/
theorem decElemSec_enc (acc : DecAcc) (ts : List Table) (pos : Nat) (tail : List UInt8) :
    decElemSec acc pos
        ((encVarNat ts.length ++ List.foldl (· ++ ·) [] (ts.map encodeElem)) ++ tail)
      = .ok ({ acc with elems := ts.map (fun t => t.init) },
          pos + (encVarNat ts.length).length
            + (List.foldl (· ++ ·) [] (ts.map encodeElem)).length) := by
  simp only [decElemSec, List.append_assoc]
  rw [decVarNatR_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + (encVarNat ts.length).length) - pos = (encVarNat ts.length).length
    from by omega,
    suffixAt, dropAppendLen]
  rw [decElemSec_go_enc]
  simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq, List.length_append]

/-- The code-entry's locals fold (one group per declared local — the
    encoder's canonical grouping). -/
theorem decCodeSec_goLocals_enc : ∀ (ts : List ValType) (q : Nat) (tail : List UInt8),
    decCodeSec.goLocals ts.length q
        (List.foldl (· ++ ·) []
          (ts.map (fun t => encVarNat 1 ++ [encodeValType t])) ++ tail)
      = .ok (ts, q + (List.foldl (· ++ ·) []
          (ts.map (fun t => encVarNat 1 ++ [encodeValType t]))).length) := by
  intro ts
  induction ts with
  | nil => intro q tail; simp [decCodeSec.goLocals]
  | cons t ts ih =>
      intro q tail
      rw [foldlMap_cons (fun t => encVarNat 1 ++ [encodeValType t]) t ts tail]
      simp only [List.append_assoc, List.length_cons, decCodeSec.goLocals]
      rw [decVarNatR_enc]
      simp only [Except.ok_bindMono]
      rw [show (q + (encVarNat 1).length) - q = (encVarNat 1).length from by omega,
        suffixAt, dropAppendLen]
      rw [decValTypesGo_one]
      simp only [Except.ok_bindMono]
      rw [show (q + (encVarNat 1).length + 1) - q = (encVarNat 1).length + 1
        from by omega,
        suffixAt, List.cons_append, List.nil_append, dropAppendSucc]
      rw [ih]
      simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq,
        foldlMap_cons_len, List.map_cons, List.cons_append, List.nil_append,
        List.length_append, List.length_singleton]
      rw [foldlApp_nil_cons (encVarNat 1 ++ [encodeValType t])
        (List.map (fun t => encVarNat 1 ++ [encodeValType t]) ts)]
      simp only [List.length_append, List.length_singleton]
      exact ⟨trivial, by omega⟩

/-- ONE code entry: the locals' fold + the body + the `0x0B`, with the
    entry's exact-length check passing (the count-discipline check is
    `q2 - pos = sz` — the decoder's own shape tooth). -/
theorem decCodeSec_goEntry_enc (fuel : Nat) (f : Func) (pos : Nat) (sz : Nat)
    (tail : List UInt8)
    (hsz : sz = (encVarNat f.locals.length).length
      + (List.foldl (· ++ ·) []
        (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))).length
      + (encodeBody f.body).length + 1)
    (hbody : bodyFrag f.body) (hfuel : lSize f.body + 2 ≤ fuel) :
    decCodeSec.goEntry fuel pos sz
        (encVarNat f.locals.length
          ++ (List.foldl (· ++ ·) []
            (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
            ++ (encodeBody f.body ++ (0x0B :: tail))))
      = .ok ((f.locals, lImage f.body), pos + sz) := by
  subst hsz
  simp only [decCodeSec.goEntry]
  rw [decVarNatR_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + (encVarNat f.locals.length).length) - pos
    = (encVarNat f.locals.length).length from by omega,
    suffixAt, dropAppendLen]
  rw [decCodeSec_goLocals_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + (encVarNat f.locals.length).length
      + (List.foldl (· ++ ·) []
        (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))).length) - pos
    = (encVarNat f.locals.length).length
      + (List.foldl (· ++ ·) []
        (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))).length
    from by omega,
    suffixAt, dropAppendSucc2, dropAppendLen]
  rw [decBody_enc f.body fuel _ tail hfuel]
  simp only [Except.ok_bindMono]
  split
  · simp only [Except.ok.injEq, Prod.mk.injEq]
    first | omega | exact ⟨trivial, by omega⟩
  · omega

/-- THE FUNDING LEMMA: one entry's bytes always exceed the body's
    count-discipline bound by two (the length prefix + the locals
    prefix + the `0x0B`) — the code-slot's fuel faces it. -/
theorem encodeFuncEntry_ge (f : Func) :
    lSize f.body + 2 ≤ (encodeFuncEntry f).length := by
  have h5 : (encodeFuncEntry f).length
      = (encVarNat (List.length (encVarNat f.locals.length
        ++ List.foldl (· ++ ·) []
          (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
        ++ (encodeBody f.body ++ [0x0B])))).length
    + List.length (encVarNat f.locals.length
      ++ List.foldl (· ++ ·) []
        (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
      ++ (encodeBody f.body ++ [0x0B])) := by
    simp only [encodeFuncEntry, List.length_append]
  rw [h5]
  have h6 : List.length (encVarNat f.locals.length
      ++ List.foldl (· ++ ·) []
        (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
      ++ (encodeBody f.body ++ [0x0B]))
    = (encVarNat f.locals.length).length
      + (List.foldl (· ++ ·) []
        (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))).length
      + (encodeBody f.body).length + 1 := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [h6]
  have h3 := lSize_le_len f.body
  have h4 := encVarNat_pos f.locals.length
  omega

/-- The code-section's entry fold — the fuel-funded entries. -/
theorem decCodeSec_go_enc (fuel : Nat) : ∀ (fs : List Func) (pos : Nat) (tail : List UInt8),
    (∀ f ∈ fs, bodyFrag f.body) → (∀ f ∈ fs, lSize f.body + 2 ≤ fuel) →
    decCodeSec.go fuel fs.length pos
        (List.foldl (· ++ ·) [] (fs.map encodeFuncEntry) ++ tail)
      = .ok (fs.map (fun f => (f.locals, f.body)),
          pos + (List.foldl (· ++ ·) [] (fs.map encodeFuncEntry)).length) := by
  intro fs
  induction fs with
  | nil => intro pos tail _ _; simp [decCodeSec.go]
  | cons f fs ih =>
      intro pos tail hbody hfuel
      have hmem : f ∈ f :: fs := List.mem_cons_self
      have hmem' : ∀ g ∈ fs, bodyFrag g.body := fun g hg =>
        hbody g (List.mem_cons_of_mem f hg)
      have hfuel' : ∀ g ∈ fs, lSize g.body + 2 ≤ fuel := fun g hg =>
        hfuel g (List.mem_cons_of_mem f hg)
      have hfb : bodyFrag f.body := hbody f hmem
      have hff : lSize f.body + 2 ≤ fuel := hfuel f hmem
      rw [foldlMap_cons encodeFuncEntry f fs tail]
      simp only [List.length_cons, decCodeSec.go, List.map_cons]
      rw [foldlTyEntry_len]
      simp only [encodeFuncEntry, List.append_assoc, List.cons_append,
        List.nil_append]
      rw [decVarNatR_enc]
      simp only [Except.ok_bindMono, Nat.add_sub_cancel_left, suffixAt,
        dropAppendLen]
      rw [if_neg (by simp only [List.length_append, List.length_cons,
        List.length_nil]; omega)]
      rw [decCodeSec_goEntry_enc fuel f (pos + (encVarNat
          (List.length (encVarNat f.locals.length
            ++ (List.foldl (· ++ ·) []
              (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
            ++ (encodeBody f.body ++ [0x0B]))))).length)
        (List.length (encVarNat f.locals.length
          ++ (List.foldl (· ++ ·) []
            (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
          ++ (encodeBody f.body ++ [0x0B]))))
        (List.foldl (· ++ ·) [] (List.map encodeFuncEntry fs) ++ tail)
        (by simp only [List.length_append, List.length_singleton]; omega) hfb hff]
      simp only [Except.ok_bindMono, List.append_assoc, List.cons_append,
        List.nil_append]
      have hAmt : ((pos + (encVarNat (List.length (encVarNat f.locals.length
              ++ (List.foldl (· ++ ·) []
                (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
              ++ (encodeBody f.body ++ [0x0B]))))).length + (List.length (encVarNat f.locals.length
              ++ (List.foldl (· ++ ·) []
                (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
              ++ (encodeBody f.body ++ [0x0B]))))) - (pos + (encVarNat (List.length (encVarNat f.locals.length
              ++ (List.foldl (· ++ ·) []
                (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
              ++ (encodeBody f.body ++ [0x0B]))))).length)) = (List.length (encVarNat f.locals.length
              ++ (List.foldl (· ++ ·) []
                (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
              ++ (encodeBody f.body ++ [0x0B])))) := by
        omega
      have hdrop : List.drop (List.length (encVarNat f.locals.length
              ++ (List.foldl (· ++ ·) []
                (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
              ++ (encodeBody f.body ++ [0x0B]))))
          (encVarNat f.locals.length
            ++ (List.foldl (· ++ ·) []
              (f.locals.map (fun t => encVarNat 1 ++ [encodeValType t]))
            ++ (encodeBody f.body ++ (0x0B ::
              (List.foldl (· ++ ·) [] (List.map encodeFuncEntry fs) ++ tail)))))
        = List.foldl (· ++ ·) [] (List.map encodeFuncEntry fs) ++ tail := by
        rw [List.length_append, dropAppendSucc2, List.length_append,
          dropAppendSucc2, List.length_append, List.length_singleton,
          dropAppendSucc2]
        simp
      rw [hAmt, hdrop, ih _ tail hmem' hfuel', lImage_self f.body hfb]
      simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq,
        List.length_append, Nat.add_assoc]

/-- THE CODE SLOT: the body-count discipline's fuel is the
    section-content byte count (the off-by-one defeat funded). -/
theorem decCodeSec_enc (acc : DecAcc) (fs : List Func) (pos : Nat) (tail : List UInt8)
    (hbody : ∀ f ∈ fs, bodyFrag f.body) :
    decCodeSec acc pos
        ((encVarNat fs.length ++ List.foldl (· ++ ·) [] (fs.map encodeFuncEntry)) ++ tail)
      = .ok ({ acc with code := fs.map (fun f => (f.locals, f.body)) },
          pos + (encVarNat fs.length).length
            + (List.foldl (· ++ ·) [] (fs.map encodeFuncEntry)).length) := by
  simp only [decCodeSec, List.append_assoc]
  rw [decVarNatR_enc]
  simp only [Except.ok_bindMono]
  rw [show (pos + (encVarNat fs.length).length) - pos = (encVarNat fs.length).length
    from by omega,
    suffixAt, dropAppendLen]
  have hfuel : ∀ f ∈ fs, lSize f.body + 2 ≤
      (List.foldl (· ++ ·) [] (List.map encodeFuncEntry fs) ++ tail).length := by
    intro f hmem
    have h1 := foldlMap_len_ge encodeFuncEntry fs f hmem
    have h2 := encodeFuncEntry_ge f
    simp only [List.length_append] at h1 ⊢
    omega
  rw [decCodeSec_go_enc _ fs (pos + (encVarNat fs.length).length) tail hbody
    (fun f hmem => hfuel f hmem)]
  simp only [Except.ok_bindMono, Except.ok.injEq, Prod.mk.injEq, List.length_append]

/-- THE MODULE DECODER: the preamble, then the seven fixed-order
    section slots (each: id, length, content, full consumption), then
    the cross-section ties, then nothing may remain. -/
def decodeModule (bs : List UInt8) : Except DecodeError (Module × Nat) :=
  match bs with
  | 0x00 :: 0x61 :: 0x73 :: 0x6D :: 0x01 :: 0x00 :: 0x00 :: 0x00 :: bs0 =>
      (do
        let (a1, p1) ← decSection 1 decTypeSec {} 8 bs0
        let (a2, p2) ← decSection 3 decFuncSec a1 p1 (suffixAt bs0 (p1 - 8))
        let (a3, p3) ← decSection 4 decTableSec a2 p2 (suffixAt bs0 (p2 - 8))
        let (a4, p4) ← decSection 5 decMemSec a3 p3 (suffixAt bs0 (p3 - 8))
        let (a5, p5) ← decSection 7 decExportSec a4 p4 (suffixAt bs0 (p4 - 8))
        let (a6, p6) ← decSection 9 decElemSec a5 p5 (suffixAt bs0 (p5 - 8))
        let (a7, p7) ← decSection 10 decCodeSec a6 p6 (suffixAt bs0 (p6 - 8))
        match suffixAt bs0 (p7 - 8) with
        | [] =>
            let m ← assembleAcc a7 p7
            .ok (m, bs.length)
        | b :: _ => .error (.sectionOrder p7 b))
  | 0x00 :: 0x61 :: 0x73 :: 0x6D :: _ => .error (.badVersion 4)
  | _ => .error (.badMagic 0)

end WasmCore.Decode
