import CodegenCore.GuestGate
/-
# GuestlangStd.StrOps — the string intrinsics: ONE closed universe

Cedar's ExtFun pattern (notes/studies/cedar-study.md C1): ONE closed
inductive + total metadata folds (`ofName?`/`runtimeName`/
`resultWasmTy`) — every consumer (the wasm backend's emit arm, the
manifest fold) folds the same constructors; adding an intrinsic = one
ctor, and exhaustiveness forces every consumer. The named wrappers
(`strlen`/`strcat`) keep the existing signatures/usages AND the
oracle bodies verbatim.

The wrappers own the bodies: LCNF's inlineDefs unfolds the tiny
wrapper bodies and constant-folds `String.append` on literal
arguments — the baseline WAT has ZERO `call $string_cat` (every demo
strcat site folds to a string constant). The emitted bytes are pinned
(W6.10 is byte-invariant).

W9.6 unblocking (the checker audit's gap 3): `streq` — equality over
the guest string model. `ofName?` ALSO maps the LCNF spellings a
string `==` compiles to (`String.decEq`, and the BEq instance
projection) so the backend's `call String.decEq` sites lower to
`$string_eq` instead of an undefined wasm function. Byte-wise compare
over the guest layout (len@8, bytes@16) — same ASCII stance as
`$string_len` (byte-length ≠ char-length off ASCII).

This module stays core-only (CodegenCore.GuestGate alone) so the
backend can import it without the schema-lang closure.
-/

namespace GuestlangStd

/-- The guest stdlib intrinsics — the CLOSED set. -/
inductive Intrinsic
  | strlen
  | strcat
  | streq
  | strof
  deriving DecidableEq, Repr

/-- The runtime primitive spellings — the ONE place they exist (the
    emitted `call $string_len` / `call $string_cat` resolve to the
    spliced runtime's primitives over the guest string layout
    `{rc@0, tag=250@4, len u32@8, bytes@16}`). -/
def Intrinsic.runtimeName : Intrinsic → String
  | .strlen => "string_len"
  | .strcat => "string_cat"
  | .streq => "string_eq"
  | .strof => "string_oflist"

/-- The wasm result type of the intrinsic's call (the IMPL convention:
    UInt64 = raw i64; String = object pointer i32). -/
def Intrinsic.resultWasmTy : Intrinsic → String
  | .strlen => "i64"
  | .strcat => "i32"
  -- Bool = the raw i32 scalar convention (wasmTyOf?: Bool → i32)
  | .streq => "i32"
  | .strof => "i32"

/-- The Lean declaration names denoting each intrinsic — includes the
    schema-root `SchemaLang.string_len` (the raw evaluator's
    `call $string_len` wire-up contract; a name LITERAL only, this
    module never imports schema-lang). Both the Lean names and the
    runtime names derive from this ONE inductive — no string mirror. -/
def Intrinsic.ofName? : Lean.Name → Option Intrinsic
  | `GuestlangStd.strlen => some .strlen
  | `SchemaLang.string_len => some .strlen
  | `GuestlangStd.strcat => some .strcat
  | `GuestlangStd.streq => some .streq
  -- the spellings a string `==` compiles to (the W9.6 audit observed
  -- the backend emitting `call String.decEq` — an undefined wasm
  -- function): the decidable-equality fap, plus the BEq instance
  -- projection specialization may name
  | `String.decEq => some .streq
  | `instBEqString.beq => some .streq
  -- the W9.6 decode lane: `String.ofList` — the codec's string atom
  -- decodes a char LIST (`Codec.decString?`); the guest's char rides
  -- the boxed-u32 model (Char = the boxed scalar, u32 payload @8), the
  -- primitive walks the cons chain and UTF-8-encodes each codepoint.
  | `String.ofList => some .strof
  | _ => none

/-- Byte length of a string. Real body = the oracle; the backend emits
    `call $string_len` for the NAME (the body is never compiled). -/
@[guest_std]
def strlen (s : String) : UInt64 := s.length.toUInt64

/-- Concatenation: allocates a fresh string object, copies both byte
    runs (`memory.copy`). Real body = the oracle. -/
@[guest_std]
def strcat (a b : String) : String := a ++ b

/-- String equality (`decide (a = b)`): the guest lowering is the
    runtime's `$string_eq` — length check then a byte-wise walk over
    the inline bytes (@16..). Real body = the oracle; the backend
    emits `call $string_eq` for the NAME (this body is never
    compiled). LCNF sites reach this intrinsic under the callers'
    spellings (`String.decEq`, the BEq projection) — see `ofName?`. -/
@[guest_std]
def streq (a b : String) : Bool := a == b

/-- String construction from a char list (`String.ofList` — the codec
    decode lane's atom): the guest lowering is the runtime's
    `$string_oflist` — walk the cons chain of boxed chars (u32 payload
    @8), UTF-8-encode each codepoint into the string object's inline
    bytes (@16..), tag = 250, len @8. Real body = the oracle; the
    backend emits `call $string_oflist` for the NAME (this body is
    never compiled). The CHAR model: the LCNF boxes each `Char` (the
    single-u32-field structure erases to its scalar — the decChar?
    x-ray), so the primitive reads boxed u32s, never Char objects. -/
@[guest_std]
def strof (cs : List Char) : String := String.ofList cs

end GuestlangStd
