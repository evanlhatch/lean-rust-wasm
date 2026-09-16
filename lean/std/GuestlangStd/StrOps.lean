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

This module stays core-only (CodegenCore.GuestGate alone) so the
backend can import it without the schema-lang closure.
-/

namespace GuestlangStd

/-- The guest stdlib intrinsics — the CLOSED set. -/
inductive Intrinsic
  | strlen
  | strcat
  deriving DecidableEq, Repr

/-- The runtime primitive spellings — the ONE place they exist (the
    emitted `call $string_len` / `call $string_cat` resolve to the
    spliced runtime's primitives over the guest string layout
    `{rc@0, tag=250@4, len u32@8, bytes@16}`). -/
def Intrinsic.runtimeName : Intrinsic → String
  | .strlen => "string_len"
  | .strcat => "string_cat"

/-- The wasm result type of the intrinsic's call (the IMPL convention:
    UInt64 = raw i64; String = object pointer i32). -/
def Intrinsic.resultWasmTy : Intrinsic → String
  | .strlen => "i64"
  | .strcat => "i32"

/-- The Lean declaration names denoting each intrinsic — includes the
    schema-root `SchemaLang.string_len` (the raw evaluator's
    `call $string_len` wire-up contract; a name LITERAL only, this
    module never imports schema-lang). Both the Lean names and the
    runtime names derive from this ONE inductive — no string mirror. -/
def Intrinsic.ofName? : Lean.Name → Option Intrinsic
  | `GuestlangStd.strlen => some .strlen
  | `SchemaLang.string_len => some .strlen
  | `GuestlangStd.strcat => some .strcat
  | _ => none

/-- Byte length of a string. Real body = the oracle; the backend emits
    `call $string_len` for the NAME (the body is never compiled). -/
@[guest_std]
def strlen (s : String) : UInt64 := s.length.toUInt64

/-- Concatenation: allocates a fresh string object, copies both byte
    runs (`memory.copy`). Real body = the oracle. -/
@[guest_std]
def strcat (a b : String) : String := a ++ b

end GuestlangStd
