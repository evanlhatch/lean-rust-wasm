/-
# Guest.Std.StrOps — the string intrinsics: ONE closed universe

Ported from `legacy/lean/std/GuestlangStd/StrOps.lean` — the INTENT
fresh, over this tree's `LintKit.GuestGate` (the `@[guest_std]`
elaboration-time gate; pattern #13). The std OPS have REAL Lean bodies —
they are the differential ORACLE (the compiled side must compute the
same answers). The BACKEND never compiles these bodies: it special-cases
the NAMES as intrinsics (the `runtime.wat` primitives over the guest
string layout `{rc@0, tag=250@4, len u32@8, bytes@16}`) — the standard
compiler practice for intrinsic ops. In THIS slice no backend intrinsic
mapping has landed, so the lowering REFUSES the string faps loudly
(the honest boundary — pinned as a refusal tooth in GuestStdTests); the
oracle bodies + the closed universe are the std's seed.

Guest strings are BYTE-strings: `$string_len` counts bytes, which equals
Lean's `String.length` (chars) on ASCII — the oracle rows are ASCII-only
(non-ASCII byte/char divergence is documented, v1).

Cedar's ExtFun pattern (notes/studies/cedar-study.md C1): ONE closed
inductive + total metadata folds (`ofName?`/`runtimeName`/
`resultWasmTy`) — every consumer folds the same constructors; adding an
intrinsic = one ctor, and exhaustiveness forces every consumer.

`@[guest_std]` (not `@[guest]`): the std surface — String is legal
here (the ban's std level); the strict app surface stays string-free.
Every wrapper's mark is checked at ELABORATION (`LintKit.GuestGate`):
a banned runtime in a marked def fails `lake build` at the decl.

The five questions (notes/v3/01-core.md):
- root: none — the guest std's string surface (Universe content: pure
  functions over core types).
- carrier grade: none — the oracle bodies are plain defs.
- spine reading: the intrinsics' oracle semantics; the compiled lane
  reads the NAMES (the backend's manifest fold — the mark registry).
- ladder rung: n/a (no obligations beyond the elaboration gate).
- gate row: `GuestStd`'s row in Gates.Packages (the guest-mark
  registry replays from the oleans — the consumers pin it).

This module stays core-only (LintKit.GuestGate alone) so the backend
can import it without any domain-core closure.
-/

import LintKit.GuestGate

namespace GuestStd

/-- The guest stdlib intrinsics — the CLOSED set. -/
inductive Intrinsic where
  | strlen
  | strcat
  | streq
  | strof
  deriving DecidableEq, Repr, BEq

instance : ToString Intrinsic where
  toString
    | .strlen => "strlen"
    | .strcat => "strcat"
    | .streq => "streq"
    | .strof => "strof"

instance : ToString (Option Intrinsic) where
  toString
    | none => "none"
    | some i => s!"some {toString i}"

/-- The runtime primitive spellings — the ONE place they exist (the
    emitted `call $string_len` / `call $string_cat` resolve to the
    runtime's primitives over the guest string layout). -/
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
  -- Bool = the raw i32 scalar convention
  | .streq => "i32"
  | .strof => "i32"

/-- The Lean declaration names denoting each intrinsic — including the
    LCNF spellings a string `==` compiles to (`String.decEq`, the BEq
    instance projection) and the decode lane's `String.ofList`. Both
    the Lean names and the runtime names derive from this ONE
    inductive — no string mirror. (The legacy's `SchemaLang.string_len`
    row re-lands when this tree's schema evaluator consumes the name.) -/
def Intrinsic.ofName? : Lean.Name → Option Intrinsic
  | `GuestStd.strlen => some .strlen
  | `GuestStd.strcat => some .strcat
  | `GuestStd.streq => some .streq
  | `String.decEq => some .streq
  | `instBEqString.beq => some .streq
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

/-- String equality (`a == b`): the guest lowering is the runtime's
    `$string_eq` — length check then a byte-wise walk over the inline
    bytes. Real body = the oracle; the backend emits `call $string_eq`
    for the NAME. LCNF sites reach this intrinsic under the callers'
    spellings (`String.decEq`, the BEq projection) — see `ofName?`. -/
@[guest_std]
def streq (a b : String) : Bool := a == b

/-- String construction from a char list (`String.ofList` — the decode
    lane's atom): the guest lowering is the runtime's `$string_oflist` —
    walk the cons chain of boxed chars (u32 payload), UTF-8-encode each
    codepoint into the string object's inline bytes, tag = 250, len @8.
    Real body = the oracle; the backend emits `call $string_oflist` for
    the NAME. -/
@[guest_std]
def strof (cs : List Char) : String := String.ofList cs

/-! ## The oracle laws (the property pins, level 0: the definitional face) -/

/-- The length oracle IS Lean's char length (the ASCII byte-tie, v1). -/
theorem strlen_eq_length (s : String) : strlen s = s.length.toUInt64 := rfl

/-- The concat oracle IS Lean's append. -/
theorem strcat_eq_append (a b : String) : strcat a b = a ++ b := rfl

/-- The equality oracle IS Lean's string BEq. -/
theorem streq_eq_beq (a b : String) : streq a b = (a == b) := rfl

/-- The of-list oracle IS Lean's `String.ofList`. -/
theorem strof_eq_ofList (cs : List Char) : strof cs = String.ofList cs := rfl

/-- The length oracle's concat law (the differential duel's invariant:
    `strlen (strcat a b) = strlen a + strlen b` — char face; bytes
    agree on ASCII, the v1 stance). The u64 arithmetic wraps mod 2⁶⁴
    exactly as the cast does — the law is premise-free. -/
theorem strlen_strcat (a b : String) :
    strlen (strcat a b) = strlen a + strlen b :=
  UInt64.toNat.inj (by
    simp [strcat_eq_append, strlen_eq_length, String.length_append])

end GuestStd
