/-
# WasmCoreTests — the seed's test battery

Per module: the positive pins + the MANDATORY negative controls
(15-patterns #5). The sweep discipline is TestKit's LCG tape
(15-patterns #14): same seed, byte-identical replay.

1. The LEB128 codec sweep: the append-form law (pattern #2) over
   LCG-drawn 4-byte values + drawn suffixes; the negative controls are
   the sabotaged encoder (truncation) and the naive decoder (accepts
   the redundant zero group the canonical decoder refuses).
2. The golden byte-tie: ONE tiny module pinned BYTE-EXACT (type,
   function, export, code sections); the negative controls are
   tampered modules whose encodings must NOT tie.
3. The validator: the stack-balanced positives accepted (straight-
   line, a call, locals); the negative controls are a stack-unbalanced
   function (REFUSED) and an operand-type mismatch (REFUSED).

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the laws — the core-triple-only surface or the build fails.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import WasmCore
import Kit.Varint
import TestKit.Lcg
import TestKit.Spec
import TestKit.Harness
import WasmCoreTests.Axioms

open WasmCore
open Kit.Varint
open TestKit

/-! ## Fixtures — LEB128 -/

/-- The sabotaged encoder: truncates to the low 7 bits, one byte. -/
def badUleb (n : Nat) : List UInt8 := [(n % 128).toUInt8]

/-- The naive decoder: no canonicality check (accepts the redundant
    zero group). -/
def badDec : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
      if b.toNat < 128 then some (b.toNat, rest)
      else
        match badDec rest with
        | none => none
        | some (v, tail) => some (b.toNat % 128 + 128 * v, tail)

/-- Draw a 4-byte value + a 0..2-byte suffix; the append-form law must
    hold exactly. -/
def lebProp : Tape → CheckResult := fun t =>
  let (b0, t1) := t.byte
  let (b1, t2) := t1.byte
  let (b2, t3) := t2.byte
  let (b3, t4) := t3.byte
  let n := b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216
  let (k, t5) := t4.below 3
  let (r0, t6) := t5.byte
  let (r1, _) := t6.byte
  let rest := ([r0.toUInt8, r1.toUInt8]).take k
  assert (decVarNat? (encVarNat n ++ rest) == some (n, rest))
    s!"append-form law failed for n = {n} (rest length {k})"

/-- Control 1: the truncated encoder must NOT round-trip (caught
    whenever the drawn value exceeds 7 bits). -/
def lebNegTruncate : Tape → CheckResult := fun t =>
  let (b0, t1) := t.byte
  let (b1, _) := t1.byte
  let n := b0.toNat + b1.toNat * 256
  assert ((decVarNat? (badUleb n)).map (fun p => p.1) == some n)
    s!"control fired: truncated encoding round-trips for {n}"

/-- Control 2: the canonical decoder REFUSES the redundant zero group
    (0x81 0x00 = a non-minimal 1); the naive decoder's acceptance is
    the documented policy gap. -/
def lebNegRedundant : Tape → CheckResult := fun _ =>
  assert (decVarNat? [0x81, 0x00] != none) "control fired: the redundant zero group was refused"

def lebSpec : Spec :=
  Spec.ofList "LEB128 append-form round trip (drawn 4-byte values)"
    lebProp
    [ ("truncated encoder", lebNegTruncate)
    , ("redundant zero group accepted", lebNegRedundant) ]
    64 42

/-! ## Fixtures — the golden module -/

/-- The golden module: one type `() -> i64`, one function
    (`i64.const 42`), exported as `"answer"`. -/
def goldenModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [.i64const 42]⟩]
  exports := [{ name := "answer", desc := .func 0 }]

/-- The golden bytes — the module above, pinned byte-exact. -/
def goldenBytes : List UInt8 :=
  [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00,   -- magic + version
   0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7E,          -- type section
   0x03, 0x02, 0x01, 0x00,                            -- function section
   0x07, 0x0A, 0x01, 0x06, 0x61, 0x6E, 0x73, 0x77, 0x65, 0x72, 0x00, 0x00, -- export
   0x0A, 0x06, 0x01, 0x04, 0x00, 0x42, 0x2A, 0x0B]    -- code section

def bytesS (l : List UInt8) : String :=
  String.intercalate " " (l.map (fun b => toString b.toNat))

def goldenProp : Tape → CheckResult := fun _ =>
  let got := encodeModule goldenModule
  assert (got == goldenBytes) s!"byte-tie mismatch: got {bytesS got}"

/-- Control: a tampered constant must not tie. -/
def goldenNegConst : Tape → CheckResult := fun _ =>
  let tampered : Module := { goldenModule with
    funcs := [⟨0, [], [.i64const 43]⟩] }
  assert (encodeModule tampered == goldenBytes) "control fired: tampered const tied"

/-- Control: a tampered export name must not tie. -/
def goldenNegExport : Tape → CheckResult := fun _ =>
  let tampered : Module := { goldenModule with
    exports := [{ name := "Answer", desc := .func 0 }] }
  assert (encodeModule tampered == goldenBytes) "control fired: tampered export tied"

def goldenSpec : Spec :=
  Spec.ofList "the golden module byte-tie" goldenProp
    [ ("tampered const", goldenNegConst)
    , ("tampered export name", goldenNegExport) ]
    1 42

/-! ## Fixtures — the validator -/

/-- The good module: a straight-line function, a caller, and a
    locals-using function; all signatures stack-balanced. -/
def goodModule : Module where
  types := [⟨[], [.i64]⟩, ⟨[.i32], []⟩]
  funcs :=
    [ ⟨0, [], [.i64const 42]⟩
    , ⟨0, [], [.call 0]⟩
    , ⟨1, [.i32], [.localget 0, .drop]⟩ ]
  exports := []

/-- NEGATIVE: the body leaves a value the signature does not declare —
    stack-unbalanced, REFUSED. -/
def unbalancedModule : Module where
  types := [⟨[], []⟩]
  funcs := [⟨0, [], [.i64const 42]⟩]
  exports := []

/-- NEGATIVE: i32.add on i64 operands — operand-type mismatch, REFUSED. -/
def mismatchModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [.i64const 1, .i64const 2, .op .i32add]⟩]
  exports := []

def checkOk (m : Module) : Bool :=
  match checkModule m with
  | .ok () => true
  | .error _ => false

def validateProp : Tape → CheckResult := fun _ =>
  assert (checkOk goodModule) "the good module was refused"

/-- Control: the unbalanced function must be REFUSED (the control
    asserts acceptance, so it is caught). -/
def validateNegUnbalanced : Tape → CheckResult := fun _ =>
  assert (checkOk unbalancedModule) "control fired: the unbalanced function was accepted"

/-- Control: the mismatched operand must be REFUSED. -/
def validateNegMismatch : Tape → CheckResult := fun _ =>
  assert (checkOk mismatchModule) "control fired: the type-mismatched function was accepted"

def validateSpec : Spec :=
  Spec.ofList "stack-balance validation (balanced accepted)"
    validateProp
    [ ("stack-unbalanced refused", validateNegUnbalanced)
    , ("operand-type mismatch refused", validateNegMismatch) ]
    1 42

/-! ### The ONE op table's sig pins (the drift-guard) -/

/-- The sig rows the battery relies on, pinned literally: the binop row
    (the mismatch control), the comparison row, both conversion rows,
    a load row and a store row. Full-closure coverage is compile-time —
    the exhaustive `opSig`/`memSig` matches + `opSig_covers`/
    `memSig_covers` (the decide over the closed universe); here we pin
    the type content the golden and negative controls expect. -/
def sigPinProp : Tape → CheckResult := fun _ => do
  assert (opSig .i32add == ([.i32, .i32], [.i32])) "i32add sig drifted"
  assert (opSig .i64eq == ([.i64, .i64], [.i32])) "i64eq sig drifted"
  assert (opSig .i32wrapi64 == ([.i64], [.i32])) "i32wrapi64 sig drifted"
  assert (opSig .i64extendi32u == ([.i32], [.i64])) "i64extendi32u sig drifted"
  assert (memSig .i32load == ([.i32], [.i32])) "i32load sig drifted"
  assert (memSig .i32store == ([.i32, .i32], [])) "i32store sig drifted"

def sigSpec : Spec :=
  Spec.ofList "the ONE op table's sig pins" sigPinProp
    [ ("drifted binop sig", fun _ =>
        assert (opSig .i32add == ([.i32], [.i32]))
          "control fired: the drifted i32add sig was accepted")
    , ("drifted load sig", fun _ =>
        assert (memSig .i32load == ([.i32], [.i64]))
          "control fired: the drifted i32load sig was accepted") ]
    1 42

/-! ## The driver -/

def main : IO UInt32 :=
  mainOfSuites
    [ ("WasmCore.Encode/LEB128", [lebSpec])
    , ("WasmCore.Encode/golden", [goldenSpec])
    , ("WasmCore.Validate", [validateSpec])
    , ("WasmCore.Validate/sig-pins", [sigSpec]) ]
