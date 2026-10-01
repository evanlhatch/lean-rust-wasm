/-
# WasmCoreTests.Decode — the binary decoder's battery (F4's teeth)

The positioned varint readers + the structured refusals: the round-trip
sweeps (LCG tape, #14), the corruption controls (truncation/mutation
refuse), the non-minimal varint/sleb refusals (the wave's
canonicality discipline on the read side), and the refusal-rendering
pin (the ONE Diag envelope's WD family).

THE DECLARED BOUNDARY (WasmCore.Decode's header): the sleb's
round-trip THEOREM and the module-level decoder are the named
remainder — this suite is their runtime-tested discipline (the
`Slice.lean` precedent), never a silent gap.
-/

import WasmCore.Decode
import WasmCore.Duel
import WasmCore.Encode
import WasmCore.Validate
import TestingKit.Lcg
import TestingKit.Spec
import WasmCoreTests.Axioms

open WasmCore
open WasmCore.Decode
open WasmCore.Duel (duelFamily)
open Kit.Varint
open TestingKit

/-- The APPEND-FORM RE-DERIVATION (the `shrinkerDpair` shape): the
    suffix is a FUNCTION of the drawn value — `n % 3` bytes spelling
    `n`'s low bytes — so the prop's content is a function of `n`
    ALONE and the shrink attachment's `fails` is tape-free. Shrinking
    `n` re-derives the rest jointly, or not at all. -/
def restOf (n : Nat) : List UInt8 :=
  (List.range (n % 3)).map (fun i => ((n + i) % 256).toUInt8)

/-! ## Fixtures — the positioned unsigned varint -/

/-- The append-form law over drawn 4-byte values (the Kit.Varint
    sweep's positioned twin). -/
def varintProp : Tape → CheckResult := fun t =>
  let (b0, t1) := t.byte
  let (b1, t2) := t1.byte
  let (b2, t3) := t2.byte
  let (b3, _) := t3.byte
  let n := b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216
  match decVarNatR 0 (encVarNat n ++ restOf n) with
  | .ok (v, p) =>
      assert (v == n && p == (encVarNat n).length)
        s!"positioned append-form law failed for n = {n}"
  | .error e =>
      assert false s!"positioned append-form law refused n = {n}: {repr e}"
def varintNegTruncated : Tape → CheckResult := fun _ =>

  assert (match decVarNatR 0 [] with | .ok _ => true | .error _ => false)
    "control fired: the truncated read was refused"

/-- CONTROL (the broken claim): the non-minimal LEB (the redundant
    zero group) is ACCEPTED. -/
def varintNegNonMinimal : Tape → CheckResult := fun _ =>
  assert (match decVarNatR 7 [0x81, 0x00] with | .ok _ => true | .error _ => false)
    "control fired: the non-minimal varint was refused"

/-- CONTROL (the broken claim): the CANONICAL one is REFUSED (the
    refusal is blanket strictness, not the exact image). -/
def varintPosCanonical : Tape → CheckResult := fun _ =>
  assert (match decVarNatR 7 [0x01] with | .ok _ => false | .error _ => true)
    "control fired: the canonical varint decoded"

/-! ## Fixtures — the positioned signed varint -/

/-- The sleb round trips over the 64-bit wire range's edges + samples:
    the sign-extension seams (-1, -64, -65, the type maxes/mins). -/
def slebSamples : List Int :=
  [0, 1, 63, 64, -1, -64, -65, 2147483647, -2147483648,
   9223372036854775807, -9223372036854775808]

def slebProp : Tape → CheckResult := fun _ =>
  let failures := slebSamples.filter fun v =>
    match decSlebR 0 (slebI v ++ [0xFF]) with
    | .ok (w, p) => !(w == v && p == (slebI v).length)
    | .error _ => true
  assert (failures.isEmpty)
    s!"the sleb round trip failed for {failures} (the declared-gap's runtime discipline)"

/-- CONTROL (the broken claim): the non-minimal sleb is ACCEPTED. -/
def slebNegNonMinimal : Tape → CheckResult := fun _ =>
  assert (match decSlebR 3 [0x80, 0x00] with | .ok _ => true | .error _ => false)
    "control fired: the non-minimal sleb was refused"

/-- CONTROL (the broken claim): the encoder's canonical two-group form
    (100's [0xE4, 0x00]) is REFUSED. -/
def slebPosCanonical : Tape → CheckResult := fun _ =>
  assert (match decSlebR 0 (slebI 100) with | .ok _ => false | .error _ => true)
    "control fired: the canonical sleb decoded"

/-! ## The refusal rendering (the ONE envelope's WD family) -/

def decodeRenderProp : Tape → CheckResult := fun _ =>
  let d := DecodeError.toDiag (.nonMinimalVarint 9)
  assert (d.code == DecodeError.ecNonMinimalVarint && d.got.isSome)
    "the refusal's envelope lost its E-code or payload"

/-- CONTROL (the broken claim): the varint refusal's E-code DRIFTED to
    the sleb kind (the kinds are indistinguishable). -/
def decodeRenderNegDrift : Tape → CheckResult := fun _ => do
  let d := DecodeError.toDiag (.nonMinimalVarint 9)
  assert (d.code == DecodeError.ecNonMinimalSleb)
    "control fired: the refusal kinds are distinguished"
  match decSlebR 3 [0x80, 0x00] with
  | .error (.nonMinimalVarint 3) =>
      assert false "unreachable: the drift pin above already failed"
  | .error _ => pure ()
  | .ok _ => pure ()

/-- The corruption control: a dangling continuation group (the wire's
    truncation shape) refuses with the structured error, never a panic
    — on BOTH readers (the mutation control's two faces). -/
def garbageRefusal : Tape → CheckResult := fun t =>
  let (b0, t1) := t.byte
  let (b1, _) := t1.byte
  let lead : UInt8 := (b0 % 256).toUInt8 ||| 0x80
  let cut : List UInt8 := [lead, (b1 % 256).toUInt8 ||| 0x80]
  match decVarNatR 0 cut, decSlebR 0 cut with
  | .error _, .error _ => pure ()
  | a, b => assert false
    s!"control fired: the truncated run decoded: {repr a} / {repr b}"

/-! ## The module-level battery (the round trip over the differential
    corpus's source modules + the corruption refusals) -/

/-- Every duel-family module (the differential corpus's source) decodes
    from its own encoding to ITSELF. -/
def moduleRoundTrip : Tape → CheckResult := fun _ =>
  let failures := duelFamily.filter fun (nm, m) =>
    match decodeModule (encodeModule m) with
    | .ok (m', _) => !(m' == m)
    | .error e => true
  assert failures.isEmpty
    s!"the module round trip failed for {failures.map (·.1)}"

/-- The decoded module re-encodes byte-identically (the canonicality
    face of the same sweep). -/
def moduleReencode : Tape → CheckResult := fun _ =>
  let failures := duelFamily.filter fun (nm, m) =>
    match decodeModule (encodeModule m) with
    | .ok (m', _) => encodeModule m' != encodeModule m
    | .error _ => true
  assert failures.isEmpty
    s!"the module re-encode drifted for {failures.map (·.1)}"

/-- The decoded module re-validates to the same verdict as the original
    (the validator's consumption, runtime face). -/
def moduleRevalidates : Tape → CheckResult := fun _ =>
  let failures := duelFamily.filter fun (nm, m) =>
    match decodeModule (encodeModule m) with
    | .ok (m', _) => (checkModule m').isOk != (checkModule m).isOk
    | .error _ => (checkModule m).isOk
  assert failures.isEmpty
    s!"the module re-validation drifted for {failures.map (·.1)}"

/-- CONTROL (the broken claim): a module truncated mid-section decodes. -/
def moduleNegTruncated : Tape → CheckResult := fun _ =>
  let m := (duelFamily.head!).2
  let full := encodeModule m
  assert (match decodeModule (full.take (full.length - 1)) with
    | .ok _ => true | .error _ => false)
    "control fired: the truncated module decoded"

/-- CONTROL (the broken claim): the magic flipped to garbage decodes. -/
def moduleNegMagic : Tape → CheckResult := fun _ =>
  let m := (duelFamily.head!).2
  let bad := (0x62 :: (encodeModule m).drop 1)
  assert (match decodeModule bad with | .ok _ => true | .error _ => false)
    "control fired: the corrupted preamble decoded"

/-- CONTROL (the broken claim): leftover bytes after the last section decode. -/
def moduleNegLeftover : Tape → CheckResult := fun _ =>
  let m := (duelFamily.head!).2
  let bad := encodeModule m ++ [0xFF]
  assert (match decodeModule bad with | .ok _ => true | .error _ => false)
    "control fired: the leftover bytes decoded"

def decodeModuleSpec : Spec :=
  Spec.ofList "the module decoder's round trip (F4's envelope)"
    (fun t => do
      moduleRoundTrip t
      moduleReencode t
      moduleRevalidates t)
    [ ("truncated module accepted", moduleNegTruncated)
    , ("corrupted preamble accepted", moduleNegMagic)
    , ("leftover bytes accepted", moduleNegLeftover) ]
    16 43

def decodeSpec : Spec :=
  Spec.ofList "the binary decoder's read discipline (F4's landed fragment)"
    (fun t => do
      varintProp t
      slebProp t
      decodeRenderProp t
      garbageRefusal t)
    [ ("truncated varint accepted", varintNegTruncated)
    , ("non-minimal varint accepted", varintNegNonMinimal)
    , ("canonical varint refused", varintPosCanonical)
    , ("non-minimal sleb accepted", slebNegNonMinimal)
    , ("canonical sleb refused", slebPosCanonical)
    , ("refusal kind drifted", decodeRenderNegDrift) ]
    32 42
