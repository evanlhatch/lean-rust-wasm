/-
# WasmCoreTests — the seed's test battery

Per module: the positive pins + the MANDATORY negative controls
(15-patterns #5). The sweep discipline is TestingKit's LCG tape
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
   function (REFUSED) and an operand-type mismatch (REFUSED). The
   error-kind teeth pin EVERY refusal kind's ctor + payload (the
   envelope discipline: errors are data, rendered into the ONE Diag
   via `ValidateError.toDiag` — the rendering pins + their controls
   ride the same suite).
4. The WAT renderer: the golden text tie (the module above's exact
   text + the emitter row's run — the test-pinned byte-tie, see
   WasmCore.Wat's header for the artifact-placement judgment) + the
   op-spelling sweep (every op/mem-op row renders its table name);
   the negative controls are the tampered offset (a string-baked
   renderer would tie — the legacy clobber bug), the empty else
   rendered, the drifted-spelling canary, and the flat structural
   form.
5. The BINARY LANE (WasmCore.Slice — the first committed binary
   artifact): the regen's bytes ARE the battery's pinned golden
   vector (the committed artifact's independent pin); the validator
   at generation REFUSES an invalid module (a generation failure,
   never an artifact); the byte-tie (`Kit.Emit.tieBytes`) ties the
   good triple, and its teeth catch the tampered artifact byte and
   the sidecar that does not name the fresh bytes' hash.

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the laws — the core-triple-only surface or the build fails.
Evidence, not architecture — the five-question block lives in the modules under test.
-/

import WasmCore
import Kit.Text
import Kit.Varint
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import WasmCoreTests.Axioms

open WasmCore
open Kit (Text)
open Kit.Varint
open TestingKit

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

/-! ### The error-kind teeth (the envelope discipline, 05 §4) -/

/-- The refusal as data: `none` = accepted. -/
def errOf (m : Module) : Option ValidateError :=
  match checkModule m with
  | .error e => some e
  | .ok () => none

/-- NEGATIVE fixture: `drop` on an empty stack — underflow. -/
def underflowModule : Module where
  types := [⟨[], []⟩]
  funcs := [⟨0, [], [.drop]⟩]
  exports := []

/-- NEGATIVE fixture: `local.set` of an i32 into an i64 local. -/
def localSetModule : Module where
  types := [⟨[], []⟩]
  funcs := [⟨0, [.i64], [.i32const 1, .localset 0]⟩]
  exports := []

/-- NEGATIVE fixture: a block leaving junk above its entry stack. -/
def frameModule : Module where
  types := [⟨[], []⟩]
  funcs := [⟨0, [], [.block [.i64const 1]]⟩]
  exports := []

/-- NEGATIVE fixture: `select` under i64 operands (neither live row). -/
def selectModule : Module where
  types := [⟨[], []⟩]
  funcs := [⟨0, [], [.i64const 1, .i64const 2, .i64const 3, .select]⟩]
  exports := []

/-- NEGATIVE fixture: `ret` with a stack that is not the results. -/
def retModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [.ret]⟩]
  exports := []

/-- NEGATIVE fixture: `local.get` of an undeclared index. -/
def unboundLocalModule : Module where
  types := [⟨[], []⟩]
  funcs := [⟨0, [], [.localget 9]⟩]
  exports := []

/-- NEGATIVE fixture: `call` of an index past the function section. -/
def unboundFuncModule : Module where
  types := [⟨[], []⟩]
  funcs := [⟨0, [], [.call 9]⟩]
  exports := []

/-- NEGATIVE fixture: a function whose type index is past the types. -/
def typeRangeModule : Module where
  types := []
  funcs := [⟨0, [], []⟩]
  exports := []

/-- Every refusal KIND fires with its exact ctor + payload (the
    atFunc wrapper pins the refusing function's index; the
    typeIndexRange refusal is module-level — it carries the index
    itself). -/
def teethProp : Tape → CheckResult := fun _ => do
  assert (errOf mismatchModule ==
    some (ValidateError.atFunc 0 (ValidateError.operandMismatch [.i32, .i32] [.i64, .i64])))
    "operandMismatch kind/payload drifted"
  assert (errOf underflowModule ==
    some (ValidateError.atFunc 0 (ValidateError.underflow 1)))
    "underflow kind/payload drifted"
  assert (errOf localSetModule ==
    some (ValidateError.atFunc 0 (ValidateError.localTypeMismatch 0 .i64 .i32)))
    "localTypeMismatch kind/payload drifted"
  assert (errOf frameModule ==
    some (ValidateError.atFunc 0 (ValidateError.frameMismatch [] [.i64])))
    "frameMismatch kind/payload drifted"
  assert (errOf selectModule ==
    some (ValidateError.atFunc 0 (ValidateError.selectOperands [.i64, .i64, .i64])))
    "selectOperands kind/payload drifted"
  assert (errOf retModule ==
    some (ValidateError.atFunc 0 (ValidateError.unbalancedReturn [.i64] [])))
    "unbalancedReturn kind/payload drifted"
  assert (errOf unbalancedModule ==
    some (ValidateError.atFunc 0 (ValidateError.unbalancedEnd [] [.i64])))
    "unbalancedEnd kind/payload drifted"
  assert (errOf unboundLocalModule ==
    some (ValidateError.atFunc 0 (ValidateError.unboundLocal 9)))
    "unboundLocal kind/payload drifted"
  assert (errOf unboundFuncModule ==
    some (ValidateError.atFunc 0 (ValidateError.unboundFunc 9)))
    "unboundFunc kind/payload drifted"
  assert (errOf typeRangeModule ==
    some (ValidateError.typeIndexRange 0 0))
    "typeIndexRange kind/payload drifted"

/-- Controls: the WRONG kind/payload must NOT fire (a kind conflation
    or a drifted payload is caught). -/
def teethSpec : Spec :=
  Spec.ofList "the error-kind teeth (every refusal kind + payload)"
    teethProp
    [ ("mismatch mislabeled underflow", fun _ =>
        assert (errOf mismatchModule ==
          some (ValidateError.atFunc 0 (ValidateError.underflow 1)))
          "control fired: the operand mismatch was reported as underflow")
    , ("drifted mismatch payload", fun _ =>
        assert (errOf mismatchModule ==
          some (ValidateError.atFunc 0 (ValidateError.operandMismatch [.i32] [.i64, .i64])))
          "control fired: the drifted mismatch payload was accepted")
    , ("frame junk accepted", fun _ =>
        assert (checkOk frameModule)
          "control fired: the frame mismatch was accepted") ]
    1 42

/-! ### The refusal rendering's shape pins (the ONE Diag envelope) -/

/-- The one-line envelope shape: E-code, severity, message, got,
    the atFunc context frame, the valid-space enumeration (the
    suggest field stays empty — no close match, no guess). -/
def renderProp : Tape → CheckResult := fun _ => do
  assert (ValidateError.render (ValidateError.operandMismatch [.i32, .i32] [.i64, .i64]) ==
    "[WV1001] error: operand type mismatch: the stack does not provide the \
      instruction's pops (got: [i64, i64]) — valid: a stack of the form [i32, i32] ++ ts")
    "operandMismatch rendering drifted"
  assert (ValidateError.render (ValidateError.unboundLocal 9) ==
    "[WV1008] error: unbound local 9 (got: local index 9)")
    "unboundLocal rendering drifted"
  assert (ValidateError.render (ValidateError.atFunc 0 (ValidateError.underflow 1)) ==
    "[WV1002] error: stack underflow: 1 operand(s) needed (got: []) [function 0] \
      — valid: a stack of at least 1 operand(s)")
    "atFunc context rendering drifted"
  assert (ValidateError.render (ValidateError.typeIndexRange 3 7) ==
    "[WV1010] error: function 3: type index 7 out of range (got: type index 7)")
    "typeIndexRange rendering drifted"

/-- Controls: a drifted severity or E-code must NOT render. -/
def renderSpec : Spec :=
  Spec.ofList "the refusal rendering pins (the ONE envelope's shape)"
    renderProp
    [ ("drifted severity", fun _ =>
        assert (ValidateError.render (ValidateError.unboundLocal 9) ==
          "[WV1008] warning: unbound local 9 (got: local index 9)")
          "control fired: the drifted severity rendering was accepted")
    , ("drifted E-code", fun _ =>
        assert (ValidateError.render (ValidateError.unboundLocal 9) ==
          "[WV0000] error: unbound local 9 (got: local index 9)")
          "control fired: the drifted E-code rendering was accepted") ]
    1 42

/-! ### The ONE op table's sig + opcode pins (the drift-guard) -/

/-- The sig + opcode rows the battery relies on, pinned literally:
    the binop row (the mismatch control), the comparison row, both
    conversion rows, a load row and a store row; the opcodes pinned
    THROUGH the encoder (`encodeInstr`) so the byte path is what's
    proven. Full-closure coverage is compile-time — the exhaustive
    `opRow`/`memRow` matches in `WasmCore.OpTable` + `opRow_wf`/
    `memRow_wf` + `opSig_covers`/`memSig_covers` (the decide over the
    closed universe); here we pin the content the golden and negative
    controls expect. -/
def sigPinProp : Tape → CheckResult := fun _ => do
  assert (opSig .i32add == ([.i32, .i32], [.i32])) "i32add sig drifted"
  assert (opSig .i64eq == ([.i64, .i64], [.i32])) "i64eq sig drifted"
  assert (opSig .i32wrapi64 == ([.i64], [.i32])) "i32wrapi64 sig drifted"
  assert (opSig .i64extendi32u == ([.i32], [.i64])) "i64extendi32u sig drifted"
  assert (memSig .i32load == ([.i32], [.i32])) "i32load sig drifted"
  assert (memSig .i32store == ([.i32, .i32], [])) "i32store sig drifted"
  assert (opName .i32add == "i32.add") "i32add name drifted"
  assert (encodeInstr (.op .i32add) == [0x6A]) "i32add opcode drifted"
  assert (encodeInstr (.op .i64shru) == [0x88]) "i64shru opcode drifted"
  assert (encodeInstr (.op .i64extendi32u) == [0xAD]) "i64extendi32u opcode drifted"
  assert ((encodeInstr (.mem .i32load 0 none)).head? == some 0x28) "i32load opcode drifted"
  assert ((encodeInstr (.mem .i64store8 0 (some 0))).head? == some 0x3B)
    "i64store8 opcode drifted"

def sigSpec : Spec :=
  Spec.ofList "the ONE op table's sig + opcode pins" sigPinProp
    [ ("drifted binop sig", fun _ =>
        assert (opSig .i32add == ([.i32], [.i32]))
          "control fired: the drifted i32add sig was accepted")
    , ("drifted load sig", fun _ =>
        assert (memSig .i32load == ([.i32], [.i64]))
          "control fired: the drifted i32load sig was accepted")
    , ("drifted opcode", fun _ =>
        assert (encodeInstr (.op .i32add) == [0x6B])
          "control fired: the drifted i32add opcode was accepted") ]
    1 42

/-! ## The WAT renderer (WasmCore.Wat) -/

-- The rendering's discipline (WasmCore.Wat's header): the op spellings
-- ride the ONE op table's `name` fold, the memarg fields render from
-- the DATA (never string-baked — the legacy clobber-bug note), the
-- block discipline nests from the AST's structure. The round-trip
-- boundary is honest: NO parse direction — the wasm toolchain is the
-- text consumer; the correspondences are Encode's byte-level codec
-- (the SAME module, the other face) + the golden text tie below.

/-- The golden WAT module: two types, a memory, an export, and two
    functions exercising every structural form (block/br_if, if/else,
    loop/br), the memarg discipline (elided zero offset; spelled
    explicit align; spelled nonzero offset), locals, calls, and the
    flat op/drop/select/return/unreachable forms. -/
def goldenWatModule : Module where
  types := [⟨[.i32], [.i64]⟩, ⟨[], []⟩]
  funcs :=
    [ ⟨0, [.i32], [ .localget 0, .i32const 4
                  , .mem .i32load 4 none
                  , .op .i32add
                  , .block [.brif 0]
                  , .i64const 7
                  , .if_ [.drop] [.drop]
                  , .op .i64extendi32u ]⟩
    , ⟨1, [.i64], [ .loop [ .i32const 0, .i32const 1
                         , .mem .i32store 0 (some 2)
                         , .call 0, .br 0 ]
                  , .i64const 9, .i64const 8, .select
                  , .localset 0, .localget 0, .localtee 0, .drop
                  , .unreach ]⟩ ]
  exports := [{ name := "answer", desc := .func 0 }]
  memMin := 1

/-- The golden text — `watEmitter.run`'s contents over the module
    above, pinned BYTE-EXACT (the test-pinned byte-tie: the artifact
    placement judgment is WasmCore.Wat's header — nothing commits
    ahead of its writer). -/
def goldenWat : String :=
"(module\n"
++ "  (type (func (param i32) (result i64)))\n"
++ "  (type (func))\n"
++ "  (memory 1)\n"
++ "  (export \"answer\" (func 0))\n"
++ "  (func (type 0)\n"
++ "    (local i32)\n"
++ "    local.get 0\n"
++ "    i32.const 4\n"
++ "    i32.load offset=4\n"
++ "    i32.add\n"
++ "    block\n"
++ "      br_if 0\n"
++ "    end\n"
++ "    i64.const 7\n"
++ "    if\n"
++ "      drop\n"
++ "    else\n"
++ "      drop\n"
++ "    end\n"
++ "    i64.extend_i32_u\n"
++ "  )\n"
++ "  (func (type 1)\n"
++ "    (local i64)\n"
++ "    loop\n"
++ "      i32.const 0\n"
++ "      i32.const 1\n"
++ "      i32.store align=2\n"
++ "      call 0\n"
++ "      br 0\n"
++ "    end\n"
++ "    i64.const 9\n"
++ "    i64.const 8\n"
++ "    select\n"
++ "    local.set 0\n"
++ "    local.get 0\n"
++ "    local.tee 0\n"
++ "    drop\n"
++ "    unreachable\n"
++ "  )\n"
++ ")\n"

/-- The golden pin: the renderer's text ties AND the emitter row's run
    is exactly that artifact (path + contents — the 05 §2 spine face;
    field-wise, `GeneratedFile` carries no BEq). -/
def watGoldenProp : Tape → CheckResult := fun _ => do
  assert (renderModule goldenWatModule == goldenWat)
    s!"WAT golden mismatch: got\n{renderModule goldenWatModule}"
  match watEmitter.run goldenWatModule with
  | [{ path := p, contents := c }] =>
      assert (p == "gen/wasm-slice.wat") "the emitter row's path drifted"
      assert (c == goldenWat) "the emitter row's contents drifted from the golden"
  | _ => assert false "the emitter row's run shape drifted"

/-- Control: a tampered memarg offset must NOT tie (the golden renders
    the memarg's DATA — a renderer that ignores it would tie here). -/
def watNegOffset : Tape → CheckResult := fun _ =>
  let f0 : Func := { goldenWatModule.funcs[0]! with
    body := [.localget 0, .i32const 4, .mem .i32load 5 none, .op .i32add,
             .block [.brif 0], .i64const 7, .if_ [.drop] [.drop],
             .op .i64extendi32u] }
  let tampered : Module := { goldenWatModule with
    funcs := [f0, goldenWatModule.funcs[1]!] }
  assert (renderModule tampered == goldenWat) "control fired: tampered offset tied"

/-- Control: an empty else-branch must render NO `else` (the binary
    else-elision mirrored in text) — a renderer that adds one is caught. -/
def watNegElse : Tape → CheckResult := fun _ =>
  assert ((Text.render (instrW 0 (.if_ [.drop] []))).contains "else")
    "control fired: the empty else-branch rendered an else"

def watGoldenSpec : Spec :=
  Spec.ofList "the WAT golden byte-tie + the emitter row"
    watGoldenProp
    [ ("tampered offset tied", watNegOffset)
    , ("empty else rendered", watNegElse) ]
    1 42

/-! ### The op-spelling coverage (the ONE table's fold, every row) -/

/-- The closed op universes, exhaustively listed — the compile-time
    completeness authority is the exhaustive `opRow`/`memRow` matches;
    these lists drive the RUNTIME sweep (a ctor missing here renders
    nowhere — the sweep's width is the full table). -/
def allOps : List Op :=
  [ .i64add, .i64sub, .i64mul, .i64ltu, .i64leu, .i64eq
  , .i32add, .i32sub, .i32mul, .i32and, .i32xor, .i32shru, .i64shru
  , .i32eqz, .i32eq, .i32ltu, .i32gtu
  , .i32wrapi64, .i64extendi32u ]

def allMemOps : List MemOp :=
  [ .i32load8u, .i32load, .i64load, .i32store, .i64store, .i32store8, .i64store8 ]

/-- EVERY op renders its table row's spelling: the renderer's line is
    the table's `name` — byte-for-byte, at the line's exact shape
    (`{name}\\n`). Plus the literal drift-guard pins (the spelling the
    goldens rely on). -/
def opSpellProp : Tape → CheckResult := fun _ => do
  allOps.foldl (fun acc o => do
    acc
    assert (Text.render (instrW 0 (.op o)) == opName o ++ "\n")
      s!"op spelling drifted from the table: {opName o}") (pure ())
  allMemOps.foldl (fun acc m => do
    acc
    assert (Text.render (instrW 0 (.mem m 0 none)) == memName m ++ "\n")
      s!"mem-op spelling drifted from the table: {memName m}") (pure ())
  -- The literal pins (the table-spelling drift guards, sigSpec's shape).
  assert (opName .i32add == "i32.add") "i32add spelling drifted"
  assert (opName .i32shru == "i32.shr_u") "i32shru spelling drifted"
  assert (opName .i64extendi32u == "i64.extend_i32_u") "i64extendi32u spelling drifted"
  assert (memName .i32load8u == "i32.load8_u") "i32load8u spelling drifted"
  assert (memName .i64store8 == "i64.store8") "i64store8 spelling drifted"
  -- The memarg DATA rendering (the clobber-bug guards, positive face).
  assert (Text.render (instrW 0 (.mem .i32load 4 none)) == "i32.load offset=4\n")
    "the nonzero offset rendering drifted"
  assert (Text.render (instrW 0 (.mem .i32store 0 (some 2))) == "i32.store align=2\n")
    "the explicit-align rendering drifted"
  assert (Text.render (instrW 0 (.mem .i64load 0 none)) == "i64.load\n")
    "the elided-default rendering drifted"

/-- Control: a DRIFTED spelling must NOT pass the sweep (the canary:
    the table's name is the spec of record — this asserts its
    falsification, so it is caught). -/
def opSpellNegDrift : Tape → CheckResult := fun _ =>
  assert (opName .i32add == "i32.sub") "control fired: a drifted spelling was accepted"

/-- Control: the flat-render sabotage (a renderer that spells a
    structural form on one line) must NOT tie the structural shape. -/
def opSpellNegFlat : Tape → CheckResult := fun _ =>
  assert (Text.render (instrW 0 (.block [.drop])) == "block drop\n")
    "control fired: the flat structural rendering was accepted"

def opSpellSpec : Spec :=
  Spec.ofList "the op-table spelling fold (every row renders its name)"
    opSpellProp
    [ ("drifted spelling", opSpellNegDrift)
    , ("flat structural form", opSpellNegFlat) ]
    1 42

/-! ## The binary lane (WasmCore.Slice — the committed artifact) -/

-- The regen IS the writer's and the gate's ONE copy. Its bytes are
-- the battery's OWN pinned golden vector — the committed artifact's
-- independent pin, outside the spine (suite 2's `goldenBytes`).
def sliceRegenProp : Tape → CheckResult := fun _ => do
  match regen wasmSliceModule with
  | .error e => assert false s!"the slice module failed to validate: {e}"
  | .ok (texts, bins) => do
      match texts, bins with
      | [t], [b] => do
          assert (t.path == "gen/wasm-slice.wat") "the text lane's path drifted"
          assert (b.path == "gen/wasm-slice.wasm") "the binary lane's path drifted"
          assert (b.contents.toList == goldenBytes)
            s!"the regen bytes drifted from the pinned golden: got {bytesS b.contents.toList}"
      | _, _ => assert false "the regen's lane shape drifted"

/-- TEETH (the validator at generation): an invalid module is a
    generation FAILURE, never an artifact — the control asserts the
    falsification, so a regen that emits an invalid module goes
    uncaught (vacuous). -/
def sliceNegInvalid : Tape → CheckResult := fun _ =>
  match regen unbalancedModule with
  | .error _ => assert false
    "control fired: the invalid module was refused (the validator ran)"
  | .ok _ => pure ()

/-- Control: the regen bytes must NOT drift from the pinned golden
    (the tampered-constant control's artifact-side twin). -/
def sliceNegGolden : Tape → CheckResult := fun _ =>
  match regen wasmSliceModule with
  | .ok (_, [b]) =>
      assert (b.contents.toList != goldenBytes)
      "control fired: the regen bytes tied the golden after a drift"
  | _ => assert false "control fired: the regen's lane shape drifted"

def sliceSpec : Spec :=
  Spec.ofList "the wasm slice regen (the committed artifact's bytes)"
    sliceRegenProp
    [ ("invalid module generated", sliceNegInvalid)
    , ("regen bytes drifted", sliceNegGolden) ]
    1 42

/-! ### The binary byte-tie (Kit.Emit.tieBytes) — the positive + teeth -/

/-- The committed triple, constructed honestly: the fresh bytes are
    the encoder's output, the sidecar is the kit's OWN 2-line header
    shape (what `runBinaryEmitters` writes) naming the bytes' hash. -/
def freshSliceBytes : ByteArray :=
  ByteArray.mk (encodeModule wasmSliceModule).toArray

def goodSidecar : String :=
  Kit.Emit.header .lean "wasmgen" "WasmCore.Module"
    { contentHash := Kit.Emit.bytesHash freshSliceBytes }

def tieBytesProp : Tape → CheckResult := fun _ =>
  match Kit.Emit.tieBytes goodSidecar freshSliceBytes freshSliceBytes with
  | .tied => pure ()
  | .drifted why => assert false s!"the committed triple failed to tie: {why}"

/-- TEETH: one tampered artifact byte must NOT tie (the byte-tie's
    drift detection — the gate's whole point). -/
def tieBytesNegTamperedByte : Tape → CheckResult := fun _ =>
  let tampered :=
    match freshSliceBytes.toList with
    | b :: rest => ByteArray.mk (((b ^^^ 0xFF) :: rest).toArray)
    | [] => freshSliceBytes
  match Kit.Emit.tieBytes goodSidecar tampered freshSliceBytes with
  | .drifted _ => assert false
    "control fired: the tampered artifact byte did NOT tie"
  | .tied => pure ()

/-- TEETH: a sidecar that does not name the fresh bytes' hash must NOT
    tie (the sidecar's own hash check — a stale sidecar is a drift). -/
def tieBytesNegWrongSidecar : Tape → CheckResult := fun _ =>
  let stale := goodSidecar.replace (toString (Kit.Emit.bytesHash freshSliceBytes)) "0"
  match Kit.Emit.tieBytes stale freshSliceBytes freshSliceBytes with
  | .drifted _ => assert false
    "control fired: the stale sidecar did NOT fail the hash check"
  | .tied => pure ()

def tieBytesSpec : Spec :=
  Spec.ofList "the binary byte-tie (Kit.Emit.tieBytes)"
    tieBytesProp
    [ ("tampered artifact byte tied", tieBytesNegTamperedByte)
    , ("stale sidecar tied", tieBytesNegWrongSidecar) ]
    1 42

-- The outcome's observers (04 §4: the tests NAME the observation): the
-- run is read through the final stack, the trap kind, and the fuel
-- answer — the apiObs face. Nothing else is claimed.

/-- The final stack of a completed run (`none` = any other outcome). -/
def stackOf : Outcome → Option (List Val)
  | .ok s => some s.stack
  | _ => none

/-- The trap kind of a trapped run. -/
def trapOf : Outcome → Option Trap
  | .trap t => some t
  | _ => none

/-- The fuel answer. -/
def isOutOfFuel : Outcome → Bool
  | .outOfFuel => true
  | _ => false

/-- The run returned ok (any stack). -/
def isOk : Outcome → Bool
  | .ok _ => true
  | _ => false

def run1 (m : Module) (fuel : Nat) : Outcome := runFunc m 0 [] fuel

/-- The worked arithmetic module: 6 · 7 into a local, 9 into an i32
    local, decrement, return 41. Consts, both local forms, i64
    mul/sub. -/
def execArith : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [.i32, .i64],
    [ .i64const 6, .i64const 7, .op .i64mul
    , .localset 1
    , .i32const 9, .localset 0
    , .localget 1, .i64const 1, .op .i64sub ]⟩]
  exports := []
  memMin := 0

/-- The memory module: store8 at 10, load8 back (zero-extend),
    widen — the answer 7. Func 1 writes an i32 past the edge (the
    OOB teeth's fixture). -/
def execMem : Module where
  types := [⟨[], [.i64]⟩, ⟨[.i32], []⟩]
  funcs :=
    [ ⟨0, [], [ .i32const 10, .i32const 7, .mem .i32store8 0 none
              , .i32const 10, .mem .i32load8u 0 none
              , .op .i64extendi32u ]⟩
    , ⟨1, [.i32], [ .i32const 65534, .localget 0, .mem .i32store 0 none ]⟩ ]
  exports := []
  memMin := 1

/-- The out-of-bounds teeth: byte store at the size's edge, word store
    straddling it, and the offset pushing the byte out. -/
def execOob8 : Module where
  types := [⟨[], []⟩]
  funcs := [⟨0, [], [ .i32const 65536, .i32const 1, .mem .i32store8 0 none ]⟩]
  exports := []
  memMin := 1

def execOob32 : Module where
  types := [⟨[], []⟩]
  funcs := [⟨0, [], [ .i32const 65534, .i32const 1, .mem .i32store 0 none ]⟩]
  exports := []
  memMin := 1

def execOobOffset : Module where
  types := [⟨[], []⟩]
  funcs := [⟨0, [], [ .i32const 65530, .i32const 1, .mem .i32store8 10 none ]⟩]
  exports := []
  memMin := 1

/-- The loop module: l0 counts to 10 (the loop-restart discipline);
    the answer 10. Under-fueled, the honest outOfFuel. -/
def execLoop : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [.i64],
    [ .loop [ .localget 0, .i64const 1, .op .i64add, .localset 0
            , .localget 0, .i64const 10, .op .i64ltu
            , .brif 0 ]
    , .localget 0 ]⟩]
  exports := []
  memMin := 0

/-- The control modules: br exits a block early (6); if takes a branch
    into a local (7 / 99); select keeps v1 (8). -/
def execBlock : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [],
    [ .i64const 5
    , .block [ .i64const 9, .drop, .br 0, .i64const 99, .drop ]
    , .i64const 1, .op .i64add ]⟩]
  exports := []
  memMin := 0

def execIfThen : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [.i64],
    [ .i32const 1, .if_ [ .i64const 7, .localset 0 ] [ .i64const 99, .localset 0 ]
    , .localget 0 ]⟩]
  exports := []
  memMin := 0

def execIfElse : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [.i64],
    [ .i32const 0, .if_ [ .i64const 7, .localset 0 ] [ .i64const 99, .localset 0 ]
    , .localget 0 ]⟩]
  exports := []
  memMin := 0

def execSelect : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [ .i64const 9, .i64const 8, .i32const 1, .select ]⟩]
  exports := []
  memMin := 0

/-- The machine-i pins: the wrap semantics ARE the native UInt ops. -/
def execLtu : Module where
  types := [⟨[], [.i32]⟩]
  funcs := [⟨0, [], [ .i64const 3, .i64const 9, .op .i64ltu ]⟩]
  exports := []
  memMin := 0

def execWrap : Module where
  types := [⟨[], [.i32]⟩]
  funcs := [⟨0, [], [ .i64const 4294967301, .op .i32wrapi64 ]⟩]
  exports := []
  memMin := 0

def execSub : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [ .i64const 7, .i64const 2, .op .i64sub ]⟩]
  exports := []
  memMin := 0

def execAddWrap : Module where
  types := [⟨[], [.i32]⟩]
  funcs := [⟨0, [], [ .i32const 4294967295, .i32const 1, .op .i32add ]⟩]
  exports := []
  memMin := 0

/-- NEGATIVE fixture: the buggy write — 43 into the local the spec
    module leaves 42 in (the buggy-template discipline). -/
def execBuggy : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [.i64],
    [ .i64const 42, .localset 0
    , .i64const 43, .localset 0
    , .localget 0 ]⟩]
  exports := []
  memMin := 0

/-- The known-answer pins + the validator conformance (a validated
    module's run is trap-clean). -/
def execProp : Tape → CheckResult := fun _ => do
  assert (stackOf (runFunc wasmSliceModule 0 [] 100) == some [.i64 42])
    "the wasm slice module's execution drifted from the known answer"
  assert (stackOf (run1 execArith 200) == some [.i64 41]) "the arith answer drifted"
  assert (stackOf (run1 execBlock 100) == some [.i64 6]) "the block/br answer drifted"
  assert (stackOf (run1 execIfThen 100) == some [.i64 7]) "the if-then answer drifted"
  assert (stackOf (run1 execIfElse 100) == some [.i64 99]) "the if-else answer drifted"
  assert (stackOf (run1 execSelect 100) == some [.i64 8]) "the select answer drifted"
  assert (stackOf (run1 execLtu 100) == some [.i32 1]) "the lt_u answer drifted"
  assert (stackOf (run1 execWrap 100) == some [.i32 5]) "the wrap answer drifted"
  assert (stackOf (run1 execSub 100) == some [.i64 5]) "the sub answer drifted"
  assert (stackOf (run1 execAddWrap 100) == some [.i32 0]) "the i32 add wrap drifted"
  assert (stackOf (run1 execMem 200) == some [.i64 7])
    "the store8/load8 roundtrip drifted"
  assert (trapOf (run1 execArith 200) == none)
    "a validated module's run trapped (the conformance drift)"
  assert (trapOf (run1 execMem 200) == none)
    "a validated module's run trapped (the conformance drift, mem)"

def execSpec : Spec :=
  Spec.ofList "the executor's known answers + the validator conformance"
    execProp
    [ ("the buggy write agreed", fun _ =>
        assert (stackOf (run1 execBuggy 200) == some [.i64 42])
          "control fired: the buggy write agreed with the spec answer")
    , ("the OOB store was ok", fun _ =>
        assert (isOk (run1 execOob8 100))
          "control fired: the out-of-bounds store completed") ]
    1 42

/-- The trap discipline's teeth: out of bounds traps with the NAMED
    trap, at every shape (edge, straddle, offset). -/
def execTrapProp : Tape → CheckResult := fun _ => do
  assert (trapOf (run1 execOob8 100) == some Trap.memOOB)
    "the edge store8 did not answer the memOOB trap"
  assert (trapOf (run1 execOob32 100) == some Trap.memOOB)
    "the straddling i32store did not answer the memOOB trap"
  assert (trapOf (run1 execOobOffset 100) == some Trap.memOOB)
    "the offset-pushed store8 did not answer the memOOB trap"

def execTrapSpec : Spec :=
  Spec.ofList "the trap discipline's teeth (the named traps)"
    execTrapProp
    [ ("the wrong trap kind fired", fun _ =>
        assert (trapOf (run1 execOob8 100) == some Trap.unreach)
          "control fired: the trap kinds were conflated")
    , ("the OOB store type-errored", fun _ =>
        assert (trapOf (run1 execOob8 100) == some Trap.typeErr)
          "control fired: the OOB store was answered as a type error") ]
    1 42

/-- The fuel honesty: the budget is SEMANTICS — exhaustion answers the
    honest outOfFuel (an under-fueled loop, and the zero budget). -/
def execFuelProp : Tape → CheckResult := fun _ => do
  assert (isOutOfFuel (runFunc wasmSliceModule 0 [] 0))
    "the zero budget did not answer outOfFuel"
  assert (isOutOfFuel (run1 execLoop 8))
    "the under-fueled loop did not answer outOfFuel"
  assert (stackOf (run1 execLoop 1000) == some [.i64 10])
    "the loop sum drifted"

def execFuelSpec : Spec :=
  Spec.ofList "the fuel honesty (exhaustion is honest data)"
    execFuelProp
    [ ("the under-fueled run answered ok", fun _ =>
        assert (isOk (run1 execLoop 8))
          "control fired: the under-fueled loop completed")
    , ("the trap got mislabeled outOfFuel", fun _ =>
        assert (isOutOfFuel (run1 execOob8 100))
          "control fired: the OOB trap was answered as fuel exhaustion") ]
    1 42

/-! ## The calls layer (the call/ret discipline) -/

/-- The run answered the honest `.unmodeled` (the ledger's face). -/
def isUnmodeled : Outcome → Bool
  | .unmodeled => true
  | _ => false

/-- Two functions: the caller pushes 41, the callee adds 1 — the
    module's functions visible to each other. -/
def execCall2 : Module where
  types := [⟨[], [.i64]⟩, ⟨[.i64], [.i64]⟩]
  funcs :=
    [ ⟨0, [], [ .i64const 41, .call 1 ]⟩
    , ⟨1, [], [ .localget 0, .i64const 1, .op .i64add ]⟩ ]
  exports := []
  memMin := 0

/-- The arg-binding order: the args pushed in order (param 0 deepest),
    popped top-first against `params.reverse` — the callee subtracts
    param0 − param1 = 7 − 2 = 5. -/
def execCallArgs : Module where
  types := [⟨[], [.i64]⟩, ⟨[.i64, .i64], [.i64]⟩]
  funcs :=
    [ ⟨0, [], [ .i64const 7, .i64const 2, .call 1 ]⟩
    , ⟨1, [], [ .localget 0, .localget 1, .op .i64sub ]⟩ ]
  exports := []
  memMin := 0

/-- The caller's retained stack: the value below the args survives the
    call; the callee's result lands on top (10 + 32 = 42). -/
def execCallRetain : Module where
  types := [⟨[], [.i64]⟩, ⟨[], [.i64]⟩]
  funcs :=
    [ ⟨0, [], [ .i64const 10, .call 1, .op .i64add ]⟩
    , ⟨1, [], [ .i64const 32 ]⟩ ]
  exports := []
  memMin := 0

/-- The recursive factorial: f(n) = if n = 0 then 1 else f(n−1)·n —
    the call's fuel-shared sub-exec, each nesting level strictly
    descending. -/
def execFact : Module where
  types := [⟨[.i64], [.i64]⟩]
  funcs := [⟨0, [.i64],
    [ .localget 0, .i64const 0, .op .i64eq
    , .if_ [ .i64const 1, .localset 1 ]
           [ .localget 0, .localget 0, .i64const 1, .op .i64sub, .call 0,
             .op .i64mul, .localset 1 ]
    , .localget 1 ]⟩]
  exports := []
  memMin := 0

/-- The divergent recursion: g never returns — ANY budget answers the
    honest outOfFuel (the recursion honesty; never a wrong answer). -/
def execDiverge : Module where
  types := [⟨[.i64], [.i64]⟩]
  funcs := [⟨0, [], [ .localget 0, .call 0 ]⟩]
  exports := []
  memMin := 0

/-- The top-level `ret`: the return signal (`.branch none`) with the
    results on the stack; the dead tail never runs. -/
def execRet : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [ .i64const 42, .ret, .i64const 99 ]⟩]
  exports := []
  memMin := 0

/-- The callee's `ret`: the return signal escapes the callee's frames;
    the caller resumes with the results on top (41 + 1 = 42). -/
def execCallRet : Module where
  types := [⟨[], [.i64]⟩, ⟨[], [.i64]⟩]
  funcs :=
    [ ⟨0, [], [ .call 1, .i64const 1, .op .i64add ]⟩
    , ⟨1, [], [ .i64const 41, .ret, .i64const 99 ]⟩ ]
  exports := []
  memMin := 0

/-- The validator's branch-depth gap: the callee's `br 0` at its top
    level escapes its frames — the call boundary answers the honest
    `.unmodeled` (branches do not cross calls; the escape signal names
    no return convention). -/
def execBrEscape : Module where
  types := [⟨[], [.i64]⟩, ⟨[], [.i64]⟩]
  funcs :=
    [ ⟨0, [], [ .call 1 ]⟩
    , ⟨1, [], [ .i64const 7, .br 0, .i64const 9 ]⟩ ]
  exports := []
  memMin := 0

/-- The calls layer's pins: every call module validates (the
    validator's side rides first), the known answers hold, the
    recursion is fuel-honest, and the ledger stays honest on the
    validator's gaps. -/
def execCallProp : Tape → CheckResult := fun _ => do
  assert (checkOk execCall2) "the two-function module was refused"
  assert (checkOk execCallArgs) "the arg-binding module was refused"
  assert (checkOk execCallRetain) "the retained-stack module was refused"
  assert (checkOk execFact) "the recursive module was refused"
  assert (checkOk execDiverge) "the divergent module was refused"
  assert (checkOk execRet) "the ret module was refused"
  assert (checkOk execCallRet) "the callee-ret module was refused"
  assert (checkOk execBrEscape) "the br-escape module was refused"
  assert (stackOf (run1 execCall2 200) == some [.i64 42])
    "the caller+callee answer drifted"
  assert (stackOf (run1 execCallArgs 200) == some [.i64 5])
    "the arg-binding order drifted (param 0 = the first pushed)"
  assert (stackOf (run1 execCallRetain 200) == some [.i64 42])
    "the retained-stack answer drifted (the result lands on top)"
  assert (stackOf (runFunc execFact 0 [.i64 5] 10000) == some [.i64 120])
    "the recursive factorial drifted"
  assert (stackOf (run1 execRet 100) == some [.i64 42])
    "the top-level ret drifted (the dead tail must not run)"
  assert (stackOf (run1 execCallRet 200) == some [.i64 42])
    "the callee-ret answer drifted"
  -- the fuel/recursion honesty: the budget bounds the call depth
  assert (isOutOfFuel (runFunc execFact 0 [.i64 5] 20))
    "the under-fueled recursion did not answer outOfFuel"
  assert (isOutOfFuel (runFunc execDiverge 0 [.i64 1] 500))
    "the divergent recursion did not answer outOfFuel (any budget)"
  -- the ledger honesty: the validator's gaps answer unmodeled, never
  -- a fabricated return and never a trap
  assert (isUnmodeled (run1 execBrEscape 100))
    "the frame-escaping br did not answer the honest unmodeled"
  assert (isUnmodeled (run1 unboundFuncModule 100))
    "the unvalidated module's unbound call did not answer unmodeled"
  -- the conformance: a validated module's call chain never traps
  assert (trapOf (run1 execCall2 200) == none) "a validated call trapped"
  assert (trapOf (runFunc execFact 0 [.i64 5] 10000) == none)
    "a validated recursion trapped"

def execCallSpec : Spec :=
  Spec.ofList "the calls layer (call/ret discipline + the fuel honesty)"
    execCallProp
    [ ("the callee's result was ignored", fun _ =>
        assert (stackOf (run1 execCall2 200) == some [.i64 41])
          "control fired: the callee's result reached the caller")
    , ("the under-fueled recursion completed", fun _ =>
        assert (isOk (runFunc execFact 0 [.i64 5] 20))
          "control fired: the under-fueled recursion completed")
    , ("the divergent recursion answered", fun _ =>
        assert (isOk (runFunc execDiverge 0 [.i64 1] 500))
          "control fired: the divergent recursion returned")
    , ("the br-escape returned values", fun _ =>
        assert (isOk (run1 execBrEscape 100))
          "control fired: the frame-escaping br fabricated a return")
    , ("the unbound call trapped", fun _ =>
        assert (trapOf (run1 unboundFuncModule 100) == some Trap.unreach)
          "control fired: the unvalidated module's call answered a trap") ]
    1 42
/-! ## The duel (WasmCore.Duel — the execution duel's Lean half) -/

/-- The duel's computed rows, DESTRUCTURED for the pins (the `.ok`
    face — the family is total, the failure face is the loud
    generation failure the regen refuses with). -/
def duelRowsOk : List (String × Kit.Duel.Expect) :=
  match WasmCore.Duel.duelRows with
  | .ok es => es
  | .error e => panic! s!"the duel rows failed to compute — {e}"

/-- The duel's known answers: the executor's COMPUTED expectations
    over the family (never hand-spelled — this pin ties the generator
    to the SAME known answers the executor battery pins by hand). -/
def duelProp : Tape → CheckResult := fun _ => do
  assert (WasmCore.Duel.duelRowsCovered)
    "a duel manifest row names an absent vector (the generator bug)"
  assert (duelRowsOk.length == 6) "the duel's row count drifted"
  -- The slice row: the executor's computed expectation IS i64:42.
  assert (duelRowsOk.lookup (WasmCore.Duel.duelVecName "slice")
    == some (.run "i64:42")) "the slice row's computed expectation drifted"
  -- The arithmetic row (6·7+8>>3, widened, ·36−174).
  assert (duelRowsOk.lookup (WasmCore.Duel.duelVecName "arith")
    == some (.run "i64:42")) "the arith row's computed expectation drifted"
  -- The control-flow row: the loop sums 5..1, the if_ selects 100.
  assert (duelRowsOk.lookup (WasmCore.Duel.duelVecName "control")
    == some (.run "i64:100")) "the control row's computed expectation drifted"
  -- The memory row: 0x12345678 + 255.
  assert (duelRowsOk.lookup (WasmCore.Duel.duelVecName "memory")
    == some (.run "i64:305420151")) "the memory row's computed expectation drifted"
  -- The trap row: the executor's typed trap, pinned.
  assert (duelRowsOk.lookup (WasmCore.Duel.duelVecName "trap") == some .trap)
    "the trap row's computed expectation drifted"
  -- The invalid control: the validator's refusal IS the expectation.
  assert (duelRowsOk.lookup (WasmCore.Duel.duelVecName "invalid") == some .refuse)
    "the invalid control's expectation drifted"

  -- The verdict fold NAMES the first non-agree row (the positive face
  -- of the minimal-counterexample discipline; the control below holds
  -- the failure face).
  let folded := Kit.Duel.Verdict.foldRows
    [.agree, .diverge ⟨"row7", "i64:1", "i64:2"⟩, .refused "w"]
  assert (match folded with
    | .diverge w => w.loc == "row7"
    | _ => false)
    "the fold did not name the FIRST non-agree row"

/-- A family member whose run does not COMPLETE (a self-recursive
    `call` body — the recursion honesty: the fuel-shared sub-exec
    exhausts any budget = outOfFuel) is a GENERATION FAILURE, never an
    expectation. The failure face, stated as the control's function. -/
def duelUnmodeled : Tape → CheckResult := fun _ => do
  match WasmCore.Duel.duelExpect "fixture"
      ({ types := [⟨[], [.i64]⟩]
       , funcs := [⟨0, [], [.i64const 1, .i64const 2, .op .i64add, .call 0]⟩]
       , exports := [{ name := "answer", desc := .func 0 }] } : Module) with
  | .error _ => assert false "control fired: the unmodeled body was refused"
  | .ok _ => pure ()

/-- The verdict fold's failure face: a fold that LOST the divergence
    (answered agree) is the broken-generator control. -/
def duelFoldLost : Tape → CheckResult := fun _ =>
  assert (Kit.Duel.Verdict.foldRows [.agree, .diverge ⟨"row7", "1", "2"⟩]
    == .agree)
    "control fired: the fold lost the divergence"

def duelSpec : Spec :=
  Spec.ofList "WasmCore.Duel — the execution duel's Lean half"
    duelProp
    [ ("an unmodeled body produced an expectation", duelUnmodeled)
    , ("the fold lost the divergence", duelFoldLost) ]
    1 42

/-! ### The type-safety theorem (the body-level induction + the module face) -/

-- The deliverable: `WasmCore.exec_typed` (a VALIDATED body at ANY
-- budget never answers the type-mismatch trap; completing is typed
-- preservation; branch locals are typed) and `WasmCore.runFunc_safe`
-- (a validated module's function on `call`-rule-typed args: no type
-- error, completing lands on the declared results). The theorem's
-- premise is load-bearing — the teeth below pin both faces.

/-- The validation premise at the wasm slice module, discharged by the
    unfold chain (`decide` cannot: the checker's `Except` carries no
    derived `DecidableEq` — the Slice lane's documented judgment). -/
theorem wasmSlice_validated : checkModule wasmSliceModule = .ok () := by
  show checkFuncs wasmSliceModule 0 wasmSliceModule.funcs = .ok ()
  rw [show wasmSliceModule.funcs = [⟨0, [], [.i64const 42]⟩] from rfl]
  simp only [checkFuncs, Module.typeAt,
    checkFunc, checkBody, checkFlow, fnCtx, checkStep, stepFlag,
    List.foldl_cons, List.foldl_nil, map_snd_ok_eq]
  rfl

/-- THE THEOREM ON THE SLICE: the committed module's run — at ANY
    budget — never type-traps, and completing lands on the declared
    results (the runtime pins below are this theorem's witnesses). -/
theorem wasmSlice_typeSafe (fuel : Nat) :
    runFunc wasmSliceModule 0 [] fuel ≠ Outcome.trap Trap.typeErr
    ∧ (∀ s', runFunc wasmSliceModule 0 [] fuel = .ok s' →
          stackTys s'.stack = [.i64]) := by
  exact runFunc_safe wasmSliceModule 0 ⟨0, [], [.i64const 42]⟩ ⟨[], [.i64]⟩ []
    fuel (by simp [wasmSliceModule]) rfl wasmSlice_validated rfl

/-- The theorem's premise is LOAD-BEARING: the type-unsound shapes
    really do answer the type-mismatch trap at runtime — and VALIDATION
    REFUSES their modules, so `runFunc_safe` never applies to them. -/
def typeSafetyTeethProp : Tape → CheckResult := fun _ => do
  assert (trapOf (run1 underflowModule 100) == some Trap.typeErr)
    "the drop-on-empty run did not answer the type error"
  assert (trapOf (run1 mismatchModule 100) == some Trap.typeErr)
    "the i32-add-on-i64 run did not answer the type error"
  assert (!checkOk underflowModule)
    "the drop-on-empty module was accepted by validation"
  assert (!checkOk mismatchModule)
    "the mismatch module was accepted by validation"

def typeSafetyTeethSpec : Spec :=
  Spec.ofList "the type-safety premise is load-bearing (runtime trap + validation refusal)"
    typeSafetyTeethProp
    [ ("the unsound run completed", fun _ =>
        assert (isOk (run1 mismatchModule 100))
          "control fired: the type-unsound run completed ok")
    , ("the unsound module validated", fun _ =>
        assert (checkOk underflowModule)
          "control fired: the type-unsound module was accepted")
    , ("the slice run type-trapped", fun _ =>
        assert (trapOf (runFunc wasmSliceModule 0 [] 100) == some Trap.typeErr)
          "control fired: the validated slice run answered the type error") ]
    1 42

/-! ## The driver -/

def main : IO UInt32 :=
  mainOfSuites
    [ ("WasmCore.Encode/LEB128", [lebSpec])
    , ("WasmCore.Encode/golden", [goldenSpec])
    , ("WasmCore.Validate", [validateSpec])
    , ("WasmCore.Validate/error-kinds", [teethSpec, renderSpec])
    , ("WasmCore.Validate/sig-pins", [sigSpec])
    , ("WasmCore.Wat/golden", [watGoldenSpec])
    , ("WasmCore.Wat/op-spellings", [opSpellSpec])
    , ("WasmCore.Slice/regen", [sliceSpec])
    , ("WasmCore.Slice/byte-tie", [tieBytesSpec])
    , ("WasmCore.Exec", [execSpec, execTrapSpec, execFuelSpec])
    , ("WasmCore.Exec/calls", [execCallSpec])
    , ("WasmCore.Exec/type-safety", [typeSafetyTeethSpec])
    , ("WasmCore.Duel", [duelSpec]) ]
