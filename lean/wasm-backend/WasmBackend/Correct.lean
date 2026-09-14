import Lean
import Lean.Compiler.LCNF
import WasmBackend

/-!
# WasmBackend.Correct — translation correctness for the straight-line fragment

Talos seam #7 (notes/seam-contract.md): the emitted WAT's `Sem`-execution
agrees with the source Lean function's semantics, for the fragment where
that is tractable. This file owns the FIRST slice of that theorem: the
NON-BRANCHING let-chains (the `emitLet`-produced consts / binops /
`local.set`s and `emitReturn`'s load).

THE FRAGMENT (the honesty ledger):

* COVERED: the straight-line scalar core — `let x := lit k` (UInt64),
  `let y := fap UInt64.add [..]` (the `binop?` i64.add path),
  `return v`, and the i64.add machine step. This is exactly
  `double`'s and `adder`'s bodies after LCNF lowering.
* THE MODEL DELTA: `Sem.Instr` gained `i64add` (the backend's `binop?`
  emits `i64.add` for `UInt64.add`; before this lane `Sem` only modeled
  `i32.add`). The core theorems of `Sem.lean` are statement-unchanged;
  the proof gained the mirrored `i64add` cases (step / checkStack /
  exec_typed).
* COVERED (the BRANCH slice, this file's second section): the cases
  template — `emitCases`'s SCALAR-scrutinee path (`goAltsRaw`: Bool /
  UInt8/UInt32/UInt64 scrutinees branch on the VALUE) mirrored at the
  Sem level as the nested-`if_` chain (`specCases`), for the 2-alt
  shape with STRAIGHT-LINE alt bodies: the branch-preservation theorem
  `specCases_ok` (the tag picks the alt; the result = the chosen alt's
  value), the demo on `DemoFn.isBig`'s branch shape (is-big 250 = 1,
  is-big 42 = 0), and the tag-INVERTED negative control.
* THE MODEL DELTA (Sem.lean, branch slice): `i32eq` (the branch
  comparison — `goAlts` emits `i32.eq` on the scalar scrutinee; the
  i64add precedent: the core defs gained a case, statements unchanged).
* COVERED (the CALLS + CLOSURES slice, this file's third section): the
  calling-convention CONTRACT — the caller's call-prep (the pushes:
  closure ptr first = param 0, then the fresh args in order) composed
  with the callee's entry prologue (the binding pops) passes each value
  through (`call_convention1/2`), the trampoline's arg-forward contract
  (`trampoline_convention1/2` — the golden's `pap_curried._boxed_1`
  shape), the run-paps 5 = 8 inner-call demo (two convention hops + the
  adder bodies, composed), and the arg-order-swapped negative control.
* COVERED (the TAG-READ slice, this file's fourth branch addition): the
  tag LOAD — the object-scrutinee's `i32load8u` read is now part of the
  spec: the composed template `specCasesLoad` starts BEFORE the read
  (`local.get base; i32.load8u offset; local.set 0` + the chain),
  `specCasesLoad_ok` covers the composed load+branch, and the
  wrong-offset negative control (`loadCases_buggy_disagrees`) pins the
  bug class. (The OLD post-read `specCases_ok` is unchanged — the
  composed template's tail.)
* NOT COVERED (documented exclusions, not oversights): N > 2 alt
  chains (the template generalizes; the theorem pins 2), alt bodies
  containing branches/calls (the nested-case/call seams), the
  comparison op producing the Bool (`i64ltu` — the straight-line
  lane's operand layer; the demo feeds the Bool as a param), the FULL
  call semantics (no call-frames in the model — the convention theorem
  is the contract, not the machine: see the calls-slice header for the
  scope decision), the memory loads around calls (`i32.load 8` the
  fnIdx, `i32.load 16` the partial read, the box/unbox loads — Sem
  models no loads), the `call_indirect` dispatch itself (the funcref
  table), the boxed result path back to the caller, the RC discipline
  (`rc_inc`/`rc_dec`), objects (ctor/sproj/oset — the memory layer),
  `Nat` literals (GMP-banned in the guest), and the adapter/ABI layer.
* THE RETURN CONVENTION: `lower` drops `Wat.ret` — in the Sem model the
  function's result is the FINAL STACK's top (the call layer is
  unmodeled; `Sem.lean`'s header: "uncaught at the function's top level
  = the function-return signal"). Honest only because the fragment's
  `ret` is always the body's LAST instruction.

THE BRIDGE (what is proved vs what is tested):

1. THEOREMS (over the TYPED emission templates, `spec*` below — total
   defs, kernel-checked): the Sem-execution of the template computes the
   intended arithmetic, for SYMBOLIC inputs, arbitrary initial state and
   sufficient fuel (`tpl_add_ret_ok`), plus the concrete pins
   (`spec_double_ok`: 21 + 21 = 42; `spec_add_ok`: 40 + 2 = 42 — the
   duel's own values, PROVEN at the Sem level).
2. THE EXTRACTION CHECK (#guard, build-failing, interpreter-evaluated):
   the backend's ACTUAL `emitCode` — called on a hand-constructed LCNF
   decl of the known shape — lowers (`lower`) EXACTLY to the template
   instantiation the theorems talk about. This closes the template↔backend
   gap for the pinned shapes.
3. THE NEGATIVE CONTROL: an offset-swapped template (`tplLitBuggy` —
   the lit stored one slot past its own) still TYPE-CHECKS (the checker
   is shape-only, by design — `Sem.lean`'s conservative-typing note) but
   its Sem-execution DISAGREES with the spec's value — the disagreement
   is a THEOREM (`buggy_ne_spec`), not a hope.

THE EXTRACTION GAP (honest): the backend's `emitCode` is `partial` (the
LCNF `Code` recursion) and its INPUT is the impure-phase LCNF that
GenMain re-runs in CoreM. So (a) the backend's emission is pinned to the
templates only at the CONCRETE shapes below (#guard), not for ALL LCNF;
and (b) the LCNF decls here are hand-constructed to the known pipeline
shape (verified against the emitted goldens' structure), not extracted
from the pipeline's output. The full Talos step — `∀ code, Sem.exec
(lower (emit code)) ≡ the source's semantics` — needs a total, fuel-
polymorphic re-statement of the emitter plus a source-semantics model of
the LCNF machine (the next seam).

Ownership: the TRANSLATION-CORRECTNESS lane. Read-only dependencies:
`WasmBackend` (the emitter), `WasmBackend.Wat` (the AST),
`WasmBackend.Sem` (the machine — additively extended with `i64add`).
No mathlib; no `sorry`; nothing here is `axiom`-backed (gated in
Tests/Axioms.lean).
-/

open Lean Compiler.LCNF

namespace WasmBackend.Correct

/-! ## The lowering: `Wat.Instr` → `Sem.Instr` (the fragment's map)

`Sem.Instr` mirrors the flat subset 1:1 (`Sem.lean` header) except:
locals are INDEXES here vs the emitter's NAMES, and the emitter's binop
opcode is `i64.add` (modeled since this lane). Anything OUTSIDE the
fragment lowers to `none` — the checks below FAIL LOUDLY (the build
breaks) rather than silently dropping an instruction. -/

/-- The emitter's generated local names: `l{n}` (`bindLocal`/`bindFresh`
    bump a counter; the templates' shapes use this family). -/
def localIdx? (s : String) : Option Nat :=
  if s.startsWith "l" then (s.drop 1).toNat? else none

/-- One instruction, lowered. `.ret` lowers to `[]` (the return
    convention — see the header). -/
def lowerI : Wat.Instr → Option (List Sem.Instr)
  | .i32const n => some [.i32const (UInt32.ofNat n)]  -- the fragment's consts are small; the cast wraps ≥ 2^32
  | .i64const n => some [.i64const (UInt64.ofNat n)]
  | .localget n => localIdx? n |>.map fun i => [.localget i]
  | .localset n => localIdx? n |>.map fun i => [.localset i]
  | .op .i64add => some [.i64add]
  | .op .i32eq => some [.i32eq]  -- the branch comparison (the cases lane)
  | .mem .i32load8u off _ => some [.i32load8u off]  -- the tag read (the tag-read lane)
  | .unreach => some [.unreach]  -- goAlts's exhausted-chain filler
  | .ret => some []
  | _ => none

/-- A body, lowered — `none` = OUTSIDE the fragment. The `if_` case
    (the branch slice) recurses into the two NESTED bodies — the
    emitter's `goAlts` shape (the join type annotation is dropped; the
    Sem model's frames carry no result type). -/
def lower : List Wat.Instr → Option (List Sem.Instr)
  | [] => some []
  | .if_ _ t e :: rest =>
      match lower t, lower e with
      | some t', some e' => ((Sem.Instr.if_ t' e') :: ·) <$> lower rest
      | _, _ => none
  | i :: rest =>
      match lowerI i with
      | none => none
      | some is' => (is' ++ ·) <$> lower rest

/-! ## The typed emission templates (the `emitLet`/`emitReturn` shapes)

These re-state the backend's straight-line emission at the Sem level —
the objects the THEOREMS quantify over. The extraction checks below pin
them to the backend's actual output. -/

/-- `emitLet`'s `lit (uint64 v)` arm: `i64.const v; local.set l`. -/
def tplLit (n : UInt64) (l : Nat) : List Sem.Instr :=
  [.i64const n, .localset l]

/-- `emitLet`'s `fap UInt64.add [x, y]` arm (the `binop?` path):
    `local.get x; local.get y; i64.add; local.set l`. -/
def tplAdd (x y l : Nat) : List Sem.Instr :=
  [.localget x, .localget y, .i64add, .localset l]

/-- `emitReturn`'s arm: `local.get v` (the `.ret` is dropped by
    `lower` — the result is the final stack's top). -/
def tplRet (v : Nat) : List Sem.Instr :=
  [.localget v]

/-- The double-shape: `let a := lit k; let b := a + a; return b`. -/
def specDouble (k : UInt64) : List Sem.Instr :=
  tplLit k 0 ++ tplAdd 0 0 1 ++ tplRet 1

/-- The adder-shape: params a b; `let c := a + b; return c`. -/
def specAdd : List Sem.Instr :=
  tplAdd 0 1 2 ++ tplRet 2

/-! ## The machine state for the fragment's pins -/

/-- Canonical init state: all-i64-0 locals, empty stack, 64 zeroed
    bytes (the memory is untouched by this fragment). -/
def initI64 : Sem.State := ⟨fun _ => .i64 0, [], fun _ => (0 : UInt8), 64⟩

/-! ## THE THEOREMS -/

/-- THE straight-line theorem, concrete-value pin (the duel's own
    number): the template's execution for `double`'s LCNF shape computes
    `k + k` — in particular `double 21 = 42` at `k = 21`. Symbolic `k`. -/
theorem spec_double_ok (k : UInt64) :
    ∃ s', Sem.exec initI64 (specDouble k) = .ok s' ∧ s'.stack = [.i64 (k + k)] :=
  ⟨_, rfl, rfl⟩

/-- THE concrete pin, spelled out: 42. -/
theorem spec_double_42 :
    ∃ s', Sem.exec initI64 (specDouble 21) = .ok s' ∧ s'.stack = [.i64 42] :=
  spec_double_ok 21

/-- The adder-shape pin: with locals `l0 = 40`, `l1 = 2`, the template
    computes 40 + 2 = 42 — `adder 40 2`'s value, proven at the Sem
    level (concrete state, kernel-checked). -/
theorem spec_add_ok :
    ∃ s', Sem.exec ⟨fun n => match n with
                  | 0 => .i64 40 | 1 => .i64 2 | _ => .i64 0,
                  [], fun _ => (0 : UInt8), 64⟩ specAdd
      = .ok s' ∧ s'.stack = [.i64 42] :=
  ⟨_, rfl, rfl⟩

/-- THE general theorem (the theorem-shaped goal over the template):
    for ARBITRARY fuel ≥ 6, arbitrary local indices, arbitrary initial
    state whose stack is empty and whose locals `x`/`y` hold `a`/`b`,
    the emitted add-shape computes `a + b` onto the (otherwise empty)
    stack. This is the statement the per-shape pins instantiate. -/
theorem tpl_add_ret_ok (fuel : Nat) (x y l : Nat) (a b : UInt64) (s : Sem.State)
    (hx : s.locals x = .i64 a) (hy : s.locals y = .i64 b) (hs : s.stack = [])
    (hf : 6 ≤ fuel) :
    ∃ s', Sem.execList fuel s
        [Sem.Instr.localget x, Sem.Instr.localget y, .i64add, .localset l, .localget l]
      = .ok s' ∧ s'.stack = [.i64 (a + b)] := by
  obtain ⟨m, rfl⟩ : ∃ m', fuel = m'.succ.succ.succ.succ.succ.succ :=
    ⟨fuel - 6, by omega⟩
  -- one shot: simp unfolds execList/step along the 5 instructions. The
  -- machine pops the SECOND operand first (stack head = top), so i64.add
  -- computes b + a — commuted at the end.
  simp only [Sem.execList, Sem.step, hx, hy, hs]
  refine ⟨_, rfl, ?_⟩
  rw [UInt64.add_comm]
  rfl

-- The emitted program is WELL-TYPED (`checkStack` accepts it) — so
-- `Sem.typeSafety` applies: it can never raise the underflow error.
-- INTERPRETER-checked (`#guard`), not kernel-checked: the mutual
-- `checkStack`/`checkFrame` block is well-founded-compiled, so its
-- constant is opaque to the kernel — the same reason Sem.lean's own
-- checker tests are #guards.
#guard (match Sem.checkStack (fun _ => Sem.Ty.i64) [] (specDouble 21) with
        | .ok [Sem.Ty.i64] => true | _ => false) = true

/-! ## THE NEGATIVE CONTROL — the offset-swapped template -/

/-- THE BUGGY VARIANT (the offset-swap bug class — the same class that
    hit listUser's +0/+4 stores): the literal is stored one slot PAST
    its own, so `tplAdd` reads local 0 (still the init 0). -/
def tplLitBuggy (n : UInt64) (l : Nat) : List Sem.Instr :=
  [.i64const n, .localset (l + 1)]

/-- The buggy double-shape. -/
def specDoubleBuggy (k : UInt64) : List Sem.Instr :=
  tplLitBuggy k 0 ++ tplAdd 0 0 1 ++ tplRet 1

/-- The buggy template's execution yields 0 (it read the never-written
    local) — NOT `k + k`. -/
theorem spec_double_buggy_zero :
    (match Sem.exec initI64 (specDoubleBuggy 21) with
     | .ok s' => s'.stack | .error _ => []) = [.i64 0] :=
  rfl

-- THE CHECKER CANNOT CATCH IT (honest limitation, by design): the
-- buggy program still type-checks — `checkStack` is shape-only. The
-- disagreement is caught by EXECUTION (the theorem above), not typing.
-- Interpreter-checked (see the note above).
#guard (match Sem.checkStack (fun _ => Sem.Ty.i64) [] (specDoubleBuggy 21) with
        | .ok [Sem.Ty.i64] => true | _ => false) = true

/-- THE NEGATIVE INSTANCE: the buggy template's Sem-execution DISAGREES
    with the spec's value. If a regression re-introduced the swap, this
    theorem's shape is what the differential duel's sabotage control
    checks empirically. -/
theorem buggy_ne_spec :
    (match Sem.exec initI64 (specDoubleBuggy 21) with
     | .ok s' => s'.stack | .error _ => [])
      ≠
    (match Sem.exec initI64 (specDouble 21) with
     | .ok s' => s'.stack | .error _ => []) := by
  decide

/-! ## The EXTRACTION CHECKS — the backend's actual emission

The backend's `emitCode` is PURE (`M = StateT S (Except String)`) and
callable — no CoreM. The LCNF decls below are hand-constructed to the
KNOWN pipeline shape (the extraction gap is the header's point). The
`#guard`s run the REAL emitter at build time and pin its output's
lowering to the templates the theorems talk about. A regression that
changes the emission breaks the build. -/

/-- The known LCNF shape of `double`: `let x := lit k (UInt64);
    let y := fap UInt64.add [x, x]; return y`. -/
def doubleShape (k : UInt64) : Code .impure :=
  let x : FVarId := { name := `x }
  let y : FVarId := { name := `y }
  .let { fvarId := x, binderName := `x, type := .const `UInt64 []
       , value := .lit (.uint64 k) }
  (.let { fvarId := y, binderName := `y, type := .const `UInt64 []
        , value := .fap `UInt64.add #[.fvar x, .fvar x] }
  (.return y))

/-- The known LCNF shape of `adder`'s straight-line core: params a b;
    `let c := fap UInt64.add [a, b]; return c`. The params are
    PRE-BOUND (see `adderState`) under the `l0`/`l1` names the lowering
    resolves. -/
def adderShape : Code .impure :=
  let a : FVarId := { name := `a }
  let b : FVarId := { name := `b }
  let c : FVarId := { name := `c }
  .let { fvarId := c, binderName := `c, type := .const `UInt64 []
       , value := .fap `UInt64.add #[.fvar a, .fvar b] }
  (.return c)

/-- The emit-state with adder's params pre-bound — `bindNamed` keeps
    the PARAM's binder name, so the shapes below use `l0`/`l1` (and the
    let-bound `c` lands on the counter at `l2`). -/
def adderState : S :=
  { fvars := ({} : Std.HashMap FVarId (String × String))
      |>.insert { name := `a } ("l0", "i64")
      |>.insert { name := `b } ("l1", "i64")
  , n := 2 }

/-- RUN the backend's emitter (pure — `StateT S (Except String)`). The
    def is `partial` because `emitCode` is; used only under `#guard` /
    `#eval` (interpreter-evaluated), never under `decide`. -/
partial def runEmit (code : Code .impure) (st : S := {}) :
    Except String (List Wat.Instr) :=
  match (emitCode code).run st with
  | .ok (_, s) => .ok s.out.toList
  | .error e => .error e

-- The backend's ACTUAL emission for the double-shape lowers EXACTLY to
-- the `specDouble` template — the extraction check. BUILD-FAILING.
#guard (match runEmit (doubleShape 21) with
        | .ok is => lower is == some (specDouble 21)
        | .error _ => false) = true

-- Same check for the adder-shape. BUILD-FAILING.
#guard (match runEmit adderShape adderState with
        | .ok is => lower is == some specAdd
        | .error _ => false) = true

-- The emitted WAT for the record (visible in the build log):
-- `double`'s straight-line core is 8 instructions.
#eval match runEmit (doubleShape 21) with
  | .ok is => String.intercalate " ; " (is.map Wat.lineOf)
  | .error e => "emit error: " ++ e

-- The Sem-execution of the LOWERED backend output — the concrete
-- end-to-end pin (backend → lowering → machine → 42), interpreter-
-- evaluated at build time.
#guard (match runEmit (doubleShape 21) with
        | .ok is =>
            match lower is with
            | some sem =>
                (match Sem.exec initI64 sem with
                 | .ok s' => s'.stack == [.i64 42]
                 | .error _ => false)
            | none => false
        | .error _ => false) = true

/-! ## THE BRANCH SLICE — `emitCases`/`goAlts` → the Sem's structured `if_`

The backend's OBJECT-scrutinee path (`goAlts`: tag = `i32load8u` @4)
and its SCALAR path (`goAltsRaw`: branch on the value) both emit the
SAME nested-`if_` chain: level `k` = `local.get tag; i32.const cidx;
i32.eq` + `.if_` (the then-branch = alt k's body, the else-branch =
the NEXT level). The spec below mirrors the chain at the Sem level.

THE FRAGMENT (the branch ledger):

* COVERED: the 2-alt chain with STRAIGHT-LINE alt bodies (`let v :=
  lit k; return v` lowered — the straight-line lane's shapes). The
  ctor index = the alt's POSITION (the demo's scrutinee is Bool:
  false = 0, true = 1 — Lean's ctor order, which `goAltsRaw`'s
  `info.cidx` carries).
* THE SPEC'S ENTRY CONTRACT: the tag VALUE sits in local `disc` — for
  the SCALAR path (`goAltsRaw`) the theorem's `local 0 = tag`
  hypothesis is exactly its entry state. For the OBJECT path the read
  is no longer outside the spec: `specCasesLoad` below composes the
  `i32load8u` read (the tag-read lane; Sem's one-byte load) with the
  chain — the entry contract there is the OBJECT POINTER in local
  `base` and the tag byte IN MEMORY.
* THE TYPING GAP (honest): the emitter's branch join carries a RESULT
  (`if_ (some resTy) …`); Sem's frames are NO-RESULT (`checkFrame`) —
  the checker therefore REJECTS the (correct!) branch program (pinned
  in a #guard below). The branch slice's theorems are DIRECT exec
  computations; `Sem.typeSafety` does not apply here. The frame-entry
  restoration contract (what `checkFrame` guarantees for no-result
  frames) IS pinned dynamically in `branch_br0_entry_stack`.
* THE NEGATIVE CONTROL: the tag-INVERTED template (the comparison
  tests the WRONG alt's index — the branches dispatch swapped)
  executes the WRONG alt — the disagreement is a THEOREM
  (`branch_buggy_disagrees`), not a hope.
-/

/-- `goAlts`'s Sem-shape from ctor index `cidx`: level = the
    comparison + the nested `if_`; exhausted alts = the emitter's
    `unreachable`. (A literal cons chain — no `++` — so the
    `execList`/`step` equations fire under `simp only`.) -/
def specCasesFrom (disc : Nat) (cidx : UInt32) :
    List (List Sem.Instr) → List Sem.Instr
  | [] => [.unreach]
  | alt :: rest =>
      [.localget disc, .i32const cidx, .i32eq,
       .if_ alt (specCasesFrom disc (cidx + 1) rest)]

/-- THE cases template: `emitCases` + `goAlts` at the Sem level — the
    tag value in local `disc`, the alts' ctor indices = their
    positions. -/
def specCases (disc : Nat) (alts : List (List Sem.Instr)) : List Sem.Instr :=
  specCasesFrom disc 0 alts

/-- THE COMPOSED CASES TEMPLATE (the tag-read lane — closes the
    documented exclusion): the object-scrutinee's TAG READ is part of
    the spec. `emitCases`'s object path emits
    `local.get disc; i32.load8u offset=4; local.set tag` BEFORE
    `goAlts`; the template composes exactly that prefix (the byte read
    at `off` from the object pointer in local `base`, zero-extended,
    stashed in local 0) with the post-read chain `specCases 0 alts` —
    the OLD post-read template is the tail, unchanged. -/
def specCasesLoad (base off : Nat) (alts : List (List Sem.Instr)) :
    List Sem.Instr :=
  [.localget base, .i32load8u off, .localset 0] ++ specCases 0 alts

/-- THE COMPOSED BRANCH THEOREM (the tag-read lane's tractable leg,
    tag byte = 0): the load+branch template executes the CHOSEN alt
    with the tag read IN the spec — the object pointer in local `base`,
    the tag byte 0 AT `ptr + off` in memory, in bounds. The result =
    alt 0's value; the initial local 0 (overwritten by the read's
    `local.set`) is irrelevant. Arbitrary initial state, fuel ≥ 15 (the
    read's 3 steps + the dispatch's 12). Kernel-checked. -/
theorem specCasesLoad_ok (fuel : Nat) (z o : UInt64) (lz lo : Nat)
    (base off : Nat) (ptr : UInt32) (s : Sem.State)
    (hptr : s.locals base = .i32 ptr)
    (hmem : s.mem (ptr.toNat + off) = 0)
    (hbound : ptr.toNat + off < s.memSize)
    (hs : s.stack = []) (hf : 15 ≤ fuel) :
    ∃ s', Sem.execList fuel s
        (specCasesLoad base off
          [[.i64const z, .localset lz, .localget lz],
           [.i64const o, .localset lo, .localget lo]])
      = .ok s'
    ∧ s'.stack = [.i64 z] := by
  obtain ⟨m, rfl⟩ : ∃ m',
      fuel = m'.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ :=
    ⟨fuel - 15, by omega⟩
  simp [Sem.execList, Sem.step, hptr, hmem, hs, hbound, specCasesLoad,
    specCases, specCasesFrom]

/-- THE BRANCH THEOREM (the tractable version, the tag = 0 leg): the
    2-alt cases template with STRAIGHT-LINE alt bodies executes the
    CHOSEN alt — the tag `0` (false's ctor index) in local 0 selects
    alt 0; the result = the CHOSEN alt's value on the (otherwise
    unchanged) stack — the branch's preservation. Arbitrary initial
    state, fuel ≥ 12 (the dispatch's 8 steps + the 3-instruction body
    + the tail, with slack — the exact budget is the proof's
    `obtain`). Kernel-checked. (The statement splits by tag VALUE: a
    tag outside the ctor indices runs off the chain into the emitter's
    `unreachable` — `specCases_trap` below; a symbolic `if` over the
    tag would HIDE that.) -/
theorem specCases_ok (fuel : Nat) (z o : UInt64) (lz lo : Nat) (b : UInt32)
    (s : Sem.State) (hd : s.locals 0 = .i32 b) (hb : b = 0)
    (hs : s.stack = []) (hf : 12 ≤ fuel) :
    ∃ s', Sem.execList fuel s
        (specCases 0 [[.i64const z, .localset lz, .localget lz],
                      [.i64const o, .localset lo, .localget lo]])
      = .ok s'
    ∧ s'.stack = [.i64 z] := by
  subst hb
  obtain ⟨m, rfl⟩ : ∃ m',
      fuel = m'.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ := ⟨fuel - 12, by omega⟩
  simp [Sem.execList, Sem.step, hd, hs, specCases, specCasesFrom]

/-- THE mirror leg: the tag `1` (true's ctor index) selects alt 1. -/
theorem specCases_alt1 (fuel : Nat) (z o : UInt64) (lz lo : Nat) (b : UInt32)
    (s : Sem.State) (hd : s.locals 0 = .i32 b) (hb : b = 1)
    (hs : s.stack = []) (hf : 12 ≤ fuel) :
    ∃ s', Sem.execList fuel s
        (specCases 0 [[.i64const z, .localset lz, .localget lz],
                      [.i64const o, .localset lo, .localget lo]])
      = .ok s'
    ∧ s'.stack = [.i64 o] := by
  subst hb
  obtain ⟨m, rfl⟩ : ∃ m',
      fuel = m'.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ := ⟨fuel - 12, by omega⟩
  simp [Sem.execList, Sem.step, hd, hs, specCases, specCasesFrom]

/-- THE exhaustiveness leg: a tag outside the alts' ctor indices runs
    off the chain into the emitter's `unreachable` — the Sem-exec
    TRAPS (the same `unreach` the emitter's exhausted `goAlts` emits).
    The dispatch is TOTAL over the scrutinee's values: chosen, or
    trap — never a silent wrong-alt. -/
theorem specCases_trap (fuel : Nat) (z o : UInt64) (lz lo : Nat) (b : UInt32)
    (s : Sem.State) (hd : s.locals 0 = .i32 b) (hb : b ≠ 0) (hb1 : b ≠ 1)
    (hs : s.stack = []) (hf : 12 ≤ fuel) :
    ∃ e, Sem.execList fuel s
        (specCases 0 [[.i64const z, .localset lz, .localget lz],
                      [.i64const o, .localset lo, .localget lo]])
      = .error e ∧ e = .trap := by
  obtain ⟨m, rfl⟩ : ∃ m',
      fuel = m'.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ := ⟨fuel - 12, by omega⟩
  simp [Sem.execList, Sem.step, hd, hs, specCases, specCasesFrom,
    (show (0 : UInt32) ≠ b from fun hc => hb hc.symm),
    (show (1 : UInt32) ≠ b from fun hc => hb1 hc.symm)]

/-- THE checkFrame contract, dynamically: a `br 0` out of the chosen
    branch's inner frame exits at the frame-ENTRY stack — the values
    pushed inside since entry are dropped (Sem.lean's conservative
    no-result rule). This is the branch-restore behavior the scoped
    alt bodies rely on. Kernel-checked. -/
theorem branch_br0_entry_stack (fuel : Nat) (s : Sem.State)
    (hs : s.stack = []) (hf : 7 ≤ fuel) :
    ∃ s', Sem.execList fuel s
        [.i32const 1, .if_ [.block [.i64const 7, .drop, .br 0]] []]
      = .ok s' ∧ s'.stack = [] := by
  obtain ⟨m, rfl⟩ : ∃ m',
      fuel = m'.succ.succ.succ.succ.succ.succ.succ := ⟨fuel - 7, by omega⟩
  simp only [Sem.execList, Sem.step, hs]
  exact ⟨_, rfl, rfl⟩

/-! ## THE DEMO — the is-big branch shape (the duel's own function) -/

/-- The is-big BRANCH shape: the LCNF `cases` on a Bool param (the
    impl-param convention: Bool = raw i32).
    `DemoFn.isBig (x : UInt64) := x > 100` lowers to
    `let c := fap UInt64.decLt [100, x]; cases c` — the comparison
    producing the Bool is the `i64ltu` op layer (outside this
    fragment; the straight-line lane owns the operands), so THIS
    shape pins the dispatch: the Bool feeds `emitCases`'s scalar path
    directly, the alts return the duel's own values (0 / 1 as u64). -/
def isBigShape : Code .impure :=
  let x : FVarId := { name := `x }
  let z : FVarId := { name := `z }
  let o : FVarId := { name := `o }
  .cases ⟨`Bool, .const `UInt64 [], x,
    #[ .ctorAlt { name := `Bool.false, cidx := 0, size := 0, usize := 0, ssize := 0 }
         (.let { fvarId := z, binderName := `z, type := .const `UInt64 []
               , value := .lit (.uint64 0) } (.return z))
     , .ctorAlt { name := `Bool.true, cidx := 1, size := 0, usize := 0, ssize := 0 }
         (.let { fvarId := o, binderName := `o, type := .const `UInt64 []
               , value := .lit (.uint64 1) } (.return o)) ]⟩

/-- The emit-state with is-big's Bool param pre-bound (`l0`, i32 —
    `bindNamed` keeps the param's binder; the fresh-let counter starts
    at 1: z lands on `l1`, o on `l2`). -/
def isBigState : S :=
  { fvars := ({} : Std.HashMap FVarId (String × String))
      |>.insert { name := `x } ("l0", "i32")
  , n := 1 }

/-- The demo's Sem states: the Bool param in local 0 (1 = the
    comparison said true), empty stack, zeroed memory. -/
def bigParam (b : UInt32) : Sem.State :=
  ⟨fun n => match n with | 0 => .i32 b | _ => .i64 0,
   [], fun _ => (0 : UInt8), 64⟩

/-- The alts' lowered bodies, as the emitter produces them (z → l1,
    o → l2; the `.ret` dropped by the return convention). -/
def isBigAlts : List (List Sem.Instr) :=
  [[.i64const 0, .localset 1, .localget 1],
   [.i64const 1, .localset 2, .localget 2]]

-- The backend's ACTUAL emission for the is-big branch shape lowers
-- EXACTLY to the `specCases` template — the extraction check.
-- BUILD-FAILING.
#guard (match runEmit isBigShape isBigState with
        | .ok is => lower is == some (specCases 0 isBigAlts)
        | .error _ => false) = true

-- THE DUEL PINS (kernel-checked): the template computes is-big's own
-- values — the true-Bool (250 > 100) picks the true-alt (= 1), the
-- false-Bool (42 > 100) picks the false-alt (= 0).
theorem isBig_250 :
    ∃ s', Sem.exec (bigParam 1) (specCases 0 isBigAlts) = .ok s'
      ∧ s'.stack = [.i64 1] :=
  specCases_alt1 (fuel := 993 + 7) 0 1 1 2 1 (bigParam 1) rfl rfl rfl
    (by omega)

theorem isBig_42 :
    ∃ s', Sem.exec (bigParam 0) (specCases 0 isBigAlts) = .ok s'
      ∧ s'.stack = [.i64 0] :=
  specCases_ok (fuel := 993 + 7) 0 1 1 2 0 (bigParam 0) rfl rfl rfl
    (by omega)

-- THE DEMO, end-to-end (build-failing): backend emission → lowering →
-- machine → the duel's own values (is-big 250 = 1, is-big 42 = 0).
#guard (match runEmit isBigShape isBigState with
        | .ok is =>
            match lower is with
            | some sem =>
                (match Sem.exec (bigParam 1) sem with
                 | .ok s' => s'.stack == [.i64 1]
                 | .error _ => false)
                && (match Sem.exec (bigParam 0) sem with
                 | .ok s' => s'.stack == [.i64 0]
                 | .error _ => false)
            | none => false
        | .error _ => false) = true

-- The emitted WAT for the record (visible in the build log).
#eval match runEmit isBigShape isBigState with
  | .ok is => String.intercalate " ; " (is.map Wat.lineOf)
  | .error e => "emit error: " ++ e

-- HONEST LIMIT (typing): the emitter's branch join carries a RESULT
-- (`if_ (some resTy) …`), Sem's frames are no-result — the checker
-- REJECTS the (correct!) branch program. The branch slice's theorems
-- are direct exec computations; `Sem.typeSafety` does not apply here.
-- Interpreter-checked.
#guard (match Sem.checkStack
          (fun n => match n with | 0 => Sem.Ty.i32 | _ => Sem.Ty.i64) []
          (specCases 0 isBigAlts) with
        | .ok _ => false | .error _ => true) = true

-- The model-level branch-restore pin DOES type-check (no-result
-- frames) — so the typing gate covers it.
#guard (match Sem.checkStack (fun _ => Sem.Ty.i64) []
          [.i32const 1, .if_ [.block [.i64const 7, .drop, .br 0]] []] with
        | .ok [] => true | _ => false) = true

/-! ## THE TAG-READ SLICE — the composed load+branch (the exclusion,
closed) -/

/-- The demo's OBJECT state (the composed template's inputs): the
    object pointer 4 in local 1, the tag byte 0 (false's ctor index)
    AT `4 + 4 = 8` — the emitter's `i32.load8_u offset=4` shape — and
    a decoy byte 1 at address 9 (the wrong-offset control's target).
    64 zeroed bytes otherwise. -/
def tagObj : Sem.State :=
  ⟨fun n => match n with | 1 => .i32 4 | _ => .i64 0,
   [], fun i => if i = 9 then (1 : UInt8) else (0 : UInt8), 64⟩

-- The read PREFIX is well-typed (pops the i32 ptr, pushes the i32
-- tag — the load's checker case; the tag stash local 0 is a fresh
-- i32, as the emitter's `bindFresh` makes it). Interpreter-checked.
#guard (match Sem.checkStack
          (fun n => match n with | 0 | 1 => Sem.Ty.i32 | _ => Sem.Ty.i64) []
          [.localget 1, .i32load8u 4, .localset 0] with
        | .ok [] => true | _ => false) = true

-- The COMPOSED load+branch template inherits the documented typing
-- gap (the emitter's branch join carries a result; Sem's frames are
-- no-result) — same rejection as the post-read `specCases`. The
-- theorems are direct exec computations. Interpreter-checked.
#guard (match Sem.checkStack
          (fun n => match n with | 0 | 1 => Sem.Ty.i32 | _ => Sem.Ty.i64) []
          (specCasesLoad 1 4 isBigAlts) with
        | .ok _ => false | .error _ => true) = true

-- THE COMPOSED POSITIVE (kernel-checked): with the tag read IN the
-- spec, the correct offset (4) reads the tag byte at 4+4 = 8 = 0 →
-- the false-alt (= 0). Same verdict as the post-read `isBig_42`.
theorem loadCases_correct :
    (match Sem.exec tagObj (specCasesLoad 1 4 isBigAlts) with
     | .ok s' => s'.stack | .error _ => []) = [.i64 0] := by
  decide

/-- THE BUGGY VARIANT (the wrong-offset bug class): the tag read at
    offset 5 hits the decoy byte (1 = true's index) — the dispatch
    runs the WRONG alt. The checker cannot catch it (same shape —
    `checkStack` is shape-only, by design); the disagreement is
    caught by EXECUTION (the theorems below). -/
def specCasesLoadBuggy (base off : Nat) (alts : List (List Sem.Instr)) :
    List Sem.Instr :=
  [.localget base, .i32load8u (off + 1), .localset 0] ++ specCases 0 alts

-- The buggy offset's verdict: the decoy byte 1 → the TRUE-alt's value
-- comes out — NOT the false-alt's the correct template picks.
theorem loadCases_buggy_wrong_alt :
    (match Sem.exec tagObj (specCasesLoadBuggy 1 4 isBigAlts) with
     | .ok s' => s'.stack | .error _ => []) = [.i64 1] := by
  decide

-- THE NEGATIVE INSTANCE: the wrong-offset load DISAGREES with the
-- correct composed template (same object state, different alt). If a
-- regression re-offset the tag read, this theorem's shape is what the
-- differential duel's sabotage control checks empirically.
theorem loadCases_buggy_disagrees :
    (match Sem.exec tagObj (specCasesLoadBuggy 1 4 isBigAlts) with
     | .ok s' => s'.stack | .error _ => [])
      ≠
    (match Sem.exec tagObj (specCasesLoad 1 4 isBigAlts) with
     | .ok s' => s'.stack | .error _ => []) := by
  intro h
  rw [loadCases_buggy_wrong_alt, loadCases_correct] at h
  simp at h

/-! ## THE NEGATIVE CONTROL — the tag-INVERTED branch template -/

/-- THE BUGGY VARIANT (the tag-inversion bug class): every level's
    if-branches are SWAPPED — the then-branch runs the NEXT level
    instead of this alt, so the false-alt fires when the tag = 1 and
    vice versa (the comparison testing the wrong alt's index). -/
def specCasesBuggyFrom (disc : Nat) (cidx : UInt32) :
    List (List Sem.Instr) → List Sem.Instr
  | [] => [.unreach]
  | alt :: rest =>
      [.localget disc, .i32const cidx, .i32eq,
       .if_ (specCasesBuggyFrom disc (cidx + 1) rest) alt]

def specCasesBuggy (disc : Nat) (alts : List (List Sem.Instr)) :
    List Sem.Instr := specCasesBuggyFrom disc 0 alts

-- The inverted template's verdict at tag = 0: the TRUE-alt's value
-- comes out — NOT the false-alt's the correct template picks.
theorem branch_buggy_wrong_alt :
    (match Sem.exec (bigParam 0) (specCasesBuggy 0 isBigAlts) with
     | .ok s' => s'.stack | .error _ => []) = [.i64 1] := by
  decide

-- THE NEGATIVE INSTANCE: the inverted dispatch DISAGREES with the
-- correct template (same input, different result). If a regression
-- re-inverted the tag comparison, this theorem's shape is what the
-- differential duel's sabotage control checks empirically.
-- The correct template's verdict at tag = 0 (the positive side, for
-- the disagreement theorem; decide on the `=` form — the `≠`'s
-- Decidable instance does not reduce for the kernel, see below).
theorem branch_buggy_correct_zero :
    (match Sem.exec (bigParam 0) (specCases 0 isBigAlts) with
     | .ok s' => s'.stack | .error _ => []) = [.i64 0] := by
  decide

-- THE NEGATIVE INSTANCE: the inverted dispatch DISAGREES with the
-- correct template (same input, different result). Proved by composing
-- the two positive computations (decide on the bare `≠` gets stuck —
-- the List-equality Decidable instance does not whnf through the two
-- exec matches — so the rewrites carry the computation).
theorem branch_buggy_disagrees :
    (match Sem.exec (bigParam 0) (specCasesBuggy 0 isBigAlts) with
     | .ok s' => s'.stack | .error _ => [])
      ≠
    (match Sem.exec (bigParam 0) (specCases 0 isBigAlts) with
     | .ok s' => s'.stack | .error _ => []) := by
  intro h
  rw [branch_buggy_wrong_alt, branch_buggy_correct_zero] at h
  simp at h

/-! ## THE CALLS + CLOSURES SLICE — the calling convention's contract

THE HONEST SCOPE DECISION (the lane's line): `Sem.Instr` has NO
`call`/`call_indirect` and `Sem.State` has NO call-frames — the machine
is FLAT. Adding the call-stack to the model is the big change (the next
seam). This slice instead proves the CALLING CONVENTION as a CONTRACT
THEOREM over the two instruction lists the convention connects: the
caller's CALL-PREP (the pushes) and the callee's ENTRY PROLOGUE (the
binding pops). The STACK AGREEMENT = the prologue: the composition of
the prep and the prologue passes each value through — param 0 = the
DEEPEST push (wasm's `call` binds param i to the i-th pushed value),
stack drained. This is the contract, NOT the full call semantics — the
header's ledger owns the difference.

THE CONVENTION IS THE REAL ONE — the golden's trampolines
(`goldens/demo.wat`):

```
(func $pap_curried._boxed_1 (param $c i32) (param $x0 i32) (param $x1 i32) (result i32)
  local.get $c; i32.load offset=16   -- the partial arg (closure memory)
  local.get $x0; local.get $x1       -- the fresh args, IN ORDER
  call $curried._boxed)
```

and the caller's closure-apply arm (`emitLet`'s `.fvar f args`):
`local.get c; <fresh args in order>; local.get c; i32.load 8;
call_indirect sig_nbox; local.set l` — the trampoline's param 0 = the
closure ptr (pushed FIRST = deepest), params 1.. = the fresh args.
(The trampolines themselves are emitted inside `emitModule`, not
`emitCode` — the extraction hooks below reach only the caller's prep;
the trampoline templates are pinned to the golden and to the emitter's
trampoline loop by construction.)

THE CALLS LEDGER:

* COVERED: the convention's VALUE-PATH — the caller's pushes, the
  callee's binding pops, the trampoline's arg-forward (the partial
  args' delivered VALUES as placeholders), the target's straight-line
  body (the adder shape), two hops composed = the run-paps 5 = 8
  inner-call path, and the arg-order-swap negative control.
* THE MODEL DELTA: none — Sem.lean is UNCHANGED (the scope decision:
  no call-frames). The frame separation (the callee's param locals live
  in ITS OWN frame) appears in the theorems as the param-locals'
  pairwise-distinctness hypotheses — the flat model's honest stand-in.
* NOT COVERED: the memory loads around calls (`i32.load 16` the
  partial read, `i32.load 8` the fnIdx, the box/unbox loads — Sem
  models no loads; the templates pin the loads' STACK SHAPE with the
  delivered value as an explicit const), the `call_indirect` dispatch
  (the funcref table, the fnIdx), the boxed result path back (the
  caller's `local.set l` after the call), recursion/multiple frames,
  and the RC discipline (`rc_inc`/`rc_dec` around calls).
* THE NEGATIVE CONTROL: the arg-order-swapped prep (the fresh args
  pushed in reverse — the calling-convention bug class) delivers the
  SWAPPED values to the callee's params; the disagreement with the
  convention is a THEOREM (`call_convention2_buggy_disagrees`).
-/

/-- The caller's call-prep for a 1-fresh closure apply (the
    `pap_runPaps._lam_1._boxed_1` shape): push the closure ptr (the
    trampoline's param 0 — FIRST = deepest), then the fresh arg. The
    unmodeled TAIL — `local.get c; i32.load 8` (the fnIdx read) +
    `call_indirect sig_1box` + the result `local.set` — is outside the
    fragment (no loads, no call layer). -/
def tplCallPrep1 (c x : Nat) : List Sem.Instr :=
  [.localget c, .localget x]

/-- Same for a 2-fresh apply (the `pap_curried._boxed_1` shape). -/
def tplCallPrep2 (c x0 x1 : Nat) : List Sem.Instr :=
  [.localget c, .localget x0, .localget x1]

/-- The callee's ENTRY PROLOGUE (1-fresh shape): a wasm `call` binds
    the callee's param i to the i-th pushed value (param 0 = the
    deepest). Sem v1 is FLAT (no call-frames — the scope decision), so
    the binding is modeled as the prologue's pops — `local.set` from
    the stack, TOP-first (the LAST-pushed fresh arg = the HIGHEST
    param). -/
def tplPrologue1 (p0 p1 : Nat) : List Sem.Instr :=
  [.localset p1, .localset p0]

/-- The 2-fresh entry prologue. -/
def tplPrologue2 (p0 p1 p2 : Nat) : List Sem.Instr :=
  [.localset p2, .localset p1, .localset p0]

/-- THE CALLING-CONVENTION THEOREM (the 1-fresh closure-apply
    contract): the caller's pushes are EXACTLY the callee's expected
    entry state — the prep/prologue composition passes each value
    through: param 0 = the closure ptr, param 1 = the fresh arg, stack
    drained. Arbitrary initial state, symbolic values, fuel ≥ 5. The
    distinctness hypothesis = the flat model's frame separation (the
    callee's param locals are its own). Kernel-checked. -/
theorem call_convention1 (fuel : Nat) (c x p0 p1 : Nat) (C A : Sem.Val)
    (s : Sem.State) (hc : s.locals c = C) (ha : s.locals x = A)
    (hs : s.stack = []) (hd : p0 ≠ p1) (hf : 5 ≤ fuel) :
    ∃ s', Sem.execList fuel s (tplCallPrep1 c x ++ tplPrologue1 p0 p1)
      = .ok s'
    ∧ s'.locals p0 = C ∧ s'.locals p1 = A ∧ s'.stack = [] := by
  obtain ⟨m, rfl⟩ : ∃ m', fuel = m' + 5 := ⟨fuel - 5, by omega⟩
  simp only [tplCallPrep1, tplPrologue1, List.nil_append, List.cons_append,
    Sem.execList, Sem.step, hc, ha, hs]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · exact if_pos rfl
  · simp [Ne.symm hd]
  · rfl

/-- THE CALLING-CONVENTION THEOREM (the 2-fresh shape —
    `pap_curried._boxed_1`): param 0 = the closure ptr, param 1 = fresh
    arg 0, param 2 = fresh arg 1, stack drained. Kernel-checked. -/
theorem call_convention2 (fuel : Nat) (c x0 x1 p0 p1 p2 : Nat)
    (C A B : Sem.Val) (s : Sem.State)
    (hc : s.locals c = C) (h0 : s.locals x0 = A) (h1 : s.locals x1 = B)
    (hs : s.stack = [])
    (hd01 : p0 ≠ p1) (hd02 : p0 ≠ p2) (hd12 : p1 ≠ p2)
    (hf : 7 ≤ fuel) :
    ∃ s', Sem.execList fuel s (tplCallPrep2 c x0 x1 ++ tplPrologue2 p0 p1 p2)
      = .ok s'
    ∧ s'.locals p0 = C ∧ s'.locals p1 = A ∧ s'.locals p2 = B
    ∧ s'.stack = [] := by
  obtain ⟨m, rfl⟩ : ∃ m', fuel = m' + 7 := ⟨fuel - 7, by omega⟩
  simp only [tplCallPrep2, tplPrologue2, List.nil_append, List.cons_append,
    Sem.execList, Sem.step, hc, h0, h1, hs]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · exact if_pos rfl
  · simp [Ne.symm hd01]
  · simp [Ne.symm hd02, Ne.symm hd12]
  · rfl

/-- The trampoline's arg-forward (1 partial + 1 fresh — the
    `pap_runPaps._lam_1._boxed_1` shape): push the partial arg (the
    value `local.get c; i32.load 16` delivers — the LOAD is outside
    the modeled fragment: Sem models no loads; the template pins the
    stack SHAPE with the delivered value as an explicit `i32const`),
    then the fresh arg, then the target call (also outside the call
    layer). -/
def tplTrampFwd1 (p : UInt32) (x : Nat) : List Sem.Instr :=
  [.i32const p, .localget x]

/-- The trampoline's arg-forward (1 partial + 2 fresh — the golden's
    `pap_curried._boxed_1` shape). -/
def tplTrampFwd2 (p : UInt32) (x0 x1 : Nat) : List Sem.Instr :=
  [.i32const p, .localget x0, .localget x1]

/-- THE TRAMPOLINE'S CONTRACT (the trampoline→target hop, 1-fresh
    shape): the forward puts the loaded partial DEEPEST (the target's
    param 0) and the fresh arg on top — the composition with the
    target's prologue delivers partial → param 0, fresh → param 1.
    Kernel-checked. -/
theorem trampoline_convention1 (fuel : Nat) (p : UInt32) (x q0 q1 : Nat)
    (A : Sem.Val) (s : Sem.State) (ha : s.locals x = A)
    (hs : s.stack = []) (hd : q0 ≠ q1) (hf : 5 ≤ fuel) :
    ∃ s', Sem.execList fuel s (tplTrampFwd1 p x ++ tplPrologue1 q0 q1)
      = .ok s'
    ∧ s'.locals q0 = .i32 p ∧ s'.locals q1 = A ∧ s'.stack = [] := by
  obtain ⟨m, rfl⟩ : ∃ m', fuel = m' + 5 := ⟨fuel - 5, by omega⟩
  simp only [tplTrampFwd1, tplPrologue1, List.nil_append, List.cons_append,
    Sem.execList, Sem.step, ha, hs]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · exact if_pos rfl
  · simp [Ne.symm hd]
  · rfl

/-- THE TRAMPOLINE'S CONTRACT (the golden's `pap_curried._boxed_1`
    shape): partial → param 0, fresh args → params 1/2, in order.
    Kernel-checked. -/
theorem trampoline_convention2 (fuel : Nat) (p : UInt32) (x0 x1 q0 q1 q2 : Nat)
    (A B : Sem.Val) (s : Sem.State)
    (h0 : s.locals x0 = A) (h1 : s.locals x1 = B) (hs : s.stack = [])
    (hd01 : q0 ≠ q1) (hd02 : q0 ≠ q2) (hd12 : q1 ≠ q2)
    (hf : 7 ≤ fuel) :
    ∃ s', Sem.execList fuel s (tplTrampFwd2 p x0 x1 ++ tplPrologue2 q0 q1 q2)
      = .ok s'
    ∧ s'.locals q0 = .i32 p ∧ s'.locals q1 = A ∧ s'.locals q2 = B
    ∧ s'.stack = [] := by
  obtain ⟨m, rfl⟩ : ∃ m', fuel = m' + 7 := ⟨fuel - 7, by omega⟩
  simp only [tplTrampFwd2, tplPrologue2, List.nil_append, List.cons_append,
    Sem.execList, Sem.step, h0, h1, hs]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · exact if_pos rfl
  · simp [Ne.symm hd01]
  · simp [Ne.symm hd02, Ne.symm hd12]
  · rfl

/-! ## THE DEMO — the run-paps 5 = 8 inner-call path

`runPaps 5 = applyAll [adder 1, adder 2] 5 = 8` — the inner calls are
REAL pap applications: the `adder 2` closure applied to 5 (= 7), then
the `adder 1` closure applied to 7 (= 8). Each hop = the convention
composed with the adder body: the caller's prep, the trampoline's
binding, the trampoline's forward (the partial = the value the
closure-memory load + unbox delivers — the `i64const` placeholder; the
loads are the excluded memory layer), the target's binding, the adder
body (`tplAdd`, the straight-line lane's shape). All-concrete, so the
kernel checks it by `rfl`.
-/

/-- The demo's init state: local 0 = applyAll's x (i64 5); the closure
    ptrs (locals 1, 8) are placeholders (the real pap pointers come
    from `alloc` — outside the fragment; only the push ORDER matters
    here, the ptr values are never read). -/
def demoInit : Sem.State :=
  ⟨fun n => match n with | 0 => .i64 5 | _ => .i32 0,
   [], fun _ => (0 : UInt8), 64⟩

/-- The two-hop composition (locals: 0 = x, 1 = c1, 2/3 = the adder-2
    trampoline's params, 4/5 = its target's params, 6 = the inner
    result, 7 = hop 2's fresh arg, 8 = c2, 9/10 = the adder-1
    trampoline's params, 11/12 = its target's params, 13 = the final
    result). -/
def demoProg : List Sem.Instr :=
  -- hop 1: applyAll applies the `adder 2` closure to 5
  tplCallPrep1 1 0 ++ tplPrologue1 2 3
    ++ [.i64const 2, .localget 3] ++ tplPrologue1 4 5
    ++ [.localget 4, .localget 5, .i64add, .localset 6]
  -- the inner result becomes hop 2's fresh arg
    ++ [.localget 6, .localset 7]
  -- hop 2: applyAll applies the `adder 1` closure to 7
    ++ tplCallPrep1 8 7 ++ tplPrologue1 9 10
    ++ [.i64const 1, .localget 10] ++ tplPrologue1 11 12
    ++ [.localget 11, .localget 12, .i64add, .localset 13, .localget 13]

/-- THE DEMO (kernel-checked): the composed two-hop value-path computes
    run-paps 5 = 8's inner path — adder 2 on 5 = 7, adder 1 on 7 = 8. -/
theorem runPaps_inner_8 :
    ∃ s', Sem.exec demoInit demoProg = .ok s' ∧ s'.stack = [.i64 8] :=
  ⟨_, rfl, rfl⟩

-- The convention program is WELL-TYPED (all-i64 context — the
-- value-path's types): `Sem.typeSafety` applies to it. The boxed real
-- convention (i32 ptrs) is likewise typed; the loads/calls are the
-- excluded layer, not typing failures. Interpreter-checked (#guard —
-- the checker is well-founded-compiled, opaque to the kernel).
#guard (match Sem.checkStack (fun _ => Sem.Ty.i64) []
          (tplCallPrep1 0 1 ++ tplPrologue1 2 3) with
        | .ok [] => true | _ => false) = true

/-- The closure-apply LCNF shape (`emitLet`'s `.fvar f args` arm — the
    CALLER side of the convention): `let r := f c [x]` where f is an
    object-typed fvar (the closure). -/
def closureApplyShape : Code .impure :=
  let c : FVarId := { name := `c }
  let x : FVarId := { name := `x }
  let r : FVarId := { name := `r }
  .let { fvarId := r, binderName := `r, type := .const `UInt64 []
       , value := .fvar c #[.fvar x] }
  (.return r)

/-- The emit-state with the closure ptr pre-bound (`l0`, i32 — object
    pointers are i32) and the fresh arg (`l1`, i64); the result lands
    on `l2`. -/
def closureApplyState : S :=
  { fvars := ({} : Std.HashMap FVarId (String × String))
      |>.insert { name := `c } ("l0", "i32")
      |>.insert { name := `x } ("l1", "i64")
  , n := 2 }

-- The CALLER-prep extraction check: the backend's ACTUAL emission for
-- the closure-apply arm STARTS with the convention's pushes — the
-- first two instructions lower EXACTLY to `tplCallPrep1 0 1` (the
-- closure ptr, then the fresh arg); the emitted tail = the fnIdx load
-- + the `call_indirect` + the result `local.set` + the return's
-- `local.get`/`ret` (8 instructions total). The load/call tail is
-- outside the flat fragment — `lower` fails on it LOUDLY (by design),
-- so only the pushes are pinned here; the trampolines themselves are
-- emitted inside `emitModule` (not `emitCode`) and are pinned to the
-- golden `pap_curried._boxed_1` by construction. BUILD-FAILING.
#guard (match runEmit closureApplyShape closureApplyState with
        | .ok is =>
            is.length == 8
              && (match (is.take 2).mapM lowerI with
                  | some sem => sem.flatten == tplCallPrep1 0 1
                  | none => false)
        | .error _ => false) = true

/-! ## THE NEGATIVE CONTROL — the arg-order-swapped call prep -/

/-- THE BUGGY VARIANT (the arg-order swap — the calling-convention bug
    class): the fresh args pushed in REVERSE order. The checker cannot
    catch it (same stack SHAPE — `checkStack` is shape-only, by
    design); the EXECUTION disagrees. -/
def tplCallPrep2Buggy (c x0 x1 : Nat) : List Sem.Instr :=
  [.localget c, .localget x1, .localget x0]

-- The swapped prep still TYPE-CHECKS (the honest limitation, by
-- design — same shape). Interpreter-checked.
#guard (match Sem.checkStack (fun _ => Sem.Ty.i64) []
          (tplCallPrep2Buggy 0 1 2 ++ tplPrologue2 3 4 5) with
        | .ok [] => true | _ => false) = true

/-- The swapped prep delivers the SWAPPED values: param 1 = B, param 2
    = A (the same distinctness hypotheses as the convention). --/
theorem call_convention2_buggy (fuel : Nat) (c x0 x1 p0 p1 p2 : Nat)
    (C A B : Sem.Val) (s : Sem.State)
    (hc : s.locals c = C) (h0 : s.locals x0 = A) (h1 : s.locals x1 = B)
    (hs : s.stack = [])
    (hd01 : p0 ≠ p1) (hd02 : p0 ≠ p2) (hd12 : p1 ≠ p2)
    (hf : 7 ≤ fuel) :
    ∃ s', Sem.execList fuel s
        (tplCallPrep2Buggy c x0 x1 ++ tplPrologue2 p0 p1 p2)
      = .ok s'
    ∧ s'.locals p1 = B ∧ s'.locals p2 = A := by
  obtain ⟨m, rfl⟩ : ∃ m', fuel = m' + 7 := ⟨fuel - 7, by omega⟩
  -- the swapped pushes (C, then B, then A) pop TOP-first: A → p2,
  -- B → p1, C → p0 — the values land SWAPPED.
  simp only [tplCallPrep2Buggy, tplPrologue2, List.nil_append,
    List.cons_append, Sem.execList, Sem.step, hc, h0, h1, hs]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [Ne.symm hd01]
  · simp [Ne.symm hd02, Ne.symm hd12]

/-- THE NEGATIVE INSTANCE: the swapped prep DISAGREES with the
    convention — same input, different callee entry-state (param 1
    gets B instead of A). If a regression re-swapped the arg pushes,
    this theorem's shape is what the differential duel's sabotage
    control checks empirically. -/
theorem call_convention2_buggy_disagrees
    (fuel : Nat) (c x0 x1 p0 p1 p2 : Nat) (A B : Sem.Val) (s : Sem.State)
    (h0 : s.locals x0 = A) (h1 : s.locals x1 = B) (hs : s.stack = [])
    (hd01 : p0 ≠ p1) (hd02 : p0 ≠ p2) (hd12 : p1 ≠ p2)
    (hAB : A ≠ B) (hf : 7 ≤ fuel) :
    ∃ s1 s2,
      Sem.execList fuel s (tplCallPrep2 c x0 x1 ++ tplPrologue2 p0 p1 p2)
        = .ok s1
      ∧ Sem.execList fuel s
          (tplCallPrep2Buggy c x0 x1 ++ tplPrologue2 p0 p1 p2)
        = .ok s2
      ∧ s1.locals p1 ≠ s2.locals p1 := by
  obtain ⟨s1, he1, -, hA, -, -⟩ :=
    call_convention2 fuel c x0 x1 p0 p1 p2 (s.locals c) A B s rfl h0 h1 hs
      hd01 hd02 hd12 hf
  obtain ⟨s2, he2, hB, -⟩ :=
    call_convention2_buggy fuel c x0 x1 p0 p1 p2 (s.locals c) A B s rfl h0 h1 hs
      hd01 hd02 hd12 hf
  exact ⟨s1, s2, he1, he2, fun h => hAB (hA.symm.trans (h.trans hB))⟩

end WasmBackend.Correct
