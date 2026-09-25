/-
# WasmCore.Validate — the stack-typing judgment (validation by
# construction + the checked bridge)

The seed's FIRST checked judgment: a function body's stack effect
validates against its signature. Pattern #1 (15-patterns) rides the
kit's `Kit.CheckedProp` — the relation (`BodyTy`) + the decidable
checker (`checkFlow`/`checkBody`/`checkFunc`) + the proved bridge in
BOTH directions (`checkBody_sound`, `checkBody_complete`): for this
fragment the checker and the relation agree EXACTLY, so the
completeness constructor is `.proved` — never a defaulted `true` (the
design doc's loud-two-constructor discipline). The conservative
exclusions are absence from the AST (no block results, no branch-depth
check — the design doc's documented gaps), not checker strictness.

Checker structure (the layering that makes the bridge cheap):
`stepFlag` is the per-instruction step returning a STOP FLAG with the
stack — the transfer forms (`br`/`unreach`/`ret`) stop the fold (their
tail is statically dead) and everything else continues; `checkFlow` is
the fold, `checkBody` forgets the flag. Stacks are HEAD = TOP;
`Ctx.resRev` is the enclosing function's results REVERSED, because
pushing r1..rn leaves `[rn; …; r1]` — the return's expected shape.
Per-op effects are DATA — the ONE op table lives in `WasmCore.OpTable`
(07-extensibility R6: a row per op — name, opcode, sig, sem note —
never parallel semantics tables); this module folds its `opPop`/
`opPush`/`memPop`/`memPush` projections (rfl-eliminable, design doc
§2).

The refusal surface is the envelope discipline (05 §4): the checker's
errors are DATA — a closed `ValidateError` inductive whose ctors are
the failure KINDS with their payload (the expected vs got stacks, the
need, the index), never a bare string; the rendering is `toDiag` into
the ONE diagnostic envelope (`Kit.Diag`), the E-codes the WV-family
constants (the persisted registry's allocation is a later integration
step — the constants land in one place, ready for it). The checker's
SEMANTICS are unchanged: same accept/refuse, the error CONTENT is the
envelope.

The five questions (notes/v3/01-core.md):

- **Root**: the judgment is a CROSSING (the decidable checker ↔ the
  propositional relation), stated once as the kit's CheckedProp; the
  relation itself is Universe-side data (an inductive).
- **Carrier grade**: Kit.CheckedProp — the statement-as-instance grade
  (`{a // check a = true}` maps into the P-witnesses; with `.proved`
  completeness it upgrades to a true `Iso` via `CheckedProp.toIso`).
- **Spine reading**: the checker is the READ of the instruction list
  (a fold to a stack verdict); Validate consumes what the emitter
  accumulates.
- **Ladder rung**: the bridge theorems are hand theorems with named
  relational content (the checker/relation agreement) — rung 6; the
  completeness direction routes through plain relation-induction.
- **Gate row**: none at the gates yet (WasmCore is not in
  Gates.Packages' gated set) + WasmCoreTests'
  positive/negative validator suites.

Consumer trail: rides `Kit.CheckedProp` (pattern #1's carrier),
`Kit.Diag` (the ONE envelope's Kit face), `WasmCore.Types`,
`WasmCore.Instr`, `WasmCore.OpTable` (the ONE op table's sig
projections), `WasmCore.Module`. Core-only.
-/

import Kit.CheckedProp
import Kit.Diag
import WasmCore.Types
import WasmCore.Instr
import WasmCore.OpTable
import WasmCore.Module

namespace WasmCore

/-! ## The pop/push discipline -/

/-- Pop `pop` (head = top) then push `push`. Total; `none` = the
    operand types mismatch. This is the ONE operand-shape engine —
    `opPop`/`memPop`/call params all ride it. -/
def popPush (pop push : List ValType) (s : List ValType) : Option (List ValType) :=
  match pop, s with
  | [], _ => some (push ++ s)
  | _ :: _, [] => none
  | p :: ps, t :: ts => if p = t then popPush ps push ts else none

theorem popPush_append : ∀ (pop push ts : List ValType),
    popPush pop push (pop ++ ts) = some (push ++ ts) := by
  intro pop
  induction pop with
  | nil => intro push ts; rfl
  | cons p ps ih =>
    intro push ts
    simp only [popPush, List.cons_append]
    exact ih push ts

theorem popPush_some : ∀ (pop push s s' : List ValType),
    popPush pop push s = some s' → ∃ ts, s = pop ++ ts ∧ s' = push ++ ts := by
  intro pop
  induction pop with
  | nil =>
    intro push s s' h
    exact ⟨s, rfl, by simp [popPush] at h; exact h.symm⟩
  | cons p ps ih =>
    intro push s s' h
    match s with
    | [] => simp [popPush] at h
    | t :: ts =>
      simp only [popPush] at h
      split at h
      · next hin =>
          obtain ⟨u, hu1, hu2⟩ := ih push ts s' h
          exact ⟨u, by simp only [List.cons_append, hu1, hin], hu2⟩
      · next => exact absurd h (by simp)

/-! ## The error vocabulary (the envelope discipline, 05 §4) -/

/-- The value-type rendering the diagnostics use (the Diag envelope's
    string fields are ids-and-strings). -/
def renderValType : ValType → String
  | .i32 => "i32" | .i64 => "i64" | .f32 => "f32" | .f64 => "f64"
  | .funcref => "funcref" | .externref => "externref"

/-- The stack rendering: `[i32, i64]` (head = top). -/
def renderValTypes : List ValType → String :=
  fun ts => "[" ++ String.intercalate ", " (ts.map renderValType) ++ "]"

/-- THE closed-world failure vocabulary: the checker's refusal KINDS
    as ctors with their payload data — the expected vs got stacks, the
    operand need, the offending index. The checker and the bridge
    theorems ride these; the Diag rendering is `toDiag` (the ONE
    envelope). Closed on purpose: a new failure kind is a new ctor,
    and the compiler drives the extension (15-patterns #15). -/
inductive ValidateError where
  /-- The stack does not provide the pops (the ONE operand-shape
      engine's refusal — `op`/`mem`/`call`/`brif`/the frame entries;
      the valid space is the pops form `expected ++ ts`). -/
  | operandMismatch (expected got : List ValType)
  /-- The operand stack is empty but operands are still needed
      (`need` = how many). -/
  | underflow (need : Nat)
  /-- `local.set`/`local.tee`'s top operand is not the local's type. -/
  | localTypeMismatch (n : Nat) (expected got : ValType)
  /-- A frame's exit stack is not its entry stack (`block`/`loop`/
      `if_`). -/
  | frameMismatch (expected got : List ValType)
  /-- `select`'s stack is not one of its two live rows
      (`i32 :: t :: t :: ts`, `t ∈ {i32, i64}`). -/
  | selectOperands (got : List ValType)
  /-- `ret`'s stack is not the enclosing function's results. -/
  | unbalancedReturn (expected got : List ValType)
  /-- The body's final stack is not the function's results. -/
  | unbalancedEnd (expected got : List ValType)
  /-- The local index is unbound. -/
  | unboundLocal (n : Nat)
  /-- The function index is unbound. -/
  | unboundFunc (n : Nat)
  /-- A function's type index is past the type section (`fn` = the
      function's index). -/
  | typeIndexRange (fn tyIdx : Nat)
  /-- `callindirect` over an ABSENT table (the module declares no
      table section — the indirect-call lane's table-index
      discipline; the wire's table index is the constant 0). -/
  | unboundTable
  /-- `callindirect`'s type index is past the type section. -/
  | indirectTypeRange (tyIdx : Nat)
  /-- A table entry names a function index past the function section
      (the table's initialization is the active-element face — a
      dangling entry would dispatch to nothing). -/
  | tableEntryRange (fn : Nat)
  /-- The per-function wrapper: the module driver pins WHICH function
      refused (the Diag context's frame). -/
  | atFunc (i : Nat) (e : ValidateError)
  deriving Repr, BEq, DecidableEq, Inhabited

/-! The validator's E-code CONSTANTS (the WV family): they land here,
in one place, ready for the persisted registry (`Kit.CodeRegistry`'s
stable allocation is a later integration step; the meaning of the
string lives at the registry, never in the spelling alone). -/
namespace ValidateError

def ecOperandMismatch : Kit.ECode := ⟨"WV1001"⟩
def ecUnderflow : Kit.ECode := ⟨"WV1002"⟩
def ecLocalTypeMismatch : Kit.ECode := ⟨"WV1003"⟩
def ecFrameMismatch : Kit.ECode := ⟨"WV1004"⟩
def ecSelectOperands : Kit.ECode := ⟨"WV1005"⟩
def ecUnbalancedReturn : Kit.ECode := ⟨"WV1006"⟩
def ecUnbalancedEnd : Kit.ECode := ⟨"WV1007"⟩
def ecUnboundLocal : Kit.ECode := ⟨"WV1008"⟩
def ecUnboundFunc : Kit.ECode := ⟨"WV1009"⟩
def ecTypeIndexRange : Kit.ECode := ⟨"WV1010"⟩
def ecUnboundTable : Kit.ECode := ⟨"WV1011"⟩
def ecIndirectTypeRange : Kit.ECode := ⟨"WV1012"⟩
def ecTableEntryRange : Kit.ECode := ⟨"WV1013"⟩

end ValidateError

/-- THE diagnostic envelope: every refusal renders into the ONE Diag —
    the E-code from the WV family, the got/valid data from the error's
    payload, the valid-space enumeration where the world is closed
    (the expected operand types are the pops the ONE op table's
    projections feed the payload). The unbound/positional failures
    with no enumerable valid space build the literal (empty
    `valid`/`suggest` is then honest, not a skipped discipline). -/
def ValidateError.toDiag : ValidateError → Kit.Diag
  | .operandMismatch exp got =>
      Kit.Diag.closedWorld ecOperandMismatch
        "operand type mismatch: the stack does not provide the instruction's pops"
        .error (renderValTypes got)
        [s!"a stack of the form {renderValTypes exp} ++ ts"]
  | .underflow need =>
      Kit.Diag.closedWorld ecUnderflow
        s!"stack underflow: {need} operand(s) needed"
        .error (renderValTypes [])
        [s!"a stack of at least {need} operand(s)"]
  | .localTypeMismatch n exp got =>
      Kit.Diag.closedWorld ecLocalTypeMismatch
        s!"local {n} expects {renderValType exp}"
        .error (renderValType got) [renderValType exp]
  | .frameMismatch exp got =>
      Kit.Diag.closedWorld ecFrameMismatch
        "frame stack mismatch: the frame's exit stack does not match its entry stack"
        .error (renderValTypes got) [renderValTypes exp]
  | .selectOperands got =>
      Kit.Diag.closedWorld ecSelectOperands
        "select needs i32 :: t :: t :: ts with t = i32 or t = i64"
        .error (renderValTypes got)
        ["i32, t, t, … with t = i32", "i32, t, t, … with t = i64"]
  | .unbalancedReturn exp got =>
      Kit.Diag.closedWorld ecUnbalancedReturn
        "stack unbalanced at return"
        .error (renderValTypes got) [renderValTypes exp]
  | .unbalancedEnd exp got =>
      Kit.Diag.closedWorld ecUnbalancedEnd
        "stack unbalanced: the body's final stack does not match the results"
        .error (renderValTypes got) [renderValTypes exp]
  | .unboundLocal n =>
      { code := ecUnboundLocal, message := s!"unbound local {n}"
        , got := some s!"local index {n}" }
  | .unboundFunc n =>
      { code := ecUnboundFunc, message := s!"unbound function {n}"
        , got := some s!"function index {n}" }
  | .typeIndexRange fn tyIdx =>
      { code := ecTypeIndexRange
        , message := s!"function {fn}: type index {tyIdx} out of range"
        , got := some s!"type index {tyIdx}" }
  | .unboundTable =>
      { code := ecUnboundTable
        , message := "call_indirect over an absent table: the module declares no \
          table section (the indirect-call lane needs table 0)"
        , got := some "no table" }
  | .indirectTypeRange tyIdx =>
      { code := ecIndirectTypeRange
        , message := s!"call_indirect: type index {tyIdx} out of range"
        , got := some s!"type index {tyIdx}" }
  | .tableEntryRange fn =>
      { code := ecTableEntryRange
        , message := s!"table entry names function {fn} — past the function section"
        , got := some s!"function index {fn}" }
  | .atFunc i e =>
      let d := e.toDiag
      { d with context := Kit.Label.at s!"function {i}" :: d.context }

/-- The one-line rendering (the envelope's `.toString`). -/
def ValidateError.render (e : ValidateError) : String :=
  Kit.Diag.toString e.toDiag

/-! ## The checker -/

/-- The typing context: locals (params ++ declared, index-keyed), the
    call environment, the TYPE section's lookup (the indirect-call
    lane's `callindirect` type-index check — the ONE table discipline's
    static face), and the enclosing function's results REVERSED
    (head-top stacks make `resRev` the return's expected stack). -/
structure Ctx where
  lty : Nat → Option ValType
  fenv : Nat → Option FuncType
  tenv : Nat → Option FuncType
  resRev : List ValType

/-- The frame forms — the structured sub-body instructions. -/
def FrameForm : Instr → Prop
  | .block _ | .loop _ | .if_ _ _ => True
  | _ => False

/-- The snd-projection's two reduction facts (rfl — stated once so no
    consumer re-derives `Except.map`'s equations). -/
theorem map_snd_ok_eq (r : Bool × List ValType) :
    ((fun r => r.2) <$> (Except.ok r : Except ValidateError (Bool × List ValType)))
      = .ok r.2 := rfl

theorem map_snd_error (e : ValidateError) :
    ((fun r => r.2) <$> (Except.error e : Except ValidateError (Bool × List ValType)))
      = .error e := rfl

mutual
/-- The per-instruction step: a STOP FLAG + the stack. Flag `true` =
    control transferred (`br`/`unreach`/`ret`) — the tail is statically
    dead. Explicit arms, no wildcard (design doc R7). -/
def stepFlag (c : Ctx) :
    Instr → List ValType → Except ValidateError (Bool × List ValType)
  | .i32const _, s => .ok (false, .i32 :: s)
  | .i64const _, s => .ok (false, .i64 :: s)
  | .localget n, s =>
      match c.lty n with
      | some t => .ok (false, t :: s)
      | none => .error (.unboundLocal n)
  | .localset n, s =>
      match c.lty n with
      | none => .error (.unboundLocal n)
      | some u =>
        match s with
        | t :: ts => if t = u then .ok (false, ts) else .error (.localTypeMismatch n u t)
        | [] => .error (.underflow 1)
  | .localtee n, s =>
      match c.lty n with
      | none => .error (.unboundLocal n)
      | some u =>
        match s with
        | t :: ts => if t = u then .ok (false, t :: ts) else .error (.localTypeMismatch n u t)
        | [] => .error (.underflow 1)
  | .call fn, s =>
      match c.fenv fn with
      | none => .error (.unboundFunc fn)
      | some ft =>
        match popPush ft.params.reverse ft.results.reverse s with
        | some s' => .ok (false, s')
        | none => .error (.operandMismatch ft.params.reverse s)
  | .callindirect ty, s =>
      -- THE INDIRECT-CALL row (the static face): the type index must
      -- resolve (the validator's indirectTypeRange refusal), the
      -- callee INDEX is the i32 on TOP (popped first), then the args
      -- against the declared type — the runtime's table lookup + type
      -- check are Exec's (the trap teeth there).
      match c.tenv ty with
      | none => .error (.indirectTypeRange ty)
      | some ft =>
        match s with
        | .i32 :: ts =>
          match popPush ft.params.reverse ft.results.reverse ts with
          | some s' => .ok (false, s')
          | none => .error (.operandMismatch ft.params.reverse ts)
        | _ => .error (.operandMismatch [.i32] s)
  | .mem op _ _, s =>
      match popPush (memPop op) (memPush op) s with
      | some s' => .ok (false, s')
      | none => .error (.operandMismatch (memPop op) s)
  | .op o, s =>
      match popPush (opPop o) (opPush o) s with
      | some s' => .ok (false, s')
      | none => .error (.operandMismatch (opPop o) s)
  | .brif _, s =>
      match s with
      | .i32 :: ts => .ok (false, ts)
      | _ => .error (.operandMismatch [.i32] s)
  | .block b, s =>
      match b.foldl (checkStep c) (.ok (false, s)) with
      | .error e => .error e
      | .ok (_, mid) => if mid = s then .ok (false, s) else .error (.frameMismatch s mid)
  | .loop b, s =>
      match b.foldl (checkStep c) (.ok (false, s)) with
      | .error e => .error e
      | .ok (_, mid) => if mid = s then .ok (false, s) else .error (.frameMismatch s mid)
  | .if_ t e, s =>
      match s with
      | .i32 :: ts =>
        match (t : List Instr).foldl (checkStep c) (.ok (false, ts)) with
        | .error err => .error err
        | .ok (_, mid1) =>
          if mid1 = ts then
            match e.foldl (checkStep c) (.ok (false, ts)) with
            | .error err => .error err
            | .ok (_, mid2) =>
              if mid2 = ts then .ok (false, ts) else .error (.frameMismatch ts mid2)
          else .error (.frameMismatch ts mid1)
      | _ => .error (.operandMismatch [.i32] s)
  | .drop, s =>
      match s with
      | _ :: ts => .ok (false, ts)
      | [] => .error (.underflow 1)
  | .select, s =>
      match s with
      | .i32 :: .i32 :: .i32 :: ts => .ok (false, .i32 :: ts)
      | .i32 :: .i64 :: .i64 :: ts => .ok (false, .i64 :: ts)
      | _ => .error (.selectOperands s)
  | .br _, s => .ok (true, s)
  | .unreach, s => .ok (true, s)
  | .ret, s => if s = c.resRev then .ok (true, s) else .error (.unbalancedReturn c.resRev s)

/-- One fold step: an error poisons; a stopped state copies through
    (the tail is statically dead); a live state steps. -/
def checkStep (c : Ctx) :
    Except ValidateError (Bool × List ValType) → Instr → Except ValidateError (Bool × List ValType)
  | .error e, _ => .error e
  | .ok (true, s), _ => .ok (true, s)
  | .ok (false, s), i => stepFlag c i s
end

/-- The body checker: the instruction list folded to a stop-flag +
    stack verdict (a PLAIN def outside the mutual block — reducible,
    so the bridge proofs reason definitionally). -/
def checkFlow (c : Ctx) (s : List ValType) (body : List Instr) :
    Except ValidateError (Bool × List ValType) :=
  body.foldl (checkStep c) (.ok (false, s))

/-- The body's stack verdict (forgetting the stop flag). -/
def checkBody (c : Ctx) (s : List ValType) (body : List Instr) :
    Except ValidateError (List ValType) :=
  (fun r => r.2) <$> checkFlow c s body

/-- The copy laws: a stopped or poisoned state survives the rest of
    the fold (that IS what stop/poison mean). -/
theorem foldl_stopped (c : Ctx) : ∀ (body : List Instr) (s : List ValType),
    body.foldl (checkStep c) (.ok (true, s)) = .ok (true, s) := by
  intro body
  induction body with
  | nil => intro s; rfl
  | cons i is ih =>
    intro s
    simp only [List.foldl_cons, checkStep]
    exact ih s

theorem foldl_poisoned (c : Ctx) (e : ValidateError) : ∀ (body : List Instr),
    body.foldl (checkStep c) (.error e) = .error e := by
  intro body
  induction body with
  | nil => rfl
  | cons i is ih => simp only [List.foldl_cons, checkStep]; exact ih

/-- `checkBody`'s value pins the fold's result (the inversion used by
    both bridge directions). -/
theorem fold_of_checkBody (c : Ctx) (s : List ValType) (body : List Instr)
    (s' : List ValType) (h : checkBody c s body = .ok s') :
    ∃ r, checkFlow c s body = .ok r ∧ r.2 = s' := by
  simp only [checkBody] at h
  cases hf : checkFlow c s body with
  | error e => rw [hf, map_snd_error] at h; simp at h
  | ok r =>
    rw [hf, map_snd_ok_eq] at h
    simp at h
    exact ⟨r, rfl, h⟩

theorem checkBody_of_fold (c : Ctx) (s : List ValType) (body : List Instr)
    (r : Bool × List ValType) (s' : List ValType)
    (h : checkFlow c s body = .ok r) (hr : r.2 = s') :
    checkBody c s body = .ok s' := by
  simp only [checkBody]
  rw [h, map_snd_ok_eq, hr]

/-- ONE fold-step extraction (06 §7's family rule: the flat soundness
    arms all need the same fact — a live fold through `i :: is` forces
    the head step to compute — so it is stated and proved ONCE). A
    successful fold means `stepFlag c i s` either stopped (flag `true`,
    only `br`/`unreach`/`ret` can do that) or continued live from the
    stepped stack. -/
theorem foldl_cons_step (c : Ctx) (s : List ValType) (i : Instr) (is : List Instr)
    (r : Bool × List ValType)
    (h : List.foldl (checkStep c) (Except.ok (false, s)) (i :: is) = .ok r) :
    (∃ mid, stepFlag c i s = .ok (true, mid)) ∨
    (∃ mid, stepFlag c i s = .ok (false, mid) ∧
      List.foldl (checkStep c) (Except.ok (false, mid)) is = .ok r) := by
  simp only [List.foldl_cons, checkStep] at h
  cases hs : stepFlag c i s with
  | error e =>
    rw [hs] at h
    rw [foldl_poisoned] at h
    simp at h
  | ok f =>
    obtain ⟨flag, mid⟩ := f
    cases flag with
    | false => rw [hs] at h; exact Or.inr ⟨mid, rfl, h⟩
    | true => exact Or.inl ⟨mid, rfl⟩

/-! ## The relation (pattern #1's spec) -/

/-- The one-instruction typing step, as the SPEC relation — FLAT
    instructions only (the transfer and frame rules are `BodyTy`'s own
    ctors below). -/
inductive StepTy : Ctx → List ValType → Instr → List ValType → Prop where
  | i32const (c : Ctx) (s : List ValType) (n : Nat) :
      StepTy c s (.i32const n) (.i32 :: s)
  | i64const (c : Ctx) (s : List ValType) (n : Nat) :
      StepTy c s (.i64const n) (.i64 :: s)
  | localget (c : Ctx) (s : List ValType) (n : Nat) (t : ValType) :
      c.lty n = some t → StepTy c s (.localget n) (t :: s)
  | localset (c : Ctx) (ts : List ValType) (t : ValType) (n : Nat) :
      c.lty n = some t → StepTy c (t :: ts) (.localset n) ts
  | localtee (c : Ctx) (ts : List ValType) (t : ValType) (n : Nat) :
      c.lty n = some t → StepTy c (t :: ts) (.localtee n) (t :: ts)
  | op (c : Ctx) (ts : List ValType) (o : Op) :
      StepTy c (opPop o ++ ts) (.op o) (opPush o ++ ts)
  | callindirect (c : Ctx) (ts : List ValType) (ty : Nat) (ft : FuncType) :
      c.tenv ty = some ft →
      StepTy c (.i32 :: (ft.params.reverse ++ ts)) (.callindirect ty)
        (ft.results.reverse ++ ts)
  | mem (c : Ctx) (ts : List ValType) (m : MemOp) (off : Nat) (al : Option Nat) :
      StepTy c (memPop m ++ ts) (.mem m off al) (memPush m ++ ts)
  | call (c : Ctx) (ts : List ValType) (fn : Nat) (ft : FuncType) :
      c.fenv fn = some ft →
      StepTy c (ft.params.reverse ++ ts) (.call fn) (ft.results.reverse ++ ts)
  | drop (c : Ctx) (ts : List ValType) (t : ValType) :
      StepTy c (t :: ts) .drop ts
  | select (c : Ctx) (ts : List ValType) (t t' : ValType) :
      t = t' → ((t = .i32 ∨ t = .i64)) →
      StepTy c (.i32 :: t :: t' :: ts) .select (t :: ts)
  | brif (c : Ctx) (ts : List ValType) (d : Nat) :
      StepTy c (.i32 :: ts) (.brif d) ts

/-- The body-typing relation: the honest semantics the checker is
    measured against (pattern #1's spec — it never lies to fit the
    checker). Transfer forms own their tails (the tail is dead). -/
inductive BodyTy : Ctx → List ValType → List Instr → List ValType → Prop where
  | nil (c : Ctx) (s : List ValType) : BodyTy c s [] s
  | cons (c : Ctx) (s : List ValType) (i : Instr) (is : List Instr)
      (mid s' : List ValType) :
      StepTy c s i mid → BodyTy c mid is s' → BodyTy c s (i :: is) s'
  | br (c : Ctx) (s : List ValType) (is : List Instr) (d : Nat) :
      BodyTy c s (.br d :: is) s
  | unreach (c : Ctx) (s : List ValType) (is : List Instr) :
      BodyTy c s (.unreach :: is) s
  | ret (c : Ctx) (s : List ValType) (is : List Instr) :
      s = c.resRev → BodyTy c s (.ret :: is) s
  | block (c : Ctx) (s : List ValType) (b is : List Instr) (s' : List ValType) :
      BodyTy c s b s → BodyTy c s is s' → BodyTy c s (.block b :: is) s'
  | loop (c : Ctx) (s : List ValType) (b is : List Instr) (s' : List ValType) :
      BodyTy c s b s → BodyTy c s is s' → BodyTy c s (.loop b :: is) s'
  | if_ (c : Ctx) (ts : List ValType) (t e is : List Instr) (s' : List ValType) :
      BodyTy c ts t ts → BodyTy c ts e ts → BodyTy c ts is s' →
      BodyTy c (.i32 :: ts) (.if_ t e :: is) s'

/-! ## The bridge (both directions — proved, never defaulted) -/

/-! ### The ok-shape inversions (06 §7's family rule: each refusal
    lattice — `brif`'s 6-way, `select`'s closed 6×6, `localset`/
    `localtee`'s bind-or-refuse — is exploded ONCE here and cited per
    arm below; the ok-equation pins the flag to `false`, so these also
    refute the stopped cases for free.) -/

/-- `brif` computes live only on an `i32` head. -/
theorem stepFlag_brif_shape (c : Ctx) (d : Nat) (s : List ValType) (b : Bool)
    (mid : List ValType) (h : stepFlag c (.brif d) s = .ok (b, mid)) :
    b = false ∧ ∃ ts, s = .i32 :: ts ∧ mid = ts := by
  cases s with
  | nil => simp [stepFlag] at h
  | cons t ts =>
    cases t with
    | i32 =>
      simp only [stepFlag] at h
      rw [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, ts, rfl, h.2.symm⟩
    | _ => simp [stepFlag] at h

/-- `select` computes live only on `.i32 :: t :: t :: ts` with
    `t ∈ {i32, i64}` (its two live table rows). -/
theorem stepFlag_select_shape (c : Ctx) (s : List ValType) (b : Bool)
    (mid : List ValType) (h : stepFlag c .select s = .ok (b, mid)) :
    b = false ∧
    ∃ (ts : List ValType) (t : ValType),
      s = .i32 :: t :: t :: ts ∧ mid = t :: ts ∧ (t = .i32 ∨ t = .i64) := by
  cases s with
  | nil => simp [stepFlag] at h
  | cons c0 s1 =>
    cases s1 with
    | nil => simp [stepFlag] at h
    | cons c1 s2 =>
      cases s2 with
      | nil => simp [stepFlag] at h
      | cons v1 vs =>
        cases c0 with
        | i32 =>
          cases c1 with
          | i32 =>
            cases v1 with
            | i32 =>
              simp only [stepFlag] at h
              rw [Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨h.1.symm, vs, .i32, rfl, h.2.symm, Or.inl rfl⟩
            | _ => simp [stepFlag] at h
          | i64 =>
            cases v1 with
            | i64 =>
              simp only [stepFlag] at h
              rw [Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨h.1.symm, vs, .i64, rfl, h.2.symm, Or.inr rfl⟩
            | _ => simp [stepFlag] at h
          | _ => simp [stepFlag] at h
        | _ => simp [stepFlag] at h

/-- `localset n` computes live only on `t :: ts` with `c.lty n = some t`. -/
theorem stepFlag_localset_shape (c : Ctx) (n : Nat) (s : List ValType) (b : Bool)
    (mid : List ValType) (h : stepFlag c (.localset n) s = .ok (b, mid)) :
    ∃ ts t, s = t :: ts ∧ c.lty n = some t ∧ mid = ts ∧ b = false := by
  cases hln : c.lty n with
  | none => simp [hln, stepFlag] at h
  | some u =>
    cases s with
    | nil => simp [hln, stepFlag] at h
    | cons t ts =>
      simp only [hln, stepFlag] at h
      split at h
      · next htu =>
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          refine ⟨ts, t, rfl, ?_, h.2.symm, h.1.symm⟩
          rw [htu]
      · simp at h

/-- `localtee n` computes live only on `t :: ts` with `c.lty n = some t`
    (same refusal lattice as `localset`, kept as its own row). -/
theorem stepFlag_localtee_shape (c : Ctx) (n : Nat) (s : List ValType) (b : Bool)
    (mid : List ValType) (h : stepFlag c (.localtee n) s = .ok (b, mid)) :
    ∃ ts t, s = t :: ts ∧ c.lty n = some t ∧ mid = t :: ts ∧ b = false := by
  cases hln : c.lty n with
  | none => simp [hln, stepFlag] at h
  | some u =>
    cases s with
    | nil => simp [hln, stepFlag] at h
    | cons t ts =>
      simp only [hln, stepFlag] at h
      split at h
      · next htu =>
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          refine ⟨ts, t, rfl, ?_, h.2.symm, h.1.symm⟩
          rw [htu]
      · simp at h

/-- `callindirect ty` computes live only on `.i32 :: (ft.params.reverse ++ ts)`
    with `c.tenv ty = some ft` (the indirect-call row: the callee INDEX
    pops first, then the declared type's params). -/
theorem stepFlag_callindirect_shape (c : Ctx) (ty : Nat) (s : List ValType) (b : Bool)
    (mid : List ValType) (h : stepFlag c (.callindirect ty) s = .ok (b, mid)) :
    b = false ∧
    ∃ (ft : FuncType) (ts : List ValType),
      c.tenv ty = some ft ∧ s = .i32 :: (ft.params.reverse ++ ts)
        ∧ mid = ft.results.reverse ++ ts := by
  cases hten : c.tenv ty with
  | none => simp [hten, stepFlag] at h
  | some ft =>
    cases s with
    | nil => simp [hten, stepFlag] at h
    | cons t ts =>
      simp only [hten, stepFlag] at h
      cases t with
      | i32 =>
          simp only [stepFlag] at h
          split at h
          · next hp =>
              rw [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨ts2, hs1, hs2⟩ := popPush_some _ _ _ _ hp
              subst hs1
              exact ⟨h.1.symm, ft, ts2, rfl, rfl, h.2.symm.trans hs2⟩
          · simp at h
      | _ => simp [stepFlag] at h

/-- The pop/push families' ok-shape (`op`/`mem`/`call` ride the ONE
    operand-shape engine, so ONE inversion covers them): a live step
    forces the pop/push to fire exactly on `pop ++ ts`. -/
theorem stepFlag_popPush_shape (c : Ctx) (i : Instr) (pop push s mid : List ValType)
    (hstep : stepFlag c i s =
      match popPush pop push s with
      | some s' => Except.ok (false, s')
      | none => Except.error (ValidateError.operandMismatch pop s))
    (h : stepFlag c i s = .ok (false, mid)) :
    ∃ ts, s = pop ++ ts ∧ mid = push ++ ts := by
  rw [hstep] at h
  split at h
  · next x hp =>
      obtain ⟨ts, hs1, hs2⟩ := popPush_some _ _ _ _ hp
      subst hs1
      subst hs2
      rw [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨ts, rfl, h.2.symm⟩
  · simp at h

/-- The step's soundness: a LIVE completed step is related (the frame
    forms carry `FrameForm` instead — their rule is `BodyTy`-level). -/
theorem stepFlag_sound (c : Ctx) (i : Instr) (s mid : List ValType)
    (h : stepFlag c i s = .ok (false, mid)) : StepTy c s i mid ∨ FrameForm i := by
  cases i with
  | i32const n =>
      simp only [stepFlag] at h
      simp at h
      cases h
      exact Or.inl (StepTy.i32const c s n)
  | i64const n =>
      simp only [stepFlag] at h
      simp at h
      cases h
      exact Or.inl (StepTy.i64const c s n)
  | localget n =>
      simp only [stepFlag] at h
      cases hln : c.lty n with
      | none => simp [hln] at h
      | some t =>
        simp only [hln] at h
        simp at h
        cases h
        exact Or.inl (StepTy.localget c _ n t hln)
  | localset n =>
      obtain ⟨ts, t, hv, hln, hmid, -⟩ := stepFlag_localset_shape _ _ _ _ _ h
      subst hv
      subst hmid
      exact Or.inl (StepTy.localset c _ t n hln)
  | localtee n =>
      obtain ⟨ts, t, hv, hln, hmid, -⟩ := stepFlag_localtee_shape _ _ _ _ _ h
      subst hv
      subst hmid
      exact Or.inl (StepTy.localtee c _ t n hln)
  | call fn =>
      cases hf : c.fenv fn with
      | none => simp [hf, stepFlag] at h
      | some ft =>
        obtain ⟨ts, hs, hmid⟩ := stepFlag_popPush_shape c _ ft.params.reverse
          ft.results.reverse s mid (by simp only [stepFlag, hf]) h
        subst hs
        subst hmid
        exact Or.inl (StepTy.call c ts fn ft hf)
  | callindirect ty =>
      obtain ⟨-, ft, ts, hten, hv, hmid⟩ :=
        stepFlag_callindirect_shape c ty s false mid h
      subst hv
      subst hmid
      exact Or.inl (StepTy.callindirect c ts ty ft hten)
  | mem m off al =>
      obtain ⟨ts, hs, hmid⟩ := stepFlag_popPush_shape c _ (memPop m) (memPush m) s mid
        (by simp only [stepFlag]) h
      subst hs
      subst hmid
      exact Or.inl (StepTy.mem c ts m off al)
  | op o =>
      obtain ⟨ts, hs, hmid⟩ := stepFlag_popPush_shape c _ (opPop o) (opPush o) s mid
        (by simp only [stepFlag]) h
      subst hs
      subst hmid
      exact Or.inl (StepTy.op c ts o)
  | brif d =>
      obtain ⟨-, ts, hv, hmid⟩ := stepFlag_brif_shape _ _ _ _ _ h
      subst hv
      subst hmid
      exact Or.inl (StepTy.brif c _ d)
  | drop =>
      cases s with
      | nil => simp [stepFlag] at h
      | cons t ts =>
        simp only [stepFlag] at h
        simp at h
        cases h
        exact Or.inl (StepTy.drop c _ t)
  | select =>
      obtain ⟨-, ts, t, hv, hmid, htor⟩ := stepFlag_select_shape _ _ _ _ h
      subst hv
      subst hmid
      exact Or.inl (StepTy.select c _ t t rfl htor)
  | block b => exact Or.inr trivial
  | loop b => exact Or.inr trivial
  | if_ t e => exact Or.inr trivial
  | br d => simp [stepFlag] at h
  | unreach => simp [stepFlag] at h
  | ret =>
      simp only [stepFlag] at h
      split at h <;> simp at h

/-- The flat-step soundness, specialized (the `FrameForm = False`
    resolution the flat cons-cases ride). -/
theorem stepFlag_flat_sound (c : Ctx) (i : Instr) (s mid : List ValType)
    (h : stepFlag c i s = .ok (false, mid)) (hf : FrameForm i = False) :
    StepTy c s i mid := by
  rcases stepFlag_sound c i s mid h with hst | hframe
  · exact hst
  · rw [hf] at hframe
    exact absurd hframe (by simp)

/-- The flat cons-tail, packaged once (06 §7: the isomorphic
    `BodyTy.cons` tails — size arithmetic + `checkBody_of_fold` + the
    induction hypothesis — are this lemma's call sites). -/
theorem consIh (c : Ctx) (k : Nat) (s : List ValType) (i : Instr) (is : List Instr)
    (mid : List ValType) (r : Bool × List ValType)
    (hk : lSize (i :: is) ≤ k + 1) (hst : StepTy c s i mid)
    (hfold : List.foldl (checkStep c) (Except.ok (false, mid)) is = .ok r)
    (ih : ∀ (s : List ValType) (body : List Instr) (s' : List ValType),
        lSize body ≤ k → checkBody c s body = .ok s' → BodyTy c s body s') :
    BodyTy c s (i :: is) r.2 :=
  BodyTy.cons c s i is mid r.2 hst
    (ih mid is r.2 (by
        have hp := iSize_pos i
        simp only [lSize_cons] at hk
        omega)
      (checkBody_of_fold c mid is r r.2 hfold rfl))

/-- The pop/push families (`op`/`mem`/`call` ride the ONE operand-shape
    engine, so they share ONE fold shape): a live fold forces the pop/
    push to fire on `pop ++ ts`. -/
theorem fold_popPush (c : Ctx) (s : List ValType) (i : Instr) (is : List Instr)
    (pop push : List ValType) (r : Bool × List ValType)
    (hstep : stepFlag c i s =
      match popPush pop push s with
      | some s' => Except.ok (false, s')
      | none => Except.error (ValidateError.operandMismatch pop s))
    (h : List.foldl (checkStep c) (Except.ok (false, s)) (i :: is) = .ok r) :
    ∃ ts, s = pop ++ ts ∧
      List.foldl (checkStep c) (Except.ok (false, push ++ ts)) is = .ok r := by
  rcases foldl_cons_step c s i is r h with ⟨mid, hst⟩ | ⟨mid, hst, hrest⟩
  · rw [hstep] at hst
    split at hst <;> simp at hst
  · obtain ⟨ts, hs, hmid⟩ := stepFlag_popPush_shape c i pop push s mid hstep hst
    subst hs
    subst hmid
    exact ⟨ts, rfl, hrest⟩

/-- The step's completeness: every related step computes, live. -/
theorem stepFlag_complete (c : Ctx) (s mid : List ValType) (i : Instr)
    (h : StepTy c s i mid) : stepFlag c i s = .ok (false, mid) := by
  cases h
  case select =>
    rename_i ts t t' heq hor
    cases t <;> cases t' <;> simp_all [stepFlag]
  all_goals simp_all [stepFlag, popPush_append]

/-- The drift-guard (why the table is ONE): the closed universe is
    decided — every op consumes exactly its pops and leaves exactly its
    pushes through the ONE engine, so a malformed row fails at compile
    time (the row's own wf pins are `OpTable.opRow_wf`/`memRow_wf`).
    Type content is pinned in WasmCoreTests' sig pins. -/
theorem opSig_covers : ∀ o : Op,
    stepFlag (Ctx.mk (fun _ => none) (fun _ => none) (fun _ => none) []) (.op o) (opPop o ++ [])
      = .ok (false, opPush o ++ []) :=
  fun o => stepFlag_complete _ _ _ _ (StepTy.op _ [] o)

/-- The mem-op drift-guard (same decide over the closed universe). -/
theorem memSig_covers : ∀ m : MemOp,
    stepFlag (Ctx.mk (fun _ => none) (fun _ => none) (fun _ => none) []) (.mem m 0 none) (memPop m ++ [])
      = .ok (false, memPush m ++ []) :=
  fun m => stepFlag_complete _ _ _ _ (StepTy.mem _ [] m 0 none)

theorem checkFlow_eq (c : Ctx) (s : List ValType) (body : List Instr) :
    checkFlow c s body = body.foldl (checkStep c) (.ok (false, s)) := rfl

/-- The frame-form steps: the sub-body's stack-verdict determines the
    step (the flag-agnostic frame rule — legacy's conservative rule: a
    stopped sub-body still ends the frame at the entry stack). -/
theorem stepFlag_block (c : Ctx) (b : List Instr) (s : List ValType)
    (h : checkBody c s b = .ok s) : stepFlag c (Instr.block b) s = .ok (false, s) := by
  obtain ⟨r0, hf, hs⟩ := fold_of_checkBody c s b s h
  simp only [stepFlag, ← checkFlow_eq c s b, hf, hs, if_pos trivial]

theorem stepFlag_loop (c : Ctx) (b : List Instr) (s : List ValType)
    (h : checkBody c s b = .ok s) : stepFlag c (Instr.loop b) s = .ok (false, s) := by
  obtain ⟨r0, hf, hs⟩ := fold_of_checkBody c s b s h
  simp only [stepFlag, ← checkFlow_eq c s b, hf, hs, if_pos trivial]

theorem stepFlag_if_ (c : Ctx) (t e : List Instr) (ts : List ValType)
    (h1 : checkBody c ts t = .ok ts) (h2 : checkBody c ts e = .ok ts) :
    stepFlag c (Instr.if_ t e) (.i32 :: ts) = .ok (false, ts) := by
  obtain ⟨r0, hf0, hs0⟩ := fold_of_checkBody c ts t ts h1
  obtain ⟨r1, hf1, hs1⟩ := fold_of_checkBody c ts e ts h2
  simp only [stepFlag, ← checkFlow_eq c ts t, hf0, hs0, 
    ← checkFlow_eq c ts e, hf1, hs1, if_pos trivial]

/-- The completeness tail, packaged once (06 §7: the succ-branch's
    cons/frame arms share the same fold packaging). -/
theorem completeCons (c : Ctx) (s : List ValType) (i : Instr) (is : List Instr)
    (mid : List ValType) (r : Bool × List ValType)
    (hstep : stepFlag c i s = .ok (false, mid))
    (hfold : List.foldl (checkStep c) (Except.ok (false, mid)) is = .ok r) :
    checkBody c s (i :: is) = .ok r.2 := by
  simp only [checkBody, checkFlow, List.foldl_cons, checkStep, hstep, hfold, map_snd_ok_eq]

/-- The stopped-transfer completeness tail (the tail is statically dead). -/
theorem completeStop (c : Ctx) (s : List ValType) (i : Instr) (is : List Instr)
    (hstep : stepFlag c i s = .ok (true, s)) :
    checkBody c s (i :: is) = .ok s := by
  simp only [checkBody, checkFlow, List.foldl_cons, checkStep, hstep, foldl_stopped,
    map_snd_ok_eq]

/-- COMPLETENESS: a related body always checks. (Strong induction on
    the size measure; the relation's ctor drives each case.) -/
theorem checkBody_complete (c : Ctx) :
    ∀ (k : Nat) (s : List ValType) (body : List Instr) (s' : List ValType),
    lSize body ≤ k → BodyTy c s body s' → checkBody c s body = .ok s' := by
  intro k
  induction k with
  | zero =>
    intro s body s' hk h
    cases h with
    | nil =>
      simp only [checkBody, checkFlow, List.foldl_nil, map_snd_ok_eq]
    | cons _ i is mid _ _ =>
      have hp := iSize_pos i
      simp only [lSize_cons] at hk
      omega
    | _ =>
      simp only [lSize_cons, iSize] at hk
      omega
  | succ k ih =>
    intro s body s' hk h
    cases h with
    | nil =>
      simp only [checkBody, checkFlow, List.foldl_nil, map_snd_ok_eq]
    | cons _ i is mid _ hst hbody =>
      have htail : lSize is ≤ k := by
        have hp := iSize_pos i
        simp only [lSize_cons] at hk; omega
      obtain ⟨r0, hfold, hsnd⟩ := fold_of_checkBody c mid is s' (ih mid is s' (by omega) hbody)
      cases hsnd
      exact completeCons c s i is mid r0 (stepFlag_complete c s mid i hst) hfold
    | br _ is d =>
      exact completeStop c s _ is (by simp only [stepFlag])
    | unreach _ is =>
      exact completeStop c s _ is (by simp only [stepFlag])
    | ret _ is heq =>
      exact completeStop c s _ is (by simp only [stepFlag, if_pos heq])
    | block _ b is _ hb hbody =>
      have hsizes : lSize b ≤ k ∧ lSize is ≤ k := by
        simp only [lSize_cons, iSize] at hk; omega
      obtain ⟨hb_size, his_size⟩ := hsizes
      obtain ⟨r1, hfold1, hsnd1⟩ := fold_of_checkBody c s is s' (ih s is s' his_size hbody)
      cases hsnd1
      exact completeCons c s (Instr.block b) is s r1
        (stepFlag_block c b s (ih s b s hb_size hb)) hfold1
    | loop _ b is _ hb hbody =>
      have hsizes : lSize b ≤ k ∧ lSize is ≤ k := by
        simp only [lSize_cons, iSize] at hk; omega
      obtain ⟨hb_size, his_size⟩ := hsizes
      obtain ⟨r1, hfold1, hsnd1⟩ := fold_of_checkBody c s is s' (ih s is s' his_size hbody)
      cases hsnd1
      exact completeCons c s (Instr.loop b) is s r1
        (stepFlag_loop c b s (ih s b s hb_size hb)) hfold1
    | if_ ts t e is _ hb1 hb2 hbody =>
      have hsizes : lSize t ≤ k ∧ lSize e ≤ k ∧ lSize is ≤ k := by
        simp only [lSize_cons, iSize] at hk; omega
      obtain ⟨ht_size, he_size, his_size⟩ := hsizes
      obtain ⟨r2, hfold2, hsnd2⟩ := fold_of_checkBody c ts is s' (ih ts is s' his_size hbody)
      cases hsnd2
      exact completeCons c (ValType.i32 :: ts) (Instr.if_ t e) is ts r2
        (stepFlag_if_ c t e ts (ih ts t ts ht_size hb1)
          (ih ts e ts he_size hb2)) hfold2
/-- SOUNDNESS: a checked body is related. (Strong induction on the
    size measure — the checker's own termination argument. The transfer
    and frame forms construct their own ctors; the flat forms ride
    `stepFlag_flat_sound`.) -/
theorem checkBody_sound (c : Ctx) :
    ∀ (k : Nat) (s : List ValType) (body : List Instr) (s' : List ValType),
    lSize body ≤ k → checkBody c s body = .ok s' → BodyTy c s body s' := by
  intro k
  induction k with
  | zero =>
    intro s body s' hk h
    match body with
    | [] =>
      rw [checkBody, checkFlow, List.foldl_nil, map_snd_ok_eq] at h
      cases h
      exact BodyTy.nil c s
    | i :: is =>
      have hp := iSize_pos i
      simp only [lSize_cons] at hk
      exact absurd hk (by omega)
  | succ k ih =>
    intro s body s' hk h
    obtain ⟨r0, hfold0, hsnd0⟩ := fold_of_checkBody c s body s' h
    cases hsnd0
    match body with
    | [] =>
      simp only [checkFlow, List.foldl_nil] at hfold0
      simp at hfold0
      cases hfold0
      exact BodyTy.nil c s
    | i :: is =>
      have htail : lSize is ≤ k := by
        have hp := iSize_pos i
        simp only [lSize_cons] at hk
        omega
      simp only [checkFlow, List.foldl_cons] at hfold0
      cases i with
      | br d =>
        simp only [checkStep, stepFlag, foldl_stopped] at hfold0
        simp at hfold0
        cases hfold0
        exact BodyTy.br c s is d
      | unreach =>
        simp only [checkStep, stepFlag, foldl_stopped] at hfold0
        simp at hfold0
        cases hfold0
        exact BodyTy.unreach c s is
      | ret =>
        simp only [checkStep, stepFlag] at hfold0
        split at hfold0
        · next hres =>
            rw [foldl_stopped] at hfold0
            simp at hfold0
            cases hfold0
            exact BodyTy.ret c s is hres
        · next =>
            rw [foldl_poisoned] at hfold0
            simp at hfold0
      | block b =>
        have hsizes : lSize b ≤ k ∧ lSize is ≤ k := by
          simp only [lSize_cons, iSize] at hk; omega
        obtain ⟨hb_size, his_size⟩ := hsizes
        simp only [checkStep, stepFlag] at hfold0
        cases hbf : b.foldl (checkStep c) (.ok (false, s)) with
        | error e =>
          simp only [hbf, foldl_poisoned] at hfold0
          simp at hfold0
        | ok rB =>
          simp only [hbf] at hfold0
          split at hfold0
          · next hms =>
              have hbb : checkBody c s b = .ok s := by
                rw [checkBody, checkFlow, hbf, map_snd_ok_eq, hms]
              exact BodyTy.block c s b is r0.2
                (ih s b s hb_size hbb)
                (ih s is r0.2 his_size (checkBody_of_fold c s is r0 r0.2 hfold0 rfl))
          · rw [foldl_poisoned] at hfold0; simp at hfold0
      | loop b =>
        have hsizes : lSize b ≤ k ∧ lSize is ≤ k := by
          simp only [lSize_cons, iSize] at hk; omega
        obtain ⟨hb_size, his_size⟩ := hsizes
        simp only [checkStep, stepFlag] at hfold0
        cases hbf : b.foldl (checkStep c) (.ok (false, s)) with
        | error e =>
          simp only [hbf, foldl_poisoned] at hfold0
          simp at hfold0
        | ok rB =>
          simp only [hbf] at hfold0
          split at hfold0
          · next hms =>
              have hbb : checkBody c s b = .ok s := by
                rw [checkBody, checkFlow, hbf, map_snd_ok_eq, hms]
              exact BodyTy.loop c s b is r0.2
                (ih s b s hb_size hbb)
                (ih s is r0.2 his_size (checkBody_of_fold c s is r0 r0.2 hfold0 rfl))
          · rw [foldl_poisoned] at hfold0; simp at hfold0
      | if_ t e =>
        have hsizes : lSize t ≤ k ∧ lSize e ≤ k ∧ lSize is ≤ k := by
          simp only [lSize_cons, iSize] at hk; omega
        obtain ⟨ht_size, he_size, his_size⟩ := hsizes
        cases s with
        | nil => simp [checkStep, stepFlag, foldl_poisoned] at hfold0
        | cons v0 vs =>
          cases v0 with
          | i32 =>
            simp only [checkStep, stepFlag] at hfold0
            cases hbf : t.foldl (checkStep c) (.ok (false, vs)) with
            | error x =>
              simp only [hbf, foldl_poisoned] at hfold0
              simp at hfold0
            | ok rB =>
              simp only [hbf] at hfold0
              split at hfold0
              · next hm1 =>
                  cases hbf2 : e.foldl (checkStep c) (.ok (false, vs)) with
                  | error x =>
                    simp only [hbf2, foldl_poisoned] at hfold0
                    simp at hfold0
                  | ok rB2 =>
                    simp only [hbf2] at hfold0
                    split at hfold0
                    · next hm2 =>
                        have hbb1 : checkBody c vs t = .ok vs := by
                          rw [checkBody, checkFlow, hbf, map_snd_ok_eq, hm1]
                        have hbb2 : checkBody c vs e = .ok vs := by
                          rw [checkBody, checkFlow, hbf2, map_snd_ok_eq, hm2]
                        exact BodyTy.if_ c vs t e is r0.2
                          (ih vs t vs ht_size hbb1)
                          (ih vs e vs he_size hbb2)
                          (ih vs is r0.2 his_size
                            (checkBody_of_fold c vs is r0 r0.2 hfold0 rfl))
                    · rw [foldl_poisoned] at hfold0; simp at hfold0
              · rw [foldl_poisoned] at hfold0; simp at hfold0
          | i64 => simp [checkStep, stepFlag, foldl_poisoned] at hfold0
          | f32 => simp [checkStep, stepFlag, foldl_poisoned] at hfold0
          | f64 => simp [checkStep, stepFlag, foldl_poisoned] at hfold0
          | funcref => simp [checkStep, stepFlag, foldl_poisoned] at hfold0
          | externref => simp [checkStep, stepFlag, foldl_poisoned] at hfold0
      | i32const n =>
        simp only [checkStep, stepFlag] at hfold0
        exact consIh c k s _ is _ r0 hk (StepTy.i32const c s n) hfold0 ih
      | i64const n =>
        simp only [checkStep, stepFlag] at hfold0
        exact consIh c k s _ is _ r0 hk (StepTy.i64const c s n) hfold0 ih
      | localget n =>
        simp only [checkStep, stepFlag] at hfold0
        cases hln : c.lty n with
        | none =>
          simp only [hln, foldl_poisoned] at hfold0
          simp at hfold0
        | some t =>
          simp only [hln] at hfold0
          exact consIh c k _ _ is _ r0 hk
            (stepFlag_flat_sound c _ s _ (by simp only [stepFlag, hln])
              (by simp [FrameForm]))
            hfold0 ih
      | localset n =>
        rcases foldl_cons_step _ _ _ _ _ hfold0 with ⟨mid, hst⟩ | ⟨mid, hst, hrest⟩
        · obtain ⟨-, -, -, -, -, hb⟩ := stepFlag_localset_shape _ _ _ _ _ hst
          simp at hb
        · obtain ⟨ts, t, hv, hln, hmid, -⟩ := stepFlag_localset_shape _ _ _ _ _ hst
          subst hv
          subst hmid
          exact consIh c k _ _ is _ r0 hk (StepTy.localset c _ t n hln) hrest ih
      | localtee n =>
        rcases foldl_cons_step _ _ _ _ _ hfold0 with ⟨mid, hst⟩ | ⟨mid, hst, hrest⟩
        · obtain ⟨-, -, -, -, -, hb⟩ := stepFlag_localtee_shape _ _ _ _ _ hst
          simp at hb
        · obtain ⟨ts, t, hv, hln, hmid, -⟩ := stepFlag_localtee_shape _ _ _ _ _ hst
          subst hv
          subst hmid
          exact consIh c k _ _ is _ r0 hk (StepTy.localtee c _ t n hln) hrest ih
      | call fn =>
        cases hf : c.fenv fn with
        | none =>
          simp [checkStep, stepFlag, hf, foldl_poisoned] at hfold0
        | some ft =>
          obtain ⟨ts, hs, hrest⟩ :=
            fold_popPush c s _ is ft.params.reverse ft.results.reverse r0
              (by simp only [stepFlag, hf]) hfold0
          subst hs
          exact consIh c k _ _ is _ r0 hk (StepTy.call c ts fn ft hf) hrest ih
      | callindirect ty =>
        cases hten : c.tenv ty with
        | none =>
          simp [checkStep, stepFlag, hten, foldl_poisoned] at hfold0
        | some ft =>
          rcases foldl_cons_step _ _ _ _ _ hfold0 with ⟨mid, hst⟩ | ⟨mid, hst, hrest⟩
          · -- the stopped face: `callindirect` never transfers (the
            -- shape lemma pins b = false)
            obtain ⟨hb, -, -, -, -, -⟩ := stepFlag_callindirect_shape _ ty _ _ _ hst
            simp at hb
          · obtain ⟨-, ft, ts, hten, hv, hmid⟩ :=
              stepFlag_callindirect_shape c ty s false mid hst
            subst hv
            subst hmid
            exact consIh c k _ _ is _ r0 hk (StepTy.callindirect c ts ty ft hten) hrest ih
      | mem m off al =>
        obtain ⟨ts, hs, hrest⟩ :=
          fold_popPush c s _ is (memPop m) (memPush m) r0 (by simp only [stepFlag]) hfold0
        subst hs
        exact consIh c k _ _ is _ r0 hk (StepTy.mem c ts m off al) hrest ih
      | op o =>
        obtain ⟨ts, hs, hrest⟩ :=
          fold_popPush c s _ is (opPop o) (opPush o) r0 (by simp only [stepFlag]) hfold0
        subst hs
        exact consIh c k _ _ is _ r0 hk (StepTy.op c ts o) hrest ih
      | brif d =>
        rcases foldl_cons_step _ _ _ _ _ hfold0 with ⟨mid, hst⟩ | ⟨mid, hst, hrest⟩
        · obtain ⟨hb, -, -, -⟩ := stepFlag_brif_shape _ _ _ _ _ hst
          simp at hb
        · obtain ⟨-, vs, hv, hmid⟩ := stepFlag_brif_shape _ _ _ _ _ hst
          subst hv
          subst hmid
          exact consIh c k _ _ is _ r0 hk (StepTy.brif c _ d) hrest ih
      | drop =>
        rcases foldl_cons_step _ _ _ _ _ hfold0 with ⟨mid, hst⟩ | ⟨mid, hst, hrest⟩
        · cases s <;> simp [stepFlag] at hst
        · cases s with
          | nil => simp [stepFlag] at hst
          | cons t ts =>
            simp only [stepFlag, Except.ok.injEq, Prod.mk.injEq] at hst
            have hmid : ts = mid := hst.2
            subst hmid
            exact consIh c k _ _ is _ r0 hk (StepTy.drop c _ t) hrest ih
      | select =>
        rcases foldl_cons_step _ _ _ _ _ hfold0 with ⟨mid, hst⟩ | ⟨mid, hst, hrest⟩
        · obtain ⟨hb, -, -, -, -⟩ := stepFlag_select_shape _ _ _ _ hst
          simp at hb
        · obtain ⟨-, vs, t, hv, hmid, htor⟩ := stepFlag_select_shape _ _ _ _ hst
          subst hv
          subst hmid
          exact consIh c k _ _ is _ r0 hk (StepTy.select c _ t t rfl htor) hrest ih

/-! ## The function judgment + the kit's CheckedProp -/

/-- The judgment's context for one function: params ++ locals keyed by
    index, the call environment, the type section's lookup (the
    indirect-call lane's static face), the reversed results. -/
def fnCtx (fenv tenv : Nat → Option FuncType) (ft : FuncType) (f : Func) : Ctx :=
  Ctx.mk (lty := fun n => (ft.params ++ f.locals)[n]?) (fenv := fenv)
    (tenv := tenv) (resRev := ft.results.reverse)

/-- The per-function judgment: the body's stack effect validates
    against its signature — starts empty, ends at the results (reversed
    for the head-top convention). -/
def checkFunc (fenv tenv : Nat → Option FuncType) (ft : FuncType) (f : Func) :
    Except ValidateError Unit :=
  match checkBody (fnCtx fenv tenv ft f) [] f.body with
  | .ok s' =>
      if s' = ft.results.reverse then .ok ()
      else .error (.unbalancedEnd ft.results.reverse s')
  | .error e => .error e

/-- The decidable shadow of `checkFunc` (the CheckedProp's check). -/
def funcCheck (fenv tenv : Nat → Option FuncType) (ft : FuncType) (f : Func) : Bool :=
  match checkFunc fenv tenv ft f with
  | .ok () => true
  | .error _ => false

theorem checkFunc_sound (fenv tenv : Nat → Option FuncType) (ft : FuncType) (f : Func)
    (h : checkFunc fenv tenv ft f = .ok ()) :
    BodyTy (fnCtx fenv tenv ft f) [] f.body ft.results.reverse := by
  rw [checkFunc] at h
  split at h
  · next s' hs' =>
      split at h
      · next hres =>
          rw [hres] at hs'
          exact checkBody_sound (fnCtx fenv tenv ft f) (lSize f.body) [] f.body
            ft.results.reverse (Nat.le_refl _) hs'
      · simp at h
  · simp at h

theorem checkFunc_complete (fenv tenv : Nat → Option FuncType) (ft : FuncType) (f : Func)
    (h : BodyTy (fnCtx fenv tenv ft f) [] f.body ft.results.reverse) :
    checkFunc fenv tenv ft f = .ok () := by
  rw [checkFunc, checkBody_complete (fnCtx fenv tenv ft f) (lSize f.body) [] f.body
    ft.results.reverse (Nat.le_refl _) h]
  simp

/-- Pattern #1 through the kit (Kit.CheckedProp): the relation
    (`BodyTy`) + the decidable checker (`funcCheck`) + the proved
    bridge. COMPLETE for this fragment — `.proved`, never defaulted. -/
def funcChecked (fenv tenv : Nat → Option FuncType) (ft : FuncType) : Kit.CheckedProp Func where
  P f := BodyTy (fnCtx fenv tenv ft f) [] f.body ft.results.reverse
  check f := funcCheck fenv tenv ft f
  sound f h := checkFunc_sound fenv tenv ft f (by
    unfold funcCheck at h
    cases hc : checkFunc fenv tenv ft f with
    | ok u => rfl
    | error e => rw [hc] at h; simp at h)
  complete? := .proved (fun f h => by
    show funcCheck fenv tenv ft f = true
    rw [funcCheck, checkFunc_complete fenv tenv ft f h])

/-! ## The module driver -/

/-- Fold the per-function judgment over the module (explicit index for
    the curated error). -/
def checkFuncs (m : Module) : Nat → List Func → Except ValidateError Unit
  | _, [] => .ok ()
  | i, f :: fs =>
      match m.typeAt f.tyIdx with
      | none => .error (.typeIndexRange i f.tyIdx)
      | some ft =>
        match checkFunc m.fenv m.typeAt ft f with
        | .ok () => checkFuncs m (i + 1) fs
        | .error e => .error (.atFunc i e)

/-! ### The table discipline (the indirect-call lane's module face) -/

mutual
/-- Does the instruction use the indirect call? (The frame forms walk
    their bodies — a `callindirect` inside a block demands the table
    just the same.) -/
def instrIndirect : Instr → Bool
  | .callindirect _ => true
  | .block b => bodyIndirect b
  | .loop b => bodyIndirect b
  | .if_ t e => bodyIndirect t || bodyIndirect e
  | _ => false

/-- The body walk (the mutual sibling). -/
def bodyIndirect : List Instr → Bool
  | [] => false
  | i :: is => instrIndirect i || bodyIndirect is
end

/-- The entries' bound walk (`checkEntries`' helper): every entry
    names a bound function (never a dangling dispatch target). -/
def entryBounded (m : Module) : List Nat → Except ValidateError Unit
  | [] => .ok ()
  | fn :: rest =>
      match m.funcs[fn]? with
      | none => .error (.tableEntryRange fn)
      | some _ => entryBounded m rest

/-- Every entry of every table names a bound function. -/
def checkEntries (m : Module) : List Table → Except ValidateError Unit
  | [] => .ok ()
  | t :: ts =>
      match entryBounded m t.init with
      | .ok () => checkEntries m ts
      | .error e => .error e

/-- THE TABLE-INDEX DISCIPLINE (the module driver's indirect-call
    face): a body that uses `callindirect` demands the table's
    PRESENCE (the wire's table index is the constant 0), and every
    table entry names a bound function. -/
def checkTables (m : Module) : Except ValidateError Unit :=
  if m.tables.isEmpty then
    if m.funcs.any (fun f => bodyIndirect f.body) then .error .unboundTable
    else .ok ()
  else
    checkEntries m m.tables

/-- The module-level driver: the table discipline first (the
    indirect-call lane's static face), then every function's body
    validates against its (resolved) signature, indices included. -/
def checkModule (m : Module) : Except ValidateError Unit :=
  match checkTables m with
  | .error e => .error e
  | .ok () => checkFuncs m 0 m.funcs

/-- The module check's PER-FUNCTION resolution: a module that checks
    resolves every function's type index and validates its body
    (the module-level type-safety theorem's premise face — the
    driver's lookup chain is the check's own fold). -/
theorem checkFuncs_some (m : Module) :
    ∀ (fs : List Func) (i j : Nat) (f : Func),
      checkFuncs m i fs = .ok () → fs[j]? = some f →
      ∃ ft, m.typeAt f.tyIdx = some ft ∧ checkFunc m.fenv m.typeAt ft f = .ok () := by
  intro fs
  induction fs with
  | nil => intro i j f _ h; simp at h
  | cons g gs ih =>
      intro i j f hchk hidx
      cases j with
      | zero =>
          simp at hidx
          subst hidx
          rw [checkFuncs] at hchk
          split at hchk
          · simp at hchk
          · next ft hft =>
              split at hchk
              · next hc => exact ⟨ft, hft, hc⟩
              · next hc => simp at hchk
      | succ j' =>
          rw [checkFuncs] at hchk
          split at hchk
          · simp at hchk
          · next ft hft =>
              split at hchk
              · next hc => exact ih (i + 1) j' f hchk hidx
              · next hc => simp at hchk

end WasmCore
