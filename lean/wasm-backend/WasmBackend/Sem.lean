/-!
# WasmBackend.Sem — the machine semantics of the WAT fragment (TALOS-LITE)

Owner: the TALOS-LITE lane. This file is the SEMANTIC MODEL of the typed
WAT AST (`WasmBackend.Wat.Instr`) for the fragment the backend actually
emits, and the foundation of the translation-correctness proof line
(notes/seam-contract.md #7). The deliverable theorem: TYPE SAFETY —
well-typed programs never raise the stack-underflow error
(`Sem.typeSafety`), plus the preservation half (the final stack is
statically what the checker said).

THE FRAGMENT vs REAL WEBASSEMBLY (the honesty ledger):

* COVERED: i32/i64 consts, locals (get/set — indices, not names; the
  name→index resolution is the emitter's job), i32.add, i64.add (the
  translation-correctness lane added it: it is the binop the backend's
  `binop?` emits for `UInt64.add` — the straight-line template's
  arithmetic), i32.eq (the cases lane added it: the branch comparison
  `goAlts` emits on the scalar scrutinee — the branch template's
  condition), drop,
  br/br_if with STRUCTURED targets (block/loop/if frames), if/else,
  unreachable, and a one-byte bounded store (`i32store8`) as the
  memory-ops representative.
* NOT MODELED (documented exclusions, not oversights): floats, SIMD,
  threads, tables/call_indirect (the funcref-table dispatch — the
  follow-up; DIRECT calls are modeled since the calls layer: the
  `The calls layer` section, v1 = CALLS as FUNCTION-COMPOSITION, no
  call-frames), integer div/rem (their `trap` is the only missing
  trap),
  multi-value blocks (frames are no-result: a frame body must END at
  the frame's entry type — `checkFrame`), memory beyond one byte per
  store, data segments, globals, static branch-DEPTH validation (a
  `br n` deeper than the label stack surfaces as a top-level return
  signal here; wasm's validator rejects it statically).
* CONSERVATIVE TYPING (sound, weaker than wasm's validator): `br`/
  `unreach` end the static check at the CURRENT stack type and skip
  the unreachable tail; a `br` executed with values pushed inside the
  frame since entry is therefore REJECTED statically where wasm would
  accept it (the dynamic semantics would still be safe — the branch
  restores the frame-entry stack).
* MODEL ARTIFACTS (not wasm behavior): execution is fuel-bounded
  (`outOfFuel` — every flat step and every frame entry, including each
  loop restart, consumes one unit). The memory is a total function
  `Nat → UInt8` with an explicit `memSize`; an out-of-bounds store is
  a RUNTIME trap, never corruption (`storeInBounds`).

THE LAYERED ERR: `Err.branch n ls` is NOT a wasm trap — it is the
structured branch signal of the classic layered semantics: `br n`
raises it carrying the branch-point LOCALS (wasm locals are
function-scoped: mutations inside a frame survive `br`); the frame
handler absorbs `0` (restore the frame-ENTRY stack, continue — or, for
`loop`, re-run the body: the only backward edge) and decrements `n+1`
to `n` for the parent. Uncaught at the function's top level = the
function-return signal, interpreted by the (unmodeled) call layer.

Relation to Wat.Instr: `Sem.Instr` mirrors the flat subset 1:1
(`i32const`↔`i32const`, `block`/`loop` drop the label — labels are
syntactic, `localget n` takes the resolved index where `Wat.localget`
takes the name, `i32store8`↔`Wat.MemOp.i32store8`). The
Sem.Instr ↔ Wat.Instr translation and the full correctness theorem
(emitted AST's exec ≡ the LCNF source's semantics) are the NEXT Talos
step; they compose with this file's theorems unchanged.

Ownership: wasm-backend. Imports NOTHING (Init only — no Lean, no
mathlib). WasmBackend.lean does not import this file (the migration
agent owns it); it is built via the lakefile glob and gated in
Tests/Axioms.lean additively.
-/

namespace WasmBackend.Sem

/-! ## Values, types -/

/-- A runtime value. The fragment is integer-only. -/
inductive Val where
  | i32 (n : UInt32)
  | i64 (n : UInt64)
  deriving BEq, DecidableEq

/-- The static types. -/
inductive Ty where
  | i32 | i64
  deriving DecidableEq, BEq

/-- The dynamic type of a value. -/
def tyOf : Val → Ty
  | .i32 _ => .i32
  | .i64 _ => .i64

/-! ## Machine state -/

/-- One machine state. Locals = a total `Nat → Val` map ("every local
    exists" is definitional); operand stack = a `List Val` (head = top);
    memory = a total byte function + its size. -/
structure State where
  /-- The locals (function-scoped). -/
  locals : Nat → Val
  /-- The operand stack, head = TOP. -/
  stack : List Val
  /-- The (linear) memory bytes. -/
  mem : Nat → UInt8
  /-- The memory size in bytes; valid addresses are `< memSize`. -/
  memSize : Nat

/-- The static view of an operand stack (head = top). Pattern-matching
    definition so the per-cons equation lemmas are simp-usable. -/
def stackTys : List Val → List Ty
  | [] => []
  | v :: vs => tyOf v :: stackTys vs

attribute [simp] tyOf stackTys

/-! ## Errors -/

/-- The error monad of the model. `underflow` conflates operand-stack
    underflow with operand-type mismatch (both are stack-SHAPE
    violations, both unreachable for well-typed programs — the theorem
    targets the name). -/
inductive Err where
  | /-- Stack-shape violation (underflow or operand-type mismatch). -/
  underflow
  | /-- `unreachable`, or an out-of-bounds store. -/
  trap
  | /-- Model artifact: the fuel (step/frame budget) ran out. -/
  outOfFuel
  | /-- The structured branch signal: `br n` targeting the (n+1)-th
       enclosing frame, carrying the branch-point locals. Handled by
       `execList`'s frame cases, not a wasm trap. -/
  branch (n : Nat) (ls : Nat → Val)
  | /-- `step` applied to a structural instruction. Unreachable in
       practice: `execList` dispatches `block`/`loop`/`if_` before ever
       calling `step`. Present only to keep `step` total. -/
  structural

/-! ## Instructions (the flat fragment) -/

/-- The modeled instruction set. Structural forms own their bodies;
    `br n` counts frames from the innermost enclosing `block`/`loop`/
    `if_` (n = 0 is the innermost). -/
inductive Instr where
  | i32const (n : UInt32)
  | i64const (n : UInt64)
  | localget (n : Nat)
  | localset (n : Nat)
  | i32add
  | i64add
  | i32eq
  | drop
  | br (n : Nat)
  | brif (n : Nat)
  | block (body : List Instr)
  | loop (body : List Instr)
  | if_ (thenI : List Instr) (elseI : List Instr)
  | unreach
  | i32store8
  deriving BEq

/-! ## step — the flat small-step semantics -/

/-- One flat instruction, one state transition. Structural instrs
    (`block`/`loop`/`if_`) are NOT stepped here — `execList` dispatches
    them; everything else is a pure stack/locals/memory update, with
    `br`/`brif`/`unreach` raising errors. -/
def step : State → Instr → Except Err State
  | s, .i32const n => .ok { s with stack := .i32 n :: s.stack }
  | s, .i64const n => .ok { s with stack := .i64 n :: s.stack }
  | s, .localget n => .ok { s with stack := s.locals n :: s.stack }
  | s, .localset n =>
      match s.stack with
      | v :: rest => .ok { s with locals := fun m => if m = n then v else s.locals m
                                 , stack := rest }
      | [] => .error .underflow
  | s, .i32add =>
      match s.stack with
      | .i32 a :: .i32 b :: rest => .ok { s with stack := .i32 (a + b) :: rest }
      | _ => .error .underflow
  | s, .i64add =>
      match s.stack with
      | .i64 a :: .i64 b :: rest => .ok { s with stack := .i64 (a + b) :: rest }
      | _ => .error .underflow
  | s, .i32eq =>
      -- the branch comparison (`goAlts`: `tag == cidx`): 1 if equal,
      -- else 0 — the convention `brif`/`if_` consume (nonzero = true).
      match s.stack with
      | .i32 a :: .i32 b :: rest =>
          .ok { s with stack := .i32 (if a == b then 1 else 0) :: rest }
      | _ => .error .underflow
  | s, .drop =>
      match s.stack with
      | _ :: rest => .ok { s with stack := rest }
      | [] => .error .underflow
  | s, .br n => .error (.branch n s.locals)
  | s, .brif n =>
      match s.stack with
      | .i32 b :: rest =>
          if b != 0 then .error (.branch n s.locals) else .ok { s with stack := rest }
      | _ => .error .underflow
  | _, .unreach => .error .trap
  | _, .block _ => .error .structural
  | _, .loop _ => .error .structural
  | _, .if_ _ _ => .error .structural
  | s, .i32store8 =>
      -- pops the value, then the address (wasm operand order)
      match s.stack with
      | .i32 v :: .i32 a :: rest =>
          if a.toNat < s.memSize
          then .ok { s with mem := fun i => if i = a.toNat then v.toUInt8 else s.mem i
                           , stack := rest }
          else .error .trap
      | _ => .error .underflow

/-! ## execList — the structured execution -/

/-- Run a body list. Every flat step and every frame entry consumes one
    fuel unit; a loop RESTART consumes one via re-entry at the same
    instruction (the only backward edge). Branch signals pass through
    unchanged; each frame case absorbs `branch 0` (restore the frame's
    ENTRY stack, locals from the branch point) and decrements
    `branch (n+1)` to `branch n` for the parent frame. -/
def execList : Nat → State → List Instr → Except Err State
  | 0, _, _ => .error .outOfFuel
  | _+1, s, [] => .ok s
  | fuel+1, s, .block body :: is =>
      match execList fuel s body with
      | .ok s' => execList fuel s' is
      | .error (.branch 0 ls) => execList fuel { s with locals := ls, stack := s.stack } is
      | .error (.branch (n+1) ls) => .error (.branch n ls)
      | .error e => .error e
  | fuel+1, s, .loop body :: is =>
      match execList fuel s body with
      | .ok s' => execList fuel s' is
      | .error (.branch 0 ls) =>
          -- restart: re-run the loop instruction itself from the frame-entry stack
          execList fuel { s with locals := ls, stack := s.stack } (.loop body :: is)
      | .error (.branch (n+1) ls) => .error (.branch n ls)
      | .error e => .error e
  | fuel+1, s, .if_ t e :: is =>
      match s.stack with
      | .i32 b :: rest =>
          let chosen := if b != 0 then t else e
          match execList fuel { s with stack := rest } chosen with
          | .ok s' => execList fuel s' is
          | .error (.branch 0 ls) =>
              execList fuel { s with locals := ls, stack := rest } is
          | .error (.branch (n+1) ls) => .error (.branch n ls)
          | .error ee => .error ee
      | _ => .error .underflow
  | fuel+1, s, i :: is =>
      match step s i with
      | .ok s' => execList fuel s' is
      | .error e => .error e

/-- The step/frame budget for the top-level entry point. -/
def defaultFuel : Nat := 1000

/-- Top-level execution. An uncaught branch here is the function-return
    signal (the call layer is unmodeled) — it surfaces as
    `.error (.branch n ls)`, never as `underflow` for well-typed code. -/
def exec (s : State) (body : List Instr) : Except Err State :=
  execList defaultFuel s body

/-! ## checkStack — the instruction-level stack typing -/

mutual
/-- The instruction-level stack typing: each instruction POPS its
    operands and PUSHES its results on a static type stack. `locals` is
    the locals' TYPE context (the task's 3-arg signature plus the
    necessary locals context). AFTER `br`/`unreach` the tail is
    UNREACHABLE — unchecked, statically ending at the CURRENT type
    (`base`); combined with `checkFrame`'s mid = entry rule this is
    sound (the branch/trap never reaches the tail) and conservative.
    Mutually recursive with `checkFrame` (a frame body is a subterm, so
    the structural recursion terminates). -/
def checkStack (locals : Nat → Ty) : List Ty → List Instr → Except String (List Ty)
  | base, [] => .ok base
  | base, .i32const _ :: is => checkStack locals (.i32 :: base) is
  | base, .i64const _ :: is => checkStack locals (.i64 :: base) is
  | base, .localget n :: is => checkStack locals (locals n :: base) is
  | base, .localset n :: is =>
      match base with
      | [] => .error "stack underflow"
      | t :: ts => if t = locals n then checkStack locals ts is
                   else .error "operand type mismatch"
  | base, .i32add :: is =>
      match base with
      | .i32 :: .i32 :: ts => checkStack locals (.i32 :: ts) is
      | _ => .error "operand type mismatch"
  | base, .i64add :: is =>
      match base with
      | .i64 :: .i64 :: ts => checkStack locals (.i64 :: ts) is
      | _ => .error "operand type mismatch"
  | base, .i32eq :: is =>
      match base with
      | .i32 :: .i32 :: ts => checkStack locals (.i32 :: ts) is
      | _ => .error "operand type mismatch"
  | base, .drop :: is =>
      match base with
      | [] => .error "stack underflow"
      | _ :: ts => checkStack locals ts is
  | base, .br _ :: _ => .ok base
  | base, .brif _ :: is =>
      match base with
      | .i32 :: ts => checkStack locals ts is
      | _ => .error "operand type mismatch"
  | base, .block body :: is =>
      match checkFrame locals base body with
      | .ok _ => checkStack locals base is
      | .error e => .error e
  | base, .loop body :: is =>
      match checkFrame locals base body with
      | .ok _ => checkStack locals base is
      | .error e => .error e
  | base, .if_ t e :: is =>
      match base with
      | .i32 :: ts =>
          match checkFrame locals ts t with
          | .ok _ =>
              match checkFrame locals ts e with
              | .ok _ => checkStack locals ts is
              | .error err => .error err
          | .error err => .error err
      | _ => .error "operand type mismatch"
  | base, .unreach :: _ => .ok base
  | base, .i32store8 :: is =>
      match base with
      | .i32 :: .i32 :: ts => checkStack locals ts is
      | _ => .error "operand type mismatch"

/-- Check a frame body against its entry type: the body must END at the
    entry type (no-result frame — the wasm `(block)` with no result
    type). This is what makes preservation go through: on fall-through
    the stack is statically the entry type, and on `br 0` the dynamic
    handler restores exactly the entry stack. -/
def checkFrame (locals : Nat → Ty) (base : List Ty) (body : List Instr) : Except String Unit :=
  match checkStack locals base body with
  | .ok mid => if mid = base then .ok () else .error "frame stack mismatch"
  | .error e => .error e
end

/-- `checkFrame`'s contract, in the direction the safety proof needs. -/
theorem checkFrame_ok (locals : Nat → Ty) (base : List Ty) (body : List Instr)
    (h : checkFrame locals base body = .ok ()) :
    checkStack locals base body = .ok base := by
  simp only [checkFrame] at h
  cases hc : checkStack locals base body with
  | error _ => rw [hc] at h; simp at h
  | ok mid =>
    by_cases hmid : mid = base
    . rw [hmid]
    . rw [hc] at h; simp [hmid] at h

/-! ## Type safety -/

/-- THE core lemma. Part 2 additionally assumes the tail `is` is checked
    `base → final` (the restart re-enters at `.loop body :: is`). -/
theorem exec_typed (locals : Nat → Ty) :
    ∀ fuel : Nat,
      (∀ body base final s,
          checkStack locals base body = .ok final →
          stackTys s.stack = base →
          (∀ n, tyOf (s.locals n) = locals n) →
          execList fuel s body ≠ .error .underflow
          ∧ (∀ s', execList fuel s body = .ok s' →
                stackTys s'.stack = final ∧ (∀ n, tyOf (s'.locals n) = locals n))
          ∧ (∀ n ls, execList fuel s body = .error (.branch n ls) →
                (∀ m, tyOf (ls m) = locals m)))
      ∧ (∀ is body base final s,
          checkFrame locals base body = .ok () →
          checkStack locals base is = .ok final →
          stackTys s.stack = base →
          (∀ n, tyOf (s.locals n) = locals n) →
          execList fuel s (.loop body :: is) ≠ .error .underflow
          ∧ (∀ s', execList fuel s (.loop body :: is) = .ok s' →
                stackTys s'.stack = final ∧ (∀ n, tyOf (s'.locals n) = locals n))
          ∧ (∀ n ls, execList fuel s (.loop body :: is) = .error (.branch n ls) →
                (∀ m, tyOf (ls m) = locals m))) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    . intro body base final s _ _ _
      simp [execList]
    . intro is body base final s _ _ _
      simp [execList]
  | succ fuel ih =>
    constructor
    . intro body base final s hcheck hstack hloc
      obtain ⟨loc, stk, mem, msz⟩ := s
      have hloc' : ∀ m, tyOf (loc m) = locals m := fun m => hloc m
      cases body with
      | nil =>
        simp only [checkStack] at hcheck
        cases hcheck
        simp only [execList]
        exact ⟨fun h => by simp at h,
               fun s' hEq => by injection hEq with hEq'; subst hEq'; exact ⟨hstack, hloc'⟩,
               fun n ls h => by simp at h⟩
      | cons i is =>
        cases i with
        | i32const n =>
          simp only [execList, step]
          exact ih.1 is (.i32 :: base) final ⟨loc, .i32 n :: stk, mem, msz⟩
            (by simp only [checkStack] at hcheck; exact hcheck)
            (by simp [stackTys, hstack]) hloc'
        | i64const n =>
          simp only [execList, step]
          exact ih.1 is (.i64 :: base) final ⟨loc, .i64 n :: stk, mem, msz⟩
            (by simp only [checkStack] at hcheck; exact hcheck)
            (by simp [stackTys, hstack]) hloc'
        | localget n =>
          simp only [execList, step]
          exact ih.1 is (locals n :: base) final ⟨loc, loc n :: stk, mem, msz⟩
            (by simp only [checkStack] at hcheck; exact hcheck)
            (by simp only [stackTys, hstack, hloc' n]) hloc'
        | localset n =>
          cases base with
          | nil => simp [checkStack] at hcheck
          | cons t ts =>
            by_cases hteq : t = locals n
            . have hcheck' : checkStack locals ts is = .ok final := by
                simpa [checkStack, hteq] using hcheck
              cases stk with
              | nil => simp [stackTys] at hstack
              | cons v vs =>
                have hshape : tyOf v = t ∧ stackTys vs = ts := by
                  simp [stackTys] at hstack
                  exact hstack
                simp only [execList, step]
                exact ih.1 is ts final
                  ⟨fun m => if m = n then v else loc m, vs, mem, msz⟩
                  hcheck' hshape.2
                  (by intro m
                      by_cases hm : m = n
                      · subst hm
                        show tyOf (if m = m then v else loc m) = locals m
                        rw [if_pos rfl]
                        exact hshape.1.trans hteq
                      · show tyOf (if m = n then v else loc m) = locals m
                        rw [if_neg hm]
                        exact hloc' m)
            . simp [checkStack, hteq] at hcheck
        | i32add =>
          cases base with
          | nil => simp [checkStack] at hcheck
          | cons t1 ts1 =>
            cases t1 with
            | i64 => simp [checkStack] at hcheck
            | i32 =>
              cases ts1 with
              | nil => simp [checkStack] at hcheck
              | cons t2 ts2 =>
                cases t2 with
                | i64 => simp [checkStack] at hcheck
                | i32 =>
                  cases stk with
                  | nil => simp [stackTys] at hstack
                  | cons v1 vs1 =>
                    cases v1 with
                    | i64 _ => simp [stackTys] at hstack
                    | i32 a =>
                      cases vs1 with
                      | nil => simp [stackTys] at hstack
                      | cons v2 vs2 =>
                        cases v2 with
                        | i64 _ => simp [stackTys] at hstack
                        | i32 b =>
                          have hcheck' : checkStack locals (.i32 :: ts2) is = .ok final := by
                            simp only [checkStack] at hcheck; exact hcheck
                          have hts : stackTys vs2 = ts2 := by
                            simp [stackTys] at hstack
                            exact hstack
                          simp only [execList, step]
                          exact ih.1 is (.i32 :: ts2) final
                            ⟨loc, .i32 (a + b) :: vs2, mem, msz⟩
                            hcheck' (by simp [stackTys, hts]) hloc'
        | i32eq =>
          -- the branch comparison (added by the cases lane): the same
          -- stack shape as i32add (pop two i32, push one) — the VALUE is
          -- irrelevant for typing, so the case is the i32add mirror.
          cases base with
          | nil => simp [checkStack] at hcheck
          | cons t1 ts1 =>
            cases t1 with
            | i64 => simp [checkStack] at hcheck
            | i32 =>
              cases ts1 with
              | nil => simp [checkStack] at hcheck
              | cons t2 ts2 =>
                cases t2 with
                | i64 => simp [checkStack] at hcheck
                | i32 =>
                  cases stk with
                  | nil => simp [stackTys] at hstack
                  | cons v1 vs1 =>
                    cases v1 with
                    | i64 _ => simp [stackTys] at hstack
                    | i32 a =>
                      cases vs1 with
                      | nil => simp [stackTys] at hstack
                      | cons v2 vs2 =>
                        cases v2 with
                        | i64 _ => simp [stackTys] at hstack
                        | i32 b =>
                          have hcheck' : checkStack locals (.i32 :: ts2) is = .ok final := by
                            simp only [checkStack] at hcheck; exact hcheck
                          have hts : stackTys vs2 = ts2 := by
                            simp [stackTys] at hstack
                            exact hstack
                          simp only [execList, step]
                          exact ih.1 is (.i32 :: ts2) final
                            ⟨loc, .i32 (if a == b then 1 else 0) :: vs2, mem, msz⟩
                            hcheck' (by simp [stackTys, hts]) hloc'
        | i64add =>
          -- the i32add case mirrored over i64 (added by the
          -- translation-correctness lane: the backend's `binop?` emits
          -- i64.add for UInt64.add — see the header ledger)
          cases base with
          | nil => simp [checkStack] at hcheck
          | cons t1 ts1 =>
            cases t1 with
            | i32 => simp [checkStack] at hcheck
            | i64 =>
              cases ts1 with
              | nil => simp [checkStack] at hcheck
              | cons t2 ts2 =>
                cases t2 with
                | i32 => simp [checkStack] at hcheck
                | i64 =>
                  cases stk with
                  | nil => simp [stackTys] at hstack
                  | cons v1 vs1 =>
                    cases v1 with
                    | i32 _ => simp [stackTys] at hstack
                    | i64 a =>
                      cases vs1 with
                      | nil => simp [stackTys] at hstack
                      | cons v2 vs2 =>
                        cases v2 with
                        | i32 _ => simp [stackTys] at hstack
                        | i64 b =>
                          have hcheck' : checkStack locals (.i64 :: ts2) is = .ok final := by
                            simp only [checkStack] at hcheck; exact hcheck
                          have hts : stackTys vs2 = ts2 := by
                            simp [stackTys] at hstack
                            exact hstack
                          simp only [execList, step]
                          exact ih.1 is (.i64 :: ts2) final
                            ⟨loc, .i64 (a + b) :: vs2, mem, msz⟩
                            hcheck' (by simp [stackTys, hts]) hloc'
        | drop =>
          cases base with
          | nil => simp [checkStack] at hcheck
          | cons t ts =>
            have hcheck' : checkStack locals ts is = .ok final := by
              simp only [checkStack] at hcheck; exact hcheck
            cases stk with
            | nil => simp [stackTys] at hstack
            | cons v vs =>
              have hts : stackTys vs = ts := by
                simp [stackTys] at hstack
                exact hstack.2
              simp only [execList, step]
              exact ih.1 is ts final ⟨loc, vs, mem, msz⟩ hcheck' hts hloc'
        | br n =>
          simp only [execList, step]
          exact ⟨fun h => by simp at h, fun s' h => by simp at h, fun n' ls hEq => by
            injection hEq with hI
            injection hI with _ hls
            subst hls
            exact hloc'⟩
        | brif n =>
          cases base with
          | nil => simp [checkStack] at hcheck
          | cons t1 ts1 =>
            cases t1 with
            | i64 => simp [checkStack] at hcheck
            | i32 =>
              have hcheck' : checkStack locals ts1 is = .ok final := by
                simp only [checkStack] at hcheck; exact hcheck
              cases stk with
              | nil => simp [stackTys] at hstack
              | cons v vs =>
                cases v with
                | i64 _ => simp [stackTys] at hstack
                | i32 b =>
                  have hts : stackTys vs = ts1 := by
                    simp [stackTys] at hstack
                    exact hstack
                  by_cases hb : b != 0
                  . simp only [execList, step, if_pos hb]
                    exact ⟨fun h => by simp at h, fun s' h => by simp at h,
                           fun n' ls hEq => by
                             injection hEq with hI
                             injection hI with _ hls
                             subst hls
                             exact hloc'⟩
                  . simp only [execList, step, if_neg hb]
                    exact ih.1 is ts1 final ⟨loc, vs, mem, msz⟩ hcheck' hts hloc'
        | block body =>
          have hfr : checkFrame locals base body = .ok ()
              ∧ checkStack locals base is = .ok final := by
            simp only [checkStack] at hcheck
            cases hf : checkFrame locals base body with
            | error _ => rw [hf] at hcheck; simp at hcheck
            | ok _ =>
                rw [hf] at hcheck; simp at hcheck
                exact ⟨rfl, hcheck⟩
          have hin := ih.1 body base base ⟨loc, stk, mem, msz⟩
            (checkFrame_ok locals base body hfr.1) hstack hloc
          cases hx : execList fuel ⟨loc, stk, mem, msz⟩ body with
          | ok s'' =>
            simp only [execList, hx]
            exact ih.1 is base final s'' hfr.2 (hin.2.1 s'' hx).1 (hin.2.1 s'' hx).2
          | error e =>
            cases e with
            | underflow =>
              simp only [execList, hx]
              exact absurd hx hin.1
            | trap =>
              simp only [execList, hx]
              refine ⟨?_, ?_, ?_⟩
              · intro h; cases h
              · intro s' h; cases h
              · intro n' ls' hEq; cases hEq
            | outOfFuel =>
              simp only [execList, hx]
              refine ⟨?_, ?_, ?_⟩
              · intro h; cases h
              · intro s' h; cases h
              · intro n' ls' hEq; cases hEq
            | structural =>
              simp only [execList, hx]
              refine ⟨?_, ?_, ?_⟩
              · intro h; cases h
              · intro s' h; cases h
              · intro n' ls' hEq; cases hEq
            | branch k ls =>
              cases k with
              | zero =>
                simp only [execList, hx]
                exact ih.1 is base final ⟨ls, stk, mem, msz⟩ hfr.2
                  (by simp [stackTys, hstack]) (fun m => hin.2.2 0 ls hx m)
              | succ k' =>
                simp only [execList, hx]
                refine ⟨fun h => by simp at h, fun s' h => by simp at h, fun n' ls' hEq => ?_⟩
                injection hEq with hI
                injection hI with _ hls
                subst hls
                exact hin.2.2 (k'+1) ls hx
        | loop body =>
          have hfr : checkFrame locals base body = .ok ()
              ∧ checkStack locals base is = .ok final := by
            simp only [checkStack] at hcheck
            cases hf : checkFrame locals base body with
            | error _ => rw [hf] at hcheck; simp at hcheck
            | ok _ =>
                rw [hf] at hcheck; simp at hcheck
                exact ⟨rfl, hcheck⟩
          have hin := ih.1 body base base ⟨loc, stk, mem, msz⟩
            (checkFrame_ok locals base body hfr.1) hstack hloc
          cases hx : execList fuel ⟨loc, stk, mem, msz⟩ body with
          | ok s'' =>
            simp only [execList, hx]
            exact ih.1 is base final s'' hfr.2 (hin.2.1 s'' hx).1 (hin.2.1 s'' hx).2
          | error e =>
            cases e with
            | underflow =>
              simp only [execList, hx]
              exact absurd hx hin.1
            | trap =>
              simp only [execList, hx]
              refine ⟨?_, ?_, ?_⟩
              · intro h; cases h
              · intro s' h; cases h
              · intro n' ls' hEq; cases hEq
            | outOfFuel =>
              simp only [execList, hx]
              refine ⟨?_, ?_, ?_⟩
              · intro h; cases h
              · intro s' h; cases h
              · intro n' ls' hEq; cases hEq
            | structural =>
              simp only [execList, hx]
              refine ⟨?_, ?_, ?_⟩
              · intro h; cases h
              · intro s' h; cases h
              · intro n' ls' hEq; cases hEq
            | branch k ls =>
              cases k with
              | zero =>
                simp only [execList, hx]
                exact ih.2 is body base final ⟨ls, stk, mem, msz⟩ hfr.1 hfr.2
                  (by simp [stackTys, hstack]) (fun m => hin.2.2 0 ls hx m)
              | succ k' =>
                simp only [execList, hx]
                refine ⟨fun h => by simp at h, fun s' h => by simp at h, fun n' ls' hEq => ?_⟩
                injection hEq with hI
                injection hI with _ hls
                subst hls
                exact hin.2.2 (k'+1) ls hx
        | if_ t e =>
          cases base with
          | nil => simp [checkStack] at hcheck
          | cons t1 ts1 =>
            cases t1 with
            | i64 => simp [checkStack] at hcheck
            | i32 =>
              have hcks : checkStack locals ts1 is = .ok final
                  ∧ checkStack locals ts1 t = .ok ts1
                  ∧ checkStack locals ts1 e = .ok ts1 := by
                simp only [checkStack] at hcheck
                cases hf1 : checkFrame locals ts1 t with
                | error _ => rw [hf1] at hcheck; simp at hcheck
                | ok _ =>
                    rw [hf1] at hcheck
                    cases hf2 : checkFrame locals ts1 e with
                    | error _ => rw [hf2] at hcheck; simp at hcheck
                    | ok _ =>
                        rw [hf2] at hcheck; simp at hcheck
                        exact ⟨hcheck, checkFrame_ok locals ts1 t hf1,
                               checkFrame_ok locals ts1 e hf2⟩
              cases stk with
              | nil => simp [stackTys] at hstack
              | cons v vs =>
                cases v with
                | i64 _ => simp [stackTys] at hstack
                | i32 b =>
                  have hts : stackTys vs = ts1 := by
                    simp [stackTys] at hstack
                    exact hstack
                  have hthen := ih.1 t ts1 ts1 ⟨loc, vs, mem, msz⟩ hcks.2.1 hts hloc'
                  have helse := ih.1 e ts1 ts1 ⟨loc, vs, mem, msz⟩ hcks.2.2 hts hloc'
                  by_cases hb : b != 0
                  . simp only [execList, if_pos hb]
                    cases hx : execList fuel ⟨loc, vs, mem, msz⟩ t with
                    | ok s'' =>
                      exact ih.1 is ts1 final s'' hcks.1 (hthen.2.1 s'' hx).1
                        (hthen.2.1 s'' hx).2
                    | error ex =>
                      cases ex with
                      | underflow =>
                        simp only [execList, hx]
                        exact absurd hx hthen.1
                      | trap =>
                        simp only [execList, hx]
                        refine ⟨?_, ?_, ?_⟩
                        · intro h; cases h
                        · intro s' h; cases h
                        · intro n' ls' hEq; cases hEq
                      | outOfFuel =>
                        simp only [execList, hx]
                        refine ⟨?_, ?_, ?_⟩
                        · intro h; cases h
                        · intro s' h; cases h
                        · intro n' ls' hEq; cases hEq
                      | structural =>
                        simp only [execList, hx]
                        refine ⟨?_, ?_, ?_⟩
                        · intro h; cases h
                        · intro s' h; cases h
                        · intro n' ls' hEq; cases hEq
                      | branch k ls =>
                        cases k with
                        | zero =>
                          simp only [execList, hx]
                          exact ih.1 is ts1 final ⟨ls, vs, mem, msz⟩ hcks.1 hts
                            (fun m => hthen.2.2 0 ls hx m)
                        | succ k' =>
                          simp only [execList, hx]
                          refine ⟨fun h => by simp at h, fun s' h => by simp at h,
                                  fun n' ls' hEq => ?_⟩
                          injection hEq with hI
                          injection hI with _ hls
                          subst hls
                          exact hthen.2.2 (k'+1) ls hx
                  . simp only [execList, if_neg hb]
                    cases hx : execList fuel ⟨loc, vs, mem, msz⟩ e with
                    | ok s'' =>
                      exact ih.1 is ts1 final s'' hcks.1 (helse.2.1 s'' hx).1
                        (helse.2.1 s'' hx).2
                    | error ex =>
                      cases ex with
                      | underflow =>
                        simp only [execList, hx]
                        exact absurd hx helse.1
                      | trap =>
                        simp only [execList, hx]
                        refine ⟨?_, ?_, ?_⟩
                        · intro h; cases h
                        · intro s' h; cases h
                        · intro n' ls' hEq; cases hEq
                      | outOfFuel =>
                        simp only [execList, hx]
                        refine ⟨?_, ?_, ?_⟩
                        · intro h; cases h
                        · intro s' h; cases h
                        · intro n' ls' hEq; cases hEq
                      | structural =>
                        simp only [execList, hx]
                        refine ⟨?_, ?_, ?_⟩
                        · intro h; cases h
                        · intro s' h; cases h
                        · intro n' ls' hEq; cases hEq
                      | branch k ls =>
                        cases k with
                        | zero =>
                          simp only [execList, hx]
                          exact ih.1 is ts1 final ⟨ls, vs, mem, msz⟩ hcks.1 hts
                            (fun m => helse.2.2 0 ls hx m)
                        | succ k' =>
                          simp only [execList, hx]
                          refine ⟨fun h => by simp at h, fun s' h => by simp at h,
                                  fun n' ls' hEq => ?_⟩
                          injection hEq with hI
                          injection hI with _ hls
                          subst hls
                          exact helse.2.2 (k'+1) ls hx
        | unreach =>
          simp only [execList, step]
          refine ⟨?_, ?_, ?_⟩
          · intro h; cases h
          · intro s' h; cases h
          · intro n ls h; cases h
        | i32store8 =>
          cases base with
          | nil => simp [checkStack] at hcheck
          | cons t1 ts1 =>
            cases t1 with
            | i64 => simp [checkStack] at hcheck
            | i32 =>
              cases ts1 with
              | nil => simp [checkStack] at hcheck
              | cons t2 ts2 =>
                cases t2 with
                | i64 => simp [checkStack] at hcheck
                | i32 =>
                  cases stk with
                  | nil => simp [stackTys] at hstack
                  | cons v1 vs1 =>
                    cases v1 with
                    | i64 _ => simp [stackTys] at hstack
                    | i32 v =>
                      cases vs1 with
                      | nil => simp [stackTys] at hstack
                      | cons v2 vs2 =>
                        cases v2 with
                        | i64 _ => simp [stackTys] at hstack
                        | i32 a =>
                          have hcheck' : checkStack locals ts2 is = .ok final := by
                            simp only [checkStack] at hcheck; exact hcheck
                          have hts : stackTys vs2 = ts2 := by
                            simp [stackTys] at hstack
                            exact hstack
                          by_cases hlt : a.toNat < msz
                          . simp only [execList, step, if_pos hlt]
                            exact ih.1 is ts2 final
                              ⟨loc, vs2, fun i => if i = a.toNat then v.toUInt8 else mem i,
                                msz⟩
                              hcheck' hts hloc'
                          . simp only [execList, step, if_neg hlt]
                            refine ⟨?_, ?_, ?_⟩
                            · intro h; cases h
                            · intro s' h; cases h
                            · intro n' ls hEq; cases hEq
    . intro is body base final s hfr hcheck hstack hloc
      obtain ⟨loc, stk, mem, msz⟩ := s
      have hloc' : ∀ m, tyOf (loc m) = locals m := fun m => hloc m
      have hcheck' := checkFrame_ok locals base body hfr
      have hin := ih.1 body base base ⟨loc, stk, mem, msz⟩ hcheck' hstack hloc
      cases hx : execList fuel ⟨loc, stk, mem, msz⟩ body with
      | ok s' =>
        simp only [execList, hx]
        exact ih.1 is base final s' hcheck (hin.2.1 s' hx).1 (hin.2.1 s' hx).2
      | error e =>
        cases e with
        | underflow =>
          simp only [execList, hx]
          exact absurd hx hin.1
        | trap =>
          simp only [execList, hx]
          refine ⟨?_, ?_, ?_⟩
          · intro h; cases h
          · intro s' h; cases h
          · intro n' ls' hEq; cases hEq
        | outOfFuel =>
          simp only [execList, hx]
          refine ⟨?_, ?_, ?_⟩
          · intro h; cases h
          · intro s' h; cases h
          · intro n' ls' hEq; cases hEq
        | structural =>
          simp only [execList, hx]
          refine ⟨?_, ?_, ?_⟩
          · intro h; cases h
          · intro s' h; cases h
          · intro n' ls' hEq; cases hEq
        | branch k ls =>
          cases k with
          | zero =>
            simp only [execList, hx]
            exact ih.2 is body base final ⟨ls, stk, mem, msz⟩ hfr hcheck
              (by simp [stackTys, hstack]) (fun m => hin.2.2 0 ls hx m)
          | succ k' =>
            simp only [execList, hx]
            refine ⟨fun h => by simp at h, fun s' h => by simp at h, fun n' ls' hEq => ?_⟩
            injection hEq with hI
            injection hI with _ hls
            subst hls
            exact hin.2.2 (k'+1) ls hx

/-- THE deliverable theorem: a well-typed program (checked against
    its declared type), NEVER raises the stack-underflow error; and
    if it completes normally, the final stack is statically `final` with
    the locals well-formedness preserved (preservation). -/
theorem typeSafety (locals : Nat → Ty) (body : List Instr) (base final : List Ty)
    (s : State)
    (hcheck : checkStack locals base body = .ok final)
    (hstack : stackTys s.stack = base)
    (hloc : ∀ n, tyOf (s.locals n) = locals n) :
    exec s body ≠ .error .underflow
    ∧ (∀ s', exec s body = .ok s' →
          stackTys s'.stack = final ∧ (∀ n, tyOf (s'.locals n) = locals n)) := by
  have h := (exec_typed locals defaultFuel).1 body base final s hcheck hstack hloc
  exact ⟨h.1, h.2.1⟩

/-! ## Memory safety -/

/-- THE MEMORY SAFETY THEOREM (the bounded-memory variant, stated
    honestly): a successful one-byte store happened at an address
    strictly inside the memory, changed exactly ONE byte, and left the
    locals and the rest of the stack intact. Out-of-bounds = a trap,
    never a write — by construction (the `if` guard), and this theorem
    pins it. -/
theorem storeInBounds (s s' : State)
    (h : step s .i32store8 = .ok s') :
    ∃ v a : UInt32, ∃ rest : List Val,
      s.stack = .i32 v :: .i32 a :: rest
      ∧ a.toNat < s.memSize
      ∧ (∀ i : Nat, i ≠ a.toNat → s'.mem i = s.mem i)
      ∧ s'.mem a.toNat = v.toUInt8
      ∧ s'.stack = rest
      ∧ s'.locals = s.locals := by
  simp only [step] at h
  cases hs : s.stack with
  | nil => rw [hs] at h; simp at h
  | cons v vs =>
    cases v with
    | i64 _ => rw [hs] at h; simp at h
    | i32 v =>
      cases vs with
      | nil => rw [hs] at h; simp at h
      | cons a rest =>
        cases a with
        | i64 _ => rw [hs] at h; simp at h
        | i32 a =>
          rw [hs] at h
          simp only [] at h
          by_cases hlt : a.toNat < s.memSize
          . rw [if_pos hlt] at h
            cases h
            refine ⟨v, a, rest, rfl, hlt, ?_, ?_, ?_, ?_⟩
            . intro i hi; simp [hi]
            . simp
            . simp
            . simp
          . rw [if_neg hlt] at h; simp at h

/-! ## Tests — the semantics' unit tests (elaboration-time #guard gates)

Every `#guard` here is checked at BUILD time (a failure fails the
build, not just a test run). The last block is THE NEGATIVE CONTROL: an
underflowing program is REJECTED by `checkStack` AND traps with
`.underflow` in `exec` — proving the checker is not vacuous.
-/

section Tests

/-- A canonical init state: all-`i32 0` locals, empty stack, 64 bytes
    of zeroed memory. -/
def initState : State := ⟨fun _ => .i32 0, [], fun _ => (0 : UInt8), 64⟩

/-- The locals' type context matching `initState` (all i32). -/
def localsI32 : Nat → Ty := fun _ => Ty.i32

/-- The final stack, if execution succeeds. -/
def finalStack (s : State) (body : List Instr) : Except Err (List Val) :=
  match exec s body with
  | .ok s' => .ok s'.stack
  | .error e => .error e

-- 1. push/push/add/drop round-trip: types check, stack empties.
def progAdd : List Instr := [.i32const 2, .i32const 3, .i32add, .drop]
#guard (match checkStack localsI32 [] progAdd with | .ok [] => true | _ => false) = true
#guard (match finalStack initState progAdd with | .ok [] => true | _ => false) = true

-- 2. add computes: 2 + 3 = 5 (kept on the stack).
def progAddKeep : List Instr := [.i32const 2, .i32const 3, .i32add]
#guard (match finalStack initState progAddKeep with
        | .ok [.i32 5] => true | _ => false) = true

-- 3. locals round-trip: set 9 into local 0, get it back.
def progLocal : List Instr := [.i32const 9, .localset 0, .localget 0]
#guard (match checkStack localsI32 [] progLocal with
        | .ok [Ty.i32] => true | _ => false) = true
#guard (match finalStack initState progLocal with
        | .ok [.i32 9] => true | _ => false) = true

-- 4. block + br 0: the branch EXITS the block, skipping the const 2,
--    and restores the block-entry stack.
def progBr : List Instr := [.i32const 1, .block [.br 0, .i32const 2]]
#guard (match checkStack localsI32 [] progBr with
        | .ok [Ty.i32] => true | _ => false) = true
#guard (match finalStack initState progBr with
        | .ok [.i32 1] => true | _ => false) = true

-- 5. if/else: cond = 0 takes the else branch. The frame is no-result,
--    so the else body must END at the entry type: it drops the 5 and
--    pushes an i32 back (net-zero). Final stack: the 5.
def progIf : List Instr := [.i32const 5, .i32const 0, .if_ [] [.drop, .i32const 5]]
#guard (match checkStack localsI32 [] progIf with
        | .ok [Ty.i32] => true | _ => false) = true
#guard (match finalStack initState progIf with
        | .ok [.i32 5] => true | _ => false) = true

-- 6. br_if false: falls through; the condition is popped, the 7 stays.
def progBrif : List Instr := [.i32const 7, .i32const 0, .brif 0]
#guard (match finalStack initState progBrif with
        | .ok [.i32 7] => true | _ => false) = true

-- 7. store: mem[3] := 7, exactly one byte, stack drains.
def progStore : List Instr := [.i32const 3, .i32const 7, .i32store8]
#guard (match checkStack localsI32 [] progStore with | .ok [] => true | _ => false) = true
#guard (match exec initState progStore with
        | .ok s => s.stack == [] && s.mem 3 == (7 : UInt8) && s.mem 4 == (0 : UInt8)
        | .error _ => false) = true

-- 8. THE NEGATIVE CONTROL (typing): [.i32add] on an empty stack is
--    REJECTED by the checker.
#guard (match checkStack localsI32 [] [.i32add] with
        | .ok _ => false | .error _ => true) = true

-- 9. THE NEGATIVE CONTROL (execution): the same program UNDERFLOWS in
--    exec — the checker's rejection is not vacuous.
#guard (match exec initState [.i32add] with
        | .error .underflow => true | _ => false) = true

-- 10. NEGATIVE CONTROL (memory): an out-of-bounds store TRAPS and
--     never writes.
def progOOB : List Instr := [.i32const 100, .i32const 1, .i32store8]
#guard (match exec initState progOOB with
        | .error .trap => true | _ => false) = true

-- 11. NEGATIVE CONTROL (drop): drop on an empty stack underflows.
#guard (match checkStack localsI32 [] [.drop] with
        | .ok _ => false | .error _ => true) = true
#guard (match exec initState [.drop] with
        | .error .underflow => true | _ => false) = true

end Tests

/-! ## The calls layer (v1) — CALLS as FUNCTION-COMPOSITION

THE SCOPE DECISION (the CALL-SEMANTICS lane's): the previous slice
proved the CALLING CONVENTION as a CONTRACT theorem in
`WasmBackend.Correct` (the caller's prep + the callee's prologue = the
values-through) over the FLAT machine — `Instr` had NO call and
`State` NO frames. This section puts CALLS in the model, v1, WITHOUT
touching the flat machine: NO `Instr.call` constructor (it would break
`checkStack`/`exec_typed`'s exhaustive cases — the proven core is
statement-frozen), NO `State` frames. Instead the call is a BIG-STEP
OPERATOR at the program level: `callExecFuel f args s` runs the callee
`f : Fn` (arity + body — the callee IS the code; no module table) as a
SUB-EXEC of the caller's state with the args BOUND to the callee's
param locals (`bindArgs`) and the args POPPED off the operand stack
(wasm's `call` operand order: the args are pushed in order, param 0
DEEPEST; the call pops them — top-first — into the params).

`call_split` is the SEMANTIC version of Correct.lean's contract
theorems: the caller's flat program — the arg pushes (`pushArgs`), the
binding pops as `local.set`s (`popParams`), then the callee's body —
EXECUTES EXACTLY AS the big-step `callExecFuel`. The convention is no
longer a contract about two lists; it is a program EQUALITY with the
callee appended, and the end-to-end theorems (`call_exec_correct`, the
trampoline demo) compose it.

THE HONEST LIMITS (v1, documented):

* NO CALL-FRAMES: the callee's param locals are a locals-OVERRIDE of
  the caller's state (params = locals 0..arity-1). The frame
  separation is exactly Correct.lean's pairwise-distinctness
  hypotheses, now BUILT INTO `bindArgs`. A callee that clobbers its
  params sees only its own args — but a caller that keeps live values
  in locals 0..arity-1 across a call is OUTSIDE the v1 fragment
  (the emitter's calls never do: the caller's live values sit above
  the args on the stack / in higher locals).
* NON-RECURSIVE ONLY: the sub-exec budget is THIS call's fuel — a
  self-recursive callee re-enters with the SAME remaining fuel inside
  one `execList` and exhausts it (surfacing as `outOfFuel`, never a
  wrong answer). Real call-frames are the follow-up.
* DIRECT CALLS ONLY: `Fn` is the callee's code — there is no funcref
  table, so `call_indirect` (the golden's real dispatch) is the
  follow-up. The trampoline demo below models the DIRECT hop
  (`call $curried._boxed` in the golden's `pap_curried._boxed_1`).
* WRONG ARITY = TRAP: `callExecFuel` guards `args.length = f.params`
  (the v1 stand-in for the validator's static arity check — the flat
  checker is shape-only and cannot see arity; the flat COMPOSED
  program with a short prep surfaces it as `underflow` instead — both
  pinned in the tests).
-/

namespace Calls

/-! ### The callee: a function record (arity + body) -/

/-- A function: the arity (the param count = the callee's locals
    0..arity-1) and the body (the flat instruction list). v1's callee —
    the Fn value IS the code; the module-level function table (the
    `FnRef` → record map that `call_indirect` dispatches through) is
    the follow-up. -/
structure Fn where
  /-- The number of params the callee binds (locals 0..params-1). -/
  params : Nat
  /-- The callee's body. -/
  body : List Instr

/-! ### The call's two faces -/

/-- Drop the bottom `n` entries of a stack (head = TOP): the args sit
    DEEPEST, so the call's pop removes them from the bottom. -/
def dropBottom (n : Nat) (l : List Val) : List Val :=
  (l.reverse.drop n).reverse

/-- The callee's entry state: the args bound to the param locals
    (param i = the i-th PUSHED value = `args[i]` — wasm's `call`
    binds param i to the i-th operand) and the args popped off the
    stack (bottom removal). Out-of-range locals pass through — the
    arity guard in `callExecFuel` is what makes `params` the truth. -/
def bindArgs (args : List Val) (s : State) : State :=
  { s with locals := fun n => args.getD n (s.locals n)
         , stack := dropBottom args.length s.stack }

/-- THE CALL (fuel-explicit big step): arity-guarded, then the
callee's body runs as a SUB-EXEC from the bound state. Wrong arity =
the trap (the v1 stand-in for the validator's static check). -/
def callExecFuel (fuel : Nat) (f : Fn) (args : List Val) (s : State) :
    Except Err State :=
  if args.length = f.params
  then execList fuel (bindArgs args s) f.body
  else .error .trap

/-- THE CALL at the top-level budget (`exec`'s fuel). -/
def callExec (f : Fn) (args : List Val) (s : State) : Except Err State :=
  callExecFuel defaultFuel f args s

/-- THE ARITY GUARD: a wrong-arity call is the trap — never a silent
    mis-bind (the checker is shape-only and cannot see arity; this
    guard is the machine's own). -/
theorem callExecFuel_arity_trap (fuel : Nat) (f : Fn) (args : List Val)
    (s : State) (h : args.length ≠ f.params) :
    callExecFuel fuel f args s = .error .trap := by
  simp [callExecFuel, h]

/-! ### The caller's side: the prep and the binding as FLAT programs -/

/-- The value → const push. -/
def constOf : Val → Instr
  | .i32 n => .i32const n
  | .i64 n => .i64const n

/-- The caller's CALL-PREP: push the args IN ORDER — param 0 deepest
    (the golden trampolines' order: the closure ptr first, then the
    fresh args; Correct.lean's `tplCallPrep1/2`). -/
def pushArgs : List Val → List Instr
  | [] => []
  | a :: as => constOf a :: pushArgs as

/-- The call's BINDING as flat instructions: pop the args TOP-first
    into the param locals — the LAST pushed = the HIGHEST param
    (param i = the i-th pushed). For k params:
    `[local.set k-1, …, local.set 0]`. -/
def popParams : Nat → List Instr
  | 0 => []
  | k + 1 => .localset k :: popParams k

/-! ### The split theorems -/

/-- `getD` on a one-element append: the appended element is the
    length-indexed lookup (the calls layer's helper — core has no
    `getD_append`). -/
theorem getD_append_single {r d : Val} :
    ∀ (l : List Val) (m : Nat), (l ++ [r]).getD m d
      = if m < l.length then l.getD m d
        else if m = l.length then r else d := by
  intro l
  induction l with
  | nil => intro m; cases m <;> simp
  | cons x xs ih =>
    intro m
    cases m with
    | zero => simp
    | succ m =>
      have h := ih m
      by_cases hm : m < xs.length
      · simp [List.getD, List.getElem?_cons_succ, List.getElem?_append,
          List.length_cons, h, hm]
      · by_cases he : m = xs.length
        · simp [List.getD, List.getElem?_cons_succ, List.getElem?_append,
            List.length_cons, h, he]
        · have h1 : ¬ m < xs.length := by omega
          simp [List.getD, List.getElem?_cons_succ, List.getElem?_append,
            List.length_cons, h, he, h1]
          rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]

/-- The push phase: `pushArgs ++ rest` executes as `rest` from the
    stack `args.reverse ++ s.stack` (the args pushed in order, param 0
    deepest), one fuel unit per arg. -/
theorem pushArgs_exec (args : List Val) :
    ∀ (fuel : Nat) (rest : List Instr) (s : State), args.length < fuel →
      execList fuel s (pushArgs args ++ rest)
        = execList (fuel - args.length)
            { s with stack := args.reverse ++ s.stack } rest := by
  induction args with
  | nil =>
    intro fuel rest s hf
    cases fuel with
    | zero => simp at hf
    | succ n => simp [pushArgs, execList]
  | cons a as ih =>
    intro fuel rest s hf
    cases fuel with
    | zero => simp at hf
    | succ n =>
      simp only [List.length_cons] at hf
      simp only [pushArgs, List.cons_append, execList, List.length_cons]
      cases a with
      | i32 c =>
        simp only [step, constOf, List.reverse_cons, List.append_assoc]
        rw [show n + 1 - (as.length + 1) = n - as.length from by omega]
        exact ih n rest { s with stack := .i32 c :: s.stack } (by omega)
      | i64 c =>
        simp only [step, constOf, List.reverse_cons, List.append_assoc]
        rw [show n + 1 - (as.length + 1) = n - as.length from by omega]
        exact ih n rest { s with stack := .i64 c :: s.stack } (by omega)

/-- The pop phase (stated over the args' STACK IMAGE `rs` — head =
    top): `popParams rs.length ++ rest` executes as `rest` from the
    state with the args bound to the param locals (`rs.reverse` = the
    args in push order) and the stack drained to `bot`, one fuel unit
    per pop. This is Correct.lean's convention contract as a program
    EQUALITY. -/
theorem popParams_exec (rs : List Val) :
    ∀ (fuel : Nat) (rest : List Instr) (bot : List Val) (s : State),
      s.stack = rs ++ bot → rs.length < fuel →
      execList fuel s (popParams rs.length ++ rest)
        = execList (fuel - rs.length)
            { s with locals := fun n => rs.reverse.getD n (s.locals n)
                   , stack := bot } rest := by
  induction rs with
  | nil =>
    intro fuel rest bot s hs hf
    cases fuel with
    | zero => simp at hf
    | succ n =>
      rw [List.nil_append] at hs
      subst hs
      have hloc : (fun m => ([] : List Val).reverse.getD m (s.locals m))
          = s.locals := by funext m; simp
      simp [popParams, execList, hloc]
  | cons r rs ih =>
    intro fuel rest bot s hs hf
    cases fuel with
    | zero => simp at hf
    | succ n =>
      simp only [List.length_cons] at hf
      -- the head of the `rs ++ bot`-shaped stack is `r` (the top arg
      -- = the HIGHEST param); `localset rs.length` binds it, then the
      -- IH binds the rest into locals rs.length-1 … 0.
      have hstep : execList (n + 1) s
            (.localset rs.length :: (popParams rs.length ++ rest))
          = execList n
              { s with locals := fun m => if m = rs.length then r else s.locals m
                     , stack := rs ++ bot }
              (popParams rs.length ++ rest) := by
        simp only [execList, step, hs, List.cons_append]
      simp only [List.length_cons, popParams, List.cons_append, hstep]
      have hI := ih n rest bot
        { s with locals := fun m => if m = rs.length then r else s.locals m
                , stack := rs ++ bot } rfl (by omega)
      simp only [hI]
      -- the composed locals: param binding = `rs.reverse ++ [r]`'s getD
      have hfun : ∀ m, rs.reverse.getD m
                      ((fun k => if k = rs.length then r else s.locals k) m)
          = (rs.reverse ++ [r]).getD m (s.locals m) := by
        intro m
        rw [getD_append_single]
        simp only [List.getD]
        by_cases hm : m < rs.length
        · have h2 : m ≠ rs.length := by omega
          simp [hm, h2, List.length_reverse]
        · by_cases hme : m = rs.length
          · have hrn : rs.reverse.length = rs.length := by simp
            have hnone : rs.reverse[m]? = none :=
              List.getElem?_eq_none (by rw [hrn]; exact Nat.le_of_eq hme.symm)
            simp [hme, hrn, hnone]
          · have h1 : ¬ m < rs.length := by omega
            have h3 : m ≠ rs.reverse.length := by
              rw [List.length_reverse]; exact hme
            have hrn : rs.reverse.length = rs.length := by simp
            have hnone : rs.reverse[m]? = none :=
              List.getElem?_eq_none (by rw [hrn]; exact Nat.le_of_not_lt h1)
            simp [h1, hme, h3, hrn, hnone]
      rw [show n + 1 - (rs.length + 1) = n - rs.length from by omega]
      simp only [hfun, List.reverse_cons]

/-- THE SPLIT THEOREM — the calls layer's central equality, the
    SEMANTIC version of Correct.lean's `call_convention*` contract
    theorems: the caller's FLAT program (the arg pushes, the binding
    pops, then the callee's body) executes EXACTLY AS the big-step
    call (bind the args, run the body as a sub-exec). The convention
    is now a program equality with the callee appended, not a contract
    about two lists. -/
theorem call_split (fuel : Nat) (f : Fn) (args : List Val) (s : State)
    (harity : args.length = f.params) (hs : s.stack = [])
    (hf : 2 * args.length < fuel) :
    execList fuel s (pushArgs args ++ (popParams args.length ++ f.body))
      = callExecFuel (fuel - 2 * args.length) f args s := by
  have h1 := pushArgs_exec args fuel (popParams args.length ++ f.body) s (by omega)
  rw [h1]
  simp only [hs, List.append_nil]
  have h2 := popParams_exec args.reverse (fuel - args.length) f.body []
    { s with stack := args.reverse }
    (by simp [List.append_nil]) (by simp; omega)
  simp only [List.length_reverse] at h2
  rw [h2]
  -- both sides: the bound state, the callee's body
  have hfin : fuel - args.length - args.length = fuel - 2 * args.length := by omega
  rw [hfin]
  have hstack : ((s.stack.reverse.drop args.length).reverse) = [] := by
    rw [hs]; simp
  have hloc : ∀ n, args.reverse.reverse.getD n (s.locals n)
      = args.getD n (s.locals n) := by
    intro n; simp
  simp only [callExecFuel]
  rw [if_pos harity]
  simp only [bindArgs, dropBottom, hstack, hloc]

/-! ### The end-to-end theorems -/

/-- The adder callee — the golden's `curried._boxed` shape (the
    trampoline's target): the two params summed; the result = the
    final stack's top (the return convention). -/
def adderFn : Fn := { params := 2, body := [.localget 0, .localget 1, .i64add] }

/-- THE CALL-EXECUTION THEOREM: the caller's prep (the args' pushes),
    the call's binding (the pops), and the callee's body compose to
    compute the CALLEE's result on the caller's stack — the args go
    IN, the callee-computed sum comes OUT. Symbolic args, arbitrary
    initial state, kernel-checked. -/
theorem call_exec_correct (fuel : Nat) (a b : UInt64) (s : State)
    (hs : s.stack = []) (hf : 2 * 2 + 4 ≤ fuel) :
    ∃ s', execList fuel s
        (pushArgs [.i64 a, .i64 b] ++ (popParams 2 ++ adderFn.body))
      = .ok s' ∧ s'.stack = [.i64 (a + b)] := by
  have h := call_split fuel adderFn [.i64 a, .i64 b] s rfl hs
    (by have hl : ([.i64 a, .i64 b] : List Val).length = 2 := rfl; omega)
  simp only [List.length_cons, List.length_nil] at h
  simp only [h]
  obtain ⟨m, rfl⟩ : ∃ m', fuel = m' + 8 := ⟨fuel - 8, by omega⟩
  simp only [callExecFuel, adderFn, List.length_cons, List.length_nil]
  rw [show m + 8 - 2 * 2 = m + 4 from by omega]
  simp only [bindArgs, dropBottom, hs, List.reverse_nil, List.drop_nil,
    List.reverse_reverse]
  simp only [execList, step, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  refine ⟨_, rfl, ?_⟩
  rw [UInt64.add_comm]

/-- The first-param callee (returns param 0 — exposes the binding;
    the negative control's target). -/
def head0Fn : Fn := { params := 2, body := [.localget 0] }

/-- The convention's POSITIVE pin at the machine level (the head0
    callee): the correctly-ordered prep delivers param 0 = the FIRST
    arg — the mirror of `call_prep_swapped`. -/
theorem call_prep_ok (fuel : Nat) (a b : UInt64) (s : State)
    (hs : s.stack = []) (hf : 2 * 2 + 2 ≤ fuel) :
    ∃ s', execList fuel s
        (pushArgs [.i64 a, .i64 b] ++ (popParams 2 ++ head0Fn.body))
      = .ok s' ∧ s'.stack = [.i64 a] := by
  have h := call_split fuel head0Fn [.i64 a, .i64 b] s rfl hs
    (by have hl : ([.i64 a, .i64 b] : List Val).length = 2 := rfl; omega)
  simp only [List.length_cons, List.length_nil] at h
  simp only [h]
  obtain ⟨m, rfl⟩ : ∃ m', fuel = m' + 6 := ⟨fuel - 6, by omega⟩
  simp only [callExecFuel, head0Fn, List.length_cons, List.length_nil]
  rw [show m + 6 - 2 * 2 = m + 2 from by omega]
  simp only [bindArgs, dropBottom, hs, List.reverse_nil, List.drop_nil,
    List.reverse_reverse]
  simp only [execList, step, List.getD, List.getElem?_cons_zero,
    Option.getD_some]
  exact ⟨_, rfl, rfl⟩

/-- THE NEGATIVE CONTROL (the arg-order swap — the calling-convention
    bug class, now at the MACHINE level): pushing the args in REVERSE
    order binds param 0 = the LAST arg, and the callee computes on the
    swapped binding. Same input state, different result — the
    checker cannot see it (shape-only); the disagreement is a theorem
    (`call_prep_swapped_disagrees`). -/
theorem call_prep_swapped (fuel : Nat) (a b : UInt64) (s : State)
    (hs : s.stack = []) (hf : 2 * 2 + 2 ≤ fuel) :
    ∃ s', execList fuel s
        (pushArgs [.i64 b, .i64 a] ++ (popParams 2 ++ head0Fn.body))
      = .ok s' ∧ s'.stack = [.i64 b] := by
  have h := call_split fuel head0Fn [.i64 b, .i64 a] s rfl hs
    (by have hl : ([.i64 b, .i64 a] : List Val).length = 2 := rfl; omega)
  simp only [List.length_cons, List.length_nil] at h
  simp only [h]
  obtain ⟨m, rfl⟩ : ∃ m', fuel = m' + 6 := ⟨fuel - 6, by omega⟩
  simp only [callExecFuel, head0Fn, List.length_cons, List.length_nil]
  rw [show m + 6 - 2 * 2 = m + 2 from by omega]
  simp only [bindArgs, dropBottom, hs, List.reverse_nil, List.drop_nil,
    List.reverse_reverse]
  simp only [execList, step, List.getD, List.getElem?_cons_zero,
    Option.getD_some]
  exact ⟨_, rfl, rfl⟩

/-- THE NEGATIVE INSTANCE: the swapped prep DISAGREES with the
    convention — same input state, different result stack. If a
    regression re-swapped the arg pushes, this theorem's shape is what
    the differential duel's sabotage control checks empirically. -/
theorem call_prep_swapped_disagrees (fuel : Nat) (a b : UInt64) (s : State)
    (hs : s.stack = []) (hAB : a ≠ b) (hf : 2 * 2 + 3 ≤ fuel) :
    (match execList fuel s
        (pushArgs [.i64 a, .i64 b] ++ (popParams 2 ++ head0Fn.body)) with
     | .ok s' => s'.stack | .error _ => [])
      ≠ (match execList fuel s
        (pushArgs [.i64 b, .i64 a] ++ (popParams 2 ++ head0Fn.body)) with
     | .ok s' => s'.stack | .error _ => []) := by
  obtain ⟨s1, h1, h1s⟩ := call_prep_ok fuel a b s hs (by omega)
  obtain ⟨s2, h2, h2s⟩ := call_prep_swapped fuel a b s hs (by omega)
  intro hEq
  rw [h1, h2] at hEq
  simp only at hEq
  rw [h1s, h2s] at hEq
  injection hEq with hA hE1
  injection hA with hABeq
  exact hAB hABeq

/-! ### The trampoline demo (the golden's DIRECT hop) -/

/-- The trampoline's target — the golden's `curried._boxed` shape:
    the 3 params (the closure's partial + the 2 fresh) summed. -/
def curriedBoxedFn : Fn :=
  { params := 3
    body := [.localget 1, .localget 2, .i64add, .localget 0, .i64add] }

/-- THE TRAMPOLINE DEMO (the golden's `pap_curried._boxed_1` hop): the
    trampoline's forward = the caller's prep with the partial arg
    DEEPEST (the value `local.get $c; i32.load offset=16` delivers —
    the LOAD is the excluded memory layer, pinned as an explicit
    value) + the fresh args IN ORDER, then the DIRECT call (v1 models
    `call`, not `call_indirect` — the funcref table is the follow-up).
    The hop computes the target's sum of the three delivered args.
    Kernel-checked. -/
theorem trampoline_call_ok (fuel : Nat) (p a b : UInt64) (s : State)
    (hs : s.stack = []) (hf : 2 * 3 + 6 ≤ fuel) :
    ∃ s', execList fuel s
        (pushArgs [.i64 p, .i64 a, .i64 b] ++ (popParams 3 ++ curriedBoxedFn.body))
      = .ok s' ∧ s'.stack = [.i64 (p + (a + b))] := by
  have h := call_split fuel curriedBoxedFn [.i64 p, .i64 a, .i64 b] s rfl hs
    (by have hl : ([.i64 p, .i64 a, .i64 b] : List Val).length = 3 := rfl; omega)
  simp only [List.length_cons, List.length_nil] at h
  simp only [h]
  obtain ⟨m, rfl⟩ : ∃ m', fuel = m' + 12 := ⟨fuel - 12, by omega⟩
  simp only [callExecFuel, curriedBoxedFn, List.length_cons, List.length_nil]
  rw [show m + 12 - 2 * 3 = m + 6 from by omega]
  simp only [bindArgs, dropBottom, hs, List.reverse_nil, List.drop_nil]
  simp only [execList, step, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  refine ⟨_, rfl, ?_⟩
  rw [UInt64.add_comm b a]

/-! ### The type-safety cross-ref -/

/-- THE TYPE-SAFETY CROSS-REF: the composed call program is WELL-TYPED
    (hypothesis — the checker is well-founded-compiled, kernel-opaque;
    the #guards below pin the check), so `typeSafety` applies: the
    call path can NEVER stack-underflow. Correct.lean's convention
    slice, now with the machine on the other end of the theorem. -/
theorem call_exec_safe (a b : UInt64) (s : State)
    (hloc : ∀ n, tyOf (s.locals n) = Ty.i64) (hs : s.stack = [])
    (hcheck : checkStack (fun _ => Ty.i64) []
      (pushArgs [.i64 a, .i64 b] ++ (popParams 2 ++ adderFn.body))
      = .ok [Ty.i64]) :
    exec s (pushArgs [.i64 a, .i64 b] ++ (popParams 2 ++ adderFn.body))
      ≠ .error .underflow := by
  exact (typeSafety (fun _ => Ty.i64) _ [] [Ty.i64] s hcheck
    (by rw [hs]; simp) hloc).1

end Calls

/-! ### The calls layer's tests — build-failing #guards

The wrong-arity TRAP (the big-step API's guard), the short-prep
UNDERFLOW (the flat composed program's surfacing — and the checker's
static rejection of it), and the composed call program's TYPING (the
cross-ref's hypothesis, pinned by the interpreter — see the note at
the type-safety cross-ref).
-/

section CallTests

open Calls

-- 1. THE NEGATIVE CONTROL (arity, big-step API): a 1-arg call to the
--    2-param adder TRAPS — never a silent mis-bind.
#guard (match callExecFuel 100 adderFn [.i64 1] initState with
        | .error .trap => true | _ => false) = true

-- 2. THE NEGATIVE CONTROL (arity, flat program): the short prep
--    UNDERFLOWS in exec — the pop runs off the 1-pushed stack.
#guard (match exec initState
          (pushArgs [.i64 1] ++ (popParams 2 ++ adderFn.body)) with
        | .error .underflow => true | _ => false) = true

-- 3. THE CHECKER CATCHES THE SHORT PREP statically (2 pops, 1 push):
--    the rejection is not vacuous.
#guard (match checkStack (fun _ => Ty.i64) []
          (pushArgs [.i64 1] ++ (popParams 2 ++ adderFn.body)) with
        | .ok _ => false | .error _ => true) = true

-- 4. THE COMPOSED CALL PROGRAM IS WELL-TYPED (the cross-ref's
--    hypothesis): pushes, pops, body — all i64. Interpreter-checked.
#guard (match checkStack (fun _ => Ty.i64) []
          (pushArgs [.i64 1, .i64 2] ++ (popParams 2 ++ adderFn.body)) with
        | .ok [Ty.i64] => true | _ => false) = true

-- 5. THE TRAMPOLINE'S FORWARD IS WELL-TYPED (3 args, i64).
#guard (match checkStack (fun _ => Ty.i64) []
          (pushArgs [.i64 1, .i64 2, .i64 3] ++ (popParams 3
            ++ curriedBoxedFn.body)) with
        | .ok [Ty.i64] => true | _ => false) = true

-- 6. THE BIG-STEP CALL AT THE TOP-LEVEL BUDGET: callExec (the
--    `exec`-fuel API) computes the adder's sum.
#guard (match callExec adderFn [.i64 21, .i64 21]
          ⟨fun _ => .i64 0, [], fun _ => (0 : UInt8), 64⟩ with
        | .ok s' => s'.stack == [.i64 42] | .error _ => false) = true

-- 7. THE TRAMPOLINE HOP, end-to-end at the top-level budget: the
--    partial 2 + the fresh args 20, 20 = 42 (the golden's
--    `pap_curried._boxed_1` → `curried._boxed` values).
#guard (match callExec curriedBoxedFn [.i64 2, .i64 20, .i64 20]
          ⟨fun _ => .i64 0, [], fun _ => (0 : UInt8), 64⟩ with
        | .ok s' => s'.stack == [.i64 42] | .error _ => false) = true

end CallTests

end WasmBackend.Sem
