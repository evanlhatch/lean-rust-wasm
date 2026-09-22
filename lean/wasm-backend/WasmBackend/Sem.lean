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
  unreachable, and a one-byte bounded store AND load (`i32store8` /
  `i32load8u offset` — the load added by the tag-read lane: the
  object-scrutinee's tag byte, zero-extended) as the memory-ops
  representatives.
* NOT MODELED (documented exclusions, not oversights): floats, SIMD,
  threads, tables/call_indirect (the funcref-table dispatch — the
  follow-up; DIRECT calls are modeled since the calls layer: the
  `The calls layer` section, v1 = CALLS as FUNCTION-COMPOSITION, no
  call-frames), integer div/rem (their `trap` is the only missing
  trap),
  multi-value blocks (frames are no-result: a frame body must END at
  the frame's entry type — `checkFrame`), memory beyond one byte per
  access, data segments, globals, static branch-DEPTH validation (a
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

THE LATER LAYERS (this file, below the calls layer): the FRAMES layer
(v2 of calls — the frame MACHINE `Frame`/`pushFrame`/`popFrame`/
`runToReturn`/`callProtocol`, proven to compute the same result as the
big-step composition `call_split` — the machine the emitter's
`call_indirect` protocol assumes; frame separation structural, the
wrong-return-address negative control pinned) and the ALLOCATOR layer
(the EXECUTABLE model that is the SPEC of the spliced `runtime.wat`:
`$alloc` bump+freelist, `$rc_inc`/`$rc_dec` — with the no-alias /
freelist-return / free-exactly-once theorems over `Inv`, induction on
the op list, plus the double-free and use-after-free negative
controls). The allocator model's deltas from the splice are documented
in its section header (one freelist, granular sizes, no OOM path).

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

set_option hygiene false in
set_option hygiene false in
set_option hygiene false in
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
  /-- One-byte zero-extend load at a byte offset from the base
      address on the stack (`i32.load8_u offset=N`: pops the base
      `a`, reads `mem[a + N]`, pushes it zero-extended as i32). -/
  | i32load8u (offset : Nat)
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
  | s, .i32load8u off =>
      -- the tag read (`i32.load8_u offset=N`): pops the base address,
      -- reads the ONE byte at addr + offset, zero-extends to i32.
      -- Out-of-bounds = a RUNTIME trap, never corruption (the store's
      -- `storeInBounds` discipline, mirrored for loads).
      match s.stack with
      | .i32 a :: rest =>
          if a.toNat + off < s.memSize
          then .ok { s with stack := .i32 (s.mem (a.toNat + off)).toUInt32 :: rest }
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

/-! ## The Velvet glue — fuel monotonicity of decided results

The machine is deterministic and fuel only TRUNCATES the trace, so any
result other than `.error .outOfFuel` is upward-fuel-stable: more budget
never changes a decided answer. This is what makes the fuel-insensitive
(“if `execList` returns, it is right”) statements below and in
`WasmBackend.Correct` well-formed: partial correctness quantifies over
ALL fuel, termination is a separate convergence witness, and the two
compose to the old fuel-bounded forms via the monotonicity lemmas. -/

set_option hygiene false in
/-- The XFER: the subrun hypothesis `hb : execList fuel … = r` flows
    through the IH (`hb'` — the SAME run at the successor fuel) into
    `h`. The skeleton of every decided-error arm of `execList_mono`'s
    frame-instruction cases (the `#3` cut: the four-line blocks
    collapsed). `_pos`/`_neg` are the `if_` arms' variants (the stack
    shape and the condition discriminate in the `simp only`s);
    `mono_fuel`/variants discharge the `outOfFuel` arms (no IH
    transfer — the hypothesis IS the contradiction). Hygiene is off so
    the templates resolve the caller's locals (`ih`, `h`, `hle'`, and
    the fixed binder names `hb`/`hstk`/`hb0` every call site uses). -/
local macro "mono_xfer" X:tactic : tactic =>
  `(tactic| (have hb' := ih _ _ _ hb (fun he => by simp at he) _ hle';
             simp only [execList, hb] at h;
             simp only [execList, hb'];
             $X))

set_option hygiene false in
local macro "mono_xfer_pos" X:tactic : tactic =>
  `(tactic| (have hb' := ih _ _ _ hb (fun he => by simp at he) _ hle';
             simp only [execList, hstk, if_pos hb0, hb] at h;
             simp only [execList, hstk, if_pos hb0, hb'];
             $X))

set_option hygiene false in
local macro "mono_xfer_neg" X:tactic : tactic =>
  `(tactic| (have hb' := ih _ _ _ hb (fun he => by simp at he) _ hle';
             simp only [execList, hstk, if_neg hb0, hb] at h;
             simp only [execList, hstk, if_neg hb0, hb'];
             $X))

set_option hygiene false in
local macro "mono_fuel" : tactic =>
  `(tactic| (simp only [execList, hb] at h; exact absurd h.symm hr))

set_option hygiene false in
local macro "mono_fuel_pos" : tactic =>
  `(tactic| (simp only [execList, hstk, if_pos hb0, hb] at h; exact absurd h.symm hr))

set_option hygiene false in
local macro "mono_fuel_neg" : tactic =>
  `(tactic| (simp only [execList, hstk, if_neg hb0, hb] at h; exact absurd h.symm hr))

/-- THE MONOTONICITY LEMMA: any decided result — `.ok`, `trap`,
    `underflow`, `structural`, or a `branch` signal — is stable under
    extra fuel (only `outOfFuel` can flip, to the decided result the
    budget was starving). Induction on the fuel; every recursive call of
    `execList` happens at the predecessor, so the IH (generalized over
    the state, the program, and the result) covers the loop-restart
    re-entry too. -/
theorem execList_mono :
    ∀ (fuel : Nat) (s : State) (p : List Instr) (r : Except Err State),
      execList fuel s p = r → r ≠ .error .outOfFuel →
      ∀ (fuel' : Nat), fuel ≤ fuel' → execList fuel' s p = r := by
  intro fuel
  induction fuel with
  | zero =>
    intro s p r h hr
    simp only [execList] at h
    exact absurd h.symm hr
  | succ fuel ih =>
    intro s p r h hr fuel' hle
    obtain ⟨f', rfl⟩ : ∃ g, fuel' = g + 1 := ⟨fuel' - 1, by omega⟩
    have hle' : fuel ≤ f' := by omega
    cases p with
    | nil =>
      simp only [execList] at h ⊢
      exact h
    | cons i is =>
      -- case on the flat step FIRST: for the frame instrs `step` is
      -- `.structural` (contradicting the `ok` branch, unused in the
      -- `error` branch); for the 13 flat instrs the last `execList`
      -- arm is `step` then the tail, one fuel unit for the step.
      cases hst : step s i with
      | ok s1 =>
        cases i with
        | block body => simp [step] at hst
        | loop body => simp [step] at hst
        | if_ t e => simp [step] at hst
        | _ =>
          simp only [execList, hst] at h
          simp only [execList, hst]
          exact ih _ _ _ h hr _ hle'
      | error e =>
        cases i with
        | block body =>
          cases hb : execList fuel s body with
          | ok s1 => mono_xfer (exact ih _ _ _ h hr _ hle')
          | error e1 =>
            cases e1 with
            | branch n ls =>
              cases n with
              | zero => mono_xfer (exact ih _ _ _ h hr _ hle')
              | succ n' => mono_xfer (exact h)
            | outOfFuel => mono_fuel
            | trap => mono_xfer (exact h)
            | underflow => mono_xfer (exact h)
            | structural => mono_xfer (exact h)
        | loop body =>
          cases hb : execList fuel s body with
          | ok s1 => mono_xfer (exact ih _ _ _ h hr _ hle')
          | error e1 =>
            cases e1 with
            | branch n ls =>
              cases n with
              | zero => mono_xfer (exact ih _ _ _ h hr _ hle')
              | succ n' => mono_xfer (exact h)
            | outOfFuel => mono_fuel
            | trap => mono_xfer (exact h)
            | underflow => mono_xfer (exact h)
            | structural => mono_xfer (exact h)
        | if_ t e =>
          cases hstk : s.stack with
          | nil =>
            simp only [execList, hstk] at h ⊢
            exact h
          | cons v vs =>
            cases v with
            | i64 n =>
              simp only [execList, hstk] at h ⊢
              exact h
            | i32 b =>
              by_cases hb0 : b != 0
              . cases hb : execList fuel { s with stack := vs } t with
                | ok s1 => mono_xfer_pos (exact ih _ _ _ h hr _ hle')
                | error e1 =>
                  cases e1 with
                  | branch n ls =>
                    cases n with
                    | zero => mono_xfer_pos (exact ih _ _ _ h hr _ hle')
                    | succ n' => mono_xfer_pos (exact h)
                  | outOfFuel => mono_fuel_pos
                  | trap => mono_xfer_pos (exact h)
                  | underflow => mono_xfer_pos (exact h)
                  | structural => mono_xfer_pos (exact h)
              . cases hb : execList fuel { s with stack := vs } e with
                | ok s1 => mono_xfer_neg (exact ih _ _ _ h hr _ hle')
                | error e1 =>
                  cases e1 with
                  | branch n ls =>
                    cases n with
                    | zero => mono_xfer_neg (exact ih _ _ _ h hr _ hle')
                    | succ n' => mono_xfer_neg (exact h)
                  | outOfFuel => mono_fuel_neg
                  | trap => mono_xfer_neg (exact h)
                  | underflow => mono_xfer_neg (exact h)
                  | structural => mono_xfer_neg (exact h)
        | _ =>
          simp only [execList, hst] at h ⊢
          exact h


/-- The `.ok` specialization: a completed run's answer is stable under
    extra fuel. -/
theorem execList_ok_mono {fuel fuel' : Nat} {s s' : State} {p : List Instr}
    (h : execList fuel s p = .ok s') (hle : fuel ≤ fuel') :
    execList fuel' s p = .ok s' :=
  execList_mono fuel s p (.ok s') h (fun he => by simp at he) fuel' hle

/-- The `.error` specialization: a DECIDED error (anything but
    `outOfFuel`) is stable under extra fuel. -/
theorem execList_error_mono {fuel fuel' : Nat} {s : State} {p : List Instr}
    {e : Err} (h : execList fuel s p = .error e) (hne : e ≠ .outOfFuel)
    (hle : fuel ≤ fuel') :
    execList fuel' s p = .error e :=
  execList_mono fuel s p (.error e) h (fun he => absurd (Except.error.inj he) hne)
    fuel' hle

/-- THE VELVET TRANSPORT (result uniqueness): two completed runs of the
    same program from the same state — at ANY two budgets — agree. This
    is what discharges the partial-correctness reshapes: one convergence
    witness pins the answer at every fuel. -/
theorem execList_ok_unique {f1 f2 : Nat} {s s1 s2 : State} {p : List Instr}
    (h1 : execList f1 s p = .ok s1) (h2 : execList f2 s p = .ok s2) :
    s1 = s2 := by
  cases Nat.le_total f1 f2 with
  | inl hle =>
    have h2' := execList_ok_mono h1 hle
    rw [h2'] at h2
    injection h2
  | inr hle =>
    have h1' := execList_ok_mono h2 hle
    rw [h1'] at h1
    injection h1 with h1''
    exact h1''.symm

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
  | base, .i32load8u _ :: is =>
      match base with
      | .i32 :: ts => checkStack locals (.i32 :: ts) is
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

/-- The error-tail discharge: the `trap`/`outOfFuel`/`structural` arms
    of `exec_typed`'s triples. A non-underflow, non-branch error is
    OBSERVABLE — the underflow exclusion, the ok-preservation (vacuous on
    an error), and the branch-locals preservation all hold trivially.
    One definition, the ~12 repeated four-line triples deleted. -/
local macro "err_tail" : tactic =>
  `(tactic| exact ⟨fun h => (nomatch h), fun s' h => (nomatch h), fun n' ls' hEq => (nomatch hEq)⟩)

set_option hygiene false in
/-- The TWO-OPERAND skeleton (the #3 cut's biggest per-case win: the
    `i32add`/`i32eq`/`i64add` arms — pop two `V` scalars, push one; the
    arms differ only in the pushed VALUE). The base/stack shape is
    destructured with the WRONG ty (`W`) `simp`-refuted at each level;
    the check's tail re-derives (`hcheck'`) and the surviving-tail type
    (`hts`) is extracted; the IH applies to the pushed-value state.
    `pushT`/`pushV` are the result-type / stack terms — they capture the
    template's `a`, `b`, `ts2`, `vs2` binders (hygiene off). NOTE: a
    `by` inside a tactic-paren quote swallows the rest of the group, so
    every by-block sits alone in its own paren group. -/
local macro "two_operand" W:ident V:ident pushT:term "," pushV:term : tactic =>
  `(tactic| (cases base with
             | nil => simp [checkStack] at hcheck
             | cons t1 ts1 =>
               cases t1 with
               | $W => simp [checkStack] at hcheck
               | _ =>
                 cases ts1 with
                 | nil => simp [checkStack] at hcheck
                 | cons t2 ts2 =>
                   cases t2 with
                   | $W => simp [checkStack] at hcheck
                   | _ =>
                     cases stk with
                     | nil => simp [stackTys] at hstack
                     | cons v1 vs1 =>
                       cases v1 with
                       | $W _ => simp [stackTys] at hstack
                       | $V a =>
                         cases vs1 with
                         | nil => simp [stackTys] at hstack
                         | cons v2 vs2 =>
                           cases v2 with
                           | $W _ => simp [stackTys] at hstack
                           | $V b =>
                             ((have hcheck' : checkStack locals $pushT is = .ok final := by
                                 (simp only [checkStack] at hcheck; exact hcheck));
                              (have hts : stackTys vs2 = ts2 := by
                                 (simp [stackTys] at hstack; exact hstack));
                              simp only [execList, step];
                              exact ih.1 is $pushT final
                                ⟨loc, $pushV, mem, msz⟩
                                hcheck' (by simp [stackTys, hts]) hloc')))

set_option hygiene false in
/-- The SUBRUN case tree (the `block`/`loop` arms + part 2's shared
    skeleton): case on the body/subrun result; the `.ok` arm and the
    `.branch 0` arm are the caller's (they re-enter the IH for the tail
    and differ per frame shape); `underflow` contradicts the body's
    non-underflow clause; the three observable errors are `err_tail`;
    `.branch (n+1)` propagates the branch signal with the locals
    clause. -/
local macro "sub_case" hin:ident stE:term "," okTac:tactic zeroTac:tactic : tactic =>
  `(tactic| (cases hx : execList fuel $stE body with
             | ok s'' => (simp only [execList, hx]; $okTac)
             | error e =>
               cases e with
               | underflow => (simp only [execList, hx]; exact absurd hx ($hin).1)
               | trap => (simp only [execList, hx]; err_tail)
               | outOfFuel => (simp only [execList, hx]; err_tail)
               | structural => (simp only [execList, hx]; err_tail)
               | branch k ls =>
                 cases k with
                 | zero => (simp only [execList, hx]; $zeroTac)
                 | succ k' =>
                   (simp only [execList, hx];
                    refine ⟨fun h => by simp at h, fun s' h => by simp at h, fun n' ls' hEq => ?_⟩;
                    injection hEq with hI;
                    injection hI with _ hls;
                    subst hls;
                    exact ($hin).2.2 (k'+1) ls hx)))

set_option hygiene false in
/-- The SUBRUN case tree, `if_` variant: the guard's `simp only
    [execList, if_pos/if_neg cond]` (the `pre` param) precedes the case,
    and the ok arm's goal is then already reduced — no further simp
    (which would make no progress); otherwise identical to `sub_case`. -/
local macro "sub_case_if" hin:ident stE:term "," il:term "," pre:tactic okTac:tactic zeroTac:tactic : tactic =>
  `(tactic| ($pre;
             cases hx : execList fuel $stE $il with
             | ok s'' => (skip; $okTac)
             | error e =>
               cases e with
               | underflow => (simp only [execList, hx]; exact absurd hx ($hin).1)
               | trap => (simp only [execList, hx]; err_tail)
               | outOfFuel => (simp only [execList, hx]; err_tail)
               | structural => (simp only [execList, hx]; err_tail)
               | branch k ls =>
                 cases k with
                 | zero => (simp only [execList, hx]; $zeroTac)
                 | succ k' =>
                   (simp only [execList, hx];
                    refine ⟨fun h => by simp at h, fun s' h => by simp at h, fun n' ls' hEq => ?_⟩;
                    injection hEq with hI;
                    injection hI with _ hls;
                    subst hls;
                    exact ($hin).2.2 (k'+1) ls hx)))

/-- The shared frame-check case body for the `block`/`loop` arms:
    `checkStack`'s `.block` and `.loop` clauses both reduce to this
    `checkFrame`-match shape, so one proof covers both. The `.block`/
    `.loop` theorem statements are NOT defeq (distinct `Instr` ctors
    stuck under `checkStack`), so `block_checkStack_inv` /
    `loop_checkStack_inv` remain as thin entry lemmas. -/
private theorem frame_checkStack_inv_general (locals : Nat → Ty) (body is : List Instr)
    (base final : List Ty)
    (hcheck : (match checkFrame locals base body with
               | .ok _ => checkStack locals base is
               | .error e => .error e) = .ok final) :
    checkFrame locals base body = .ok () ∧ checkStack locals base is = .ok final := by
  cases hf : checkFrame locals base body with
  | error _ => rw [hf] at hcheck; simp at hcheck
  | ok _ =>
      rw [hf] at hcheck; simp at hcheck
      exact ⟨rfl, hcheck⟩

/-- The frame-check FACTORIZATION (the `block`/`loop` arms' shared
    head, lifted to a lemma so the `sub_case` macros carry no `by`): the
    case check implies the frame check holds and the tail is checked
    from `base`. -/
theorem block_checkStack_inv (locals : Nat → Ty) (body is : List Instr)
    (base final : List Ty)
    (hcheck : checkStack locals base (.block body :: is) = .ok final) :
    checkFrame locals base body = .ok () ∧ checkStack locals base is = .ok final := by
  simp only [checkStack] at hcheck
  exact frame_checkStack_inv_general locals body is base final hcheck

/-- The `.loop` mirror of `block_checkStack_inv` (the restart form). -/
theorem loop_checkStack_inv (locals : Nat → Ty) (body is : List Instr)
    (base final : List Ty)
    (hcheck : checkStack locals base (.loop body :: is) = .ok final) :
    checkFrame locals base body = .ok () ∧ checkStack locals base is = .ok final := by
  simp only [checkStack] at hcheck
  exact frame_checkStack_inv_general locals body is base final hcheck

/-- THE core lemma. Part 2 additionally assumes the tail `is` is checked
    `base → final` (the restart re-enters at `.loop body :: is`). The
    per-arm proofs are the `#3` cut's skeletons: `two_operand` (the
    pop-two-push-one arithmetic/compare arms), `frame_prelude` +
    `sub_case` (the block/loop arms and part 2), `sub_case_if` (the
    `if_` arms), `err_tail` (the observable-error triples). The
    genuinely divergent arms stay hand-written: `localset` (the locals
    update's pointwise proof), `drop`/`brif`/`i32load8u` (pop-ONE
    shapes, each with its own discrimination), `i32store8` (pop-two
    with NO push plus the bounds `by_cases`), and the short
    `i32const`/`i64const`/`localget` pushes. -/
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
        | i32add => two_operand i64 i32 (.i32 :: ts2), (.i32 (a + b) :: vs2)
        | i32eq => two_operand i64 i32 (.i32 :: ts2), (.i32 (if a == b then 1 else 0) :: vs2)
        | i64add => two_operand i32 i64 (.i64 :: ts2), (.i64 (a + b) :: vs2)
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
          have hfr := block_checkStack_inv locals body is base final hcheck
          have hin := ih.1 body base base ⟨loc, stk, mem, msz⟩
            (checkFrame_ok locals base body hfr.1) hstack hloc
          sub_case hin ⟨loc, stk, mem, msz⟩,
            (exact ih.1 is base final s'' hfr.2 (hin.2.1 s'' hx).1 (hin.2.1 s'' hx).2)
            (exact ih.1 is base final ⟨ls, stk, mem, msz⟩ hfr.2
              (by simp [stackTys, hstack]) (fun m => hin.2.2 0 ls hx m))
        | loop body =>
          have hfr := loop_checkStack_inv locals body is base final hcheck
          have hin := ih.1 body base base ⟨loc, stk, mem, msz⟩
            (checkFrame_ok locals base body hfr.1) hstack hloc
          sub_case hin ⟨loc, stk, mem, msz⟩,
            (exact ih.1 is base final s'' hfr.2 (hin.2.1 s'' hx).1 (hin.2.1 s'' hx).2)
            (exact ih.2 is body base final ⟨ls, stk, mem, msz⟩ hfr.1 hfr.2
              (by simp [stackTys, hstack]) (fun m => hin.2.2 0 ls hx m))
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
                  . sub_case_if hthen ⟨loc, vs, mem, msz⟩, t, (simp only [execList, if_pos hb])
                      (exact ih.1 is ts1 final s'' hcks.1 (hthen.2.1 s'' hx).1
                        (hthen.2.1 s'' hx).2)
                      (exact ih.1 is ts1 final ⟨ls, vs, mem, msz⟩ hcks.1 hts
                        (fun m => hthen.2.2 0 ls hx m))
                  . sub_case_if helse ⟨loc, vs, mem, msz⟩, e, (simp only [execList, if_neg hb])
                      (exact ih.1 is ts1 final s'' hcks.1 (helse.2.1 s'' hx).1
                        (helse.2.1 s'' hx).2)
                      (exact ih.1 is ts1 final ⟨ls, vs, mem, msz⟩ hcks.1 hts
                        (fun m => helse.2.2 0 ls hx m))
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
                            err_tail
        | i32load8u off =>
          -- mirror of i32store8 with ONE popped operand; net-zero (pop i32, push i32); VALUE irrelevant for typing.
          cases base with
          | nil => simp [checkStack] at hcheck
          | cons t1 ts1 =>
            cases t1 with
            | i64 => simp [checkStack] at hcheck
            | i32 =>
              have hcheck' : checkStack locals (.i32 :: ts1) is = .ok final := by
                simp only [checkStack] at hcheck; exact hcheck
              cases stk with
              | nil => simp [stackTys] at hstack
              | cons v1 vs1 =>
                cases v1 with
                | i64 _ => simp [stackTys] at hstack
                | i32 a =>
                  have hts : stackTys vs1 = ts1 := by
                    simp [stackTys] at hstack
                    exact hstack
                  by_cases hlt : a.toNat + off < msz
                  . simp only [execList, step, if_pos hlt]
                    exact ih.1 is (.i32 :: ts1) final
                      ⟨loc, .i32 (mem (a.toNat + off)).toUInt32 :: vs1, mem, msz⟩
                      hcheck' (by simp [stackTys, hts]) hloc'
                  . simp only [execList, step, if_neg hlt]
                    err_tail
    . intro is body base final s hfr hcheck hstack hloc
      obtain ⟨loc, stk, mem, msz⟩ := s
      have hloc' : ∀ m, tyOf (loc m) = locals m := fun m => hloc m
      have hcheck' := checkFrame_ok locals base body hfr
      have hin := ih.1 body base base ⟨loc, stk, mem, msz⟩ hcheck' hstack hloc
      sub_case hin ⟨loc, stk, mem, msz⟩,
        (exact ih.1 is base final s'' hcheck (hin.2.1 s'' hx).1 (hin.2.1 s'' hx).2)
        (exact ih.2 is body base final ⟨ls, stk, mem, msz⟩ hfr hcheck
          (by simp [stackTys, hstack]) (fun m => hin.2.2 0 ls hx m))


/-- THE deliverable theorem, FUEL-INSENSITIVE (the Velvet primary —
    W6.9): at ANY budget, a well-typed program (checked against its
    declared type) NEVER raises the stack-underflow error; and IF it
    completes normally at that budget, the final stack is statically
    `final` with the locals well-formedness preserved (preservation).
    No fuel lower bound: at budget 0 the machine returns `outOfFuel`,
    which is not `underflow`, and the `.ok` clause is vacuous —
    `exec_typed` already quantifies over all fuel. Termination (enough
    fuel exists) is a SEPARATE question; this is partial correctness. -/
theorem typeSafetyList (locals : Nat → Ty) (body : List Instr) (base final : List Ty)
    (s : State) (fuel : Nat)
    (hcheck : checkStack locals base body = .ok final)
    (hstack : stackTys s.stack = base)
    (hloc : ∀ n, tyOf (s.locals n) = locals n) :
    execList fuel s body ≠ .error .underflow
    ∧ (∀ s', execList fuel s body = .ok s' →
          stackTys s'.stack = final ∧ (∀ n, tyOf (s'.locals n) = locals n)) :=
  ⟨(exec_typed locals fuel).1 body base final s hcheck hstack hloc |>.1,
   ((exec_typed locals fuel).1 body base final s hcheck hstack hloc).2.1⟩

/-- THE deliverable theorem at the top-level budget: a well-typed
    program NEVER raises the stack-underflow error; and if it completes
    normally, the final stack is statically `final` with the locals
    well-formedness preserved (preservation). Thin corollary of the
    fuel-insensitive `typeSafetyList` at `defaultFuel`. -/
theorem typeSafety (locals : Nat → Ty) (body : List Instr) (base final : List Ty)
    (s : State)
    (hcheck : checkStack locals base body = .ok final)
    (hstack : stackTys s.stack = base)
    (hloc : ∀ n, tyOf (s.locals n) = locals n) :
    exec s body ≠ .error .underflow
    ∧ (∀ s', exec s body = .ok s' →
          stackTys s'.stack = final ∧ (∀ n, tyOf (s'.locals n) = locals n)) :=
  typeSafetyList locals body base final s defaultFuel hcheck hstack hloc

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

-- 12. LOAD: `i32load8u 0` reads back the stored byte, zero-extended.
def progLoad : List Instr := [.i32const 3, .i32const 7, .i32store8,
                             .i32const 3, .i32load8u 0]
#guard (match checkStack localsI32 [] progLoad with
        | .ok [Ty.i32] => true | _ => false) = true
#guard (match finalStack initState progLoad with
        | .ok [.i32 7] => true | _ => false) = true

-- 13. LOAD at an offset: base 8 + offset 4 = address 12 — the
--     `i32.load8_u offset=4` shape the emitter's tag read uses.
def progLoadOff : List Instr := [.i32const 12, .i32const 7, .i32store8,
                                 .i32const 8, .i32load8u 4]
#guard (match finalStack initState progLoadOff with
        | .ok [.i32 7] => true | _ => false) = true

-- 14. NEGATIVE CONTROL (typing): a load on an empty stack (no base
--     address) is REJECTED by the checker.
#guard (match checkStack localsI32 [] [.i32load8u 0] with
        | .ok _ => false | .error _ => true) = true

-- 15. NEGATIVE CONTROL (memory): an out-of-bounds load TRAPS and
--     never reads — the store's OOB discipline, mirrored.
#guard (match exec initState [.i32const 100, .i32load8u 0] with
        | .error .trap => true | _ => false) = true

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
    `getD_append`; checked the 4.33 toolchain's Init/Data/List lemmas). -/
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
    deepest), one fuel unit per arg. UNCONDITIONAL in the fuel (W6.9):
    an underfueled push phase exhausts mid-list = `outOfFuel`, which is
    exactly `execList (fuel - args.length)` at a zeroed budget — the
    equation absorbs the starvation. -/
theorem pushArgs_exec (args : List Val) :
    ∀ (fuel : Nat) (rest : List Instr) (s : State),
      execList fuel s (pushArgs args ++ rest)
        = execList (fuel - args.length)
            { s with stack := args.reverse ++ s.stack } rest := by
  induction args with
  | nil =>
    intro fuel rest s
    cases fuel with
    | zero => simp [execList]
    | succ n => simp [pushArgs, execList]
  | cons a as ih =>
    intro fuel rest s
    cases fuel with
    | zero => simp [execList]
    | succ n =>
      simp only [pushArgs, List.cons_append, execList, List.length_cons]
      cases a with
      | i32 c =>
        simp only [step, constOf, List.reverse_cons, List.append_assoc]
        rw [show n + 1 - (as.length + 1) = n - as.length from by omega]
        exact ih n rest { s with stack := .i32 c :: s.stack }
      | i64 c =>
        simp only [step, constOf, List.reverse_cons, List.append_assoc]
        rw [show n + 1 - (as.length + 1) = n - as.length from by omega]
        exact ih n rest { s with stack := .i64 c :: s.stack }

/-- The pop phase (stated over the args' STACK IMAGE `rs` — head =
    top): `popParams rs.length ++ rest` executes as `rest` from the
    state with the args bound to the param locals (`rs.reverse` = the
    args in push order) and the stack drained to `bot`, one fuel unit
    per pop. This is Correct.lean's convention contract as a program
    EQUALITY. UNCONDITIONAL in the fuel (W6.9 — same `outOfFuel`
    absorption as `pushArgs_exec`). -/
theorem popParams_exec (rs : List Val) :
    ∀ (fuel : Nat) (rest : List Instr) (bot : List Val) (s : State),
      s.stack = rs ++ bot →
      execList fuel s (popParams rs.length ++ rest)
        = execList (fuel - rs.length)
            { s with locals := fun n => rs.reverse.getD n (s.locals n)
                   , stack := bot } rest := by
  induction rs with
  | nil =>
    intro fuel rest bot s hs
    cases fuel with
    | zero => simp [execList]
    | succ n =>
      rw [List.nil_append] at hs
      subst hs
      have hloc : (fun m => ([] : List Val).reverse.getD m (s.locals m))
          = s.locals := by funext m; simp
      simp [popParams, execList, hloc]
  | cons r rs ih =>
    intro fuel rest bot s hs
    cases fuel with
    | zero => simp [execList]
    | succ n =>
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
                , stack := rs ++ bot } rfl
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
    about two lists. UNCONDITIONAL in the fuel (W6.9): an underfueled
    prep exhausts = `outOfFuel` = `callExecFuel` at a zeroed budget. -/
theorem call_split (fuel : Nat) (f : Fn) (args : List Val) (s : State)
    (harity : args.length = f.params) (hs : s.stack = []) :
    execList fuel s (pushArgs args ++ (popParams args.length ++ f.body))
      = callExecFuel (fuel - 2 * args.length) f args s := by
  have h1 := pushArgs_exec args fuel (popParams args.length ++ f.body) s
  rw [h1]
  simp only [hs, List.append_nil]
  have h2 := popParams_exec args.reverse (fuel - args.length) f.body []
    { s with stack := args.reverse }
    (by simp [List.append_nil])
  simp only [List.length_reverse] at h2
  rw [h2]
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

/-- THE CALL-EXECUTION THEOREM, the TERMINATION leg (W6.9): at any
    budget ≥ 8 the composed call program RETURNS — the caller's prep
    (the args' pushes), the call's binding (the pops), and the callee's
    body compose to compute the CALLEE's result on the caller's stack.
    Symbolic args, arbitrary initial state, kernel-checked. -/
theorem call_exec_correct_converges (a b : UInt64) (s : State)
    (hs : s.stack = []) :
    ∀ m, ∃ s', execList (m + 8) s
        (pushArgs [.i64 a, .i64 b] ++ (popParams 2 ++ adderFn.body))
      = .ok s' ∧ s'.stack = [.i64 (a + b)] := by
  intro m
  have h := call_split (m + 8) adderFn [.i64 a, .i64 b] s rfl hs
  simp only [List.length_cons, List.length_nil] at h
  simp only [h]
  simp only [callExecFuel, adderFn, List.length_cons, List.length_nil]
  rw [show m + 8 - 2 * 2 = m + 4 from by omega]
  simp only [bindArgs, dropBottom, hs, List.reverse_nil, List.drop_nil,
    List.reverse_reverse]
  simp only [execList, step, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  refine ⟨_, rfl, ?_⟩
  rw [UInt64.add_comm]

/-- THE CALL-EXECUTION THEOREM, PARTIAL CORRECTNESS (the primary,
    fuel-insensitive statement — W6.9): IF the composed call program
    returns a state at ANY budget, the stack IS the callee-computed
    sum — the args go IN, the sum comes OUT. No fuel hypothesis: an
    underfueled run returns `outOfFuel`, not a wrong state (the
    `execList_ok_unique` transport against the convergence witness). -/
theorem call_exec_correct (a b : UInt64) (s : State)
    (hs : s.stack = []) (fuel : Nat) (s' : State)
    (h : execList fuel s
        (pushArgs [.i64 a, .i64 b] ++ (popParams 2 ++ adderFn.body))
      = .ok s') :
    s'.stack = [.i64 (a + b)] := by
  obtain ⟨s8, h8, hs8⟩ := call_exec_correct_converges a b s hs 0
  cases execList_ok_unique h8 h
  exact hs8

/-- The first-param callee (returns param 0 — exposes the binding;
    the negative control's target). -/
def head0Fn : Fn := { params := 2, body := [.localget 0] }

/-- The convention's POSITIVE pin, the TERMINATION leg (W6.9): at any
    budget ≥ 6 the correctly-ordered prep returns with param 0 = the
    FIRST arg — the mirror of `call_prep_swapped_converges`. -/
theorem call_prep_ok_converges (a b : UInt64) (s : State)
    (hs : s.stack = []) :
    ∀ m, ∃ s', execList (m + 6) s
        (pushArgs [.i64 a, .i64 b] ++ (popParams 2 ++ head0Fn.body))
      = .ok s' ∧ s'.stack = [.i64 a] := by
  intro m
  have h := call_split (m + 6) head0Fn [.i64 a, .i64 b] s rfl hs
  simp only [List.length_cons, List.length_nil] at h
  simp only [h]
  simp only [callExecFuel, head0Fn, List.length_cons, List.length_nil]
  rw [show m + 6 - 2 * 2 = m + 2 from by omega]
  simp only [bindArgs, dropBottom, hs, List.reverse_nil, List.drop_nil,
    List.reverse_reverse]
  simp only [execList, step, List.getD, List.getElem?_cons_zero,
    Option.getD_some]
  exact ⟨_, rfl, rfl⟩

/-- The convention's POSITIVE pin, PARTIAL CORRECTNESS (primary,
    fuel-insensitive — W6.9): IF the correctly-ordered prep program
    returns at ANY budget, param 0 got the FIRST arg. -/
theorem call_prep_ok (a b : UInt64) (s : State)
    (hs : s.stack = []) (fuel : Nat) (s' : State)
    (h : execList fuel s
        (pushArgs [.i64 a, .i64 b] ++ (popParams 2 ++ head0Fn.body))
      = .ok s') :
    s'.stack = [.i64 a] := by
  obtain ⟨s6, h6, hs6⟩ := call_prep_ok_converges a b s hs 0
  cases execList_ok_unique h6 h
  exact hs6

/-- THE NEGATIVE CONTROL (the arg-order swap — the calling-convention
    bug class, now at the MACHINE level): pushing the args in REVERSE
    order binds param 0 = the LAST arg, and the callee computes on the
    swapped binding. Same input state, different result — the
    checker cannot see it (shape-only); the disagreement is a theorem
    (`call_prep_swapped_disagrees`). The TERMINATION leg (W6.9). -/
theorem call_prep_swapped_converges (a b : UInt64) (s : State)
    (hs : s.stack = []) :
    ∀ m, ∃ s', execList (m + 6) s
        (pushArgs [.i64 b, .i64 a] ++ (popParams 2 ++ head0Fn.body))
      = .ok s' ∧ s'.stack = [.i64 b] := by
  intro m
  have h := call_split (m + 6) head0Fn [.i64 b, .i64 a] s rfl hs
  simp only [List.length_cons, List.length_nil] at h
  simp only [h]
  simp only [callExecFuel, head0Fn, List.length_cons, List.length_nil]
  rw [show m + 6 - 2 * 2 = m + 2 from by omega]
  simp only [bindArgs, dropBottom, hs, List.reverse_nil, List.drop_nil,
    List.reverse_reverse]
  simp only [execList, step, List.getD, List.getElem?_cons_zero,
    Option.getD_some]
  exact ⟨_, rfl, rfl⟩

/-- THE NEGATIVE CONTROL, PARTIAL CORRECTNESS (primary, fuel-insensitive
    — W6.9): IF the swapped prep returns at ANY budget, param 0 got the
    LAST arg. -/
theorem call_prep_swapped (a b : UInt64) (s : State)
    (hs : s.stack = []) (fuel : Nat) (s' : State)
    (h : execList fuel s
        (pushArgs [.i64 b, .i64 a] ++ (popParams 2 ++ head0Fn.body))
      = .ok s') :
    s'.stack = [.i64 b] := by
  obtain ⟨s6, h6, hs6⟩ := call_prep_swapped_converges a b s hs 0
  cases execList_ok_unique h6 h
  exact hs6

/-- THE NEGATIVE INSTANCE (fuel-insensitive — W6.9): the swapped prep
    DISAGREES with the convention at ANY pair of budgets — whenever
    BOTH return, the result stacks differ. If a regression re-swapped
    the arg pushes, this theorem's shape is what the differential
    duel's sabotage control checks empirically. (The old same-fuel
    match-form at `fuel ≥ 11` is recovered via the `_converges` legs.) -/
theorem call_prep_swapped_disagrees (a b : UInt64) (s : State)
    (hs : s.stack = []) (hAB : a ≠ b) (f1 f2 : Nat) (s1 s2 : State)
    (h1 : execList f1 s
        (pushArgs [.i64 a, .i64 b] ++ (popParams 2 ++ head0Fn.body))
      = .ok s1)
    (h2 : execList f2 s
        (pushArgs [.i64 b, .i64 a] ++ (popParams 2 ++ head0Fn.body))
      = .ok s2) :
    s1.stack ≠ s2.stack := by
  have h1s := call_prep_ok a b s hs f1 s1 h1
  have h2s := call_prep_swapped a b s hs f2 s2 h2
  intro hEq
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
    The TERMINATION leg (W6.9): at any budget ≥ 12 the hop returns.
    Kernel-checked. -/
theorem trampoline_call_ok_converges (p a b : UInt64) (s : State)
    (hs : s.stack = []) :
    ∀ m, ∃ s', execList (m + 12) s
        (pushArgs [.i64 p, .i64 a, .i64 b] ++ (popParams 3 ++ curriedBoxedFn.body))
      = .ok s' ∧ s'.stack = [.i64 (p + (a + b))] := by
  intro m
  have h := call_split (m + 12) curriedBoxedFn [.i64 p, .i64 a, .i64 b] s rfl hs
  simp only [List.length_cons, List.length_nil] at h
  simp only [h]
  simp only [callExecFuel, curriedBoxedFn, List.length_cons, List.length_nil]
  rw [show m + 12 - 2 * 3 = m + 6 from by omega]
  simp only [bindArgs, dropBottom, hs, List.reverse_nil, List.drop_nil]
  simp only [execList, step, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  refine ⟨_, rfl, ?_⟩
  rw [UInt64.add_comm b a]

/-- THE TRAMPOLINE DEMO, PARTIAL CORRECTNESS (primary, fuel-insensitive
    — W6.9): IF the hop's program returns at ANY budget, the stack IS
    the target's sum of the three delivered args. -/
theorem trampoline_call_ok (p a b : UInt64) (s : State)
    (hs : s.stack = []) (fuel : Nat) (s' : State)
    (h : execList fuel s
        (pushArgs [.i64 p, .i64 a, .i64 b] ++ (popParams 3 ++ curriedBoxedFn.body))
      = .ok s') :
    s'.stack = [.i64 (p + (a + b))] := by
  obtain ⟨s12, h12, hs12⟩ := trampoline_call_ok_converges p a b s hs 0
  cases execList_ok_unique h12 h
  exact hs12

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

/-! ## The frames layer (v2) — the call MACHINE over call frames

THE SCOPE DECISION (the FRAMES lane): the calls layer above is v1 —
CALLS AS FUNCTION-COMPOSITION (`call_split`): no frames, the callee's
params bound into the caller's locals-map (the pairwise-distinctness
hypotheses were the frame separation's stand-in). This section lifts
the model to FRAMES: a call FREEZES the caller — its locals, its
operand stack (args popped), and its remaining code (the return
address, `retTo`) — into a `Frame`; the callee runs in its own frame;
the return pops and hands the result to the restored caller.

THE FRAME THEOREM (`callProtocol_agrees` + the composition corollary
`callProtocol_is_call_split`): the machine's call protocol — the
caller's flat prep, `pushFrame`, `runToReturn`, the pop — computes the
SAME result as the big-step composition (`callExecFuel` / `call_split`):
the callee's run inside the machine IS the big-step's sub-exec (same
`bindArgs` state, same body, same fuel). The machine the emitter's
`call_indirect` protocol assumes IS the composition semantics. Frame
separation is now STRUCTURAL (`frame_demo_separation`): the caller's
locals survive the call even where the callee's params overlap them.

HONEST LIMITS: DIRECT calls only (no funcref table — the model is the
PROTOCOL the `call_indirect` dispatch drives); one result value per
frame (the fragment's return convention — a frame returning NO value
halts the machine at `popFrame`'s `none`); the calls are the DRIVER
API (`pushFrame`), not `Instr`s — an `Instr.call` would break the
statement-frozen `checkStack`/`exec_typed` exhaustiveness; the
agreement theorems are pinned on the NON-RECURSIVE fragment (one call
per protocol run — `runToReturn` itself is frame-stack-general). The
protocol's caller contract: the args already pushed, stack EXACTLY
`args.reverse` (the emitter's calls happen with an empty operand
stack — everything lives in locals). Fuel artifact: every phase entry
and every pop consumes one unit, so the protocol runs at the
composition's sub-exec budget + 1.
-/

namespace Calls

/-- One call frame: the FROZEN caller. On the pop the machine restores
    exactly these three things — the frame separation IS this record. -/
structure Frame where
  /-- The caller's locals (the callee's param bindings live in its OWN
      frame, never here). -/
  locals : Nat → Val
  /-- The caller's remaining code — the RETURN ADDRESS (what the
      machine resumes at the pop). -/
  retTo : List Instr
  /-- The caller's operand stack at the call, args popped (the result
      is pushed on top at the pop). -/
  retStack : List Val

/-- The machine state: the frame stack, the CURRENT frame's `State`
    (its locals + operand stack; the MEMORY is shared — it lives in
    `cur` and flows forward through the pops, the callee's stores
    persist), and the current frame's remaining code. -/
structure Mach where
  frames : List Frame
  cur : State
  code : List Instr

/-- The machine's flat phase: run the current code to exhaustion (the
    frame's return point). One fuel unit per instruction (`execList`'s
    budget). -/
def mRun (fuel : Nat) (m : Mach) : Except Err Mach :=
  match execList fuel m.cur m.code with
  | .ok s' => .ok { m with cur := s', code := [] }
  | .error e => .error e

/-- `pushFrame` — THE CALL (arity-guarded, the big-step guard
    mirrored): the args are popped off the current stack (bottom
    removal — under the entry contract the stack IS `args.reverse`) and
    bound to the callee's param locals (param i = the i-th pushed —
    `bindArgs`'s map); the callee starts with an EMPTY operand stack;
    the caller freezes into a `Frame` with `retTo` = its remaining
    code. Wrong arity = the trap. -/
def pushFrame (f : Fn) (args : List Val) (retTo : List Instr) (m : Mach) :
    Except Err Mach :=
  if args.length = f.params then
    .ok { frames := Frame.mk m.cur.locals retTo
            (dropBottom args.length m.cur.stack) :: m.frames
        , cur := { locals := fun n => args.getD n (m.cur.locals n)
                 , stack := []
                 , mem := m.cur.mem, memSize := m.cur.memSize }
        , code := f.body }
  else .error .trap

/-- `popFrame` — THE RETURN: the current frame's stack TOP is the
    result (the return convention); the frame pops, the frozen caller
    resumes — its locals, its stack with the result pushed, its
    `retTo` as the code. The memory stays the callee's (shared, stores
    persist). A frame returning NO value, or no frame to pop (the
    top-level return), is `none`. -/
def popFrame (m : Mach) : Option Mach :=
  match m.frames with
  | [] => none
  | fr :: rest =>
      match m.cur.stack with
      | [] => none
      | r :: rs =>
          some { frames := rest
               , cur := { locals := fr.locals, stack := r :: fr.retStack
                        , mem := m.cur.mem, memSize := m.cur.memSize }
               , code := fr.retTo }

/-- `runToReturn` — run the machine: flat phase, pop, repeat, until
    nothing is left to pop (the program's result). Every phase entry
    and every pop consumes one fuel unit. Errors propagate: a
    branch/trap in ANY frame kills the machine (branches do not cross
    calls in this fragment — the layered-err note at the top). -/
def runToReturn : Nat → Mach → Except Err Mach
  | 0, _ => .error .outOfFuel
  | fuel + 1, m =>
      match mRun fuel m with
      | .error e => .error e
      | .ok done =>
          match popFrame done with
          | some m' => runToReturn fuel m'
          | none => .ok done

/-- THE CALL PROTOCOL — what the emitter's `call_indirect` sequence
    assumes: the caller's flat prep has ALREADY pushed the args (v1's
    `pushArgs_exec`; the entry contract `s.stack = args.reverse` — the
    caller's operand stack is empty at the call), the machine frames
    the call (`pushFrame`, the caller's remaining code `rest` = the
    return address), and `runToReturn` runs the callee to its return
    and pops back into the caller at `retTo`. -/
def callProtocol (fuel : Nat) (f : Fn) (args : List Val) (s : State)
    (rest : List Instr) : Except Err Mach :=
  match pushFrame f args rest ⟨[], s, []⟩ with
  | .error e => .error e
  | .ok m2 => runToReturn fuel m2

/-- The pop's contract (kernel-checked, definitional): popping a frame
    resumes EXACTLY the frozen caller — its locals, its stack with the
    result on top, its `retTo` as the code, the shared memory. -/
theorem popFrame_restores (fr : Frame) (rest : List Frame) (s : State) (r : Val)
    (rs : List Val) :
    ∃ m', popFrame ⟨fr :: rest, { s with stack := r :: rs }, []⟩ = some m'
      ∧ m'.cur.locals = fr.locals
      ∧ m'.cur.stack = r :: fr.retStack
      ∧ m'.code = fr.retTo
      ∧ m'.frames = rest := by
  refine ⟨{ frames := rest
          , cur := { locals := fr.locals, stack := r :: fr.retStack
                   , mem := s.mem, memSize := s.memSize }
          , code := fr.retTo }, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [popFrame]

/-- THE FRAME THEOREM: the frame machine's call protocol computes the
    SAME result as the big-step composition — same result value, same
    errors. The callee's run inside the machine IS `callExecFuel`'s
    sub-exec (`call_split`'s right side): same `bindArgs` state, same
    body, same fuel. The machine the emitter's `call_indirect` protocol
    assumes IS the composition semantics. The 2-slack fuel hypothesis
    is the model artifact (the pop + the resume phase each consume a
    unit) — and it is GENUINE (W6.9 audit): at `fuel = 1` the resume
    phase starves (`runToReturn 1` runs its `mRun` at 0 = `outOfFuel`)
    while the big-step side has already returned, so the fuel-
    insensitive form is FALSE and the bound stays. Kernel-checked. -/
theorem callProtocol_agrees (fuel : Nat) (f : Fn) (args : List Val) (s : State)
    (harity : args.length = f.params) (hs : s.stack = args.reverse)
    (hf : 2 ≤ fuel) :
    (match callProtocol (fuel + 1) f args s [] with
     | .ok m => m.cur.stack.head?
     | .error _ => none)
      =
    (match execList fuel (bindArgs args s) f.body with
     | .ok s' => s'.stack.head?
     | .error _ => none) := by
  rw [callProtocol, pushFrame, if_pos harity]
  dsimp only
  have hbound : ({ locals := fun n => args.getD n (s.locals n)
                 , stack := ([] : List Val), mem := s.mem
                 , memSize := s.memSize } : State)
      = bindArgs args s := by
    simp only [bindArgs, dropBottom, hs, List.reverse_reverse, List.drop_length,
      List.reverse_nil]
  rw [hbound]
  simp only [runToReturn, mRun]
  cases hx : execList fuel (bindArgs args s) f.body with
  | error e => simp
  | ok s'' =>
      simp only [popFrame]
      cases hs2 : s''.stack with
      | nil => simp [hs2]
      | cons r rs =>
          cases fuel with
          | zero => simp [execList] at hx
          | succ k =>
              cases k with
              | zero => exact absurd hf (by omega)
              | succ k' => simp [runToReturn, mRun, execList, popFrame, hs2]

/-- THE COMPOSITION COROLLARY: the machine ≡ the FULL flat composition
    (`call_split`'s left side — prep pushes, binding pops, callee body)
    at the matched budget. The emitter's `call_indirect` protocol and
    the composition semantics are the same machine. Kernel-checked.
    The `+ 2` fuel slack STAYS (W6.9 note): it is the machine's own
    budget arithmetic, not a correctness hypothesis — `callProtocol`'s
    resume phase consumes one unit beyond the sub-exec's, so at
    `fuel - 2*len = 1` the machine starves mid-resume (`outOfFuel`,
    genuinely observable: `callProtocol_agrees` at fuel 1 is a
    counterexample) where the flat side has already returned. -/
theorem callProtocol_is_call_split (fuel : Nat) (f : Fn) (args : List Val) (s : State)
    (harity : args.length = f.params) (hs0 : s.stack = [])
    (hf : 2 * args.length + 2 ≤ fuel) :
    (match callProtocol (fuel - 2 * args.length + 1) f args
        { s with stack := args.reverse } [] with
     | .ok m => m.cur.stack.head?
     | .error _ => none)
      =
    (match execList fuel s (pushArgs args ++ (popParams args.length ++ f.body)) with
     | .ok s' => s'.stack.head?
     | .error _ => none) := by
  rw [call_split fuel f args s harity hs0]
  rw [callExecFuel, if_pos harity]
  have h := callProtocol_agrees (fuel - 2 * args.length) f args
    { s with stack := args.reverse } harity rfl (by have := hf; omega)
  rw [h]
  have hEq : bindArgs args { s with stack := args.reverse } = bindArgs args s := by
    simp [bindArgs, dropBottom, hs0, List.drop_length]
  rw [hEq]

/-- The frame-demo caller state: the post-prep convention (the args
    pushed — `callProtocol`'s entry contract), a live value in local 5
    (the caller's own), locals 0/1 = 0 (the callee's params will bind
    21/21 in ITS OWN frame). -/
def frameDemo : State :=
  ⟨fun n => if n = 5 then .i64 77 else .i64 0, [.i64 21, .i64 21],
   fun _ => (0 : UInt8), 64⟩

/-- THE FRAME-SEPARATION PIN (kernel-checked): after the protocol, the
    caller's local 5 is INTACT (77) and local 0 is the CALLER's (0 —
    the callee's param binding did not leak into the caller's frame),
    with the result on the stack. The flat model's
    pairwise-distinctness hypotheses, made structural. -/
theorem frame_demo_separation :
    (match callProtocol 50 adderFn [.i64 21, .i64 21] frameDemo [] with
     | .ok m => (m.cur.locals 5, m.cur.locals 0, m.cur.stack)
     | .error _ => (.i64 0, .i64 0, []))
      = (.i64 77, .i64 0, [.i64 42]) := by
  decide

/-! ### THE NEGATIVE CONTROL — the wrong return address -/

/-- THE BUGGY VARIANT (the return-address corruption class): the frame
    records the WRONG `retTo` — here the CALLEE's body as the caller's
    return address (the "return into the callee" bug). -/
def pushFrameBuggy (f : Fn) (args : List Val) (retTo : List Instr) (m : Mach) :
    Except Err Mach :=
  if args.length = f.params then
    .ok { frames := Frame.mk m.cur.locals f.body
            (dropBottom args.length m.cur.stack) :: m.frames
        , cur := { locals := fun n => args.getD n (m.cur.locals n)
                 , stack := []
                 , mem := m.cur.mem, memSize := m.cur.memSize }
        , code := f.body }
  else .error .trap

/-- The protocol over the corrupt `pushFrameBuggy`. -/
def callProtocolBuggy (fuel : Nat) (f : Fn) (args : List Val) (s : State)
    (rest : List Instr) : Except Err Mach :=
  match pushFrameBuggy f args rest ⟨[], s, []⟩ with
  | .error e => .error e
  | .ok m2 => runToReturn fuel m2

/-- THE WRONG-RETURN-ADDRESS NEGATIVE CONTROL: the corrupted frame
    runs the callee body AGAIN after the pop (the wrong `retTo`) — the
    final machine state disagrees with the correct protocol's (the
    caller's stack grows instead of halting at the result). If a
    regression corrupted the frame's return address, this theorem's
    shape is the sabotage control. Kernel-checked (decide). -/
theorem callProtocolBuggy_disagrees :
    (match callProtocolBuggy 50 adderFn [.i64 21, .i64 21] frameDemo [] with
     | .ok m => m.cur.stack | .error _ => [])
      ≠
    (match callProtocol 50 adderFn [.i64 21, .i64 21] frameDemo [] with
     | .ok m => m.cur.stack | .error _ => []) := by
  decide

end Calls

/-! ### The frames layer's tests — build-failing #guards -/

section FrameTests

open Calls

-- 1. THE PROTOCOL PIN: the protocol computes the adder's 42.
#guard (match callProtocol 50 adderFn [.i64 21, .i64 21] frameDemo [] with
        | .ok m => m.cur.stack == [.i64 42] | .error _ => false) = true

-- 2. THE ARITY GUARD, machine level: a 1-arg call to the 2-param
--    adder TRAPS in pushFrame (the big-step guard, mirrored).
#guard (match callProtocol 50 adderFn [.i64 21] frameDemo [] with
        | .error .trap => true | _ => false) = true

-- 3. THE CALLER RESUMES: rest = the post-call code runs with the
--    RESULT on top (what the caller's `local.set` consumes).
#guard (match callProtocol 50 adderFn [.i64 21, .i64 21] frameDemo
          [.localset 6, .localget 6] with
        | .ok m => m.cur.stack == [.i64 42] && m.cur.locals 6 == .i64 42
        | .error _ => false) = true

-- 4. TWO HOPS: the first call's result feeds the second (the frames
--    stack and unwind — the run-paps shape).
#guard (match callProtocol 50 adderFn [.i64 21, .i64 21] frameDemo [] with
        | .ok m1 =>
            match callProtocol 50 adderFn [.i64 42, .i64 8]
                { m1.cur with stack := .i64 8 :: m1.cur.stack } [] with
            | .ok m2 => m2.cur.stack == [.i64 50]
            | .error _ => false
        | .error _ => false) = true

end FrameTests

/-! ## The allocator layer — the SPEC of the spliced `runtime.wat`

THE LOAD-BEARING SPLICE: WasmGenMain splices `runtime.wat`'s funcs/globals
into the emitted module (single module, no imports) — the allocator
(`$alloc`: size-class freelist + bump) and the Perceus RC discipline
(`$rc_inc`/`$rc_dec`: dec→0 pushes the block back to its class pool).
This section is the EXECUTABLE MODEL = the SPEC of that splice (not a
copy): alloc/free over a byte-array mem + freelist, with the
THEOREM-LEVEL invariants the emitter's object code silently relies on:

* `aAlloc_no_alias` — an alloc never returns a block overlapping a
  LIVE object (the no-alias invariant), and it preserves `Inv`, so by
  induction (`runOps_inv`) EVERY alloc in a run is alias-free against
  the live set at its own moment;
* `aFree_returns` — a freed block RETURNS to the freelist and leaves
  the live set;
* `aFree_twice_errors` / `rcDec_frees_once` — rc_dec to zero frees
  EXACTLY ONCE: the second dec (or a bare double free) TRIPS.

Kernel-checked (small closed list shapes — the induction goes
through); the concrete traces are additionally #guard-witnessed below,
with the double-free negative control.

THE MODEL DELTAS (documented, honest): ONE freelist (the runtime's 6
size classes are 6 independent copies of this ONE discipline — the
class index is dropped); the freelist links live in the state (the
runtime stores `next` in the block's first word, `p.next =
freelist[cls]`); sizes are the GRANULAR (16-byte-class) sizes, the
16-align rounding folded into the caller's size; the bump's
`memory.grow` OOM path and the 48..256 canonical-ABI return-area
reserve are the caller's initialization (unmodeled). `rc_dec` on an
rc-0 block ERRORS here where the runtime's `i32.sub` would WRAP to
0xFFFFFFFF and free nothing — the model is stricter, pinned as the
use-after-free class.
-/

namespace Alloc

/-- A block: (byte address, granular size). The runtime's blocks are
    the object records `{ rc: u32 @0, tag: u8 @4, class: u8 @5,
    fields @8 }` (runtime.wat's layout comment). -/
abbrev Blk := Nat × Nat

/-- Two blocks' byte ranges do not overlap. -/
def disj (p q : Blk) : Prop := p.1 + p.2 ≤ q.1 ∨ q.1 + q.2 ≤ p.1

theorem disj_symm {p q : Blk} (h : disj p q) : disj q p := by
  cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

/-- Pairwise range-disjointness over a block list. Deliberately NO
    `p ≠ q` side condition: a nonempty block never overlaps itself, so
    this definition also forbids duplicate entries and duplicate
    addresses (under `Inv`'s positivity) — the discipline that keeps
    the freelist honest. -/
def pairwise : List Blk → Prop
  | [] => True
  | b :: bs => (∀ q, q ∈ bs → disj b q) ∧ pairwise bs

/-- The allocator state — the SPEC of the spliced `runtime.wat`
    (guestlang-owned pooled allocator + Perceus RC):
    * `freeL` — the freelist (head = next pop; the runtime's 6 size
      classes are 6 independent copies of this one discipline);
    * `liveL` — the blocks handed out and not yet freed (the OBSERVER
      the invariants need; the runtime has no such registry);
    * `top` — `$heap` (the bump pointer; the 48..256 return-area
      reserve is the caller's init, unmodeled);
    * `mem` — the linear memory as a byte function; `mem blk` is the
      block's rc cell — `$rc_inc`/`$rc_dec`'s target. -/
structure ASt where
  freeL : List Blk
  liveL : List Blk
  top : Nat
  mem : Nat → UInt8

/-- THE ALLOCATOR INVARIANT: every block (free or live) is nonempty
    and ends at or below the bump pointer, and ALL blocks — across the
    free/live boundary — are pairwise range-disjoint. Preserved by
    every op (`runOps_inv`); it is what makes every alloc in a run
    alias-free (`aAlloc_no_alias`), not just the first. (`InvP` over
    explicit components + the `abbrev` — the components, not the state
    record, are what the proofs destructure.) -/
def InvP (fl live : List Blk) (top : Nat) : Prop :=
  (∀ p ∈ fl ++ live, p.1 + p.2 ≤ top)
    ∧ (∀ p ∈ fl ++ live, 0 < p.2)
    ∧ pairwise (fl ++ live)

abbrev Inv (a : ASt) : Prop := InvP a.freeL a.liveL a.top

theorem pairwise_head_nmem {b : Blk} {bs : List Blk} (hpos : 0 < b.2)
    (h : pairwise (b :: bs)) : b ∉ bs := by
  intro hb
  have hd := h.1 b hb
  cases hd with
  | inl hd => omega
  | inr hd => omega

/-- The split: a pairwise list's parts are pairwise, and cross-disjoint
    (unconditionally — the `≠`-free definition). -/
theorem pairwise_append {xs ys : List Blk} (h : pairwise (xs ++ ys)) :
    pairwise xs ∧ pairwise ys ∧ ∀ x ∈ xs, ∀ y ∈ ys, disj x y := by
  induction xs with
  | nil => exact ⟨True.intro, h, fun x hx => absurd hx (by simp)⟩
  | cons b bs ih =>
      obtain ⟨hall, hpair⟩ := h
      obtain ⟨h1, h2, h3⟩ := ih hpair
      refine ⟨⟨fun q hq => hall q (List.mem_append.mpr (Or.inl hq)), h1⟩, h2, ?_⟩
      intro x hx y hy
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hall y (List.mem_append.mpr (Or.inr hy))
      · exact h3 x hx' y hy

/-- The maker (the append direction the proofs need). -/
theorem pairwise_append_mk {xs ys : List Blk} (h1 : pairwise xs) (h2 : pairwise ys)
    (hcross : ∀ x ∈ xs, ∀ y ∈ ys, disj x y) : pairwise (xs ++ ys) := by
  induction xs with
  | nil => exact h2
  | cons b bs ih =>
      show (∀ q, q ∈ bs ++ ys → disj b q) ∧ pairwise (bs ++ ys)
      refine ⟨fun q hq => ?_, ih h1.2 (fun x hx y hy => hcross x
        (List.mem_cons_of_mem _ hx) y hy)⟩
      rcases List.mem_append.mp hq with hq' | hq'
      · exact h1.1 q hq'
      · exact hcross b (by simp) q hq'

/-- Filtering a pairwise list preserves pairwise disjointness (the
    free's live-set removal). -/
theorem pairwise_filter (g : Blk → Bool) (l : List Blk) (h : pairwise l) :
    pairwise (l.filter g) := by
  induction l with
  | nil => exact trivial
  | cons b bs ih =>
      by_cases hb : g b = true
      · rw [List.filter_cons_of_pos hb]
        exact ⟨fun q hq => h.1 q (List.mem_filter.mp hq).1, ih h.2⟩
      · rw [List.filter_cons_of_neg hb]
        exact ih h.2

/-- `$alloc` (runtime.wat): pop the class freelist if non-empty (the
    rc cell RESET to 1 — the runtime's `rc reset to 1` comment), else
    BUMP (`$heap` advances; the 16-align rounding is folded into the
    granular `size`). Returns the new state and the block record. -/
def aAlloc (size : Nat) (a : ASt) : ASt × Blk :=
  match a.freeL with
  | p :: rest =>
      (⟨rest, p :: a.liveL, a.top,
        fun i => if i = p.1 then (1 : UInt8) else a.mem i⟩, p)
  | [] =>
      (⟨[], (a.top, size) :: a.liveL, a.top + size,
        fun i => if i = a.top then (1 : UInt8) else a.mem i⟩, (a.top, size))

/-- THE NO-ALIAS THEOREM: an alloc from an `Inv` state returns a block
    whose byte range overlaps NO LIVE block (`liveL`) — and preserves
    `Inv`, so by induction (`runOps_inv`) EVERY alloc in a run is
    alias-free against the live set at its own moment. Kernel-checked. -/
theorem aAlloc_no_alias (size : Nat) (a : ASt) (h : Inv a) (hsz : 0 < size) :
    Inv (aAlloc size a).1 ∧ ∀ p ∈ a.liveL, disj (aAlloc size a).2 p := by
  obtain ⟨hend, hpos, hpair⟩ := h
  obtain ⟨hfreeP, hliveP, hcross⟩ := pairwise_append hpair
  cases hfl : a.freeL with
  | nil =>
      -- the bump path: the new block starts AT the bump pointer
      simp only [aAlloc, hfl, Inv]
      refine ⟨⟨?_, ?_, ?_⟩, fun p hp => Or.inr ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · omega
        · have := hend q (List.mem_append.mpr (Or.inr hq'))
          omega
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · omega
        · exact hpos q (List.mem_append.mpr (Or.inr hq'))
      · refine ⟨fun q hq => Or.inr ?_, hliveP⟩
        have := hend q (List.mem_append.mpr (Or.inr hq))
        omega
      · have := hend p (List.mem_append.mpr (Or.inr hp))
        omega
  | cons p rest =>
      -- the freelist-pop path: the popped block is REUSED
      simp only [aAlloc, hfl, Inv]
      rw [hfl] at hfreeP
      obtain ⟨hfreeHead, hfreeTail⟩ := hfreeP
      have hmemFL : ∀ x ∈ rest, x ∈ a.freeL := by
        intro x hx; rw [hfl]; exact List.mem_cons_of_mem _ hx
      have hheadFL : p ∈ a.freeL := by rw [hfl]; simp
      refine ⟨⟨?_, ?_, ?_⟩, fun y hy => ?_⟩
      · intro q hq
        rcases List.mem_append.mp hq with hq' | hq'
        · exact hend q (List.mem_append.mpr (Or.inl (hmemFL q hq')))
        · rcases List.mem_cons.mp hq' with hc | hq''
          · rw [hc]
            exact hend p (List.mem_append.mpr (Or.inl hheadFL))
          · exact hend q (List.mem_append.mpr (Or.inr hq''))
      · intro q hq
        rcases List.mem_append.mp hq with hq' | hq'
        · exact hpos q (List.mem_append.mpr (Or.inl (hmemFL q hq')))
        · rcases List.mem_cons.mp hq' with hc | hq''
          · rw [hc]
            exact hpos p (List.mem_append.mpr (Or.inl hheadFL))
          · exact hpos q (List.mem_append.mpr (Or.inr hq''))
      · refine pairwise_append_mk hfreeTail ⟨fun y hy => hcross p hheadFL y hy,
          hliveP⟩ ?_
        intro x hx y hy
        rcases List.mem_cons.mp hy with hc | hy'
        · rw [hc]
          exact disj_symm (hfreeHead x hx)
        · exact hcross x (hmemFL x hx) y hy'
      · exact hcross p hheadFL y hy

/-- Any two DISTINCT entries of a pairwise list are disjoint in one
    order or the other (position-independent). -/
theorem pairwise_mem2 {cs : List Blk} (hpos : ∀ p ∈ cs, 0 < p.2) (h : pairwise cs) :
    ∀ p ∈ cs, ∀ q ∈ cs, p ≠ q → disj p q ∨ disj q p := by
  induction cs with
  | nil => intro p hp; cases hp
  | cons b bs ih =>
      obtain ⟨hall, hpair⟩ := h
      have hpos' : ∀ p ∈ bs, 0 < p.2 := fun p hp => hpos p (List.mem_cons_of_mem _ hp)
      intro p hp q hq hne
      rcases List.mem_cons.mp hp with rfl | hp'
      · rcases List.mem_cons.mp hq with hq' | hq'
        · exact absurd hq' (fun hc => hne hc.symm)
        · exact Or.inl (hall q hq')
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact Or.inr (hall p hp')
      · exact ih hpos' hpair p hp' q hq' hne

/-- `$rc_dec`'s dec→0 arm (runtime.wat): return the block to its class
    pool — `p.next = freelist[cls]; freelist[cls] = p`. Freeing an
    address that is NOT live (never allocated, or ALREADY FREED — the
    double-free) is an ERROR: the model trips where the runtime's
    freelist push would silently corrupt (the pinned bug class). -/
def aFree (blk : Nat) (a : ASt) : Except String ASt :=
  match a.liveL.find? (fun p => p.1 = blk) with
  | some p => .ok ⟨p :: a.freeL, a.liveL.filter (fun q => q.1 != blk), a.top, a.mem⟩
  | none => .error s!"free of unowned / double-freed block {blk}"

/-- THE FREELIST-RETURN THEOREM: freeing a live block returns it to
    the freelist (the popped-again record), removes it from the live
    set (NO entry with that address remains live), preserves `Inv`,
    and leaves the memory untouched. Kernel-checked. -/
theorem aFree_returns (blk : Nat) (a : ASt) (h : Inv a)
    (hmem : ∃ sz, (blk, sz) ∈ a.liveL) :
    ∃ a', aFree blk a = .ok a'
      ∧ (∃ sz, (blk, sz) ∈ a'.freeL)
      ∧ (∀ sz, (blk, sz) ∉ a'.liveL)
      ∧ a'.mem = a.mem
      ∧ Inv a' := by
  obtain ⟨sz, hmem⟩ := hmem
  have hfind : a.liveL.find? (fun p => p.1 = blk) ≠ none := by
    intro hnone
    have := List.find?_eq_none.mp hnone (blk, sz) hmem
    simp at this
  obtain ⟨p, hfound⟩ : ∃ q, a.liveL.find? (fun q => q.1 = blk) = some q := by
    cases hf : a.liveL.find? (fun q => q.1 = blk) with
    | none => exact absurd hf hfind
    | some q => exact ⟨q, rfl⟩
  have hp1 : p.1 = blk := by simpa using List.find?_some hfound
  subst hp1
  have hpmem : p ∈ a.liveL := List.mem_of_find?_eq_some hfound
  obtain ⟨hend, hpos, hpair⟩ := h
  obtain ⟨hfreeP, hliveP, hcross⟩ := pairwise_append hpair
  have hpos' : ∀ q ∈ a.liveL, 0 < q.2 := fun q hq => hpos q (List.mem_append.mpr (Or.inr hq))
  refine ⟨⟨p :: a.freeL, a.liveL.filter (fun q => q.1 != p.1), a.top, a.mem⟩, by
      simp only [aFree, hfound], ⟨p.2, by simp [List.mem_cons]⟩, ?_, rfl, ⟨?_, ?_, ?_⟩⟩
  · -- the address left the live set (filter removes EVERY match)
    intro sz hq
    have hq' := (List.mem_filter.mp hq).2
    simp at hq'
  · -- endLE: p from liveEnd (it was live), the rest unchanged
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · rcases List.mem_cons.mp hq' with hc | hq''
      · rw [hc]
        exact hend p (List.mem_append.mpr (Or.inr hpmem))
      · exact hend q (List.mem_append.mpr (Or.inl hq''))
    · exact hend q (List.mem_append.mpr (Or.inr (List.mem_filter.mp hq').1))
  · -- pos
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · rcases List.mem_cons.mp hq' with hc | hq''
      · rw [hc]
        exact hpos' p hpmem
      · exact hpos q (List.mem_append.mpr (Or.inl hq''))
    · exact hpos' q (List.mem_filter.mp hq').1
  · -- pairAll: pairwise ((p :: freeL) ++ filter (=≠ blk) liveL)
    show (∀ q, q ∈ a.freeL ++ a.liveL.filter (fun q => q.1 != p.1) → disj p q)
      ∧ pairwise (a.freeL ++ a.liveL.filter (fun q => q.1 != p.1))
    refine ⟨fun q hq => ?_, pairwise_append_mk hfreeP
      (pairwise_filter (fun q => q.1 != p.1) a.liveL hliveP)
      (fun x hx y hy => hcross x hx y (List.mem_filter.mp hy).1)⟩
    rcases List.mem_append.mp hq with hq' | hq'
    · -- q free: q before p in the old append → cross + symm
      exact disj_symm (hcross q hq' p hpmem)
    · -- q live (filtered): its address ≠ p.1 → q ≠ p
      have hqm : q ∈ a.liveL := (List.mem_filter.mp hq').1
      have hqp : q ≠ p := by
        intro hc
        rw [hc] at hq'
        simp at hq'
      rcases pairwise_mem2 hpos' hliveP p hpmem q hqm hqp.symm with hd | hd
      · exact hd
      · exact disj_symm hd

/-- THE DOUBLE-FREE NEGATIVE CONTROL (theorem-level): a second free
    of the same address — with no re-alloc in between — ALWAYS trips.
    Kernel-checked. -/
theorem aFree_twice_errors (blk : Nat) (a a' : ASt) (h : Inv a)
    (hmem : ∃ sz, (blk, sz) ∈ a.liveL) (hok : aFree blk a = .ok a') :
    ∃ e, aFree blk a' = .error e := by
  obtain ⟨sz, hmem⟩ := hmem
  have hfind : a.liveL.find? (fun p => p.1 = blk) ≠ none := by
    intro hnone
    have h0 := List.find?_eq_none.mp hnone (blk, sz) hmem
    simp at h0
  cases hf : a.liveL.find? (fun p => p.1 = blk) with
  | none => exact absurd hf hfind
  | some p =>
      simp only [aFree, hf] at hok
      cases hok
      refine ⟨s!"free of unowned / double-freed block {blk}", ?_⟩
      have hnone :
          (a.liveL.filter (fun q => q.1 != blk)).find? (fun q => q.1 = blk) = none := by
        apply List.find?_eq_none.mpr
        intro x hx
        have hne : x.1 ≠ blk := by
          simpa using (List.mem_filter.mp hx).2
        simp [hne]
      simp [aFree, hnone]

/-- `$rc_inc` (runtime.wat): `rc += 1` — the model's rc cell IS the
    block's first byte (`mem blk`). -/
def rcInc (blk : Nat) (a : ASt) : ASt :=
  { a with mem := fun i => if i = blk then a.mem blk + 1 else a.mem i }

/-- `$rc_dec` (runtime.wat): decrement the rc cell; rc → 0 returns the
    block to its pool (the `aFree` arm — the runtime's `rc == 0 →
    return the block to its class pool`). rc = 0 BEFORE the decrement
    is the USE-AFTER-FREE error: the runtime's `i32.sub` would WRAP to
    0xFFFFFFFF and free nothing — the model is stricter, pinned as its
    own class. -/
def rcDec (blk : Nat) (a : ASt) : Except String ASt :=
  match a.mem blk |>.toNat with
  | 0 => .error s!"use after free: rc({blk}) already 0"
  | 1 => aFree blk { a with mem := fun i => if i = blk then (0 : UInt8) else a.mem i }
  | rc + 2 =>
      .ok { a with mem := fun i => if i = blk then (rc + 1 : Nat).toUInt8 else a.mem i }

/-- THE RC THEOREM — rc_dec to zero frees EXACTLY ONCE: a live block
    at rc = 1, on `rcDec`, leaves the live set, enters the freelist,
    its rc cell reads 0 — and a SECOND `rcDec` TRIPS (use after
    free). No double-free. Kernel-checked. -/
theorem rcDec_frees_once (blk : Nat) (a : ASt) (h : Inv a)
    (hmem : ∃ sz, (blk, sz) ∈ a.liveL) (hrc : a.mem blk = 1) :
    ∃ a', rcDec blk a = .ok a'
      ∧ (∀ sz, (blk, sz) ∉ a'.liveL)
      ∧ (∃ sz, (blk, sz) ∈ a'.freeL)
      ∧ a'.mem blk = 0
      ∧ (∃ e, rcDec blk a' = .error e) := by
  obtain ⟨hend, hpos, hpair⟩ := h
  have hsetInv : Inv { a with mem := fun i => if i = blk then (0 : UInt8) else a.mem i } :=
    ⟨hend, hpos, hpair⟩
  have hset : ({ a with mem := fun i => if i = blk then (0 : UInt8) else a.mem i }).mem blk = 0 :=
    by simp
  obtain ⟨a', hfree, hfl, hnl, hmem', hinv'⟩ :=
    aFree_returns blk { a with mem := fun i => if i = blk then (0 : UInt8) else a.mem i }
      hsetInv hmem
  refine ⟨a', ?_, hnl, hfl, ?_, ?_⟩
  · simp only [rcDec, hrc]
    exact hfree
  · rw [hmem']
    exact hset
  · refine ⟨s!"use after free: rc({blk}) already 0", ?_⟩
    have h0 : a'.mem blk = 0 := by rw [hmem']; exact hset
    simp [rcDec, h0]

/-- One allocator operation: `$alloc size`, or `$rc_dec` with the rc
    reaching 0 (the free). -/
inductive AOp where
  | alloc (size : Nat)
  | free (blk : Nat)

/-- Run an op list. A free of an unowned address KILLS the run (the
    error propagates — see `aFree_twice_errors` for the double-free
    instance). -/
def runOps : List AOp → ASt → Except String ASt
  | [], a => .ok a
  | .alloc size :: rest, a => runOps rest (aAlloc size a).1
  | .free blk :: rest, a => aFree blk a >>= runOps rest

/-- THE OP-LIST THEOREM (the induction the shapes allow): `runOps`
    preserves `Inv` (the alloc sizes positive — the runtime never
    allocates an empty class record) — so every alloc in a run from a
    sound state is alias-free against the live set AT ITS OWN MOMENT
    (per-op: `aAlloc_no_alias`), every free returns its block (per-op:
    `aFree_returns`), and any free of an unowned/double-freed address
    kills the run (the `.error` arm — the `True` there is the vacuous
    side of the match; the error ITSELF is pinned by
    `aFree_twice_errors` and the #guard traces). Kernel-checked. -/
theorem runOps_inv : ∀ (ops : List AOp),
    (∀ sz : Nat, AOp.alloc sz ∈ ops → 0 < sz) →
    ∀ a, Inv a →
    (match runOps ops a with
     | .ok a' => Inv a'
     | .error _ => True) := by
  intro ops
  induction ops with
  | nil => intro _ a h; simp only [runOps]; exact h
  | cons op ops ih =>
      intro hsz a h
      cases op with
      | alloc size =>
          simp only [runOps]
          exact ih (fun sz hsz' => hsz sz (List.mem_cons_of_mem _ hsz')) _
            (aAlloc_no_alias size a h (hsz size (by simp))).1
      | free blk =>
          simp only [runOps]
          by_cases hlive : ∃ sz, (blk, sz) ∈ a.liveL
          · obtain ⟨a', hfree, _, hnl, hmem', hinv'⟩ := aFree_returns blk a h hlive
            rw [hfree]
            show (match runOps ops a' with | .ok a'' => Inv a'' | .error _ => True)
            exact ih (fun sz hsz' => hsz sz (List.mem_cons_of_mem _ hsz')) a' hinv'
          · have hnone : a.liveL.find? (fun p => p.1 = blk) = none := by
              apply List.find?_eq_none.mpr
              intro x hx
              have hne : x.1 ≠ blk := by
                intro hc
                cases x with
                | mk xa xb =>
                    have hxab : xa = blk := hc
                    rw [hxab] at hx
                    exact hlive ⟨xb, hx⟩
              simp [hne]
            obtain ⟨e, herr⟩ : ∃ e, aFree blk a = .error e :=
              ⟨s!"free of unowned / double-freed block {blk}", by
                simp only [aFree, hnone]⟩
            simp only [herr]
            exact trivial

end Alloc

/-! ### The allocator layer's traces — build-failing #guards -/

section AllocTests

open Alloc

/-- The demo allocator state: the heap top at 256 (above the 48..256
    return-area reserve — runtime.wat's `$heap` init), zeroed memory. -/
def demoASt : ASt := ⟨[], [], 256, fun _ => (0 : UInt8)⟩

-- 1. Two allocs bump: live addrs 256, 288 (the granular records),
--    top at 320 — the second never aliases the first (witnessed).
#guard (match runOps [.alloc 32, .alloc 32] demoASt with
        | .ok a => a.liveL.map Prod.fst == [288, 256] && a.top == 320
        | .error _ => false) = true

-- 2. THE FREELIST RETURN + REUSE: free the first block → it returns
--    to the freelist; the next alloc REUSES it (the pop) — the freed
--    address comes back, the live one (288) untouched.
#guard (match runOps [.alloc 32, .alloc 32, .free 256, .alloc 32] demoASt with
        | .ok a => a.liveL.map Prod.fst == [256, 288] && a.freeL == []
        | .error _ => false) = true

-- 3. THE DOUBLE-FREE NEGATIVE CONTROL: the second free of the same
--    address TRIPS (the run dies) — never a silent freelist corruption.
#guard (match runOps [.alloc 32, .free 256, .free 256] demoASt with
        | .error _ => true | .ok _ => false) = true

-- 4. rc_dec TO ZERO FREES EXACTLY ONCE: alloc (rc = 1), two rc_inc
--    (rc = 3), three rc_dec — the third frees (rc cell 0, block on
--    the freelist); a FOURTH trips (use after free).
#guard (match rcDec 256 (rcInc 256 (rcInc 256 (aAlloc 32 demoASt).1)) with
        | .ok a1 => match rcDec 256 a1 with
          | .ok a2 => match rcDec 256 a2 with
            | .ok a => (256, 32) ∈ a.freeL && a.mem 256 == 0
            | .error _ => false
          | .error _ => false
        | .error _ => false) = true
#guard (match rcDec 256 (rcInc 256 (rcInc 256 (aAlloc 32 demoASt).1)) with
        | .ok a1 => match rcDec 256 a1 with
          | .ok a2 => match rcDec 256 a2 with
            | .ok a => match rcDec 256 a with | .error _ => true | .ok _ => false
            | .error _ => false
          | .error _ => false
        | .error _ => false) = true

end AllocTests

end WasmBackend.Sem
