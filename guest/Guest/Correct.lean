/-
# Guest.Correct — translation correctness for the straight-line fragment

The mined P1 (`legacy/lean/wasm-backend/WasmBackend/Correct.lean` +
`Sem.lean`): the emitted wasm's EXECUTION agrees with the source
function's semantics, for the fragment where that is tractable. The
legacy proved it over TYPED EMISSION TEMPLATES because its emitter was
`partial`; the new tree's lowering (`Guest.Lower.lowerFunc`) is TOTAL
and the executor (`WasmCore.Exec`) is a total fuel-bounded function,
so the correspondence is stated DIRECTLY: the compiled chain's
`execList` run computes the source chain's value.

THE FRAGMENT (the honesty ledger — the slice the guest covers TODAY,
distilled to what the theorem honestly speaks about):

* COVERED (the theorem face): the straight-line u64 ANF let-chain —
  `let r := lit v` (the `emitLet` u64-literal row), `let r := a OP b`
  for the u64 arithmetic rows (add/sub/mul — the legacy's proven
  `UInt64.add` row grown to three), and `return r` (the exit-frame
  discipline: `localget r; localset res; br 0`, the result read after
  the frame — values never ride the stack across the branch). The
  machine face is the TEMPLATE (`compileChain`/`fnBody`) — the exact
  instruction shapes `Guest.Lower.lowerFunc` emits for these rows,
  pinned to the REAL lowering's output by the extraction `#guard`s
  below (the legacy's build-failing discipline; the new lowering is
  total and pure, so the pin compares full `Func` VALUES, body and
  locals, not a rendering).
* COVERED (the map discipline): the correspondence is GENERIC in the
  op map `w : SrcOp → Op` with the PER-PRIMITIVE ROW as the only
  per-map input (`hrow`: the map's op computes `machVal` — §6's box,
  proved once per primitive, `rfl` per row). The HONEST map `opW`
  satisfies `machVal opW op x y = opEval op x y` — the machine IS the
  source (`evalW_opW`). THE NEGATIVE CONTROL: a SABOTAGED map
  (`wBuggy` — add ↦ i64sub, the wrong-lowering bug class) is
  CONSISTENTLY wrong (the SAME generic theorem applies: the machine
  computes the sabotaged semantics exactly) and the pinned program's
  execution DISAGREES with the source value — a theorem
  (`buggy_disagrees`), not a hope.
* THE FUEL DISCIPLINE (01-core §3: the budget is SEMANTICS): the
  convergence legs carry the fuel-sufficiency premise in the
  statement (`need e` — the chain's exact budget: every flat step AND
  the completion unit); the partial-correctness leg (`run_chain_inv`)
  is fuel-INSENSITIVE: if the run answers `.ok` at ANY budget, the
  value is the map-relative semantics' — an underfueled run answers
  `.outOfFuel`, never a wrong state.
* NOT COVERED (the named boundaries, each the mechanical extension of
  the per-primitive-row pattern): the comparison/shift/conversion rows
  (decLt/decEq/shiftRight/toUInt32 — the row's value spelling wants
  its own pinned pin), the i32/u8 lanes (the second width dimension),
  the control flow (cases/jp — the frame plumbing's correspondence),
  the call lane (the recursive fragment), the boxed-Nat/object lanes
  (the memory layer's correspondence). Each lands with its own slice;
  none is silently claimed here.

THE RELATIONAL DISCIPLINE (notes/v3/01-core.md §6): the
source-semantics vs the wasm-execution crossing rides the engine's
PATTERN — per-primitive preservation rows + ONE generic theorem —
where the fragment honestly fits. The honest fit: the ANF chain's
state threading is NOT the engine's pure tree fold (`Kit.Expr`'s
leaf/un/bin) — the chain mutates a binding environment, so the
relation is the Kripke-style EVOLVING relation (§6's named extension,
`Kit.Kripke` — this file is its first consumer): `Realizes L env s`
relates the source env to the machine state, and the chain induction
composes the per-primitive rows through the env's evolution. The
value level is the engine's diagonal: the honest map's row
`machVal opW op x y = opEval op x y` is reflexivity-as-determinism
(`Rel.det_iff`'s face) — the machine's u64 IS the source's u64.

The five questions (notes/v3/01-core.md):

- **Root**: the crossing Universe↔TraceModel — the source semantics
  (a total big-step fold, `evalS`) vs the machine's execution (the
  executor's fuel-bounded run); the correspondence is the carrier.
- **Carrier grade**: refinement/simulation (impl ≤ spec, one
  direction): the machine run AGREES with the source value whenever
  it completes — `run_chain_inv` is the refinement's law; the
  convergence legs add the completeness premise.
- **Spine reading**: the correspondence reads `Guest.Lower`'s emitted
  shape (the templates) through `WasmCore.Exec`'s equations — the
  proof spine over the ONE AST.
- **Ladder rung**: rung 6 — hand theorems with named relational
  content (the generic chain theorem + the per-primitive rows).
- **Gate row**: `gates kernel-check` + lintkit's gated roots;
  GuestTests' correctness suite pins the runtime face.

Consumer trail: rides `Guest.Lower` (the templates mirror ITS emitted
rows; the extraction pins compare against its real output),
`WasmCore.Exec` (the machine), `Kit.Relation` (the pattern's citation
surface). The fixture rides `Guest.IR` directly (the IR-face pin — no
LCNF import; the chain theorems consume it through `Guest.lowerFunc`).
-/

import Guest.Lower
import WasmCore
import LintKit.Basic  -- the nolint opt-out attribute (core-only)

namespace Guest.Correct

open WasmCore

/-! ## The source fragment's op rows -/

/-- THE u64 arithmetic rows (the `binop?` UInt64 lane's proven surface,
distilled to the theorem's slice; the comparison/shift/conversion rows
are the named boundary). -/
inductive SrcOp where
  | add | sub | mul
deriving BEq, DecidableEq, Repr, Inhabited

/-- THE HONEST op map: the source row → the wasm op `Guest.Lower`'s
`binop?` emits for it. -/
def opW : SrcOp → Op
  | .add => .i64add
  | .sub => .i64sub
  | .mul => .i64mul

/-- THE SABOTAGED MAP (the negative control's bug class — a wrong
lowering): `add` compiled to `i64sub`. Everything else honest — the
control isolates the ONE wrong row. -/
def wBuggy : SrcOp → Op
  | .add => .i64sub
  | .sub => .i64sub
  | .mul => .i64mul

/-- THE SOURCE semantics of one row (UInt64's own machine arithmetic —
the native wrap IS the mod-2^64 semantics, both sides). -/
def opEval : SrcOp → UInt64 → UInt64 → UInt64
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y

/-- The MACHINE's op value: what `semOp` computes for the map's op on
the pushed args (push x then y ⇒ the stack's head is y ⇒ pop order
`[y, x]`; `semOp .i64add [.i64 a, .i64 b] = .i64 (b + a)`). Defined
THROUGH `semOp` (no second op table — the R6 discipline): a map whose
row lands outside `semOp`'s i64 answers falls to 0 — unreachable
under the row premise `hrow` the theorems consume. -/
def machVal (w : SrcOp → Op) (op : SrcOp) (x y : UInt64) : UInt64 :=
  match semOp (w op) [Val.i64 y, Val.i64 x] with
  | some (.i64 z) => z
  | _ => 0

/-- THE PER-PRIMITIVE ROW, the honest map (§6's box: proved once per
primitive — `rfl` per row: the machine's op row IS the source's
arithmetic). -/
theorem machVal_opW : ∀ (op : SrcOp) (x y : UInt64),
    machVal opW op x y = opEval op x y := by
  intro op x y; cases op <;> rfl

/-! ## The source chain (the ANF let-chain, distilled) -/

/-- THE straight-line ANF chain: `lit` binds a u64 literal, `fap` binds
a row's application of two PREVIOUSLY BOUND indices (LCNF's ANF — the
args are reads, never subcomputations), `ret` returns an index. The
indices are the fvar discipline's shadow ALREADY in machine
coordinates (the lowering's local indices). -/
inductive Src where
  | lit (r : Nat) (v : UInt64) (k : Src)
  | fap (r : Nat) (op : SrcOp) (a b : Nat) (k : Src)
  | ret (r : Nat)
deriving BEq, DecidableEq, Repr, Inhabited

/-- THE SOURCE SEMANTICS: the big-step fold over the binding env (the
LCNF evaluation discipline for the straight-line fragment — one env,
every let extends it, the ret reads it). -/
def evalS : Src → (Nat → UInt64) → UInt64
  | .lit r v k, env => evalS k (fun n => if n = r then v else env n)
  | .fap r op a b k, env =>
      evalS k (fun n => if n = r then opEval op (env a) (env b) else env n)
  | .ret r, env => env r

/-- THE MAP-RELATIVE semantics: the same fold with the node value from
the map's machine row (`machVal`) — what the compiled chain computes.
The honest map's `evalW` IS `evalS` (`evalW_opW` below); the sabotaged
map's differs — the control. -/
def evalW (w : SrcOp → Op) : Src → (Nat → UInt64) → UInt64
  | .lit r v k, env => evalW w k (fun n => if n = r then v else env n)
  | .fap r op a b k, env =>
      evalW w k (fun n => if n = r then machVal w op (env a) (env b) else env n)
  | .ret r, env => env r

/-- The chain's FINAL env (the bindings' composition — the machine's
locals' source shadow at the chain's end). -/
def envUpd (w : SrcOp → Op) : Src → (Nat → UInt64) → (Nat → UInt64)
  | .lit r v k, env => envUpd w k (fun n => if n = r then v else env n)
  | .fap r op a b k, env =>
      envUpd w k (fun n => if n = r then machVal w op (env a) (env b) else env n)
  | .ret _, env => env

/-- The well-scoped discipline: every index the chain names is a
declared local (below the budget `L`) — the Realizes invariant's
domain. -/
inductive Wf (L : Nat) : Src → Prop where
  | lit : ∀ r v k, r < L → Wf L k → Wf L (.lit r v k)
  | fap : ∀ r op a b k, a < L → b < L → r < L → Wf L k → Wf L (.fap r op a b k)
  | ret : ∀ r, r < L → Wf L (.ret r)

/-- THE CHAIN'S EXACT BUDGET (the fuel-sufficiency premise): the chain's
flat-step count — lit = const + set, fap = get + get + op + set, ret =
the read. The completion unit rides the corollary's `m ≥ 1`. -/
def need : Src → Nat
  | .lit _ _ k => need k + 2
  | .fap _ _ _ _ k => need k + 4
  | .ret _ => 1

/-! ## The compiled face (the lowering's emitted shape) -/

/-- THE COMPILED CHAIN: `emitLet`'s u64 rows verbatim (the literal's
const+set, the fap's left-to-right arg pushes + the map's op + the
set) — the template `Guest.Lower.lowerFunc` emits for these rows; the
extraction pins below compare the REAL lowering's output to it. -/
def compileChain (w : SrcOp → Op) : Src → List Instr
  | .lit r v k => [.i64const v.toNat, .localset r] ++ compileChain w k
  | .fap r op a b k =>
      [.localget a, .localget b, .op (w op), .localset r] ++ compileChain w k
  | .ret r => [.localget r]

/-- THE FUNCTION BODY (the exit-frame discipline, `declWalk`'s shape):
the chain inside the outermost frame, the return stored to the result
local and branched out, the result read after the frame — values never
ride the stack across the branch. -/
def fnBody (w : SrcOp → Op) (res : Nat) (e : Src) : List Instr :=
  [.block (compileChain w e ++ [.localset res, .br 0]), .localget res]

/-! ## The state relation (the Kripke extension's first consumer) -/

/-- THE STATE RELATION — §6's Kripke-style evolving relation (the
named extension's shape, `Kit.Kripke (Nat → UInt64) State Unit`: the
relation family indexed by the evolving source state `env`): the
machine state `s` realizes the source env — empty stack, every
declared local holding its env value boxed in i64. The chain induction
composes the per-primitive rows through this relation's evolution (the
env's), never a hidden assumption. -/
def Realizes (L : Nat) : Kit.Kripke (Nat → UInt64) State Unit :=
  fun env s _ => s.stack = [] ∧ ∀ n, n < L → s.locals n = Val.i64 (env n)

/-! ## The honest map's agreement (the value level) -/

/-- THE HONEST MAP's agreement: the map-relative semantics IS the
source semantics — the per-primitive rows composed through the ONE
fold induction (§6: the whole-program claim by structural induction,
once). -/
theorem evalW_opW : ∀ (e : Src) (env : Nat → UInt64),
    evalW opW e env = evalS e env := by
  intro e
  induction e with
  | lit r v k ih =>
      intro env; simp only [evalW, evalS]; rw [ih]
  | fap r op a b k ih =>
      intro env; simp only [evalW, evalS]
      rw [ih]
      congr 2
      funext n
      by_cases h : n = r
      · subst h; simp only [machVal_opW]
      · simp only [h, if_false]
  | ret r => intro env; rfl

/-! ## The state bookkeeping (the induction's hypothesis builders) -/

/-- The localset's written slot never leaks into the ≥ L branch (the
binding discipline's face: r < L, so the if-arm's join is trivial
outside the invariant's domain). -/
theorem locals_else (s : State) (L r : Nat) (v : Val) (hr : r < L) (n : Nat)
    (hn : L ≤ n) : (if n = r then v else s.locals n) = s.locals n := by
  have hne : n ≠ r := fun h => by omega
  simp [hne]

/-- The env's extension preserves the state relation (the lit node's
step face: the machine's localset wrote the SAME slot the env's
extension bound). -/
theorem realizes_lit (env : Nat → UInt64) (L : Nat) (r : Nat) (v : UInt64)
    (s : State) (hR : Realizes L env s ()) :
    Realizes L (fun n => if n = r then v else env n)
      { locals := fun n => if n = r then Val.i64 v else s.locals n
      , stack := [], mem := s.mem, memSize := s.memSize } () := by
  refine ⟨rfl, ?_⟩
  intro n hn
  by_cases hrn : n = r <;> simp [hrn, hR.2 n hn]

/-- The env's extension preserves the state relation (the fap node's
step face). -/
theorem realizes_fap (env : Nat → UInt64) (L : Nat) (r : Nat) (w : SrcOp → Op)
    (op : SrcOp) (a b : Nat) (s : State) (hR : Realizes L env s ()) :
    Realizes L (fun n => if n = r then machVal w op (env a) (env b) else env n)
      { locals := fun n => if n = r then Val.i64 (machVal w op (env a) (env b))
                           else s.locals n
      , stack := [], mem := s.mem, memSize := s.memSize } () := by
  refine ⟨rfl, ?_⟩
  intro n hn
  by_cases hrn : n = r <;> simp [hrn, hR.2 n hn]

/-! ## THE GENERIC CORRESPONDENCE (the chain theorem) -/

/-- THE PER-PRIMITIVE ROW PREMISE (written once): one `op` step pops
    the two pushed args and pushes the map-relative value, the state
    otherwise untouched — the chain theorems' shared premise, named so
    the theorem statements (and the two per-map rows below) cite it
    instead of spelling the step equation per theorem. -/
abbrev RowP (w : SrcOp → Op) : Prop :=
  ∀ (op : SrcOp) (x y : UInt64) (lcls : Nat → Val) (mem : Nat → UInt8)
    (msz : Nat),
    step { locals := lcls, stack := [Val.i64 y, Val.i64 x]
         , mem := mem, memSize := msz } (Instr.op (w op))
      = .ok { locals := lcls, stack := [Val.i64 (machVal w op x y)]
            , mem := mem, memSize := msz }

/-- THE PER-PRIMITIVE ROW AT THE MACHINE STEP (the honest map): the
map's op step takes the two pushed args to the source row's value —
the machine state otherwise untouched. Proved once per primitive
(`rfl` per row: `opPop`'s sig + `semOp`'s value + `machVal`'s spelling
are the ONE op table's faces of the same row). -/
theorem row_opW : RowP opW := by
  intro op x y lcls mem msz; cases op <;>
    simp [step, popTys, opPop, opSig, opRow, semOp, machVal, opW, tyOf]

/-- THE PER-PRIMITIVE ROW, the sabotaged map: `add`'s step computes
`x - y` — consistently the WRONG arithmetic, the SAME row shape (the
generic theorem consumes it verbatim: a wrong map is wrong
SYSTEMATICALLY, and the pinned disagreement below catches it). -/
theorem row_wBuggy : RowP wBuggy := by
  intro op x y lcls mem msz; cases op <;>
    simp [step, popTys, opPop, opSig, opRow, semOp, machVal, wBuggy, tyOf]

/-- THE LIT DECOMPOSITION (shared by both chain theorems): the const's
    push, then the set's write — the two steps the `lit` case walks. -/
theorem lit_steps {L : Nat} {env : Nat → UInt64} (r : Nat) (v : UInt64)
    {s : State} (hR : Realizes L env s ()) :
    step s (Instr.i64const v.toNat)
      = .ok { locals := s.locals, stack := [Val.i64 (v.toNat.toUInt64)]
            , mem := s.mem, memSize := s.memSize }
    ∧ step { locals := s.locals, stack := [Val.i64 (v.toNat.toUInt64)]
           , mem := s.mem, memSize := s.memSize } (Instr.localset r)
      = .ok { locals := fun n => if n = r then Val.i64 v else s.locals n
            , stack := [], mem := s.mem, memSize := s.memSize } :=
  ⟨by simp [step, hR.1], by simp [step]⟩

/-- THE FAP DECOMPOSITION (shared by both chain theorems): the two
    reads, the map's op row (`hrow`), the write — the four steps the
    `fap` case walks. -/
theorem fap_steps {L : Nat} {env : Nat → UInt64} {w : SrcOp → Op}
    (hrow : RowP w) (r : Nat) (op : SrcOp) (a b : Nat) {s : State}
    (hR : Realizes L env s ()) (ha : a < L) (hb : b < L) :
    step s (Instr.localget a)
      = .ok { locals := s.locals, stack := [Val.i64 (env a)]
            , mem := s.mem, memSize := s.memSize }
    ∧ step { locals := s.locals, stack := [Val.i64 (env a)]
           , mem := s.mem, memSize := s.memSize } (Instr.localget b)
      = .ok { locals := s.locals
            , stack := [Val.i64 (env b), Val.i64 (env a)]
            , mem := s.mem, memSize := s.memSize }
    ∧ step { locals := s.locals, stack := [Val.i64 (env b), Val.i64 (env a)]
           , mem := s.mem, memSize := s.memSize } (Instr.op (w op))
      = .ok { locals := s.locals
            , stack := [Val.i64 (machVal w op (env a) (env b))]
            , mem := s.mem, memSize := s.memSize }
    ∧ step { locals := s.locals
           , stack := [Val.i64 (machVal w op (env a) (env b))]
           , mem := s.mem, memSize := s.memSize } (Instr.localset r)
      = .ok { locals := fun n => if n = r
                  then Val.i64 (machVal w op (env a) (env b)) else s.locals n
            , stack := [], mem := s.mem, memSize := s.memSize } :=
  ⟨by simp [step, hR.2 a ha, hR.1], by simp [step, hR.2 b hb],
   hrow op (env a) (env b) s.locals s.mem s.memSize, by simp [step]⟩

/-- THE CHAIN THEOREM, the convergence leg (the fuel-sufficiency
premise in the statement): for ANY op map whose rows compute (`hrow` —
the per-primitive preservation rows, §6's box), the compiled chain's
execution at budget `m + need e` IS the map-relative semantics' run —
the value pushed on the (empty) entry stack, the bindings' env
evolution written to the locals, the suffix continuation riding the
final state. ONE induction over the chain; the per-primitive rows are
its only per-map input. -/
theorem run_chain (w : SrcOp → Op) (hrow : RowP w)
    (e : Src) : ∀ (mod : Module) (env : Nat → UInt64) (L m : Nat)
    (is : List Instr) (s : State), Wf L e → Realizes L env s () →
    execList mod (m + need e) s (compileChain w e ++ is)
      = execList mod m
          { s with
              locals :=
                (fun n => if n < L then Val.i64 (envUpd w e env n) else s.locals n),
              stack := [Val.i64 (evalW w e env)] } is := by
  induction e with
  | lit r v k ih =>
      intro mod env L m is s hwf hR
      cases hwf with
      | lit _ _ _ hr ihwf =>
        -- the two steps: the const's push, the set's write
        obtain ⟨h1, h2⟩ := lit_steps r v hR
        rw [show m + need (Src.lit r v k) = ((m + need k + 1) + 1) from by
          simp [need]; omega]
        simp only [compileChain, List.cons_append, List.nil_append, execList, h1, h2]
        rw [ih mod (fun n => if n = r then v else env n) L m is
          { locals := fun n => if n = r then Val.i64 v else s.locals n
          , stack := [], mem := s.mem, memSize := s.memSize }
          ihwf (realizes_lit env L r v s hR)]
        refine congrArg (fun st => execList mod m st is) ?_
        congr 1
        · funext n
          by_cases hn : n < L
          · simp [envUpd, hn]
          · have hle : L ≤ n := Nat.le_of_not_gt hn
            simp only [hn, if_false]
            rw [locals_else s L r (Val.i64 v) hr n hle]
  | fap r op a b k ih =>
      intro mod env L m is s hwf hR
      cases hwf with
      | fap _ _ _ _ _ ha hb hr ihwf =>
        -- the four steps: two reads, the map's op row, the write
        obtain ⟨h1, h2, h3, h4⟩ := fap_steps hrow r op a b hR ha hb
        rw [show m + need (Src.fap r op a b k)
              = ((((m + need k + 1) + 1) + 1) + 1) from by
          simp [need]; omega]
        simp only [compileChain, List.cons_append, List.nil_append, execList, h1, h2, h3, h4]
        rw [ih mod (fun n => if n = r then machVal w op (env a) (env b) else env n)
          L m is
          { locals := fun n => if n = r
                    then Val.i64 (machVal w op (env a) (env b)) else s.locals n
          , stack := [], mem := s.mem, memSize := s.memSize }
          ihwf (realizes_fap env L r w op a b s hR)]
        refine congrArg (fun st => execList mod m st is) ?_
        congr 1
        · funext n
          by_cases hn : n < L
          · simp [envUpd, hn]
          · have hle : L ≤ n := Nat.le_of_not_gt hn
            simp only [hn, if_false]
            rw [locals_else s L r (Val.i64 (machVal w op (env a) (env b))) hr n hle]
  | ret r =>
      intro mod env L m is s hwf hR
      cases hwf with
      | ret _ hr =>
        have h1 : step s (Instr.localget r)
            = .ok { locals := s.locals, stack := [Val.i64 (env r)]
                  , mem := s.mem, memSize := s.memSize } := by
          simp [step, hR.2 r hr, hR.1]
        simp only [compileChain, List.cons_append, List.nil_append]
        simp only [envUpd, evalW]
        refine congrArg (fun st => execList mod m st is) ?_
        congr 1
        · funext n
          by_cases hn : n < L
          · rw [hR.2 n hn]
            simp only [hn, if_pos]
          · simp only [hn, if_false, if_false]
        · rw [hR.2 r hr, hR.1]

/-- The zero-fuel contradiction, named once (the fuel-peel's absurd
    arm: budget 0 answers `.outOfFuel` — data, never a wrong state —
    so an `.ok` hypothesis at fuel 0 is vacuous). -/
theorem execList_zero_ok_absurd {m : Module} {s s' : State}
    {body : List Instr} (h : execList m 0 s body = .ok s') : False := by
  rw [execList_zero] at h
  exact absurd h (by simp)

/-- THE CHAIN THEOREM, the partial-correctness leg (fuel-INSENSITIVE,
the refinement's law): if the compiled chain's run answers `.ok` at
ANY budget, the final stack IS the map-relative semantics' value, and
the locals carry the bindings' env evolution. An underfueled run
answers `.outOfFuel` — data about the budget, never a wrong state.
(The run is over the chain ALONE — a suffix could add to the stack;
the composition face is `run_chain`'s equation.) -/
theorem run_chain_inv (w : SrcOp → Op) (hrow : RowP w)
    (e : Src) : ∀ (mod : Module) (env : Nat → UInt64) (L fuel : Nat) (s s' : State),
    Wf L e → Realizes L env s () →
    execList mod fuel s (compileChain w e) = .ok s' →
    s'.stack = [Val.i64 (evalW w e env)]
      ∧ (∀ n, n < L → s'.locals n = Val.i64 (envUpd w e env n)) := by
  induction e with
  | lit r v k ih =>
      intro mod env L fuel s s' hwf hR hok
      cases hwf with
      | lit _ _ _ hr ihwf =>
        cases fuel with
        | zero => exact (execList_zero_ok_absurd hok).elim
        | succ f =>
          obtain ⟨h1, h2⟩ := lit_steps r v hR
          rw [compileChain, List.cons_append] at hok
          simp only [execList, List.cons_append, h1] at hok
          cases f with
          | zero => exact (execList_zero_ok_absurd hok).elim
          | succ f' =>
          simp only [execList, h2] at hok
          obtain ⟨h1', h2'⟩ := ih mod (fun n => if n = r then v else env n) L f'
              { locals := fun n => if n = r then Val.i64 v else s.locals n
              , stack := [], mem := s.mem, memSize := s.memSize }
              s' ihwf (realizes_lit env L r v s hR) hok
          simp only [evalW, envUpd]
          exact ⟨h1', h2'⟩
  | fap r op a b k ih =>
      intro mod env L fuel s s' hwf hR hok
      cases hwf with
      | fap _ _ _ _ _ ha hb hr ihwf =>
        cases fuel with
        | zero => exact (execList_zero_ok_absurd hok).elim
        | succ f =>
          obtain ⟨h1, h2, h3, h4⟩ := fap_steps hrow r op a b hR ha hb
          rw [compileChain, List.cons_append] at hok
          simp only [execList, List.cons_append, h1] at hok
          cases f with
          | zero => exact (execList_zero_ok_absurd hok).elim
          | succ g1 =>
          simp only [execList, h2] at hok
          cases g1 with
          | zero => exact (execList_zero_ok_absurd hok).elim
          | succ g2 =>
          simp only [execList, h3] at hok
          cases g2 with
          | zero => exact (execList_zero_ok_absurd hok).elim
          | succ g3 =>
          simp only [execList, h4] at hok
          obtain ⟨h1', h2'⟩ :=
              ih mod (fun n => if n = r then machVal w op (env a) (env b) else env n)
              L g3
              { locals := fun n => if n = r
                          then Val.i64 (machVal w op (env a) (env b)) else s.locals n
              , stack := [], mem := s.mem, memSize := s.memSize }
              s' ihwf (realizes_fap env L r w op a b s hR) hok
          simp only [evalW, envUpd]
          exact ⟨h1', h2'⟩
  | ret r =>
      intro mod env L fuel s s' hwf hR hok
      cases hwf with
      | ret _ hr =>
        cases fuel with
        | zero => exact (execList_zero_ok_absurd hok).elim
        | succ f =>
          have h1 : step s (Instr.localget r)
              = .ok { locals := s.locals, stack := [Val.i64 (env r)]
                    , mem := s.mem, memSize := s.memSize } := by
            simp [step, hR.2 r hr, hR.1]
          rw [compileChain] at hok
          simp only [execList, h1] at hok
          cases f with
          | zero => exact (execList_zero_ok_absurd hok).elim
          | succ f' =>
          rw [execList_nil, Outcome.ok.injEq] at hok
          subst hok
          simp only [evalW, envUpd]
          exact ⟨trivial, hR.2⟩

/-! ## The exit-frame discipline (the fn-body face) -/

/-- THE EXIT-FRAME THEOREM (the fn-body face): the compiled body — the
chain inside the outermost frame, the return stored + branched, the
result read after the frame — at budget `need e + 3` executes to
EXACTLY the map-relative semantics' value on the stack, the result
local written, nothing else moved. The frame absorbs the branch; the
value rides the LOCAL, never the stack (the lowering's discipline). -/
theorem run_fnBody (w : SrcOp → Op) (hrow : RowP w)
    (e : Src) (mod : Module) (env : Nat → UInt64) (res L fuel : Nat) (s : State)
    (hwf : Wf L e) (hR : Realizes L env s ()) (hf : need e + 3 ≤ fuel) :
    execList mod fuel s (fnBody w res e)
      = .ok { s with
              locals := fun n => if n = res then Val.i64 (evalW w e env)
                                 else (if n < L then Val.i64 (envUpd w e env n)
                                       else s.locals n)
            , stack := [Val.i64 (evalW w e env)] } := by
  cases fuel with
  | zero => exact absurd hf (by omega)
  | succ f =>
    obtain ⟨k, rfl⟩ : ∃ k, f = k + (need e + 2) := ⟨f - (need e + 2), by omega⟩
    simp only [fnBody, execList]
    rw [show k + (need e + 2) = (k + 2) + need e from by omega]
    rw [run_chain w hrow e mod env L (k + 2) [Instr.localset res, Instr.br 0] s hwf hR]
    -- the tail: the set pops the value into the result local; the br
    -- raises the branch signal the frame absorbs
    have hT : execList mod (k + 2)
          { locals := (fun n => if n < L then Val.i64 (envUpd w e env n) else s.locals n)
          , stack := [Val.i64 (evalW w e env)], mem := s.mem, memSize := s.memSize }
          [Instr.localset res, Instr.br 0]
        = .branch (some 0)
          { locals := fun n => if n = res then Val.i64 (evalW w e env)
                               else (if n < L then Val.i64 (envUpd w e env n)
                                     else s.locals n)
          , stack := [], mem := s.mem, memSize := s.memSize } := by
      have hk : k + 2 = (k + 1) + 1 := by omega
      rw [hk]
      simp [execList, step]
    -- the frame absorbs the branch (`resume`'s `(some 0)` arm: the
    -- re-entry state rides the branch-point LOCALS, the frame-ENTRY
    -- stack restored); the result read closes at the normalized budget
    simp only [hT, hR.1]
    rw [show k + 2 + need e = (k + need e) + 1 + 1 from by omega]
    simp [resume, execList, step]

/-! ## The module face (the driver's runFunc) -/

/-- The u64 view of a machine value (the args' binding face; the i32
arm is the untyped-fallback the `hargs` premise excludes). -/
def u64Of : Val → UInt64
  | .i64 v => v
  | .i32 _ => 0

/-- THE TEMPLATE MODULE (one function, one export, no memory — the
shape `lowerFunc` emits for the fragment's parameterless decls). -/
def fnModuleW (w : SrcOp → Op) (e : Src) (p res L : Nat) : Module :=
  { types := [⟨List.replicate p ValType.i64, [ValType.i64]⟩]
  , funcs := [{ tyIdx := 0, locals := List.replicate L ValType.i64
              , body := fnBody w res e }]
  , exports := [{ name := "f", desc := ExportDesc.func 0 }] }

theorem localsDefault_replicate (L : Nat) :
    localsDefault? (List.replicate L ValType.i64)
      = some (List.replicate L (Val.i64 0)) := by
  induction L with
  | zero => rfl
  | succ n ih =>
      show (match valDefault? ValType.i64 with
            | none => none
            | some v => (localsDefault? (List.replicate n ValType.i64)).map (v :: ·))
        = some (Val.i64 0 :: List.replicate n (Val.i64 0))
      rw [valDefault?, ih]
      rfl

/-- The pop's split: the popped args are a PREFIX (the values, in pop
order), the rest the suffix. -/
theorem popTys_split : ∀ (pops : List ValType) (l args rest : List Val),
    popTys pops l = some (args, rest) → l = args ++ rest := by
  intro pops
  induction pops with
  | nil =>
      intro l args rest h
      rw [popTys, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.2, ← h.1]
      simp
  | cons t ts ih =>
      intro l args rest h
      cases l with
      | nil => simp [popTys] at h
      | cons v vs =>
          simp only [popTys] at h
          split at h
          · next ht =>
              cases hp : popTys ts vs with
              | none => rw [hp] at h; simp at h
              | some p =>
                  obtain ⟨a2, r2⟩ := p
                  rw [hp, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨h1, h2⟩ := h
                  subst h1
                  subst h2
                  rw [ih vs a2 r2 hp]
                  rfl
          · simp at h

/-- All-i64 args (the hargs premise's content, per element). -/
theorem all_i64 : ∀ (args : List Val) (p : Nat),
    stackTys args = List.replicate p ValType.i64 →
    ∀ v, v ∈ args → ∃ x, v = Val.i64 x := by
  intro args
  induction args with
  | nil => intro p h v hv; cases hv
  | cons v vs ih =>
      intro p h v' hv'
      cases p with
      | zero => simp [stackTys] at h
      | succ p' =>
          rw [stackTys, List.replicate_succ, List.cons.injEq] at h
          obtain ⟨h1, h2⟩ := h
          have hv : v' = v ∨ v' ∈ vs := by
            cases hv' with
            | head => exact Or.inl rfl
            | tail _ ht => exact Or.inr ht
          rcases hv with hv1 | ht
          · rw [hv1]
            cases v with
            | i32 n => simp [tyOf] at h1
            | i64 n => exact ⟨n, rfl⟩
          · exact ih p' h2 v' ht

/-- The stackTys fold preserves the length (the args' length face). -/
theorem stackTys_len : ∀ l : List Val, (stackTys l).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [stackTys, List.length_cons]; exact congrArg Nat.succ ih

/-- THE MODULE FACE (the mandate's `runModule … = the source's value`
shape): the template module's entry, run by the DRIVER on i64 args
(the executor's convention: args head = TOP = the last param), at
budget `fuel ≥ need e + 3`, returns the source semantics' value — the
env is the args' binding (param i = the i-th arg in push order). -/
theorem fnModule_ok (w : SrcOp → Op) (hrow : RowP w)
    (e : Src) (env : Nat → UInt64) (args : List Val) (p res L fuel : Nat)
    (hwf : Wf (p + L) e) (hf : need e + 3 ≤ fuel)
    (hargs : stackTys args = List.replicate p ValType.i64)
    (henv : ∀ n, n < p + L →
      env n = u64Of ((args.reverse ++ List.replicate L (Val.i64 0)).getD n (Val.i32 0))) :
    ∃ s', runFunc (fnModuleW w e p res L) 0 args fuel = .ok s'
      ∧ s'.stack = [Val.i64 (evalW w e env)] := by
  have hargsI64 := all_i64 args p hargs
  -- the args' element type pins the length (the stackTys fold's face)
  have hlen : args.length = p := by
    rw [← stackTys_len, hargs, List.length_replicate]
  -- the driver's init state (the args bound over the defaults, the
  -- zeroed page)
  let INIT : State :=
    { locals := fun n => (args.reverse ++ List.replicate L (Val.i64 0)).getD n (Val.i32 0)
    , stack := [], mem := zeroMem, memSize := 0 }
  have hrun : runFunc (fnModuleW w e p res L) 0 args fuel
      = finishRun (execList (fnModuleW w e p res L) fuel
          INIT
          (fnBody w res e)) := by
    simp only [runFunc, fnModuleW, Module.typeAt, List.getElem?_cons_zero,
      List.reverse_replicate]
    obtain ⟨bound, rest, hpop, hbd, hrest⟩ :=
      popTys_of_stackTys (List.replicate p ValType.i64) args []
        (by rw [List.append_nil]; exact hargs)
    have hr0 : rest = [] := nil_of_stackTys_nil rest hrest
    have hba : args = bound := by
      rw [popTys_split (List.replicate p ValType.i64) args bound rest hpop, hr0,
        List.append_nil]
    subst hba
    simp only [hpop, hr0, localsDefault_replicate]
    rfl
  -- the init state realizes the env (the args' binding face)
  have hR : Realizes (p + L) env INIT () := by
    refine ⟨rfl, fun n hn => ?_⟩
    -- the reverse's length face (both branches)
    have hrl : (args.reverse).length = p := by
      rw [List.length_reverse]; exact hlen
    by_cases hnp : n < p
    · -- the args' region: the reverse's index n reads args[p-1-n]
      have hget : (args.reverse ++ List.replicate L (Val.i64 0)).getD n (Val.i32 0)
          = args[p - 1 - n]?.getD (Val.i32 0) := by
        show (args.reverse ++ List.replicate L (Val.i64 0))[n]?.getD (Val.i32 0)
            = args[p - 1 - n]?.getD (Val.i32 0)
        rw [List.getElem?_append_left (by omega),
          List.getElem?_reverse' (j := p - 1 - n) (by omega)]
      obtain ⟨v, hv⟩ : ∃ v, args[p - 1 - n]? = some v := by
        cases hq : args[p - 1 - n]? with
        | none => rw [List.getElem?_eq_none_iff] at hq; exact absurd hq (by omega)
        | some v => exact ⟨v, rfl⟩
      have hmem : v ∈ args := List.mem_of_getElem? hv
      obtain ⟨x, hx⟩ := hargsI64 v hmem
      rw [henv n hn, hget, hv, Option.getD_some, hx]
      show (args.reverse ++ List.replicate L (Val.i64 0)).getD n (Val.i32 0) = Val.i64 x
      rw [hget, hv, Option.getD_some, hx]
    · -- the defaults' region: the zero box
      have hge : p ≤ n := by omega
      have hlt : n - p < L := by omega
      rw [henv n hn]
      show (args.reverse ++ List.replicate L (Val.i64 0)).getD n (Val.i32 0)
          = Val.i64 (u64Of ((args.reverse ++ List.replicate L (Val.i64 0)).getD n (Val.i32 0)))
      simp [List.getD,
        List.getElem?_append_right (show (args.reverse).length ≤ n from by omega), hlt, hlen,
        u64Of]
  -- the body's run (the exit-frame theorem), then the driver's finish
  have hclaim := run_fnBody w hrow e (fnModuleW w e p res L) env res (p + L) fuel
    INIT hwf hR hf
  have hrun2 : runFunc (fnModuleW w e p res L) 0 args fuel
      = .ok { INIT with
              locals := (fun n => if n = res then Val.i64 (evalW w e env) else (if n < p + L then Val.i64 (envUpd w e env n) else INIT.locals n)),
              stack := [Val.i64 (evalW w e env)] } := by
    rw [hrun]
    simp only [INIT]
    rw [hclaim]
    simp only [INIT]
    rfl
  exact ⟨_, hrun2, rfl⟩

/-! ## The pinned program + the controls (the wrong-lowering bug class) -/

/-- THE ADDER's IR decl, hand-written (the IR-face pin — the toy
frontend's pin rides the IR: it is the whole contract): params a b; `let c := binop u64add [a, b];
return c`. The REAL lowering runs on it below — total and pure, so the
extraction pin compares full Func VALUES at build time. The
param/result rows ride the executor's convention: params bind locals
0,1 in order, the result local is next (2), the let binding follows
(3) — the same machine coordinates `adderSrc` spells. -/
def adderDecl : IR.Decl :=
  { name := "adder"
  , params := [("a", .u64), ("b", .u64)]
  , resultTy := .u64
  , value :=
      .let_ { var := "c", ty := .u64
            , value := .binop .u64add #[.var "a", .var "b"] }
      (.ret "c") }

/-- THE ADDER's source shadow (the machine-coordinate distillation of
`adderDecl`: params a b → locals 0,1; the result local 2; the binding
c → local 3). -/
def adderSrc : Src := .fap 3 .add 0 1 (.ret 3)

/-- The adder's Wf (all indices below the locals budget 4). -/
theorem adderWf : Wf 4 adderSrc :=
  Wf.fap (r := 3) (op := .add) (a := 0) (b := 1) (k := .ret 3)
    (by decide) (by decide) (by decide) (Wf.ret (r := 3) (by decide))

/-- The adder's Wf at the module's budget (p + L = 2 + 4). -/
theorem adderWf6 : Wf 6 adderSrc :=
  Wf.fap (r := 3) (op := .add) (a := 0) (b := 1) (k := .ret 3)
    (by decide) (by decide) (by decide) (Wf.ret (r := 3) (by decide))

/-- The adder's env (param 0 = 40, param 1 = 2 — the duel's own
values). -/
def env40 : Nat → UInt64 := fun n => if n = 0 then 40 else if n = 1 then 2 else 0

/-- The adder's args (the driver's convention: head = TOP = the LAST
param — param 0 = 40, param 1 = 2). -/
def adderArgs : List Val := [Val.i64 2, Val.i64 40]

/-- THE SOURCE VALUE: the source semantics computes 42. -/
theorem adder_value : evalS adderSrc env40 = 42 := rfl

/-- THE HONEST RUN: the template module's entry, driven by `runFunc`,
returns the SOURCE semantics' value — the mandate's `runModule … = the
source's value` shape, kernel-checked. -/
theorem adder_run :
    ∃ s', runFunc (fnModuleW opW adderSrc 2 2 4) 0 adderArgs 20 = .ok s'
      ∧ s'.stack = [Val.i64 (evalS adderSrc env40)] := by
  have h := fnModule_ok opW row_opW adderSrc env40 adderArgs 2 2 4 20
    adderWf6 (by decide)
    (by simp [adderArgs, stackTys])
    (by
      intro n hn
      revert n hn
      decide)
  obtain ⟨s', hr, hs⟩ := h
  exact ⟨s', hr, by rw [← evalW_opW, hs]⟩

/-- THE CONTROL'S EXECUTION: the SABOTAGED map's module (the same
template, `add` compiled to `i64sub`) runs to the WRONG value 38 —
consistently, by the SAME generic theorem (the map's rows are its only
input). -/
theorem buggy_run :
    ∃ s', runFunc (fnModuleW wBuggy adderSrc 2 2 4) 0 adderArgs 20 = .ok s'
      ∧ s'.stack = [Val.i64 38] := by
  have h := fnModule_ok wBuggy row_wBuggy adderSrc env40 adderArgs 2 2 4 20
    adderWf6 (by decide)
    (by simp [adderArgs, stackTys])
    (by
      intro n hn
      revert n hn
      decide)
  obtain ⟨s', hr, hs⟩ := h
  exact ⟨s', hr, by rw [hs]; rfl⟩

/-- THE NEGATIVE CONTROL (a THEOREM, not a hope): the sabotaged
map's execution DISAGREES with the source value — a wrong lowering
produces a wrong execution, and the pinned disagreement catches the
bug class. -/
theorem buggy_disagrees :
    evalW wBuggy adderSrc env40 ≠ evalS adderSrc env40 := by
  rw [adder_value]
  decide

/-! ## The extraction pins (the real lowering's output = the templates) -/

/-- THE EXTRACTION PIN (the legacy's build-failing discipline): the
REAL lowering's output for the adder decl IS the template the theorems
speak about — the full `Func` VALUE compared (body + locals + type
index), not a rendering. A regression that changes the emission breaks
the build. -/
def adderExtraction : Bool :=
  match Guest.lowerFunc adderDecl with
  | .ok m =>
      m.funcs[0]? == some { tyIdx := 0
                          , locals := [ValType.i64, ValType.i64]
                          , body := fnBody opW 2 adderSrc }
  | .error _ => false

/-- The control's face: the SABOTAGED template is NOT what the real
lowering emits. -/
def adderExtractionBuggy : Bool :=
  match Guest.lowerFunc adderDecl with
  | .ok m =>
      m.funcs[0]?.map (·.body) == some (fnBody wBuggy 2 adderSrc)
  | .error _ => false

-- BUILD-FAILING: the real lowering's output = the honest template.
#guard adderExtraction = true

-- BUILD-FAILING: the sabotaged template ≠ the real emission (the
-- control's honesty).
#guard adderExtractionBuggy = false

-- BUILD-FAILING, the END-TO-END extraction: the REAL lowering's
-- module, driven by the REAL executor, returns the source semantics'
-- value 42.
#guard (match Guest.lowerFunc adderDecl with
        | .ok m =>
            match runFunc m 0 adderArgs 20 with
            | .ok s' => s'.stack == [Val.i64 (evalS adderSrc env40)]
            | _ => false
        | .error _ => false)

end Guest.Correct
