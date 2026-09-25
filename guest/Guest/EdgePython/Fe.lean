/-
# Guest.EdgePython.Fe — the Py AST → Guest.IR lowering (the frontend's product)

Owner: the guest lane's SECOND FRONTEND. THE POINT: every emitted
constructor is a `Guest.IR` constructor — ZERO new constructors. The IR
seam is the frontend-agnostic contract (`Guest.IR`'s header: the
frontends are per-language, THIS module is what they all produce), and
the second frontend targets it unchanged — the multi-frontend doctrine's
payoff, mined from `legacy/lean/edgepython/EdgePython/Compiler.lean`
(the legacy emitted the frozen WAT AST directly; the tree's doctrine
splits the seam — the IR in between, `Guest.Lower` shared).

The translation (the legacy's discipline, retargeted):

* Python `int` = the IR `u64` row (the exported surface); Python `bool`
  = the IR `bool` row (the `cases_` condition's i32 repr).
* expressions are ANF'd: every sub-expression one `let` (the IR's ANF
  discipline — one let spine, every value form a variable reference);
  a fresh IR variable per binding (the source name + a supply suffix —
  rebinding shadows, never reuses).
* `if c: t else: e` → `cases_` on the bool via the VALUE lane, `true`
  = ctor 1, `false` = ctor 0; the statements AFTER the `if` ride BOTH
  arms (the env-carrying-continuation translation — each arm's
  post-env feeds the SAME tail, which is exactly Python's
  branch-local assignment semantics).
* `while c: body` → THE JP LOOP SHAPE (the `Guest.Lower.loopEntry`
  discipline's shape, read off the lowering's detector):
  `jp L(ms…) = cases c | true => body…; jmp L(ms…') | false => rest`
  with the entry `jmp L(ms⁰)` — the loop-carried vars `ms` (the body's
  assignment targets, in first-assignment order) are the jp's params;
  the loop-back jmp's args are the values at the END of the body (per
  path — the env-carrying continuation); the loop's EXIT is the false
  arm, where the statements AFTER the loop ride (they see the
  LAST-iteration values — the jp params).
  The loop-entry discipline holds: the continuation is the bare entry
  `jmp` (the zero-let spine `splitEntry` accepts).
* calls → the IR's `call` (the cross-decl sibling lane; the module's
  decl order IS the function-table indices, self-recursion included).

THE NAMED BOUNDARY (beyond Ast.lean's exclusions): a loop-carried
variable (assigned in a `while` body) must be bound BEFORE the loop —
a first assignment inside the body refuses (the loop's entry args
would be unbound; Python's loop-scoped-variable face is the named
follow-up).

The composed pipeline (`compileModule`): parse → check → lower to the
IR → `Guest.lowerFuncs` (the SHARED lowering — the second frontend's
conformance evidence that the IR is the whole contract). Every refusal
renders through the ONE envelope (`Guest.LowerError` → `Kit.Diag`); no
new E-codes (the closed vocabulary's extension is compiler-driven).

The five questions (notes/v3/01-core.md):

- **Root**: none — a frontend fold (the input face of the lane).
- **Carrier grade**: none — the output is the IR's own data; the
  refusals ride the shared envelope.
- **Spine reading**: the Py AST is the registry-content this frontend
  folds into the IR spine (`Guest.Lower`'s spine).
- **Ladder rung**: n/a (the IR is closed data; the fold is total over
  it — the statement folds ride the explicit `sizeOf` measures, the
  expression folds are structural).
- **Gate row**: the Guest row (Gates.Packages).
-/

import Guest.IR
import Guest.Lower
import Guest.Frontend
import Guest.EdgePython.Ast
import Guest.EdgePython.Check
import Guest.EdgePython.Parse

namespace Guest.EdgePython.Fe

open Guest
open Guest.EdgePython.Py Guest.EdgePython.Check

/-! ## The rows -/

/-- The Python type → the IR row: `int` = the u64 row (the exported
    surface), `bool` = the i32-repr row (the condition type). -/
def rowOf : Ty → IR.Ty
  | .int => .u64
  | .bool => .bool

/-- The arithmetic op's row. -/
def opBinop : BinOp → IR.Binop
  | .add => .u64add
  | .sub => .u64sub
  | .mul => .u64mul

/-- The comparison op's row (the op surface's ONLY u64 compares). -/
def opCmp : CmpOp → IR.Binop
  | .lt => .u64ltu
  | .eq => .u64eq

/-! ## The size substrate (the statement folds' measures — the
##    Lcnf discipline: explicit total measures over a foreign fold) -/

/-- The OWNED measure (the derived `sizeOf`'s ctor faces are not
    rfl-transparent, so the fold carries its own count — the same
    discipline as the Lcnf's explicit measures, fully under our
    control). -/
def msE : Expr → Nat
  | .int _ => 1
  | .boolV _ => 1
  | .var _ => 1
  | .bin _ l r => 1 + msE l + msE r
  | .cmp _ l r => 1 + msE l + msE r
  | .call _ args => 1 + args.foldl (fun n a => n + msE a) 0

mutual
def msS : Stmt → Nat
  | .assign _ e => 1 + msE e
  | .ret e => 1 + msE e
  | .ifelse c t e => 1 + msE c + msL t + msL e
  | .while c body => 1 + msE c + msL body
def msL : List Stmt → Nat
  | [] => 1
  | s :: ss => 1 + msS s + msL ss
end

-- the rfl faces of the OWNED measure (the equations the decreasing
-- proofs fold — the derived sizeOf's ctor faces are not rfl, these are)
theorem msL_nil : msL [] = 1 := rfl
theorem msL_cons (s : Stmt) (ss : List Stmt) :
    msL (s :: ss) = 1 + msS s + msL ss := rfl
theorem msS_assign (x : String) (e : Expr) :
    msS (Stmt.assign x e) = 1 + msE e := rfl
theorem msS_ret (e : Expr) :
    msS (Stmt.ret e) = 1 + msE e := rfl
theorem msS_ifelse (c : Expr) (t e : List Stmt) :
    msS (Stmt.ifelse c t e) = 1 + msE c + msL t + msL e := rfl
theorem msS_while (c : Expr) (body : List Stmt) :
    msS (Stmt.while c body) = 1 + msE c + msL body := rfl

/-! ## The fold state -/

/-- The variable binding: source name → the IR variable + its row. -/
abbrev Env := List (String × (IR.Var × IR.Ty))

def lookupEnv (env : Env) (x : String) : Option (IR.Var × IR.Ty) :=
  match env with
  | [] => none
  | (y, b) :: rest => if y == x then some b else lookupEnv rest x

/-- The frontend fold's monad: the fresh-variable supply over the
    shared refusal envelope. -/
abbrev FM := StateT Nat (Except LowerError)

/-- A fresh IR variable (the source base + the supply suffix — unique
    within the module's fold). -/
def fresh (base : String) : FM IR.Var := do
  let n ← get
  set (n + 1)
  pure (base ++ "!" ++ toString n)

/-! ## The expression fold (the ANF face) -/

/-- One expression → the let spine + the result variable + its row.
    Expressions carry NO control flow (the fragment's discipline), so
    the product is straight lets. -/
def compE (env : Env) : Expr →
    FM (List IR.LetDecl × IR.Var × IR.Ty)
  | .int n => do
      let v ← fresh "lit"
      pure ([{ var := v, ty := .u64, value := .litU64 n }], v, .u64)
  | .boolV b => do
      let v ← fresh "lit"
      pure ([{ var := v, ty := .bool
             , value := .litU32 (if b then 1 else 0) }], v, .bool)
  | .var x =>
      match lookupEnv env x with
      | some (v, t) => pure ([], v, t)
      | none => throw (.unboundFVar x)
  | .bin op l r => do
      let (ll, lv, _) ← compE env l
      let (rl, rv, _) ← compE env r
      let v ← fresh "bin"
      pure (ll ++ rl
            ++ [{ var := v, ty := .u64
                , value := .binop (opBinop op) #[.var lv, .var rv] }],
            v, .u64)
  | .cmp op l r => do
      let (ll, lv, _) ← compE env l
      let (rl, rv, _) ← compE env r
      let v ← fresh "cmp"
      pure (ll ++ rl
            ++ [{ var := v, ty := .bool
                , value := .binop (opCmp op) #[.var lv, .var rv] }],
            v, .bool)
  | .call f args => do
      let (als, avs) ← compEs env args
      let v ← fresh "call"
      let callArgs : Array IR.Arg := avs.toArray.map (fun a => .var a)
      pure (als
            ++ [{ var := v, ty := .u64, value := .call f callArgs }],
            v, .u64)
where
  -- the args' fold (the explicit list recursion — the higher-order
  -- foldlM face would break the structural inference)
  compEs (env : Env) : List Expr →
      FM (List IR.LetDecl × List IR.Var)
    | [] => pure ([], [])
    | a :: rest => do
      let (l1, v1, _) ← compE env a
      let (l2, vs) ← compEs env rest
      pure (l1 ++ l2, v1 :: vs)

/-! ## The assignment-target collector (the loop-carried vars' order) -/

/-- The assignment targets, FIRST-occurrence order, threaded through an
    accumulator (structural on the list — no append-in-recursive-
    position). -/
def assignedVarsAcc (acc : List String) :
    List Stmt → List String
  | [] => acc
  | .assign x _ :: ss =>
      assignedVarsAcc (if acc.contains x then acc else acc ++ [x]) ss
  | .ret _ :: ss => assignedVarsAcc acc ss
  | .ifelse _ t e :: ss =>
      assignedVarsAcc (assignedVarsAcc (assignedVarsAcc acc t) e) ss
  | .while _ body :: ss =>
      assignedVarsAcc (assignedVarsAcc acc body) ss

/-- The body's assignment targets in first-assignment order (the jp
    params' order — determinism for the loop shape). -/
def assignedVars (body : List Stmt) : List String :=
  assignedVarsAcc [] body

/-! ## The statement fold (the control forms) -/

/-- The statement list fold: `ss` translated against `env`; the
    continuation `k` receives the POST-FOLD env — the loop-back jmp's
    args are the values at the END of the body (per path: a branch's
    assignments ride its own path's jmp). Returns the code for
    `ss ++ (k env')` where env' is the post-fold env. -/
def compSs (env : Env) : List Stmt → (Env → FM IR.Code) → FM IR.Code
  | [], k => k env
  | .assign x e :: rest, k => do
      let (lets, v, t) ← compE env e
      let restC ← compSs ((x, (v, t)) :: env) rest k
      pure (lets.foldr IR.Code.let_ restC)
  | .ret e :: _, _ => do
      let (lets, v, _) ← compE env e
      pure (lets.foldr IR.Code.let_ (IR.Code.ret v))
  | .ifelse c t e :: rest, k => do
      let (clets, cv, ct) ← compE env c
      if ct != .bool then
        throw (.unsupportedConstruct "if condition"
          "the condition must be bool-typed (the checker's contract — \
           this is the lowering-side defense)")
      -- the continuation rides BOTH arms (the branch-local assignment
      -- semantics: each arm's post-env feeds the SAME continuation —
      -- the values the branch bound are the ones the tail reads)
      let thenC ← compSs env t (fun envT => compSs envT rest k)
      let elseC ← compSs env e (fun envE => compSs envE rest k)
      pure (clets.foldr IR.Code.let_
        (IR.Code.cases_ "if" .value cv
          [IR.Alt.ctorAlt 1 thenC, IR.Alt.ctorAlt 0 elseC]))
  | .while c body :: rest, k => do
      -- THE JP LOOP SHAPE (the module header's derivation)
      let ms := assignedVars body
      -- every loop-carried var must be bound at loop entry
      for x in ms do
        match lookupEnv env x with
        | some _ => pure ()
        | none =>
            throw (.unsupportedConstruct s!"loop-carried variable {x}"
              "first assigned inside the while body — a loop-carried \
               variable must be bound BEFORE the loop (the entry args' \
               face; the named boundary)")
      let jpName ← fresh "loop"
      -- the jp params: the loop-carried vars, first-assignment order
      let params ← ms.foldlM (fun acc x => do
        match lookupEnv env x with
        | some (_, t) => do
            let p ← fresh x
            pure (acc ++ [(p, t)])
        | none => throw (.unboundFVar x)) []
      -- the body's env: the loop-carried vars ARE the params (ms.zip
      -- pairs the source name with its (param var, row) binding)
      let envLoop : Env := ms.zip params ++ env
      let (clets, cv, ct) ← compE envLoop c
      if ct != .bool then
        throw (.unsupportedConstruct "while condition"
          "the condition must be bool-typed (the checker's contract — \
           this is the lowering-side defense)")
      -- the loop-back jmp: the args are the loop-carried vars' values
      -- at the END of the body (the post-body env — per path)
      let bodyC ← compSs envLoop body (fun envAfter => pure
        (.jmp jpName
          ((ms.filterMap (lookupEnv envAfter)).toArray.map
            (fun b => IR.Arg.var b.1))))
      -- the EXIT arm: the statements after the loop (the last
      -- iteration's values — the params)
      let exitC ← compSs envLoop rest (fun _ => k envLoop)
      -- the ENTRY: the pre-loop bindings
      let entryArgs : Array IR.Arg :=
        (ms.filterMap (lookupEnv env)).toArray.map (fun b => .var b.1)
      let value : IR.Code :=
        clets.foldr IR.Code.let_
          (IR.Code.cases_ "while" .value cv
            [IR.Alt.ctorAlt 1 bodyC, IR.Alt.ctorAlt 0 exitC])
      pure (IR.Code.jp jpName params value (.jmp jpName entryArgs))
  termination_by ss => msL ss
  decreasing_by
    all_goals
      (simp only [msL_cons, msS_assign, msS_ifelse, msS_while]
       omega)

/-! ## The decl fold -/

/-- One function → one IR decl: the params u64 (the exported surface),
    the result u64, the body's fold ending in `unreach` (fall-off-the-end
    is outside the surface — the legacy discipline). -/
def compFn (f : Fn) (types : List (String × Ty)) : FM IR.Decl := do
  let params ← f.params.foldlM (fun acc p => do
    let v ← fresh p
    pure (acc ++ [(p, (v, IR.Ty.u64))])) []
  let env0 : Env := params.map (fun p => (p.1, (p.2.1, p.2.2)))
  let _types := types  -- the checker's merged env: consumed by the
                       -- row checks at each site (rowOf/compE); kept
                       -- in the signature as the two folds' joint face
  let body ← compSs env0 f.body (fun _ => pure .unreach)
  pure { name := f.name
       , params := env0.map (fun p => (p.2.1, p.2.2))
       , resultTy := .u64
       , value := body }

/-- The program → the IR decls: the checker first (its refusal is the
    named `unsupportedConstruct` — the checker's Option gate has no
    detail payload), then the fold (the supply threads across decls —
    IR variables are module-unique). -/
def lowerProgram (fns : List Py.Fn) :
    Except LowerError (List IR.Decl) := do
  match Check.checkModule fns with
  | none =>
      .error (.unsupportedConstruct "the type checker refused the module"
        "a bool-typed call arg, a non-bool condition, a non-int \
         return, a branch-merge type clash, or a duplicate name — \
         Check.lean's refusals")
  | some tss =>
      let act : FM (List IR.Decl) :=
        (fns.zip tss).foldlM (fun acc p => do
          let d ← compFn p.1 p.2
          pure (acc ++ [d])) []
      match StateT.run act 0 with
      | .ok (ds, _) => .ok ds
      | .error e => .error e

/-! ## The composed pipeline -/

/-- THE PIPELINE: the surface text → the parsed ASTs → the checked
    types → the IR decls → the SHARED lowering → the wasm module (the
    tail is the kit's `Frontend.link` — the ONE rendering at the
    driver's String boundary). The second frontend's conformance face:
    every stage below the parse is the tree's own machinery unchanged. -/
def compileModule (text : String) : Except String WasmCore.Module := do
  let fns ← match Guest.EdgePython.Parse.parseProgram text with
    | .ok fns => pure fns
    | .error e => .error e
  match Frontend.link (lowerProgram fns) with
    | .ok m => .ok m
    | .error e => .error e.render

end Guest.EdgePython.Fe
