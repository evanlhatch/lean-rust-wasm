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
  = the IR `bool` row (the `cases_` condition's i32 repr); tuples and
  lists = the IR `obj` row (the ctor objects).
* expressions are ANF'd: every sub-expression one `let` (the IR's ANF
  discipline — one let spine, every value form a variable reference);
  a fresh IR variable per binding (the source name + a supply suffix —
  rebinding shadows, never reuses).
* the comparison/logic spellings ride the op surface's EXISTING rows
  (zero new Binops): `>` = `u64ltu` with the operands SWAPPED; `<=` /
  `>=` / `!=` = the (swapped) row then `1 - x` (the `u32sub` not-face
  over the 0/1 bool repr); `not x` = `u32sub(1, x)`; `and` = `u32mul`
  (the 0/1 ring's meet); `or` = `a + b - a*b` (the ring's join); unary
  minus = `u64sub(0, x)` (the ring's negation). EAGER — Python's
  short-circuit is the named divergence (the module header's note in
  `Ast`).
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
* `for x in xs: body` → THE SAME JP LOOP SHAPE over the LIST OBJECT's
  tag (the `cases_` TAG lane — the cons-walk discipline):
  `cur = xs; jp L(cur, ms…) = cases tag cur | cons(1) => x := head(cur);
  tail := tail(cur); body…; jmp L(tail, ms…') | nil(0) => rest` with
  the entry `jmp L(cur⁰, ms⁰)`. The list repr is the cons-object
  family the ctor face builds: nil = the payload-free ctor object
  (tag 0), cons = the two-field object (tag 1) — for an int element
  the packing law puts the ref tail in slot 0 and the u64 head in the
  scalar region (base slot 1); for an object element both fields are
  refs (head slot 0, tail slot 1). The for-variable does NOT leak past
  the loop unless the body assigns it (Python leaks the last element —
  the named boundary).
* tuples `(a, b, …)` → the ctor object (tag 0) with the elements as
  fields — the PACKING LAW's coordinates (refs first, then u64 scalars
  by offset); `t[i]` with a LITERAL i → the `oproj`/`sproj` read at
  the SAME coordinates (the packing recomputed source-side). Lists
  `[a, b, …]` → the nested cons objects; `xs[0]` → the head read.
* calls → the IR's `call` (the cross-decl sibling lane; the module's
  decl order IS the function-table indices, self-recursion included).

THE NAMED BOUNDARIES (beyond Ast.lean's exclusions): a loop-carried
variable (assigned in a `while`/`for` body) must be bound BEFORE the
loop — a first assignment inside the body refuses (the loop's entry
args would be unbound); list indexing past the head has no bounds
check to ride (the length is not stored — the bounds-checked walk is
the named follow-up); STRINGS refuse (the IR carries no string value
row — `Guest.IR.Ty`'s closed set: u64/u32/u8/bool/char/enum + the
object rows; byte-lists land with lists, but concatenation and
equality need either a string row or the growing-object discipline —
the named deferral, the honest report for E6 item 1); `%` refuses
(no rem row in the IR's `Binop` set — the same report).

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
    surface), `bool` = the i32-repr row (the condition type), tuples
    and lists = the object row (the ctor objects). -/
def rowOf : Ty → IR.Ty
  | .int => .u64
  | .bool => .bool
  | .tup _ => .obj
  | .list _ => .obj

/-- The arithmetic op's row (`and`/`or` ride the u32 lane — the bools'
    i32 repr; `or` is a THREE-op spelling, see `compE`). -/
def opBinop : BinOp → IR.Binop
  | .add => .u64add
  | .sub => .u64sub
  | .mul => .u64mul
  | .and => .u32mul

/-- The comparison op's row — the op surface's u64 compares; the
    swapped/negated spellings live in `compE`. -/
def opCmp : CmpOp → IR.Binop
  | .lt => .u64ltu
  | .eq => .u64eq
  | _ => .u64eq  -- unreachable (the swapped spellings never hit this)

/-- The machine's u64 cap (the literal refusal's face). -/
def u64Cap : Nat := 18446744073709551616

/-! ## The packing-law coordinates (the ctor face's read-back) -/

/-- A tuple/list element's field class: refs (tuple/list elements) take
    the slots first, u64 scalars pack after (a bool element has no
    class — the checker's refusal). -/
def elemRef (t : Ty) : Bool :=
  match t with
  | .int => false
  | .bool => false  -- unreachable (the checker's class-set refusal)
  | .tup _ | .list _ => true

/-- The element's read coordinates for the object whose fields are the
    source-order element types `ts`, reading field `i`:
    `(isRef, slotOrBase, offset)` — a ref element reads `oproj slot`;
    a u64 element reads `sproj base offset` (base = the ref count —
    the scalar region's first slot; offset = the same-class packing).
    THE SAME packing law the lowering's ctor face writes. -/
def elemCoords (ts : List Ty) (i : Nat) : Bool × Nat × Nat :=
  let before := ts.take i
  let nRefs := (ts.filter elemRef).length
  if elemRef (ts.get? i |>.getD .int) then
    (true, (before.filter elemRef).length, 0)
  else
    (false, nRefs, (before.filter (fun t => !elemRef t)).length * 8)

/-- The cons object's coordinates for element type `t`: the head read
    and the tail's slot (the cons ctor's args are [head, tail] — the
    packing law's order does the rest). -/
def consCoords (t : Ty) : Bool × Nat × Nat :=
  if elemRef t then (true, 0, 0)          -- both refs: head slot 0
  else (false, 1, 0)                      -- tail ref slot 0, head u64 @base 1

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
  | .un _ e => 1 + msE e
  | .tup es => 1 + es.foldl (fun n a => n + msE a) 0
  | .listLit es => 1 + es.foldl (fun n a => n + msE a) 0
  | .idx b i => 1 + msE b + msE i
  | .call _ args => 1 + args.foldl (fun n a => n + msE a) 0

mutual
def msS : Stmt → Nat
  | .assign _ e => 1 + msE e
  | .ret e => 1 + msE e
  | .ifelse c t e => 1 + msE c + msL t + msL e
  | .while c body => 1 + msE c + msL body
  | .forIn _ xs body => 1 + msE xs + msL body
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
theorem msS_forIn (x : String) (xs : Expr) (body : List Stmt) :
    msS (Stmt.forIn x xs body) = 1 + msE xs + msL body := rfl

/-! ## The fold state -/

/-- The variable binding: source name → the IR variable + its SOURCE
    type (the element types' faces — tuple/list/index reads — need the
    tuple/list shape, which the IR row erases; `rowOf` delivers the IR
    row where a let needs it). -/
abbrev Env := List (String × (IR.Var × Ty))

def lookupEnv (env : Env) (x : String) : Option (IR.Var × Ty) :=
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

/-- The cons chain (the right fold over the element vars — nil first,
    one cons ctor per element). -/
def buildCons : List IR.Var → IR.Var → FM (List IR.LetDecl × IR.Var)
  | [], tailV => pure ([], tailV)
  | h :: rest, tailV => do
      let (letsT, tv) ← buildCons rest tailV
      let c ← fresh "cons"
      pure ({ var := c, ty := .obj
            , value := .ctor 1 #[.var h, .var tv] } :: letsT, c)

/-- One expression → the let spine + the result variable + its SOURCE
    type. Expressions carry NO control flow (the fragment's
    discipline — the eager `and`/`or` included), so the product is
    straight lets. -/
def compE (env : Env) : Expr →
    FM (List IR.LetDecl × IR.Var × Ty)
  | .int n => do
      if n >= u64Cap then
        throw (.unsupportedConstruct s!"integer literal {n}"
          "at/above 2^64 — the machine's u64 ring is the surface's int \
           domain (the model wraps; a literal at/above the cap refuses)")
      let v ← fresh "lit"
      pure ([{ var := v, ty := .u64, value := .litU64 n }], v, .int)
  | .boolV b => do
      let v ← fresh "lit"
      pure ([{ var := v, ty := .bool
             , value := .litU32 (if b then 1 else 0) }], v, .bool)
  | .var x =>
      match lookupEnv env x with
      | some (v, t) => pure ([], v, t)
      | none => throw (.unboundFVar x)
  | .bin .and l r => do
      -- the 0/1 ring's meet: a*b (EAGER — the header's note)
      let (ll, lv, lt) ← compE env l
      let (rl, rv, rt) ← compE env r
      if lt != .bool || rt != .bool then
        throw (.unsupportedConstruct "and" "bool operands (the checker's \
          contract — this is the lowering-side defense)")
      let v ← fresh "and"
      pure (ll ++ rl
            ++ [{ var := v, ty := .bool
                , value := .binop .u32mul #[.var lv, .var rv] }],
            v, .bool)
  | .bin .or l r => do
      -- the 0/1 ring's join: a + b - a*b (three rows, zero new ctors)
      let (ll, lv, lt) ← compE env l
      let (rl, rv, rt) ← compE env r
      if lt != .bool || rt != .bool then
        throw (.unsupportedConstruct "or" "bool operands (the checker's \
          contract — this is the lowering-side defense)")
      let s ← fresh "ors"
      let p ← fresh "orp"
      let v ← fresh "or"
      pure (ll ++ rl
            ++ [{ var := s, ty := .bool
                , value := .binop .u32add #[.var lv, .var rv] }
               , { var := p, ty := .bool
                 , value := .binop .u32mul #[.var lv, .var rv] }]
            ++ [{ var := v, ty := .bool
                , value := .binop .u32sub #[.var s, .var p] }],
            v, .bool)
  | .bin op l r => do
      let (ll, lv, lt) ← compE env l
      let (rl, rv, rt) ← compE env r
      if lt != .int || rt != .int then
        throw (.unsupportedConstruct "arithmetic" "int operands (the \
          checker's contract — this is the lowering-side defense)")
      let v ← fresh "bin"
      pure (ll ++ rl
            ++ [{ var := v, ty := .u64
                , value := .binop (opBinop op) #[.var lv, .var rv] }],
            v, .int)
  | .cmp .gt l r => do
      -- the SWAPPED spelling: `l > r` = `r < l` (one row, zero new)
      let (ll, lv, _) ← compE env l
      let (rl, rv, _) ← compE env r
      let v ← fresh "cmp"
      pure (ll ++ rl
            ++ [{ var := v, ty := .bool
                , value := .binop .u64ltu #[.var rv, .var lv] }],
            v, .bool)
  | .cmp op l r => do
      match op with
      | .lt | .eq =>
          -- the direct rows (the op surface's own compares)
          let (ll, lv, _) ← compE env l
          let (rl, rv, _) ← compE env r
          let v ← fresh "cmp"
          pure (ll ++ rl
                ++ [{ var := v, ty := .bool
                    , value := .binop (opCmp op) #[.var lv, .var rv] }],
                v, .bool)
      | _ =>
          -- le/ge/ne: the (swapped) row then the u32sub not-face 1 - x
          let (ll, lv, _) ← compE env l
          let (rl, rv, _) ← compE env r
          let inner ← fresh "cmp"
          let (innerOp, args) :=
            match op with
            | .le => (.u64ltu, #[.var rv, .var lv])   -- l <= r = !(r < l)
            | .ge => (.u64ltu, #[.var lv, .var rv])   -- l >= r = !(l < r)
            | .ne => (.u64eq, #[.var lv, .var rv])    -- l != r = !(l == r)
            | _ => (.u64eq, #[.var lv, .var rv])      -- unreachable
          let z ← fresh "lit"
          let v ← fresh "cmp"
          pure (ll ++ rl
                ++ [{ var := inner, ty := .bool
                    , value := .binop innerOp args }
                   , { var := z, ty := .bool, value := .litU32 1 }
                   , { var := v, ty := .bool
                     , value := .binop .u32sub #[.var z, .var inner] }],
              v, .bool)
  | .un .neg e => do
      -- the ring's negation: 0 - x (the model wraps; so does the machine)
      let (el, ev, t) ← compE env e
      if t != .int then
        throw (.unsupportedConstruct "unary minus" "an int operand (the \
          checker's contract — this is the lowering-side defense)")
      let z ← fresh "lit"
      let v ← fresh "neg"
      pure (el
            ++ [{ var := z, ty := .u64, value := .litU64 0 }
               , { var := v, ty := .u64
                 , value := .binop .u64sub #[.var z, .var ev] }],
            v, .int)
  | .un .not e => do
      -- the bools' ring face: 1 - x (the u32 lane — the i32 repr)
      let (el, ev, t) ← compE env e
      if t != .bool then
        throw (.unsupportedConstruct "not" "a bool operand (the \
          checker's contract — this is the lowering-side defense)")
      let z ← fresh "lit"
      let v ← fresh "not"
      pure (el
            ++ [{ var := z, ty := .bool, value := .litU32 1 }
               , { var := v, ty := .bool
                 , value := .binop .u32sub #[.var z, .var ev] }],
            v, .bool)
  | .tup es => do
      let (als, avs, ats) ← compEsT env es
      -- the class-set defense: a bool element has no field class
      if ats.any (fun t => t == .bool) then
        throw (.unsupportedConstruct "tuple element"
          "a bool element has no field class (the packing law's set: \
           refs + u64 scalars — the checker's refusal)")
      let v ← fresh "tup"
      pure (als
            ++ [{ var := v, ty := .obj
                , value := .ctor 0 (avs.toArray.map (fun a => .var a)) }],
            v, .tup ats)
  | .listLit es => do
      let (als, avs, ats) ← compEsT env es
      match ats, ats.head? with
      | _ :: _, some t0 =>
          if ats.any (fun t => t != t0) then
            throw (.unsupportedConstruct "list literal"
              "a heterogeneous literal (the checker's homogeneous \
               contract — this is the lowering-side defense)")
          if t0 == .bool then
            throw (.unsupportedConstruct "list element"
              "a bool element has no field class (the packing law's \
               set: refs + u64 scalars — the checker's refusal)")
          -- the right fold: nil first, then one cons per element
          let nilV ← fresh "nil"
          let nilLet : IR.LetDecl :=
            { var := nilV, ty := .obj, value := .ctor 0 #[] }
          let (lastV, consLets) ← buildCons avs nilV
          pure (als ++ (nilLet :: consLets), lastV, .list t0)
      | _, _ =>
          throw (.unsupportedConstruct "[]"
            "an empty list literal has no element type to infer (the \
             checker's refusal — this is the lowering-side defense)")
  | .idx b (.int i) => do
      let (bl, bv, bt) ← compE env b
      match bt with
      | .tup ts =>
          match ts.get? i with
          | some t =>
              if t == .bool then
                throw (.unsupportedConstruct "tuple element"
                  "a bool element has no field class (the packing law's \
                   set — the checker's refusal)")
              let (isRef, a1, a2) := elemCoords ts i
              let v ← fresh "fld"
              let decl : IR.LetDecl :=
                if isRef then
                  { var := v, ty := .obj, value := .oproj a1 bv }
                else
                  { var := v, ty := .u64
                  , value := .sproj a1 a2 bv }
              pure (bl ++ [decl], v, t)
          | none =>
              throw (.unsupportedConstruct "tuple index"
                s!"index {i} at/above the tuple's arity {ts.length} (the \
                   checker's refusal — this is the lowering-side defense)")
      | .list t =>
          if i != 0 then
            throw (.unsupportedConstruct "list index"
              "only [0] — the head; a deeper index has no bounds check \
               to ride (the length is not stored — the bounds-checked \
               walk is the named follow-up)")
          match t with
          | .int =>
              -- the cons layout: tail ref slot 0, head u64 @base slot 1
              let v ← fresh "head"
              pure (bl ++ [{ var := v, ty := .u64
                           , value := .sproj 1 0 bv }], v, .int)
          | .bool =>
              throw (.unsupportedConstruct "list element"
                "a bool element has no field class (the packing law's \
                 set — the checker's refusal)")
          | .tup _ | .list _ =>
              let v ← fresh "head"
              pure (bl ++ [{ var := v, ty := .obj
                           , value := .oproj 0 bv }], v, t)
      | _ =>
          throw (.unsupportedConstruct "index"
            "a tuple/list-typed base (the checker's contract — this is \
             the lowering-side defense)")
  | .idx _ _ =>
      throw (.unsupportedConstruct "dynamic index"
        "the index must be an INT LITERAL (the bounds-checked walk is \
         the named follow-up)")
  | .call f args => do
      let (als, avs) ← compEs env args
      let v ← fresh "call"
      let callArgs : Array IR.Arg := avs.toArray.map (fun a => .var a)
      pure (als
            ++ [{ var := v, ty := .u64, value := .call f callArgs }],
            v, .int)
where
  -- the args' fold WITH the types (the tuple/list literals' element
  -- faces; the explicit list recursion — the higher-order foldlM face
  -- would break the structural inference)
  compEsT (env : Env) : List Expr →
      FM (List IR.LetDecl × List IR.Var × List Ty)
    | [] => pure ([], [], [])
    | a :: rest => do
        let (l1, v1, t1) ← compE env a
        let (l2, vs, ts) ← compEsT env rest
        pure (l1 ++ l2, v1 :: vs, t1 :: ts)

/-- The args' fold (the call lane's; the types drop). -/
def compEs (env : Env) : List Expr →
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
  | .forIn _ _ body :: ss =>
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
      -- (the source type rides the info pairs — `rowOf` at the param)
      let msInfo ← ms.foldlM (fun acc x => do
        match lookupEnv env x with
        | some (v, t) => do
            let p ← fresh x
            pure (acc ++ [(x, (p, t))])
        | none => throw (.unboundFVar x)) []
      let params : List (IR.Var × IR.Ty) :=
        msInfo.map (fun b => (b.2.1, rowOf b.2.2))
      -- the body's env: the loop-carried vars ARE the params (the
      -- info pairs bind the source name to its (param var, source ty))
      let envLoop : Env := msInfo ++ env
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
  | .forIn x xs body :: rest, k => do
      -- THE CONS-WALK (the module header's derivation): the while
      -- shape with the LIST OBJECT's tag as the condition
      let (xlets, xv, xt) ← compE env xs
      let t : Ty :=
        match xt with
        | .list t => t
        | _ =>
            throw (.unsupportedConstruct "for target"
              "a list-typed iterable (the checker's contract — this is \
               the lowering-side defense)")
      let ms := assignedVars body
      -- every loop-carried var must be bound at loop entry
      for x2 in ms do
        match lookupEnv env x2 with
        | some _ => pure ()
        | none =>
            throw (.unsupportedConstruct s!"loop-carried variable {x2}"
              "first assigned inside the for body — a loop-carried \
               variable must be bound BEFORE the loop (the entry args' \
               face; the named boundary)")
      let jpName ← fresh "loop"
      -- the jp params: the cursor (the list object) first, then the
      -- body's loop-carried vars in first-assignment order
      let curP ← fresh (x ++ "cur")
      let msInfo ← ms.foldlM (fun acc x2 => do
        match lookupEnv env x2 with
        | some (v2, t2) => do
            let p ← fresh x2
            pure (acc ++ [(x2, (p, t2))])
        | none => throw (.unboundFVar x2)) []
      let msParams : List (IR.Var × IR.Ty) :=
        msInfo.map (fun b => (b.2.1, rowOf b.2.2))
      let params : List (IR.Var × IR.Ty) := (curP, IR.Ty.obj) :: msParams
      let envLoop : Env := msInfo ++ env
      -- the cons arm's reads: the element + the next cursor (the
      -- packing law's coordinates — `consCoords`)
      let xRead ← fresh x
      let tailV ← fresh (x ++ "tail")
      let (isRef, a1, a2) := consCoords t
      let xDecl : IR.LetDecl :=
        if isRef then
          { var := xRead, ty := .obj, value := .oproj a1 curP }
        else
          { var := xRead, ty := .u64, value := .sproj a1 a2 curP }
      let tailDecl : IR.LetDecl :=
        if isRef then
          { var := tailV, ty := .obj, value := .oproj 1 curP }
        else
          { var := tailV, ty := .obj, value := .oproj 0 curP }
      -- the body's env: the element binding FIRST (a body assignment
      -- of `x` shadows it — the cons order), then the carried params
      let bodyC ← compSs ((x, (xRead, t)) :: envLoop) body
        (fun envAfter => pure
          (.jmp jpName
            (#[IR.Arg.var tailV]
              ++ ((ms.filterMap (lookupEnv envAfter)).toArray.map
                (fun b => IR.Arg.var b.1)))))
      -- the EXIT arm: the statements after the loop (the carried
      -- vars' last-iteration values — the params; the ELEMENT does
      -- not leak — the named boundary)
      let exitC ← compSs envLoop rest (fun _ => k envLoop)
      -- the ENTRY: the cursor = the iterable, the carried vars' pre-
      -- loop bindings
      let entryArgs : Array IR.Arg :=
        (#[IR.Arg.var xv] ++
          ((ms.filterMap (lookupEnv env)).toArray.map
            (fun b => .var b.1)))
      pure (IR.Code.jp jpName params
        (xlets.foldr IR.Code.let_
          (IR.Code.cases_ "for" .tag curP
            [IR.Alt.ctorAlt 1
                (IR.Code.let_ xDecl (IR.Code.let_ tailDecl bodyC))
            , IR.Alt.ctorAlt 0 exitC])
          (.jmp jpName entryArgs)))
  termination_by ss => msL ss
  decreasing_by
    all_goals
      (simp only [msL_cons, msS_assign, msS_ifelse, msS_while, msS_forIn]
       omega)

/-! ## The decl fold -/

/-- One function → one IR decl: the params u64 (the exported surface),
    the result u64, the body's fold ending in `unreach` (fall-off-the-end
    is outside the surface — the legacy discipline). -/
def compFn (f : Fn) (types : List (String × Ty)) : FM IR.Decl := do
  let params ← f.params.foldlM (fun acc p => do
    let v ← fresh p
    pure (acc ++ [(p, (v, Ty.int))])) []
  let env0 : Env := params.map (fun p => (p.1, (p.2.1, p.2.2)))
  let _types := types  -- the checker's merged env: consumed by the
                       -- row checks at each site (rowOf/compE); kept
                       -- in the signature as the two folds' joint face
  let body ← compSs env0 f.body (fun _ => pure .unreach)
  pure { name := f.name
       , params := env0.map (fun p => (p.2.1, rowOf p.2.2))
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
        "a repr-split operand, a bool-typed call arg, a non-bool \
         condition, a non-int return, a branch-merge type clash, an \
         ill-formed tuple/list/index, or a duplicate name — Check.lean's \
         refusals")
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
