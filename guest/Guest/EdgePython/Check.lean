/-
# Guest.EdgePython.Check — the Python-subset type checker (the {int, bool, tup, list} lattice)

Owner: the guest lane's SECOND FRONTEND. Ported from
`legacy/lean/edgepython/EdgePython/Compiler.lean`'s checking section —
the SAME lattice discipline, retargeted: the legacy's `Ty` feeds the
wasm type strings directly, THIS checker's rows feed `Guest.IR.Ty`
(`int` → the `u64` row, `bool` → the `bool` row, tuples/lists → the
object rows) so the lowering sees the contract's closed rows.

The lattice (E6): Python `int` = the u64 row; Python `bool` = the
i32-repr row (the `cases_` condition type); `tup ts`/`list t` = the
object row (the ctor objects — `Fe`'s packing-law layouts). The
REPR-SPLIT teeth: `+ - *` and comparisons take INT operands only, and
`or`/`not` take BOOL operands only — mixing the i64 and i32 reprs in
one binop is the invalid-module face, refused at CHECK time. Tuple and
list elements must be int or tuple/list themselves (the packing law's
field-class set; a bool element has no class — the named refusal).
Assignments type variables; `if`/`else` branches merge (a var added in
BOTH branches must have the SAME type, else a compile error); `while`
bodies merge against the pre-loop env (the loop may run zero times, so
a loop-added var is still a var — the wasm-default-initialized face);
`for x in xs` binds `x` at the element's type and merges like `while`.

DELIBERATE CHOICE (the legacy's ladder-audit judgment, kept): an
`Option Unit` gate, not a `WellTyped` inductive with a checker↔relation
bridge. The edgepython lane is parity-pinned — its correctness statement
is the parity suite's conformance pins (compiled wasm == the model on
every fixture), which check these paths end to end; a WellTyped relation
here would be an uncited statement. THE NAMED UPGRADE: if the lane
graduates (real consumers, the exclusions lifted), mirror
`SchemaLang.Wf` — the inductive + the `checkE_ok_iff` bridge, and
`collectSs`'s env threading re-quantifies through it.

The five questions (notes/v3/01-core.md):

- **Root**: Universe — the checker is a total function over closed data.
- **Carrier grade**: none — `Option Unit` refusals; the renderable face
  rides `Fe`'s translation into the shared `Guest.LowerError` envelope.
- **Spine reading**: none — the checker's product (the merged env) is
  the lowering's input discipline.
- **Ladder rung**: rung 1.
- **Gate row**: the Guest row (Gates.Packages).
-/

import Guest.EdgePython.Ast
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Guest.EdgePython.Check

open Guest.EdgePython.Py

/-! ## The lattice lookup -/

def findTy : List (String × Ty) → String → Option Ty
  | [], _ => none
  | (y, t) :: rest, x => if y == x then some t else findTy rest x

/-! ## The expression typing + the deep checks -/

/-- The static type of an expression under an env. The DEEP operand
    checks live in `checkE` — call sites run `checkE` first, then this
    for the result row. -/
def exprTy (env : List (String × Ty)) : Expr → Option Ty
  | .int _ => some .int
  | .boolV _ => some .bool
  | .var x => findTy env x
  | .bin .and _ _ => some .bool
  | .bin .or _ _ => some .bool
  | .bin _ _ _ => some .int
  | .cmp _ _ _ => some .bool
  | .un .neg _ => some .int
  | .un .not _ => some .bool
  | .tup es => do
      let ts ← es.mapM (exprTy env)
      -- the packing law's class set: a bool element has no field class
      if ts.any (fun t => t == .bool) then none else some (.tup ts)
  | .listLit [] => none  -- an empty list has no element type to infer
  | .listLit (e :: rest) => do
      let t0 ← exprTy env e
      -- homogeneous (the named refusal on a mixed literal) + the class set
      for e' in rest do
        let t' ← exprTy env e'
        if t' != t0 then none else pure ()
      if t0 == .bool then none else some (.list t0)
  | .idx b i => do
      -- THE INDEX must be an INT LITERAL (the dynamic-index deferral)
      match i with
      | .int n =>
          match ← exprTy env b with
          | .tup ts => if n < ts.length then ts[n]? else none
          | .list t => if n == 0 then some t else none  -- the head only
          | _ => none
      | _ => none
  | .call _ _ => some .int

-- The deep checks `exprTy` can't see: the ARITH/CMP operands must be
-- int-typed and the LOGIC operands bool-typed (the repr split), the
-- call args must be int-typed (the u64 surface), the index must be a
-- literal. The operand sites are MUTUAL with `checkE` (each recurses
-- through the other — the operand sites re-run `checkE`, the arith
-- arms re-run the operand sites).
mutual
def intOperand (env : List (String × Ty)) (e : Expr) : Option Unit := do
  let _ ← checkE env e
  if exprTy env e == some .int then some () else none

/-- Is this expression a bool-typed operand? -/
def boolOperand (env : List (String × Ty)) (e : Expr) : Option Unit := do
  let _ ← checkE env e
  if exprTy env e == some .bool then some () else none

/-- The deep checks `exprTy` can't see: the ARITH/CMP operands must be
    int-typed and the LOGIC operands bool-typed (the repr split), the
    call args must be int-typed (the u64 surface), the index must be a
    literal. -/
def checkE (env : List (String × Ty)) : Expr → Option Unit
  | .int _ | .boolV _ | .var _ => some ()
  | .bin .add l r => do
      let _ ← intOperand env l
      let _ ← intOperand env r
      some ()
  | .bin .sub l r => do
      let _ ← intOperand env l
      let _ ← intOperand env r
      some ()
  | .bin .mul l r => do
      let _ ← intOperand env l
      let _ ← intOperand env r
      some ()
  | .bin .and l r => do
      let _ ← boolOperand env l
      let _ ← boolOperand env r
      some ()
  | .bin .or l r => do
      let _ ← boolOperand env l
      let _ ← boolOperand env r
      some ()
  | .cmp _ l r => do
      let _ ← intOperand env l
      let _ ← intOperand env r
      some ()
  | .un op e => do
      -- the operand's row: neg rides INT, not rides BOOL (the repr split)
      match op with
      | .neg => let _ ← intOperand env e; some ()
      | .not => let _ ← boolOperand env e; some ()
  | .tup es => es.foldl (fun acc e => do let _ ← acc; checkE env e) (some ())
  | .listLit es =>
      es.foldl (fun acc e => do let _ ← acc; checkE env e) (some ())
  | .idx b i => do
      let _ ← checkE env b
      let _ ← checkE env i
      -- the result-type check fires the literal/shape refusals
      let _t ← exprTy env (.idx b i)
      some ()
  | .call _ args =>
      args.foldl (fun acc a => do
        let _ ← acc
        let _ ← checkE env a
        let t ← exprTy env a
        if t == .int then some () else none) (some ())
end

/-- Conditions must be bool-typed (Python truthiness of ints is OUTSIDE
    the fragment — comparisons and the logic ops are the conditions). -/
def checkCond (env : List (String × Ty)) (c : Expr) : Option Unit := do
  let _ ← checkE env c
  let t ← exprTy env c
  if t == .bool then some () else none

/-! ## Local collection — one pass, branch-merged -/

def mergeEnv : List (String × Ty) → List (String × Ty) → Option (List (String × Ty))
  | a, [] => some a
  | a, (x, t) :: rest =>
      match findTy a x with
      | some t' => if t' == t then mergeEnv a rest else none
      | none => mergeEnv ((x, t) :: a) rest

/-- The one-pass local collection (the legacy's, verbatim discipline). -/
def collectSs : List Stmt → List (String × Ty) → Option (List (String × Ty))
  | [], env => some env
  | s :: ss, env => do
      let env ← collectS s env
      collectSs ss env
where
  collectS : Stmt → List (String × Ty) → Option (List (String × Ty))
    | .assign x e, env => do
        let _ ← checkE env e
        let t ← exprTy env e
        match findTy env x with
        | some t' => if t' == t then some env else none
        | none => some ((x, t) :: env)
    | .ret e, env => do
        let _ ← checkE env e
        let t ← exprTy env e
        if t == .int then some env else none
    | .ifelse c t e, env => do
        let _ ← checkCond env c
        let envT ← collectSs t env
        let envE ← collectSs e env
        mergeEnv envT envE
    | .while c body, env => do
        let _ ← checkCond env c
        let envB ← collectSs body env
        mergeEnv env envB
    | .forIn x xs body, env => do
        let _ ← checkE env xs
        match ← exprTy env xs with
        | .list t =>
            let envB ← collectSs body ((x, t) :: env)
            mergeEnv env envB
        | _ => none

/-! ## The module-level checks -/

/-- The duplicate names (the functions' and the params'): a duplicate
    function name would collide in the IR's sibling registry; a
    duplicate param would collide in the IR's param locals. -/
def nodupNames : List String → Bool
  | [] => true
  | x :: rest => !(rest.contains x) && nodupNames rest

/-- ONE function's check: the params' names distinct, then the body's
    collection under the params' env (all params int-typed — the u64
    surface). -/
def checkFn (f : Fn) : Option (List (String × Ty)) := do
  if nodupNames f.params then pure () else none
  let env0 := f.params.map (fun p => (p, Ty.int))
  collectSs f.body env0

/-- THE MODULE check: distinct function names, each function checked;
    the product is the merged local-type env per function (the
    lowering's rows derive from it). THE BARE-CHECKER opt-out (the
    legacy's deliberate choice, see the module header): the lane is
    parity-pinned — its correctness statement is the parity suite's
    conformance pins, not a checker↔relation bridge; the named upgrade
    (a WellTyped inductive + `checkModule_ok`) is the graduation face. -/
@[nolint linter.guestlang.bareChecker "the legacy lane's Option-gate discipline kept: the correctness face is the parity suite's conformance pins (EdgeSpecs), not a bridge theorem — the WellTyped graduation is the named upgrade"]
def checkModule (fns : List Fn) : Option (List (List (String × Ty))) := do
  if nodupNames (fns.map (·.name)) then pure () else none
  fns.mapM checkFn

end Guest.EdgePython.Check
