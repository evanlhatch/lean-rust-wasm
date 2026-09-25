/-
# Guest.EdgePython.Check — the Python-subset type checker (the {int, bool} lattice)

Owner: the guest lane's SECOND FRONTEND. Ported from
`legacy/lean/edgepython/EdgePython/Compiler.lean`'s checking section —
the SAME lattice discipline, retargeted: the legacy's `Ty` feeds the
wasm type strings directly, THIS checker's rows feed `Guest.IR.Ty`
(`int` → the `u64` row, `bool` → the `bool` row) so the lowering sees
the contract's closed rows.

The small lattice: Python `int` = the u64 row; Python `bool` = the
i32-repr row (the `cases_` condition type). Assignments type variables;
`if`/`else` branches merge (a var added in BOTH branches must have the
SAME type, else a compile error); `while` bodies merge against the
pre-loop env (the loop may run zero times, so a loop-added var is still
a var — the wasm-default-initialized face).

DELIBERATE CHOICE (the legacy's ladder-audit judgment, kept): an
`Option Unit` gate, not a `WellTyped` inductive with a checker↔relation
bridge. The edgepython lane is parity-pinned — its correctness statement
is the parity suite's conformance pins (compiled wasm == the Python
model on every fixture), which check these paths end to end; a
WellTyped relation here would be an uncited statement. THE NAMED
UPGRADE: if the lane graduates (real consumers, the exclusions lifted),
mirror `SchemaLang.Wf` — the inductive + the `checkE_ok_iff` bridge, and
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

/-- The static type of an expression under an env. Call args are checked
    separately (`checkE`) — this only types the RESULT. -/
def exprTy (env : List (String × Ty)) : Expr → Option Ty
  | .int _ => some .int
  | .boolV _ => some .bool
  | .var x => findTy env x
  | .bin _ _ _ => some .int
  | .cmp _ _ _ => some .bool
  | .call _ _ => some .int

/-- The deep checks `exprTy` can't see: call ARGS must be int-typed
    (the u64 surface) — a bool arg is a compile ERROR, not a silent
    extend. -/
def checkE (env : List (String × Ty)) : Expr → Option Unit
  | .int _ | .boolV _ | .var _ => some ()
  | .bin _ l r => do let _ ← checkE env l; let _ ← checkE env r; some ()
  | .cmp _ l r => do let _ ← checkE env l; let _ ← checkE env r; some ()
  | .call _ args =>
      args.foldl (fun acc a => do
        let _ ← acc
        let _ ← checkE env a
        let t ← exprTy env a
        if t == .int then some () else none) (some ())

/-- Conditions must be bool-typed (Python truthiness of ints is OUTSIDE
    the v1 surface — comparisons are the conditions). -/
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
