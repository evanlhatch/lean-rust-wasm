/-
# EdgePython.Compiler — Py AST → the FROZEN WasmBackend.Wat AST

Owner: the EDGEPYTHON lane. THE POINT of this file: every emitted
instruction is a `WasmBackend.Instr` — ZERO new constructors. The
IR seam is the wasm-backend lane's typed WAT AST, and a second frontend
targets it unchanged (notes/full-remaining-work.md: "same fixtures →
same IR").

The translation (the guestlang module shape, minus the heap):

* Python `int` = wasm i64; Python `bool` = wasm i32 (the `br_if`
  condition type). Params/returns are i64 (the exported surface).
* variables → NAMED wasm locals (`Wat.localget/localset` take names;
  the renderer resolves `refW` — a name, not an index — and the
  name→index resolution stays the emitter/binary's job, per Sem.lean's
  header).
* `while c: body` → `block $exit { loop $top { c; i32.eqz; br_if $exit;
  body; br $top } }` — the condition INVERTED by `i32.eqz` so `br_if`
  exits on false (both `i32eqz` and the shape are in the frozen AST).
* `if c: t else: e` → `if (result none) t e` — no-result frames, the
  shape `WasmBackend.Sem.checkFrame` models.
* calls → `Wat.call` (direct; no funcref table). Functions fall off the
  end into `unreachable` (implicit-return is OUTSIDE the i64 surface —
  every fixture returns explicitly).
* NO alloc/RC: scalars only, nothing heap-allocated — the simpler
  frontend proving the runtime layer is a guestlang concern, not an
  IR-seam concern.

The FROZEN-AST GAP (REPORTED, per lane rules — not worked around):
`Wat.Op` lacks `i64.gt_u`/`i64.le_u`/`i64.ge_u`/`i64.ne` (it has only
`i64ltu`/`i64eq` for i64 compares), so the v1 comparison set is `<` and
`==` only; `a > b` is authorable as `b < a`.

Deliberate v1 exclusions: recursion (the eval model's fuel would mask
it), `for`, strings/lists/objects, negative literals (use `0 - n`).
-/

import WasmBackend.Wat
import EdgePython.Ast

namespace EdgePython.Compiler

open WasmBackend.Wat EdgePython.Py

/-! ## Type checking — the small lattice {int, bool} -/

def findTy : List (String × Ty) → String → Option Ty
  | [], _ => none
  | (y, t) :: rest, x => if y == x then some t else findTy rest x

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
    (the i64 surface) — a bool arg is a compile ERROR, not a silent
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

/-! ## Local collection — one pass, branch-merged

Python assigns types by ASSIGNMENT; wasm locals are typed once. The
pass threads the env linearly; `if/else` branches merge (a var added in
both branches must have the SAME type, else a compile error); `while`
bodies merge against the pre-loop env (the loop may run zero times, so
a loop-added var is still a var — initialized to wasm's 0). -/

def mergeEnv : List (String × Ty) → List (String × Ty) → Option (List (String × Ty))
  | a, [] => some a
  | a, (x, t) :: rest =>
      match findTy a x with
      | some t' => if t' == t then mergeEnv a rest else none
      | none => mergeEnv ((x, t) :: a) rest

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

/-! ## The emission -/

/-- Expression → the instruction list (post type-check; the result type
    is `exprTy`'s verdict: cmp = i32, everything else = i64). -/
def compE : Expr → List Instr
  | .int n => [.i64const n]
  | .boolV b => [.i32const (if b then 1 else 0)]
  | .var x => [.localget x]
  | .bin .add l r => compE l ++ compE r ++ [.op .i64add]
  | .bin .sub l r => compE l ++ compE r ++ [.op .i64sub]
  | .bin .mul l r => compE l ++ compE r ++ [.op .i64mul]
  | .cmp .lt l r => compE l ++ compE r ++ [.op .i64ltu]
  | .cmp .eq l r => compE l ++ compE r ++ [.op .i64eq]
  | .call f args => args.flatMap compE ++ [.call f]

/-- Statement → the instruction list. -/
def compSs : List Stmt → List Instr
  | [] => []
  | s :: ss => compS s ++ compSs ss
where
  compS : Stmt → List Instr
    | .assign x e => compE e ++ [.localset x]
    | .ret e => compE e ++ [.ret]
    | .ifelse c t e => compE c ++ [.if_ none (compSs t) (compSs e)]
    | .while c body =>
        let inner := compE c ++ [.op .i32eqz, .brif "exit"]
          ++ compSs body ++ [.br "top"]
        [.block "exit" [.loop "top" inner]]

/-- One function → one `Func`: params/locals typed, the body
    terminated by `unreachable` (fall-off-the-end is outside the i64
    surface). -/
def compFn (f : Py.Fn) : Option Func := do
  let env ← collectSs f.body (f.params.map (fun p => (p, Py.Ty.int)))
  let locals := env.filter (fun (x, _) => !(f.params.contains x))
  some { name := f.name
       , params := f.params.map (fun p => ({ name := some p, ty := "i64" } : Param))
       , result := some "i64"
       , locals := locals.map (fun (x, t) => (x, if t == Py.Ty.bool then "i32" else "i64"))
       , body := compSs f.body ++ [.unreach] }

/-- The MODULE: the same shape as the guestlang line — funcs + exports +
    memory — minus the runtime splice (no alloc/RC needed: nothing is
    heap-allocated). -/
def compModule (fns : List Py.Fn) : Option Module := do
  let fs ← fns.mapM compFn
  let exports := fns.map (fun f =>
    ({ name := f.name, desc := .func f.name } : Export))
  some { items := fs.map Item.func
                ++ exports.map Item.export
                ++ [Item.memory 1] }

end EdgePython.Compiler
