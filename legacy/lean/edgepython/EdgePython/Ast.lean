/-!
# EdgePython.Ast — the Python-subset AST + the reference semantics

Owner: the EDGEPYTHON lane (the SECOND FRONTEND — notes/full-remaining-work.md
"EdgePython frontend"). EdgePython proves the IR-seam's NEUTRALITY: a
different frontend compiling to the SAME `WasmBackend.Wat` AST, running on
the SAME runtimes (steel-host's wasmtime + guestlang-rt's wasmi).

THE HONEST SUBSET (v1 — scalars only, no heap):

* integer literals (NONNEGATIVE; negatives arise as values via `-`),
  `+ - *` arithmetic, `<` and `==` comparisons,
* `if/else`, `while` (the wasm `block`/`loop`/`br_if` shape),
* assignments, function calls, `return`.

NOT MODELED (documented exclusions, not oversights): strings, lists,
objects (no heap — the alloc/RC runtime layer is the guestlang lane's and
is simply not needed for scalars), `>`/`<=`/`>=`/`!=` (the frozen
`Wat.Op` has only `i64ltu`/`i64eq` for i64 compares — REPORTED to the
wasm-backend lane, not worked around), negative literals (write `0 - n`;
the wasm model wraps to two's-complement i64), bool-typed params/returns
(the exported surface is i64; Python `bool` is an internal i32).

TWO LEVELS:
1. the AST (`Py.Expr`/`Py.Stmt`/`Py.Fn`) — the AUTHORING surface (a Lean
   DSL; a string tokenizer + syntax embedding is the follow-up, the
   `[inv|]`-precedent pattern),
2. `pyEval*` — the PYTHON reference semantics: unbounded Int, `bool`
   coerced to Int (Python's `True == 1`), sequential env, call-by-value.
   This is the authority the compiled wasm is parity-tested against.
-/

namespace EdgePython.Py

/-- Binary arithmetic operators. -/
inductive BinOp where
  | add | sub | mul
  deriving BEq, DecidableEq, Inhabited

/-- Comparison operators — ONLY the two the frozen `Wat.Op` supports
    (`i64ltu`, `i64eq`); the rest are REPORTED gaps, not silent drops. -/
inductive CmpOp where
  | lt | eq
  deriving BEq, DecidableEq, Inhabited

/-- The static type of a value: Python `int` = wasm i64, Python `bool`
    = wasm i32 (the `br_if` condition type). -/
inductive Ty where
  | int | bool
  deriving BEq, DecidableEq, Inhabited

inductive Expr where
  | int (n : Nat)
  | boolV (b : Bool)
  | var (x : String)
  | bin (op : BinOp) (l r : Expr)
  | cmp (op : CmpOp) (l r : Expr)
  | call (f : String) (args : List Expr)
  deriving BEq, Inhabited

inductive Stmt where
  | /-- `x = e` -/
  assign (x : String) (e : Expr)
  | /-- `return e` — the exported surface is i64, so `e` must be int. -/
  ret (e : Expr)
  | /-- `if c: ... else: ...` — the condition must be bool-typed. -/
  ifelse (c : Expr) (thenB elseB : List Stmt)
  | /-- `while c: ...` — the condition must be bool-typed. -/
  while (c : Expr) (body : List Stmt)
  deriving BEq, Inhabited

/-- One function: `def name(params...): body`. -/
structure Fn where
  name : String
  params : List String
  body : List Stmt
  deriving BEq, Inhabited

/-! ## The Python reference semantics -/

/-- The environment: name → Int (bools coerce: `True` = 1 — Python's
    own `bool ⊂ int`). Lookup = the FIRST match (shadowing-friendly). -/
def Env.get : List (String × Int) → String → Option Int
  | [], _ => none
  | (y, v) :: rest, x => if y == x then some v else Env.get rest x

def Env.set (env : List (String × Int)) (x : String) (v : Int) :
    List (String × Int) :=
  (x, v) :: env

/-- The statement-level flow: either the function returned, or the body
    fell through with the final env. -/
inductive PyFlow where
  | ret (v : Int)
  | fall (env : List (String × Int))

mutual
/-- Evaluate one expression under the Python model. EVERY recursive
    edge (including the sub-expression ones) strictly decreases the
    fuel — the mutual block is structural on Nat. The fuel bounds the
    call/loop/expr depth (a model artifact, never hit by the fixtures
    at the pyEval budget). -/
def evE (fns : List Fn) : Nat → List (String × Int) → Expr → Option Int
  | 0, _, _ => none
  | _+1, _env, .int n => some n
  | _+1, _env, .boolV b => some (if b then 1 else 0)
  | _+1, env, .var x => Env.get env x
  | fuel+1, env, .bin .add l r => do
      let a ← evE fns fuel env l
      let b ← evE fns fuel env r
      some (a + b)
  | fuel+1, env, .bin .sub l r => do
      let a ← evE fns fuel env l
      let b ← evE fns fuel env r
      some (a - b)
  | fuel+1, env, .bin .mul l r => do
      let a ← evE fns fuel env l
      let b ← evE fns fuel env r
      some (a * b)
  | fuel+1, env, .cmp .lt l r => do
      let a ← evE fns fuel env l
      let b ← evE fns fuel env r
      some (if a < b then 1 else 0)
  | fuel+1, env, .cmp .eq l r => do
      let a ← evE fns fuel env l
      let b ← evE fns fuel env r
      some (if a == b then 1 else 0)
  | fuel+1, env, .call f args => do
      let vs ← evArgs fns fuel env args
      evCall fns fuel f vs

def evArgs (fns : List Fn) : Nat → List (String × Int) → List Expr →
    Option (List Int)
  | 0, _, _ => none
  | _+1, _, [] => some []
  | fuel+1, env, e :: rest => do
      let v ← evE fns fuel env e
      let vs ← evArgs fns fuel env rest
      some (v :: vs)

/-- Call the function `name` with the (already evaluated) args. -/
def evCall (fns : List Fn) : Nat → String → List Int → Option Int
  | 0, _, _ => none
  | fuel+1, name, args => do
      let f ← findFn fns name
      let env0 := f.params.zip args
      match ← evSs fns fuel f.body env0 with
      | .ret v => some v
      | .fall _ => none  -- no implicit return in the i64 surface

def findFn (fns : List Fn) (name : String) : Option Fn :=
  match fns with
  | [] => none
  | f :: rest => if f.name == name then some f else findFn rest name

/-- Execute a statement list. -/
def evSs (fns : List Fn) : Nat → List Stmt → List (String × Int) → Option PyFlow
  | 0, _, _ => none
  | _+1, [], env => some (.fall env)
  | fuel+1, .assign x e :: ss, env => do
      let v ← evE fns fuel env e
      evSs fns fuel ss (Env.set env x v)
  | fuel+1, .ret e :: _ss, env => do
      let v ← evE fns fuel env e
      some (.ret v)
  | fuel+1, .ifelse c t e :: ss, env => do
      let b ← evE fns fuel env c
      let branch := if b != 0 then t else e
      match ← evSs fns fuel branch env with
      | .ret v => some (.ret v)
      | .fall env' => evSs fns fuel ss env'
  | fuel+1, .while c body :: ss, env => do
      let b ← evE fns fuel env c
      if b != 0 then
        match ← evSs fns fuel body env with
        | .ret v => some (.ret v)
        | .fall env' => evSs fns fuel (.while c body :: ss) env'
      else
        evSs fns fuel ss env
end

/-- THE Python model's top level: run `name(args...)` over `fns`. -/
def pyEval (fns : List Fn) (name : String) (args : List Int) : Option Int :=
  evCall fns 400 name args

end EdgePython.Py
