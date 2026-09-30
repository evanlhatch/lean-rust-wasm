/-
# Guest.EdgePython.Ast — the Python-subset surface AST + the reference semantics

Owner: the guest lane's SECOND FRONTEND (the multi-frontend doctrine,
`Guest.IR`'s header: the frontends are per-language and the IR is what
they all produce). Ported from `legacy/lean/edgepython/EdgePython/Ast.lean`
(read-only mining source — the CONTENT ported fresh, retargeted: the
legacy compiled straight to a frozen WAT AST, this frontend produces
`Guest.IR`).

THE HONEST SUBSET (v2 — the productive fragment; the E6 growth):

* integer literals (below 2^64 — the machine's face; compile-time
  refusal at/above), `+ - *` arithmetic, unary minus (`-x` = `0 - x`
  in the machine's ring), `< <= > >= == !=` comparisons,
* `and` / `or` / `not` on BOOL operands (EAGER — Python's
  short-circuit is the named divergence: the fragment's expressions
  are pure, so only a nonterminating/trapping operand could tell),
* `if/else`, `while` (the IR's jp loop shape), `for x in xs` (over
  LIST values; the while+cons-walk discipline in `Fe`),
* assignments, function calls, `return`,
* TUPLE literals `(a, b, …)` + CONSTANT-index access `t[i]` (the IR's
  object face: the packing law's coordinates),
* LIST literals `[a, b, …]` (homogeneous; nonempty) + constant index
  (`xs[0]` — the head; deeper indexing waits on the bounds-checked
  walk) + `for` iteration.

THE VALUES: the int domain IS the machine's u64 ring — `pyEval`'s
arithmetic WRAPS mod 2^64 (the honest oracle is the machine's own
semantics; the v1 "unbounded Int" fiction diverged from the compiled
wasm the first time `0 - 1` ran). Tuples/lists ride `Val`'s object
faces; the compiled reprs are the IR's ctor objects (`Fe`'s layouts).

NOT MODELED (documented exclusions, not oversights): strings (the IR
carries NO string value row — `Guest.IR.Ty`'s closed set has no
string; byte-lists land with lists, but concatenation/equality need
either a string row or the growing-object discipline — the named
deferral, REPORTED in `Fe`'s header), `%` (no u64 rem row in the IR's
`Binop` set — the named deferral), dynamic indexing (`t[expr]` with a
non-literal index), list indexing past the head, `bool`/tuple/list
ELEMENTS in tuples and lists (the packing law's class set: refs +
u64 scalars only), bool operands for `+ - *` and comparisons (the
repr split: bool = i32, int = i64 — mixing reprs in one binop is the
invalid-module face), `bool`/tuple/list params/returns/args (the
exported surface is u64), comments, augmented assignment, comparison
chaining, heterogeneous list literals, empty list literals (no
element type to infer), singleton tuples.

TWO LEVELS:

1. the AST (`Py.Expr`/`Py.Stmt`/`Py.Fn`) — the AUTHORING surface; the
   text face is `Guest.EdgePython.Parse` (TextKit's parser lane),
2. `pyEval` — the WRAPPED-u64 reference semantics: the machine's ring
   arithmetic, `bool` values as 0/1 (Python's `True == 1`), sequential
   env, call-by-value. This is the authority the compiled wasm is
   parity-tested against (the GuestTests.EdgeSpecs pins).

The five questions (notes/v3/01-core.md):

- **Root**: Universe (finite closed data — the surface's constructors).
- **Carrier grade**: none — plain data.
- **Spine reading**: none — the frontend's INPUT, folded by
  `Guest.EdgePython.Fe` into the IR spine.
- **Ladder rung**: rung 1 (closed data; every non-fragment input
  refuses — at the parser or the checker).
- **Gate row**: the Guest row (Gates.Packages) — the module rides the
  Guest lib's glob.
-/

import Kit.Diag

namespace Guest.EdgePython.Py

/-- Binary arithmetic/logic operators. `and`/`or` are the BOOL
    operands' rows (the checker refuses non-bool operands — the eager
    semantics, see the module header). -/
inductive BinOp where
  | add | sub | mul | and | or
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Comparison operators — the full five-op set, each riding the IR's
    `u64ltu`/`u64eq` rows (the swapped/negated spellings in `Fe`). -/
inductive CmpOp where
  | lt | le | gt | ge | eq | ne
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Unary operators: `-x` (int; the ring's `0 - x`) and `not x` (bool;
    the ring's `1 - x`). -/
inductive UnOp where
  | neg | not
  deriving BEq, DecidableEq, Inhabited, Repr

/-- The static type of a value: Python `int` = wasm i64 (the IR's `u64`
    row), Python `bool` = wasm i32 (the IR's `bool` row — the
    `cases_` condition type), tuples/lists = the object rows (the IR's
    ctor objects). -/
inductive Ty where
  | int | bool
  | tup (ts : List Ty)
  | list (t : Ty)
  deriving BEq, DecidableEq, Inhabited, Repr

inductive Expr where
  | int (n : Nat)
  | boolV (b : Bool)
  | var (x : String)
  | bin (op : BinOp) (l r : Expr)
  | cmp (op : CmpOp) (l r : Expr)
  | un (op : UnOp) (e : Expr)
  | /-- `(a, b, …)` — the tuple literal (the IR's ctor object). -/
  tup (es : List Expr)
  | /-- `[a, b, …]` — the (homogeneous, nonempty) list literal. -/
  listLit (es : List Expr)
  | /-- `b[i]` — the index access; the checker pins `i` to an INT
        LITERAL (the dynamic-index deferral). -/
  idx (b i : Expr)
  | call (f : String) (args : List Expr)
  deriving BEq, Inhabited, Repr

inductive Stmt where
  | /-- `x = e` -/
  assign (x : String) (e : Expr)
  | /-- `return e` — the exported surface is u64, so `e` must be int. -/
  ret (e : Expr)
  | /-- `if c: ... else: ...` — the condition must be bool-typed. -/
  ifelse (c : Expr) (thenB elseB : List Stmt)
  | /-- `while c: ...` — the condition must be bool-typed. -/
  while (c : Expr) (body : List Stmt)
  | /-- `for x in xs: body` — `xs` list-typed; `x` binds the element. -/
  forIn (x : String) (xs : Expr) (body : List Stmt)
  deriving BEq, Inhabited, Repr

/-- One function: `def name(params...): body`. -/
structure Fn where
  name : String
  params : List String
  body : List Stmt
  deriving BEq, Inhabited, Repr

/-! ## The wrapped-u64 reference semantics -/

/-- THE MACHINE'S RING: the model's arithmetic wraps mod 2^64 (the
    honest oracle = the machine's own semantics; the module header's
    note). Lean's `%` on a negative Int can stay negative under the
    truncated convention, so the correction adds the modulus back. -/
def wrapU64 (v : Int) : Int :=
  let m := v % 18446744073709551616
  if m < 0 then m + 18446744073709551616 else m

/-- The runtime value: the machine int (bools are 0/1 — Python's
    `bool ⊂ int`), the tuple, the list. -/
inductive Val where
  | vi (n : Int)
  | vtup (es : List Val)
  | vlist (es : List Val)
  deriving BEq, Inhabited, Repr

/-- The environment: name → value. Lookup = the FIRST match
    (shadowing-friendly). -/
def Env.get : List (String × Val) → String → Option Val
  | [], _ => none
  | (y, v) :: rest, x => if y == x then some v else Env.get rest x

def Env.set (env : List (String × Val)) (x : String) (v : Val) :
    List (String × Val) :=
  (x, v) :: env

/-- The statement-level flow: either the function returned, or the body
    fell through with the final env. -/
inductive PyFlow where
  | ret (v : Val)
  | fall (env : List (String × Val))

/-- The int's face of a value (the arith/cmp operands'; a tuple/list
    where the checker demands an int is `none` — the checker's contract
    makes it unreachable for compiled programs). -/
def Val.asInt : Val → Option Int
  | .vi n => some n
  | _ => none

/-- Python's truthiness for the model's values (an int's `!= 0`). -/
def Val.truthy : Val → Option Bool
  | .vi n => some (n != 0)
  | _ => none

mutual
/-- Evaluate one expression under the wrapped-u64 model. EVERY
    recursive edge (including the sub-expression ones) strictly
    decreases the fuel — the mutual block is structural on Nat. The
    fuel bounds the call/loop/expr depth (a model artifact, never hit
    by the fixtures at the pyEval budget). -/
def evE (fns : List Fn) : Nat → List (String × Val) → Expr → Option Val
  | 0, _, _ => none
  | _+1, _env, .int n => some (.vi n)
  | _+1, _env, .boolV b => some (.vi (if b then 1 else 0))
  | _+1, env, .var x => Env.get env x
  | fuel+1, env, .bin .add l r => do
      let a ← Val.asInt (← evE fns fuel env l)
      let b ← Val.asInt (← evE fns fuel env r)
      some (.vi (wrapU64 (a + b)))
  | fuel+1, env, .bin .sub l r => do
      let a ← Val.asInt (← evE fns fuel env l)
      let b ← Val.asInt (← evE fns fuel env r)
      some (.vi (wrapU64 (a - b)))
  | fuel+1, env, .bin .mul l r => do
      let a ← Val.asInt (← evE fns fuel env l)
      let b ← Val.asInt (← evE fns fuel env r)
      some (.vi (wrapU64 (a * b)))
  | fuel+1, env, .bin .and l r => do
      -- Python's operand-value semantics (a truthy → b else a) — for
      -- the checker's 0/1 bool operands this IS the eager `mul`.
      let a ← evE fns fuel env l
      let b ← evE fns fuel env r
      if (← Val.truthy a) then some b else some a
  | fuel+1, env, .bin .or l r => do
      let a ← evE fns fuel env l
      let b ← evE fns fuel env r
      if (← Val.truthy a) then some a else some b
  | fuel+1, env, .cmp .lt l r => do
      let a ← Val.asInt (← evE fns fuel env l)
      let b ← Val.asInt (← evE fns fuel env r)
      some (.vi (if a < b then 1 else 0))
  | fuel+1, env, .cmp .le l r => do
      let a ← Val.asInt (← evE fns fuel env l)
      let b ← Val.asInt (← evE fns fuel env r)
      some (.vi (if a <= b then 1 else 0))
  | fuel+1, env, .cmp .gt l r => do
      let a ← Val.asInt (← evE fns fuel env l)
      let b ← Val.asInt (← evE fns fuel env r)
      some (.vi (if a > b then 1 else 0))
  | fuel+1, env, .cmp .ge l r => do
      let a ← Val.asInt (← evE fns fuel env l)
      let b ← Val.asInt (← evE fns fuel env r)
      some (.vi (if a >= b then 1 else 0))
  | fuel+1, env, .cmp .eq l r => do
      let a ← Val.asInt (← evE fns fuel env l)
      let b ← Val.asInt (← evE fns fuel env r)
      some (.vi (if a == b then 1 else 0))
  | fuel+1, env, .cmp .ne l r => do
      let a ← Val.asInt (← evE fns fuel env l)
      let b ← Val.asInt (← evE fns fuel env r)
      some (.vi (if a != b then 1 else 0))
  | fuel+1, env, .un .neg e => do
      let a ← Val.asInt (← evE fns fuel env e)
      some (.vi (wrapU64 (0 - a)))
  | fuel+1, env, .un .not e => do
      let a ← evE fns fuel env e
      some (.vi (if (← Val.truthy a) then 0 else 1))
  | fuel+1, env, .tup es => do
      let vs ← evArgs fns fuel env es
      some (.vtup vs)
  | _+1, _env, .listLit [] => none  -- no element type (the checker's refusal)
  | fuel+1, env, .listLit es => do
      let vs ← evArgs fns fuel env es
      some (.vlist vs)
  | fuel+1, env, .idx b i => do
      let bv ← evE fns fuel env b
      let iv ← Val.asInt (← evE fns fuel env i)
      match bv, iv with
      | .vtup es, .ofNat n => es.get? n
      | .vlist es, .ofNat n => es.get? n
      | _, _ => none
  | fuel+1, env, .call f args => do
      let vs ← evArgs fns fuel env args
      evCall fns fuel f vs

def evArgs (fns : List Fn) : Nat → List (String × Val) → List Expr →
    Option (List Val)
  | 0, _, _ => none
  | _+1, _, [] => some []
  | fuel+1, env, e :: rest => do
      let v ← evE fns fuel env e
      let vs ← evArgs fns fuel env rest
      some (v :: vs)

/-- Call the function `name` with the (already evaluated) args. -/
def evCall (fns : List Fn) : Nat → String → List Val → Option Val
  | 0, _, _ => none
  | fuel+1, name, args => do
      let f ← findFn fns name
      let env0 := f.params.zip args
      match ← evSs fns fuel f.body env0 with
      | .ret v => some v
      | .fall _ => none  -- no implicit return in the u64 surface

def findFn (fns : List Fn) (name : String) : Option Fn :=
  match fns with
  | [] => none
  | f :: rest => if f.name == name then some f else findFn rest name

/-- Execute a statement list. -/
def evSs (fns : List Fn) : Nat → List Stmt → List (String × Val) →
    Option PyFlow
  | 0, _, _ => none
  | _+1, [], env => some (.fall env)
  | fuel+1, .assign x e :: ss, env => do
      let v ← evE fns fuel env e
      evSs fns fuel ss (Env.set env x v)
  | fuel+1, .ret e :: _ss, env => do
      let v ← evE fns fuel env e
      some (.ret v)
  | fuel+1, .ifelse c t e :: ss, env => do
      let b ← Val.truthy (← evE fns fuel env c)
      let branch := if b then t else e
      match ← evSs fns fuel branch env with
      | .ret v => some (.ret v)
      | .fall env' => evSs fns fuel ss env'
  | fuel+1, .while c body :: ss, env => do
      let b ← Val.truthy (← evE fns fuel env c)
      if b then
        match ← evSs fns fuel body env with
        | .ret v => some (.ret v)
        | .fall env' => evSs fns fuel (.while c body :: ss) env'
      else
        evSs fns fuel ss env
  | fuel+1, .forIn x xsE body :: ss, env => do
      -- the list walk: Python iterates the list's elements in order;
      -- each element binds `x` for the body (and LEAKS past the loop —
      -- the compiled face keeps the element only through the body, the
      -- named boundary in `Fe`)
      match ← evE fns fuel env xsE with
      | .vlist es =>
          let rec walk (env : List (String × Val)) : List Val →
              Option PyFlow
            | [] => evSs fns fuel ss env
            | e :: rest => do
                match ← evSs fns fuel body (Env.set env x e) with
                | .ret v => some (.ret v)
                | .fall env' => walk env' rest
          walk env es
      | _ => none  -- the checker's list-typed contract
end

/-- THE Python model's top level: run `name(args...)` over `fns`. -/
def pyEval (fns : List Fn) (name : String) (args : List Int) : Option Int :=
  match evCall fns 400 name (args.map Val.vi) with
  | some v => v.asInt
  | none => none

end Guest.EdgePython.Py
