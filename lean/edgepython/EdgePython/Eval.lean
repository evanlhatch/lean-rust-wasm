/-
# EdgePython.Eval — the wasm-level semantics over the FROZEN Instr

Owner: the EDGEPYTHON lane. The evaluator the parity theorems run on:
it consumes `WasmBackend.Instr` values — the SAME AST the compiler
emits and the backend renders — with NO translation step in between
(the IR-reuse claim is type-checked, not asserted).

Why not `WasmBackend.Sem` (the backend's own model)? READ-ONLY, and its
modeled op set stops at `i64add`/`i32eq` — `i64.mul`, `i64.sub`,
`i64.lt_u`, `i32.eqz` (everything this frontend's fixtures need beyond
add) are outside its fragment. REPORTED to the wasm-backend lane as the
Sem-gap; this file is the edgepython-owned evaluator in the meantime,
scoped to EXACTLY the constructors the compiler emits + `unreach`.

Deltas from real wasm (documented, fixture-scoped): fuel-bounded (the
model artifact, as in Sem.lean); branch payloads carry the CURRENT
stack (the emitted fragment only branches with an empty extra stack, so
frame-entry == branch-point); locals are NAMED (the renderer's `refW`
convention — binary-level index resolution is downstream).
-/

import WasmBackend.Wat

namespace EdgePython.WEval

open WasmBackend.Wat

/-- A runtime value: i32 (bools/conditions) or i64 (ints). -/
inductive WVal where
  | w32 (n : Nat)
  | w64 (v : Int)
  deriving BEq, DecidableEq, Inhabited

/-- Two's-complement wrap into the signed i64 range. -/
def wrap64 (x : Int) : Int :=
  let m : Int := (2 : Int) ^ 64
  let y := ((x % m) + m) % m
  if y ≥ (2 : Int) ^ 63 then y - m else y

/-- The UNSIGNED reinterpretation (the `_u` in `i64.lt_u`). -/
def u64Of (x : Int) : Int :=
  if x < 0 then x + (2 : Int) ^ 64 else x

/-- Locals: name → value, first-match lookup. -/
def getLocal : List (String × WVal) → String → WVal
  | [], _ => .w64 0
  | (y, v) :: rest, x => if y == x then v else getLocal rest x

def setLocal : List (String × WVal) → String → WVal → List (String × WVal)
  | [], x, v => [(x, v)]
  | (y, w) :: rest, x, v =>
      if y == x then (x, v) :: rest else (y, w) :: setLocal rest x v

def findFn : List Func → String → Option Func
  | [], _ => none
  | f :: rest, name => if f.name == name then some f else findFn rest name

/-- Branch-target depth: the FIRST matching label, innermost-first (the
    label stack's head is the innermost frame). -/
def labelDepth : List String → String → Option Nat
  | [], _ => none
  | l :: rest, name => if l == name then some 0 else (labelDepth rest name).map (· + 1)

def popN : List WVal → Nat → Option (List WVal × List WVal)
  | stk, 0 => some ([], stk)
  | [], _+1 => none
  | v :: rest, n+1 => do
      let (vs, stk) ← popN rest n
      some (v :: vs, stk)

/-- The flat-step outcome: a state update, or the function-return signal
    (`Wat.ret` — unwinds ALL frames). -/
inductive FlatFlow where
  | st (locals : List (String × WVal)) (stack : List WVal)
  | fnret (v : WVal)

/-- The frame-flow of the structured executor. -/
inductive Flow where
  | next (locals : List (String × WVal)) (stack : List WVal)
  | br (k : Nat) (locals : List (String × WVal)) (stack : List WVal)
  | retv (v : WVal)

/-- One FLAT instruction (never `block`/`loop`/`if_` — those are
    dispatched by `execInstrs`). -/
def stepI (locals : List (String × WVal)) (stack : List WVal) :
    Instr → Option FlatFlow
  | .i32const n => some (.st locals (.w32 n :: stack))
  | .i64const n => some (.st locals (.w64 n :: stack))
  | .localget x => some (.st locals (getLocal locals x :: stack))
  | .localset x =>
      match stack with
      | v :: rest => some (.st (setLocal locals x v) rest)
      | [] => none
  | .localtee x =>
      match stack with
      | v :: rest => some (.st (setLocal locals x v) (v :: rest))
      | [] => none
  | .op .i64add =>
      match stack with
      | .w64 b :: .w64 a :: rest => some (.st locals (.w64 (wrap64 (a + b)) :: rest))
      | _ => none
  | .op .i64sub =>
      match stack with
      | .w64 b :: .w64 a :: rest => some (.st locals (.w64 (wrap64 (a - b)) :: rest))
      | _ => none
  | .op .i64mul =>
      match stack with
      | .w64 b :: .w64 a :: rest => some (.st locals (.w64 (wrap64 (a * b)) :: rest))
      | _ => none
  | .op .i64ltu =>
      match stack with
      | .w64 b :: .w64 a :: rest =>
          some (.st locals (.w32 (if u64Of a < u64Of b then 1 else 0) :: rest))
      | _ => none
  | .op .i64eq =>
      match stack with
      | .w64 b :: .w64 a :: rest =>
          some (.st locals (.w32 (if a == b then 1 else 0) :: rest))
      | _ => none
  | .op .i32eqz =>
      match stack with
      | .w32 b :: rest => some (.st locals (.w32 (if b == 0 then 1 else 0) :: rest))
      | _ => none
  | .ret =>
      match stack with
      | v :: _ => some (.fnret v)
      | [] => none
  | .unreach => none
  | _ => none  -- outside the emitted fragment (mem ops, globals, …)

mutual
/-- Execute an instruction list against a label stack (innermost
    first). Every flat step AND every frame entry consumes one fuel
    unit (the model artifact, as in Sem.lean). -/
def execInstrs : Nat → List Func → List String →
    List (String × WVal) → List WVal → List Instr → Option Flow
  | 0, _, _, _, _, _ => none
  | _+1, _, _, locals, stack, [] => some (.next locals stack)
  | fuel+1, fns, labels, locals, stack, .block l body :: rest =>
      match execInstrs fuel fns (l :: labels) locals stack body with
      | some (.next l' s') => execInstrs fuel fns labels l' s' rest
      | some (.br 0 l' s') => execInstrs fuel fns labels l' s' rest
      | some (.br (k+1) l' s') => some (.br k l' s')
      | some (.retv v) => some (.retv v)
      | none => none
  | fuel+1, fns, labels, locals, stack, .loop l body :: rest =>
      match execInstrs fuel fns (l :: labels) locals stack body with
      | some (.next l' s') => execInstrs fuel fns labels l' s' rest
      | some (.br 0 l' s') =>
          -- THE backward edge: restart the loop with the branched state
          execInstrs fuel fns labels l' s' (.loop l body :: rest)
      | some (.br (k+1) l' s') => some (.br k l' s')
      | some (.retv v) => some (.retv v)
      | none => none
  | fuel+1, fns, labels, locals, stack, .if_ _ thenI elseI :: rest =>
      -- `if` is UNLABELED in the frozen AST: no frame on the label
      -- stack; a branch through it propagates UNCHANGED.
      match stack with
      | .w32 b :: s' =>
          let chosen := if b != 0 then thenI else elseI
          match execInstrs fuel fns labels locals s' chosen with
          | some (.next l' s'') => execInstrs fuel fns labels l' s'' rest
          | some (.br k l' s'') => some (.br k l' s'')
          | some (.retv v) => some (.retv v)
          | none => none
      | _ => none
  | fuel+1, fns, labels, locals, stack, .brif l :: rest =>
      match stack with
      | .w32 b :: s' =>
          if b != 0 then
            match labelDepth labels l with
            | some k => some (.br k locals s')
            | none => none
          else execInstrs fuel fns labels locals s' rest
      | _ => none
  | _fuel+1, _fns, labels, locals, stack, .br l :: _rest =>
      match labelDepth labels l with
      | some k => some (.br k locals stack)
      | none => none
  | fuel+1, fns, labels, locals, stack, i :: rest =>
      match stepI locals stack i with
      | some (.st l' s') => execInstrs fuel fns labels l' s' rest
      | some (.fnret v) => some (.retv v)
      | none => none

/-- Call one function with concrete args (the frame machine: fresh
    locals = the params bound to the args, empty stack, no labels). -/
def execFn : Nat → List Func → Func → List WVal → Option WVal
  | 0, _, _, _ => none
  | fuel+1, fns, g, args =>
      let locals0 : List (String × WVal) :=
        (g.params.map (fun p => p.name.getD "")).zip args
      match execInstrs fuel fns [] locals0 [] g.body with
      | some (.retv v) => some v
      | some (.next _ [v]) => some v
      | _ => none
end

/-- THE top level: run exported fn `name(args...)` over a module's
    funcs. The i64 result is the model's answer. -/
def callModule (fns : List Func) (name : String) (args : List Int) :
    Option Int :=
  match findFn fns name with
  | none => none
  | some g =>
    match execFn 400 fns g (args.map WVal.w64) with
    | some (.w64 v) => some v
    | some (.w32 n) => some n
    | none => none

/-- The module's functions (the `Item.func` fold). -/
def modFns (m : Module) : List Func :=
  m.items.foldr (fun i acc =>
    match i with
    | .func f => f :: acc
    | _ => acc) []

end EdgePython.WEval
