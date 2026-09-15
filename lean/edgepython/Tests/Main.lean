/-
# EdgePython tests — the structural + negative-control surface

The kernel-checked half of the conformance claim (the PARITY THEOREMS
live in `EdgePython/Parity.lean` — a lib module the axiom gate imports):

* IR-REUSE (the point): every emitted instruction IS a
  `WasmBackend.Wat.Instr` — type-checked by construction; the guards
  pin the shapes (block/loop/br_if/if_), the export surface, and the
  module shape (funcs + exports + memory — the guestlang shape minus
  the runtime splice: no heap, no alloc/RC).
* NEGATIVE CONTROLS (non-vacuity of the CHECKER): each out-of-subset
  program (bool return, undeclared var, int condition, bool call-arg,
  branch-type conflict) is REJECTED by the type checker.
-/

import EdgePython
import EdgePython.Compiler
import EdgePython.Eval
import EdgePython.Parity

open EdgePython EdgePython.Py EdgePython.WEval WasmBackend.Wat

/-! ## The compile succeeds — the module is real, not the empty fallback -/

#guard compiledModule?.isSome = true
#guard (compiledFns.map (·.name)) == ["double", "adder", "dec1", "loop_sum", "if_max"]

/-! ## IR-reuse evidence: the emitted shapes, pinned -/

-- the loop fixture compiles to the block/loop/br_if shape (ALL frozen
-- constructors — this file could not name a new one if it wanted to)
#guard (match compiledFns.find? (fun f => f.name == "loop_sum") with
  | some f => f.body.any (fun i =>
      match i with | .block _ (.loop _ _ :: _) => true | _ => false)
  | none => false) = true

-- the if fixture compiles to the no-result `if_` frame
#guard (match compiledFns.find? (fun f => f.name == "if_max") with
  | some f => f.body.any (fun i =>
      match i with | .if_ none _ _ => true | _ => false)
  | none => false) = true

-- the export surface: every fixture exported by name, func-backed
#guard (match fixturesModule.items.filterMap
          (fun i => match i with | .export e => some e | _ => none) with
  | es => (es.map (·.name)) == ["double", "adder", "dec1", "loop_sum", "if_max"]
          && es.all (fun e => match e.desc with | .func _ => true | _ => false)
  ) = true

-- the module shape: funcs + exports + the memory item (the guestlang
-- module shape, minus the runtime splice — no heap, no alloc/RC)
#guard (fixturesModule.items.countP (fun i => match i with | .func _ => true | _ => false)) == 5
#guard (fixturesModule.items.countP (fun i => match i with | .export _ => true | _ => false)) == 5
#guard (fixturesModule.items.countP (fun i => match i with | .memory _ => true | _ => false)) == 1

-- the Python model's own values (cheap, kernel-checked: no loop)
#guard Py.pyEval fixtures "double" [21] = some 42
#guard Py.pyEval fixtures "adder" [40, 2] = some 42
#guard Py.pyEval fixtures "if_max" [3, 9] = some 9
#guard Py.pyEval fixtures "if_max" [9, 3] = some 9

/-! ## NEGATIVE CONTROLS — the type checker rejects the out-of-subset -/

-- The out-of-subset programs (the fixtures' field style — proven to
-- parse). Each MUST fail the type checker.
def badRet : List Py.Fn :=
  [{ name := "bad", params := ["x"]
     body := [.ret (.cmp .lt (.var "x") (.var "x"))] }]

def badVar : List Py.Fn :=
  [{ name := "bad", params := ["x"]
     body := [.ret (.var "y")] }]

def badCond : List Py.Fn :=
  [{ name := "bad", params := ["x"]
     body := [.ifelse (.int 1) [] []] }]

def badArg : List Py.Fn :=
  [{ name := "bad", params := ["x"]
     body := [.ret (.call "double" [.boolV true])] }]

def badBranch : List Py.Fn :=
  [{ name := "bad", params := ["x"]
     body := [.ifelse (.cmp .lt (.var "x") (.var "x"))
                [.assign "v" (.int 1)]
                [.assign "v" (.cmp .eq (.var "x") (.var "x"))],
              .ret (.var "v")] }]

-- a bool return (the exported surface is i64): REJECTED
#guard Compiler.compModule badRet = none

-- an undeclared variable: REJECTED
#guard Compiler.compModule badVar = none

-- an int-typed condition (no truthiness coercion in v1): REJECTED
#guard Compiler.compModule badCond = none

-- a bool call-arg: REJECTED (the i64 surface)
#guard Compiler.compModule badArg = none

-- an inconsistent variable type across branches: REJECTED
#guard Compiler.compModule badBranch = none

def main : IO UInt32 := do
  IO.println "edgepython: structural + negative controls green (Lean engine)"
  return 0
