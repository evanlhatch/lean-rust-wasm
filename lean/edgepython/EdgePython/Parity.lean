/-
# EdgePython.Parity — the shared-machine conformance theorems (M3)

Owner: the EDGEPYTHON lane. THE PARITY: the compiled wasm (evaluated
over the SHARED machine — `EdgePython.SemExec.callModule`: the thin
adapter that lowers the compiled `Wat.Instr` bodies into the Sem
fragment and runs `Sem.exec`, the wasm-backend's PROVED machine) ==
the Python reference semantics (`Py.pyEval`) on every fixture, at
multiple argument points. These live in a LIB module so
`Tests/Axioms.lean` can `#print axioms` them (the gate).

PROOF DISCIPLINE: the engine computations run through the mutual
fuel-bounded machinery — kernel reduction exceeds the whnf budget —
so they are `native_decide`-proved, the repo's DISCLOSED trust basis
(the axiom gate allows it, as for the old evaluator). Non-vacuity
rides the same evaluator: the buggy-emission negative controls below
DIVERGE.

THE M3 CHANGE (2026-12): the engine side was the edgepython-owned
interpreter `EdgePython.WEval` (a SECOND frame machine, unproved —
the M3 finding; ~231 lines beside a proved one). That evaluator is
DELETED in this work. The theorems keep their NAMES and fixture set —
the engine is now the shared Sem machine (per-op semantics live in
`WasmBackend.SemOp`'s table next to `Wat.Op`, and in `Sem.step`'s
arms; the adapter's `.op` translation goes through `SemOp.opInstr`, so
the compiled fixtures run on the ONE machine).

The wasmtime + wasmi halves of the duel run in the Rust `edgepython`
tests on the SAME compiled module and pin the SAME values.
-/

import EdgePython
import EdgePython.SemExec

namespace EdgePython.Parity

open EdgePython EdgePython.Py EdgePython.SemExec WasmBackend.Wat

/-! ## THE PARITY: compiled wasm == Python model (the shared machine) -/

theorem parity_double_21 :
    SemExec.callModule compiledFns "double" [21] = Py.pyEval fixtures "double" [21] :=
  by native_decide
theorem parity_double_0 :
    SemExec.callModule compiledFns "double" [0] = Py.pyEval fixtures "double" [0] :=
  by native_decide
theorem parity_adder_40_2 :
    SemExec.callModule compiledFns "adder" [40, 2] = Py.pyEval fixtures "adder" [40, 2] :=
  by native_decide
theorem parity_dec1_5 :
    SemExec.callModule compiledFns "dec1" [5] = Py.pyEval fixtures "dec1" [5] :=
  by native_decide
theorem parity_loop_sum_10 :
    SemExec.callModule compiledFns "loop_sum" [10] = Py.pyEval fixtures "loop_sum" [10] :=
  by native_decide
theorem parity_loop_sum_0 :
    SemExec.callModule compiledFns "loop_sum" [0] = Py.pyEval fixtures "loop_sum" [0] :=
  by native_decide
theorem parity_loop_sum_1 :
    SemExec.callModule compiledFns "loop_sum" [1] = Py.pyEval fixtures "loop_sum" [1] :=
  by native_decide
theorem parity_if_max_3_9 :
    SemExec.callModule compiledFns "if_max" [3, 9] = Py.pyEval fixtures "if_max" [3, 9] :=
  by native_decide
theorem parity_if_max_9_3 :
    SemExec.callModule compiledFns "if_max" [9, 3] = Py.pyEval fixtures "if_max" [9, 3] :=
  by native_decide

/-! ## The duel constants (the Rust engines pin the SAME values) -/

theorem wasm_double_21 : SemExec.callModule compiledFns "double" [21] = some 42 :=
  by native_decide
theorem wasm_adder_40_2 : SemExec.callModule compiledFns "adder" [40, 2] = some 42 :=
  by native_decide
theorem wasm_loop_sum_10 : SemExec.callModule compiledFns "loop_sum" [10] = some 45 :=
  by native_decide
theorem wasm_if_max_3_9 : SemExec.callModule compiledFns "if_max" [3, 9] = some 9 :=
  by native_decide
theorem wasm_if_max_9_3 : SemExec.callModule compiledFns "if_max" [9, 3] = some 9 :=
  by native_decide

/-! ## NEGATIVE CONTROLS — the parity gate has teeth -/

-- (1) a buggy compiler (sub emitted where mul belongs): the eval
-- DIVERGES from the Python model — the parity theorems are not vacuous.
def buggyDouble : List Func :=
  [{ name := "double"
   , params := [{ name := some "x", ty := "i64" }]
   , result := some "i64"
   , locals := []
   , body := [.localget "x", .localget "x", .op .i64sub, .ret, .unreach] }]
theorem buggy_double_diverges :
    SemExec.callModule buggyDouble "double" [21]
      ≠ Py.pyEval fixtures "double" [21] := by native_decide

-- (2) the operand-ORDER swap (l/r reversed for i64sub): diverges.
def swappedDec1 : List Func :=
  [{ name := "dec1"
   , params := [{ name := some "n", ty := "i64" }]
   , result := some "i64"
   , locals := []
   , body := [.i64const 1, .localget "n", .op .i64sub, .ret, .unreach] }]
theorem swapped_dec1_diverges :
    SemExec.callModule swappedDec1 "dec1" [5]
      ≠ Py.pyEval fixtures "dec1" [5] := by native_decide

end EdgePython.Parity
