import EdgePython
import EdgePython.Parity
import EdgePython.Eval

/- Axiom gate: the EdgePython parity theorems + compiler/eval. The
   parity computations are native_decide (DISCLOSED — the interpreter's
   fuel-bounded brecOn exceeds the kernel's whnf budget; the axiom gate
   allows the native_decide trust basis, as for the backend's
   fixed-width rung). Everything else is pure computation: propext +
   Quot.sound only. -/

#print axioms EdgePython.Parity.parity_double_21
#print axioms EdgePython.Parity.parity_adder_40_2
#print axioms EdgePython.Parity.parity_dec1_5
#print axioms EdgePython.Parity.parity_loop_sum_10
#print axioms EdgePython.Parity.parity_if_max_3_9
#print axioms EdgePython.Parity.buggy_double_diverges
#print axioms EdgePython.Compiler.compModule
#print axioms EdgePython.WEval.callModule
