import WasmBackend
import WasmBackend.Correct
import WasmBackend.Audit

/- Axiom gate: wasm-backend's robustness contract = the runtime `throw`s
   + the differential gate, PLUS the Sem module's proved type-safety
   (the Talos-lite foundation: the well-typed programs don't
   stack-underflow). Headline defs get `#print axioms`. -/

#print axioms WasmBackend.wasmTyOf?
#print axioms WasmBackend.emitModule
#print axioms WasmBackend.emitAdapter
#print axioms WasmBackend.Sem.exec_typed
#print axioms WasmBackend.Sem.checkFrame_ok

-- The translation-correctness lane (seam #7, the straight-line slice):
-- the emitted templates' Sem-execution = the source arithmetic.
#print axioms WasmBackend.Correct.spec_double_ok
#print axioms WasmBackend.Correct.spec_add_ok
#print axioms WasmBackend.Correct.tpl_add_ret_ok
#print axioms WasmBackend.Correct.buggy_ne_spec

-- The translation-correctness lane (seam #7, the BRANCH slice): the
-- cases template's execution = the chosen alt's semantics; the demo on
-- the is-big branch shape; the tag-inverted negative control.
#print axioms WasmBackend.Correct.specCases_ok
#print axioms WasmBackend.Correct.specCases_alt1
#print axioms WasmBackend.Correct.specCases_trap
#print axioms WasmBackend.Correct.isBig_250
#print axioms WasmBackend.Correct.isBig_42
#print axioms WasmBackend.Correct.branch_br0_entry_stack
#print axioms WasmBackend.Correct.branch_buggy_disagrees

-- The translation-correctness lane (seam #7, the CALLS + CLOSURES
-- slice): the calling-convention contract (the caller's pushes = the
-- callee's entry state, over the prep/prologue composition), the
-- trampoline's arg-forward contract, the run-paps 5 = 8 inner-call
-- demo, and the arg-order-swap negative control.
#print axioms WasmBackend.Correct.call_convention1
#print axioms WasmBackend.Correct.call_convention2
#print axioms WasmBackend.Correct.trampoline_convention1
#print axioms WasmBackend.Correct.trampoline_convention2
#print axioms WasmBackend.Correct.runPaps_inner_8
#print axioms WasmBackend.Correct.call_convention2_buggy_disagrees
#print axioms WasmBackend.Wat.Audit.audit
#print axioms WasmBackend.Wat.Audit.audit_nil

-- The CALL-SEMANTICS lane: the calls layer in Sem.lean (v1 = CALLS as
-- FUNCTION-COMPOSITION — the big-step callExecFuel + the split theorem
-- that identifies it with the flat prep/pops/body program), the
-- end-to-end call-execution theorems, the trampoline's DIRECT hop, the
-- type-safety cross-ref, and the arity/arg-order negative controls.
#print axioms WasmBackend.Sem.Calls.callExecFuel_arity_trap
#print axioms WasmBackend.Sem.Calls.pushArgs_exec
#print axioms WasmBackend.Sem.Calls.popParams_exec
#print axioms WasmBackend.Sem.Calls.call_split
#print axioms WasmBackend.Sem.Calls.call_exec_correct
#print axioms WasmBackend.Sem.Calls.call_prep_ok
#print axioms WasmBackend.Sem.Calls.call_prep_swapped
#print axioms WasmBackend.Sem.Calls.call_prep_swapped_disagrees
#print axioms WasmBackend.Sem.Calls.trampoline_call_ok
#print axioms WasmBackend.Sem.Calls.call_exec_safe
