import WasmBackend

/- Axiom gate: wasm-backend is an emitter package — zero theorems by
design (the robustness contract is runtime `throw`s + the differential
gate, not kernel proofs). The import above is the gate: any axiom leak
in the imported modules fails here. Headline defs get `#print axioms`
as they gain proof obligations. -/

#print axioms WasmBackend.wasmTyOf?
#print axioms WasmBackend.emitModule
#print axioms WasmBackend.emitAdapter
