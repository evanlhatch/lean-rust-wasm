import WasmCore.WatParse

namespace Probe
open WasmCore

-- probe A: literal append by rfl (kernel)
example : ("ab" ++ "cd" : String) = "abcd" := by rfl

-- probe B: literal append disequality by decide
example : (("ab" ++ "cd" : String) = "xy") = false := by decide

-- probe C: allOps nodup (ctor list, DecidableEq Op)
example : allOps.Nodup := by decide

-- probe D: simp reduces append of literal produced by match
example : ∀ (o : Op), ("p-" ++ opName o ++ ".wasm" : String) ≠ "q.wasm" := by
  intro o; cases o <;> simp [opName] <;> decide

end Probe
