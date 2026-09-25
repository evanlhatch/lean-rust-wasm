import WasmCore.Duel
namespace WasmCore
example (s : State) (i : Instr) : step s i ≠ .outOfFuel := by
  cases i <;> simp [step] <;> (try split) <;> (try split) <;> (try simp)
example (s : State) (i : Instr) : step s i ≠ .structural ∨ FrameForm i = True := by
  cases i <;> simp [step, FrameForm] <;> (try split) <;> (try split) <;> (try simp)
end WasmCore
