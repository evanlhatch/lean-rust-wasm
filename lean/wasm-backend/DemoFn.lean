/- DemoFn — the functions the WASM backend compiles (compiler-line demo
   stage). Plain Lean defs: the LCNF pipeline handles the lowering.
   UInt64 shapes only: the guest has no GMP (no Nat arithmetic).
   Structural recursion on UInt64 needs WF proofs with no omega — the
   loop forms arrive with guestlang-std's iterators, not here. -/

/-- The backend's hello-world: pure integer arithmetic. -/
def double (x : UInt64) : UInt64 := x + x

/-- Branching: lowers to LCNF branches. -/
def isBig (x : UInt64) : Bool := x > 100

/-- Closure: LCNF `fun` + captured env (`pap`). -/
def adder (a : UInt64) : UInt64 → UInt64 := fun b => a + b

/-- Constructor dispatch: LCNF `cases` + `ctor` + `proj`. -/
inductive Shape where
  | circle (r : UInt64)
  | rect (w h : UInt64)

def area (s : Shape) : UInt64 :=
  match s with
  | .circle r => r * r
  | .rect w h => w * h
