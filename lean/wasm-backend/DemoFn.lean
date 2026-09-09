/- DemoFn — the functions the WASM backend compiles (compiler-line demo
   stage). Plain Lean defs: the LCNF pipeline handles the lowering.
   UInt64 shapes only: the guest has no GMP (no Nat arithmetic). -/

/-- The backend's hello-world: pure integer arithmetic. -/
def double (x : UInt64) : UInt64 := x + x

/-- Branching: lowers to LCNF branches. -/
def isBig (x : UInt64) : Bool := x > 100

/-- Closure: LCNF `fun` + captured env (`pap`) — mono eta-reduces it. -/
def adder (a : UInt64) : UInt64 → UInt64 := fun b => a + b

/-- Constructor dispatch: LCNF `cases` + `sproj` (byte offsets). -/
inductive Shape where
  | circle (r : UInt64)
  | rect (w h : UInt64)

def area (s : Shape) : UInt64 :=
  match s with
  | .circle r => r * r
  | .rect w h => w * h

/-- The full OBJECT LIFECYCLE: ctor alloc ($alloc, rc=1) → call →
    Perceus dec ($rc_dec → pooled free) → scalar out. The differential
    smoke asserts the pooled allocator doesn't corrupt values. -/
def doubleArea (r : UInt64) : UInt64 := area (.circle (r + r))
