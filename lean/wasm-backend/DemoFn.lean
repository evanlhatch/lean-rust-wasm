import WasmBackend.Check

/- DemoFn — the functions the WASM backend compiles (compiler-line demo
   stage). `@[guest]` checks each def at ELABORATION: banned runtimes
   (Nat/GMP, String, IO, Task, Thunk) fail `lake build` at the decl —
   the earliest possible error, zero proofs. -/

/-- The backend's hello-world: pure integer arithmetic. -/
@[guest]
def double (x : UInt64) : UInt64 := x + x

/-- Branching: lowers to LCNF branches. -/
@[guest]
def isBig (x : UInt64) : Bool := x > 100

/-- Closure: LCNF `fun` + captured env (`pap`) — mono eta-reduces it. -/
@[guest]
def adder (a : UInt64) : UInt64 → UInt64 := fun b => a + b

/-- Constructor dispatch: LCNF `cases` + `sproj` (byte offsets).
Guest-compat is enforced on the FUNCTIONS using the type. -/
inductive Shape where
  | circle (r : UInt64)
  | rect (w h : UInt64)

@[guest]
def area (s : Shape) : UInt64 :=
  match s with
  | .circle r => r * r
  | .rect w h => w * h

/-- The full OBJECT LIFECYCLE: ctor alloc ($alloc, rc=1) → call →
    Perceus dec ($rc_dec → pooled free) → scalar out. The differential
    smoke asserts the pooled allocator doesn't corrupt values. -/
@[guest]
def doubleArea (r : UInt64) : UInt64 := area (.circle (r + r))

/-- An ESCAPING closure: returned from a conditional — mono cannot
    eta-reduce it (the body branches). Exercises pap + closure apply. -/
@[guest]
def pick (b : Bool) (a : UInt64) : UInt64 → UInt64 :=
  fun x => if b then a + x else a * x

/-- Closures stored in objects SURVIVE mono (boxed into the erased
    world): applyAll [adder 1, adder 2] 5 runs two real paps. -/
@[guest]
def applyAll (fs : List (UInt64 → UInt64)) (x : UInt64) : UInt64 :=
  match fs with
  | [] => x
  | f :: rest => f (applyAll rest x)

@[guest]
def runPaps (x : UInt64) : UInt64 := applyAll [adder 1, adder 2] x

/-- Tail recursion: `let r := fap ...; return r` fuses to return_call
    (the tail-call proposal) — flat WASM stack. Structural on the list
    (no WF proof needed); accumulator style. -/
@[guest]
def sumList (xs : List UInt64) (acc : UInt64) : UInt64 :=
  match xs with
  | [] => acc
  | x :: rest => sumList rest (acc + x)


/-- MULTI-ARITY closures: pap with 1 captured arg, TWO fresh args —
    a second trampoline signature (sig_2box). -/
@[guest]
def curried (a : UInt64) : UInt64 → UInt64 → UInt64 :=
  fun x y => a + x + y

@[guest]
def apply2All (fs : List (UInt64 → UInt64 → UInt64)) (x y : UInt64) : UInt64 :=
  match fs with
  | [] => x + y
  | f :: rest => apply2All rest (f x y) y

@[guest]
def useCurried (a : UInt64) : UInt64 := apply2All [curried a] 3 4

@[guest]
def total (a b c : UInt64) : UInt64 := sumList [a, b, c] 0
