import WasmBackend.Check
import LintKit.PackageNamespace
import SchemaLang.Meta.Reflect
import SchemaLang.WitnessCheck

/- DemoFn — the functions the WASM backend compiles (compiler-line demo
   stage). `@[guest]` checks each def at ELABORATION: banned runtimes
   (Nat/GMP, String, IO, Task, Thunk) fail `lake build` at the decl —
   the earliest possible error, zero proofs. -/

-- The declaration names in this module ARE the demo world's WIT export
-- names (demo-world.wit) — they deliberately stay unprefixed.
set_option linter.guestlang.packageNamespace false -- because these decl names are the WIT export contract (demo-world.wit), not library API

/-- The backend's hello-world: pure integer arithmetic. -/
@[guest, schema_fn]
def double (x : UInt64) : UInt64 := x + x

/-- Branching: lowers to LCNF branches. -/
@[guest, schema_fn]
def isBig (x : UInt64) : Bool := x > 100

/-- Closure: LCNF `fun` + captured env (`pap`) — mono eta-reduces it. -/
@[guest, schema_fn]
def adder (a : UInt64) : (b : UInt64) → UInt64 := fun b => a + b

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
@[guest, schema_fn]
def doubleArea (r : UInt64) : UInt64 := area (.circle (r + r))

/-- An ESCAPING closure: returned from a conditional — mono cannot
    eta-reduce it (the body branches). Exercises pap + closure apply. -/
@[guest, schema_fn]
def pick (b : Bool) (a : UInt64) : (x : UInt64) → UInt64 :=
  fun x => if b then a + x else a * x

/-- Closures stored in objects SURVIVE mono (boxed into the erased
    world): applyAll [adder 1, adder 2] 5 runs two real paps. -/
@[guest]
def applyAll (fs : List (UInt64 → UInt64)) (x : UInt64) : UInt64 :=
  match fs with
  | [] => x
  | f :: rest => f (applyAll rest x)

@[guest, schema_fn]
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

@[guest, schema_fn]
def total (a b c : UInt64) : UInt64 := sumList [a, b, c] 0

/-- THE W9.6 WITNESS EXPORT (notes/design-guest-verified.md §4 step 3,
    the audit's bytes-in/verdict-out wrapper): the committed witness
    wire format IN (`decWitness?` — the guest-marked decode lane over
    the Codec), the W9.2 checker's verdict OUT. The version pin (`1`)
    is the demo's envelope version — a mismatching envelope decodes
    `none` → refused, loud. The CERTIFICATION CONTEXT is the v1 demo's:
    the empty field list + the empty row + the empty log — so the
    checkable claims are the literal fragment (`eqU` of literals, a
    `valid` over an all-literal expr); the record-anchored lanes
    (`col`/`strlenCol`/`chain`) resolve `none` → refused. The fuel is
    the ARTIFACT's own (`w.fuel` — §7.3: host and guest agree by
    construction). The duel rows (Oracle.lean's witness fixtures):
    valid → 1, tampered → 0 — and the tampered row is refused BY THE
    GUEST (the oracle-manifest replay pins it). -/
@[guest_std, schema_fn, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def verifyWitness (bs : List UInt8) : Bool :=
  match SchemaLang.Witness.decWitness? 1 bs with
  | none => false
  | some w =>
      SchemaLang.WitnessCheck.checkWitness w.fuel w.claim w.proof [] .nil []
