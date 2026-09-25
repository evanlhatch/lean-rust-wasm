/-
# GuestTests.Fixture — the compiled functions the end-to-end pin reads

The test fixture: plain `def`s compiled normally (the package builds
this module), whose impure-phase LCNF the driver reads IN-PROCESS
(Guest.Lcnf's re-run discipline — the impure phase is not persisted
in oleans). The slice's fragment (probed against the real pipeline's
impure phase — each fixture pins one construct's EXACT shape):

- `add64` — the pin: a UInt64 add through the `binop?` fap surface.
- `sel64` — the control flow: a Bool scrutinee's `cases` (the
  scalar-branch discipline; the arms return the params).
- `jpShared` — THE join-point shape the pipeline emits (probed: a
  shared continuation lowers to `jp` + `goto`s from the case arms).
- `jpThree` — NESTED cases (a case arm carrying another case).
- `Small`/`smallTag` — the tag discipline: a scalar-representable
  enum (all ctors payload-free) branches on the unboxed tag.
- `u32lane`/`u32cmp`/`u8sub`/`u64shr`/`i32wrap` — the op-surface
  growth (the i32 lane, the u8 mask, the shift, the width conversion).
- `multiA`/`multiB` — the multi-decl module (call-disjoint decls).
- `sumTo` — the SELF-RECURSIVE decl (recursive callees survive the
  inliner): the cross-decl call lane at the own index, the real
  pipeline's fap.
- `sumMain` — the caller: a cross-decl call to `sumTo` through the
  REAL pipeline (the two-decl program; the inliner honesty is pinned
  separately — the small `add64` call in `crossCall` dissolves).
- `crossCall` — the INLINER-HONESTY fixture: a call to a SMALL decl
  (`add64`) that LCNF inlines away — the lowering sees what LCNF
  PRODUCES (no fap, no refusal, the inlined body).
- `applyTwice`/`addN`/`twiceAdd5` — THE CLOSURE FAMILY: `addN 5`
  rides as a partial application (the pap lane's real face);
  `twiceAdd5` pulls the `_closed` fixpoint family (the `_closed_0`
  producer + the `_boxed_const_1` literal + the `_lam_1` closure
  body + the `_lam_1._boxed` adapter) into the pipeline's local
  cache — the tests read it with `Guest.readFamily?` (ONE run over
  the root); `applyTwice`'s own body is the FIRST-CLASS application
  (the applied fvar has no pap provenance — the indirect-call
  lane's named refusal, the pinned tooth).
- `listSum`/`listMain` — THE LIST DISCIPLINE (the object tag
  dispatch's payoff): the fold's cons/nil dispatch (the tag @4 read
  + the oproj field reads + the self-recursive fap + the boxed-Nat
  add + the result's dec) and the literal's cons-chain construction
  (the `_closed_0/1/2` family shape).

Everything beyond the fragment is the named exclusion set
(Lower.lean's header) — the refusals pin it.

Import note: `LintKit.Basic` is imported ONLY for the `natAdd`
fixture's `@[nolint]` opt-out row (LintKit is core-only: any package
may import it — the Lower.lean convention). The driver's LCNF reader
is unaffected: it reads the fixture decls, not the import closure.
-/

import LintKit.Basic

def GuestTests.add64 (a b : UInt64) : UInt64 := a + b

def GuestTests.sel64 (c : Bool) (a b : UInt64) : UInt64 :=
  if c then a else b

def GuestTests.jpShared (c : Bool) (a b : UInt64) : UInt64 :=
  (if c then a else b) + 1

def GuestTests.jpThree (n : UInt64) : UInt64 :=
  if n < 10 then 1 else if n < 20 then 2 else 3

inductive GuestTests.Small where
  | red | green | blue

def GuestTests.smallTag (s : Small) : UInt64 :=
  match s with
  | .red => 0
  | .green => 1
  | .blue => 2

def GuestTests.u32lane (a b : UInt32) : UInt32 := a * b + a

def GuestTests.u32cmp (a b : UInt32) : Bool := a < b

def GuestTests.u8sub (a b : UInt8) : UInt8 := a - b

def GuestTests.u64shr (n : UInt64) : UInt64 := n >>> 1

def GuestTests.i32wrap (n : UInt64) : UInt32 := n.toUInt32

def GuestTests.multiA (a b : UInt64) : UInt64 := a * b + a

def GuestTests.multiB (x : UInt64) : UInt64 := x + 1

def GuestTests.crossCall (n : UInt64) : UInt64 := add64 n 1

/-- The SELF-RECURSIVE decl: recursive callees survive the inliner, so
    the real pipeline hands the lowering a fap naming the decl's OWN
    sibling name — the call lane lowers it to `call` at the own index;
    the recursion's only bound is the executor's fuel (the honest
    `outOfFuel`). The termination proof is the fixture's own (UInt64
    subtraction's toNat face), never part of the lowering. -/
def GuestTests.sumTo (n : UInt64) : UInt64 :=
  if _h : n = 0 then 0 else n + sumTo (n - 1)
termination_by n.toNat
decreasing_by
  have hne : ¬ (n = 0) := _h
  have h1 : 0 < n.toNat := by
    cases hn : n.toNat with
    | zero =>
        exact absurd
          (UInt64.toNat.inj (by rw [hn]; exact UInt64.toNat_zero.symm)) hne
    | succ _ => omega
  have hone : (1 : UInt64).toNat = 1 := rfl
  have h2 : (n - 1).toNat = n.toNat - 1 :=
    UInt64.toNat_sub_of_le (a := n) (b := 1)
      (UInt64.le_iff_toNat_le.mpr (by rw [hone]; omega))
  rw [h2]
  omega

def GuestTests.sumMain (n : UInt64) : UInt64 := sumTo n + 1

def GuestTests.applyTwice (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f (f x)

/-- THE FIRST-CLASS FIXTURES (the indirect-call lane's real face): a
capture-free function VALUE (`mkTriple`) flows through a CONSUMER
(`useFn`) that applies its closure PARAM first-class — the applied
fvar has no pap provenance, so the application lowers to
call_indirect (the fnIdx @8 IS the table index). `tripleMain` is the
end-to-end: the closure flows through the sibling call + the first-
class dispatch, the answer x·3. A PARTIAL closure (the pap family)
applied first-class answers the executor's indirect type trap — the
type discipline's honesty (never a wrong call). -/
def GuestTests.mkTriple : UInt64 → UInt64 := fun y => y * 3

def GuestTests.useFn (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f x

def GuestTests.tripleMain (x : UInt64) : UInt64 := useFn mkTriple x

def GuestTests.useFnBig (f : UInt64 → UInt64) (x y : UInt64) : UInt64 :=
  let a := f (x * y + 7)
  let b := f (x + y)
  if a < b then a else b

def GuestTests.bigMain (x : UInt64) : UInt64 := useFnBig mkTriple x 900

def GuestTests.addN (n x : UInt64) : UInt64 := x + n

/-- The closure-family consumer: `addN 5` rides as a PARTIAL
    application (the pap lane's real face); the FAMILY (the `_closed_0`
    fixpoint + the `_boxed_const_1` producer + the `_lam_1` closure
    body + the `_lam_1._boxed` adapter) is the real-pipeline closure
    module the tests lower and run. -/
def GuestTests.twiceAdd5 (x : UInt64) : UInt64 := applyTwice (addN 5) x

/-! ## The boxed-Nat lane's fixtures (the real pipeline's face)

The probe-observed impure-phase shapes: a `Nat` rides `tobj` (params/
results), a Nat literal binds `tagged`, and the arith faps arrive as
`Nat.add`/`mul`/`sub`/`decLt`/`decEq`/`decLe`. The compiler CONSTANT-
FOLDS small Nat arithmetic (observed: `natMain`'s operands fold to
ONE literal — the literal-box lane's end-to-end face) and delivers
statically-overflowing products as DIRECT literals ≥ the cap (the
compile-time design-error refusal — the model's overflow honesty
where static). -/

-- The nolint row: the fixture's body IS the tested content — the
-- boxed-Nat add's LCNF shape (the fap to `Nat.add`) is what the
-- lowering pins read; a shared upstream spelling would dissolve the
-- fixture's own decl body (the dup-body linter's opt-out, the named
-- reason).
@[nolint linter.guestlang.dupDefBodies "the fixture's body is the tested content — the lowering pins read THIS decl's add shape; a shared upstream spelling dissolves the fixture"]
def GuestTests.natAdd (a b : Nat) : Nat := a + b

def GuestTests.natMul (a b : Nat) : Nat := a * b

def GuestTests.natLt (a b : Nat) : Bool := a < b

def GuestTests.natEq (a b : Nat) : Bool := a == b

/-- The literal-box lane end-to-end: the folded sum 1.7e18 below the
cap — the module is ONE boxed literal + a return; the run's answer
is read from the box's payload @8. -/
def GuestTests.natMain : Nat := GuestTests.natAdd 900000000000000000 800000000000000000

/-- The STATICALLY-overflowing product: the compiler's folding
delivers 2305843009213693951 * 4 = 9223372036854775804 ≥ 2^62 as a
direct `lit.nat` — the lowering refuses with the cap's design-error
diagnostic (the model's overflow honesty where static). -/
def GuestTests.natMulRun : Nat := GuestTests.natMul 2305843009213693951 4

/-! ## The list discipline's fixtures (the object tag dispatch's payoff)

The LIST as the cons/nil objects: the literal's cons chain allocates the
objects (the object seed's ctor lane), the fold's `match l with` compiles
to the OBJECT TAG DISPATCH (the tag @4 read + the per-alt dispatch), the
cons arm's fields ride the pipeline's oproj field-binding lets (the
proved slots @8/@16), and the recursion is the cross-decl call lane's
self-recursive fap. -/

def GuestTests.listSum (l : List Nat) : Nat :=
  match l with
  | .nil => 0
  | .cons h t => h + listSum t

/-- The fold's caller: the list literal's construction + the call (the
end-to-end list program the tests run). -/
def GuestTests.listMain : Nat := GuestTests.listSum [7, 8]
