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
- `crossCall` — the cross-decl call REFUSAL fixture (the call lane is
  wasmcore's in-flight work).

Everything beyond the fragment is the named exclusion set
(Lower.lean's header) — the refusals pin it.
-/

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
