/-
Smoke fixture for lean-sys-v433: exported pure functions, compiled to C by
build.rs (`lean -c`) and linked into `tests/smoke.rs`, which initializes the
Lean runtime in-process and calls them over the C ABI.
-/

/-- Scalar round-trip: UInt64 crosses unboxed both ways. -/
@[export lean_sys_smoke_add40]
def add40 (n : UInt64) : UInt64 := n + 40

/-- Heap-object round-trip: String crosses as a refcounted `lean_object*`. -/
@[export lean_sys_smoke_greet]
def greet (name : String) : String := s!"hello from lean, {name}"
