/-
FFI fixture for lean-ffi (W6.2): `ByteArray → ByteArray`-shaped exports,
compiled to C by build.rs (`lean -c`) and linked into `tests/roundtrip.rs`,
which initializes the Lean runtime in-process and calls them over the safe
`lean_ffi` API.
-/

/-- Echo the REVERSE of the input bytes: the byte-array marshaling channel
exercised end-to-end in both directions. -/
@[export lean_ffi_echo_reverse]
def reverseBytes (bs : ByteArray) : ByteArray :=
  ⟨bs.data.reverse⟩

/-- A 2-object-field ctor (tag 0) for the tag-checked `LeanCtorObject`
access tests: field 0 echoes the input, field 1 its reverse. -/
@[export lean_ffi_mk_pair]
def mkPair (bs : ByteArray) : ByteArray × ByteArray :=
  (bs, ⟨bs.data.reverse⟩)
