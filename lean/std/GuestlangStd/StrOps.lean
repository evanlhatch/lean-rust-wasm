import CodegenCore.GuestGate
/-
# GuestlangStd.StrOps — the string intrinsics' DECLARATIONS

The std ops' bodies are never compiled (the backend maps the NAMES to
the runtime primitives — see WasmBackend.stdOp?); they live here so the
impl module can use them and the oracle can EVAL them. The bodies are
the real Lean implementations (the oracle's authority).
-/

namespace GuestlangStd

/-- Byte length of a string. Real body = the oracle; the backend emits
    `call $string_len` for the NAME (the body is never compiled). -/
@[guest_std]
def strlen (s : String) : UInt64 := s.length.toUInt64

/-- Concatenation: allocates a fresh string object, copies both byte
    runs (`memory.copy`). Real body = the oracle. -/
@[guest_std]
def strcat (a b : String) : String := a ++ b

end GuestlangStd
