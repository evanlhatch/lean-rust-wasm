import CodegenCore.GuestGate

/-!
# WasmBackend.Check — the guest gate, re-exported

The gate MOVED to `CodegenCore.GuestGate` (the std package needs the
attributes; requiring the backend from std is a lake-require cycle).
This module re-exports the blessed surface under the historical path —
existing `import WasmBackend.Check` sites keep working. The attributes
register ONCE (in codegen-core).
-/

export CodegenCore.GuestGate (Ban bannedAt?
  checkExprAt checkExpr reasons checkGuest checkGuestStd)
