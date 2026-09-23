import CodegenCore.GuestGate

/-!
# WasmBackend.Check — the guest gate, re-exported

The gate lives in `CodegenCore.GuestGate` (the std package needs its
attributes; requiring the backend from std would be a lake-require
cycle). This module re-exports the blessed surface under the historical
path — existing `import WasmBackend.Check` sites keep working. The
attributes register ONCE (in codegen-core).
-/

export CodegenCore.GuestGate (Ban bannedAt?
  checkExprAt checkExpr reasons checkGuest checkGuestStd)
