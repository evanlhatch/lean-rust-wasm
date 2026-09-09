import Lean

/-!
# WasmBackend.Check — `@[guest]`: elab-time guest-compatibility

The earliest possible correctness gate: a `@[guest]` def is scanned at
ELABORATION (`.afterCompilation` — the same mechanism as `@[schema]`)
for constructs the WASM backend cannot compile. Banned = anything whose
runtime the guest does not have:

- `Nat.*` — bignum (GMP); the guest's integers are fixed-width
- `String.*` — UTF-8 objects land with guestlang-std
- `IO.*` / `Task.*` / `Thunk.*` — host capabilities, not guest code

Failure is an elaboration error AT THE DECL — `lake build` fails before
any emitter runs. No proofs, no LCNF: a one-pass Expr scan. The
backend's `unsupported` throw then only ever fires for constructs the
scan can't see (LCNF-only shapes like `jmp`) — belt and suspenders.

Coverage note: the scan is SYNTACTIC (constants in the elaborated
term). It over-approximates: `if n == 0` on Nat bans even when the
value is always small — correct stance for a boundary check.
-/

namespace WasmBackend.Check

open Lean

/-- Banned root namespaces → the reason (shown in the error). -/
def banned? (n : Name) : Option String :=
  let root := n.getRoot
  if root == `Nat then some "Nat is bignum (GMP) — the guest has fixed-width integers only (use UInt64/Int64)"
  else if root == `String then some "String runtime lands with guestlang-std — not yet compilable"
  else if root == `IO then some "IO is a host capability — guest functions must be pure over guestlang-std's WASI layer"
  else if root == `Task then some "Task is the host scheduler — not guest code"
  else if root == `Thunk then some "Thunk (laziness) needs heap + scheduler — not guest code"
  else none

/-- Scan one Expr for banned constants (Expr trees are finite — no
termination concern; def self-reference is a leaf const). -/
partial def scan (e : Expr) : CoreM Unit := do
  match e with
  | .const n _ =>
      match banned? n with
      | some why =>
          throwError "WasmBackend: `@[guest]` uses `{n}` — {why}"
      | none => pure ()
  | .app f a => scan f; scan a
  | .lam _ t b _ => scan t; scan b
  | .letE _ t v b _ => scan t; scan v; scan b
  | .forallE _ t b _ => scan t; scan b
  | .mdata _ e => scan e
  | .proj _ _ e => scan e
  | _ => pure ()

/-- The `@[guest]` attribute: check a def's type + value at elab time. -/
def checkGuest (decl : Name) : CoreM Unit := do
  let env ← getEnv
  match env.find? decl with
  | some (.defnInfo di) =>
      scan di.type
      scan di.value
  | some _ =>
      throwError "`@[guest]` applies to defs only: `{decl.toString}`"
  | none => pure ()

initialize registerBuiltinAttribute {
  name := `guest
  descr := "check the def compiles for the WASM guest (elab-time: bans Nat/String/IO/Task/Thunk runtimes)"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => (checkGuest decl : CoreM Unit)
}

end WasmBackend.Check
