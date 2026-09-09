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

The PREDICATE is pure (`checkExpr : Expr → List String`) — unit-testable
(Tests/Main.lean: positive + negative controls). The attribute handler
renders the violations into the elaboration error AT THE DECL — `lake
build` fails before any emitter runs. No proofs, no LCNF: a one-pass
Expr scan. The backend's `unsupported` throw then only ever fires for
constructs the scan can't see (LCNF-only shapes like `jmp`) — belt and
suspenders.

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

/-- PURE predicate: every banned constant root in the Expr, in scan
order, deduped. The testable core of the `@[guest]` gate. -/
partial def checkExpr (e : Expr) (acc : List String := []) : List String :=
  match e with
  | .const n _ =>
      let hit := (banned? n).map fun _ => n.getRoot.toString
      match hit with
      | some h => if acc.contains h then acc else acc ++ [h]
      | none => acc
  | .app f a => checkExpr f (checkExpr a acc)
  | .lam _ t b _ => checkExpr t (checkExpr b acc)
  | .letE _ t v b _ => checkExpr t (checkExpr v (checkExpr b acc))
  | .forallE _ t b _ => checkExpr t (checkExpr b acc)
  | .mdata _ e => checkExpr e acc
  | .proj _ _ e => checkExpr e acc
  | _ => acc

/-- Rendered reason for each violation (for the elab error). -/
def reasons (violations : List String) : String :=
  String.intercalate "\n" (violations.map fun v =>
    match banned? v.toName with
    | some why => s!"- `{v}` — {why}"
    | none => s!"- `{v}`")

/-- The `@[guest]` attribute: check a def's type + value at elab time. -/
def checkGuest (decl : Name) : CoreM Unit := do
  let env ← getEnv
  match env.find? decl with
  | some (.defnInfo di) =>
      let violations := checkExpr di.type (checkExpr di.value [])
      if !violations.isEmpty then
        throwError s!"`@[guest]` function `{decl}` is not guest-compilable:\n{reasons violations}"
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
