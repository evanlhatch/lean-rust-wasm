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

/-- The BAN LEVEL: strict (the app-authoring surface) vs std (the
    guestlang-std authoring surface — match-only Nat is fine: the LCNF
    for a match on Nat = ctor dispatch on the zero/succ object, no GMP
    arithmetic; Nat ARITHMETIC consts stay banned). String opens up in
    std mode too (the std runtime implements it). -/
inductive Ban where
  | strict | std

/-- Banned root namespaces → the reason (shown in the error). -/
def bannedAt? (level : Ban) (n : Name) : Option String :=
  let root := n.getRoot
  if root == `IO then some "IO is a host capability — guest functions must be pure over guestlang-std's WASI layer"
  else if root == `Task then some "Task is the host scheduler — not guest code"
  else if root == `Thunk then some "Thunk (laziness) needs heap + scheduler — not guest code"
  else if root == `Nat then
    match level with
    | .strict => some "Nat is bignum (GMP) — the guest has fixed-width integers only (use UInt64/Int64)"
    | .std =>
      -- match-only Nat is std-legal; ARITHMETIC is GMP — banned
      let s := n.toString
      let arith := ["Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod",
        "Nat.pred", "Nat.pow", "Nat.gcd", "Nat.log2"].any (fun op => s == op || s.startsWith (op ++ "."))
      if arith then some "Nat arithmetic is GMP — std code may only MATCH on Nat (zero/succ patterns)"
      else none
  else if root == `String then
    match level with
    | .strict => some "String runtime lands with guestlang-std — not yet compilable"
    | .std => none
  else none

/-- STRICT ban (the `@[guest]` surface). -/
def banned? (n : Name) : Option String := bannedAt? .strict n

/-- PURE predicate: every banned constant root in the Expr, in scan
order, deduped. The testable core of the `@[guest]`/`@[guest_std]`
gates. -/
partial def checkExprAt (level : Ban) (e : Expr) (acc : List String := []) : List String :=
  match e with
  | .const n _ =>
      let hit := (bannedAt? level n).map fun _ => n.getRoot.toString
      match hit with
      | some h => if acc.contains h then acc else acc ++ [h]
      | none => acc
  | .app f a => checkExprAt level f (checkExprAt level a acc)
  | .lam _ t b _ => checkExprAt level t (checkExprAt level b acc)
  | .letE _ t v b _ => checkExprAt level t (checkExprAt level v (checkExprAt level b acc))
  | .forallE _ t b _ => checkExprAt level t (checkExprAt level b acc)
  | .mdata _ e => checkExprAt level e acc
  | .proj _ _ e => checkExprAt level e acc
  | _ => acc

/-- The strict predicate (the `@[guest]` surface). -/
def checkExpr (e : Expr) (acc : List String := []) : List String :=
  checkExprAt .strict e acc

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
      let violations := checkExprAt .strict di.type (checkExprAt .strict di.value [])
      if !violations.isEmpty then
        throwError s!"`@[guest]` function `{decl}` is not guest-compilable:\n{reasons violations}"
  | some _ =>
      throwError "`@[guest]` applies to defs only: `{decl.toString}`"
  | none => pure ()

/-- The `@[guest_std]` attribute: the guestlang-std authoring surface —
match-only Nat + String allowed; IO/Task/Thunk + Nat arithmetic stay
banned. The std runtime ITSELF is compiled with this. -/
def checkGuestStd (decl : Name) : CoreM Unit := do
  let env ← getEnv
  match env.find? decl with
  | some (.defnInfo di) =>
      let violations := checkExprAt .std di.type (checkExprAt .std di.value [])
      if !violations.isEmpty then
        throwError s!"`@[guest_std]` function `{decl}` is not guest-compilable:\n{reasons violations}"
  | some _ =>
      throwError "`@[guest_std]` applies to defs only: `{decl.toString}`"
  | none => pure ()

initialize registerBuiltinAttribute {
  name := `guest
  descr := "check the def compiles for the WASM guest (elab-time: bans Nat/String/IO/Task/Thunk runtimes)"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => (checkGuest decl : CoreM Unit)
}

initialize registerBuiltinAttribute {
  name := `guest_std
  descr := "the guestlang-std authoring surface (match-only Nat + String OK; IO/Task/Thunk + Nat arithmetic banned)"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => (checkGuestStd decl : CoreM Unit)
}

end WasmBackend.Check
