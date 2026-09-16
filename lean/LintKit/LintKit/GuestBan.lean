/-
LintKit.GuestBan — the guest-runtime ban as a DECL-CHECK (W7.13).

PROVENANCE: the pure predicate (`Ban`/`bannedAt?`/`checkExprAt`/`checkExpr`/
`reasons`) moved VERBATIM from `CodegenCore.GuestGate` (itself moved verbatim
from `wasm-backend/WasmBackend/Check.lean`). It lives here because the same
check mounts BOTH ways and only codegen-core → LintKit is a legal import
direction (LintKit is first in `lean_pkgs`, zero requires): the LINT mount
(`guestBanLinter` below, in the Runner table) needs the check in LintKit;
the GATE mount (the `@[guest]`/`@[guest_std]` attributes) stays in
`CodegenCore.GuestGate`, which re-exports this surface (`export`) so
downstream (`WasmBackend.Check`, the wasm-backend #guard pins) sees no
change. The guest-mark registry + attribute handlers remain in codegen-core
— the mark write is a side effect the pure check cannot carry.

The ban: anything whose runtime the WASM guest does not have —

- `Nat.*` — bignum (GMP); the guest's integers are fixed-width
- `String.*` — UTF-8 objects land with guestlang-std
- `IO.*` / `Task.*` / `Thunk.*` — host capabilities, not guest code

The scan is SYNTACTIC (constants in the elaborated term, pre-LCNF) and
over-approximates: `if n == 0` on Nat bans even when the value is always
small — correct stance for a boundary check.

The lint (`linter.guestlang.guestBan`) is default-OFF tree-wide (the
recursiveSimpEqns precedent): it answers "would this def pass `@[guest_std]`"
for EVERY def of a package — a census question, not a gate. Enforcement
stays with the attributes. Census run:
  cd lean/<pkg> && lake env <guestlang-lint> --enable=linter.guestlang.guestBan <roots>

The option is declared at top level (see LintKit.Basic's header note).
-/
import LintKit.DeclCheck

open Lean Meta Linter EnvLinter

@[nolint linter.guestlang.packageNamespace "option declarations must be top-level: the builtin_env_linter registration checks `env.contains <raw option name>` at attribute time (see LintKit.Basic header)"]
register_option linter.guestlang.guestBan : Bool := {
  defValue := false
  descr := "report declarations that would FAIL `@[guest_std]` (banned \
    guest runtimes: IO/Task/Thunk, Nat arithmetic) — default off: a census \
    lint, not a gate; the `@[guest]`/`@[guest_std]` attributes enforce"
}

-- Feed the option into v4.33's per-declaration snapshot machinery (the
-- AxiomAllowlist pattern).
initialize Linter.addEnvLinterOption linter.guestlang.guestBan

namespace LintKit.GuestBan

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

/-- PURE predicate: every banned constant root in the Expr, in scan
order, deduped. The testable core of the `@[guest]`/`@[guest_std]`
gates. Scan = core's memoized `Expr.getUsedConstants` REVERSED: the
original hand-fold visited argument-before-function / body-before-type
(reverse pre-order — e.g. `f Nat.x` lists `"Nat"` before `"IO"` for
`IO.println (Nat.add ..)`), and the #guard tests pin that order. -/
def checkExprAt (level : Ban) (e : Expr) (acc : List String := []) : List String :=
  e.getUsedConstants.toList.reverse.foldl (init := acc) fun a n =>
    match (bannedAt? level n).map fun _ => n.getRoot.toString with
    | some h => if a.contains h then a else a ++ [h]
    | none => a

/-- The strict predicate (the `@[guest]` surface). -/
def checkExpr (e : Expr) (acc : List String := []) : List String :=
  checkExprAt .strict e acc

/-- One rendered violation line (the `- \`X\` — reason` row), at the
    check's OWN ban level — the `@[guest_std]` error used to render STRICT
    reasons (bug 0.5). Violations are ROOTS: at `.std` a `Nat` root can
    only have come from ARITHMETIC (match-only Nat is legal), so the reason
    is the arithmetic one, not the strict bignum one. -/
def reasonLine (level : Ban) (v : String) : String :=
  let why? := match level, v with
    | .std, "Nat" =>
      some "Nat arithmetic is GMP — std code may only MATCH on Nat (zero/succ patterns)"
    | _, _ => bannedAt? level v.toName
  match why? with
  | some why => s!"- `{v}` — {why}"
  | none => s!"- `{v}`"

/-- Rendered reason for each violation (for the elab error), at the
    check's OWN ban level. -/
def reasons (level : Ban) (violations : List String) : String :=
  String.intercalate "\n" (violations.map (reasonLine level))

/-- The guest ban as the SHARED decl-check (W7.13): scan the def's type +
    value at `level`; one diag carrying the historical error text
    (`attrName` is the mount's display name — the gate throws the message
    verbatim, the lint reports it). Non-defs are NOT findings: the lint
    mount sweeps every decl kind, and "wrong kind" is not a violation —
    the attribute's "applies to defs only" error is gate-side misuse
    validation (in `CodegenCore.GuestGate.checkGuestAt`), like the
    guest-mark write. -/
def guestBanCheck (attrName : String) (level : Ban) : LintKit.DeclCheck :=
  fun decl env =>
    match env.find? decl with
    | some (.defnInfo di) =>
        let violations := checkExprAt level di.type (checkExprAt level di.value [])
        if violations.isEmpty then []
        else [{ code := String.intercalate "," violations
              , message := s!"`@{attrName}` function `{decl}` is not guest-compilable:\n{reasons level violations}" }]
    | _ => []

/-- The LINT mount: the std-level ban as a report (default off — see the
    option's comment). -/
meta def guestBanLinter : EnvLinter :=
  LintKit.mountAsLinter (guestBanCheck "guest_std" .std)
    "no declaration uses runtimes the WASM guest cannot compile"
    "declarations using banned guest runtimes (the `@[guest_std]` ban)"

end LintKit.GuestBan

@[builtin_env_linter linter.guestlang.guestBan]
meta def LintKit.GuestBan.guestBanLinter.reg : EnvLinter := LintKit.GuestBan.guestBanLinter
