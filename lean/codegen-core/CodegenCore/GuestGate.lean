module

public meta import Lean
public meta import CodegenCore.Registry
public meta import CodegenCore.AttrKit
public meta import LintKit.GuestBan

public meta section

/- PROVENANCE: moved verbatim from wasm-backend/WasmBackend/Check.lean
   (the guest gate + the @[guest]/@[guest_std] attributes) — the STD
   package (lean/std) needs the attributes and requiring the BACKEND
   from it is a lake-require cycle (the backend's GenMain imports the
   std oleans). The gate is codegen-layer infrastructure: both the
   backend and the std package require codegen-core.

   W7.13: the PURE predicate (`Ban`/`bannedAt?`/`checkExprAt`/`checkExpr`/
   `reasons`) moved verbatim to `LintKit.GuestBan` — ONE `DeclCheck`
   (`LintKit.GuestBan.guestBanCheck`) now mounts BOTH ways: as the
   attribute GATE here (hard elab error, via `CodegenCore.mountAsGate`)
   and as the `linter.guestlang.guestBan` env-LINT (a report) in
   LintKit's runner. This module keeps the attributes, the guest-mark
   registry, and re-exports the predicate surface (`export` below) so
   downstream (`WasmBackend.Check`'s re-export, the wasm-backend #guard
   pins) sees no change. -/

/-!
# CodegenCore.GuestGate — `@[guest]`: elab-time guest-compatibility

The earliest possible correctness gate: a `@[guest]` def is scanned at
ELABORATION (`.afterCompilation` — the same mechanism as `@[schema]`)
for constructs the WASM backend cannot compile. Banned = anything whose
runtime the guest does not have:

- `Nat.*` — bignum (GMP); the guest's integers are fixed-width
- `String.*` — UTF-8 objects land with guestlang-std
- `IO.*` / `Task.*` / `Thunk.*` — host capabilities, not guest code

The PREDICATE is pure (`checkExpr : Expr → List String`) — unit-testable
(wasm-backend's Tests/Main.lean: positive + negative controls). The
attribute handler renders the violations into the elaboration error AT
THE DECL — `lake build` fails before any emitter runs. No proofs, no
LCNF: a one-pass Expr scan. The backend's `unsupported` throw then only
ever fires for constructs the scan can't see (LCNF-only shapes like
`jmp`) — belt and suspenders.

The predicate + the shared `DeclCheck` live in `LintKit.GuestBan` (the
lint mount needs them in LintKit; only codegen-core → LintKit is a legal
import direction). BOUNDARY: the guest-mark registry write and the
"applies to defs only" misuse error stay HERE, in the attribute handler
— a pure `Name → Environment → List DeclDiag` check cannot modify the
env, and a lint sweeping every decl kind has no "wrong kind" failure.

Coverage note: the scan is SYNTACTIC (constants in the elaborated
term). It over-approximates: `if n == 0` on Nat bans even when the
value is always small — correct stance for a boundary check.
-/

namespace CodegenCore.GuestGate

open Lean

-- The predicate surface, re-homed in LintKit.GuestBan (W7.13) — the
-- historical names keep resolving (WasmBackend.Check re-exports them;
-- the wasm-backend #guard pins use them via `open`).
export LintKit.GuestBan (Ban bannedAt? checkExprAt checkExpr reasonLine reasons)

/-- The guest-mark registry: every decl that PASSED a `@[guest]`/`@[guest_std]`
    check, append-only, replayed from oleans at import (the mkRegistryExt
    semantics). The wasm backend's manifest fold reads it: the marked decls
    ARE the compile roots (the manifest = the modules, the marks = the
    decls, the fold = the rest — GenMain.lean). -/
initialize guestMarkExt :
    SimplePersistentEnvExtension Name (List Name) ←
  CodegenCore.mkRegistryExt `guestMarkExt

/-- Guest-marked decls from an environment (the backend fold's entry). -/
def guestMarkedDecls (env : Environment) : List Name :=
  guestMarkExt.getState env

/-- Record the mark after the check passes (the compile-root seam). -/
def recordGuestMark (decl : Name) : CoreM Unit :=
  modifyEnv fun env => guestMarkExt.addEntry env decl

/-- The shared attribute check: the GATE mount of
    `LintKit.GuestBan.guestBanCheck` — scan the def's type + value at the
    attribute's ban level, hard-fail on diags; mark on pass. The two
    attributes (`@[guest]`/`@[guest_std]`) are one code path with the level
    as the parameter (the `@[guest_std]` error used to render STRICT
    reasons — bug 0.5 — the level-pinned `reasonLine` is the fix, and it
    lives in the shared check). GATE-SIDE, outside the shared check (the
    boundary): the "applies to defs only" misuse error and the guest-mark
    registry write. -/
def checkGuestAt (attrName : String) (level : Ban) (decl : Name) : CoreM Unit := do
  let env ← getEnv
  match env.find? decl with
  | some (.defnInfo _) =>
      mountAsGate (LintKit.GuestBan.guestBanCheck attrName level) decl
      recordGuestMark decl
  | some _ =>
      throwError s!"`@{attrName}` applies to defs only: `{decl.toString}`"
  | none => pure ()

/-- The `@[guest]` attribute: check a def's type + value at elab time. -/
def checkGuest (decl : Name) : CoreM Unit := checkGuestAt "guest" .strict decl

/-- The `@[guest_std]` attribute: the guestlang-std authoring surface —
match-only Nat + String allowed; IO/Task/Thunk + Nat arithmetic stay
banned. The std runtime ITSELF is compiled with this. -/
def checkGuestStd (decl : Name) : CoreM Unit := checkGuestAt "guest_std" .std decl

register_check_attribute `guest : "check the def compiles for the WASM guest (elab-time: bans Nat/String/IO/Task/Thunk runtimes)" := fun decl _stx _kind => (checkGuest decl : CoreM Unit)

register_check_attribute `guest_std : "the guestlang-std authoring surface (match-only Nat + String OK; IO/Task/Thunk + Nat arithmetic banned)" := fun decl _stx _kind => (checkGuestStd decl : CoreM Unit)

end CodegenCore.GuestGate
