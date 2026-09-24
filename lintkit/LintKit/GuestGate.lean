/-
LintKit.GuestGate — `@[guest]`/`@[guest_std]`: elaboration-time
guest-compatibility (mined from legacy
legacy/lean/codegen-core/CodegenCore/GuestGate.lean, ported fresh — the
legacy's `register_check_attribute`/registry substrate re-expressed
inline since no codegen-core exists in this tree yet).

The earliest possible correctness gate: a `@[guest]` def is scanned at
ELABORATION (`applicationTime := .afterCompilation`) for constructs the
WASM guest cannot compile, via `LintKit.GuestBan`'s pure predicate.
Banned = anything whose runtime the guest does not have (Nat bignum,
String, IO/Task/Thunk). The attribute handler renders the violations
into an elaboration error AT THE DECL — `lake build` fails before any
emitter runs. On pass, the decl is recorded in the guest-mark registry
(the compile-root seam; the backend's manifest fold consumes it when the
wasm lane lands — the leftover rule notes it is the mark's first reader
debt).

Coverage note: the scan is SYNTACTIC (constants in the elaborated
term). It over-approximates: `if n == 0` on Nat bans even when the
value is always small — correct stance for a boundary check.

The two attributes are one code path with the ban level as the
parameter: `@[guest]` (strict) and `@[guest_std]` (the std authoring
surface: match-only Nat + String allowed; IO/Task/Thunk + Nat
arithmetic stay banned). A `@[guest_std]` error renders std-level
reasons (the legacy bug-0.5 fix, level-pinned `reasonLine`).

GATE-side, outside the shared check (the DeclCheck boundary): the
"applies to defs only" misuse error and the guest-mark registry write.

The five questions (notes/v3/01-core.md):
- root: none — the guest boundary's gate mount.
- carrier grade: none — host machinery.
- spine reading: the interpretation stage at elaboration time (decl →
  error); the registry is the artifact-side record.
- ladder rung: n/a.
- gate row: the guest gate (this module IS it).
-/
module

public meta import Lean
public import LintKit.GuestBan

public meta section

open Lean

namespace LintKit.GuestGate

/-- The guest-mark registry: every decl that PASSED a
    `@[guest]`/`@[guest_std]` check, append-only, replayed from oleans at
    import. The wasm backend's manifest fold reads it: the marked decls
    ARE the compile roots. -/
initialize guestMarkExt :
    SimplePersistentEnvExtension Name (List Name) ←
  registerSimplePersistentEnvExtension {
    name := `guestMarkExt
    addEntryFn := fun s n => n :: s
    addImportedFn := fun ass => ass.foldl (fun s a => a.foldl (fun s n => n :: s) s) []
  }

/-- Guest-marked decls from an environment (the backend fold's entry). -/
def guestMarkedDecls (env : Environment) : List Name :=
  guestMarkExt.getState env

/-- Record the mark after the check passes (the compile-root seam). -/
def recordGuestMark (decl : Name) : CoreM Unit :=
  modifyEnv fun env => guestMarkExt.addEntry env decl

/-- The shared attribute check: the GATE mount of the guest ban — scan
    the def's type + value at the attribute's ban level, hard-fail on
    violations; mark on pass. Module-system timing: at
    `.afterCompilation` the main thread's env still holds the SIGNATURE
    AXIOM (the body elaborates async — `MutualDef`'s `commitSignature` vs
    `commitConst`), so the check awaits the committed constant via
    `getAsyncConstInfo` (the `Sym.simp` attribute's own precedent) and
    scans the real `defnInfo` directly — it cannot go through a pure
    `DeclCheck` mount, which reads the (still-placeholder) env. The
    pure `DeclCheck` shape is the LINT mount's (`GuestBan.guestBanCheck`);
    GATE-side, outside it (the boundary): the "applies to defs only"
    misuse error and the guest-mark registry write. -/
def checkGuestAt (attrName : String) (level : GuestBan.Ban) (decl : Name) : CoreM Unit := do
  -- `withoutExporting`: attribute handlers run in an EXPORTING environment
  -- (module-system: `applyAttributesCore`'s `withExporting`), where the
  -- freshly-added def still resolves to its committed SIGNATURE AXIOM —
  -- the value is only realized in the non-exported view. Without this,
  -- the gate sees the axiom and can never scan the value.
  withoutExporting do
    let info ← getAsyncConstInfo decl
    match info.toConstantInfo with
    | .defnInfo di =>
        let violations :=
          GuestBan.checkExprAt level di.type (GuestBan.checkExprAt level di.value [])
        unless violations.isEmpty do
          throwError s!"`@{attrName}` function `{decl}` is not guest-compilable:\n{GuestBan.reasons level violations}"
        recordGuestMark decl
    | _ =>
        throwError s!"`@{attrName}` applies to defs only: `{decl.toString}`"

/-- The `@[guest]` attribute: check a def's type + value at elab time. -/
def checkGuest (decl : Name) : CoreM Unit := checkGuestAt "guest" GuestBan.Ban.strict decl

/-- The `@[guest_std]` attribute: the guestlang-std authoring surface —
match-only Nat + String allowed; IO/Task/Thunk + Nat arithmetic stay
banned. The std runtime ITSELF is compiled with this. -/
def checkGuestStd (decl : Name) : CoreM Unit := checkGuestAt "guest_std" GuestBan.Ban.std decl

end LintKit.GuestGate

namespace LintKit

open LintKit.GuestGate

/-- The `@[guest]` builtin attribute (strict ban). -/
initialize guestAttr : Unit ← registerBuiltinAttribute {
  name := `guest
  descr := "check the def compiles for the WASM guest (elab-time: bans Nat/String/IO/Task/Thunk runtimes)"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => checkGuest decl
  erase := fun _decl => throwError "attribute `[guest]` cannot be erased"
}

/-- The `@[guest_std]` builtin attribute (the std ban level). -/
initialize guestStdAttr : Unit ← registerBuiltinAttribute {
  name := `guest_std
  descr := "the guestlang-std authoring surface (match-only Nat + String OK; IO/Task/Thunk + Nat arithmetic banned)"
  applicationTime := .afterCompilation
  add := fun decl _stx _kind => checkGuestStd decl
  erase := fun _decl => throwError "attribute `[guest_std]` cannot be erased"
}

end LintKit
