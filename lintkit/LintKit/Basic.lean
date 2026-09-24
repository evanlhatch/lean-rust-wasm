/-
LintKit.Basic — shared infrastructure for the tree's env-linters.

MINED from `legacy/lean/LintKit/LintKit/Basic.lean` (the proven pattern,
ported fresh per notes/v3/14-build-map.md): the `@[nolint]` parametric
attribute (the per-site opt-out), the shared skip discipline
(`skipDecl`: private/internal/generated/auxiliary names, equation-lemma
shapes, constructors, eliminators), and the
`register_guestlang_linter` one-liner registration macro.

Owns the `@[nolint linter.guestlang.<x> "reason"]` attribute; v4.33 core
has no `builtin_nolint` (checked the 4.33 toolchain: only the doc comment
in EnvLinter/Basic.lean).

The `linter.guestlang.*` options deliberately live at TOP LEVEL in their
own linter modules, not here and not inside a namespace: `register_option`
inside a namespace prefixes the option's declaration name, while the
`builtin_env_linter` attribute checks `env.contains <raw option name>` at
registration time — option and attribute must be declared together,
outside any namespace (the scratch-verified v4.33 behavior).

Deliberate exclusions: no LSpec/mathlib (core-only so any package may
import it); the driver lives in `LintKit.Runner`; the `@[derived]`
generating-command stamp of the legacy Basic arrives with the codegen
lane (nothing here consumes it — the doctrine's nothing-without-a-
consumer rule).

The five questions (notes/v3/01-core.md):
- root: none — the lint substrate (elab infrastructure, host-side).
- carrier grade: none — meta-level machinery, not a data crossing.
- spine reading: none — the linters/runner interpret environments;
this is their shared mount.
- ladder rung: n/a (host machinery; no proof family).
- gate row: infrastructure FOR the axiom gate + the lintkit sweep
(LintKit itself is a gated package: its roots ride the axiom report).
-/
module

public meta import Lean

public meta section

open Lean Meta

namespace LintKit

/-- Parameter of `@[nolint]`: the linter options to silence, plus the
justification (kept for readers; not machine-checked beyond presence at
the site). -/
structure NolintParam where
  linters : Array Name
  reason  : String
  deriving Inhabited

end LintKit

-- Attribute lookup (`Lean.Elab.Attributes.elabAttr`) resolves a custom
-- attribute by `Name.mkSimple` over the FULL syntax kind — for kind
-- `LintKit.lintkitNolint` that is `lintkitNolint` — so the registered
-- attribute name must be exactly the kind's last component. (The first
-- port registered `guestlangNolint` here and `@[nolint]` never resolved:
-- the fixture teeth were its first real consumer.) The kind stays
-- `LintKit.`-prefixed (the packageNamespace rule).
syntax (name := LintKit.lintkitNolint) "nolint " ident* (str)? : attr

initialize LintKit.nolintAttr : ParametricAttribute LintKit.NolintParam ←
  registerParametricAttribute {
    name := `lintkitNolint
    descr := "Opt a declaration out of the tree's env-linters: \
      `@[nolint linter.guestlang.<option> \"reason\"]`. The reason is required."
    getParam := fun _ stx => do
      match stx with
      | `(attr| nolint $ids* $[$r?]?) =>
        pure { linters := ids.map (·.getId)
               reason := match r? with
                 | some s => s.getString
                 | none => "" }
      | _ => throwError "invalid `@[nolint]` syntax: expected `nolint <linter>* <reason>?`"
  }

namespace LintKit

/-- Is `decl` opted out of the linter with option name `optName` via
`@[nolint]`? -/
def hasNolint (env : Environment) (decl optName : Name) : Bool :=
  match nolintAttr.getParam? env decl with
  | some p => p.linters.contains optName
  | none   => false

/-! ## `register_guestlang_linter` — the env-linter registration one-liner

Every env-linter carries the same three-part ritual: a `register_option`
block (top level — see the module header), the `addEnvLinterOption`
snapshot hookup, and the `@[builtin_env_linter]` mount def. One command:

    register_guestlang_linter linter.guestlang.axiomAllowlist
      LintKit.axiomAllowlistLinter "flag declarations …"

A CENSUS linter (default OFF — the recursiveSimpEqns/guestBan precedent:
it answers a question for every def of a package, it does not gate) adds
the `default_false` token:

    register_guestlang_linter linter.guestlang.guestBan
      LintKit.GuestBan.guestBanLinter default_false
      "report declarations that would fail `@[guest_std]` …"

The linter def (`<name>` — a `LintKit`-prefixed `EnvLinter` value, its
test defined above the call) keeps its exact name; the mount lands at
`<name>.reg`, the name the stock `lake lint` path knows. -/

syntax (name := LintKit.registerGuestlangLinter)
  "register_guestlang_linter " ident ident ("default_false")? str : command

open Lean.Elab.Command in
@[command_elab LintKit.registerGuestlangLinter]
meta def elabRegisterGuestlangLinter : Lean.Elab.Command.CommandElab := fun stx => do
  let opt := stx[1].getId
  let linter := stx[2].getId
  let descr := stx[4].isStrLit?.getD ""
  let defValue := stx[3].isNone  -- `default_false` present ⇒ census linter
  -- (1) the option (exact name), (2) the per-decl snapshot hookup,
  -- (3) the stock-`lake lint` mount at `<name>.reg`.
  Lean.Elab.Command.elabCommand (← `(register_option $(mkIdent opt) : Bool := {
    defValue := $(quote defValue)
    descr := $(quote descr)
  }))
  Lean.Elab.Command.elabCommand (← `(initialize Lean.Linter.addEnvLinterOption $(mkIdent opt)))
  Lean.Elab.Command.elabCommand (← `(@[builtin_env_linter $(mkIdent opt)]
    meta def $(mkIdent (linter.str "reg")) : Lean.Linter.EnvLinter.EnvLinter :=
      $(mkIdent linter)))

/-- Skip declarations no linter should ever look at: private names,
internal names, macro expansions, and compiler/relator-generated
auxiliaries (`proof_*`, `match_*`, `unsafe_*`, `grind_*`, recursor/ctor
helpers — see `Lean.isAutoDeclOrPrivate_Internal`), plus
equation-lemma-shaped names (`foo.eq_1`, `foo.eq_def`) whose findings
would duplicate the report on their parent definition, plus constructors
and eliminators of inductive types (kernel-generated; their names follow
the inductive's — the inductive decl itself is the report site). -/
def skipDecl (decl : Name) : CoreM Bool := do
  if ← Lean.isAutoDeclOrPrivate_Internal decl then return true
  let env ← getEnv
  if env.isConstructor decl then return true
  match decl with
  | .str p s =>
    -- equation-lemma and unfold-lemma names: the parent def is the report site
    if s.startsWith "eq_" || s == "eq_def" then return true
    -- the ofNat∘ctorIdx law the compiler generates under an enum-like
    -- inductive's namespace (observed under `deriving DecidableEq`)
    if s == "ofNat_ctorIdx" then return true
    -- eliminators: `isAutoDeclOrPrivate_Internal` covers `recOn`/`casesOn`/
    -- `brecOn`/`below`/… but not plain `rec`
    if let some (.inductInfo _) := env.find? p then
      return s == "rec"
    return false
  | _ => return false

end LintKit
