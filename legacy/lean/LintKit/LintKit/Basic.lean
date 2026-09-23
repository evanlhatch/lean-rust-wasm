/-
LintKit.Basic — shared infrastructure for the guestlang linters
(notes/lean-refactor-guide.md Phase 6, notes/lean-doctrine.md §3).

Owns the `@[nolint linter.guestlang.<x> "reason"]` attribute (the per-site
opt-out the refactor guide spells `@[nolint]`; v4.33 core has no
`builtin_nolint` (checked the 4.33 toolchain: only the doc comment in
EnvLinter/Basic.lean)) and the skip
predicate shared by every linter (private/internal/compiler-generated
declarations are never linted).

The `linter.guestlang.*` options deliberately live at TOP LEVEL in their own
linter modules, not here and not inside a namespace: `register_option`
inside a namespace prefixes the option's declaration name, while the
`builtin_env_linter` attribute checks `env.contains <raw option name>` at
registration time — option and attribute must be declared together, outside
any namespace (the scratch-verified v4.33 behavior).

Deliberate exclusions: no LSpec/mathlib (core-only so any package may import
it); the driver lives in `LintKit.Runner`, not here, so this module stays
cheap to import at a nolint site.
-/
module

public meta import Lean

public meta section

open Lean Meta

namespace LintKit

/-- Parameter of `@[nolint]`: the linter options to silence, plus the
justification (kept for readers; not machine-checked beyond presence at the
site — the `noLinterDisable` text lint covers `set_option` opt-outs, and
review covers this attribute). -/
structure NolintParam where
  linters : Array Name
  reason  : String
  deriving Inhabited

end LintKit

-- Attribute lookup uses the LAST component of the syntax kind
-- (`Lean.Elab.Attributes.elabAttr`: `.str _ s => Name.mkSimple s`), so the
-- kind stays `LintKit.`-prefixed (the packageNamespace rule) while the
-- registered attribute name is the unprefixed `guestlangNolint`.
syntax (name := LintKit.guestlangNolint) "nolint " ident* (str)? : attr

initialize LintKit.nolintAttr : ParametricAttribute LintKit.NolintParam ←
  registerParametricAttribute {
    name := `guestlangNolint
    descr := "Opt a declaration out of guestlang env-linters: \
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

/-- `@[derived]` — the GENERATING-COMMAND stamp: a `declare_*`-style command
    (or the `addDecl` route) marks every declaration it EMITS, so env-linters
    exempt generated output STRUCTURALLY. The stamp replaces the per-consumer
    `set_option linter.guestlang.packageNamespace false` ritual: a generated
    decl has no honest source site to carry a per-site opt-out (the comment
    the ritual sites repeat: "the framework's registration command emits the
    instances into SchemaLang by construction; no source-site attribute
    exists"). Consulted via `hasDerived`; stamped by the attribute
    (elabCommand route: `@[derived]` in the generated source) or
    `stampDerived` (addDecl route). Registration lives HERE, not in
    codegen-core: LintKit is first in the import DAG (the linter must consult
    the stamp, and LintKit cannot import codegen-core — the importBan row). -/
initialize derivedAttr : TagAttribute ← registerTagAttribute `derived "generated output: the emitting command stamps this; env-linters exempt derived declarations structurally (no per-site opt-out exists at a generated decl's source site)"

/-- Has `decl` the `@[derived]` stamp? The linter-side skip predicate. -/
def hasDerived (env : Environment) (decl : Name) : Bool :=
  derivedAttr.hasTag env decl

/-- The `addDecl`-route stamp: a command that assembles the `Declaration`
    itself (e.g. `schema_update`'s emitted instances) has no source syntax
    for the attribute to ride. -/
def stampDerived [Monad m] [MonadEnv m] [MonadError m] (decl : Name) : m Unit :=
  TagAttribute.setTag derivedAttr decl

/-! ## `register_guestlang_linter` — the env-linter registration one-liner

Every env-linter carried the same three-part ritual: a `register_option`
block (wrapped in a packageNamespace nolint — now structural: the skip
exempts `linter.`-rooted option decls, whose root is Lean's own option-
registration namespace, not drift), the `addEnvLinterOption` snapshot
hookup, and the `@[builtin_env_linter]` mount def. One command now:

    register_guestlang_linter linter.guestlang.axiomAllowlist
      LintKit.axiomAllowlistLinter "flag declarations …"

with the optional `default_false` token for the census linters (the two
default-OFF options keep their exact defaults — the gates call them by
name). The linter def (`<name>` — a `LintKit`-prefixed `EnvLinter` value,
its test defined above the call) keeps its exact name; the mount lands at
`<name>.reg`, the name the stock `lake lint` path knows. -/

syntax (name := LintKit.registerGuestlangLinter)
  "register_guestlang_linter " ident ident (&" default_false")? str : command

open Lean.Elab.Command in
@[command_elab LintKit.registerGuestlangLinter]
meta def elabRegisterGuestlangLinter : Lean.Elab.Command.CommandElab := fun stx => do
  let defaultFalse := !stx[3].isNone
  let opt := stx[1].getId
  let linter := stx[2].getId
  let descr := stx[4].isStrLit?.getD ""
  -- (1) the option (exact name + default preserved), (2) the per-decl
  -- snapshot hookup, (3) the stock-`lake lint` mount at `<name>.reg`.
  Lean.Elab.Command.elabCommand (← `(register_option $(mkIdent opt) : Bool := {
    defValue := $(quote (!defaultFalse))
    descr := $(quote descr)
  }))
  Lean.Elab.Command.elabCommand (← `(initialize Lean.Linter.addEnvLinterOption $(mkIdent opt)))
  Lean.Elab.Command.elabCommand (← `(@[builtin_env_linter $(mkIdent opt)]
    meta def $(mkIdent (linter.str "reg")) : Lean.Linter.EnvLinter.EnvLinter :=
      $(mkIdent linter)))

/-- Skip declarations no linter should ever look at: private names, internal
names, macro expansions, and compiler/relator-generated auxiliaries
(`proof_*`, `match_*`, `unsafe_*`, `grind_*`, recursor/ctor helpers — see
`Lean.isAutoDeclOrPrivate_Internal`), plus equation-lemma-shaped names
(`foo.eq_1`, `foo.eq_def`) whose findings would duplicate the report on
their parent definition, plus constructors and eliminators of inductive
types (kernel-generated; their names follow the inductive's — the inductive
decl itself is the report site, and aux decls added by inductive
elaboration do not reliably inherit `set_option` snapshots). -/
def skipDecl (decl : Name) : CoreM Bool := do
  if ← Lean.isAutoDeclOrPrivate_Internal decl then return true
  let env ← getEnv
  if env.isConstructor decl then return true
  match decl with
  | .str p s =>
    -- equation-lemma and unfold-lemma names: the parent def is the report site
    if s.startsWith "eq_" || s == "eq_def" then return true
    -- eliminators: `isAutoDeclOrPrivate_Internal` covers `recOn`/`casesOn`/
    -- `brecOn`/`below`/… but not plain `rec`
    if let some (.inductInfo _) := env.find? p then
      return s == "rec"
    return false
  | _ => return false

end LintKit
