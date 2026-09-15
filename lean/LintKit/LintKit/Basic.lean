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
import Lean

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
