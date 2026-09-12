/-
LintKit.DupDefBodies — notes/lean-refactor-guide.md 6.3, doctrine §2:
duplicate def bodies within a package are drift waiting to happen (the
`pipelineRust`/`pipelineTrans` class of bug, guide 1.5).

Within each linted PACKAGE ROOT — the first component of the module name
(`Machines.Machines.Core` and `Machines.Machines.Session` both root at
`Machines`) — clusters public defs/theorems by body after stripping binder
names (so `fun n => n + 1` and `fun m => m + 1` cluster — `Expr.eqv` is
alpha-equivalence, but `Expr.hash` keeps binder names, so the strip is what
makes the HashMap keys consistent) and flags every member of a cluster of
≥2, regardless of which module of the root the members live in (cross-module
copies land in sibling modules — `pipelineRust`/`pipelineTrans` were in
separate files). Opt out per site:
`@[nolint linter.guestlang.dupDefBodies "reason"]`.

Deliberate scope: exact structural equality modulo binder names. No
defeq/unification (a kernel check per pair — too slow for a lint). Cluster
scope is the package root, NOT the whole environment: cross-PACKAGE mirrors
are deliberate, bridged copies (e.g. SchemaLang.Ty.EqAns vs Substrait's own
EqAns — different roots, never flagged). Reducible decls (`abbrev`s) are
excluded: a transparent alias is body-equal BY DESIGN — role-named types
(`FieldName`/`ExtId`) and boundary markers (`Async.Future`) would otherwise
false-fire.

Performance: the cluster scan iterates every constant of the environment
(including mathlib's), so the module-name array is hoisted and the computed
root clusters are cached per root across the run (decls of different roots
interleave; a single-slot cache would recompute per switch).

The option is declared at top level (see LintKit.Basic's header note).
-/
import LintKit.Basic

open Lean Meta Linter EnvLinter

@[nolint linter.guestlang.packageNamespace "option declarations must be top-level: the builtin_env_linter registration checks `env.contains <raw option name>` at attribute time (see LintKit.Basic header)"]
register_option linter.guestlang.dupDefBodies : Bool := {
  defValue := true
  descr := "flag clusters of ≥2 public definitions/theorems (defs, theorems) with \
    alpha-equivalent bodies sharing one package root"
}

initialize Linter.addEnvLinterOption linter.guestlang.dupDefBodies

namespace LintKit

/-- Erase binder names so alpha-equivalent bodies compare (and hash) equal. -/
partial def stripBinderNames : Expr → Expr
  | .bvar i => .bvar i
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort l => .sort l
  | .const n ls => .const n ls
  | .app f a => .app (stripBinderNames f) (stripBinderNames a)
  | .lam _ t b bi => .lam .anonymous (stripBinderNames t) (stripBinderNames b) bi
  | .forallE _ t b bi => .forallE .anonymous (stripBinderNames t) (stripBinderNames b) bi
  | .letE _ t v b nd => .letE .anonymous (stripBinderNames t) (stripBinderNames v)
      (stripBinderNames b) nd
  | .lit l => .lit l
  | .mdata d e => .mdata d (stripBinderNames e)
  | .proj s i e => .proj s i (stripBinderNames e)

/-- Cached per-package-root duplicate clusters: package root → (decl name →
its cluster mates, excluding itself). Only members of ≥2-clusters appear. -/
structure DupCache where
  roots : Std.HashMap Name (NameMap (Array Name)) := {}
  deriving Inhabited

initialize dupCacheRef : IO.Ref DupCache ← IO.mkRef {}

/-- Compute the duplicate-body clusters for one package root (`root` = first
component of the module name — the top-level namespace every module of the
package lives under): every public, non-skip decl with a body (defs and
theorems), grouped by stripped body, across ALL modules of that root. -/
def computeRootDups (env : Environment) (root : Name) : CoreM (NameMap (Array Name)) := do
  -- `env.header.moduleNames` is a def (recomputes the array per access);
  -- hoist it — the cluster scan touches it once per env constant.
  let mns := env.header.moduleNames
  let mut bodies : Std.HashMap ExprStructEq (Array Name) := {}
  for (decl, info) in env.constants.map₁.toList do
    let some idx := env.const2ModIdx[decl]? | continue
    if (mns[idx]!).getRoot != root then continue
    if ← skipDecl decl then continue
    -- abbrevs: transparent aliases, body-equality is the design (see header)
    if ← isReducible decl then continue
    let some v := info.value? | continue
    let key : ExprStructEq := ⟨stripBinderNames v⟩
    let existing := (bodies.get? key).getD #[]
    bodies := bodies.insert key (existing.push decl)
  let mut mates : NameMap (Array Name) := {}
  for (_, names) in bodies.toList do
    if names.size ≥ 2 then
      for n in names do
        mates := mates.insert n (names.erase n)
  return mates

/-- Cluster mates of `decl` within its own package root (the first component
of the decl's module name; cached per root). -/
def dupMates? (decl : Name) : CoreM (Option (Array Name)) := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? decl | return none
  let root := (env.header.moduleNames[idx]!).getRoot
  let cache ← dupCacheRef.get
  let mates ← match cache.roots.get? root with
    | some m => pure m
    | none =>
      let m ← computeRootDups env root
      dupCacheRef.modify fun c => { c with roots := c.roots.insert root m }
      pure m
  return mates.find? decl

meta def dupDefBodiesTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  match ← dupMates? decl with
  | none => return none
  | some mates =>
    let env ← getEnv
    let some idx := env.getModuleIdxFor? decl | return none
    let mod := env.header.moduleNames[idx]!
    return some m!"duplicate definition body (alpha-equivalent, modulo binder \
      names) also borne by {mates.toList} across this package root `{mod.getRoot}` \
      — deduplicate, or opt out with `@[nolint linter.guestlang.dupDefBodies \
      \"reason\"]`"

meta def dupDefBodiesLinter : EnvLinter where
  test := dupDefBodiesTest
  noErrorsFound := "no duplicate definition bodies within any linted package root"
  errorsFound := "duplicate definition bodies"

end LintKit

@[builtin_env_linter linter.guestlang.dupDefBodies]
meta def LintKit.dupDefBodiesLinter.reg : EnvLinter := LintKit.dupDefBodiesLinter
