/-
LintKit.DupDefBodies — notes/lean-refactor-guide.md 6.3, doctrine §2:
duplicate def bodies within a package are drift waiting to happen (the
`pipelineRust`/`pipelineTrans` class of bug, guide 1.5).

Within each linted module, clusters public defs/theorems by body after
stripping binder names (so `fun n => n + 1` and `fun m => m + 1` cluster —
`Expr.eqv` is alpha-equivalence, but `Expr.hash` keeps binder names, so the
strip is what makes the HashMap keys consistent) and flags every member of a
cluster of ≥2. Opt out per site:
`@[nolint linter.guestlang.dupDefBodies "reason"]`.

Deliberate scope: exact structural equality modulo binder names. No
defeq/unification (a kernel check per pair — too slow for a lint), no
cross-module clustering (per-module is where accidental copies land).
Reducible decls (`abbrev`s) are excluded: a transparent alias is
body-equal BY DESIGN — role-named types (`FieldName`/`ExtId`) and
boundary markers (`Async.Future`) would otherwise false-fire.

The option is declared at top level (see LintKit.Basic's header note).
-/
import LintKit.Basic

open Lean Meta Linter EnvLinter

@[nolint linter.guestlang.packageNamespace "option declarations must be top-level: the builtin_env_linter registration checks `env.contains <raw option name>` at attribute time (see LintKit.Basic header)"]
register_option linter.guestlang.dupDefBodies : Bool := {
  defValue := true
  descr := "flag clusters of ≥2 public definitions/theorems in one module with \
    alpha-equivalent bodies"
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

/-- Cached per-module duplicate clusters: decl name → its cluster mates
(excluding itself). Only members of ≥2-clusters appear. -/
structure DupCache where
  module : Name := .anonymous
  mates  : NameMap (Array Name) := {}
  deriving Inhabited

initialize dupCacheRef : IO.Ref DupCache ← IO.mkRef {}

/-- Compute the duplicate-body clusters for one module: every public,
non-skip decl with a body (defs and theorems), grouped by stripped body. -/
def computeModuleDups (env : Environment) (mod : Name) : CoreM DupCache := do
  let some idx := env.header.moduleNames.findIdx? (· == mod) | return {}
  let mut bodies : Std.HashMap ExprStructEq (Array Name) := {}
  for (decl, info) in env.constants.map₁.toList do
    if env.const2ModIdx[decl]? != some idx then continue
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
  return { module := mod, mates }

/-- Cluster mates of `decl` within its own module (cached per module). -/
def dupMates? (decl : Name) : CoreM (Option (Array Name)) := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? decl | return none
  let mod := env.header.moduleNames[idx]!
  let cache ← dupCacheRef.get
  let cache ←
    if cache.module == mod then pure cache
    else do
      let c ← computeModuleDups env mod
      dupCacheRef.set c
      pure c
  return cache.mates.find? decl

meta def dupDefBodiesTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  match ← dupMates? decl with
  | none => return none
  | some mates =>
    return some m!"duplicate definition body (alpha-equivalent, modulo binder \
      names) also borne by {mates.toList} in this module — deduplicate, or opt \
      out with `@[nolint linter.guestlang.dupDefBodies \"reason\"]`"

meta def dupDefBodiesLinter : EnvLinter where
  test := dupDefBodiesTest
  noErrorsFound := "no duplicate definition bodies within any linted module"
  errorsFound := "duplicate definition bodies"

end LintKit

@[builtin_env_linter linter.guestlang.dupDefBodies]
meta def LintKit.dupDefBodiesLinter.reg : EnvLinter := LintKit.dupDefBodiesLinter
