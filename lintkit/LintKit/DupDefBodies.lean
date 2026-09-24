/-
LintKit.DupDefBodies — "one copy per concept" (notes/v3 doctrine §1's
dedup discipline; mined from legacy DupDefBodies + UpstreamDup, which
were two linters over one comparison shape — here ONE linter with BOTH
scopes):

(a) IN-PACKAGE: clusters of ≥2 public defs/theorems with alpha-equivalent
    bodies within one package root (the first component of the module
    name — the `pipelineRust`/`pipelineTrans` class of drift; cross-module
    copies land in sibling modules, so the cluster scope is the root).
(b) UPSTREAM (the extension against Init/core): a def whose body is
    alpha-equivalent to a constant defined in an UPSTREAM module
    (`upstreamRoots`: Init, Lean, Std, Batteries, Lake, Mathlib) — the
    zipIdx/mergeSort class: a hand copy of stock API rots on an upstream
    fix. The comparison set is the linted ENV — everything in it is in
    the linted package's importing cone by construction, so a core-only
    package can never be flagged against a mathlib def (mathlib is simply
    not in its env).

False-positive calibration (documented, mined from the legacy module):
* Binder names are STRIPPED before comparing (`Expr.eqv` is alpha-
  equivalence but `Expr.hash` keeps binder names — the strip is what
  makes the HashMap keys consistent).
* Level-param names are normalized by first-occurrence order (a def
  written `{u v}` compares equal to the compiler-renamed `{u_1 u_2}`).
* NON-TRIVIAL bodies only for the upstream scope: bodies under
  `upstreamDupMinNodes` Expr nodes are never compared (a `fun x => x`
  colliding with `id` is not a finding; a numeral body counts 9 —
  instance bloat — so the threshold sits above trivial bodies, below a
  copy worth flagging).
* `abbrev`s are excluded on BOTH sides: a transparent alias is
  body-equal BY DESIGN (role-named types and boundary markers would
  otherwise false-fire).
* The upstream scope flags OUR defs only (`defnInfo`); re-proving an
  upstream THEOREM is a different (name-searchable) sin.

Deliberate scope: exact structural equality modulo binder names. No
defeq/unification (a kernel check per pair — too slow for a lint).
Opt out per site: `@[nolint linter.guestlang.dupDefBodies "reason"]`.

Performance: the cluster scan iterates every constant of the environment,
so the module-name array is hoisted and the computed maps are cached per
root (and once for the upstream map) across the run — decls of different
roots interleave; a single-slot cache would recompute per switch.

The five questions (notes/v3/01-core.md):
- root: none — the dedup discipline's linter (one copy per concept).
- carrier grade: none — alpha-equivalence over Expr bodies, not a
presentation crossing.
- spine reading: the interpretation stage (linted env → findings).
- ladder rung: n/a (host machinery; the comparison is decided).
- gate row: the lintkit sweep over the gated roots.
-/
module

public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- Erase binder names so alpha-equivalent bodies compare (and hash)
equal. -/
-- Total (structural recursion on the Expr subterm) — noNewPartial's
-- ratchet: LintKit itself carries zero `partial def`.
def stripBinderNames : Expr → Expr
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

/-! ## The upstream comparison shape: binder names stripped + level params normalized -/

private def collectLevelPsL (l : Level) (acc : Array Name) : Array Name :=
  match l with
  | .zero => acc
  | .succ l => collectLevelPsL l acc
  | .max a b => collectLevelPsL b (collectLevelPsL a acc)
  | .imax a b => collectLevelPsL b (collectLevelPsL a acc)
  | .param n => if acc.contains n then acc else acc.push n
  | .mvar _ => acc

private def collectLevelPs (e : Expr) (acc : Array Name) : Array Name :=
  match e with
  | .bvar _ => acc
  | .fvar _ => acc
  | .sort l => collectLevelPsL l acc
  | .const _ ls => ls.foldl (fun a l => collectLevelPsL l a) acc
  | .app f a => collectLevelPs a (collectLevelPs f acc)
  | .lam _ t b _ => collectLevelPs b (collectLevelPs t acc)
  | .forallE _ t b _ => collectLevelPs b (collectLevelPs t acc)
  | .letE _ t v b _ => collectLevelPs b (collectLevelPs v (collectLevelPs t acc))
  | .lit _ => acc
  | .mdata _ e => collectLevelPs e acc
  | .proj _ _ e => collectLevelPs e acc
  | .mvar _ => acc

private def renLevelL (ren : Std.HashMap Name Level) : Level → Level
  | .succ l => .succ (renLevelL ren l)
  | .max a b => .max (renLevelL ren a) (renLevelL ren b)
  | .imax a b => .imax (renLevelL ren a) (renLevelL ren b)
  | .param n => ren.getD n (.param n)
  | l => l

private def renLevelE (ren : Std.HashMap Name Level) : Expr → Expr
  | .sort l => .sort (renLevelL ren l)
  | .const n ls => .const n (ls.map (renLevelL ren))
  | .app f a => .app (renLevelE ren f) (renLevelE ren a)
  | .lam n t b bi => .lam n (renLevelE ren t) (renLevelE ren b) bi
  | .forallE n t b bi => .forallE n (renLevelE ren t) (renLevelE ren b) bi
  | .letE n t v b nd => .letE n (renLevelE ren t) (renLevelE ren v)
      (renLevelE ren b) nd
  | .mdata d e => .mdata d (renLevelE ren e)
  | .proj s i e => .proj s i (renLevelE ren e)
  | e => e

/-- The upstream comparison shape: binder names stripped (the alpha-
equivalence) then level params renamed by first-occurrence order. -/
def upShape (e : Expr) : Expr := Id.run do
  let stripped := stripBinderNames e
  let ps := collectLevelPs stripped #[]
  let mut ren : Std.HashMap Name Level := {}
  for i in [:ps.size] do
    ren := ren.insert ps[i]! (.param (s!"u_{i}").toName)
  return renLevelE ren stripped

/-- Node count of an Expr (the non-triviality metric). -/
def exprNodeCount : Expr → Nat
  | .bvar _ => 1 | .fvar _ => 1 | .mvar _ => 1
  | .sort _ => 1 | .const _ _ => 1 | .lit _ => 1
  | .app f a => exprNodeCount f + exprNodeCount a + 1
  | .lam _ t b _ => exprNodeCount t + exprNodeCount b + 1
  | .forallE _ t b _ => exprNodeCount t + exprNodeCount b + 1
  | .letE _ t v b _ => exprNodeCount t + exprNodeCount v + exprNodeCount b + 1
  | .mdata _ e => exprNodeCount e
  | .proj _ _ e => exprNodeCount e + 1

/-- Module-name roots that count as UPSTREAM (core + the std/mathlib
layers). A constant defined in a module rooted here is stock API — our
defs must not bear its body. Workspace packages are NEVER in this list:
cross-package mirrors inside the workspace are deliberate (bridged
copies stay deliberate). -/
def upstreamRoots : List Name :=
  [`Init, `Lean, `Std, `Batteries, `Lake, `Mathlib]

/-- Bodies smaller than this many Expr nodes are never compared (the
upstream scope's non-triviality filter — see the module header's
calibration note). -/
def upstreamDupMinNodes : Nat := 20

/-! ## Cached body maps (computed once per process; the env is fixed) -/

/-- Cached per-package-root duplicate clusters: package root → (decl name
→ its cluster mates, excluding itself). Only members of ≥2-clusters
appear. -/
structure DupCache where
  roots : Std.HashMap Name (NameMap (Array Name)) := {}
  deriving Inhabited

initialize dupCacheRef : IO.Ref DupCache ← IO.mkRef {}

/-- Compute the duplicate-body clusters for one package root (`root` =
first component of the module name): every public, non-skip decl with a
body (defs and theorems), grouped by stripped body, across ALL modules of
that root. -/
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

/-- Cluster mates of `decl` within its own package root (cached per
root). -/
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

/-- Cached upstream body map: upstream bodies → the upstream names
bearing them. Only NON-TRIVIAL, non-reducible, non-skip bodies with
values are inserted. -/
def computeUpstreamMap (env : Environment) :
    CoreM (Std.HashMap ExprStructEq (Array Name)) := do
  let mns := env.header.moduleNames
  let mut bodies : Std.HashMap ExprStructEq (Array Name) := {}
  for (decl, info) in env.constants.map₁.toList do
    let some idx := env.const2ModIdx[decl]? | continue
    unless upstreamRoots.contains (mns[idx]!).getRoot do continue
    if ← skipDecl decl then continue
    if ← isReducible decl then continue
    let some v := info.value? | continue
    let shape := upShape v
    if exprNodeCount shape < upstreamDupMinNodes then continue
    let key : ExprStructEq := ⟨shape⟩
    let existing := (bodies.get? key).getD #[]
    bodies := bodies.insert key (existing.push decl)
  return bodies

initialize upstreamMapRef : IO.Ref (Option (Std.HashMap ExprStructEq (Array Name))) ←
  IO.mkRef none

/-- The upstream body map, cached once per process. -/
def upstreamMap (env : Environment) : CoreM (Std.HashMap ExprStructEq (Array Name)) := do
  let cache? ← upstreamMapRef.get
  match cache? with
  | some m => return m
  | none =>
    let m ← computeUpstreamMap env
    upstreamMapRef.set m
    return m

/-! ## The linter -/

meta def dupDefBodiesTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  -- (a) in-package cluster mates
  match ← dupMates? decl with
  | some mates =>
    let some idx := env.getModuleIdxFor? decl | return none
    let mod := env.header.moduleNames[idx]!
    return some m!"duplicate definition body (alpha-equivalent, modulo binder \
      names) also borne by {mates.toList} across this package root `{mod.getRoot}` \
      — deduplicate, or opt out with `@[nolint linter.guestlang.dupDefBodies \
      \"reason\"]"
  | none => pure ()
  -- (b) the upstream extension: OUR defs only, non-trivial bodies
  let some (.defnInfo di) := env.find? decl | return none
  if ← isReducible decl then return none
  let shape := upShape di.value
  if exprNodeCount shape < upstreamDupMinNodes then return none
  let map ← upstreamMap env
  match map.get? (ExprStructEq.mk shape) with
  | none => return none
  | some upstreams =>
    return some m!"duplicate definition body (alpha-equivalent, modulo binder \
      names and level-param names) also borne by UPSTREAM {upstreams.toList} — \
      use the upstream declaration instead of copying it (the zipIdx/mergeSort \
      class: the copy rots on an upstream fix), or opt out with \
      `@[nolint linter.guestlang.dupDefBodies \"reason\"]`"

meta def dupDefBodiesLinter : EnvLinter where
  test := dupDefBodiesTest
  noErrorsFound :=
    "no duplicate definition bodies within any linted package root, none against upstream"
  errorsFound := "duplicate definition bodies"

end LintKit

register_guestlang_linter linter.guestlang.dupDefBodies LintKit.dupDefBodiesLinter
  "flag clusters of ≥2 public definitions/theorems with alpha-equivalent \
    bodies sharing one package root, and package defs whose body duplicates \
    an upstream (core/Batteries) declaration — non-trivial bodies only"
