/-
LintKit.UpstreamDup — doctrine §2 "one copy per concept" (the DupDefBodies
rule) extended CROSS-BOUNDARY: a def in OUR tree whose body is
alpha-equivalent to a core/Batteries declaration is drift waiting for an
upstream rename (the zipIdx/mergeSort/replicate class — hand copies of
stock functions that rot when upstream fixes a bug or changes a shape).

Rule: flag a package def whose stripped, level-normalized body collides
with a constant defined in an UPSTREAM module (`upstreamRoots`). The
comparison set is the linted ENV — everything in it is in the linted
package's importing cone by construction (the driver `importModules` the
package's roots), so a core-only package can never be flagged against a
mathlib def: mathlib is simply not in its env.

False-positive calibration (documented):
* NON-TRIVIAL bodies only: bodies with fewer than `minBodyNodes` Expr
  nodes are never compared (a one-line `fun x => x` colliding with `id`
  is not a finding — `id`'s body counts 5 nodes).
* `abbrev`s are excluded on BOTH sides: a transparent alias is body-equal
  by design (the DupDefBodies exclusion, applied to the upstream set too).
* OUR side is defs only (`defnInfo`): re-proving an upstream THEOREM is a
  different (name-searchable) sin; the upstream side takes every kind that
  carries a body.
* Level-param names are normalized by first-occurrence order: a def
  written `{u v}` compares equal to the compiler-renamed `{u_1 u_2}`.
Opt out per site: `@[nolint linter.guestlang.upstreamDup "reason"]`.

The option is declared at top level (see LintKit.Basic's header note), via
the `register_guestlang_linter` one-liner at the bottom of this file.
-/
module

public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- Self-contained copy of the DupDefBodies alpha-equivalence strip (kept
local: UpstreamDup must not depend on another agent's in-flight file). -/
private def upStripBinders : Expr → Expr
  | .bvar i => .bvar i
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort l => .sort l
  | .const n ls => .const n ls
  | .app f a => .app (upStripBinders f) (upStripBinders a)
  | .lam _ t b bi => .lam .anonymous (upStripBinders t) (upStripBinders b) bi
  | .forallE _ t b bi => .forallE .anonymous (upStripBinders t) (upStripBinders b) bi
  | .letE _ t v b nd => .letE .anonymous (upStripBinders t) (upStripBinders v)
      (upStripBinders b) nd
  | .lit l => .lit l
  | .mdata d e => .mdata d (upStripBinders e)
  | .proj s i e => .proj s i (upStripBinders e)

/-- Module-name roots that count as UPSTREAM (core + the std/mathlib
layers). A constant defined in a module rooted here is stock API — our
defs must not bear its body. Workspace packages are NEVER in this list:
cross-package mirrors inside the workspace are the DupDefBodies scope
decision (bridged copies stay deliberate). -/
def upstreamRoots : List Name :=
  [`Init, `Lean, `Std, `Batteries, `Lake, `Mathlib]

/-- Bodies smaller than this many Expr nodes are never compared — the
non-triviality filter. CALIBRATION (observed on the 4.33 env): a one-line
`fun x => x` (`id`) counts 5; a numeral body counts 9 — `def x : Nat := 1`
elaborates to `OfNat.ofNat Nat 1 (instOfNatNat 1)` (instance bloat — a
naive ≥6 threshold false-fired on every tiny numeral def); the smallest
real copy in the fixture set (`Prod.swap`-shaped) counts 31. 20 sits
between the bloat ceiling of trivial bodies and the structure floor of a
copy worth flagging. -/
def upstreamDupMinNodes : Nat := 20

/-! ## Body shape: binder names stripped + level params normalized -/

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
  | .letE n t v b nd => .letE n (renLevelE ren t) (renLevelE ren v) (renLevelE ren b) nd
  | .mdata d e => .mdata d (renLevelE ren e)
  | .proj s i e => .proj s i (renLevelE ren e)
  | e => e

/-- The comparison shape: binder names stripped (the DupDefBodies alpha-
equivalence) then level params renamed by first-occurrence order. -/
def upShape (e : Expr) : Expr := Id.run do
  let stripped := upStripBinders e
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

/-! ## The upstream body map (computed once per process; the env is fixed) -/

initialize upstreamMapRef : IO.Ref (Option (Std.HashMap ExprStructEq (Array Name))) ←
  IO.mkRef none

/-- Upstream bodies → the upstream names bearing them. Only NON-TRIVIAL,
non-reducible, non-skip bodies with values are inserted. -/
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

def upstreamMap (env : Environment) : CoreM (Std.HashMap ExprStructEq (Array Name)) := do
  let cache? ← upstreamMapRef.get
  match cache? with
  | some m => return m
  | none =>
    let m ← computeUpstreamMap env
    upstreamMapRef.set m
    return m

/-! ## The linter -/

meta def upstreamDupTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  let some (.defnInfo di) := env.find? decl | return none
  if ← isReducible decl then return none
  let v := di.value
  let shape := upShape v
  if exprNodeCount shape < upstreamDupMinNodes then return none
  let map ← upstreamMap env
  match map.get? (ExprStructEq.mk shape) with
  | none => return none
  | some upstreams =>
    return some m!"duplicate definition body (alpha-equivalent, modulo binder \
      names and level-param names) also borne by UPSTREAM {upstreams.toList} — \
      use the upstream declaration instead of copying it (the zipIdx/mergeSort \
      class: the copy rots on an upstream fix), or opt out with \
      `@[nolint linter.guestlang.upstreamDup \"reason\"]`"

meta def upstreamDupLinter : EnvLinter where
  test := upstreamDupTest
  noErrorsFound := "no definition body duplicates an upstream (core/Batteries) declaration"
  errorsFound := "definition bodies duplicating upstream declarations"

end LintKit

register_guestlang_linter linter.guestlang.upstreamDup LintKit.upstreamDupLinter
  "flag package defs whose body is alpha-equivalent to an upstream \
    (core/Batteries) declaration — non-trivial bodies only"
