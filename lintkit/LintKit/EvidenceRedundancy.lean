/-
LintKit.EvidenceRedundancy — the evidence-redundancy census (B6; D37;
16-surface §3's weakest-sufficient discipline: the entourage's first
question — "does the type already carry it?" — asked over the tree's
HAND-written declarations, the face the generator's computation cannot
reach).

THE NAMED HEURISTIC CLASS — a declaration whose STATEMENT is
constructor-guaranteed (the fact the construction itself carries, so
any generated/hand artifact re-proving it is waste). Two detectable
shapes:

* CLASS A — the re-proof of a carried law: a THEOREM whose ∀-stripped
  statement is the round-trip shape of a `Kit.Codec`'s `decode_encode`
  or a `Kit.Iso`'s `to_inv`/`inv_to` law field — the SAME instance
  constant on both sides — whose PROOF does not cite the law field.
  The law is a structure FIELD (the construction carries it); the
  ladder's currency is the citation (`c.decode_encode`), and a
  re-proof (rfl, simp, omega scripts) is waste, same discipline as
  dead code.
* CLASS B — the mis-tiered obligation row: a def whose type is
  `Kit.Obligation _ P` or `Kit.Discharged _ P` (a CONCRETE row — no
  parameters), whose claim `P` is closed and `Decidable`-
  SYNTHESIZABLE (the kernel decides — the entourage's `closedFinite`
  face computes kind `kernelDecide`, tier `decidableNow`), while the
  row's claimed backend is a LITERAL weaker tier — `.oracleSwept`,
  `.generatedCheck` or `.guestVerified` (an `Obligation` tier field or
  a `Discharged` evidence ctor). A sweep over a space the kernel
  decides is evidence redundancy; the weakest SUFFICIENT tier is
  `decidableNow`.

THE HONEST LIMITS (stated plainly — this is a census because they are
real):

* A claim over an UNBOUNDED space (no `Decidable` instance
  synthesizes) is invisible — correctly so: there the sweep IS the
  honest tier.
* A tier routed through a helper def (`Contract.obligation`) or the
  entourage's own computation (`kind.tier!`) is not a LITERAL —
  invisible to the value-side read; the computed route is the
  guaranteed-honest one, so only literals are read.
* A sweep artifact (a `SweepVerdict` def) does not name the boundedness
  of the space it swept — the carrier's shape is not recoverable from
  the environment; Class B catches the ROW's tier claim, not the sweep
  fn's input.
* Statement shapes beyond the three carried laws (a proof of `x.nodup`
  where x's type carries nodup — the 16 §3 example) are NOT
  structurally recoverable per-declaration (the "carries" relation is
  a fact about the TYPE's definition, not the statement's syntax);
  they land when the entourage's per-type invariants table exists.
* The GENERATOR-level waste the enforcement audit named (~40 LOC) is
  invisible here BY CONSTRUCTION — the entourage's own computation
  (`Kit.Derive.Evidence`'s emissions + the `tier!` route) prevents it
  at the source; this lint is the RESIDUAL face for hand-written
  declarations.
* THE FIRST CENSUS'S ADJUDICATED FINDING (on record): the carried-law
  fields' own declaration sites fired — the field decl IS the
  construction (false-positive class #1, fixed by the name exemption
  in the test); no weaker-than-kernel obligation row exists in the
  buildable tree (Class B's first fold was empty — the honest zero,
  not a dead heuristic: the fixture teeth prove it fires).

Census-first (09 §8's trigger discipline): default OFF, findings as
DATA, promoted to the baselined report-gate
`gates evidence-redundancy-census` (notes/evidence-redundancy-census.md)
at this wave's first adjudicated run.

  lake exe lintkit --enable=linter.guestlang.evidenceRedundancy <roots>

Opt out per site: `@[nolint linter.guestlang.evidenceRedundancy "reason"]`.

The five questions (notes/v3/01-core.md):
- root: none — the evidence-redundancy census (D37's teeth).
- carrier grade: none — host machinery.
- spine reading: interpretation (env → carried-law shapes → findings).
- ladder rung: ENFORCES the weakest-sufficient discipline (16 §3): the
  carried facts get citations, the closed spaces get the kernel.
- gate row: the baselined report-gate (the decide-first-census pattern).
-/
module

public import LintKit.Basic

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- The application's head constant + args (a shallow spine read —
    implicit/instance args ride the array verbatim). -/
def spineHead? : Expr → Option (Name × Array Expr)
  | .app f a =>
      match spineHead? f with
      | some (h, args) => some (h, args.push a)
      | none => none
  | .const n _ => some (n, #[])
  | _ => none

/-- The spine's arg at index `i`, if it is a bare constant (the
    instance slot of the carried-law shapes: for the projections
    `Codec.decode`/`Codec.encode`/`Iso.to`/`Iso.inv` — implicit
    `A B` first — the instance is arg 2). -/
def spineConstAt? (args : Array Expr) (i : Nat) : Option Expr :=
  match args[i]? with
  | some c@(.const _ _) => some c
  | _ => none

/-- The spine's arg at index `i`, defaulting to a degenerate bvar. -/
def spineArgAt (args : Array Expr) (i : Nat) : Expr :=
  args.getD i (.bvar 0)

/-- CLASS A's statement side: the ∀-stripped type is a carried law's
    round-trip shape — `c.decode (c.encode b) = some _`,
    `i.to (i.inv b) = _`, `i.inv (i.to a) = _`, the SAME instance
    constant both sides; the result is the law field's name (the
    citation face the proof must use). -/
def carriedLawShape? : Expr → Option Name
  | .forallE _ _ b _ => carriedLawShape? b
  | e =>
      match spineHead? e with
      | some (``Eq, #[_, lhs, rhs]) =>
          match spineHead? rhs with
          | some (``Option.some, _) => codecFace? lhs
          | _ => isoFace? lhs
      | _ => none
where
  codecFace? (lhs : Expr) : Option Name :=
    match spineHead? lhs with
    | some (`Kit.Codec.decode, dArgs) =>
        match spineHead? (spineArgAt dArgs 3) with
        | some (`Kit.Codec.encode, eArgs) =>
            if spineConstAt? dArgs 2 == spineConstAt? eArgs 2
            then some `Kit.Codec.decode_encode else none
        | _ => none
    | _ => none
  isoFace? (lhs : Expr) : Option Name :=
    match spineHead? lhs with
    | some (`Kit.Iso.to, tArgs) =>
        match spineHead? (spineArgAt tArgs 3) with
        | some (`Kit.Iso.inv, iArgs) =>
            if spineConstAt? tArgs 2 == spineConstAt? iArgs 2
            then some `Kit.Iso.to_inv else none
        | _ => none
    | some (`Kit.Iso.inv, iArgs) =>
        match spineHead? (spineArgAt iArgs 3) with
        | some (`Kit.Iso.to, tArgs) =>
            if spineConstAt? tArgs 2 == spineConstAt? iArgs 2
            then some `Kit.Iso.inv_to else none
        | _ => none
    | _ => none

/-- The carried-law citation faces (the proof side's quiet set). -/
def carriedLawCites : List Name :=
  [`Kit.Codec.decode_encode, `Kit.Iso.to_inv, `Kit.Iso.inv_to]

/-- The weaker-than-kernel tiers: a claimed backend BELOW
    `decidableNow` for a claim the kernel decides (16 §3's
    weakest-sufficient — the redundancy). -/
def weakTiers : List Name :=
  [`Kit.Tier.oracleSwept, `Kit.Tier.generatedCheck, `Kit.Tier.guestVerified]

/-- The weaker-than-kernel evidence shapes (the Discharged face's
    literal ctors mapping to `weakTiers` through `Evidence.tier`). -/
def weakEvidence : List Name :=
  [`Kit.Evidence.oracleRow, `Kit.Evidence.generatedCheck,
   `Kit.Evidence.guestWitness]

meta def evidenceRedundancyTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  let some ci := env.find? decl | return none
  -- THE FIRST CENSUS'S ADJUDICATION (the refinement): the carried-law
  -- FIELDS' own declaration sites (`Kit.Codec.decode_encode`,
  -- `Kit.Iso.to_inv`, `Kit.Iso.inv_to` — structure fields at exactly
  -- these names) fired in the first tree-wide fold. The field decl IS
  -- the construction — there is nothing there to re-prove. Exempted.
  if carriedLawCites.contains decl then return none
  let ty := ← instantiateMVars ci.type
  -- CLASS A: a theorem re-proving a carried law (the citation is free)
  if ci matches .thmInfo _ then
    let some law := carriedLawShape? ty | return none
    -- proof side: citing the law field is the honest face — quiet
    let some value := ci.value? (allowOpaque := true) | return none
    if (← instantiateMVars value).getUsedConstants.any (carriedLawCites.contains ·) then
      return none
    return some m!"evidence redundancy (carried law re-proof): the \
      statement is the construction's own `{law}` law field — cite it \
      (the instance projection) instead of re-proving it; a proof of a \
      construction-guaranteed fact is waste (16-surface §3, D37). If \
      the re-proof IS the point, opt out with `@[nolint \
      linter.guestlang.evidenceRedundancy \"reason\"]`"
  -- CLASS B: a concrete obligation row claiming a weaker-than-kernel
  -- tier over a closed, kernel-decidable claim
  let some claim := obligationClaim? ty | return none
  if claim.hasExprMVar || claim.hasFVar then return none
  let dec? : Option Expr ←
    try some <$> synthInstance (.app (mkConst `Decidable) claim)
    catch _ => pure none
  let some _ := dec? | return none
  -- the weaker-than-kernel claim, at the row's literal faces
  let some v := ci.value? (allowOpaque := true) | return none
  match spineHead? (← whnfR (← instantiateMVars v)) with
  | some (`Kit.Obligation.mk, args) =>
      -- fields: implicit α P, label, tier, payload, provenance — tier = 3
      match args[3]? with
      | some (Expr.const t _) =>
          if weakTiers.contains t then
            pure (some m!"the obligation's tier is `{t}` over a claim \
              the kernel decides — the weakest SUFFICIENT tier is \
              `decidableNow` (a sweep or generated check over a closed \
              space is evidence redundancy; 16-surface §3, D37)")
          else pure none
      | _ => pure none
  | some (`Kit.Discharged.mk, args) =>
      -- fields: implicit α P, obligation, evidence, tierOK — evidence = 3
      match args[3]? with
      | some ev =>
          match spineHead? (← whnfR ev) with
          | some (eCtor, _) =>
              if weakEvidence.contains eCtor then
                pure (some m!"the discharge's evidence is a `{eCtor}` \
                  row over a claim the kernel decides — the weakest \
                  SUFFICIENT evidence is `.decided true` (the kernel \
                  rung; 16-surface §3, D37)")
              else pure none
          | none => pure none
      | none => pure none
  | _ => pure none
where
  obligationClaim? (ty : Expr) : Option Expr :=
    match spineHead? ty with
    | some (`Kit.Obligation, args) => args[1]?
    | some (`Kit.Discharged, args) => args[1]?
    | _ => none

meta def evidenceRedundancyLinter : EnvLinter where
  test := evidenceRedundancyTest
  noErrorsFound := "every carried law is cited and every decidable claim's row is kernel-tiered"
  errorsFound := "evidence redundancy: re-proofs of carried laws, weaker-than-kernel obligation rows"

end LintKit

-- the census linter: registered default-OFF via the `default_false` token
-- (LintKit.Basic — the one-liner registration).
register_guestlang_linter linter.guestlang.evidenceRedundancy
  LintKit.evidenceRedundancyLinter default_false
  "flag re-proofs of carried laws (Codec.decode_encode / Iso.to_inv / \
    Iso.inv_to shapes) and obligation rows claiming a weaker-than-kernel \
    tier over a closed decidable claim (16-surface §3, D37 — census: \
    default OFF, the baselined report-gate is the teeth)"
