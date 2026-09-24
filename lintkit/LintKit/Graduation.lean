/-
LintKit.Graduation — the graded-carrier graduation discipline
(notes/v3/15-patterns.md #11: every Retraction/Codec whose image is
decidable should ship its toImageIso upgrade — strength left on the
table is a finding).

The finding: a declared `Kit.Retraction`/`Kit.Codec` VALUE whose image
predicate is decidable, with NO graduation call site in the tree — no
`Kit.Retraction.toImageIso` (or equivalent iso-assembly) consuming it.

The honest minimal detection (and its limits — the census exists because
this is a heuristic):

* GRADE side: the decl's type (after binders) is `Kit.Retraction A B` or
  `Kit.Codec A B` with CLOSED type args (generic carrier combinators —
  `Kit.Codec.refl`, `trans`, `prod`, … — cannot carry an instance and
  are never flagged), non-reducible, non-Tests-module.
* DECIDABLE side: the image/policy predicate must synthesize a
  `Decidable` instance. Codec: the policy FIELD is read off the value's
  `Kit.Codec.mk` application (a `fun a => …` body — a NAMED policy def
  is invisible to instance search and stays quiet); Retraction: the
  image predicate `∃ a, emb a = b` is rebuilt from the value's `emb`
  and probed (fires only where a `DecidableExists`-style instance
  exists — none is generated in the tree today, so the Retraction
  branch is currently quiet-by-construction; it is kept for the day
  the tree grows the instance).
* GRADUATION side: quiet iff the value itself mentions
  `Kit.Retraction.toImageIso` (a graduated derivative) or some OTHER
  constant's type/value mentions BOTH this decl and
  `Kit.Retraction.toImageIso` (the iso-assembly call site). Codec-side
  graduation has no kit constructor yet — a decidable-policy codec with
  no graduated consumer is a finding telling you the upgrade is free.

Default-OFF (the `default_false` token below — census mode, the
detection is fuzzy): promote to a gate after the false-positive review.

Opt out per site: `@[nolint linter.guestlang.graduation "reason"]`.

The five questions (notes/v3/01-core.md):
- root: none — the graduation census.
- carrier grade: none — host machinery reading the carriers.
- spine reading: interpretation (env → findings).
- ladder rung: n/a (it reads rungs, proves none).
- gate row: census only (default OFF).
-/
module

public import LintKit.Basic
public import LintKit.Citations

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

/-- The head grade of a carrier's type: binders stripped, then the
const-head of what remains (returns the grade name + the carrier's type
args: `Kit.Retraction A B` → (`Kit.Retraction`, #[A, B])). -/
def carrierGrade? (type : Expr) : MetaM (Option (Name × Array Expr)) := do
  let mut ty := type
  repeat
    match ty with
    | .forallE _ _ b _ => ty := b
    | _ => break
  -- direct const-head read: a graded carrier's type after the binder
  -- strip is `Kit.Retraction A B` / `Kit.Codec A B` literally (decl types
  -- are not reducible-wrapped here), so no whnf pass is needed
  let fn := ty.getAppFn
  match fn with
  | .const n _ =>
      if n == `Kit.Retraction || n == `Kit.Codec then
        return some (n, ty.getAppArgs)
      else
        return none
  | _ => return none

/-- The ctor-arg index of a structure field: ctor args are
`#[params…, fields…]` (`Kit.Codec.mk`'s 7 args = the 2 type params + the
5 fields), so the index is `numParams + fieldIdx`. -/
def structFieldCtorIdx? (env : Environment) (grade : Name) (field : Name) :
    Option Nat := do
  let fields := Lean.getStructureFields env grade
  let i ← fields.idxOf? field
  match env.find? grade with
  | some (.inductInfo ii) => some (i + ii.numParams)
  | _ => none

/-- A structure FIELD off a `<Grade>.mk`-shaped value. -/
def structFieldFromValue? (env : Environment) (grade : Name) (field : Name)
    (value : Expr) : MetaM (Option Expr) := do
  let some idx := structFieldCtorIdx? env grade field | return none
  let v ← whnfR value
  match v.getAppFn with
  | .const n _ =>
      if n == grade.append `mk then
        return v.getAppArgs[idx]?
      else
        return none
  | _ => return none

/-- Can `Decidable p` be synthesized for this predicate `p`? -/
def decidableSynth? (p : Expr) : MetaM Bool := do
  let r : Option Expr ←
    try (some <$> synthInstance (.app (mkConst ``Decidable) p))
    catch _ => pure none
  return r.isSome

/-- The image predicate of a RETRACTION value, rebuilt over fresh fvars
(`∃ a, emb a = b`), probed for decidability. The Retraction branch is
quiet-by-construction today (no `DecidableExists`-style instance in the
tree) — kept for the day the tree grows one (see the module header). -/
def retractionImageDecidable? (emb : Expr) (A B : Expr) : MetaM Bool := do
  withLocalDeclD `a A fun a => do
  withLocalDeclD `b B fun b => do
    let embA := emb.instantiate1 a
    let eqE ← mkEq embA b
    let pred := .lam `a A eqE .default
    let ex := mkAppN (mkConst ``Exists [Level.one]) #[A, pred]
    decidableSynth? ex

/-- Is `decl` already graduated: its value mentions `toImageIso`, or
some other constant's type/value mentions BOTH `decl` and
`Kit.Retraction.toImageIso` (the iso-assembly call site). -/
def graduatedViaToImageIso? (env : Environment)
    (census : NameMap (Array Name)) (decl : Name) : Bool :=
  let upgrade := `Kit.Retraction.toImageIso
  match env.find? decl with
  | some info =>
      let own := info.type.getUsedConstants ++
        (info.value? (allowOpaque := true) |>.map (·.getUsedConstants) |>.getD #[])
      if own.contains upgrade then true
      else ((census.find? decl).getD #[]).any fun c =>
        (declRefs env c).contains upgrade
  | none => false

meta def graduationTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  let some (.defnInfo di) := env.find? decl | return none
  if ← isReducible decl then return none
  let some idx := env.getModuleIdxFor? decl | return none
  let mod := env.header.moduleNames[idx]!
  if isTestModule mod then return none
  let some (grade, tyArgs) ← carrierGrade? di.type | return none
  -- generic carrier combinators (open type args) cannot carry an instance
  if tyArgs.any fun e => e.hasFVar || e.hasMVar then return none
  -- already graduated?
  let census ← citationCensus env
  if graduatedViaToImageIso? env census decl then return none
  -- decidability gate: the image/policy predicate
  let some A := tyArgs[0]? | return none
  let some B := tyArgs[1]? | return none
  let imageDecidable : Bool ←
    if grade == `Kit.Codec then
      match ← structFieldFromValue? env grade `policy di.value with
      | none => return none  -- policy not readable: honest skip (census)
      | some (.lam _ _ body _) =>
          withLocalDeclD `a A fun a => decidableSynth? (body.instantiate1 a)
      | some pol =>
          withLocalDeclD `a A fun a => decidableSynth? (.app pol a)
    else
      match ← structFieldFromValue? env grade `emb di.value with
      | none => return none
      | some emb => retractionImageDecidable? emb A B
  unless imageDecidable do return none
  return some m!"strength left on the table: `{decl}` is a \
    {if grade == `Kit.Codec then "codec with a decidable accepted-byte policy"
      else "retraction with a decidable image"} but nothing in the tree \
    assembles its image iso — the `toImageIso`-style upgrade is free here \
    (15-patterns #11: every Retraction/Codec whose image is decidable \
    ships the upgrade); opt out with \
    `@[nolint linter.guestlang.graduation \"reason\"]` if the gap is honest"

meta def graduationLinter : EnvLinter where
  test := graduationTest
  noErrorsFound := "every decidable-image Retraction/Codec ships its image-iso upgrade"
  errorsFound := "decidable-image Retraction/Codec values with no graduation call site"

end LintKit

-- the census linter: registered default-OFF via the `default_false` token
-- (LintKit.Basic — the one-liner registration).
register_guestlang_linter linter.guestlang.graduation
  LintKit.graduationLinter default_false
  "flag Kit.Retraction/Kit.Codec values whose image is decidable with no \
    toImageIso call site (15-patterns #11 — census: default OFF, promote \
    to gate after the false-positive review)"
