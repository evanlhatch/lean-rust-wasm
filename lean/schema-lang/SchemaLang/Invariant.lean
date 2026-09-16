/-
# SchemaLang.Invariant — invariants as first-class registry items

SPEC-core §5: an invariant names a RECORD and carries its predicate as
the VExpr FAMILY over that record's fields (SchemaLang.Validate's
indexed expression layer — the misspelled column fails to elaborate).
This module defines the registry ITEM; the authoring surface (the
`schema_invariant` command + the `invariantItemExt` env extension)
lives in `SchemaLang.Meta.Reflect` (one command + one extension, the
file's lock discipline), and the emission in `SchemaLang.Emit.Invariant`.

- `Tier` — the computed enforcement ladder: `boundaryCheck` (the
  executable VExpr is compiled to the emitted check fn — v1's computed
  rung), `proved` (a theorem name is CITED at registration and RESOLVED
  at registration — `checkCitation?` below, the `Dbsp.Certs`
  `#check_cert` pattern: a missing, non-theorem, sorry-tainted, or
  wrong-shape citation is an ELABORATION error),
  `oracleCovered` (a differential-oracle row covers it — wired when the
  first oracle consumer lands; a closed ctor so the ladder is total).
- `SchemaInvariant` — the existential wrapper: the field list PLUS the
  `VExpr fields .bool` value (the GADT index rides the stored fields —
  a row for another schema cannot be applied to it; the executor casts
  only after a data equality guard).
- `InvariantItem` — name, the referenced record's registry name, tier,
  the cited proof name, the wrapper, and the ELABORATED term (the
  registration's own expr as an `Expr` — the elaboration-time executor
  composes it with `validates` without a value→term requoter).

Ownership: the invariant lane (this module + Meta.Reflect's command +
Emit.Invariant). Deliberate exclusions: no negation/implication on
VExpr (Validate's closed fragment governs — extend THERE, not here);
no emission logic (Emit.Invariant owns it).
-/

import Lean
import SchemaLang.Validate

namespace SchemaLang

/-! ## The enforcement ladder -/

/-- The tier: HOW the invariant is enforced. v1 computes
    `boundaryCheck` for executable VExpr rows; `proved` rows cite a
    theorem name (RESOLVED at registration — `checkCitation?` below). -/
inductive Tier where
  | boundaryCheck
  | proved
  | oracleCovered
deriving Repr, BEq, DecidableEq, Inhabited

/-- The tier's rendering (the emitted doc comment + the test pins). -/
def Tier.render : Tier → String
  | .boundaryCheck => "boundary-check"
  | .proved => "proved"
  | .oracleCovered => "oracle-covered"

instance : ToString Tier := ⟨Tier.render⟩

/-- The v1 computation: a cited proof name lifts the row to `proved`;
    an executable VExpr alone computes `boundaryCheck`. -/
def tierOf : Option Lean.Name → Tier
  | some _ => .proved
  | none => .boundaryCheck

/-! ## The proved-tier citation resolver (the `Dbsp.Certs` wire) -/

/-- THE RESOLVER — the `Dbsp.Certs.#check_cert` pattern, applied to the
    proved tier's stored citation. The cited name must
    (1) resolve in the environment (`Environment.find?`),
    (2) BE a theorem (certs cite proofs — a def/axiom citation is
        rejected),
    (3) have a clean axiom footprint (no `sorryAx`), and
    (4) carry the expected SHAPE — `validates <the invariant's own
        stored term> <row> = true` for some row (up to defeq; the row
        is a unification variable — the citation pins the PREDICATE,
        any row witnesses it).

    `none` = resolved clean; `some d` = the diagnostic. The caller
    (Meta.Reflect's `schema_invariant` command) turns `some d` into an
    ELABORATION error — a proved-invariant registration with a
    missing/mistyped citation fails the build (the former
    stored-but-unchecked hole is closed). `fsList` is the invariant's
    field list as a `List Field` literal term (`fieldsToExpr` at the
    call site) and `exprTerm` the item's stored elaborated predicate —
    exactly the term the shape check must pin. -/
def checkCitation? (env : Lean.Environment)
    (fsList exprTerm : Lean.Expr) (pn : Lean.Name) :
    Lean.Meta.MetaM (Option String) := do
  let some ci := env.find? pn
    | return some s!"cited proof `{pn}` does not resolve"
  unless ci.isTheorem do
    return some s!"cited proof `{pn}` is not a theorem — a proved-tier citation cites a proof"
  let axs ← Lean.collectAxioms pn
  if axs.contains `sorryAx then
    return some s!"cited proof `{pn}` depends on `sorryAx`"
  -- the expected shape: the cited theorem is the predicate's verdict on
  -- some row (`validates <stored term> <row> = true`); `mkEq` builds the
  -- `Eq` application with its universe instantiated (a raw `mkConst
  -- ``Eq` is `Eq.[]` — malformed, and the defeq check fails spuriously)
  let rowMv ← Lean.Meta.mkFreshExprMVar none
  let expected ← Lean.Meta.mkEq
    (Lean.mkApp3 (Lean.mkConst ``validates) fsList exprTerm rowMv)
    (Lean.mkConst ``Bool.true)
  unless ← Lean.Meta.isDefEq ci.type expected do
    return some s!"cited proof `{pn}` has type `{ci.type}` — not the proved-invariant shape `validates <the registered predicate> <row> = true`"
  pure none

/-! ## The item -/

/-- The predicate, as the VExpr FAMILY over the referenced record's
    fields: the GADT index IS the stored field list, so the expression
    cannot outlive the schema shape it was elaborated against. -/
structure SchemaInvariant where
  fields : List Field
  expr : VExpr fields .bool

/-- The registered invariant row. `proofName` is `some` exactly on
    `proved` rows (the citation); `exprTerm` is the elaborated term the
    command captured (elaboration-time execution only — never a
    backend target). -/
structure InvariantItem where
  name : String
  schemaRef : String
  tier : Tier
  proofName : Option Lean.Name
  inv : SchemaInvariant
  exprTerm : Lean.Expr := .bvar 0

/-- The GADT's only default: the empty schema with a trivially-false
    u64 comparison (registry state needs an inhabitant; no registered
    row ever takes this shape). -/
instance : Inhabited SchemaInvariant := ⟨[], .gt (.lit 0) (.lit 0)⟩

instance : Inhabited InvariantItem :=
  ⟨{ name := "", schemaRef := "", tier := .boundaryCheck
   , proofName := none, inv := default }⟩

/-! ## Execution — the existential's eliminator -/

-- The registered predicate against a schema-aligned row: the row's
-- field list must BE the invariant's (the guard compares them as
-- data), so the cast is representation-true — same fields, same
-- order ⇒ the same `RowVals` tree. A mismatched row refuses (false)
-- rather than misreads.
/-- The safe executor: the row's field list must EQUAL the wrapper's —
    `guardCastApply` (Validate's cast kit, W3.6) at the constant family
    `fun _ => Bool`: the `DecidableEq` guard carries the proof (the `▸`
    cast is kernel-level — no `lcProof`, the axiom gate's finding),
    `validates` runs on the cast row; a row for another schema executes
    as `false` (type mismatch = refusal). -/
@[irreducible]  -- W6.13 (the audit block at `SchemaLang.Update.SomeUpdate`)
def InvariantItem.checkOn {fs : List Field} (it : InvariantItem) (row : RowVals fs) : Bool :=
  guardCastApply (G := fun _ => Bool) false (validates it.inv.expr) row

end SchemaLang
