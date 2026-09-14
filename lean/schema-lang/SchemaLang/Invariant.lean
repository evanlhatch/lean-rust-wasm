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
  rung), `proved` (a theorem name is CITED at registration; resolving
  the citation is CI's job later — the name is stored, not checked),
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
    theorem name (stored — resolution is CI's job later). -/
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
/-- The safe executor: the row's field list must EQUAL the wrapper's
    (the `DecidableEq` guard carries the proof; the `▸` cast is
    kernel-level — no `lcProof`, the axiom gate's finding). A row for
    another schema executes as `false` (type mismatch = refusal). -/
def InvariantItem.checkOn {fs : List Field} (it : InvariantItem) (row : RowVals fs) : Bool :=
  if h : fs = it.inv.fields then
    validates it.inv.expr (h ▸ row)
  else false

end SchemaLang
