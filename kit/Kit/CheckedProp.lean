/-
# Kit.CheckedProp — the relation + checker + bridge discipline

A proposition with an executable checker. Soundness is mandatory — a
`true` verdict is a proof. Completeness is a constructor choice with NO
default: every construction must write `.proved h` or `.missing`, so a
one-directional gate is DECLARED, never implied (15-patterns #1: the
spec never lies to fit the checker; a partial checker is honest data).

Provenance: mined from `legacy/lean/codegen-core/CodegenCore/Kit.lean`
(the `CheckedProp` section — verbatim theorem content). This IS the
v3 statement-as-instance: a checked fact is the correspondence between
the decidable shadow and the proposition (`check a = true` → `P a` via
soundness; an `Iso` when completeness holds, an honest one-ended map
when it doesn't).

Core-only.

The five questions (notes/v3/01-core.md):
- root: none — the statement-as-instance discipline (01 §4: a checked
  fact IS the correspondence between the decidable shadow and the
  proposition).
- carrier grade: the shadow→Prop map is soundness-mandatory; complete
  checkers upgrade it to an Iso, incomplete ones stay one-ended — the
  constructor choice is the declaration.
- spine reading: none — the checkers that mount it are the consumers.
- ladder rung: the bridge theorem is the small hand kind (01 §7); the
  discipline lives in the SHAPE (no default completeness).
- gate row: none yet — Kit is outside Gates.Packages' gated set;
  KitTests.Axioms pins the bridge's cone.
-/

import Kit.Correspondence

namespace Kit

/-- The completeness half of a `CheckedProp`, as DATA. `missing` is the
    loud, greppable declaration "this gate is one-directional — the
    checker may reject valid inputs". (An `Option (complete proof)`
    cannot carry a Prop without a `PLift` wrapper — the noise at every
    construction site is worse than a two-constructor inductive.) -/
inductive CheckedProp.Completeness {α : Type} (P : α → Prop) (check : α → Bool) : Type where
  | missing : Completeness P check
  | proved : (∀ a, P a → check a = true) → Completeness P check

/-- A proposition with an executable checker. Soundness is mandatory —
    a `true` verdict is a proof. Completeness is a constructor choice
    with NO default: every construction must write `.proved h` or
    `.missing`, so a one-directional gate is declared, never implied. -/
structure CheckedProp (α : Type) where
  P : α → Prop
  check : α → Bool
  sound : ∀ a, check a = true → P a
  complete? : CheckedProp.Completeness P check

namespace CheckedProp

/-- Both-ways construction: the common case. -/
def ofComplete (P : α → Prop) (check : α → Bool)
    (sound : ∀ a, check a = true → P a) (complete : ∀ a, P a → check a = true) :
    CheckedProp α :=
  ⟨P, check, sound, .proved complete⟩

/-- The verdict decides the proposition when completeness is present. -/
theorem check_iff (c : CheckedProp α) (h : ∀ a, c.P a → c.check a = true) (a : α) :
    c.check a = true ↔ c.P a :=
  ⟨c.sound a, h a⟩

/-- Loud completeness flag: `false` means soundness-only. -/
def isComplete (c : CheckedProp α) : Bool :=
  match c.complete? with
  | .missing => false
  | .proved _ => true

/-- The soundness half as a MAP: the checked universe
    `{a // check a = true}` maps into the proposition's witnesses
    `{a // P a}` (01-core §4: the statement-as-instance — the checked
    fact is the correspondence between the decidable shadow and the
    proposition). One-ended: the inverse needs completeness (`toIso`).
    An honest Retraction in the other direction does NOT exist without
    completeness — the checker may reject valid inputs, so a P-witness
    cannot always produce a check witness. -/
def toMap (c : CheckedProp α) : {a : α // c.check a = true} → {a : α // c.P a} :=
  fun x => ⟨x.1, c.sound x.1 x.2⟩

/-- The soundness map is injective (its inverse on values is the
    subtype's own projection). -/
theorem toMap_injective (c : CheckedProp α) {x x' : {a : α // c.check a = true}}
    (h : c.toMap x = c.toMap x') : x = x' := by
  refine Subtype.ext ?_
  show (c.toMap x).1 = (c.toMap x').1
  exact congrArg Subtype.val h

/-- With completeness, the checked fact upgrades to a true `Iso` —
    both round trips (the upgrade 15-patterns #11 names). -/
def toIso (c : CheckedProp α) (hc : ∀ a, c.P a → c.check a = true) :
    Iso {a : α // c.check a = true} {a : α // c.P a} where
  to x := ⟨x.1, c.sound x.1 x.2⟩
  inv x := ⟨x.1, hc x.1 x.2⟩
  to_inv _ := Subtype.ext rfl
  inv_to _ := Subtype.ext rfl
end CheckedProp

end Kit
