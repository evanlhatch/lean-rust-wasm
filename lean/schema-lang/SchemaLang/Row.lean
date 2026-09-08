/-
# SchemaLang.Row — dependent records over field lists

A `Row sem fs` is a heterogeneous record indexed by the schema's field
list: the field TYPES are `Ty.toType sem` reifications, so a row
holding a `UInt64` where the schema says `.u64` is enforced by the
kernel.

Access is proof-carrying: `Row.get`/`Row.set` go through `HasField`
(the linen `outParam` idiom) — the ordinal is computed by instance
search, the `resolves` proof is discharged by the class, and a
misspelled field is an elaboration error.

THE REDUCIBILITY RULE (load-bearing): field lists must be `abbrev` for
instance search to see through them.

This is the CRA register surface: a component's state is a `Row`,
updates are copyless per-field `set`s, and well-formedness (the field
exists, the value has the declared type) is a TYPE, not a check.
-/

import SchemaLang.Ty
import SchemaLang.Field

namespace SchemaLang

/-- A heterogeneous row over the schema's field list. -/
inductive Row (sem : TySem) : List Field → Type where
  | nil : Row sem []
  | cons : {n : String} → {t : Ty} → t.toType sem → Row sem fs →
      Row sem ({name := n, ty := t} :: fs)

theorem Field.get?_succ {f : Field} {rest : List Field} {idx : Nat} :
    Field.get? (f :: rest) (idx + 1) = Field.get? rest idx := rfl

/-- Copyless per-field update by ordinal (the CRA register write). -/
def Row.setN {sem : TySem} : {fs : List Field} → Row sem fs → (idx : Nat) → (f : Field) →
    Field.get? fs idx = some f → f.ty.toType sem → Row sem fs
  | _, .cons _ rest, 0, _, h, v => by
      injection h with he; subst he; exact .cons v rest
  | _, .cons v rest, (idx + 1), f, h, nv => by
      rw [Field.get?_succ] at h
      exact .cons v (Row.setN rest idx f h nv)

/-- Copyless per-field read by ordinal. -/
def Row.getN {sem : TySem} : {fs : List Field} → Row sem fs → (idx : Nat) → (f : Field) →
    Field.get? fs idx = some f → f.ty.toType sem
  | _, .cons v _, 0, _, h => by
      injection h with he; subst he; exact v
  | _, .cons _ rest, (idx + 1), f, h => by
      rw [Field.get?_succ] at h
      exact Row.getN rest idx f h

/-- Typed field read: the ordinal comes from `HasField` instance search,
    the value type from the schema. -/
def Row.get {sem : TySem} {fs : List Field} (r : Row sem fs)
    (name : String) (t : Ty) [h : HasField fs name t] : t.toType sem :=
  Row.getN r h.index ⟨name, t⟩ h.resolves

/-- Typed field write: copyless, ordinal from `HasField`. -/
def Row.set {sem : TySem} {fs : List Field} (r : Row sem fs)
    (name : String) (t : Ty) [h : HasField fs name t] (v : t.toType sem) :
    Row sem fs :=
  Row.setN r h.index ⟨name, t⟩ h.resolves v

end SchemaLang
