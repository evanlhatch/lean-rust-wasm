/-
# SchemaLang.Field — schema-indexed field resolution (the linen idiom)

The `outParam` two-parameter-class idiom (linen's `Ixed`/`At`, adapted
from flatland's `HasCol`): a class whose head binds the field NAME as a
pattern variable over the list's constructor, so instance search only
succeeds when the queried name matches the head field — misspelled
fields are elaboration errors, ordinals are computed, and the proof
(`resolves`) rides the instance.

THE REDUCIBILITY RULE (load-bearing): the field list must be declared
`abbrev` (or `@[reducible]` def) — instance search sees through
reducible definitions only. A plain `def` list defeats resolution.

This is the seed the `@[schema]` macro will generate per record
(schema-indexed package completes it: expressions indexed by the
resolved field type, validators, etc.).
-/

import SchemaLang.Item

namespace SchemaLang

/-- The nth field of a field list, `none` out of range. -/
def Field.get? : List Field → Nat → Option Field
  | [], _ => none
  | f :: _, 0 => some f
  | _ :: rest, n + 1 => Field.get? rest n

/--
`HasField fs name t` — evidence that field `name` sits at a known
ordinal in `fs`, with type `t`. Both `t` is an `outParam` so a lookup
like `field userFields "id" .u64` synthesizes the instance and yields
the ordinal. Search is head/tail over literal field-list abbreviations;
misses fail at elaboration time.
-/
class HasField (fs : List Field) (name : String) (t : outParam Ty) where
  /-- The ordinal of the field in `fs`. -/
  index : Nat
  /-- The resolution is CORRECT: the list's `index`-th field IS this
      (name, type) pair. (Flatland HasCol's proof-obligation-as-field
      discipline: stated in the type, checked at elaboration.) -/
  resolves : Field.get? fs index = some { name := name, ty := t }

instance (priority := high) : HasField ({ name := n, ty := t } :: fs) n t where
  index := 0
  resolves := rfl

instance [h : HasField fs n t] : HasField (f :: fs) n t where
  index := h.index + 1
  resolves := h.resolves

/-- Resolve a field name to its ordinal via instance search. -/
def fieldIndex (fs : List Field) (name : String) (t : Ty)
    [h : HasField fs name t] : Nat := h.index

end SchemaLang
