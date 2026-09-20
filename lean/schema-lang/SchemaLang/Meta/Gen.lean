/- # SchemaLang.Meta.Gen — `derive_row_gen`: the registry-driven row
   generators

The `Meta/Derive.lean` pattern applied to the generator lane: the
command walks the registry (`schemaItemExt`/`registeredItems`) at
elaboration time and emits the row generator + the closed-field
witnesses for a registered record. The mirror cannot drift because it
is not written — renaming a field or changing its type in Demo fails
THIS module's elaboration (the emitted `abbrev` is built from the
registry's live values, did-you-mean included on a miss).

Shape-FILLED discipline (the lane's law): the row's SHAPE (fields,
order, types) is the registry's data — the emitted term fills it,
never chooses it. The per-field value generation is `genVal` (the
tensor arm fills dims, never chooses them — the same rule one level
down).

Refusal discipline (shift-left): a field OUTSIDE the codec-closed
universe (`f32`/`f64` — no closure case, no round-trip proof;
`.ty n` refs — `Value` has no constructor for them) makes the row
ungeneratable. The command THROWS (did-you-mean included for the
record itself; the field-level error names the field and the type).
Such a record's row generator is unwritable, not a runtime `none`.

Ownership: schema-lang's generator lane (the elab half; the runtime
half — `FieldsClosed`/`genRowVals` — is `SchemaLang.Gen`).
-/

module

public import Lean
public import SchemaLang.Meta.Derive
public import SchemaLang.Meta.Reflect
public import SchemaLang.Gen

public meta section

namespace SchemaLang.Meta

open Lean Elab Command

/-! ## The registry lookups + term builders

`registeredRecord?`/`fieldTerm` live in `SchemaLang.Meta.Derive` (the
lower module — the derive kit owns the shared builders; W2.6). -/

/-- The fields list literal (the `RowVals` index — shape carried). -/
def fieldsTerm : List Field → CommandElabM Term
  | [] => `([])
  | f :: rest => do `($(← fieldTerm f) :: $(← fieldsTerm rest))

/-- The `CodecClosed` witness term for a field's type, built
    STRUCTURALLY from the registry's `Ty` value. NOT a `Ty` quote —
    the Ty reifiers are `Meta.tyTerm` (Term level, the shared walker)
    and `ToExpr Ty` (Expr level); the target here is the
    `CodecClosed` family, whose shape DIFFERS (the map key and tensor
    dims are DROPPED — no witness needed; `f32`/`f64`/`.ty` have no
    constructor: the refusal IS the error, see the module header) — so
    it cannot ride the shared quoter without changing what it builds.
    Still its own compiler-exhaustive walk: a new `Ty` ctor fails THIS
    match too. -/
def ccTerm : Ty → CommandElabM Term
  | .bool => `(CodecClosed.bool) | .u8 => `(CodecClosed.u8)
  | .u16 => `(CodecClosed.u16) | .u32 => `(CodecClosed.u32)
  | .u64 => `(CodecClosed.u64) | .i8 => `(CodecClosed.i8)
  | .i16 => `(CodecClosed.i16) | .i32 => `(CodecClosed.i32)
  | .i64 => `(CodecClosed.i64)
  | .string => `(CodecClosed.string)
  | .bytes => `(CodecClosed.bytes)
  | .option a => do `(CodecClosed.option $(← ccTerm a))
  | .result o e => do
      `(CodecClosed.result $(← ccTerm o) $(← ccTerm e))
  | .list a => do `(CodecClosed.list $(← ccTerm a))
  -- the key half needs NO witness (the key codec is complete by
  -- `decode_encodeKey_append` — `CodecClosed.map`/`set` take none)
  | .map _ v => do `(CodecClosed.map $(← ccTerm v))
  | .set _ => `(CodecClosed.set)
  | .tensor _ a => do `(CodecClosed.tensor $(← ccTerm a))
  | .future a => do `(CodecClosed.future $(← ccTerm a))
  | .stream a => do `(CodecClosed.stream $(← ccTerm a))
  | .f32 | .f64 | .ty _ =>
      throwError "derive_row_gen: the field's type is outside the codec-closed universe (no CodecClosed case, no value generator, no default)"

/-- The `FieldsClosed` witness term: `FieldsClosed.cons` per field over
    `FieldsClosed.nil` (Trace's inductive family — the same shape the
    row-codec's round-trip theorem consumes). -/
def fieldsClosedTerm : List Field → CommandElabM Term
  | [] => `(SchemaLang.FieldsClosed.nil)
  | f :: rest => do
      `(SchemaLang.FieldsClosed.cons $(← ccTerm f.ty) $(← fieldsClosedTerm rest))

/-! ## The command -/

/-- `derive_row_gen for <Record>` — define `<record>RowGen` (the
    decapitalized record name + `RowGen`, e.g. `User` ↦ `userRowGen`)
    as a `Gen (RowVals <fields>)`, the fields quoted from the registry.
    Fuel-parameterized (default 3 — the sweep's nesting budget).
    Elaboration error on an unregistered/wrong-kind record (did-you-mean
    included) or any non-closed field (named). -/
syntax (name := deriveRowGen) "derive_row_gen " " for " ident : command

@[command_elab deriveRowGen]
def deriveRowGenImpl : CommandElab := fun stx => do
  let declName := stx[2].getId
  match registeredRecord? (← getEnv) declName with
  | .error msg => throwError msg
  | .ok fields =>
    let fieldsT ← fieldsTerm fields
    let ccT ← fieldsClosedTerm fields
    -- the target: the record's own name, decapitalized, + RowGen (+
    -- the Fields abbrev carrying the shape — the consumers' handle on
    -- the row's index without a hand mirror)
    let base := (declName.toString.splitOn ".").getLast!
    let target := mkIdent (Name.mkSimple
      ((base.take 1).toString.toLower ++ base.drop 1 ++ "RowGen"))
    let fieldsTarget := mkIdent (Name.mkSimple
      ((base.take 1).toString.toLower ++ base.drop 1 ++ "RowGenFields"))
    elabCommand (← `(abbrev $fieldsTarget : List SchemaLang.Field := $fieldsT))
    elabCommand (← `(abbrev $target (fuel : Nat := 3) :
        Plausible.Gen (SchemaLang.RowVals $fieldsTarget) :=
      SchemaLang.genRowVals $fieldsTarget ($ccT) fuel))

end SchemaLang.Meta
