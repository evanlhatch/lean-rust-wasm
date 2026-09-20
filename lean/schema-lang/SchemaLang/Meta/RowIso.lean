/-
# SchemaLang.Meta.RowIso — `@[row_bridge]`: the record↔row `Iso`, generated

Every `@[schema]` record has TWO presentations — the native Lean structure
and its `RowVals fields` row form. Until now the bridges existed PER-LANE
(the event-sourcing lane's `esToRow`/`esOfRow`, Meta/EventSourced.lean;
the wire-codec lane's field walkers, Meta/WireCodec.lean), each carrying
its own round-trip proof. This module is the type-driven consolidation:
ONE generated bridge per record, and the lanes' bridges become its
aliases/projections — the doctrine's "types not conventions" applied to
the row bridge (the correspondence preference: a TRUE `Iso` over a
`PartialIso` — see the choice below).

Generated (for a record `R` with fields `fs`, in the record's namespace):

| decl | what |
|---|---|
| `R.fields` | the field-list snapshot (the registry read, `abbrev`) |
| `R.toRow` | native → `RowVals R.fields` (one `.cons` per field, boxed) |
| `R.ofRow` | `RowVals R.fields` → native (one `.cons` level per field, unboxed) |
| `R.toRow_ofRow` | LAW: `toRow (ofRow row) = row` (the row side) |
| `R.ofRow_toRow` | LAW: `ofRow (toRow r) = r` (the record side) |
| `R.rowIso` | THE ISO — `CodegenCore.Iso R (RowVals R.fields)` |

The iso's laws are the `Iso` kit's `to_inv`/`inv_to` fields, discharged by
the generated proofs — one screen each, no per-field lemma re-proving:
the record side is `cases r; rfl` (the projections), the row side is ONE
nested match on the row (each `Value` constructor's projection is total).
If a record's proof ever balloons, the FIELD-BRIDGE structure is wrong —
stop and report (the W5.4 proof-budget rule).

**Correspondence choice (the work order's honesty question).** The bridge
is a TRUE `Iso`, not a `PartialIso`: `RowVals` is a GADT indexed BY the
field list, so a wrong-shape row (wrong arity, wrong field type) does not
TYPECHECK — the domain `RowVals R.fields` already IS the well-formed rows.
A `PartialIso` would re-check what the type discipline enforces; the
byte-level decode stays partial (the codecs' `decRowVals?`), the row-level
bridge is total on the right shape.

**The WireCodec sibling verdict (no merge).** `deriving WireCodec`'s
walkers and this iso are SIBLINGS over one bridge, not candidates for a
merge: the codec walks VALUES field-wise through its own `WireCodec`
class law (the append-form composition), the iso transports the
STRUCTURE against the `RowVals` GADT. They agree because both consume
the same declaration-order field list from the same registry — the
sibling relationship is this paragraph, deliberately not shared code.

**Fragment (shared with Meta.EventSourced — ONE table).** The flat
scalars `Bool/UInt8..UInt64/Int8..Int64/String`: the types whose `Value`
constructor carries the NATIVE Lean type verbatim (boxing is
wrapper-only both directions) and which carry a total unbox projection
(`SchemaLang.EventSourced.unbox*`). Everything else is a loud
elaboration error naming the field. `Meta.EventSourced` consumes this
same table (`BridgeFrag`/`bridgeFragment`/`bridgeFragOf`) — the
event-sourcing fragment and the row-bridge fragment are one fragment by
construction, so every `@[event_sourced]` record is row-bridge-able and
`esToRow`/`esOfRow` are abbreviations of the iso's fields.

Mechanics: the `register_check_attribute` pattern (attribute ORDER
matters: `@[schema, row_bridge]` — the schema registration must land
first; composing with `@[event_sourced]` in either order is safe — the
first bridge writer wins, the second call is a no-op). Generated
theorems are kernel-checked; defs are compiled; `abbrev`s additionally
reduce at elaboration (the dot-notation and instance-search discipline).
-/

module

public import Lean
public import SchemaLang.Meta.Reflect
public import SchemaLang.Meta.Derive
public import CodegenCore.Kit
public import CodegenCore.AttrKit
public import SchemaLang.EventSourced

public meta section

namespace SchemaLang.Meta

open Lean

/-! ## The flat-scalar bridge fragment (ONE table — `Meta.EventSourced`
    consumes it too) -/

/-- One fragment entry: the schema type, its native Lean type, its
    `Ty`/`Value`/`CodecClosed` constructors, and the total unbox
    projection (the ofRow decode half; the key codec's decode half). -/
meta structure BridgeFrag where
  ty : Ty
  leanTy : Name
  tyCtor : Name
  valueCtor : Name
  ccCtor : Name
  unboxFn : Name

/-- The flat-scalar bridge fragment (the codec-closed types; the
    event-sourcing fragment IS this fragment — one table, two lanes). -/
meta def bridgeFragment : List BridgeFrag :=
  [ ⟨.bool, ``Bool, ``SchemaLang.Ty.bool, ``SchemaLang.Value.bool,
     ``SchemaLang.CodecClosed.bool, ``SchemaLang.EventSourced.unboxBool⟩
  , ⟨.u8, ``UInt8, ``SchemaLang.Ty.u8, ``SchemaLang.Value.u8,
     ``SchemaLang.CodecClosed.u8, ``SchemaLang.EventSourced.unboxU8⟩
  , ⟨.u16, ``UInt16, ``SchemaLang.Ty.u16, ``SchemaLang.Value.u16,
     ``SchemaLang.CodecClosed.u16, ``SchemaLang.EventSourced.unboxU16⟩
  , ⟨.u32, ``UInt32, ``SchemaLang.Ty.u32, ``SchemaLang.Value.u32,
     ``SchemaLang.CodecClosed.u32, ``SchemaLang.EventSourced.unboxU32⟩
  , ⟨.u64, ``UInt64, ``SchemaLang.Ty.u64, ``SchemaLang.Value.u64,
     ``SchemaLang.CodecClosed.u64, ``SchemaLang.EventSourced.unboxU64⟩
  , ⟨.i8, ``Int8, ``SchemaLang.Ty.i8, ``SchemaLang.Value.i8,
     ``SchemaLang.CodecClosed.i8, ``SchemaLang.EventSourced.unboxI8⟩
  , ⟨.i16, ``Int16, ``SchemaLang.Ty.i16, ``SchemaLang.Value.i16,
     ``SchemaLang.CodecClosed.i16, ``SchemaLang.EventSourced.unboxI16⟩
  , ⟨.i32, ``Int32, ``SchemaLang.Ty.i32, ``SchemaLang.Value.i32,
     ``SchemaLang.CodecClosed.i32, ``SchemaLang.EventSourced.unboxI32⟩
  , ⟨.i64, ``Int64, ``SchemaLang.Ty.i64, ``SchemaLang.Value.i64,
     ``SchemaLang.CodecClosed.i64, ``SchemaLang.EventSourced.unboxI64⟩
  , ⟨.string, ``String, ``SchemaLang.Ty.string, ``SchemaLang.Value.string,
     ``SchemaLang.CodecClosed.string, ``SchemaLang.EventSourced.unboxString⟩
  ]

/-- Fragment lookup (the gate calls this only after the membership
    check). -/
meta def bridgeFragOf (t : Ty) : CoreM BridgeFrag := do
  match bridgeFragment.find? (fun f => f.ty == t) with
  | some f => pure f
  | none => throwError s!"row_bridge: internal: `{repr t}` passed the fragment gate but has no entry"

/-! ## The shared generated-decl elaborator (moved from
    `Meta.EventSourced` — one copy; the shapes are its, the home is here) -/

/-- The generated-declaration kinds: theorems are kernel-checked; defs
    are compiled (the consumers evaluate them); `abbrev`s additionally
    reduce at elaboration (the dot-notation and instance-search
    discipline). -/
meta inductive GenKind where
  | thm | dfn | abbr

/-- Elaborate one generated declaration (type + value SYNTAX) and add
    it to the environment, with its provenance doc string. -/
meta def elabGen (record short : Name) (doc : String)
    (tyStx valStx : Syntax) (kind : GenKind) : CoreM Unit := do
  let name := record ++ short
  Lean.Meta.MetaM.run' <| Elab.Term.TermElabM.run' do
    let ty ← Elab.Term.elabTerm tyStx none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let val ← Elab.Term.elabTerm valStx (some ty)
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let val ← instantiateMVars val
    if ty.hasExprMVar || val.hasExprMVar then
      throwError s!"row_bridge: internal: unresolved metavariables in `{name}`"
    match kind with
    | .thm =>
      Lean.addDecl (Declaration.thmDecl {
        name, levelParams := [], type := ty, value := val })
    | .dfn | .abbr =>
      Lean.addAndCompile (Declaration.defnDecl {
        name, levelParams := [], type := ty, value := val
        , hints := match kind with | .abbr => .abbrev | _ => .opaque
        , safety := .safe })
      -- the `abbrev` hint in the declaration alone does not reach
      -- instance search (addDecl'd defs miss the reducibility attr
      -- table — the generated `R.fields` must unfold there)
      match kind with
      | .abbr => Lean.setReducibleAttribute name
      | _ => pure ()
  Lean.addDocStringCore name doc

/-! ## The term builders -/

/-- One field → its `Field` literal term. -/
meta def bridgeFieldTerm (f : Field) : CoreM Term := do
  let frag ← bridgeFragOf f.ty
  `(⟨$(quote f.name), $(mkIdent frag.tyCtor)⟩)

/-- The `.cons`-chain row literal over the record's projections,
    boxing each per its schema type. -/
meta def toRowTerm (record : Name) (r : Ident) : List Field → CoreM Term
  | [] => `(.nil)
  | f :: fs => do
      let frag ← bridgeFragOf f.ty
      let rest ← toRowTerm record r fs
      let proj := mkIdent (record ++ Name.mkSimple f.name)
      `(.cons ($(mkIdent frag.valueCtor) ($proj $r)) $rest)

/-- The nested row pattern: one `.cons` level per field, each value
    caught by its `Value` constructor, ending `.nil`. -/
meta partial def ofRowPat : List Field → Nat → CoreM Term
  | [], _ => `(.nil)
  | f :: fs, i => do
      let frag ← bridgeFragOf f.ty
      let restPat ← ofRowPat fs (i + 1)
      `(.cons ($(mkIdent frag.valueCtor) $(mkIdent (Name.mkSimple s!"v{i}"))) $restPat)

/-- The record constructor's arguments, one per field, in schema order
    — the bare pattern vars: the nested `Value`-ctor pattern already
    binds the PAYLOAD (matching `.u64 v` against `Value .u64` IS the
    unboxing — one level, no separate projection). -/
meta partial def ofRowArgs : List Field → Nat → CoreM (Array Term)
  | [], _ => pure #[]
  | _ :: fs, i => do
      let rest ← ofRowArgs fs (i + 1)
      pure (#[(← `($(mkIdent (Name.mkSimple s!"v{i}"))))] ++ rest)

/-- The nested-match row destructor: `match row with | PAT => ⟨…⟩`. -/
meta def ofRowTerm (row : Ident) (fields : List Field) : CoreM Term := do
  let pat ← ofRowPat fields 0
  let args ← ofRowArgs fields 0
  `(match $row:term with | $pat:term => ⟨$[$args],*⟩)

/-- The `to_inv` proof: the SAME nested match, each branch `rfl` — the
    record side reduces through the unbox projections (one screen by
    construction; a balloon here means the field-bridge shape is wrong). -/
meta def toRowOfRowTerm (fields : List Field) : CoreM Term := do
  let pat ← ofRowPat fields 0
  let row := mkIdent `row
  `(fun $row:ident => match $row:term with | $pat:term => rfl)

/-! ## The generator -/

/-- The provenance registry: record declaration ↦ the declarations the
    bridge minted for it. Append-only, replayed from oleans at import
    (the `CodegenCore.mkRegistryExt` semantics). -/
initialize rowBridgeExt :
    SimplePersistentEnvExtension (Name × List Name) (List (Name × List Name)) ←
  CodegenCore.mkRegistryExt `rowBridgeExt

/-- The provenance rows from an environment (the audit entry point). -/
meta def rowBridgeDecls (env : Environment) : List (Name × List Name) :=
  rowBridgeExt.getState env

/-- Has the bridge already been minted for this record? (The
    `@[row_bridge]`/`@[event_sourced]` composition: first writer wins.) -/
meta def rowBridgeDone (env : Environment) (decl : Name) : Bool :=
  (rowBridgeDecls env).any (fun (n, _) => n == decl)

/-- Generate the record↔row bridge for a `@[schema]`-registered record
    (the module header's table). Idempotent: a record that already
    carries the bridge is skipped, so `@[row_bridge]` and
    `@[event_sourced]` compose in either attribute order. -/
meta def rowBridgeAdd (decl : Name) : CoreM Unit := do
  unless rowBridgeDone (← getEnv) decl do
    let env ← getEnv
    let fields ← match registeredRecord? env decl with
      | .ok fs => pure fs
      | .error msg => throwError s!"@[row_bridge] `{decl}`: {msg}"
    for f in fields do
      unless (bridgeFragment.any (fun fr => fr.ty == f.ty)) do
        throwError s!"@[row_bridge] `{decl}`: field `{f.name}` has type \
          {repr f.ty}, outside the flat-scalar bridge fragment \
          (Bool/UInt8–UInt64/Int8–Int64/String) — the row unboxing needs \
          a one-level `Value` ctor with a total projection"
    -- the generated names must not collide with the record's own fields
    for short in [`fields, `toRow, `ofRow, `toRow_ofRow, `ofRow_toRow, `rowIso] do
      if fields.any (fun f => f.name == short.toString) then
        throwError s!"@[row_bridge] `{decl}`: generated name `{short}` \
          collides with the record's field of the same name"
    let R := mkIdent decl
    let id (short : Name) : Ident := mkIdent (decl ++ short)
    let doc (what : String) : String :=
      s!"{what} (generated by `@[row_bridge]` on `{decl}` — the record↔row Iso)"
    let gen (short : Name) (what : String)
        (tyStx valStx : Syntax) (kind : GenKind) : CoreM Unit :=
      elabGen decl short (doc what) tyStx valStx kind
    -- the field-list snapshot
    let fieldTerms ← fields.mapM bridgeFieldTerm
    gen `fields "The field-list snapshot (the registry read; `abbrev` — instance search sees through)."
      (← `(List SchemaLang.Field)) (← `([$fieldTerms.toArray,*])) .abbr
    -- the native ↔ row bridges
    let rId : Ident := ⟨← `(r)⟩
    gen `toRow "Native → row (one `.cons` per field, boxed)."
      (← `($R → SchemaLang.RowVals $(id `fields)))
      (← `(fun $rId:ident => $(← toRowTerm decl rId fields))) .abbr
    let rowId : Ident := ⟨← `(row)⟩
    gen `ofRow "Row → native (one `.cons` level per field, unboxed — TOTAL on `RowVals R.fields`: wrong-shape rows are unrepresentable, the RowVals discipline)."
      (← `(SchemaLang.RowVals $(id `fields) → $R))
      (← `(fun $rowId:ident => $(← ofRowTerm rowId fields))) .abbr
    -- the laws (the Iso kit's to_inv/inv_to fields, one screen each)
    gen `toRow_ofRow "LAW: `toRow (ofRow row) = row` — the row side (ONE nested match; each `Value` ctor's projection is total)."
      (← `(∀ (row : SchemaLang.RowVals $(id `fields)),
          $(id `toRow) ($(id `ofRow) row) = row))
      (← toRowOfRowTerm fields) .thm
    gen `ofRow_toRow "LAW: `ofRow (toRow r) = r` — the record side (`cases`; each field is a projection)."
      (← `(∀ (r : $R), $(id `ofRow) ($(id `toRow) r) = r))
      (← `(by intro r; cases r; rfl)) .thm
    -- THE ISO
    gen `rowIso "THE ROW ISO — `CodegenCore.Iso R (RowVals R.fields)`: every lane's row bridge projects its fields (the correspondence preference: a TRUE Iso — the row side is total because `RowVals` admits only well-formed rows)."
      (← `($(mkCIdent ``CodegenCore.Iso) $R (SchemaLang.RowVals $(id `fields))))
      (← `(⟨$(id `toRow), $(id `ofRow), $(id `toRow_ofRow), $(id `ofRow_toRow)⟩)) .dfn
    -- provenance: the (record, generated) row
    let generated : List Name :=
      [ `fields, `toRow, `ofRow, `toRow_ofRow, `ofRow_toRow, `rowIso
      ].map (decl ++ ·)
    modifyEnv fun env => rowBridgeExt.addEntry env (decl, generated)

/- `@[row_bridge]` — derive the record↔row bridge for a `@[schema]`
    record (the module header's table). -/
register_check_attribute `row_bridge : "derive the record↔row bridge (R.fields/R.toRow/R.ofRow + the two laws + R.rowIso : CodegenCore.Iso R (RowVals R.fields)) for a @[schema] record" := fun decl _stx _kind =>
    (rowBridgeAdd decl : CoreM Unit)

end SchemaLang.Meta

end -- public meta section
