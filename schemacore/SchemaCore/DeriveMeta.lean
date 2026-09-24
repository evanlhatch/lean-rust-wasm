/- # SchemaCore.DeriveMeta — the capability mounts (the deriving handlers)

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/05-codegen.md §3 (the deriving protocol:
`@[schema] … deriving Cap1, Cap2` — a capability is a handler that
reflects the record ONCE into its description and synthesizes the thin
wrappers); notes/v3/12-construction.md §1 (`deriving WireCodec` — the
authoring surface); the GenCtx lesson (the mount stays monad-light:
pure reflection + pure syntax construction + `elabCommand` — no
elaboration-context threading, no global state beyond the handler
registry).

## The mounts

- `deriving WireCodec` — the record codec capability: describes the
  structure (the ONE reflection path, SchemaCore.Describe), emits
  `T.descr` (the reflected description, pinned literal), `T.tupleIso`
  (the ctor↔tuple `Kit.Iso`, both laws `rfl`), and
  `T.codec := (deriveCodec T.descr).transportRight ⟨tupleIso flipped⟩`
  — the wire grade whose law fields route through the GENERIC theorems
  (`deriveCodec_correct` / `deriveDec_eq` via `Kit.Codec`'s own
  transports), never a per-record proof.
- `deriving row_bridge` — the record↔row capability: emits
  `T.fields` (the registry's first-order rows, via `itemOfFields` —
  a nested product field is the SD0006 refusal), `T.fieldNames` +
  `T.fields_nodup` (the determinacy fact, decided) + `T.nameIso`
  (the name↔index iso, RowVals.lean's `fieldIndexIso` at the
  record's names), and the bridge:
  `T.toRow := toRowF T.fields ∘ T.tupleIso.to`,
  `T.ofRow := T.tupleIso.inv ∘ ofRowF T.fields`,
  `T.rowIso := T.tupleIso.trans (rowBridgeIso T.fields)` — the ONE
  `Kit.Iso` with both round-trip laws from the GENERIC theorems
  (`ofRowF_toRowF` / `toRowF_ofRowF`).

## The evidence entourage (notes/v3/16-surface.md §3 — the mounts' emissions)

Each handler ALSO emits the capability's evidence cone, COMPUTED from
the evidence kind (Kit.Derive.Evidence — the kind is a function of the
capability + the carrier's shape, so the tier cannot be mislabeled):

- `WireCodec` (carrier UNBOUNDED → kind `lgcSweep` → emissions
  `[obligationRow, sweepControls, simpSet]`): `T.codecEvidenceKind`
  (the kind row, computed), `T.codecObligation` (the Prop-indexed
  obligation, tier `= T.codecEvidenceKind.tier!` — `oracleSwept`,
  never `provedAtElab`), `T.codecDischarged` (the tier-matched
  oracle-row discharge — a `citedProof` cannot construct here),
  `T.codecSweep` (the LCG sweep, width 16, seed pinned) +
  `T.codecSabotages` (the MECHANICAL controls — truncation,
  empty-tape, and — where the description has an option — bad-tag;
  the names are `Kit.Derive.Evidence.mechanicalControls
  .unbounded`'s rows), and `@[schemaCodec] T.codec_roundtrip` (the
  simp-set's registration — the PROOF IS THE CITATION: the codec's
  own law field, zero new proof content). The law's PROOF side is
  TYPE-CARRIED (`Kit.Codec`'s law fields) — the entourage generates
  NO proof artifact for it (the census).
- `row_bridge` (the round trips CARRIED → kind `typeCarried` →
  emissions `[]` for them — the census: the entourage generates
  NOTHING where the type carries it; the determinacy fact is
  CLOSED-FINITE → kind `kernelDecide` → emissions
  `[obligationRow, simpSet]`): `T.fieldsEvidenceKind` +
  `T.fieldsObligation` (tier computed — `decidableNow`) +
  `T.fieldsDischarged` (the decided evidence), and `@[schemaCodec]`
  on `T.fields_nodup` (the simp-set's registration).

Curated failures: a structure outside the fragment refuses with the
Diag envelope (the reflection's SD-codes, rendered verbatim — got +
the valid space + the did-you-mean). Deriving is LAZY (D12): a record
gets exactly the capabilities its deriving clause names; nothing
derives otherwise.

META module (imports Lean; core-only up to `SchemaCore.Derive`).

TOOLCHAIN NOTE (06 §6's environment traps, verified): on v4.33.0 a
term quotation carrying an antiquotation elaborates MONADICALLY (the
`MonadQuotation` block does not unify with a pure `TSyntax` expected
type), so every syntax builder here is `CommandElabM`-monadic and
splices via explicit `do` binds — the same shape Kit.Lane's and
Machines.Dsl's builders use. The builders stay total and pure-reading
(no environment access beyond quotation hygiene).

The five questions: root = META — the authoring surface's mount phase;
carrier grade: none of its own (the generated entries are the core
layer's types: Descr / Kit.Iso / Kit.Codec / RowVals rows); spine
reading: the reflection stage's thin-wrapper synthesis; ladder rung:
the generated laws are CITATIONS (the generic theorems' instances);
gate row: SchemaTests' derive suite (the end-to-end pins + the
#guard_msgs refusal teeth) + the axiom report.
-/

import Lean
import Kit.Derive.Evidence
import TestingKit.Lcg
import SchemaCore.Derive
import SchemaCore.Describe

namespace SchemaCore

/-! ## The capability markers -/

/-- The `deriving WireCodec` capability marker (05 §3). No instances —
    the class's deriving handler (the bottom of this module) is the
    surface. -/
class WireCodec

/-- The `deriving row_bridge` capability marker (the `@[row_bridge]`
    shape, RowVals.lean's note). No instances — the handler is the
    surface. -/
class row_bridge

/-- THE PER-DOMAIN SIMP SET (the entourage's registration face): the
    generated laws land under `@[schemaCodec]` — one named set per
    domain, the deriving handlers' emissions registered at the mount,
    never hand-tagged at call sites. -/
register_simp_attr schemaCodec

/-! ## The description literal's syntax (the serialization face) -/

open Lean Elab Command Term

/-- A `Ty` literal's syntax (the ctor dots resolve via the expected
    type at the generated code's elaboration). -/
private partial def tySyntax : Ty → CommandElabM Term
  | .bool => `(.bool)
  | .u64 => `(.u64)
  | .i64 => `(.i64)
  | .string => `(.string)
  | .option t => do
      let inner ← tySyntax t
      `(.option $inner)
  | .list t => do
      let inner ← tySyntax t
      `(.list $inner)
  | .result a b => do
      let ia ← tySyntax a
      let ib ← tySyntax b
      `(.result $ia $ib)
  | .map k v => do
      let ik ← keySyntax k
      let iv ← tySyntax v
      `(.map $ik $iv)
  | .set k => do
      let ik ← keySyntax k
      `(.set $ik)
  | .bounded n => `(.bounded $(quote n))
where
  /-- A `KeyTy` literal's syntax. -/
  keySyntax : KeyTy → CommandElabM Term
    | .bool => `(.bool)
    | .u64 => `(.u64)
    | .i64 => `(.i64)
    | .string => `(.string)

/-- A `Descr` literal's syntax (the reflection's serialized face — the
    generated `descr` def's value). The product's field list folds to
    the right-nested `Prod.mk` chain, `()`-terminated. -/
private partial def descrSyntax : Descr → CommandElabM Term
  | .prim t => do
      let it ← tySyntax t
      `(.prim $it)
  | .option d => do
      let inner ← descrSyntax d
      `(.option $inner)
  | .list d => do
      let inner ← descrSyntax d
      `(.list $inner)
  | .product n fs => do
      let inner ← fs.foldrM
        (fun (fn : String × Descr) (acc : Term) => do
          let fd ← descrSyntax fn.2
          `(List.cons ($(quote fn.1), $fd) $acc))
        (← `(List.nil))
      `(.product $(quote n) $inner)

/-- The registry `Field` rows' literal (the generated `fields`
    abbrev's value). The field TYPES are `Ty`s already — the handler
    resolves them through `itemOfFields` (which refuses a nested
    product field, SD0006) before calling this. -/
private def fieldRowsSyntax (fs : List Field) : CommandElabM Term :=
  match fs with
  | [] => `(List.nil)
  | f :: rest => do
      let ity ← tySyntax f.ty
      let irest ← fieldRowsSyntax rest
      `(List.cons ({ name := $(quote f.name), ty := $ity }) $irest)

/-- A RAW identifier (no macro scope): it resolves against
    quote-generated binders by plain name — the generated accessor
    references (`r.ready`) must see the `fun r` binder the SAME
    generated command introduces (the hygiene mismatch: a scoped
    ident from a builder-side quotation cannot see the consumer-side
    binder; Q-verified: raw ident + raw binder resolves). -/
private def rawIdent (n : Name) : Term :=
  ⟨Syntax.ident SourceInfo.none ((n.toString).toRawSubstring) n []⟩

/-- The field projections' nested tuple (`(r.a, (r.b, ()))`),
    right-nested to the `prodTyOf` shape, `Unit`-terminated. -/
private partial def projTuple (flds : List String) : CommandElabM Term :=
  match flds with
  | [] => `(())
  | f :: rest => do
      let tail ← projTuple rest
      `(Prod.mk $(rawIdent (`r ++ Name.mkSimple f)) $tail)

/-- The j-th nested `.2`-path from the raw binder `t` (`t.2.2…`, j
    deep) — the tuple's walk spine for the ctor application (the tuple
    is right-nested, `Unit`-terminated — every field sits at a
    `.1`). -/
private partial def tupPath (j : Nat) : CommandElabM Term :=
  match j with
  | 0 => pure (rawIdent `t)
  | n + 1 => do
      let inner ← tupPath n
      `(($inner).2)

/-! ## The generated declaration builders -/

/-- `T.descr : Descr := …` — the reflected description, as an abbrev
    (the GADT-index unfolding rule: the tupleIso's type and every
    generated row type must see through it). -/
private def elabDescrDef (tn : Lean.Name) (d : Descr) : CommandElabM Unit := do
  let dv ← descrSyntax d
  elabCommand (← `(command| abbrev $(mkIdent (tn ++ `descr)) :
    $(mkIdent `SchemaCore.Descr) := $dv))

/-- `T.tupleIso : Kit.Iso T (Descr.Ty T.descr)` — the ctor↔tuple
    bijection; both laws `rfl` (structure eta + Prod eta). The `to`
    face projects per field; the `inv` face applies the (curried) ctor
    to the tuple's nested `.1` paths. -/
private def elabTupleIsoDef (env : Lean.Environment) (tn : Lean.Name)
    (d : Descr) : CommandElabM Unit := do
  let flds := match d with | .product _ fs => fs.map (·.1) | _ => []
  let ctor := Lean.getStructureCtor env tn
  let mut app : Term := mkIdent ctor.name
  for j in [:flds.length] do
    let p ← tupPath j
    app ← `($app ($p).1)
  let toFace ← projTuple flds
  let rId := rawIdent `r
  let tId := rawIdent `t
  elabCommand (← `(command|
    def $(mkIdent (tn ++ `tupleIso)) :
        $(mkIdent `Kit.Iso) $(mkIdent tn)
          ($(mkIdent `SchemaCore.Descr.Ty) $(mkIdent (tn ++ `descr))) :=
      { to := fun $rId => $toFace
        inv := fun $tId => $app
        to_inv := fun _ => rfl
        inv_to := fun _ => rfl }))

/-- `T.codec : Kit.Codec (List UInt8) T` — THE thin wrapper: the
    generic codec transported along the ctor↔tuple iso. `transportRight`
    reads the iso in the `Descr.Ty descr → T` direction — the tupleIso
    FLIPPED, field-for-field (no `Kit.Iso.symm` exists and none is
    needed: the flipped iso's law fields ARE the tupleIso's, swapped).
    The law fields route through `deriveCodec_correct` / `deriveDec_eq`
    (the generic theorems) via `Kit.Codec`'s own transports — never a
    per-record proof. -/
private def elabCodecDef (tn : Lean.Name) : CommandElabM Unit := do
  let iso := mkIdent (tn ++ `tupleIso)
  elabCommand (← `(command|
    def $(mkIdent (tn ++ `codec)) : $(mkIdent `Kit.Codec) (List UInt8) $(mkIdent tn) :=
      ($(mkIdent `SchemaCore.deriveCodec) $(mkIdent (tn ++ `descr))).transportRight
        { to := ($iso).inv
          inv := ($iso).to
          to_inv := ($iso).inv_to
          inv_to := ($iso).to_inv }))

/-- `T.toRow` / `T.ofRow` — the thin row bridge: the generic
    field-list bridge transported along the ctor↔tuple iso. -/
private def elabRowDefs (tn : Lean.Name) : CommandElabM Unit := do
  let flds := mkIdent (tn ++ `fields)
  elabCommand (← `(command|
    def $(mkIdent (tn ++ `toRow)) : $(mkIdent tn) →
        $(mkIdent `SchemaCore.RowVals) $flds :=
      $(mkIdent `SchemaCore.toRowF) $flds ∘ ($(mkIdent (tn ++ `tupleIso))).to))
  elabCommand (← `(command|
    def $(mkIdent (tn ++ `ofRow)) : $(mkIdent `SchemaCore.RowVals) $flds →
        $(mkIdent tn) :=
      ($(mkIdent (tn ++ `tupleIso))).inv ∘ $(mkIdent `SchemaCore.ofRowF) $flds))

/-- `T.rowIso : Kit.Iso T (RowVals T.fields)` — THE row bridge as a
    `Kit.Iso` value; both round-trip laws from the generic theorems
    (`toRowF_ofRowF` / `ofRowF_toRowF`) via `Kit.Iso.trans`. -/
private def elabRowIsoDef (tn : Lean.Name) : CommandElabM Unit := do
  let flds := mkIdent (tn ++ `fields)
  elabCommand (← `(command|
    def $(mkIdent (tn ++ `rowIso)) : $(mkIdent `Kit.Iso) $(mkIdent tn)
        ($(mkIdent `SchemaCore.RowVals) $flds) :=
      $(mkIdent (tn ++ `tupleIso)).trans ($(mkIdent `SchemaCore.rowBridgeIso) $flds)))

/-! ## The evidence entourage (the handlers' emissions — 16-surface §3) -/

/-- `T.codecEvidenceKind` — the kind row (computed; the census's data
    face). -/
private def elabKindDef (tn : Lean.Name) : CommandElabM Unit := do
  let kindTy : Lean.Term := mkIdent `Kit.Derive.Evidence.EvidenceKind
  let kindOf : Lean.Term := mkIdent `Kit.Derive.Evidence.evidenceKindOf
  let cap : Lean.Term := mkIdent `Kit.Derive.Evidence.DerivCap.wireCodec
  elabCommand (← `(command|
    /-- GENERATED by `deriving WireCodec` — the evidence-kind row (the
        census's data face): kind COMPUTED from the capability + the
        carrier shape (unbounded → the LCG sweep). -/
    def $(mkIdent (tn ++ `codecEvidenceKind)) : $kindTy :=
      $kindOf $cap))

/-- `T.codecObligation` + `T.codecDischarged` — the Prop-indexed
    obligation with the COMPUTED tier, and the tier-matched discharge
    (the evidence is the ORACLE ROW — the sweep; a `citedProof` cannot
    construct here, the tier mismatch is unrepresentable). -/
private def elabObligationDef (tn : Lean.Name) : CommandElabM Unit := do
  let tnT : Term := mkIdent tn
  let oblTy : Term := mkIdent `Kit.Obligation
  let disTy : Term := mkIdent `Kit.Discharged
  let codec := mkIdent (tn ++ `codec)
  let claim : Term ←
    `(∀ (v : $tnT), ($codec).decode (($codec).encode v) = some v)
  let kind : Term := mkIdent (tn ++ `codecEvidenceKind)
  elabCommand (← `(command|
    /-- GENERATED by `deriving WireCodec` — the evidence entourage's
        obligation row: THE CLAIM IS THE TYPE INDEX (the round-trip
        law), the tier COMPUTED from the evidence kind — a sweep
        reports `oracleSwept`, never `provedAtElab`. The law's PROOF
        side is type-carried (`Kit.Codec`'s law fields — the census
        generates no proof artifact for it); this row attests the
        SWEEP. -/
    def $(mkIdent (tn ++ `codecObligation)) : $oblTy String $claim :=
      { label := $(quote s!"{tn}/wire-roundtrip")
        tier := ($kind).tier!
        payload := "the LCG sweep + the mechanical controls \
          (unbounded carrier — Kit.Derive.Evidence.evidenceKindOf \
          wireCodec)"
        provenance := $(quote tn) }))
  elabCommand (← `(command|
    /-- GENERATED by `deriving WireCodec` — the obligation's discharge:
        the evidence is the ORACLE ROW (the sweep's verdict),
        tier-matched by construction (a `citedProof` cannot construct
        here — the tier mismatch is unrepresentable). -/
    def $(mkIdent (tn ++ `codecDischarged)) : $disTy String $claim :=
      { obligation := $(mkIdent (tn ++ `codecObligation))
        evidence := Kit.Evidence.oracleRow $(quote s!"{tn}.codecSweep") }))

/-- `T.codecSweep` — the LCG sweep (width 16, seed pinned; the verdict
    is DATA). -/
private def elabSweepDef (tn : Lean.Name) : CommandElabM Unit := do
  let codec := mkIdent (tn ++ `codec)
  let descr := mkIdent (tn ++ `descr)
  let tupleIso := mkIdent (tn ++ `tupleIso)
  let run : Lean.Term := mkIdent `SchemaCore.runCodecSweep
  let drawF : Lean.Term := mkIdent `SchemaCore.drawDescr
  elabCommand (← `(command|
    /-- GENERATED by `deriving WireCodec` — the LCG SWEEP (16-surface
        §3 kind 3): width 16 instances from the pinned seed, the round
        trip + the mechanical truncation discrimination per instance.
        The verdict is DATA — the tier stays `oracleSwept` — and a
        failing instance replays byte-identically from its seed. -/
    def $(mkIdent (tn ++ `codecSweep)) : SchemaCore.SweepVerdict :=
      $run $codec
        (enc := fun a => ($codec).encode a)
        (draw := fun tape =>
          ($drawF $descr tape).map fun p => (($tupleIso).inv p.1, p.2))
        16 42))

/-- `T.codecSabotages` — the MECHANICAL controls (the consumer suite's
    negatives): the rows the capability's shape demands, the names the
    entourage's data renders (never hand-invented). -/
private def elabSabotagesDef (tn : Lean.Name) (d : Descr) : CommandElabM Unit := do
  let descr := mkIdent (tn ++ `descr)
  let codec := mkIdent (tn ++ `codec)
  let tupleIso := mkIdent (tn ++ `tupleIso)
  let kitAssert : Lean.Term := mkIdent `TestingKit.assert
  let truncF : Lean.Term := mkIdent `SchemaCore.truncDiscriminates
  let drawF : Lean.Term := mkIdent `SchemaCore.drawDescr
  let emptyF : Lean.Term := mkIdent `SchemaCore.emptyRefused
  let badTagF : Lean.Term := mkIdent `SchemaCore.badTagRefused
  let mut rows : Array (TSyntax `term) := #[]
  if encNonempty d then
    rows := rows.push (← `(
      ("sabotage: the decoder accepts the truncated encoding",
        fun tape =>
          $(kitAssert) ($truncF $codec (fun a => ($codec).encode a)
              (Option.map (fun p => ($tupleIso).inv p.1) ($drawF $descr tape))
              == false)
            "control fired: the truncation probe stopped discriminating")))
    rows := rows.push (← `(
      ("sabotage: the decoder accepts the empty tape",
        fun _ =>
          $(kitAssert) ($emptyF $descr == false)
            "control fired: the decoder decoded the empty tape")))
  if hasOption d then
    rows := rows.push (← `(
      ("sabotage: the decoder accepts a bad tag",
        fun _ =>
          $(kitAssert) ($badTagF $descr == false)
            "control fired: the decoder decoded the unknown tag")))
  elabCommand (← `(command|
    /-- GENERATED by `deriving WireCodec` — the MECHANICAL controls
        (the entourage's sabotage shapes; a codec's truncation and
        empty-tape refusals are mechanical, never hand-invented). Each
        row MUST fail — the consumer's suite takes them as its
        negatives (a suite without controls does not construct, and a
        control that stops failing is the suite's `vacuous` verdict). -/
    def $(mkIdent (tn ++ `codecSabotages)) :
        List (String × (TestingKit.Tape → Except String Unit)) :=
      [$rows,*]))

/-- `@[schemaCodec] T.codec_roundtrip` — the simp-set's registration of
    the generated law. THE PROOF IS THE CITATION — the carrier's own
    law field (zero new proof content; a re-proof of a type-carried
    fact is the census finding). -/
private def elabSimpLemmaDef (tn : Lean.Name) : CommandElabM Unit := do
  let tnT : Term := mkIdent tn
  let codec := mkIdent (tn ++ `codec)
  elabCommand (← `(command|
    /-- GENERATED by `deriving WireCodec` — the round-trip law under
        the per-domain `@[schemaCodec]` simp set. The proof is the
        carrier's own law field (the citation face — the ladder's
        currency), not a re-proof. -/
    @[schemaCodec] theorem $(mkIdent (tn ++ `codec_roundtrip)) :
        ∀ (v : $tnT), ($codec).decode (($codec).encode v) = some v :=
      ($codec).decode_encode))

/-- `T.fieldsEvidenceKind` + `T.fieldsObligation` +
    `T.fieldsDischarged` — the determinacy fact's entourage (the
    closed-finite kind → the kernel decides → tier `decidableNow`).
    The ROUND TRIPS' entourage is EMPTY (the census: the `Kit.Iso` law
    fields carry both laws — nothing generates for them). -/
private def elabFieldsEntourageDef (tn : Lean.Name) : CommandElabM Unit := do
  let kindTy : Term := mkIdent `Kit.Derive.Evidence.EvidenceKind
  let kindOfShape : Term := mkIdent `Kit.Derive.Evidence.evidenceKindOfShape
  let shape : Term := mkIdent `Kit.Derive.Evidence.CarrierShape.closedFinite
  let oblTy : Term := mkIdent `Kit.Obligation
  let disTy : Term := mkIdent `Kit.Discharged
  let fieldNames := mkIdent (tn ++ `fieldNames)
  elabCommand (← `(command|
    /-- GENERATED by `deriving row_bridge` — the evidence-kind row: the
        determinacy fact lives over the CLOSED field-name list — the
        kernel decides. (The round trips' own kind is `typeCarried` —
        the census generates nothing for them.) -/
    def $(mkIdent (tn ++ `fieldsEvidenceKind)) : $kindTy :=
      $kindOfShape $shape))
  elabCommand (← `(command|
    /-- GENERATED by `deriving row_bridge` — the obligation row: the
        claim is the determinacy fact (the type index), the tier
        COMPUTED from the kind (`decidableNow`). -/
    def $(mkIdent (tn ++ `fieldsObligation)) :
        $oblTy (List String) (List.Nodup $fieldNames) :=
      { label := $(quote s!"{tn}/fields-nodup")
        tier := $(mkIdent (tn ++ `fieldsEvidenceKind)).tier!
        payload := $fieldNames
        provenance := $(quote tn) }))
  elabCommand (← `(command|
    /-- GENERATED by `deriving row_bridge` — the discharge: the DECIDED
        evidence (the tier-matched backend; a `citedProof` or an
        `oracleRow` cannot construct here). -/
    def $(mkIdent (tn ++ `fieldsDischarged)) :
        $disTy (List String) (List.Nodup $fieldNames) :=
      { obligation := $(mkIdent (tn ++ `fieldsObligation))
        evidence := Kit.Evidence.decided true }))

/-! ## The handlers -/

/-- THE `deriving WireCodec` handler: describe (the ONE reflection
    path), then the three thin wrappers. The refusal is the reflection
    's Diag, rendered verbatim (the envelope's got + valid space +
    did-you-mean). -/
private def wireCodecHandler : Lean.Elab.DerivingHandler := fun typeNames => do
  let env ← Lean.getEnv
  for tn in typeNames do
    match describe env tn with
    | .error d =>
        throwError "deriving WireCodec refused `{tn}`: {d.toString}"
    | .ok d =>
        unless env.contains (tn ++ `descr) do
          elabDescrDef tn d
          elabTupleIsoDef env tn d
        elabCodecDef tn
        -- THE EVIDENCE ENTOURAGE (16-surface §3): kind computed,
        -- obligation row + tier-matched discharge, the LCG sweep + the
        -- mechanical controls, the simp-set registration. Nothing is
        -- emitted for the law's PROOF (type-carried — the census).
        elabKindDef tn
        elabObligationDef tn
        elabSweepDef tn
        elabSabotagesDef tn d
        elabSimpLemmaDef tn
  return true

/-- THE `deriving row_bridge` handler: the rows + the determinacy fact
    + the name↔index iso + the bridge. The registry rows ride
    `itemOfFields` — the SAME flattening the registry consumes (the
    row layer never re-walks the description; a nested product field
    is the SD0006 refusal). The descr + tupleIso defs are generated
    here only if the codec capability has not already landed them. -/
private def rowBridgeHandler : Lean.Elab.DerivingHandler := fun typeNames => do
  let env ← Lean.getEnv
  for tn in typeNames do
    match describe env tn with
    | .error d =>
        throwError "deriving row_bridge refused `{tn}`: {d.toString}"
    | .ok d =>
        let fields := match d with | .product _ fs => fs | _ => []
        match itemOfFields fields with
        | .error dg =>
            throwError "deriving row_bridge refused `{tn}`: {dg.toString}"
        | .ok flds =>
            unless env.contains (tn ++ `descr) do
              elabDescrDef tn d
              elabTupleIsoDef env tn d
            elabCommand (← `(command|
              abbrev $(mkIdent (tn ++ `fields)) : List $(mkIdent `SchemaCore.Field) :=
                $(← fieldRowsSyntax flds)))
            elabCommand (← `(command|
              abbrev $(mkIdent (tn ++ `fieldNames)) : List String :=
                ($(mkIdent (tn ++ `fields))).map fun f => f.name))
            elabCommand (← `(command|
              -- GENERATED — the simp-set registration (the entourage's
              -- simpSet emission): the decided law under the per-domain
              -- `@[schemaCodec]` set.
              @[schemaCodec] theorem $(mkIdent (tn ++ `fields_nodup)) :
                  List.Nodup ($(mkIdent (tn ++ `fieldNames))) := by decide))
            -- THE EVIDENCE ENTOURAGE: the determinacy fact's obligation
            -- (kind computed: closed-finite → the kernel decides) + the
            -- simp-set registration. The ROUND TRIPS generate NOTHING
            -- (type-carried by the rowIso's law fields — the census).
            elabFieldsEntourageDef tn
            elabCommand (← `(command|
              def $(mkIdent (tn ++ `nameIso)) :=
                $(mkIdent `SchemaCore.fieldIndexIso) $(mkIdent (tn ++ `fields_nodup))))
            elabRowDefs tn
            elabRowIsoDef tn
  return true

-- `initialize` (NOT `builtin_initialize`): a non-builtin module's
-- builtin-initializer does not run from the olean import — the
-- registry's rows must land in the consumer's process (Kit.Lane's
-- initializer-chain note).
initialize
  registerDerivingHandler `SchemaCore.WireCodec wireCodecHandler
  registerDerivingHandler `SchemaCore.row_bridge rowBridgeHandler

end SchemaCore
