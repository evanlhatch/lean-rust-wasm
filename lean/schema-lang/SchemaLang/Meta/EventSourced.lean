/-
# SchemaLang.Meta.EventSourced — `@[event_sourced]`: the event-log row, derived

The canon row: **an event log = `@[event_sourced]`: delta variant +
journal codec + replay + upcasters, derived**. ONE attribute on a
`@[schema]`-registered record assembles the whole lane in the record's
namespace; every law is a PROOF (never a stub — the zero-sorry rule).

    @[schema, event_sourced]
    structure Account where
      id : UInt64
      label : String
      balance : Int64

Input choice (the work order's honest-input question): the RECORD, not
an enum of events. The delta variant is determined by the record (the
Delta.lean shape — insert/update carry the full row, remove carries the
key, `Item.keyOf`'s first-field convention, REUSED not re-read); an
event enum would need a user-supplied step function and no law could be
derived. The generated `R.Event` is `EventSourced.Delta R K` — the SAME
shape the emitters lower to `delta.wit`/`delta_generated.rs`.

Generated (for a record `R` with key field `k` of native type `K`):

| decl | what |
|---|---|
| `R.esFields` | the field-list snapshot (the registry read, `abbrev`) |
| `R.esFieldsClosed` | the `FieldsClosed` witness (the codec's hypothesis) |
| `R.esKey` | the key projection (first field — `Item.keyOf`) |
| `R.esToRow` / `R.esOfRow` | native ↔ `RowVals` bridges |
| `R.esOfRow_esToRow` | the bridge round trip (proved) |
| `R.Event` | THE DELTA VARIANT — `EventSourced.Delta R K` |
| `R.replay` | replay = the I operator (fold the log to state) |
| `R.replay_snoc` | LAW: replay-after-append = one more apply (cites `EventSourced.replay_snoc`) |
| `R.esEncode` / `R.esDecode?` | the row codec (rides `encRowVals`/`decRowVals?`) |
| `R.esRow_roundtrip` | LAW: row round trip (cites `decRowVals_encRowVals_append`) |
| `R.esEncodeKey` / `R.esDecodeKey?` | the key codec |
| `R.esKey_roundtrip` | LAW: key round trip (cites `decode_encodeValue_append`) |
| `R.esEncodeEvent` / `R.esDecodeEvent?` | the event codec (tag byte in ctor order — wire-breaking to reorder) |
| `R.esEvent_roundtrip` | LAW: event round trip (cites `decDelta_encDelta_append`) |
| `R.esEncodeJournal` / `R.esDecodeJournal?` | THE JOURNAL CODEC (length-prefixed event list) |
| `R.esJournal_roundtrip` | LAW: journal round trip (cites `decList_encList_append`) |
| `R.Upcaster` / `R.upcastId` | the upcaster hook — identity by default (the migration lane's mount point; a real upcaster replaces the def) |
| `R.upcast_id` | the identity upcaster's law (the hook's default) |
| `R.esMachine` | THE `Machines.RewindableMachine` (firing = patching by the recorded delta; the rewind family applies) |
| `R.esDelta_inverse` | LAW: delta-inverse consistency — revert-after-apply = identity (the ChangeInversion row, via `RewindableMachine.revert_left`) |

The v1 FRAGMENT (loud elaboration error outside it, field named): flat
scalars `Bool/UInt8..UInt64/Int8..Int64/String` — the codec-closed types
whose `Value` constructor carries the NATIVE Lean type verbatim, so the
row boxing is wrapper-only both directions. Floats (no round-trip law),
`ByteArray` (vs `List UInt8`), option/list/result/tensor/async, and `.ty`
refs are out (the CodecValue doctrine).

Provenance: every generated decl carries a doc string naming its
origin, and the (record, generated-decl-names) pair is registered in
`eventSourcedExt` (a `SimplePersistentEnvExtension` — replayed from
oleans at import, the `mkRegistryExt` semantics).

Mechanics (the module-system era): the attribute handler runs in CoreM
at `.afterCompilation` (the `register_check_attribute` pattern), reads
the schema registry, and adds each generated declaration via
`TermElabM`-over-CoreM elaboration + `addDecl`/`addAndCompile`
(theorems kernel-checked; defs compiled so `#guard`/`decide` evaluate
them). Attribute ORDER matters: `@[schema, event_sourced]` — the schema
registration must land first (the handler reads it).
-/

module

public import Lean
public import SchemaLang.Meta.Reflect
public import SchemaLang.Meta.Derive
public import CodegenCore.AttrKit
public import SchemaLang.EventSourced
public import SchemaLang.Trace
public meta import SchemaLang.Delta

public meta section

namespace SchemaLang.Meta

open Lean

/-- The v1 fragment entry: the schema type, its native Lean type, its
    `Ty`/`Value`/`CodecClosed` constructors, and the core's unbox
    projection (the key codec's decode half). -/
meta structure EsFrag where
  ty : Ty
  leanTy : Name
  tyCtor : Name
  valueCtor : Name
  ccCtor : Name
  unboxFn : Name

/-- The v1 event-sourcing fragment: the flat scalars whose `Value`
    constructor carries the NATIVE Lean type verbatim (boxing is
    wrapper-only, both directions) and whose wire round trip is proved
    (`CodecClosed`). Everything else — floats, bytes, option/list/
    result/tensor/future/stream, `.ty` refs — is a loud elaboration
    error naming the field (the CodecValue doctrine, extended). -/
meta def esFragment : List EsFrag :=
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
meta def esFragOf (t : Ty) : CoreM EsFrag := do
  match esFragment.find? (fun f => f.ty == t) with
  | some f => pure f
  | none => throwError s!"event_sourced: internal: `{repr t}` passed the fragment gate but has no entry"

/-- The provenance registry: record declaration ↦ the declarations the
    attribute minted for it. Append-only, replayed from oleans at
    import (the `CodegenCore.mkRegistryExt` semantics). -/
initialize eventSourcedExt :
    SimplePersistentEnvExtension (Name × List Name) (List (Name × List Name)) ←
  CodegenCore.mkRegistryExt `eventSourcedExt

/-- The provenance rows from an environment (the audit entry point). -/
meta def eventSourcedDecls (env : Environment) : List (Name × List Name) :=
  eventSourcedExt.getState env

/-- The generated-declaration kinds: theorems are kernel-checked; defs
    are compiled (the journal/machine consumers evaluate them);
    `abbrev`s additionally reduce at elaboration (the dot-notation and
    instance-search discipline). -/
meta inductive EsGenKind where
  | thm | dfn | abbr

/-- Elaborate one generated declaration (type + value SYNTAX) and add
    it to the environment, with its provenance doc string. -/
meta def elabGen (record short : Name) (doc : String)
    (tyStx valStx : Syntax) (kind : EsGenKind) : CoreM Unit := do
  let name := record ++ short
  Lean.Meta.MetaM.run' <| Elab.Term.TermElabM.run' do
    let ty ← Elab.Term.elabTerm tyStx none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let val ← Elab.Term.elabTerm valStx (some ty)
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let val ← instantiateMVars val
    if ty.hasExprMVar || val.hasExprMVar then
      throwError s!"event_sourced: internal: unresolved metavariables in `{name}`"
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
      -- table — the generated `R.Event` must unfold there)
      match kind with
      | .abbr => Lean.setReducibleAttribute name
      | _ => pure ()
  Lean.addDocStringCore name doc

/-! ## The term builders (CoreM; the `Meta.Derive`/`Meta.Gen` builders
    are CommandElabM-typed and cannot ride an attribute handler — the
    shapes are theirs, the monad is the difference) -/

/-- One field → its `Field` literal term. -/
meta def esFieldTerm (f : Field) : CoreM Term := do
  let frag ← esFragOf f.ty
  `(⟨$(quote f.name), $(mkIdent frag.tyCtor)⟩)

/-- The `FieldsClosed` witness term: `cons` per field over `nil`
    (Trace's inductive family; flat fragment = no recursion). -/
meta def esFieldsClosedTerm : List Field → CoreM Term
  | [] => `(SchemaLang.FieldsClosed.nil)
  | f :: fs => do
      let frag ← esFragOf f.ty
      let rest ← esFieldsClosedTerm fs
      `(SchemaLang.FieldsClosed.cons $(mkIdent frag.ccCtor) $rest)

/-- The `.cons`-chain row literal over the record's projections,
    boxing each per its schema type. -/
meta def esToRowTerm (record : Name) (r : Ident) : List Field → CoreM Term
  | [] => `(.nil)
  | f :: fs => do
      let frag ← esFragOf f.ty
      let rest ← esToRowTerm record r fs
      let proj := mkIdent (record ++ Name.mkSimple f.name)
      `(.cons ($(mkIdent frag.valueCtor) ($proj $r)) $rest)

/-- The nested-match row destructor: one `.cons` level per field, a
    final `.nil`, the record rebuilt from the unboxed payloads. -/
meta partial def esOfRowGo : (rest : List Field) → (src : Ident) →
    (i : Nat) → (acc : Array Term) → CoreM Term
  | [], src, _, acc => `(match $src:term with | .nil => ⟨$[$acc],*⟩)
  | f :: fs, src, i, acc => do
      let frag ← esFragOf f.ty
      let v := mkIdent (Name.mkSimple s!"v{i}")
      let tail := mkIdent (Name.mkSimple s!"t{i}")
      let body ← esOfRowGo fs tail (i + 1)
        (acc.push (← `($(mkIdent frag.unboxFn) $v)))
      `(match $src:term with | .cons $v $tail => $body)

/-- The attribute handler: read the registry, gate the fragment,
    assemble the lane. -/
meta def eventSourcedAdd (decl : Name) : CoreM Unit := do
  let env ← getEnv
  let fields ← match registeredRecord? env decl with
    | .ok fs => pure fs
    | .error msg => throwError s!"@[event_sourced] `{decl}`: {msg}"
  let keyF ← match (registeredItem? env decl) >>= Item.keyOf with
    | some f => pure f
    | none => throwError s!"@[event_sourced] `{decl}`: a field-less record has \
        no key and no event semantics (the Delta.lean `Item.keyOf` convention)"
  for f in fields do
    unless (esFragment.any (fun fr => fr.ty == f.ty)) do
      throwError s!"@[event_sourced] `{decl}`: field `{f.name}` has type \
        {repr f.ty}, outside the v1 event-sourcing fragment \
        (flat scalars: Bool/UInt8–UInt64/Int8–Int64/String) — the journal \
        codec needs the codec-closed round trip and the native↔row boxing \
        needs a one-level `Value` ctor"
  let keyFrag ← esFragOf keyF.ty
  let R := mkIdent decl
  let keyTy := mkIdent keyFrag.leanTy
  let keyTyCtor := mkIdent keyFrag.tyCtor
  let keyValueCtor := mkIdent keyFrag.valueCtor
  let keyCc := mkIdent keyFrag.ccCtor
  let keyUnbox := mkIdent keyFrag.unboxFn
  let id (short : Name) : Ident := mkIdent (decl ++ short)
  let doc (what : String) : String :=
    s!"{what} (generated by `@[event_sourced]` on `{decl}` — the event-log row, W5.1)"
  let gen (short : Name) (what : String)
      (tyStx valStx : Syntax) (kind : EsGenKind) : CoreM Unit :=
    elabGen decl short (doc what) tyStx valStx kind
  -- the schema snapshot + the closure witness
  let fieldTerms ← fields.mapM esFieldTerm
  gen `esFields "The field-list snapshot (the registry read)."
    (← `(List SchemaLang.Field)) (← `([$fieldTerms.toArray,*])) .abbr
  gen `esFieldsClosed "The codec-closure witness (the row codec's hypothesis)."
    (← `(SchemaLang.FieldsClosed $(id `esFields)))
    (← esFieldsClosedTerm fields) .dfn
  -- the key projection
  gen `esKey "The key projection (the first field — `Item.keyOf`)."
    (← `($R → $keyTy)) (← `(fun r => $(mkIdent (decl ++ Name.mkSimple keyF.name)):ident r)) .abbr
  -- the native ↔ row bridges + their round trip
  let rId : Ident := ⟨← `(r)⟩
  gen `esToRow "Native → row (the journal codec's encode half rides it)."
    (← `($R → SchemaLang.RowVals $(id `esFields)))
    (← `(fun $rId:ident => $(← esToRowTerm decl rId fields))) .abbr
  let rowId : Ident := ⟨← `(row)⟩
  gen `esOfRow "Row → native (one `.cons` level per field, unboxed)."
    (← `(SchemaLang.RowVals $(id `esFields) → $R))
    (← `(fun $rowId:ident => $(← esOfRowGo fields rowId 0 #[]))) .abbr
  gen `esOfRow_esToRow "The bridge round trip."
    (← `(∀ (r : $R), $(id `esOfRow) ($(id `esToRow) r) = r))
    (← `(by intro r; cases r; rfl)) .thm
  -- (a) the delta variant + (c) replay + its law
  gen `Event "THE DELTA VARIANT (`EventSourced.Delta` — the Delta.lean shape: insert/update carry the full row, remove the key)."
    (← `(Type)) (← `(SchemaLang.EventSourced.Delta $R $keyTy)) .abbr
  gen `replay "REPLAY — the I operator: fold the event log to state."
    (← `(List $(id `Event) → List $R → List $R))
    (← `(fun log init => SchemaLang.EventSourced.replay $(id `esKey) log init)) .abbr
  gen `replay_snoc "LAW (replay-after-append): replaying `log ++ [e]` IS one more apply."
    (← `(∀ (log : List $(id `Event)) (e : $(id `Event)) (init : List $R),
        $(id `replay) (log ++ [e]) init
          = SchemaLang.EventSourced.apply $(id `esKey) e ($(id `replay) log init)))
    (← `(fun log e init =>
        SchemaLang.EventSourced.replay_snoc $(id `esKey) log e init)) .thm
  -- (b) the journal codec, built row codec → key codec → event → journal
  gen `esEncode "The row codec (encode half — rides `encRowVals`)."
    (← `($R → List UInt8))
    (← `(fun r => SchemaLang.encRowVals $(id `esFields) ($(id `esToRow) r))) .abbr
  gen `esDecode? "The row codec (decode half — rides `decRowVals?`)."
    (← `(List UInt8 → Option ($R × List UInt8)))
    (← `(fun bs => (SchemaLang.decRowVals? $(id `esFields) bs).map
        fun p => ($(id `esOfRow) p.1, p.2))) .abbr
  gen `esRow_roundtrip "LAW: the row round trip, append form (cites `decRowVals_encRowVals_append`)."
    (← `(∀ (r : $R) (rest : List UInt8),
        $(id `esDecode?) ($(id `esEncode) r ++ rest) = some (r, rest)))
    -- (the generated defs are addDecl'd — no equation lemmas; the
    -- `show` unfolds the abbrevs by defeq, the rw fires the row codec's
    -- own law, the bridge round trip closes it)
    (← `(by
          intro r rest
          show ((SchemaLang.decRowVals? $(id `esFields)
                (SchemaLang.encRowVals $(id `esFields) ($(id `esToRow) r) ++ rest)).map
                fun p => ($(id `esOfRow) p.1, p.2)) = some (r, rest)
          rw [SchemaLang.decRowVals_encRowVals_append $(id `esFieldsClosed):ident]
          simp only [Option.map_some, $(id `esOfRow_esToRow):ident])) .thm
  gen `esEncodeKey "The key codec (encode half — the scalar `Value` codec)."
    (← `($keyTy → List UInt8))
    (← `(fun k => SchemaLang.encodeValue $keyTyCtor ($keyValueCtor k))) .abbr
  gen `esDecodeKey? "The key codec (decode half — unboxed)."
    (← `(List UInt8 → Option ($keyTy × List UInt8)))
    (← `(fun bs => (SchemaLang.decVal? $keyTyCtor bs).map
        fun p => ($keyUnbox p.1, p.2))) .abbr
  gen `esKey_roundtrip "LAW: the key round trip, append form (cites `decode_encodeValue_append`)."
    (← `(∀ (k : $keyTy) (rest : List UInt8),
        $(id `esDecodeKey?) ($(id `esEncodeKey) k ++ rest) = some (k, rest)))
    (← `(by
          intro k rest
          show ((SchemaLang.decVal? $keyTyCtor
                (SchemaLang.encodeValue $keyTyCtor ($keyValueCtor k) ++ rest)).map
                fun p => ($keyUnbox p.1, p.2)) = some (k, rest)
          rw [SchemaLang.decode_encodeValue_append $keyTyCtor $keyCc]
          simp only [Option.map_some, $keyUnbox:ident])) .thm
  gen `esEncodeEvent "The event codec (tag byte in ctor order — 0 insert / 1 update / 2 remove; wire-breaking to reorder)."
    (← `($(id `Event) → List UInt8))
    (← `(SchemaLang.EventSourced.encDelta $(id `esEncode) $(id `esEncodeKey))) .abbr
  gen `esDecodeEvent? "The event decoder (unknown tags reject)."
    (← `(List UInt8 → Option ($(id `Event) × List UInt8)))
    (← `(SchemaLang.EventSourced.decDelta? $(id `esDecode?) $(id `esDecodeKey?))) .abbr
  gen `esEvent_roundtrip "LAW: the event round trip, append form (cites `decDelta_encDelta_append`)."
    (← `(∀ (e : $(id `Event)) (rest : List UInt8),
        $(id `esDecodeEvent?) ($(id `esEncodeEvent) e ++ rest) = some (e, rest)))
    (← `(fun e rest =>
        SchemaLang.EventSourced.decDelta_encDelta_append
          $(id `esEncode) $(id `esEncodeKey) $(id `esDecode?) $(id `esDecodeKey?)
          $(id `esRow_roundtrip) $(id `esKey_roundtrip) e rest)) .thm
  gen `esEncodeJournal "THE JOURNAL CODEC (encode — a length-prefixed event list)."
    (← `(List $(id `Event) → List UInt8))
    (← `(fun log => SchemaLang.EventSourced.encJournal $(id `esEncode) $(id `esEncodeKey) log)) .abbr
  gen `esDecodeJournal? "THE JOURNAL CODEC (decode)."
    (← `(List UInt8 → Option (List $(id `Event) × List UInt8)))
    (← `(fun bs => SchemaLang.EventSourced.decJournal? $(id `esDecode?) $(id `esDecodeKey?) bs)) .abbr
  gen `esJournal_roundtrip "LAW: the journal round trip, append form (cites `decList_encList_append`)."
    (← `(∀ (log : List $(id `Event)) (rest : List UInt8),
        $(id `esDecodeJournal?) ($(id `esEncodeJournal) log ++ rest) = some (log, rest)))
    (← `(fun log rest =>
        SchemaLang.EventSourced.decJournal_encJournal_append
          $(id `esEncode) $(id `esEncodeKey) $(id `esDecode?) $(id `esDecodeKey?)
          $(id `esRow_roundtrip) $(id `esKey_roundtrip) log rest)) .thm
  -- (d) the upcaster hook (identity by default — the migration lane's
  -- mount point: a real upcaster replaces `upcastId` and discharges
  -- `replay (log.map upcast)` against the old log's replay)
  gen `Upcaster "The upcaster hook (the migration row's mount point): old event payloads → new."
    (← `(Type)) (← `($(id `Event) → $(id `Event))) .abbr
  gen `upcastId "The identity upcaster (the default — no schema evolution yet)."
    ((id `Upcaster) : Syntax) (← `(fun e => e)) .abbr
  gen `upcast_id "The identity upcaster is the identity."
    (← `(∀ (e : $(id `Event)), $(id `upcastId) e = e)) (← `(fun _ => rfl)) .thm
    -- (no `replay_upcastId` law: the `map upcastId` statement rides
    -- the abbrev consts and lands in the ill-typed-at-implicit-
    -- transparency swamp that `rw` rejects — the pointwise law
    -- `upcast_id` is the hook's law; a real upcaster's replay law is
    -- the migration lane's obligation, W5.1 follow-up)
  pure ()
  -- (e) the machine + the delta-inverse law
  gen `esMachine "THE RewindableMachine: firing = patching by the recorded delta; the rewind family (rewind_runLogged, rewind_suffix — rewind-K = undo-K) applies."
    (← `(Machines.RewindableMachine))
    (← `(SchemaLang.EventSourced.esMachine $(id `esKey))) .abbr
  gen `esDelta_inverse "LAW (delta-inverse consistency — the ChangeInversion row): revert-after-apply is the identity."
    (← `(∀ (l : $(id `esMachine).Label) (s : $(id `esMachine).State)
        (h : ($(id `esMachine).event l).guard s = true),
        $(id `esMachine).revert ($(id `esMachine).deltaOf l s h)
          (($(id `esMachine).event l).action s h) = s))
    (← `(fun l s h => Machines.RewindableMachine.revert_left $(id `esMachine) l s h)) .thm
  -- provenance: the (record, generated) row
  let generated : List Name :=
    [ `esFields, `esFieldsClosed, `esKey, `esToRow, `esOfRow
    , `esOfRow_esToRow, `Event, `replay, `replay_snoc
    , `esEncode, `esDecode?, `esRow_roundtrip
    , `esEncodeKey, `esDecodeKey?, `esKey_roundtrip
    , `esEncodeEvent, `esDecodeEvent?, `esEvent_roundtrip
    , `esEncodeJournal, `esDecodeJournal?, `esJournal_roundtrip
    , `Upcaster, `upcastId, `upcast_id
    , `esMachine, `esDelta_inverse ].map (decl ++ ·)
  modifyEnv fun env => eventSourcedExt.addEntry env (decl, generated)

/- `@[event_sourced]` — derive the event-sourcing assembly for a
    `@[schema]`-registered record (the module header's table). -/
register_check_attribute `event_sourced : "derive the event-sourcing assembly (delta variant + journal codec + replay + upcaster + laws + RewindableMachine) for a @[schema] record" := fun decl _stx _kind =>
    (eventSourcedAdd decl : CoreM Unit)

end SchemaLang.Meta

end -- public meta section
