/- Axiom gate: headline theorems must depend only on the core triple
   (propext / Classical.choice / Quot.sound) plus native_decide's
   disclosed trust base. The package's theorems span the Vortex dtype
   round-trip, the codec seeds, the Substrait bridge congruence, and
   the pipeline-machine acyclicity/happy-path proofs. -/
import SchemaLang
import SchemaLang.Bridge
import Demo

#print axioms SchemaLang.Vortex.PType.ofDiscriminant_toDiscriminant
#print axioms SchemaLang.Vortex.PType.engineName_inj
#print axioms SchemaLang.Vortex.PType.byteWidth_pos
#print axioms SchemaLang.Ty.eqViaAns_beq
#print axioms SchemaLang.Codec.decode_encodeBool
#print axioms SchemaLang.Codec.decode_encodeU8
#print axioms SchemaLang.Codec.decVarNat_append
#print axioms SchemaLang.Codec.decOpt_encOpt_append
#print axioms SchemaLang.Codec.decProd_encProd_append
#print axioms SchemaLang.Codec.decList_encList_append
#print axioms SchemaLang.Codec.decEnum_encEnum_append
#print axioms SchemaLang.Codec.decBytes_encBytes_append
#print axioms SchemaLang.Codec.decEnvelope_encEnvelope
#print axioms SchemaLang.Codec.decEnvelope_wrong_version
#print axioms SchemaLang.Ty.toSType?_congr
#print axioms SchemaLang.decode_encodeValue_append
#print axioms SchemaLang.TVal.toList_length
#print axioms SchemaLang.buildOne?_toList
#print axioms SchemaLang.pipeline.rank_advances
#print axioms SchemaLang.pipeline.rank_advances_tr
#print axioms SchemaLang.decode_encodeValue_append
#print axioms SchemaLang.flatIdxT_inj
#print axioms SchemaLang.TSlices.toList_get
#print axioms SchemaLang.TVal.toList_get
#print axioms SchemaLang.flatIdxT_ofList
#print axioms SchemaLang.tick.rank_advances
#print axioms SchemaLang.tick.rank_advances_tr
#print axioms SchemaLang.orderMachine.rank_advances
#print axioms SchemaLang.orderMachine.rank_advances_tr
#print axioms SchemaLang.happy_path
#print axioms SchemaLang.reject_out_of_order
#print axioms SchemaLang.reset_from_failed
#print axioms SchemaLang.widenU32U64_sound

-- The proved-tier citation wire (the `Dbsp.Certs.#check_cert` pattern
-- applied to `schema_invariant ... proved`): the resolver (a def — its
-- own footprint is part of the gate) and the demo-cited theorem the
-- registration RESOLVES at elaboration (Demo.lean's `name-min-length`).
#print axioms SchemaLang.checkCitation?
#print axioms userNameLenProved

-- The W3.5 checker↔relation bridge (`universeCheck` → `WellFormed` and
-- back). The demo discharge (`demoItems_wellFormed`) lives in
-- Tests/Main.lean — the test root is not importable from here.
#print axioms SchemaLang.universeCheck_sound
#print axioms SchemaLang.universeCheck_complete

-- W7.2 ExprLang: the interface's law fields and the two readings'
-- tie theorems on the VExpr instance.
#print axioms SchemaLang.vexprViewU64_eval
#print axioms SchemaLang.vexprFoldBool_spec
#print axioms SchemaLang.evalSpecI_vexpr
#print axioms SchemaLang.evalRawI_vexpr
#print axioms SchemaLang.validatesI_vexpr

-- W3.4/W4.3: the raw lane's ONE general-index neutrality theorem (the
-- fixed-slice `evalU_set_neutral`/`evalBNeutral` pair, collapsed) and
-- the cascade as a `Dbsp.DeltaSystem` (disjoint-commutes + the N-update
-- order-freedom via `Dbsp.applySeq_perm`).
#print axioms SchemaLang.VExpr.evalRaw_set_neutral
#print axioms SchemaLang.cascade_two_commute
#print axioms SchemaLang.cascade_disj_commutes
#print axioms SchemaLang.cascade_applySeq_perm

-- W5.1: the event-sourcing core (the generic laws the attribute cites)
#print axioms SchemaLang.EventSourced.replay_snoc
#print axioms SchemaLang.EventSourced.insertIdx_eraseIdx_eq_set
#print axioms SchemaLang.EventSourced.wDeltaChangeInversion
#print axioms SchemaLang.EventSourced.upsert_eq_set
#print axioms SchemaLang.EventSourced.upsert_eq_append
#print axioms SchemaLang.EventSourced.apply_eq_patchW
#print axioms SchemaLang.EventSourced.witnessOf_valid
#print axioms SchemaLang.EventSourced.decDelta_encDelta_append
#print axioms SchemaLang.EventSourced.decJournal_encJournal_append

-- W6.11 check-eliminates-error (SchemaLang/Error.lean): every lane's
-- sufficiency theorem, the two exact-checker iffs, the CheckedProp packs
-- (defs — their completeness proofs ride in the value), and the review's
-- outstanding Obligation pin ("add the axiom pin now").
#print axioms SchemaLang.flatIdx_eq_some_of_inB
#print axioms SchemaLang.Coords.ofList?_isSome_of_inB
#print axioms SchemaLang.Coords.ofList?_ne_none_of_inB
#print axioms SchemaLang.Coords.inB_of_ofList?_eq_some
#print axioms SchemaLang.coordsChecked
#print axioms SchemaLang.Vortex.Ty.lower_isSome_iff
#print axioms SchemaLang.Vortex.Ty.lower_ne_none_of_checks
#print axioms SchemaLang.Subschema.ofMem?_isSome_iff_forall_mem
#print axioms SchemaLang.subschemaChecked
#print axioms SchemaLang.Item.keyOf_isSome_of_fields_ne_nil
#print axioms SchemaLang.Item.changeTy_isSome_of_fields_ne_nil
#print axioms SchemaLang.Snapshot.Open.close_isOk_of_ret
#print axioms SchemaLang.CasePath.mem_map_fst
#print axioms SchemaLang.VRow.isName_eq_false_of_not_mem
#print axioms SchemaLang.CasePath.payloadOf_isSome_of_isName
#print axioms SchemaLang.universeWellFormed_iff
#print axioms SchemaLang.SchemaObligation.discharge_isSome_of_computed
