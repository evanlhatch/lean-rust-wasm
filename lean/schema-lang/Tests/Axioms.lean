/- Axiom gate: headline theorems must depend only on the core triple
   (propext / Classical.choice / Quot.sound) plus native_decide's
   disclosed trust base. The package's theorems span the Vortex dtype
   round-trip, the codec seeds, the Substrait bridge congruence, and
   the pipeline-machine acyclicity/happy-path proofs. -/
import SchemaLang
import SchemaLang.Bridge
import SchemaLang.TableInvariant
import SchemaLang.EntityMachine
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

-- W7.1 phase 2: the decidableNow backend — soundness (a `.decided
-- true` discharge IS the default-row claim) and completeness (a true
-- claim fires the backend). decide-backed, no new trust base.
#print axioms SchemaLang.SchemaObligation.discharge_decidableNow_sound
#print axioms SchemaLang.SchemaObligation.discharge_decidableNow_of_claim

-- W9.2: the guest witness checker — the soundness deliverable (artifact
-- level + judgment level), the per-step lemma, the fuel discipline
-- (zero refuses; acceptance monotone), the evalV/validates grounding
-- ties, the CheckedProp pack. Bar: the core triple only.
#print axioms SchemaLang.WitnessCheck.checkWitness_sound
#print axioms SchemaLang.WitnessCheck.checkWitnessArtifact_sound
#print axioms SchemaLang.WitnessCheck.checkSteps_sound
#print axioms SchemaLang.WitnessCheck.checkWitness_zero
#print axioms SchemaLang.WitnessCheck.checkWitness_mono
#print axioms SchemaLang.WitnessCheck.checkSteps_mono
#print axioms SchemaLang.WitnessCheck.evalWU64?_eq_evalU
#print axioms SchemaLang.WitnessCheck.evalWBool?_eq_evalB
#print axioms SchemaLang.WitnessCheck.WHolds.valid_iff_validates
#print axioms SchemaLang.WitnessCheck.WHolds.eqU_iff_evalU
#print axioms SchemaLang.WitnessCheck.WHolds.chain_validates
#print axioms SchemaLang.WitnessCheck.witnessChecked

-- W8.2: the keys lane — the checker↔relation bridge (both directions
-- + the CheckedProp pack), the obligation backend's soundness and
-- completeness, the keyOf-migration equivalence. Bar: the core triple.
#print axioms SchemaLang.keyDeclsCheck_sound
#print axioms SchemaLang.keyDeclsCheck_complete
#print axioms SchemaLang.keysChecked
#print axioms SchemaLang.keyDeclsWellFormed_iff
#print axioms SchemaLang.KeyObligation.discharge_decidableNow_sound
#print axioms SchemaLang.KeyObligation.discharge_decidableNow_of_claim
#print axioms SchemaLang.Item.keyOfWith_eq_keyOf
#print axioms SchemaLang.Item.keyOfWith_eq_keyOf_of_decl_head
#print axioms SchemaLang.FieldVal.beq_refl

-- W9.3: the fifth tier's discharge backend — the arm's equation,
-- soundness (a fired guestVerified discharge IS the WHolds denotation,
-- via checkWitnessArtifact_sound), the fires-direction. Bar: the core
-- triple only. (`discharge_isSome_of_computed` above is re-pinned by
-- its existing row — the re-stated disjunct proof rides the same name.)
#print axioms SchemaLang.SchemaObligation.discharge_guestVerified_eq
#print axioms SchemaLang.SchemaObligation.discharge_guestVerified_sound
#print axioms SchemaLang.SchemaObligation.discharge_guestVerified_of_accept

-- W8.8: table-level invariants — the existential executor's interface
-- (guarded-cast collapse), the decidableNow backend's soundness and
-- completeness over a PROVIDED materialized table, the mis-wire check.
-- Bar: the core triple.
#print axioms SchemaLang.TableInvItem.checkOn_self
#print axioms SchemaLang.TableInvItem.checkOn_of_ne
#print axioms SchemaLang.TableObligation.discharge_decidableNow_sound
#print axioms SchemaLang.TableObligation.discharge_decidableNow_of_holds
#print axioms SchemaLang.TableObligation.discharge_tier_agrees

-- W9.4: host-side witness generation — the acceptance lemmas (the
-- checker's exact cost), generation completeness (a TRUE claim
-- self-checks: WHolds → the generated certificate passes at its
-- pinned fuel), the demo registry's semantic premise, the emitter
-- law's discharge. Bar: the core triple only.
#print axioms SchemaLang.Emit.Witness.checkWitness_accept_valid
#print axioms SchemaLang.Emit.Witness.checkWitness_accept_eqU
#print axioms SchemaLang.Emit.Witness.checkSteps_accept
#print axioms SchemaLang.Emit.Witness.checkWitness_accept_chain
#print axioms SchemaLang.Emit.Witness.selfChecked?_of_WHolds
#print axioms SchemaLang.Emit.Witness.demoWitnessSpec_holds
#print axioms SchemaLang.Emit.Witness.witnessLaw_discharged

-- W9.5: the witness-gated migration checkpoint — the seam's soundness
-- wrapper, the fuel classifier's exactness lemmas (below the need =
-- always refuse; at/above it = fuel-free verdict), the gate's refusal
-- classes + the acceptance theorem (accept → the replay AND the
-- claim's denotation). Bar: the core triple only.
#print axioms SchemaLang.WitnessCheck.verifyWitness_sound
#print axioms SchemaLang.WitnessCheck.checkSteps_fuel_sufficient
#print axioms SchemaLang.WitnessCheck.checkWitness_fuel_sufficient
#print axioms SchemaLang.WitnessCheck.checkSteps_eq_false_of_fuel_lt
#print axioms SchemaLang.WitnessCheck.checkWitness_eq_false_of_fuel_lt
#print axioms SchemaLang.EventSourced.replayMigrated?_ok
#print axioms SchemaLang.EventSourced.replayMigrated?_fuelExhausted
#print axioms SchemaLang.EventSourced.replayMigrated?_diverged

-- W8.5: scheduling — rates (the decide tie, periodicity, multiples,
-- the in-period negative), delays (the next-tick law, composition,
-- the Dbsp.delay tie), deadlines (the missed iff overdue-and-undone
-- family). Bar: the core triple.
#print axioms SchemaLang.Scheduling.Rate.due?_iff
#print axioms SchemaLang.Scheduling.Rate.due_zero
#print axioms SchemaLang.Scheduling.Rate.due_periodic
#print axioms SchemaLang.Scheduling.Rate.due_mul
#print axioms SchemaLang.Scheduling.Rate.due?_false_of_lt
#print axioms SchemaLang.Scheduling.Rate.sample_due
#print axioms SchemaLang.Scheduling.Rate.sample_hold
#print axioms SchemaLang.Scheduling.delayBy_zero
#print axioms SchemaLang.Scheduling.delayBy_one_zero
#print axioms SchemaLang.Scheduling.delayBy_one_succ
#print axioms SchemaLang.Scheduling.delayBy_add
#print axioms SchemaLang.Scheduling.delayBy_eq_delay
#print axioms SchemaLang.Scheduling.missed_false_of_done
#print axioms SchemaLang.Scheduling.missed_false_of_lt
#print axioms SchemaLang.Scheduling.missed_at
#print axioms SchemaLang.Scheduling.missed_true_of_overdue

-- W8.6 effects/commands: the well-formedness bridge (the lane's own
-- footprint) + the derived session's laws — each law CITES the generic
-- Machines.Session theorem (the mechanism is proved once, there).
#print axioms SchemaLang.EffectDecl.check_eq_nil_iff
#print axioms SchemaLang.EffectDecl.check_sound
#print axioms SchemaLang.EffectDecl.check_complete
#print axioms SchemaLang.EffectDecl.protocol_dual
#print axioms SchemaLang.EffectDecl.protocol_deadlockFree
#print axioms SchemaLang.EffectDecl.protocol_terminates
#print axioms SchemaLang.EffectDecl.toWire_eq
#print axioms SchemaLang.EffectDecl.protocol_wire_bridge
#print axioms SchemaLang.EffectDecl.protocol_wire_payloads

-- W8.4 entity-machine preset: the generic laws (one proof per law, every
-- generated machine instantiates them) + the agreement chain.
#print axioms SchemaLang.EntityMachine.legalFrom
#print axioms SchemaLang.EntityMachine.legalJournal_iff
#print axioms SchemaLang.EntityMachine.replay_of_legalJournal
#print axioms SchemaLang.EntityMachine.trans_honest
#print axioms SchemaLang.EntityMachine.hookEdges_legal
#print axioms SchemaLang.EntityMachine.hookStates_reachable
#print axioms SchemaLang.EntityMachine.EntityObligation.discharge_sound
#print axioms SchemaLang.EntityMachine.EntityObligation.discharge_of_claim
