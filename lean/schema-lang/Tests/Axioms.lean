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
