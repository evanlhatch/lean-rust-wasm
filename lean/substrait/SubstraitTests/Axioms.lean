/- Axiom gate — the headline theorems must print only the core triple
   (+ disclosed native_decide). Ported from the flatland lineage's fuller
   list (~22 decls), names adapted to this tree's namespaces
   (`Substrait`, not `LeanSubstrait`; Grammar.lean lives in
   `Substrait.Grammar`). The lineage's `splitTopLevel_join_rbracket` /
   `sep_toList_joinCSep` entries are dropped: both were dead here and got
   deleted (Decode.lean sweep). -/
import Substrait

-- the typed lowering + evaluator
#print axioms Substrait.Typed.Rel.toProto
#print axioms Substrait.Typed.Rel.toPlan
#print axioms Substrait.Typed.Rel.toCtx
#print axioms Substrait.Typed.Rel.toProtoWith
#print axioms Substrait.Typed.eval
#print axioms Substrait.Typed.evalProject
#print axioms Substrait.Typed.evalJoin
#print axioms Substrait.Emit.Text.emit

-- the type-inversion layer
#print axioms Substrait.Decode.parseType_mono
#print axioms Substrait.Decode.parseType_mono_of_le
-- the typed grammar spine: lexing uniqueness + the ctor-generic scalar
-- inversion (the nine hand-written parseType_<scalar> wrappers are gone;
-- scalarT is the one theorem)
#print axioms Substrait.Grammar.TCtor.prefix_unique
#print axioms Substrait.Decode.lexCtor_self
#print axioms Substrait.Decode.parseType_scalar
#print axioms Substrait.Decode.parseType_scalar_nullable
#print axioms Substrait.Decode.scalarT
#print axioms Substrait.Decode.parseType_typeText

-- the expression inversions (field refs, bool/int literals, escape round-trip)
#print axioms Substrait.Decode.parseExpr_field
#print axioms Substrait.Decode.parseExpr_lit_bool
#print axioms Substrait.Decode.parseExpr_lit_i64
#print axioms Substrait.Decode.unescape_escape

-- the relation layer (parseNamedCol + the splitAppend inversion chain)
#print axioms Substrait.Decode.parseNamedCol_emitted
#print axioms Substrait.Decode.splitAppend_map_parseNamedCol

-- the decode round-trip entry point
#print axioms Substrait.Decode.parsePlan

-- W5.3 phase 2a: the name-family tables + round trips
#print axioms Substrait.Grammar.findName_self
#print axioms Substrait.Grammar.joinGrammar_name_nodup
#print axioms Substrait.Grammar.setGrammar_name_nodup
#print axioms Substrait.Grammar.sortDirGrammar_name_nodup
#print axioms Substrait.Decode.joinTypeOfName_joinTypeName
#print axioms Substrait.Decode.setOpOfName_setOpName
#print axioms Substrait.Decode.sortDirOfName_sortDirName
#print axioms Substrait.Decode.parseType_literalTypeName

-- W5.3 phase 2b: the line-shape grammar (tokens + indent + the bindings
-- and Root inversions).  The extension/version row inversions are the
-- generated `inv_urnLine`/`inv_declLine`/`inv_versionLines` theorems
-- (Substrait.Decode.Inversions); their pre-macro wrapper names
-- (`parseUrnEntry_urnLine` & kin, the `invcor` corollaries) were deleted
-- with the wrappers, so their pins are gone with them.
#print axioms Substrait.Grammar.ExtKind.ofHeader_self
#print axioms Substrait.Grammar.ExtKind.ofNum_self
#print axioms Substrait.Grammar.CastFbCtor.ofBehavior_toBehavior
#print axioms Substrait.Decode.castFbScan_token
#print axioms Substrait.Decode.splitOnPipe_self
#print axioms Substrait.Decode.indentOf_indentUnits
#print axioms Substrait.Decode.drop_indentUnits
#print axioms Substrait.Decode.parseRootNames_emitted
