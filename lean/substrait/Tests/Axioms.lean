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
