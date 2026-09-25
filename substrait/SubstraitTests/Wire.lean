/-
# SubstraitTests.Wire — the protobuf wire's sweeps + the negative controls

The wire lane's pins (the WireTarget row's entourage, executed):

1. `wireSweep` — the LCG-drawn plans over the inDomain fragment (every
   Rel arm, every expression arm, the read's optional schema, the fetch's
   optional window), full round trip at the law's fuel + the per-rel nil
   face + the per-arm face over the DRAWN sub-rels.
2. Negative controls (mandatory): the TRUNCATION sweep (a plan's encoding
   minus its last byte refuses — the canonical dialect's length
   discipline), the TRAILING-BYTE refusal (the full face's exact-image
   discipline), the OFF-DOMAIN plan (the non-ASCII function name: the
   gate refuses at the emission boundary AND the wire refuses the
   truncated byte — the pinned loss, pattern #5), and the
   WireTarget-row pins (the honest conditional grade; the row's own
   off-domain control).
-/

import Substrait
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness

open Substrait Substrait.Proto Substrait.Wire TestingKit Kit.Proto

set_option maxRecDepth 8000

/-! ## the drawers (the LCG-drawn plans over the inDomain fragment) -/

def drawNull (t : Tape) : (Nullability × Tape) :=
  let (k, t) := t.below 3
  ((nullabilityOfNum? k).getD .unspecified, t)

def drawPTy (t : Tape) : (PType × Tape) :=
  let (k, t) := t.below 4
  match k with
  | 0 => let (n, t) := drawNull t; (.bool n, t)
  | 1 => let (n, t) := drawNull t; (.i32 n, t)
  | 2 => let (n, t) := drawNull t; (.i64 n, t)
  | _ => let (n, t) := drawNull t; (.string n, t)

def drawLit (t : Tape) : (Literal × Tape) :=
  let (k, t) := t.below 4
  let (n, t) := drawNull t
  let nbl := n == .nullable
  match k with
  | 0 => let (b, t) := t.below 2; ({ literalType := .bool (b == 1), nullable := nbl }, t)
  | 1 => let (v, t) := t.below 1000; ({ literalType := .i32 v, nullable := nbl }, t)
  | 2 => let (v, t) := t.below 1000; ({ literalType := .i64 v, nullable := nbl }, t)
  | _ => let (s, t) := drawString t; ({ literalType := .string s, nullable := nbl }, t)

def drawExpr : Nat → Tape → (Expression × Tape)
  | 0, t => let (l, t) := drawLit t; (.literal l, t)
  | depth + 1, t =>
      let (k, t) := t.below 3
      match k with
      | 0 => let (l, t) := drawLit t; (.literal l, t)
      | 1 => let (o, t) := t.below 8; (.field { ordinal := o }, t)
      | _ =>
          let (nm, t) := drawString t
          let (nargs, t) := t.below 3
          let (args, t) := drawMany nargs (drawExpr depth) t
          let (out, t) := drawPTy t
          (.scalarFunction nm args out, t)

def drawSortField (t : Tape) : (SortField × Tape) :=
  let (e, t) := drawExpr 1 t
  let (d, t) := t.below 2
  ({ expr := e, direction := if d == 0 then .ascNullsFirst else .descNullsFirst }, t)

def drawRead (t : Tape) : (Rel × Tape) :=
  let (nnames, t) := t.below 3
  let (nms, t) := drawMany nnames drawString t
  let (hasSchema, t) := t.below 2
  if hasSchema == 1 then
    let (ntypes, t) := t.below 3
    let (tys, t) := drawMany ntypes drawPTy t
    let (ncols, t) := t.below 3
    let (cols, t) := drawMany ncols drawString t
    (.read (.namedTable nms) (some { fields := tys, names := cols }), t)
  else
    (.read (.namedTable nms) none, t)

/-- The rel drawer: all EIGHT arms, at a bounded depth. -/
def drawRel : Nat → Tape → (Rel × Tape)
  | 0, t => drawRead t
  | depth + 1, t =>
      let (k, t) := t.below 8
      match k with
      | 0 => drawRead t
      | 1 =>
          let (c, t) := drawExpr 2 t
          let (i, t) := drawRel depth t
          (.filter c i, t)
      | 2 =>
          let (nes, t) := t.below 3
          let (es, t) := drawMany nes (drawExpr 2) t
          let (i, t) := drawRel depth t
          (.project es i, t)
      | 3 =>
          let (jt, t) := t.below 4
          let (l, t) := drawRel depth t
          let (r, t) := drawRel depth t
          let (c, t) := drawExpr 2 t
          (.join ((joinTypeOfNum? jt).getD .inner) l r c, t)
      | 4 =>
          let (ng, t) := t.below 3
          let (gs, t) := drawMany ng (drawExpr 2) t
          let (nm, t) := t.below 3
          let (ms, t) := drawMany nm (drawExpr 2) t
          let (i, t) := drawRel depth t
          (.aggregate gs ms i, t)
      | 5 =>
          let (nk, t) := t.below 3
          let (ks, t) := drawMany nk drawSortField t
          let (i, t) := drawRel depth t
          (.sort ks i, t)
      | 6 =>
          let (hl, t) := t.below 2
          let (ho, t) := t.below 2
          let (lim, t) :=
            if hl == 1 then let (v, t) := t.below 100; (some v, t) else (none, t)
          let (off, t) :=
            if ho == 1 then let (v, t) := t.below 100; (some v, t) else (none, t)
          let (i, t) := drawRel depth t
          (.fetch lim off i, t)
      | _ =>
          let (so, t) := t.below 2
          let (l, t) := drawRel depth t
          let (r, t) := drawRel depth t
          (.set (if so == 0 then .unionAll else .unionDistinct) l r, t)

def drawPlanRel (depth : Nat) (t : Tape) : (PlanRel × Tape) :=
  let (k, t) := t.below 2
  let (r, t) := drawRel depth t
  match k with
  | 0 => (.rel r, t)
  | _ =>
      let (nn, t) := t.below 3
      let (nms, t) := drawMany nn drawString t
      (.root nms r, t)

def drawPlan (t : Tape) : (Plan × Tape) :=
  let (nrels, t) := t.below 3
  let (rels, t) := drawMany nrels (drawPlanRel 2) t
  let (nfns, t) := t.below 3
  let (fns, t) := drawMany nfns drawString t
  ({ functions := fns, relations := rels }, t)

/-! ## the sweep -/

/-- The wire's round trip, swept over the drawn plans: the drawn plans
    ride the inDomain fragment (the ASCII strings' drawer, the bounded
    fetch window), the full face at the law's fuel = the encoded size +
    1, and the drawn SUB-RELS' nil faces at theirs. These value-level
    rows are the LAWS' executable echo (decPlan?_encPlan,
    decRelBody?_law), kept as a drift tripwire over the concrete
    spellings. -/
def wireProp (t : Tape) : CheckResult := do
  let (p, _) := drawPlan t
  let bytes := encPlan p
  assert (inDomainPlan p = true) "the drawn plan left the inDomain fragment"
  assert (decPlan? ((encPlan p).length + 1) (encPlan p) == some p)
    "the plan round trip broke at the law's fuel"
  -- the truncation face, swept: minus its last byte, the drawn plan's
  -- encoding refuses (the canonical dialect's length discipline; the
  -- empty plan's encoding is empty — the row is skipped then)
  assert (!(bytes.length > 0) || decPlan? bytes.length (bytes.take (bytes.length - 1)) == none)
    "the truncated plan parsed"
  let (r, _) := drawRel 2 t
  assert ((decRelBody? ((encRelBody r).length + 1) (encRelBody r)).map
      (fun s => match s with | .more a _ => a | .stop _ => .read (.namedTable []) none)
      == r)
    "the rel body's nil face broke at the law's fuel"

/-- The TRUNCATION SABOTAGE: claims the truncated plan still parses to
    the plan — caught (every field's length prefix outruns the bytes;
    the canonical dialect's discipline). -/
def truncationProp (_t : Tape) : CheckResult := do
  let p : Plan := { functions := ["add"], relations := [.rel (.read (.namedTable ["t", "u"]) none)] }
  let bytes := encPlan p
  assert (decPlan? bytes.length (bytes.take (bytes.length - 1)) == some p)
    "the truncated plan parsed (the length discipline broke)"

/-! ## the negative controls (mandatory) -/

/-- The OFF-DOMAIN SABOTAGE: the non-ASCII function name — claims the
    GATE accepts it and the WIRE round-trips it — caught on BOTH faces
    (the gate refuses at the emission boundary; the codepoint's
    truncation puts a byte ≥ 128 in the string face, whose read-back
    refuses) — the pinned loss (pattern #5), never a silent law gap. -/
def negOffDomain (_t : Tape) : CheckResult := do
  let bad : Plan := { functions := ["dé"], relations := [] }
  assert (inDomainPlan bad)
    "the non-ASCII function name passed the gate"
  assert (decPlan? ((encPlan bad).length + 1) (encPlan bad) == some bad)
    "the off-domain plan's encoding parsed"

/-- The TRAILING-BYTE SABOTAGE: junk bytes after a complete plan —
    claims they still parse to the plan — caught (the full face's
    exact-image discipline; the plan law's clean-suffix conditionality
    is the honest face of exactly this). -/
def negTrailingByte (_t : Tape) : CheckResult := do
  let p : Plan := { functions := ["add"], relations := [.rel (.read (.namedTable ["t"]) none)] }
  assert (decPlan? ((encPlan p).length + 6) (encPlan p ++ [0, 0, 0, 0, 0]) == some p)
    "the trailing bytes parsed"

/-- The WIRE-TARGET-ROW SABOTAGE: claims the grade is the full Codec
    (a fake — the plan law is inDomain- + clean-suffix-conditional) and
    that the row's off-domain control is in-domain — caught on both. -/
def negWireTargetRow (_t : Tape) : CheckResult := do
  assert (planWireTarget.grade == .codec)
    "the plan WireTarget's grade is not the honest conditional one"
  assert ((planWireTarget.offDomain.map inDomainPlan).all (· = true))
    "the WireTarget row's off-domain control is in-domain"

/-! ## the suite -/

def wireSpec : Spec :=
  Spec.ofList "the protobuf wire: the drawn-fragment round trips + the truncation sweep"
    wireProp
    [ ("truncated-plan-refusal", truncationProp)
    , ("off-domain-plan-refusal", negOffDomain)
    , ("trailing-byte-refusal", negTrailingByte)
    , ("wire-target-row-pins", negWireTargetRow) ]
    32 20260929
