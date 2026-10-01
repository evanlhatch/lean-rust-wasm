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

/-- The rel drawer: all TEN arms, at a bounded depth. -/
def drawRel : Nat → Tape → (Rel × Tape)
  | 0, t => drawRead t
  | depth + 1, t =>
      let (k, t) := t.below 10
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
      | 7 =>
          let (so, t) := t.below 2
          let (l, t) := drawRel depth t
          let (r, t) := drawRel depth t
          (.set (if so == 0 then .unionAll else .unionDistinct) l r, t)
      | 8 =>
          let (l, t) := drawRel depth t
          let (r, t) := drawRel depth t
          (.cross l r, t)
      | _ =>
          -- the write rel: named table + op + table schema (fields
          -- drawn from the narrow type set) + the input rel
          let (nn, t) := t.below 3
          let (nms, t) := drawMany nn drawString t
          let (o, t) := t.below 4
          let (nt, t) := t.below 3
          let (tys, t) := drawMany nt drawPTy t
          let (nc, t) := t.below 3
          let (cols, t) := drawMany nc drawString t
          let (i, t) := drawRel depth t
          (.write nms ((writeOpOfNum? o).getD .insert)
            { fields := tys, names := cols } i, t)

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

/-! ## the shrinker (the Shrink discipline's first consumer over the
    drawn plans; testingkit/TestingKit/Shrink.lean) -/

/-- The rel's structural size: one per node (the shrinker's measure's
    summand — removals of a sub-rel strictly shorten). -/
def relSize : Rel → Nat
  | .read _ _ => 1
  | .filter _ r => 1 + relSize r
  | .project _ r => 1 + relSize r
  | .join _ l r _ => 1 + relSize l + relSize r
  | .aggregate _ _ r => 1 + relSize r
  | .sort _ r => 1 + relSize r
  | .fetch _ _ r => 1 + relSize r
  | .set _ l r => 1 + relSize l + relSize r
  | .cross l r => 1 + relSize l + relSize r
  | .write _ _ _ r => 1 + relSize r

/-- The plan-rel's size (the root's own node counts). -/
def planRelSize : PlanRel → Nat
  | .rel r => relSize r
  | .root _ r => 1 + relSize r

/-- The plan's size: the function rows + the relation nodes. -/
def planSize (p : Plan) : Nat :=
  p.functions.length + (p.relations.map planRelSize).sum

theorem relSize_pos : ∀ r : Rel, 0 < relSize r := by
  intro r; cases r <;> simp only [relSize] <;> omega

theorem planRelSize_pos : ∀ pr : PlanRel, 0 < planRelSize pr := by
  intro pr; cases pr with
  | rel r => simp only [planRelSize]; exact relSize_pos r
  | root _ r => simp only [planRelSize]; have h := relSize_pos r; omega

/-- Removing an element from a list strictly shrinks the mapped sum
    when every element's size is positive (the removals shrinker's
    `smaller` obligation, at the sum-of-sizes measure). -/
theorem sum_removals_lt : ∀ (xs : List α) (f : α → Nat), (∀ x, 0 < f x) →
    ∀ r, r ∈ removals xs → (r.map f).sum < (xs.map f).sum
  | [], _, _, r, hr => absurd hr (by simp [removals])
  | x :: xs, f, hpos, r, hr => by
      simp only [removals, List.mem_cons] at hr
      rcases hr with h1 | h'
      · subst h1
        simp only [List.map_cons, List.sum_cons]
        have h0 := hpos x
        omega
      · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp h'
        simp only [List.map_cons, List.sum_cons]
        have h := sum_removals_lt xs f hpos r' hr'
        omega

theorem sum_ones (xs : List α) : (xs.map (fun _ => 1)).sum = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      omega

/-- The PLAN shrinker: single-relation removals + single-function
    removals, on the structural-size measure. The plan's fields are
    INDEPENDENT (no coupled re-derivation — the dependent-pair
    anti-pattern does not apply; the coupling combinator's discipline
    is for Σ-types), so the field-wise candidate families are valid
    here; validity is trivial (any plan is a plan). -/
def shrinkPlan : ShrinkerV (α := Plan) (fun _ => True) where
  shrink p :=
    (removals p.relations).map (fun rs => { p with relations := rs })
      ++ (removals p.functions).map (fun fs => { p with functions := fs })
  measure p := planSize p
  smaller p c hc := by
    rcases List.mem_append.mp hc with h | h
    · obtain ⟨rs, hr, rfl⟩ := List.mem_map.mp h
      have hlt := sum_removals_lt p.relations planRelSize planRelSize_pos rs hr
      simp only [planSize] at hlt ⊢
      simpa using hlt
    · obtain ⟨fs, hf, rfl⟩ := List.mem_map.mp h
      have hlt := sum_removals_lt p.functions (fun _ => 1)
        (fun _ => Nat.zero_lt_succ 0) fs hf
      simp only [planSize, sum_ones] at hlt ⊢
      simpa using hlt
  valid := fun _ _ _ => trivial

/-- The wire prop's content at the drawn plan ALONE (the attachment's
    `fails`: tape-free — the in-domain gate + the full round trip at
    the law's fuel; the truncation/sub-rel faces are the sweep's
    other teeth, not the plan's content). -/
def wireFails (p : Plan) : Bool :=
  !(inDomainPlan p = true
    && decPlan? ((encPlan p).length + 1) (encPlan p) == some p)

/-- The drawn plan's render (the failure evidence's face). -/
def renderPlan (p : Plan) : String :=
  s!"plan(size {planSize p}, {p.relations.length} rels, {p.functions.length} fns)"

/-- THE SHRINK PIN's fixture: the SABOTAGED twin sweep — claims a
    drawn plan never carries two relations (it fails exactly there) —
    with the SAME attachment shape. Its failure evidence MUST carry
    the shrunk counterexample + the path; the wire spec's control
    below fires iff it does. -/
def wireSabFails (p : Plan) : Bool := p.relations.length ≥ 2

def wireSabSpec : Spec :=
  Spec.ofList "sabotaged: the drawn plan stays under two relations"
    (fun t => assert (!wireSabFails (drawPlan t).1) "sabotaged: the plan grew two relations")
    [ ("truncated-plan-refusal", truncationProp)
    , ("off-domain-plan-refusal", negOffDomain) ]
    8 20260929
    (shrunk := some ⟨Plan, fun _ => True, fun t => (drawPlan t).1,
                     renderPlan, wireSabFails, shrinkPlan⟩)

/-- THE SHRINK PIN (the discipline's tooth): the sabotaged twin's
    failure evidence reports the SHRUNK counterexample + the path.
    The control asserts the evidence is ABSENT — it must FAIL (be
    caught); a dead attachment leaves it uncaught → VACUOUS, louder
    than passing. -/
def wireNegNoShrinkEvidence : Tape → CheckResult := fun _ =>
  match wireSabSpec.run with
  | .fail .prop _ _ m =>
      assert (!((m.splitOn "shrunk: minimal").length > 1))
        s!"control fired: the shrink evidence WAS present: {m}"
  | _ => assert false "the sabotaged sweep did not fail"

/-! ## the suite -/

def wireSpec : Spec :=
  Spec.ofList "the protobuf wire: the drawn-fragment round trips + the truncation sweep"
    wireProp
    [ ("truncated-plan-refusal", truncationProp)
    , ("off-domain-plan-refusal", negOffDomain)
    , ("trailing-byte-refusal", negTrailingByte)
    , ("wire-target-row-pins", negWireTargetRow)
    , ("shrink evidence absent", wireNegNoShrinkEvidence) ]
    32 20260929
    (shrunk := some ⟨Plan, fun _ => True, fun t => (drawPlan t).1,
                     renderPlan, wireFails, shrinkPlan⟩)
