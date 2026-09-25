/-
# SchemaCore.Dependent — the dependent-schemas lane (D20's honest fragment)

Owner: the SchemaCore dependent lane (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/decisions.md D20 (dependent schemas
first-class: length dependencies + tagged payloads, with the honest
target story — storage repr + smart constructors + boundary validators
+ the correspondence); notes/v3/02-data-plane.md §1-2 (the schema
describes valid worlds; a dependency BETWEEN fields is a row-level
constraint, not a type); notes/v3/15-patterns.md #1 (the
relation-as-spec + executable checker + proved bridge — the pattern,
reused, never a parallel table) + #4 (the obligation as data);
notes/v3/04-verification.md §1 (the ladder).

THE SHAPE CALL (the lane's one judgment, made once): the dependent
discipline is a SPEC OVER THE ITEM, not a `Ty` extension.

- `Ty` is a CLOSED first-order universe (Ty.lean's header): a
  length-dependent field (`Vector UInt8 length`) needs a NAME REFERENCE
  inside a type — exactly the open-world `.ty (name : TyRef)` lane the
  closed universe deliberately excludes (the well-formedness resolution
  machinery has no slice consumer). Extending `Ty` would also break
  every fold's exhaustiveness for a fragment the folds cannot see.
- The dependencies are BETWEEN fields: `length` and `bytes` are each
  ordinary closed-`Ty` fields; the RELATION between them is row-level
  content — 02 §1-2's reading (a row predicate is a constraint over one
  row). So the dependency is DECLARED AS DATA over the item's fields,
  with the checker + the Sat relation + the proved bridge — pattern #1
  at the dependent tier, the same shape `Pred`/`Check` mount.

THE FRAGMENT (D20's honestly-supported list at the tree's scale):

- `Dep.lengthEq count bytes` — the LENGTH DEPENDENCY: the list field
  `bytes`'s length equals the u64 field `count`'s value (the
  `Packet { length : Nat, bytes : Vector UInt8 length }` review
  example's schema-level form);
- `Dep.tagMatches tag payload` — the TAGGED DEPENDENT PAYLOAD: the
  result-flavored field `payload`'s arm is determined by the u64 field
  `tag` (0 = ok, 1 = err; a tag outside {0,1} refuses — the enum
  dependency's honest minimal).

Everything else (finite indices, general refinement predicates,
substitutions) stays OUT until its first consumer — the leftover rule
names each extension when it lands.

THE THREE FACES (pattern #1): `Dep.Sat` — the spec of record (defined
before the checker); `Dep.check` — the decidable procedure; `check_iff`
— both directions proved once. On top: `DepSpec` (the item + its
declared dependencies), the shape/legality discipline (`onFields` +
`shapeDiags` + the proved bridge — the first-match reading, matching
the projection's), THE PROOF-CARRYING PARSE (`validate` — successful
validation CONSTRUCTS the typed value; a validated row's invalid
successor is unconstructible), the RESTRICTED MUTATION (`setList?` —
the only list mutation is the re-validating one), and the TARGET
CORRESPONDENCE (D20's story stated over the lane's data: the ordinary
storage representation is the `RowVals` row; the smart constructor is
`validate`; the boundary validator's RUST FACE renders from the SAME
`Dep` data the Lean checker reads — one owner. The emitter integration
(`SchemaCore.Emit` consuming `rustCheck` for dependent records) is the
NAMED step: Emit/ is a separate lane's file; the dependent lane's
emitter row lands with that wave. Proof erasure does NOT eliminate the
boundary validation: the erased artifact keeps `check`, the proof
`Sat` rides the type).

The five questions (notes/v3/01-core.md): root = Universe (data — the
dependency declaration over the item's fields); carrier = the
`ValidRow` subtype (an invalid row is INHABITABLE as validated data —
rung 1 where it counts, the checker bridge where it decides); spine
reading = Registry row → validate → typed value (the ingress
discipline's spine); ladder rung = the bridge is the small hand kind
(one induction, both directions), the subtype the rung-1 face; gate
row = SchemaTests' dependentSpec pins + the negative controls + the
axiom report.

Core-only (imports SchemaCore.Fold, SchemaCore.Pred,
SchemaCore.RowVals — the cone rule; the Rust face renders TEXT only,
it is not an emitter).
-/

import SchemaCore.Fold
import SchemaCore.Pred
import SchemaCore.RowVals

namespace SchemaCore

/-! ## The projected readings the dependencies need -/

/-- The list sibling's length (the reading the length dependency
    consumes; structural, kernel-visible). -/
def VList.len : {t : Ty} → VList t → Nat
  | _, .nil => 0
  | _, .cons _ vs => 1 + vs.len

/-- The list-length reading of a projected field: `some n` when the
    column is a list of length `n`; `none` when missing or mistyped
    (the `u64?` refusal discipline, Pred.lean's). -/
def FieldVal.listLen? : FieldVal → Option Nat
  | ⟨.list _, .list vl⟩ => some vl.len
  | _ => none

/-- The result-arm reading of a projected field: `some true` = the ok
    arm, `some false` = the err arm; `none` when missing or not a
    result (the refusal discipline again). -/
def FieldVal.okIs? : FieldVal → Option Bool
  | ⟨.result _ _, .ok _⟩ => some true
  | ⟨.result _ _, .err _⟩ => some false
  | _ => none

/-! ## The dependency fragment -/

/-- One declared dependency BETWEEN two fields of a record. The
    fragment is CLOSED (the module header's honesty): two shapes, each
    naming the pair of fields it constrains. -/
inductive Dep where
  /-- The length dependency: the list field `bytes`'s length equals
      the u64 field `count`'s value. -/
  | lengthEq (count bytes : String)
  /-- The tagged payload: the result field `payload`'s arm is the u64
      field `tag`'s value (0 = ok, 1 = err). -/
  | tagMatches (tag payload : String)
  deriving Repr, BEq

/-- The dependency's referenced field names (the legality surface's
    input — Check.lean's `Pred.reads` discipline). -/
def Dep.knownNames : Dep → List String
  | .lengthEq c b => [c, b]
  | .tagMatches t p => [t, p]

/-- THE CHECKER — the decidable procedure. A projection failure
    refuses (`false`): a missing or mistyped column does not satisfy a
    dependency (the `columnU64?` discipline, never a fabricated
    comparison). -/
def Dep.check : Dep → (fs : List Field) → RowVals fs → Bool
  | .lengthEq c b, fs, row =>
      match (RowVals.project? fs row c).bind FieldVal.u64?,
            (RowVals.project? fs row b).bind FieldVal.listLen? with
      | some n, some l => n.toNat == l
      | _, _ => false
  | .tagMatches t p, fs, row =>
      match (RowVals.project? fs row t).bind FieldVal.u64?,
            (RowVals.project? fs row p).bind FieldVal.okIs? with
      | some tag, some arm => (tag == 0 && arm) || (tag == 1 && !arm)
      | _, _ => false

/-- THE SEMANTICS: a dependency's meaning over a row — the honest
    relation, defined before and independently of the checker
    (pattern #1: the spec never lies to fit the checker). -/
def Dep.Sat : Dep → (fs : List Field) → RowVals fs → Prop
  | .lengthEq c b, fs, row =>
      ∃ n, (RowVals.project? fs row c).bind FieldVal.u64? = some n
        ∧ (RowVals.project? fs row b).bind FieldVal.listLen? = some n.toNat
  | .tagMatches t p, fs, row =>
      ∃ tag, (RowVals.project? fs row t).bind FieldVal.u64? = some tag
        ∧ (tag = 0 ∨ tag = 1)
        ∧ (RowVals.project? fs row p).bind FieldVal.okIs? = some (tag == 0)

/-! ## THE BRIDGE (pattern #1) — checker → relation, both directions -/

theorem Dep.check_iff :
    ∀ (d : Dep) (fs : List Field) (row : RowVals fs),
      d.check fs row = true ↔ d.Sat fs row := by
  intro d
  cases d with
  | lengthEq c b =>
      intro fs row
      simp only [Dep.check, Dep.Sat]
      cases hc : (RowVals.project? fs row c).bind FieldVal.u64? with
      | none =>
          constructor
          · intro h
            exact absurd h Bool.false_ne_true
          · rintro ⟨n, hn, _⟩
            cases hn
      | some n =>
          cases hb : (RowVals.project? fs row b).bind FieldVal.listLen? with
          | none =>
              constructor
              · intro h
                exact absurd h Bool.false_ne_true
              · rintro ⟨n', hn1, hn2⟩
                cases hn2
          | some l =>
              constructor
              · intro h
                have h' : (n.toNat == l) = true := h
                exact ⟨n, rfl, by rw [beq_iff_eq.mp h']⟩
              · intro h
                obtain ⟨n', hn1, hn2⟩ := h
                rw [← Option.some.inj hn1] at hn2
                exact beq_iff_eq.mpr (Option.some.inj hn2).symm
  | tagMatches t p =>
      intro fs row
      simp only [Dep.check, Dep.Sat]
      cases ht : (RowVals.project? fs row t).bind FieldVal.u64? with
      | none =>
          constructor
          · intro h
            exact absurd h Bool.false_ne_true
          · rintro ⟨tag, htag, _, _⟩
            cases htag
      | some tag =>
          cases hp : (RowVals.project? fs row p).bind FieldVal.okIs? with
          | none =>
              constructor
              · intro h
                exact absurd h Bool.false_ne_true
              · rintro ⟨tag', ht1, _, hp1⟩
                cases hp1
          | some arm =>
              constructor
              · intro h
                have h' : ((tag == 0 && arm) || (tag == 1 && !arm)) = true := h
                rcases Bool.or_eq_true_iff.mp h' with h0 | h1
                · rw [Bool.and_eq_true] at h0
                  exact ⟨tag, rfl, Or.inl (beq_iff_eq.mp h0.1),
                    by simp [beq_iff_eq.mp h0.1, h0.2]⟩
                · rw [Bool.and_eq_true] at h1
                  have h1b : arm = false := by simpa using h1.2
                  exact ⟨tag, rfl, Or.inr (beq_iff_eq.mp h1.1),
                    by simp [beq_iff_eq.mp h1.1, h1b]⟩
              · intro h
                obtain ⟨tag', ht1, hrange, hp1⟩ := h
                have htag : tag = tag' := Option.some.inj ht1
                have harm : arm = (tag' == 0) := Option.some.inj hp1
                rw [htag, harm]
                rcases hrange with h0 | h1
                · subst h0; simp
                · subst h1; simp

/-- SOUNDNESS: a `true` verdict is a proof of `Sat` (the checker never
    fabricates a satisfaction — pattern #1's soundness face). -/
theorem Dep.check_sound (fs : List Field) (d : Dep) (row : RowVals fs)
    (h : d.check fs row = true) : d.Sat fs row :=
  (d.check_iff fs row).mp h

/-- COMPLETENESS: every satisfying row's verdict is `true`. -/
theorem Dep.check_complete (fs : List Field) (d : Dep) (row : RowVals fs)
    (h : d.Sat fs row) : d.check fs row = true :=
  (d.check_iff fs row).mpr h

/-! ## The shape/legality discipline (the first-match reading) -/

/-- The scalar shape gates (the closure's reading — a Bool per shape,
    kernel-reducible over concrete types). -/
def Ty.isU64 : Ty → Bool
  | .u64 => true
  | _ => false

def Ty.isList : Ty → Bool
  | .list _ => true
  | _ => false

def Ty.isResult : Ty → Bool
  | .result _ _ => true
  | _ => false

/-- THE GENERIC IF-NIL LEMMA: two guard-gated message lists join to
    nil iff both guards hold — the shape bridge's one content lemma
    (proved once; the two dep constructors cite it). -/
theorem ifNil_pair (X Y : Bool) (mx my : String) :
    ((if X then [] else [mx]) ++ (if Y then [] else [my])) = []
      ↔ (X = true ∧ Y = true) := by
  cases X <;> cases Y <;> simp

/-- The dependency's WELL-FORMEDNESS on a field list: both referenced
    fields RESOLVE (first match — the projection's own reading, so the
    legality can never drift from what the checker reads) and carry
    the shapes the dependency constrains. -/
def Dep.onFields (fields : List Field) : Dep → Prop
  | .lengthEq c b =>
      match fields.find? (·.name == c), fields.find? (·.name == b) with
      | some fC, some fB => fC.ty.isU64 = true ∧ fB.ty.isList = true
      | _, _ => False
  | .tagMatches t p =>
      match fields.find? (·.name == t), fields.find? (·.name == p) with
      | some fT, some fP => fT.ty.isU64 = true ∧ fP.ty.isResult = true
      | _, _ => False

/-- The diagnostic authority: the same facts as DATA (the closed-world
    constructor carries the offending field + the valid space — the
    Check.lean `scopedDiags` discipline). Empty = legal. -/
def Dep.shapeDiags (fields : List Field) : Dep → List String
  | .lengthEq c b =>
      match fields.find? (·.name == c) with
      | none => [s!"field `{c}` is not on record — the length \
          dependency's count field must be a declared field"]
      | some fC =>
          match fields.find? (·.name == b) with
          | none => [s!"field `{b}` is not on record — the length \
              dependency's bytes field must be a declared field"]
          | some fB =>
              (if fC.ty.isU64 then []
                else [s!"field `{c}` must be u64 (got {renderTy fC.ty})"])
              ++ (if fB.ty.isList then []
                else [s!"field `{b}` must be a list (got {renderTy fB.ty})"])
  | .tagMatches t p =>
      match fields.find? (·.name == t) with
      | none => [s!"field `{t}` is not on record — the tagged \
          payload's tag field must be a declared field"]
      | some fT =>
          match fields.find? (·.name == p) with
          | none => [s!"field `{p}` is not on record — the tagged \
              payload's payload field must be a declared field"]
          | some fP =>
              (if fT.ty.isU64 then []
                else [s!"field `{t}` must be u64 (got {renderTy fT.ty})"])
              ++ (if fP.ty.isResult then []
                else [s!"field `{p}` must be a result (got {renderTy fP.ty})"])

/-- THE SHAPE BRIDGE: the diagnostic authority and the reasoning
    authority agree (the `*_eq_nil_iff` family's shape — one fold, both
    directions; Check.lean's precedent; the content is the ONE generic
    `ifNil_pair` lemma, cited per constructor). -/
theorem Dep.shapeDiags_nil_iff (fields : List Field) (d : Dep) :
    d.shapeDiags fields = [] ↔ d.onFields fields := by
  cases d with
  | lengthEq c b =>
      unfold shapeDiags onFields
      cases hC : fields.find? (fun f => f.name == c) with
      | none => simp [hC]
      | some fC =>
          cases hB : fields.find? (fun f => f.name == b) with
          | none => simp [hC, hB]
          | some fB => simp [hC, hB]
  | tagMatches t p =>
      unfold shapeDiags onFields
      cases hT : fields.find? (fun f => f.name == t) with
      | none => simp [hT]
      | some fT =>
          cases hP : fields.find? (fun f => f.name == p) with
          | none => simp [hT, hP]
          | some fP => simp [hT, hP]

/-! ## The spec: the item + its declared dependencies -/

/-- The dependent SPEC over an item: the item is the record-of-`Ty`
    fields (the ordinary storage representation — D20's target story
    starts HERE, not at a dependent type); `deps` declares the
    between-field relations the item's rows must satisfy. -/
structure DepSpec where
  item : Item
  deps : List Dep
  deriving Repr, BEq

/-- The spec's fields (the raw carrier's index — spelled once). -/
def DepSpec.fields (sp : DepSpec) : List Field := sp.item.fields

/-- THE VALID-ROW RELATION: every declared dependency is satisfied.
    The spec of record for the boundary validation. -/
def DepSpec.valid (sp : DepSpec) (row : RowVals sp.fields) : Prop :=
  ∀ d ∈ sp.deps, d.Sat sp.fields row

/-- The decidable shadow: the checker's all. -/
def DepSpec.check (sp : DepSpec) (row : RowVals sp.fields) : Bool :=
  sp.deps.all (fun d => d.check sp.fields row)

/-- THE SPEC BRIDGE: the checker decides the relation (the per-dep
    bridge lifted over the dependency list — one fold, both
    directions). -/
theorem DepSpec.check_iff (sp : DepSpec) (row : RowVals sp.fields) :
    sp.check row = true ↔ sp.valid row := by
  constructor
  · intro h d hd
    exact d.check_sound sp.fields row
      (List.all_eq_true.mp h d hd)
  · intro h
    exact List.all_eq_true.mpr
      (fun d hd => d.check_complete sp.fields row (h d hd))

/-- The validity claim is DECIDABLE over a concrete row (the claim's
    decision procedure is the checker — the bridge makes it decide the
    RELATION, not the checker's private Bool). -/
instance DepSpec.validDecidable (sp : DepSpec) (row : RowVals sp.fields) :
    Decidable (sp.valid row) :=
  decidable_of_iff _ (sp.check_iff row)

/-- The validated carrier: a row TOGETHER WITH its validity proof —
    the rung-1 face (an invalid row is uninhabitable as validated
    data). -/
abbrev ValidRow (sp : DepSpec) : Type :=
  { r : RowVals sp.fields // sp.valid r }

/-- THE PROOF-CARRYING PARSE (the boundary validator): the foreign
    bytes' ingress discipline. Successful validation CONSTRUCTS the
    typed value — the `some` branch carries the row AND the proof; a
    refused row constructs nothing. Proof erasure at the target does
    not eliminate this check (the erased artifact keeps `check`). -/
def DepSpec.validate (sp : DepSpec) (row : RowVals sp.fields) :
    Option (ValidRow sp) :=
  if h : sp.valid row then some ⟨row, h⟩ else none

/-- THE VALIDATOR'S SOUNDNESS: what `validate` returns IS the input
    row (validation never transforms) carrying the validity proof —
    the review's "successful validation constructs the typed value",
    stated as a theorem. -/
theorem DepSpec.validate_sound (sp : DepSpec) (row : RowVals sp.fields)
    (vrow : ValidRow sp) (h : sp.validate row = some vrow) :
    vrow.1 = row ∧ sp.valid vrow.1 := by
  simp only [validate] at h
  split at h
  · next hv =>
      have hvrow : vrow = ⟨row, hv⟩ := (Option.some.inj h).symm
      rw [hvrow]
      exact ⟨rfl, hv⟩
  · next => exact absurd h (by simp)

/-- The validator's teeth: a refused row REALLY fails a dependency
    (the refusal is the checker's verdict, not a silent acceptance). -/
theorem DepSpec.validate_none (sp : DepSpec) (row : RowVals sp.fields)
    (h : sp.validate row = none) : ¬ sp.valid row := by
  simp only [validate] at h
  split at h
  · next hv => exact absurd h (by simp)
  · next hne => exact hne

/-! ## The restricted mutation -/

/-- The list-payload replacement by field name: the ONE row-level edit
    the mutation API exposes. A field that is absent or not a u64-list
    refuses (`none` — the shape is checked IN the match, never
    cast). -/
def RowVals.replaceU64List? :
    (fs : List Field) → RowVals fs → String → VList .u64 →
    Option (RowVals fs)
  | [], .nil, _, _ => none
  | { name := nm, ty := t } :: fs, .cons v vs, n, vl =>
      if nm == n then
        match t with
        | .list .u64 => some (.cons (.list vl) vs)
        | _ => none
      else
        match RowVals.replaceU64List? fs vs n vl with
        | some vs' => some (.cons v vs')
        | none => none

/-- THE RESTRICTED MUTATION: the only way a validated row's list
    payload changes — through a RE-VALIDATING replace (the edit +
    re-validate discipline; the invalid successor is unconstructible:
    the only exits are a valid new row or a typed refusal). -/
def DepSpec.setList? (sp : DepSpec) (n : String) (vl : VList .u64)
    (vr : ValidRow sp) : Option (ValidRow sp) :=
  match vr.1.replaceU64List? sp.fields n vl with
  | some raw => sp.validate raw
  | none => none

/-- The mutation's law: a returned row is VALID (the subtype carries
    the proof — the API cannot fabricate an invalid successor). -/
theorem DepSpec.setList_sound (sp : DepSpec) (n : String)
    (vl : VList .u64) (vr : ValidRow sp) (w : ValidRow sp)
    (_h : sp.setList? n vl vr = some w) : sp.valid w.1 :=
  w.2

/-- The mutation's refusal teeth: when the replace refuses (absent or
    mistyped field) the mutation refuses with it — never a silent
    no-op passthrough of the old row. -/
theorem DepSpec.setList_none (sp : DepSpec) (n : String)
    (vl : VList .u64) (vr : ValidRow sp)
    (h : RowVals.replaceU64List? sp.fields vr.1 n vl = none) :
    sp.setList? n vl vr = none := by
  simp only [setList?]
  rw [h]

/-! ## The spec-level legality -/

/-- The spec's diagnostic authority: every dependency's shape diags
    over the item's fields (one fold). -/
def DepSpec.scopedDiags (sp : DepSpec) : List String :=
  sp.deps.flatMap (·.shapeDiags sp.fields)

/-- The spec's legality statement: every dependency is well-formed on
    the item's fields. -/
def DepSpec.Legal (sp : DepSpec) : Prop :=
  ∀ d ∈ sp.deps, d.onFields sp.fields

/-- THE SPEC-LEVEL BRIDGE: empty diags iff legal (the
    `flatMap`-nil bridge; per-dep facts ride `shapeDiags_nil_iff`). -/
theorem DepSpec.scopedDiags_eq_nil_iff (sp : DepSpec) :
    sp.scopedDiags = [] ↔ sp.Legal := by
  unfold scopedDiags Legal
  rw [List.flatMap_eq_nil_iff]
  constructor
  · intro h d hd
    exact (d.shapeDiags_nil_iff sp.fields).mp (h d hd)
  · intro h d hd
    exact (d.shapeDiags_nil_iff sp.fields).mpr (h d hd)

/-! ## The target correspondence (D20's honest target story) -/

/-- The boundary validator's RUST FACE, rendered from the SAME `Dep`
    data the Lean checker reads (one owner — the emitter consumes THIS;
    never a second table). Per dependency, the check statements of the
    smart constructor `try_new`:
    - `lengthEq c b` — the list's len must equal the count field;
    - `tagMatches t p` — the tag must select the payload's arm.
    The INTEGRATION STEP is named, not landed: `SchemaCore.Emit` grows
    the dependent-record row (the emitted `try_new` + the restricted
    setters) when the Emit lane's wave takes it — Emit/ is a separate
    lane's file this order. -/
def Dep.rustCheck : Dep → String
  | .lengthEq c b =>
      "    if record." ++ b ++ ".len() as u64 != record." ++ c ++ " {\n" ++
      "        return Err(ValidError::LengthMismatch {\n" ++
      "            count: record." ++ c ++ ",\n" ++
      "            got: record." ++ b ++ ".len() as u64,\n" ++
      "        });\n    }\n"
  | .tagMatches t p =>
      "    if (record." ++ t ++ " == 0) != record." ++ p ++ ".is_ok() {\n" ++
      "        return Err(ValidError::TagMismatch {\n" ++
      "            tag: record." ++ t ++ ",\n" ++
      "        });\n    }\n"

/-- The spec's rendered check statements (the smart constructor's
    body, in declaration order — the correspondence's data face). -/
def DepSpec.rustChecks (sp : DepSpec) : String :=
  String.join (sp.deps.map (·.rustCheck))

/-! ## The coverage pins (the fragment reduces — kernel-visible) -/

/-- The Packet fixture's field list (the review's example, at the
    schema level: `length : u64`, `bytes : list u64`, plus the tagged
    pair). -/
def packetFields : List Field :=
  [ { name := "length", ty := .u64 }
  , { name := "bytes", ty := .list .u64 }
  , { name := "tag", ty := .u64 }
  , { name := "result", ty := .result .u64 .string } ]

/-- The Packet spec: the length dependency + the tagged payload. -/
def packetSpec : DepSpec :=
  { item := { name := "Packet", fields := packetFields }
    deps := [ .lengthEq "length" "bytes"
            , .tagMatches "tag" "result" ] }

-- the valid packet: length 2, two bytes, tag 0 with the ok payload
example : Dep.check (.lengthEq "length" "bytes") packetFields
    (.cons (.u64 2) (.cons (.list (.cons (.u64 7) (.cons (.u64 9) .nil)))
      (.cons (.u64 0) (.cons (.ok (.u64 1)) .nil)))) = true := rfl

-- the MISMATCHED packet: length says 2, bytes carries 3 — refuses
example : Dep.check (.lengthEq "length" "bytes") packetFields
    (.cons (.u64 2) (.cons (.list (.cons (.u64 7) (.cons (.u64 9)
      (.cons (.u64 3) .nil))))
      (.cons (.u64 0) (.cons (.ok (.u64 1)) .nil)))) = false := rfl

-- the tagged payload: tag 1 must carry the err arm
example : Dep.check (.tagMatches "tag" "result") packetFields
    (.cons (.u64 2) (.cons (.list .nil)
      (.cons (.u64 1) (.cons (.err (.string "no")) .nil)))) = true := rfl
example : Dep.check (.tagMatches "tag" "result") packetFields
    (.cons (.u64 2) (.cons (.list .nil)
      (.cons (.u64 1) (.cons (.ok (.u64 1)) .nil)))) = false := rfl
-- a tag outside {0,1} refuses (the enum dependency's gate)
example : Dep.check (.tagMatches "tag" "result") packetFields
    (.cons (.u64 2) (.cons (.list .nil)
      (.cons (.u64 7) (.cons (.ok (.u64 1)) .nil)))) = false := rfl

-- the legality discipline: the Packet spec is legal, diags empty
example : packetSpec.scopedDiags = [] := rfl
example : packetSpec.Legal := (packetSpec.scopedDiags_eq_nil_iff).mp rfl

-- a spec naming an ABSENT field: the diags carry it as data
example : ({ packetSpec with
    deps := [.lengthEq "nolength" "bytes"] }).scopedDiags
  = ["field `nolength` is not on record — the length dependency's \
      count field must be a declared field"] := rfl

-- a spec with a MISTYPED payload field (u64, not a result): refused
example : ({ packetSpec with
    deps := [.tagMatches "tag" "length"] }).scopedDiags
  = ["field `length` must be a result (got u64)"] := rfl

end SchemaCore
