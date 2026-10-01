/-
# Query.TypedBridge — the Q ↔ Typed.Schema bridge + the project-covering lowering

Owned by: the qlang-foundation agent (the mandate tree; the design note
`notes/design-forward-surface.md` §3 is the spec of record).

THE BRIDGE (§3.3's gap, landed): the query lane's schemas are
`List Field` (name × ty); the substrait typed layer's are
`Schema = List Col` (name × ty × nullable). ONE crossing, graded
honestly (`Kit.Correspondence`'s vocabulary — the legacy one-ended
`PartialIso` is v3's `Retraction`/`Codec`):

- **Field → Col: `Kit.Retraction`** (`fieldColRetract`). The emb pins
  the nullability bit to `false` (the query lane's rows carry no NULLs
  — the nullability-face note); the inverse recovers only (name, ty) —
  the bit is NOT recoverable, so the round trip `inv ∘ emb = id` is the
  STRONGEST honest law. The image (the non-nullable columns) is a TRUE
  `Iso` (`Retraction.toImageIso` — cited, the grade's own upgrade).
- **RowVals → Typed.Row: `Kit.Codec`** (`rowCodec`). The encode is
  total (every cell `some`); the decode refuses any NULL cell (the
  nullability face at runtime) — `decode ∘ encode = id` plus the
  exact-image policy (`decode a = some b → a = encode b`, proved by
  induction, so `decode_some_policy` holds with the policy = the image).

THE LOWERING (§3.2's `qToRel`): `Q fs gs` lowers to
`Substrait.Typed.Rel (fieldsSchema fs) (fieldsSchema gs)` for the
`table` / `select` / `project` / `union` arms, with the FULL `Pred`
fragment lowered to `Expr` (`predToExpr` — the atoms resolve by-name
through `resolveCol`, first-name-match, the refusal reading preserved;
the comparisons ride `evalFunc`'s bridge kernels). The agreement — the
duel of design-forward-surface §3.2 — is the THEOREM SET:

- `qEval_sound`: every row the substrait evaluator produces decodes to
  a `QSat` row (the evaluator never invents rows outside the spec);
- `qEval_complete`: every `QSat` row's typed image is produced;
- `qEval_agree_iff`: both directions — the two evaluators agree at the
  set level over Bool weights (`evalQ_true_iff` is the lift).

THE TWO NAMED WALLS — BOTH DISSOLVED (the keep witness's pattern
applied twice; the residue lives in the named narrowings):

- **`project` DISSOLVED**: `Substrait.Typed` grew `Rel.keep` — the
  DROP projection (the caller-spelled output schema tied to the input
  by the `Sublist` proof). The design choice: the PROOF-TIED spelling,
  not a rel-term schema cast — the output index is the spelled term
  (the bridge's `fieldsSchema (c.fields gs)`, defeq with the Q
  fragment's own computation), never a transport, so `evalRel`'s
  definitional match reductions survive (the wall's teeth). The
  keep-pick bridge is `toTypedRow_keep`: over the bridged schemas the
  typed keep-walk IS the query lane's `Cols.pick`. The co-requisite
  was the v2 `Cols` redesign (order-preserving keep/skip per position
  — the old positional-`Fin` shape made the agreement undemonstrable
  without demotion casts). A REORDERING projection is the named
  narrowing (the wire's project node appends; the emit lane's
  spelling); `colsSub` is total, the narrowing lives in the SURFACE's
  elaboration (Query.QLang's QL0004), not in a partial bridge.
- **`join` DISSOLVED (the wave-30 F2 disposition)**: the two defeat
  attempts named the wall precisely — (a) `Typed.Rel.join` reads a
  DOUBLED stream (the reader-splitting convention); (b) the schema
  mismatch `fieldsSchema ga ++ fieldsSchema gb` vs `fieldsSchema
  (ga ++ gb)` is NOT defeq, so a lowering through the doubled-stream
  join needs a rel-term schema cast, killing `evalRel`'s definitional
  reductions. The dissolve: `Substrait.Typed` grew `Rel.join'` — the
  SHARED-BASE join (both children read the SAME stream, the query
  lane's reading) whose output index is the CALLER'S SPELLING carried
  by the concatenation witness `AppendCols` (the Keep pattern's data
  face — never a transport; the evaluator's walk is `Row.appendW`,
  and its bridge is `appendW_colsAppend`: the walked pair IS the
  query lane's joined row's typed image). The join condition is BUILT
  (`joinCond`: the left key resolved in the LEFT schema, the right in
  the RIGHT, at the common first-name-match type, lifted by
  `HasCol.atLeft`/`atRight` — the type disagreement IS the resolution
  failure, no transport) and its agreement is `joinCond_ok` (the
  built condition evaluates to exactly `onEq`'s verdict). The pair
  walk's completeness (`evalJoinPairs_ok_complete`) landed as the
  mirror of the seed's soundness pin. The dissolve's residue (QL0001,
  the named narrowings): an unresolvable key column, a key type the
  two sides disagree on, and a key type outside the comparison-kernel
  fragment (u64, string — the same atoms `Pred` compares); the INNER
  reading only (the Q equijoin is the inner join; the outer rows'
  padding is the named follow-up); and the WIRE spelling (the emit
  lane ports with its consumer — the keep precedent).

THE qlang! SURFACE (landed, `Query.QLang`): the term-elab macro
elaborates the Lean-embedded pipeline directly to the typed `Q` —
`HasCol`-style by-name resolution at ELABORATION time (a mis-typed
query refuses with a structured `Kit.Diag`, the QL family's E-codes),
the result-schema typing free (the `Q` index). The bridge here is the
macro's semantic consumer (`qToRel` + the agreement theorems).

The five questions (notes/v3/01-core.md):
- **Root**: Universe × Interpretation — the typed fragment's TWO
  executable readings (the query lane's `evalQ`, the typed layer's
  `evalRel`) pinned to one spec (`QSat`).
- **Carrier grade**: the crossings graded (`Retraction` schema,
  `Codec` rows) — the agreement is the engine-grade statement, both
  directions, no grade inflation.
- **Spine reading**: the typed layer's spine (Typed → Proto/Text/Eval)
  gains a query-lane FEEDER; nothing emitted here.
- **Ladder rung**: hand theorems of the small kind — the per-primitive
  predicate row (`predToExpr_ok`), the column-read row
  (`typedGet_project`), the keep-pick bridge (`toTypedRow_keep`), the
  agreement inductions.
- **Gate rows**: the axiom report + QueryTests' bridge suite (the
  round-trip teeth, the agreement pins, the refusal negative controls)
  + SubstraitTests' kernel pins; the Axioms files pin `#print axioms`.

Cone: imports Query.Eval + Substrait.Typed/Eval (core-only — the cone
rule; the Query → Substrait edge is the bridge itself, no cycle) +
Kit.Diag (the E-code envelope; the Effects precedent).
-/

import Query.Eval
import Substrait.Typed
import Substrait.Eval
import Kit.Diag

namespace Query

open SchemaCore Substrait.Typed ZSet

/-! ## The field ↔ column crossing (Retraction grade) -/

/-- The field's column face: the nullability bit pinned to `false` —
    the query lane's rows carry no NULLs (the nullability-face note,
    design note §3.3). -/
def fieldToCol (f : Field) : Col := (f.name, f.ty, false)

/-- The column's field face: only (name, ty) recover — the nullability
    bit is NOT (the honest gap that makes this a `Retraction`). -/
def colToField (c : Col) : Field := { name := c.1, ty := c.2.1 }

/-- THE SCHEMA CROSSING, `Retraction` grade: `colToField (fieldToCol f)
    = f` (the one round trip); the inverse direction loses the bit. -/
def fieldColRetract : Kit.Retraction Field Col where
  emb := fieldToCol
  inv := colToField
  inv_emb := fun _ => rfl

/-- The image face: ON the bridge's image (the non-nullable columns)
    the crossing is a TRUE `Iso` — the grade's own upgrade
    (`Retraction.toImageIso`), cited, not re-proved. -/
def fieldColImageIso : Kit.Iso fieldColRetract.image Field :=
  fieldColRetract.toImageIso

/-! ## The schema bridge -/

/-- THE SCHEMA BRIDGE: fields → columns, positionally (map — order and
    length preserved by construction). -/
def fieldsSchema : List Field → Schema := List.map fieldToCol

theorem fieldsSchema_cons (f : Field) (fs : List Field) :
    fieldsSchema (f :: fs) = (f.name, f.ty, false) :: fieldsSchema fs := rfl

theorem fieldsSchema_app (a b : List Field) :
    fieldsSchema (a ++ b) = fieldsSchema a ++ fieldsSchema b := by
  simp only [fieldsSchema]
  exact List.map_append

theorem fieldsSchema_length (fs : List Field) :
    (fieldsSchema fs).length = fs.length := by
  simp only [fieldsSchema, List.length_map]

/-! ## The row bridge (Codec grade) -/

/-- The row's encode face: query-lane values → typed cells, every cell
    `some` (the required-column discipline of `fieldToCol`). -/
def toTypedRow : (fs : List Field) → RowVals fs → Substrait.Typed.Row (fieldsSchema fs)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (some v) (toTypedRow _ vs)

/-- The row's decode face: all-`some` cells → the query row; any NULL
    cell refuses (`none` — the nullability face at runtime, the
    honest partiality that keeps this a `Codec`, not an `Iso`). -/
def typedRowToVals : (fs : List Field) → Substrait.Typed.Row (fieldsSchema fs) →
    Option (RowVals fs)
  | [], .nil => some .nil
  | _ :: _, .cons none _ => none
  | _ :: _, .cons (some v) vs => (typedRowToVals _ vs).map (RowVals.cons v)

/-- THE ROUND TRIP (the Codec's `decode_encode`): the decode of the
    encode is the identity. -/
theorem toTypedRow_round : ∀ (fs : List Field) (r : RowVals fs),
    typedRowToVals fs (toTypedRow fs r) = some r := by
  intro fs
  induction fs with
  | nil => intro r; cases r; rfl
  | cons f fs' ih =>
      intro r
      cases r with
      | cons v vs =>
          show (typedRowToVals fs' (toTypedRow fs' vs)).map (RowVals.cons v)
            = some (RowVals.cons v vs)
          rw [ih vs]
          rfl

/-- The decode is EXACT: a successful decode's answer encodes back to
    the input row (the image policy's content — `decode_some_policy`'s
    strong face). -/
theorem typedRowToVals_exact : ∀ (fs : List Field)
    (a : Substrait.Typed.Row (fieldsSchema fs)) (b : RowVals fs),
    typedRowToVals fs a = some b → toTypedRow fs b = a := by
  intro fs
  induction fs with
  | nil =>
      intro a b h
      cases a
      cases h
      rfl
  | cons f fs' ih =>
      intro a b h
      cases a with
      | cons cell rest =>
          cases cell with
          | none =>
              have hred : typedRowToVals (f :: fs')
                  (Substrait.Typed.Row.cons none rest) = none := rfl
              rw [hred] at h
              exact absurd h (by simp)
          | some v =>
              cases b with
              | cons w ws =>
                  have hred : typedRowToVals (f :: fs')
                      (Substrait.Typed.Row.cons (some v) rest)
                      = (typedRowToVals fs' rest).map (RowVals.cons v) := rfl
                  rw [hred, Option.map_eq_some_iff] at h
                  obtain ⟨b', hb, hbe⟩ := h
                  have hveq : v = w := (RowVals.cons_inj hbe).1
                  have hws : b' = ws := (RowVals.cons_inj hbe).2
                  subst hveq
                  subst hws
                  show Substrait.Typed.Row.cons (some v) (toTypedRow fs' b') = _
                  rw [ih rest b' hb]
                  rfl

/-- THE ROW CODEC, `Codec` grade: encode total, decode partial on the
    NULL face, the policy = the image, decode-exactness proved. -/
def rowCodec (fs : List Field) :
    Kit.Codec (Substrait.Typed.Row (fieldsSchema fs)) (RowVals fs) where
  encode := toTypedRow fs
  decode := typedRowToVals fs
  policy a := ∃ r : RowVals fs, toTypedRow fs r = a
  decode_encode := toTypedRow_round fs
  decode_some_policy := fun _ _ h => ⟨_, typedRowToVals_exact fs _ _ h⟩

/-- The encode is injective (the round trip's corollary — the bridge
    never conflates rows). -/
theorem toTypedRow_inj {fs : List Field} {r1 r2 : RowVals fs}
    (h : toTypedRow fs r1 = toTypedRow fs r2) : r1 = r2 := by
  have h1 := toTypedRow_round fs r1
  rw [h] at h1
  have h2 := toTypedRow_round fs r2
  rw [h1] at h2
  exact Option.some.inj h2

/-! ## The by-name column resolution (the first-name-match discipline) -/

/-- The by-name column resolver over a schema: FIRST name-match decides
    (the query lane's `RowVals.project?` discipline), then the type and
    nullability must match. A miss or mismatch is `none` — the
    lowering's refusal face (never a fabricated comparison). -/
def resolveCol : (s : Schema) → (name : String) → (t : Ty) → (n : Bool) →
    Option (HasCol s name t n)
  | [], _, _, _ => none
  | (name', t', n') :: rest, name, t, n =>
      if h1 : name' = name then
        if h2 : t' = t ∧ n' = n then
          some { index := 0, resolves := by simp only [Schema.get?, ← h1, ← h2.1, ← h2.2] }
        else none
      else
        match resolveCol rest name t n with
        | some h => some { index := h.index + 1, resolves := h.resolves }
        | none => none

/-- THE ONE RESOLVER's data walk (the ordinal face, type-erased): the
    FIRST name-match decides — its ordinal, type, and nullability. The
    dependent resolver above is this walk WITH the type-checked index:
    a name match DECIDES (the type/nullability check is the refusal
    gate at that ordinal, never a keep-searching), so `resolveCol`'s
    index field IS this walk's ordinal (`resolveCol_index_colWalk?`).
    The two data spellings consume the walk directly, never a
    re-spelled recursion: the QLang face (`QLang.findCol` — the
    elaboration-time ordinal + type) and the join-key spelling
    (`fieldTy?` — the lowering's type lookup). One resolver, three
    faces, zero re-walks. -/
def colWalk? : Schema → String → Option (Nat × Ty × Bool)
  | [], _ => none
  | (name', t', n') :: rest, name =>
      if name' = name then some (0, t', n')
      else (colWalk? rest name).map (fun p => (p.1 + 1, p.2.1, p.2.2))

/-- THE ORDINAL TIE (the derivation witness): whenever the dependent
    resolver discharges at `hc`, the data walk returns the SAME ordinal
    and the SAME (type, nullability) — the index `resolveCol` projects
    is `colWalk?`'s. This is what makes the three faces ONE resolver:
    the data spellings cannot drift off the dependent walk's ordinals. -/
theorem resolveCol_index_colWalk? :
    ∀ (s : Schema) (name : String) (t : Ty) (n : Bool)
        (hc : HasCol s name t n),
      resolveCol s name t n = some hc →
      colWalk? s name = some (hc.index, t, n) := by
  intro s
  induction s with
  | nil =>
      intro name t n hc h
      exact absurd h (by simp [resolveCol])
  | cons c rest ih =>
      intro name t n hc h
      simp only [resolveCol] at h
      split at h
      · next h1 =>
          split at h
          · next h2 =>
              injection h with hEq
              have hi : hc.index = 0 := by rw [← hEq]; rfl
              simp only [colWalk?]
              rw [if_pos h1, hi]
              exact congrArg _ (by simp [h2.1, h2.2])
          · exact absurd h (by simp)
      · next h1 =>
          split at h
          · next h' heq =>
              injection h with hEq
              have hi : hc.index = h'.index + 1 := by rw [← hEq]; rfl
              simp only [colWalk?]
              rw [if_neg h1, hi, ih name t n h' heq]
              rfl
          · exact absurd h (by simp)

/-- THE COLUMN-READ ROW: a bridged resolution reads the typed row at
    exactly the query lane's projected value — the field read's
    agreement, first-name-match to first-name-match (this is what the
    lowering's `HasCol` proofs BUY the agreement theorem: the read's
    type is proved, and its VALUE is the projected one). -/
theorem typedGet_project : ∀ (fs : List Field) (row : RowVals fs) (n : String)
    (t : Ty) (hc : HasCol (fieldsSchema fs) n t false),
    resolveCol (fieldsSchema fs) n t false = some hc →
    ∃ v : Value t, (toTypedRow fs row).get hc.index = some (Sigma.mk t (some v))
      ∧ RowVals.project? fs row n = some { ty := t, val := v } := by
  intro fs
  induction fs with
  | nil =>
      intro row n t hc h
      have hnone : resolveCol (fieldsSchema ([] : List Field)) n t false = none := rfl
      rw [hnone] at h
      exact absurd h (by simp)
  | cons f fs' ih =>
      intro row n t hc h
      cases row with
      | cons v rest =>
          -- the schema bridge's cons face is definitional: the
          -- resolution's cons-unfolding is read off the EXPLICIT-ctor
          -- schema (the congruence pattern — never a dependent rewrite
          -- through the GADT hypothesis)
          have hEq0 : resolveCol ((f.name, f.ty, false) :: fieldsSchema fs') n t false
              = some hc := h
          simp only [resolveCol] at hEq0
          split at hEq0
          · next h1 =>
              split at hEq0
              · next h2 =>
                  injection hEq0 with hcin
                  cases hcin
                  have hty : f.ty = t := h2.1
                  subst hty
                  refine ⟨v, ?_, ?_⟩
                  · rfl
                  · simp only [RowVals.project?]
                    rw [if_pos (show (f.name == n) = true from
                      beq_iff_eq.mpr h1)]
              · simp at hEq0
          · next h1 =>
              cases hrc2 : resolveCol (fieldsSchema fs') n t false with
              | none =>
                  rw [hrc2] at hEq0
                  simp at hEq0
              | some hcol' =>
                  rw [hrc2] at hEq0
                  simp only [] at hEq0
                  cases hEq0
                  obtain ⟨v', hget, hproj⟩ := ih rest n t hcol' hrc2
                  refine ⟨v', ?_, ?_⟩
                  · exact hget
                  · simp only [RowVals.project?]
                    rw [if_neg (show ¬((f.name == n) = true) from
                      fun hc' => h1 (beq_iff_eq.mp hc'))]
                    exact hproj

/-! ## The predicate lowering -/

/-- The comparison signatures (one NAME per argument type — the
    dispatch is injective in the compared columns' type, so a
    mixed-type comparison cannot share a kernel). -/
def u64EqSig : FunctionSig :=
  { name := "u64equal", args := [(.u64, false), (.u64, false)]
  , ret := .bool, retNullable := false }

def u64GtSig : FunctionSig :=
  { name := "u64gt", args := [(.u64, false), (.u64, false)]
  , ret := .bool, retNullable := false }

def strEqSig : FunctionSig :=
  { name := "strequal", args := [(.string, false), (.string, false)]
  , ret := .bool, retNullable := false }

def andSig : FunctionSig :=
  { name := "and", args := [(.bool, false), (.bool, false)]
  , ret := .bool, retNullable := false }

def orSig : FunctionSig :=
  { name := "or", args := [(.bool, false), (.bool, false)]
  , ret := .bool, retNullable := false }

def notSig : FunctionSig :=
  { name := "not", args := [(.bool, false)]
  , ret := .bool, retNullable := false }

/-- THE PREDICATE LOWERING: `Pred fs` → a typed Bool expression over
    the bridged schema. Except-valued: a column that does not resolve
    (first-name-match + type) REFUSES the query — the query lane's
    checker returns `false` for the same row; the lowering refuses
    the QUERY (the refusal reading, never a fabricated comparison). -/
def predToExpr {fs : List Field} (p : Pred fs) :
    Except String (Expr (fieldsSchema fs) .bool false) :=
  match p with
  | .lit b => .ok (.literal false (.bool b))
  | .u64EqLit n v =>
      match resolveCol (fieldsSchema fs) n .u64 false with
      | some h => .ok (Expr.call u64EqSig (Args.cons .u64 false
          (Expr.field n .u64 false h)
          (Args.cons .u64 false (.literal false (.u64 v)) Args.nil)))
      | none => .error s!"typed-bridge: column {n} : u64 does not resolve (the refusal reading)"
  | .u64GtLit n v =>
      match resolveCol (fieldsSchema fs) n .u64 false with
      | some h => .ok (Expr.call u64GtSig (Args.cons .u64 false
          (Expr.field n .u64 false h)
          (Args.cons .u64 false (.literal false (.u64 v)) Args.nil)))
      | none => .error s!"typed-bridge: column {n} : u64 does not resolve (the refusal reading)"
  | .u64Eq a b =>
      match resolveCol (fieldsSchema fs) a .u64 false,
            resolveCol (fieldsSchema fs) b .u64 false with
      | some ha, some hb => .ok (Expr.call u64EqSig (Args.cons .u64 false
          (Expr.field a .u64 false ha)
          (Args.cons .u64 false (Expr.field b .u64 false hb) Args.nil)))
      | _, _ => .error "typed-bridge: a u64 column does not resolve (the refusal reading)"
  | .strEqLit n s =>
      match resolveCol (fieldsSchema fs) n .string false with
      | some h => .ok (Expr.call strEqSig (Args.cons .string false
          (Expr.field n .string false h)
          (Args.cons .string false (.literal false (.string s)) Args.nil)))
      | none => .error s!"typed-bridge: column {n} : string does not resolve (the refusal reading)"
  | .and p q =>
      match predToExpr p, predToExpr q with
      | .ok ep, .ok eq => .ok (Expr.call andSig (Args.cons .bool false ep
          (Args.cons .bool false eq Args.nil)))
      | .error e, _ => .error e
      | _, .error e => .error e
  | .or p q =>
      match predToExpr p, predToExpr q with
      | .ok ep, .ok eq => .ok (Expr.call orSig (Args.cons .bool false ep
          (Args.cons .bool false eq Args.nil)))
      | .error e, _ => .error e
      | _, .error e => .error e
  | .not p =>
      match predToExpr p with
      | .ok ep => .ok (Expr.call notSig (Args.cons .bool false ep Args.nil))
      | .error e => .error e

/-! ## The bridge kernels' equations (the small faces the agreement
     reads; each `rfl` — the plain-match discipline) -/

theorem evalFunc_u64equal (x y : UInt64) :
    evalFunc u64EqSig [Sigma.mk .u64 (some (Value.u64 x)),
                       Sigma.mk .u64 (some (Value.u64 y))]
      = .ok (some (Value.bool (x == y))) := rfl

theorem evalFunc_u64gt (x y : UInt64) :
    evalFunc u64GtSig [Sigma.mk .u64 (some (Value.u64 x)),
                       Sigma.mk .u64 (some (Value.u64 y))]
      = .ok (some (Value.bool (u64gt x y))) := rfl

theorem evalFunc_strequal (x y : String) :
    evalFunc strEqSig [Sigma.mk .string (some (Value.string x)),
                       Sigma.mk .string (some (Value.string y))]
      = .ok (some (Value.bool (x == y))) := rfl

theorem evalFunc_and (b1 b2 : Bool) :
    evalFunc andSig [Sigma.mk .bool (some (Value.bool b1)),
                     Sigma.mk .bool (some (Value.bool b2))]
      = .ok (some (Value.bool (b1 && b2))) := rfl

theorem evalFunc_or (b1 b2 : Bool) :
    evalFunc orSig [Sigma.mk .bool (some (Value.bool b1)),
                    Sigma.mk .bool (some (Value.bool b2))]
      = .ok (some (Value.bool (b1 || b2))) := rfl

theorem evalFunc_not (b : Bool) :
    evalFunc notSig [Sigma.mk .bool (some (Value.bool b))]
      = .ok (some (Value.bool (!b))) := rfl

/-- The checker's u64 bind, reduced (the projected `some` cell's
    reading — `FieldVal.u64?`'s constructor face). -/
theorem bind_u64?_some (v : UInt64) :
    (some (FieldVal.mk .u64 (.u64 v))).bind FieldVal.u64? = some v := rfl

/-- The checker's string bind, reduced. -/
theorem bind_str?_some (s : String) :
    (some (FieldVal.mk .string (.string s))).bind FieldVal.str? = some s := rfl

/-- THE PREDICATE ROW (the per-primitive agreement): a lowered
    predicate evaluates over the bridged row to exactly the query
    lane's `check` verdict — the kernels and the checker read the SAME
    projected value (`typedGet_project`), decide the SAME comparison.
    Both faces ride the ENGINE's equations (`Expr.evalCell`,
    `Args.eval`, `evalFunc`) — never a hand induction over the
    expression structure (the engine covers it; cost/Expr +
    Analysis.Checker are the precedents). -/
theorem predToExpr_ok {fs : List Field} (p : Pred fs) :
    ∀ (e : Expr (fieldsSchema fs) .bool false), predToExpr p = .ok e →
    ∀ (row : RowVals fs),
      e.evalCell (toTypedRow fs row) = .ok (some (.bool (p.check row))) := by
  induction p with
  | lit b =>
      intro e h row
      simp only [predToExpr, Except.ok.injEq] at h
      obtain rfl := h
      rfl
  | u64EqLit n v =>
      intro e h row
      simp only [predToExpr] at h
      cases hrc : resolveCol (fieldsSchema fs) n .u64 false with
      | none => rw [hrc] at h; simp at h
      | some hcol =>
          rw [hrc] at h
          simp only [] at h
          obtain rfl := Except.ok.inj h
          obtain ⟨x, hget, hproj⟩ := typedGet_project fs row n .u64 hcol hrc
          cases x with
          | u64 x0 =>
              simp only [Pred.check, hproj, bind_u64?_some,
                Expr.evalCell, Args.eval, hget, castVal_self, evalFunc_u64equal]
              rfl
  | u64GtLit n v =>
      intro e h row
      simp only [predToExpr] at h
      cases hrc : resolveCol (fieldsSchema fs) n .u64 false with
      | none => rw [hrc] at h; simp at h
      | some hcol =>
          rw [hrc] at h
          simp only [] at h
          obtain rfl := Except.ok.inj h
          obtain ⟨x, hget, hproj⟩ := typedGet_project fs row n .u64 hcol hrc
          cases x with
          | u64 x0 =>
              simp only [Pred.check, hproj, bind_u64?_some,
                Expr.evalCell, Args.eval, hget, castVal_self, evalFunc_u64gt]
              rfl
  | u64Eq a b =>
      intro e h row
      simp only [predToExpr] at h
      cases ha : resolveCol (fieldsSchema fs) a .u64 false with
      | none => rw [ha] at h; simp at h
      | some hcolA =>
          rw [ha] at h
          cases hb : resolveCol (fieldsSchema fs) b .u64 false with
          | none => rw [hb] at h; simp at h
          | some hcolB =>
              rw [hb] at h
              simp only [] at h
              obtain rfl := Except.ok.inj h
              obtain ⟨x, hgetA, hprojA⟩ := typedGet_project fs row a .u64 hcolA ha
              obtain ⟨y, hgetB, hprojB⟩ := typedGet_project fs row b .u64 hcolB hb
              cases x with
              | u64 x0 =>
                  cases y with
                  | u64 y0 =>
                      simp only [Pred.check, hprojA, hprojB, bind_u64?_some,
                        Expr.evalCell, Args.eval, hgetA, hgetB, castVal_self,
                        evalFunc_u64equal]
                      rfl
  | strEqLit n s =>
      intro e h row
      simp only [predToExpr] at h
      cases hrc : resolveCol (fieldsSchema fs) n .string false with
      | none => rw [hrc] at h; simp at h
      | some hcol =>
          rw [hrc] at h
          simp only [] at h
          obtain rfl := Except.ok.inj h
          obtain ⟨x, hget, hproj⟩ := typedGet_project fs row n .string hcol hrc
          cases x with
          | string x0 =>
              simp only [Pred.check, hproj, bind_str?_some,
                Expr.evalCell, Args.eval, hget, castVal_self, evalFunc_strequal]
              rfl
  | and p q ihp ihq =>
      intro e h row
      simp only [predToExpr] at h
      cases hp : predToExpr p with
      | error ee => rw [hp] at h; simp at h
      | ok ep =>
          rw [hp] at h
          cases hq2 : predToExpr q with
          | error ee => rw [hq2] at h; simp at h
          | ok eq' =>
              rw [hq2] at h
              simp only [] at h
              obtain rfl := Except.ok.inj h
              have h1 : Expr.evalCell ep (toTypedRow fs row)
                  = .ok (some (Value.bool (p.check row))) := ihp ep hp row
              have h2 : Expr.evalCell eq' (toTypedRow fs row)
                  = .ok (some (Value.bool (q.check row))) := ihq eq' hq2 row
              simp only [Pred.check, Expr.evalCell, Args.eval, h1, h2, evalFunc_and]
              rfl
  | or p q ihp ihq =>
      intro e h row
      simp only [predToExpr] at h
      cases hp : predToExpr p with
      | error ee => rw [hp] at h; simp at h
      | ok ep =>
          rw [hp] at h
          cases hq2 : predToExpr q with
          | error ee => rw [hq2] at h; simp at h
          | ok eq' =>
              rw [hq2] at h
              simp only [] at h
              obtain rfl := Except.ok.inj h
              have h1 : Expr.evalCell ep (toTypedRow fs row)
                  = .ok (some (Value.bool (p.check row))) := ihp ep hp row
              have h2 : Expr.evalCell eq' (toTypedRow fs row)
                  = .ok (some (Value.bool (q.check row))) := ihq eq' hq2 row
              simp only [Pred.check, Expr.evalCell, Args.eval, h1, h2, evalFunc_or]
              rfl
  | not p ihp =>
      intro e h row
      simp only [predToExpr] at h
      cases hp : predToExpr p with
      | error ee => rw [hp] at h; simp at h
      | ok ep =>
          rw [hp] at h
          simp only [] at h
          obtain rfl := Except.ok.inj h
          have h1 : Expr.evalCell ep (toTypedRow fs row)
              = .ok (some (Value.bool (p.check row))) := ihp ep hp row
          simp only [Pred.check, Expr.evalCell, Args.eval, h1, evalFunc_not]
          rfl

/-! ## The join refusals (the wall-2 dissolve's named narrowings) -/

/-- The QL family — the qlang/bridge E-codes, allocated from the
    PERSISTED registry (`notes/code-registry.txt`, the spec of record).
    The bridge's site is QL0001; the surface's are QLang's (QL0002–
    QL0005). The constants are the family's DECLARATION — the sites use
    them, never a bare string, and the code-registry gate's coverage
    scan ties every spelling to its allocated live row. -/
def eQL0001 : Kit.ECode := ⟨"QL0001"⟩

/-- THE JOIN KEY REFUSALS (the wall-2 dissolve's residue): the shared-
    base join (`Typed.Rel.join'`) lowers the equijoin itself; what still
    refuses is the KEY — a key column that does not resolve
    (first-name-match, per side), a key type the two sides disagree on,
    or a key type outside the comparison-kernel fragment (u64, string —
    the same atoms `Pred` compares; the bool/i64 kernel rows port with
    their consumer). Rendered through the one Diag envelope. -/
def joinKeyRefusal (why : String) : String :=
  Kit.Diag.toString
    { code := eQL0001
      message := s!"typed-bridge: the equijoin's key refuses — {why}"
      severity := .error }

/-! ## The join lowering (wall 2's dissolve) -/

/-- The key column's type lookup (first-name-match — the query lane's
    `RowVals.project?` discipline at the lowering): the ONE resolver's
    data walk (`colWalk?`), the type projection — never a re-spelled
    recursion (the ordinal-tie theorem keeps it off `resolveCol`'s
    index). -/
def fieldTy? (fs : List Field) (n : String) : Option Ty :=
  (colWalk? (fieldsSchema fs) n).map (fun p => p.2.1)

/-- The appended output schema's canonical concatenation witness: the
    equijoin's result schema IS the left bridge's elementwise append of
    the right — total over `ga`, the `(f :: rest) ++ gb` and
    `List.map`-cons reductions carry it definitionally (the Keep-
    witness discipline: the Type-sorted data face, the spelled index —
    never a transport). -/
def colsAppendCols : (ga gb : List Field) →
    AppendCols (fieldsSchema ga) (fieldsSchema gb) (fieldsSchema (ga ++ gb))
  | [], _ => .wnil
  | f :: rest, gb => .wcons (fieldToCol f) (colsAppendCols rest gb)

/-- THE APPEND-WALK BRIDGE (the wall-2 dissolve's teeth — the
    `toTypedRow_keep` sibling): over the canonical witness, the typed
    evaluator's appended-pair re-index IS the query lane's joined row's
    typed image. This is what buys the agreement theorems' join case:
    the walked pair decodes to exactly `QSat.join`'s appended row. NOTE
    the two append faces are NOT defeq — `fieldsSchema ga ++
    fieldsSchema gb` vs `fieldsSchema (ga ++ gb)` is the wall's own
    tooth (the cast this whole dissolve refuses to take) — the WITNESS
    WALK is the honest crossing, exactly the Keep discipline. -/
theorem appendW_colsAppend : ∀ (ga gb : List Field) (la : RowVals ga) (rb : RowVals gb),
    Substrait.Typed.Row.appendW (colsAppendCols ga gb)
        (Substrait.Typed.Row.append (toTypedRow ga la) (toTypedRow gb rb))
      = toTypedRow (ga ++ gb) (Query.Row.append la rb) := by
  intro ga gb
  induction ga with
  | nil => intro la rb; cases la; rfl
  | cons f rest ih =>
      intro la rb
      cases la with
      | cons v vs =>
          show Substrait.Typed.Row.cons (some v)
              (Substrait.Typed.Row.appendW (colsAppendCols rest gb)
                (Substrait.Typed.Row.append (toTypedRow rest vs) (toTypedRow gb rb)))
            = Substrait.Typed.Row.cons (some v)
                (toTypedRow (rest ++ gb) (Query.Row.append vs rb))
          rw [ih vs rb]

/-- A left-schema key read, lifted into the appended pair's row, reads
    the query lane's projected value (`typedGet_project`'s face at the
    left side — the index is unchanged by the left lift). -/
theorem appendPair_get_left {ga gb : List Field} (la : RowVals ga) (rb : RowVals gb)
    (n : String) (t : Ty) (hc : HasCol (fieldsSchema ga) n t false)
    (hrc : resolveCol (fieldsSchema ga) n t false = some hc) :
    ∃ v : Value t,
      (Substrait.Typed.Row.append (toTypedRow ga la) (toTypedRow gb rb)).get
          (HasCol.atLeft (fieldsSchema ga) hc (fieldsSchema gb)).index
        = some (Sigma.mk t (some v))
      ∧ RowVals.project? ga la n = some { ty := t, val := v } := by
  obtain ⟨v, hget, hproj⟩ := typedGet_project ga la n t hc hrc
  refine ⟨v, ?_, hproj⟩
  rw [HasCol.atLeft_index hc (fieldsSchema gb),
    Substrait.Typed.Row.get_append_left _ _ _ (Schema.get?_lt _ _ _ hc.resolves)]
  exact hget

/-- A right-schema key read, lifted into the appended pair's row, reads
    the query lane's projected value (the right lift's index is the
    left schema's length plus the column's own ordinal). -/
theorem appendPair_get_right {ga gb : List Field} (la : RowVals ga) (rb : RowVals gb)
    (n : String) (t : Ty) (hc : HasCol (fieldsSchema gb) n t false)
    (hrc : resolveCol (fieldsSchema gb) n t false = some hc) :
    ∃ v : Value t,
      (Substrait.Typed.Row.append (toTypedRow ga la) (toTypedRow gb rb)).get
          (HasCol.atRight (fieldsSchema ga) (fieldsSchema gb) hc).index
        = some (Sigma.mk t (some v))
      ∧ RowVals.project? gb rb n = some { ty := t, val := v } := by
  obtain ⟨v, hget, hproj⟩ := typedGet_project gb rb n t hc hrc
  refine ⟨v, ?_, hproj⟩
  rw [HasCol.atRight_index (fieldsSchema ga) hc,
    Substrait.Typed.Row.get_append_right _ _ _]
  exact hget

/-- The shared-key condition's kernel face: the two lifted field reads
    at the COMMON key type — the comparison kernels' dispatch (u64,
    string; any other key type refuses — the comparison-kernel
    fragment's boundary, the named narrowing). One NAME per argument
    type, so the dispatch is injective in the key's type. -/
def joinCondOf {ga gb : List Field} (ln rn : String) :
    (t : Ty) → HasCol (fieldsSchema ga) ln t false →
      HasCol (fieldsSchema gb) rn t false →
      Except String (Expr (fieldsSchema ga ++ fieldsSchema gb) .bool false)
  | .u64, hl, hr =>
      .ok (Expr.call u64EqSig (Args.cons .u64 false
        (Expr.field ln .u64 false (HasCol.atLeft (fieldsSchema ga) hl (fieldsSchema gb)))
        (Args.cons .u64 false
          (Expr.field rn .u64 false (HasCol.atRight (fieldsSchema ga) (fieldsSchema gb) hr))
          Args.nil)))
  | .string, hl, hr =>
      .ok (Expr.call strEqSig (Args.cons .string false
        (Expr.field ln .string false (HasCol.atLeft (fieldsSchema ga) hl (fieldsSchema gb)))
        (Args.cons .string false
          (Expr.field rn .string false (HasCol.atRight (fieldsSchema ga) (fieldsSchema gb) hr))
          Args.nil)))
  | _, _, _ =>
      .error (joinKeyRefusal "the key columns' common type is outside the \
        comparison-kernel fragment (u64, string)")

/-- THE JOIN CONDITION BUILDER (the wall-2 dissolve's face): the
    equijoin's ON as a typed Bool expression over the appended output
    schemas — the left key resolved IN the left schema (lifted left),
    the right key resolved IN the right schema at the LEFT key's type
    (so a type disagreement IS the resolution failure — no transport),
    first-name-match per side. A missing key, a type disagreement, or a
    key type outside the kernel fragment refuses (QL0001 — the named
    narrowing; the query lane's missing-key reading is the no-match
    semantics, the lowering refuses the QUERY — the predToExpr
    discipline). -/
def joinCond (ga gb : List Field) (ln rn : String) :
    Except String (Expr (fieldsSchema ga ++ fieldsSchema gb) .bool false) :=
  match fieldTy? ga ln with
  | some t =>
      match resolveCol (fieldsSchema ga) ln t false with
      | some hl =>
          match resolveCol (fieldsSchema gb) rn t false with
          | some hr => joinCondOf ln rn t hl hr
          | none => .error (joinKeyRefusal "the right key column does not resolve \
            at the left key's type (first-name-match, per side)")
      | none => .error (joinKeyRefusal "the left key column does not resolve \
        at its first-name-match type")
  | none => .error (joinKeyRefusal "the left key column does not resolve \
    at its first-name-match type")

/-- THE JOIN CONDITION ROW (the per-key agreement — `predToExpr_ok`'s
    sibling): the built condition evaluates over the TYPED appended
    pair (the cond's own schema — `l' ++ r'`, the evaluator's pair
    shape) to exactly the query lane's `onEq` verdict — the lifted
    reads and the kernels read the SAME projected values. -/
theorem joinCond_ok {ga gb : List Field} (ln rn : String)
    (la : RowVals ga) (rb : RowVals gb)
    (e : Expr (fieldsSchema ga ++ fieldsSchema gb) .bool false)
    (h : joinCond ga gb ln rn = .ok e) :
    e.evalCell (Substrait.Typed.Row.append (toTypedRow ga la) (toTypedRow gb rb))
      = .ok (some (.bool (onEq ga gb ln rn la rb))) := by
  simp only [joinCond] at h
  cases hf : fieldTy? ga ln with
  | none => rw [hf] at h; simp at h
  | some t =>
      simp only [hf] at h
      cases hrc1 : resolveCol (fieldsSchema ga) ln t false with
      | none => rw [hrc1] at h; simp at h
      | some hl =>
          simp only [hrc1] at h
          cases hrc2 : resolveCol (fieldsSchema gb) rn t false with
          | none => rw [hrc2] at h; simp at h
          | some hr =>
              simp only [hrc2] at h
              cases t with
              | u64 =>
                  simp only [joinCondOf] at h
                  injection h with h'
                  subst h'
                  obtain ⟨a, hgetL, hprojL⟩ :=
                    appendPair_get_left la rb ln .u64 hl hrc1
                  obtain ⟨b, hgetR, hprojR⟩ :=
                    appendPair_get_right la rb rn .u64 hr hrc2
                  cases a with | u64 a0 => cases b with | u64 b0 =>
                  simp only [Expr.evalCell, Args.eval, hgetL, hgetR, castVal_self,
                    evalFunc_u64equal, onEq, hprojL, hprojR]
                  rfl
              | string =>
                  simp only [joinCondOf] at h
                  injection h with h'
                  subst h'
                  obtain ⟨a, hgetL, hprojL⟩ :=
                    appendPair_get_left la rb ln .string hl hrc1
                  obtain ⟨b, hgetR, hprojR⟩ :=
                    appendPair_get_right la rb rn .string hr hrc2
                  cases a with | string a0 => cases b with | string b0 =>
                  simp only [Expr.evalCell, Args.eval, hgetL, hgetR, castVal_self,
                    evalFunc_strequal, onEq, hprojL, hprojR]
                  rfl
              | _ => simp [joinCondOf] at h

/-- The built condition's evaluation is TOTAL over any appended pair
    of the children's rows (the field reads are proved, the kernels
    are total at the two-argument arity) — the refusals live in the
    builder, never in the walk. -/
theorem fieldRead_total {s : Schema} {name : String} {t : Ty} {nul : Bool}
    (hc : HasCol s name t nul) (row : Row s) :
    ∃ v, (Expr.field name t nul hc).evalCell row = .ok v := by
  obtain ⟨c0, hc0⟩ := Substrait.Typed.Row.get_resolves hc row
  cases c0 with
  | none => exact ⟨none, by simp only [Expr.evalCell, hc0]⟩
  | some w => exact ⟨some w, by simp only [Expr.evalCell, hc0, castVal_self]⟩

/-- The comparison kernels are TOTAL at the two-argument arity (the
    binKernel's NULL face — a missing operand is `.ok none`, the SQL
    refusal reading, never an error). -/
theorem evalFunc_u64equal_total (v1 v2 : Option (Value .u64)) :
    ∃ v, evalFunc u64EqSig [Sigma.mk .u64 v1, Sigma.mk .u64 v2] = .ok v := by
  cases v1 with
  | none => exact ⟨none, rfl⟩
  | some w =>
      cases w with
      | u64 x =>
          cases v2 with
          | none => exact ⟨none, rfl⟩
          | some w2 =>
              cases w2 with
              | u64 y => exact ⟨some (Value.bool (x == y)), rfl⟩

theorem evalFunc_strequal_total (v1 v2 : Option (Value .string)) :
    ∃ v, evalFunc strEqSig [Sigma.mk .string v1, Sigma.mk .string v2] = .ok v := by
  cases v1 with
  | none => exact ⟨none, rfl⟩
  | some w =>
      cases w with
      | string x =>
          cases v2 with
          | none => exact ⟨none, rfl⟩
          | some w2 =>
              cases w2 with
              | string y => exact ⟨some (Value.bool (x == y)), rfl⟩

/-- The call-face totality: a call evaluates when the args' spine
    evaluates and the kernel answers (the engine's dispatch — the
    `hfun` hypothesis carries the per-sig face). -/
theorem evalCell_call_total {s : Schema} (sig : FunctionSig)
    (args : Args s sig.args) (row : Row s)
    (hargs : ∃ vs, args.eval row = .ok vs)
    (hfun : ∀ vs, args.eval row = .ok vs → ∃ v, evalFunc sig vs = .ok v) :
    ∃ v, (Expr.call sig args).evalCell row = .ok v := by
  obtain ⟨vs, hvs⟩ := hargs
  have hunfold : (Expr.call sig args).evalCell row
      = match args.eval row with
        | .ok vs' => evalFunc sig vs'
        | .error e => .error e := rfl
  rw [hunfold, hvs]
  exact hfun vs hvs

theorem joinCondOf_evalCell_total {ga gb : List Field} (ln rn : String)
    (t : Ty) (hl : HasCol (fieldsSchema ga) ln t false)
    (hr : HasCol (fieldsSchema gb) rn t false)
    (e : Expr (fieldsSchema ga ++ fieldsSchema gb) .bool false)
    (h : joinCondOf ln rn t hl hr = .ok e)
    (l : Substrait.Typed.Row (fieldsSchema ga))
    (r : Substrait.Typed.Row (fieldsSchema gb)) :
    ∃ v, e.evalCell (Substrait.Typed.Row.append l r) = .ok v := by
  cases t with
  | u64 =>
      simp only [joinCondOf] at h
      injection h with h'
      subst h'
      obtain ⟨v1, hv1⟩ := fieldRead_total
        (HasCol.atLeft (fieldsSchema ga) hl (fieldsSchema gb))
        (Substrait.Typed.Row.append l r)
      obtain ⟨v2, hv2⟩ := fieldRead_total
        (HasCol.atRight (fieldsSchema ga) (fieldsSchema gb) hr)
        (Substrait.Typed.Row.append l r)
      refine evalCell_call_total u64EqSig _ _
        ⟨[Sigma.mk .u64 v1, Sigma.mk .u64 v2], ?_⟩ (fun vs hvs => ?_)
      · simp only [Args.eval, hv1, hv2]
      · simp only [Args.eval, hv1, hv2] at hvs
        injection hvs with hvs'
        subst hvs'
        exact evalFunc_u64equal_total v1 v2
  | string =>
      simp only [joinCondOf] at h
      injection h with h'
      subst h'
      obtain ⟨v1, hv1⟩ := fieldRead_total
        (HasCol.atLeft (fieldsSchema ga) hl (fieldsSchema gb))
        (Substrait.Typed.Row.append l r)
      obtain ⟨v2, hv2⟩ := fieldRead_total
        (HasCol.atRight (fieldsSchema ga) (fieldsSchema gb) hr)
        (Substrait.Typed.Row.append l r)
      refine evalCell_call_total strEqSig _ _
        ⟨[Sigma.mk .string v1, Sigma.mk .string v2], ?_⟩ (fun vs hvs => ?_)
      · simp only [Args.eval, hv1, hv2]
      · simp only [Args.eval, hv1, hv2] at hvs
        injection hvs with hvs'
        subst hvs'
        exact evalFunc_strequal_total v1 v2
  | _ => simp [joinCondOf] at h

/-- The built condition's `condHolds` is total (the totality face the
    join walk's totality consumes). -/
theorem joinCond_holds_total {ga gb : List Field} (ln rn : String)
    (c : Expr (fieldsSchema ga ++ fieldsSchema gb) .bool false)
    (h : joinCond ga gb ln rn = .ok c)
    (l : Substrait.Typed.Row (fieldsSchema ga))
    (r : Substrait.Typed.Row (fieldsSchema gb)) :
    ∃ b, condHolds c l r = .ok b := by
  have hstruct : ∃ (t : Ty) (hl : HasCol (fieldsSchema ga) ln t false)
      (hr : HasCol (fieldsSchema gb) rn t false),
      joinCondOf ln rn t hl hr = .ok c := by
    simp only [joinCond] at h
    cases hf : fieldTy? ga ln with
    | none => rw [hf] at h; simp at h
    | some t =>
        simp only [hf] at h
        cases hrc1 : resolveCol (fieldsSchema ga) ln t false with
        | none => rw [hrc1] at h; simp at h
        | some hl =>
            simp only [hrc1] at h
            cases hrc2 : resolveCol (fieldsSchema gb) rn t false with
            | none => rw [hrc2] at h; simp at h
            | some hr =>
                simp only [hrc2] at h
                cases t with
                | u64 => exact ⟨.u64, hl, hr, h⟩
                | string => exact ⟨.string, hl, hr, h⟩
                | _ => simp [joinCondOf] at h
  obtain ⟨t, hl, hr, hjoin⟩ := hstruct
  obtain ⟨v, hv⟩ := joinCondOf_evalCell_total ln rn t hl hr c hjoin l r
  unfold condHolds
  rw [hv]
  cases v with
  | none => exact ⟨false, rfl⟩
  | some s => cases s with | bool b => exact ⟨b, rfl⟩

/-! ## The keep-pick bridge (the wall-1 dissolve's teeth) -/

/-- The bridged schemas' canonical keep witness: the drop projection's
    keep/skip column data IS an order-preserving subselection of the
    bridged schema — TOTAL over `Cols` (the reordering narrowing lives
    in the surface's elaboration, not here). The WITNESS, not a
    `Sublist` proof: the proof is a proposition whose elimination into
    data is refused — the witness is its data face, and the evaluator
    walks it (`Row.keepW`). -/
def colsKeep : (fs : List Field) → (c : Cols fs) →
    Keep (fieldsSchema fs) (fieldsSchema (c.fields fs))
  | [], .nil => .wnil
  | f :: fs', .keep c => .wkeep (f.name, f.ty, false) (colsKeep fs' c)
  | f :: fs', .skip c => .wdrop (f.name, f.ty, false) (colsKeep fs' c)

/-- THE KEEP-PICK BRIDGE (the wall-1 dissolve's teeth): over the
    bridged schemas, the typed keep-walk IS the query lane's projection
    — one induction, the keep/skip constructors' lockstep. This is what
    buys the agreement theorems' project case: the evaluator's kept row
    decodes to exactly `Cols.pick`'s row. -/
theorem toTypedRow_keep : ∀ (fs : List Field) (c : Cols fs) (r' : RowVals fs),
    Row.keepW (toTypedRow fs r') (colsKeep fs c)
      = toTypedRow (c.fields fs) (c.pick fs r') := by
  intro fs
  induction fs with
  | nil =>
      intro c r'
      cases c
      cases r'
      rfl
  | cons f fs' ih =>
      intro c r'
      cases c with
      | keep c =>
          cases r' with
          | cons v rest =>
              show Row.cons (some v)
                  ((toTypedRow fs' rest).keepW (colsKeep fs' c))
                = Row.cons (some v)
                    (toTypedRow (c.fields fs') (c.pick fs' rest))
              rw [ih c rest]
      | skip c =>
          cases r' with
          | cons v rest =>
              show (toTypedRow fs' rest).keepW (colsKeep fs' c)
                = toTypedRow (c.fields fs') (c.pick fs' rest)
              exact ih c rest

/-! ## The query lowering (the full endo-free fragment) -/

/-- The base table's name in a lowered plan (the query lane's `Q` is
    anonymous over its base rows — the reader is the theorem side's
    binding; the bridge reader responds to every name). -/
def qRelBase : String := "query.base"

/-- THE LOWERING (design note §3.2's `qlangToRel`, now over the FULL
    fragment INCLUDING the equijoin — wall 2's dissolve): the `table` /
    `select` / `project` / `union` arms lower as before; the `join` arm
    lowers to the typed layer's SHARED-BASE JOIN (`Rel.join'` — both
    children read the same stream, the query lane's reading; the output
    index is the caller's spelling carried by the concatenation
    witness `colsAppendCols`, so NO transport). Never lossy, never
    cast: every arm produces a `Rel` whose indices are DEFEQ the
    bridge's schema (the project arm's output index IS the Q fragment's
    own `c.fields gs` computation; the join arm's IS the Q fragment's
    own `fieldsSchema (ga ++ gb)` — the keep-pick discipline), so
    `evalRel`'s definitional reductions survive (06's discipline). The
    join arm's residual refusals are the KEY's (joinKeyRefusal, QL0001:
    unresolvable key, type disagreement, key type outside the
    comparison-kernel fragment — the named narrowings) plus the inner
    reading (the Q fragment's equijoin is the inner join; the outer
    rows' padding is the named follow-up). -/
def qToRel {fs gs : List Field} (q : Q fs gs) :
    Except String (Rel (fieldsSchema fs) (fieldsSchema gs)) :=
  match q with
  | .table => .ok (.read qRelBase (fieldsSchema fs))
  | .select p q' =>
      match qToRel q', predToExpr p with
      | .ok r, .ok pe => .ok (.filter r pe)
      | .error e, _ => .error e
      | _, .error e => .error e
  | .project c q' =>
      match qToRel q' with
      | .ok r => .ok (.keep r (colsKeep _ c))
      | .error e => .error e
  | .union q1 q2 =>
      match qToRel q1, qToRel q2 with
      | .ok r1, .ok r2 => .ok (.set .unionAll r1 r2)
      | .error e, _ => .error e
      | _, .error e => .error e
  | @Q.join _ _ _ ln rn q1 q2 =>
      match qToRel q1, qToRel q2, joinCond _ _ ln rn with
      | .ok r1, .ok r2, .ok c =>
          .ok (.join' r1 r2 (colsAppendCols _ _) c .inner)
      | .error e, _, _ => .error e
      | _, .error e, _ => .error e
      | _, _, .error e => .error e

/-- The bridge reader: responds to EVERY name with the base rows'
    typed images (the lowering emits one fixed name — `qRelBase`; the
    shared-base join feeds BOTH children this reader directly — no
    reader-splitting ever occurs in the lowered fragment). -/
def bridgeReader {fs : List Field} (rows : List (RowVals fs)) :
    Reader (fieldsSchema fs) :=
  fun _ => .ok (rows.map (toTypedRow fs))

/-- The Except-filter's totality: when `f` succeeds on every row, the
    walk succeeds (the refusals live in `f`, never in the walk). -/
theorem filterRowsM_ok_exists {s : Schema} (f : Substrait.Typed.Row s → Except String Bool)
    (rows : List (Substrait.Typed.Row s)) (hf : ∀ x ∈ rows, ∃ b, f x = .ok b) :
    ∃ out, filterRowsM f rows = .ok out := by
  induction rows with
  | nil => exact ⟨[], rfl⟩
  | cons x rest ih =>
      obtain ⟨b, hb⟩ := hf x (by simp)
      obtain ⟨out, hout⟩ := ih (fun y hy => hf y (by simp [hy]))
      rw [filterRowsM, hb]
      cases b with
      | false => exact ⟨out, hout⟩
      | true => refine ⟨x :: out, ?_⟩; rw [hout]

/-- THE AGREEMENT, sound face: every row the substrait evaluator
    produces over a lowered query decodes to a `QSat` row — the
    evaluator never invents rows outside the spec (the refusal
    reading's positive face). -/
theorem qEval_sound {fs : List Field} :
    ∀ (gs : List Field) (q : Q fs gs)
      (rel : Rel (fieldsSchema fs) (fieldsSchema gs)),
    qToRel q = .ok rel →
    ∀ (rows : List (RowVals fs)) (input : Table (fieldsSchema fs))
      (out : Table (fieldsSchema gs)),
    evalRel (bridgeReader rows) rel input = .ok out →
    ∀ r : Substrait.Typed.Row (fieldsSchema gs), r ∈ out →
    ∃ r' : RowVals gs, QSat fs rows q r' ∧ toTypedRow gs r' = r := by
  intro gs q
  induction q with
  | table =>
      intro rel h rows input out hok r hr
      simp only [qToRel] at h
      obtain rfl := Except.ok.inj h
      simp only [evalRel, bridgeReader] at hok
      obtain rfl := Except.ok.inj hok
      obtain ⟨r', hr'in, htr⟩ := List.mem_map.mp hr
      exact ⟨r', QSat.table r' hr'in, htr⟩
  | select p q ih =>
      intro rel h rows input out hok r hr
      simp only [qToRel] at h
      cases hqr : qToRel q with
      | error e => rw [hqr] at h; simp at h
      | ok rq =>
          rw [hqr] at h
          cases hpe : predToExpr p with
          | error e => rw [hpe] at h; simp at h
          | ok pe =>
              rw [hpe] at h
              simp only [Except.ok.injEq] at h
              obtain rfl := h
              simp only [evalRel] at hok
              cases hin : evalRel (bridgeReader rows) rq input with
              | error e => rw [hin] at hok; simp at hok
              | ok in' =>
                  rw [hin] at hok
                  simp only [] at hok
                  obtain ⟨hm, ht⟩ := filterRowsM_ok_sound
                    (fun row => match pe.evalCell row with
                      | .ok (some (.bool b)) => .ok b
                      | .ok _ => .ok false
                      | .error e => .error e) in' out hok r hr
                  obtain ⟨r', hq', htr⟩ := ih rq hqr rows input in' hin r hm
                  refine ⟨r', QSat.select hq' ?_, htr⟩
                  rw [← htr] at ht
                  simpa only [predToExpr_ok p pe hpe r', Except.ok.injEq] using ht
  | project c q ih =>
      intro rel h rows input out hok r hr
      simp only [qToRel] at h
      cases hqr : qToRel q with
      | error e => rw [hqr] at h; simp at h
      | ok rq =>
          rw [hqr] at h
          simp only [Except.ok.injEq] at h
          obtain rfl := h
          simp only [evalRel] at hok
          cases hin : evalRel (bridgeReader rows) rq input with
          | error e => rw [hin] at hok; simp at hok
          | ok in' =>
              rw [hin] at hok
              simp only [Except.ok.injEq] at hok
              obtain rfl := hok
              obtain ⟨r₀, hm, hrEq⟩ := evalKeepW_in (colsKeep _ c) in' r hr
              obtain ⟨r', hq', htr⟩ := ih rq hqr rows input in' hin r₀ hm
              refine ⟨c.pick _ r', QSat.project hq' rfl, ?_⟩
              rw [hrEq, ← htr, toTypedRow_keep]
  | join ln rn q1 q2 ih1 ih2 =>
      intro rel h rows input out hok r hr
      simp only [qToRel] at h
      cases hr1 : qToRel q1 with
      | error e => rw [hr1] at h; simp at h
      | ok r1 =>
          rw [hr1] at h
          cases hr2 : qToRel q2 with
          | error e => rw [hr2] at h; simp at h
          | ok r2 =>
              rw [hr2] at h
              cases hc : joinCond _ _ ln rn with
              | error e => rw [hc] at h; simp at h
              | ok c =>
                  rw [hc] at h
                  simp only [Except.ok.injEq] at h
                  obtain rfl := h
                  simp only [evalRel] at hok
                  cases hin1 : evalRel (bridgeReader rows) r1 input with
                  | error e => rw [hin1] at hok; simp at hok
                  | ok lrows =>
                      rw [hin1] at hok
                      cases hin2 : evalRel (bridgeReader rows) r2 input with
                      | error e => rw [hin2] at hok; simp at hok
                      | ok rrows =>
                          rw [hin2] at hok
                          simp only [evalJoin] at hok
                          cases hp : evalJoinPairs c lrows rrows with
                          | error e => rw [hp] at hok; simp at hok
                          | ok inner =>
                              rw [hp] at hok
                              cases hul : unmatchedLeft c lrows rrows with
                              | error e => rw [hul] at hok; simp at hok
                              | ok ul =>
                                  rw [hul] at hok
                                  cases hur : unmatchedRight c rrows lrows with
                                  | error e => rw [hur] at hok; simp at hok
                                  | ok ur =>
                                      rw [hur] at hok
                                      simp only [Except.ok.injEq] at hok
                                      obtain rfl := hok
                                      obtain ⟨x, hxin, hrx⟩ := List.mem_map.mp hr
                                      obtain ⟨la, rb, hxe, hla, hrb, hcond⟩ :=
                                        evalJoinPairs_ok_sound c lrows rrows inner hp x hxin
                                      obtain ⟨la', hq1, htr1⟩ :=
                                        ih1 r1 hr1 rows input lrows hin1 la hla
                                      obtain ⟨rb', hq2, htr2⟩ :=
                                        ih2 r2 hr2 rows input rrows hin2 rb hrb
                                      have hon : onEq _ _ ln rn la' rb' = true := by
                                        unfold condHolds at hcond
                                        rw [← htr1, ← htr2,
                                          joinCond_ok ln rn la' rb' c hc] at hcond
                                        simpa using hcond
                                      exact ⟨Query.Row.append la' rb',
                                        QSat.join hq1 hq2 hon rfl,
                                        by rw [← hrx, hxe, ← htr1, ← htr2,
                                          appendW_colsAppend]⟩
  | union q1 q2 ih1 ih2 =>
      intro rel h rows input out hok r hr
      simp only [qToRel] at h
      cases hr1 : qToRel q1 with
      | error e => rw [hr1] at h; simp at h
      | ok r1 =>
          rw [hr1] at h
          cases hr2 : qToRel q2 with
          | error e => rw [hr2] at h; simp at h
          | ok r2 =>
              rw [hr2] at h
              simp only [Except.ok.injEq] at h
              obtain rfl := h
              simp only [evalRel] at hok
              cases hl : evalRel (bridgeReader rows) r1 input with
              | error e => rw [hl] at hok; simp at hok
              | ok l =>
                  rw [hl] at hok
                  cases hrr : evalRel (bridgeReader rows) r2 input with
                  | error e => rw [hrr] at hok; simp at hok
                  | ok rr =>
                      rw [hrr] at hok
                      simp only [Except.ok.injEq] at hok
                      obtain rfl := hok
                      rcases List.mem_append.mp hr with hr | hr
                      · obtain ⟨r', hq, htr⟩ := ih1 r1 hr1 rows input l hl r hr
                        exact ⟨r', QSat.unionL hq, htr⟩
                      · obtain ⟨r', hq, htr⟩ := ih2 r2 hr2 rows input rr hrr r hr
                        exact ⟨r', QSat.unionR hq, htr⟩

/-- The lowered fragment's evaluation is TOTAL over the bridge reader:
    the refusals live in the LOWERING, not the evaluation (every
    stream row decodes — soundness — and every kernel resolves). -/
theorem qEval_total {fs : List Field} :
    ∀ (gs : List Field) (q : Q fs gs)
      (rel : Rel (fieldsSchema fs) (fieldsSchema gs)),
    qToRel q = .ok rel →
    ∀ (rows : List (RowVals fs)) (input : Table (fieldsSchema fs)),
    ∃ out, evalRel (bridgeReader rows) rel input = .ok out := by
  intro gs q
  induction q with
  | table =>
      intro rel h rows input
      simp only [qToRel] at h
      obtain rfl := Except.ok.inj h
      exact ⟨_, rfl⟩
  | @select g p q ih =>
      intro rel h rows input
      simp only [qToRel] at h
      cases hqr : qToRel q with
      | error e => rw [hqr] at h; simp at h
      | ok rq =>
          rw [hqr] at h
          cases hpe : predToExpr p with
          | error e => rw [hpe] at h; simp at h
          | ok pe =>
              rw [hpe] at h
              obtain rfl := Except.ok.inj h
              obtain ⟨in', hin⟩ := ih rq hqr rows input
              have himg : ∀ x ∈ in', ∃ b, (fun (row : Substrait.Typed.Row (fieldsSchema g)) =>
                  match pe.evalCell row with
                  | Except.ok (Option.some (Value.bool bb)) => Except.ok bb
                  | Except.ok _ => Except.ok false
                  | Except.error e => Except.error e) x = .ok b := by
                intro x hx
                obtain ⟨r'', _, htr''⟩ := qEval_sound _ q rq hqr rows input in' hin x hx
                refine ⟨p.check r'', ?_⟩
                rw [← htr'']
                simp only [predToExpr_ok p pe hpe r'']
              obtain ⟨out, hout⟩ := filterRowsM_ok_exists
                (fun row => match pe.evalCell row with
                  | .ok (some (.bool bb)) => .ok bb | .ok _ => .ok false
                  | .error e => .error e) in' himg
              refine ⟨out, ?_⟩
              simp only [evalRel, hin]
              exact hout
  | project c q ih =>
      intro rel h rows input
      simp only [qToRel] at h
      cases hqr : qToRel q with
      | error e => rw [hqr] at h; simp at h
      | ok rq =>
          rw [hqr] at h
          obtain rfl := Except.ok.inj h
          obtain ⟨in', hin⟩ := ih rq hqr rows input
          refine ⟨evalKeepW (colsKeep _ c) in', ?_⟩
          simp only [evalRel, hin]
  | join ln rn q1 q2 ih1 ih2 =>
      intro rel h rows input
      simp only [qToRel] at h
      cases hr1 : qToRel q1 with
      | error e => rw [hr1] at h; simp at h
      | ok r1 =>
          rw [hr1] at h
          cases hr2 : qToRel q2 with
          | error e => rw [hr2] at h; simp at h
          | ok r2 =>
              rw [hr2] at h
              cases hc : joinCond _ _ ln rn with
              | error e => rw [hc] at h; simp at h
              | ok c =>
                  rw [hc] at h
                  simp only [Except.ok.injEq] at h
                  obtain rfl := h
                  obtain ⟨lrows, hl1⟩ := ih1 r1 hr1 rows input
                  obtain ⟨rrows, hr2'⟩ := ih2 r2 hr2 rows input
                  have htot : ∀ (l : Substrait.Typed.Row _) (r' : Substrait.Typed.Row _),
                      ∃ b, condHolds c l r' = .ok b := joinCond_holds_total _ _ c hc
                  obtain ⟨t, ht⟩ := evalJoin_ok_exists .inner c htot lrows rrows
                  exact ⟨t.map (fun x => Substrait.Typed.Row.appendW (colsAppendCols _ _) x),
                    by simp only [evalRel, hl1, hr2', ht]⟩
  | union q1 q2 ih1 ih2 =>
      intro rel h rows input
      simp only [qToRel] at h
      cases hr1 : qToRel q1 with
      | error e => rw [hr1] at h; simp at h
      | ok r1 =>
          rw [hr1] at h
          cases hr2 : qToRel q2 with
          | error e => rw [hr2] at h; simp at h
          | ok r2 =>
              rw [hr2] at h
              obtain rfl := Except.ok.inj h
              obtain ⟨l, hl⟩ := ih1 r1 hr1 rows input
              obtain ⟨rr, hrr⟩ := ih2 r2 hr2 rows input
              refine ⟨l ++ rr, ?_⟩
              simp only [evalRel]
              rw [hl, hrr]

/-- THE AGREEMENT, complete face: every `QSat` row's typed image is
    produced — the evaluator drops nothing the spec keeps. The
    induction is over the QSAT DERIVATION: its indices there are the
    derivation's own binders, so the dependent elimination needs no
    index unification (inverting a `QSat` whose row index is the
    computed `c.fields gs` under the agreement's substitutions is not
    eliminable — the derivation-induction is the honest shape). -/
theorem qEval_complete {fs : List Field} (rows : List (RowVals fs)) :
    ∀ {gs : List Field} (q : Q fs gs) (r : RowVals gs),
    QSat fs rows q r →
    ∀ (rel : Rel (fieldsSchema fs) (fieldsSchema gs)),
    qToRel q = .ok rel →
    ∃ out, evalRel (bridgeReader rows) rel ([] : Table (fieldsSchema fs)) = .ok out
      ∧ toTypedRow gs r ∈ out := by
  intro gs q r hq
  induction hq with
  | table r₀ hm =>
      intro rel h
      simp only [qToRel] at h
      obtain rfl := Except.ok.inj h
      exact ⟨_, rfl, List.mem_map.mpr ⟨r₀, hm, rfl⟩⟩
  | @select g p q r hqc hcheck ih =>
      intro rel h
      simp only [qToRel] at h
      cases hqr : qToRel q with
      | error e => rw [hqr] at h; simp at h
      | ok rq =>
          rw [hqr] at h
          cases hpe : predToExpr p with
          | error e => rw [hpe] at h; simp at h
          | ok pe =>
              rw [hpe] at h
              simp only [Except.ok.injEq] at h
              obtain rfl := h
              obtain ⟨in', hin, hmem⟩ := ih rq hqr
              have himg : ∀ x ∈ in', ∃ b, (fun (row : Substrait.Typed.Row (fieldsSchema g)) =>
                  match pe.evalCell row with
                  | Except.ok (Option.some (Value.bool bb)) => Except.ok bb
                  | Except.ok _ => Except.ok false
                  | Except.error e => Except.error e) x = .ok b := by
                intro x hx
                obtain ⟨r'', _, htr''⟩ := qEval_sound _ q rq hqr rows [] in' hin x hx
                refine ⟨p.check r'', ?_⟩
                rw [← htr'']
                simp only [predToExpr_ok p pe hpe r'']
              obtain ⟨out, hout⟩ := filterRowsM_ok_exists
                (fun row => match pe.evalCell row with
                  | .ok (some (.bool bb)) => .ok bb | .ok _ => .ok false
                  | .error e => .error e) in' himg
              refine ⟨out, ?_, ?_⟩
              · simp only [evalRel, hin]
                exact hout
              · exact filterRowsM_ok_complete
                  (fun row => match pe.evalCell row with
                    | .ok (some (.bool bb)) => .ok bb | .ok _ => .ok false
                    | .error e => .error e) in' out hout
                  (toTypedRow _ r) hmem
                  (by simpa only [predToExpr_ok p pe hpe r, Except.ok.injEq] using hcheck)
  | @project g c q r' r hpre hpick ih =>
      intro rel h
      simp only [qToRel] at h
      cases hqr : qToRel q with
      | error e => rw [hqr] at h; simp at h
      | ok rq =>
          rw [hqr] at h
          simp only [Except.ok.injEq] at h
          obtain rfl := h
          obtain ⟨in', hin, hmem⟩ := ih rq hqr
          refine ⟨evalKeepW (colsKeep _ c) in', ?_, ?_⟩
          · simp only [evalRel, hin]
          · rw [← hpick, ← toTypedRow_keep]
            exact evalKeepW_out _ in' _ hmem
  | @join ga gb ln rn q1 q2 la rb r h1 h2 h3 h4 ih1 ih2 =>
      intro rel h
      simp only [qToRel] at h
      cases hr1 : qToRel q1 with
      | error e => rw [hr1] at h; simp at h
      | ok r1 =>
          rw [hr1] at h
          cases hr2 : qToRel q2 with
          | error e => rw [hr2] at h; simp at h
          | ok r2 =>
              rw [hr2] at h
              cases hc : joinCond _ _ ln rn with
              | error e => rw [hc] at h; simp at h
              | ok c =>
                  rw [hc] at h
                  obtain rfl := Except.ok.inj h
                  obtain ⟨lrows, hl1, hla⟩ := ih1 r1 hr1
                  obtain ⟨rrows, hr2', hrb⟩ := ih2 r2 hr2
                  have hc2 : condHolds c (toTypedRow ga la) (toTypedRow gb rb)
                      = .ok true := by
                    unfold condHolds
                    rw [joinCond_ok ln rn la rb c hc]
                    simpa using h3
                  have htot : ∀ (l : Substrait.Typed.Row _) (r' : Substrait.Typed.Row _),
                      ∃ b, condHolds c l r' = .ok b := joinCond_holds_total _ _ c hc
                  obtain ⟨p, hp⟩ := evalJoinPairs_ok_exists c htot lrows rrows
                  obtain ⟨ul, hul⟩ := unmatchedWith_ok_exists (anyMatch c)
                    (fun x t => anyMatchOn_ok_exists (condHolds c) htot x t) lrows rrows
                  obtain ⟨ur, hur⟩ := unmatchedWith_ok_exists (anyMatchR c)
                    (fun x t => anyMatchOn_ok_exists
                      (fun fixed walked => condHolds c walked fixed)
                      (fun y x => htot x y) x t) rrows lrows
                  have hjoin' : evalJoin .inner c lrows rrows = .ok p := by
                    simp only [evalJoin, unmatchedLeft, unmatchedRight,
                      hp, hul, hur]
                  refine ⟨p.map (fun x => Substrait.Typed.Row.appendW (colsAppendCols _ _) x),
                    ?_, ?_⟩
                  · simp only [evalRel, hl1, hr2', hjoin']
                  · rw [List.mem_map]
                    refine ⟨Substrait.Typed.Row.append (toTypedRow ga la)
                      (toTypedRow gb rb), ?_, ?_⟩
                    · exact evalJoinPairs_ok_complete c lrows rrows p hp
                        _ hla _ hrb hc2
                    · rw [appendW_colsAppend, ← h4]
  | @unionL g q1 q2 r h1 ih =>
      intro rel h
      simp only [qToRel] at h
      cases hr1 : qToRel q1 with
      | error e => rw [hr1] at h; simp at h
      | ok r1 =>
          rw [hr1] at h
          cases hr2 : qToRel q2 with
          | error e => rw [hr2] at h; simp at h
          | ok r2 =>
              rw [hr2] at h
              simp only [Except.ok.injEq] at h
              obtain rfl := h
              obtain ⟨out1, hok1, hmem⟩ := ih r1 hr1
              obtain ⟨out2, hok2⟩ := qEval_total g q2 r2 hr2 rows []
              refine ⟨out1 ++ out2, ?_, ?_⟩
              · simp only [evalRel, hok1, hok2]
              · exact List.mem_append.mpr (Or.inl hmem)
  | @unionR g q1 q2 r h2 ih =>
      intro rel h
      simp only [qToRel] at h
      cases hr1 : qToRel q1 with
      | error e => rw [hr1] at h; simp at h
      | ok r1 =>
          rw [hr1] at h
          cases hr2 : qToRel q2 with
          | error e => rw [hr2] at h; simp at h
          | ok r2 =>
              rw [hr2] at h
              simp only [Except.ok.injEq] at h
              obtain rfl := h
              obtain ⟨out2, hok2, hmem⟩ := ih r2 hr2
              obtain ⟨out1, hok1⟩ := qEval_total g q1 r1 hr1 rows []
              refine ⟨out1 ++ out2, ?_, ?_⟩
              · simp only [evalRel, hok1, hok2]
              · exact List.mem_append.mpr (Or.inr hmem)

/-- THE DUEL (design note §3.2): the two evaluators agree at the set
    level over Bool weights — a typed row is produced by the substrait
    evaluator EXACTLY when it is the image of a row in `evalQ`'s
    support (`evalQ_true_iff` is the lift; both directions). -/
theorem qEval_agree_iff {fs gs : List Field} (q : Q fs gs)
    (rel : Rel (fieldsSchema fs) (fieldsSchema gs)) (h : qToRel q = .ok rel)
    (rows : List (RowVals fs)) (r : RowVals gs)
    (out : Table (fieldsSchema gs))
    (hok : evalRel (bridgeReader rows) rel ([] : Table (fieldsSchema fs)) = .ok out) :
    toTypedRow gs r ∈ out ↔ weightW (evalQ q (tableW rows true)) r = true := by
  have hs := qEval_sound gs q rel h rows [] out hok
  constructor
  · intro hr
    obtain ⟨r', hq, htr⟩ := hs _ hr
    have hrr : r' = r := toTypedRow_inj htr
    rw [hrr] at hq
    exact (evalQ_true_iff q rows r).mpr hq
  · intro hw
    obtain ⟨out', hok', hmem⟩ := qEval_complete rows q r
      ((evalQ_true_iff q rows r).mp hw) rel h
    rw [hok'] at hok
    obtain rfl := Except.ok.inj hok
    exact hmem

end Query
