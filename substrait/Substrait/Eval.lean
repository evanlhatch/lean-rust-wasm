/-
# Substrait.Eval — the typed rels' in-memory evaluation + the query-lane reading

Owner: the substrait port agent (the mandate tree, `substrait/`).
Provenance: ported FRESH from `legacy/lean/substrait/Substrait/Eval.lean`
(the definitional second reading alongside `toProto` — the
two-readings idea), retargeted onto SchemaCore's closed `Ty`/`Value`
(the legacy's parallel `Cell` universe dies: a runtime cell IS
`Option (SchemaCore.Value t)` — `none` is SQL NULL) and NARROWED to the
grown rel fragment (read/filter/project/join/aggregate/fetch/set; the
narrowings are named at their arms):

- `sort` REFUSES loudly: the evaluator's fragment carries no total cell
  order over the closed `Ty` (the ordering lane ports with its
  consumer); sort's row-set identity is the type — the ORDER is the
  named gap.
- `set` implements `unionAll` (list append); `unionDistinct` REFUSES —
  deduplication is non-linear (the same boundary the query lane's
  Eval.lean names: "deduplication is non-linear"), and row equality
  over the GADT carrier needs more than this slice carries.
- `join` implements all four narrow join types (inner/left/right/outer
  with the `none`-padding).
- `evalFunc`'s built-in kernels: add/subtract over `i64`, gt/lt/equal
  over `i64`, and/or over `bool` — the extension catalogue is not
  consulted; any other name fails loudly (the legacy's discipline).

THE QUERY-LANE CONNECTION (the honest state):

- WHERE THE FRAGMENTS MEET — the semantics, pinned as theorems here:
  `evalRel`'s filter IS the query lane's `QSat.select` reading
  (selection RESTRICTS — `filterRowsM_ok_sound` +
  `filterRowsM_ok_complete`: the output rows are exactly the input rows
  whose condition evaluates to true, both directions), the join's
  inner core IS `QSat.join`'s conjunctive reading
  (`evalJoinPairs_ok_sound`: every produced row is an appended PAIR
  whose sides are present and whose condition holds), and the keep arm
  (the drop projection, `Rel.keep`) is the query lane's `QSat.project`
  reading via `Query.TypedBridge.toTypedRow_keep` — the kept row IS
  the picked row over the bridged schemas. The query lane's
  executable bridge (`Query.Eval.evalQ_true_iff`) is the same
  restricts/conjunctive discipline at ITS carrier.
- WHERE THEY DON'T (the named boundary): NO type-level conversion
  `Rel → Query.Q` lands in this slice. The row carriers differ (the
  GADT `Row` over `Schema`'s (name, Ty, nullable) triples vs the
  query lane's `RowVals` over `List Field`), and the query fragment's
  join is the EQUIJOIN on named columns while the typed rel's
  condition is the general `Expr` — the conversion needs both a
  schema-level Field/Ty unification and a condition-fragment map, and
  neither is forced by a current consumer (the leftover rule). The
  connection today is the SEMANTIC one above: the same relational
  readings, pinned at both carriers, named here — plus the FORWARD
  crossing that now exists: `Query.TypedBridge` lowers the query
  lane's `Q` (join-free fragment) into `Rel` and pins the evaluation
  agreement BOTH directions (`qEval_sound`/`qEval_complete`); its
  `Pred` lowering consumes this module's bridge kernels
  (`u64equal`/`u64gt`/`strequal`/`boolequal`/`not`).

MECHANICS (the seed's discipline, kept): every evaluator def is a
plain structural MATCH — no do-notation, no monad-lemma plumbing; the
bridge theorems' equations reduce (06's structural-recursion
discipline). The `list.mapM`/`filterM` shapes of the legacy became
explicit recursive helpers (`projectionCells`, `filterRowsM`,
`matchedRow`, ...) whose membership laws are provable by structural
induction — the Except-valued monad combinators are kernel-opaque and
would kill the bridges.

The five questions (notes/v3/01-core.md):
- root: Universe × Interpretation — the executable reading of the
  typed rels over runtime rows.
- carrier grade: the Row GADT (a row of the wrong schema is
  unconstructible); `HasCol.resolves` buys the field read's type
  (`Row.get_resolves` — the proof, not a cast check).
- spine reading: the SECOND reading — Typed → Proto (the wire) →
  Text, and Typed → Eval (the execution); the two readings of one
  structure.
- ladder rung: hand theorems of the small kind (the filter bridge
  both ways, the join soundness — structural inductions over the
  explicit helpers).
- gate row: the axiom report (Substrait is gated); SubstraitTests
  carries the eval pins + the mandatory negative controls.
-/

import Substrait.Typed

namespace Substrait.Typed

open SchemaCore

/-! ## runtime rows -/

/--
A runtime row over a schema: heterogeneous cells, one per column. A
cell IS `Option (Value t)` (the retarget: no parallel `Cell` universe)
— `none` is SQL NULL (the typed nullability says when `none` is LEGAL;
the evaluator treats a `none` cell as NULL regardless — the legacy's
nullability rule, kept).
-/
inductive Row : Schema → Type where
  | nil : Row []
  | cons : {t : Ty} → {name : String} → {n : Bool} →
      Option (Value t) → Row s → Row ((name, t, n) :: s)

/-- A table: a list of rows over one schema. -/
abbrev Table (s : Schema) := List (Row s)

/-- The source-resolver: table name → rows. -/
abbrev Reader (s : Schema) := String → Except String (Table s)

/-- The cell at ordinal `i` (with its runtime type), or `none` when out
    of range. -/
def Row.get : Row s → Nat → Option (Σ t, Option (Value t))
  | .nil, _ => none
  | .cons c _, 0 => some ⟨_, c⟩
  | .cons _ r, k + 1 => r.get k

/-- A row cell at a resolved ordinal carries the schema's type — the row
    is indexed by the schema, so `Row.get` at a `HasCol`-resolved index
    returns the claimed (name, type) triple's cell. This is what
    `HasCol.resolves` BUYS the evaluator: the field read's type is
    PROVED, not cast-checked (the legacy's fix, ported as content). -/
theorem Row.get_resolves {s : Schema} {name : String} {t : Ty} {n : Bool}
    (h : HasCol s name t n) (row : Row s) :
    ∃ c : Option (Value t), row.get h.index = some ⟨t, c⟩ := by
  induction s generalizing name t n with
  | nil =>
      exfalso
      have := h.resolves
      simp [Schema.get?] at this
  | cons col tl ih =>
      cases row with
      | cons cell rest =>
          by_cases h0 : h.index = 0
          · -- the head column IS (name, t, n) by resolves
            have hres := h.resolves
            rw [h0] at hres
            simp only [Schema.get?, Option.some.injEq, Prod.mk.injEq] at hres
            obtain ⟨hcol, ht', _⟩ := hres
            obtain ⟨_, _⟩ := hcol
            subst_vars
            exact ⟨cell, by simp [Row.get, h0]⟩
          · obtain ⟨k, hk⟩ : ∃ k, h.index = k + 1 := ⟨h.index - 1, by omega⟩
            have hres := h.resolves
            rw [hk] at hres
            simp only [Schema.get?] at hres
            obtain ⟨c, hc⟩ := ih ⟨k, hres⟩ rest
            refine ⟨c, ?_⟩
            rw [hk]
            exact hc

/-- Cast a runtime value to a pinned type: the transport along the
    (decidable) type equality — total over the closed `Ty`. The
    legacy's per-ctor `castCell` dies here: the closed universe's
    derived `DecidableEq` makes the cast ONE transport, and a
    same-type cast is the identity (below). -/
def castVal (t : Ty) : (Σ u, Value u) → Option (Value t)
  | Sigma.mk u v => if h : u = t then some (h ▸ v) else none

/-- A same-type cast is the identity — the runtime cast can only fail
    when an erased walk's cell type mismatches the schema. -/
theorem castVal_self (t : Ty) (v : Value t) : castVal t ⟨t, v⟩ = some v := by
  show (if h : t = t then some (h ▸ v) else none) = some v
  rw [dif_pos rfl]

/-- Build a row from a schema and runtime values (missing cells become
    NULL) — the aggregate output rows' builder. -/
def Row.ofCells : (schema : Schema) → List (Option (Σ t, Value t)) → Row schema
  | [], _ => .nil
  | (_, t, _) :: rest, es =>
      match es with
      | [] => .cons none (Row.ofCells rest [])
      | e :: es' => .cons (e.bind (fun w => castVal t w)) (Row.ofCells rest es')

/-- Append extra cells to a row, extending the schema by `extra` (the
    project arm's builder; the recursion unfolds the BASE row first so
    the appended schema stays on the tail — the legacy's shape). -/
def Row.appendCells (r : Row p) : (extra : Schema) →
    List (Option (Σ t, Value t)) → Row (p ++ extra) :=
  match r with
  | .nil => fun extra cells => Row.ofCells extra cells
  | .cons c base => fun extra cells => .cons c (Row.appendCells base extra cells)

/-- Concatenate two rows, extending the schema by list append (the
    join's builder; the base row unfolds first — the legacy's shape). -/
def Row.append {a b : Schema} : Row a → Row b → Row (a ++ b)
  | .nil, r => r
  | .cons c base, r => .cons c (Row.append base r)

/-- THE KEPT-CELLS ROW BUILDER (the drop projection's runtime face,
    `Rel.keep`'s evaluation): walk the KEEP WITNESS, keeping or
    skipping cells — the witness (the Type-sorted data face of the
    subselection; a `List.Sublist` PROOF cannot drive the walk, its
    elimination into data is refused) drives it, so no index search and
    no cast; the recursion is structural on the witness. -/
def Row.keepW {s' outs : Schema} : Row s' → Keep s' outs → Row outs
  | .nil, .wnil => .nil
  | .cons _ rest, .wdrop _ h => Row.keepW rest h
  | .cons c rest, .wkeep _ h => .cons c (Row.keepW rest h)

/-- The drop-everything walk: the `Keep.none` witness's canonical shape
    drops every cell (the bridge's keep-pick lemma's nil case). -/
theorem keepW_none : ∀ (l : Schema) (row : Row l),
    Row.keepW row (Keep.none l) = .nil := by
  intro l
  induction l with
  | nil => intro row; cases row; rfl
  | cons a l' ih => intro row; cases row; exact ih _

/-- The drop-projection's table walk (total — every kept cell exists by
    the type; the drop never refuses). -/
def evalKeepW {s' outs : Schema} (w : Keep s' outs) :
    Table s' → Table outs
  | [] => []
  | r :: rest => Row.keepW r w :: evalKeepW w rest

/-- The keep walk's membership, sound face: every kept row is a kept
    copy of an input row. -/
theorem evalKeepW_in {s' outs : Schema} (w : Keep s' outs) :
    ∀ (t : Table s') (r : Row outs), r ∈ evalKeepW w t →
    ∃ r₀, r₀ ∈ t ∧ r = Row.keepW r₀ w := by
  intro t
  induction t with
  | nil => intro r hr; cases hr
  | cons r0 rest ih =>
      intro r hr
      simp only [evalKeepW, List.mem_cons] at hr
      rcases hr with hr | hr
      · exact ⟨r0, List.mem_cons.mpr (Or.inl rfl), hr⟩
      · obtain ⟨r₀, hm, hrEq⟩ := ih r hr
        exact ⟨r₀, List.mem_cons.mpr (Or.inr hm), hrEq⟩

/-- The keep walk's membership, complete face: every input row's kept
    copy is in the output. -/
theorem evalKeepW_out {s' outs : Schema} (w : Keep s' outs) :
    ∀ (t : Table s') (r₀ : Row s'), r₀ ∈ t → Row.keepW r₀ w ∈ evalKeepW w t := by
  intro t
  induction t with
  | nil => intro r₀ hm; cases hm
  | cons r0 rest ih =>
      intro r₀ hm
      simp only [evalKeepW, List.mem_cons]
      rcases List.mem_cons.mp hm with hm | hm
      · rw [hm]
        exact Or.inl rfl
      · exact Or.inr (ih r₀ hm)

/-- An all-`none` row of the given schema (the outer-join padding). -/
def Row.padNone : (s : Schema) → Row s
  | [] => .nil
  | (_, _, _) :: rest => .cons none (Row.padNone rest)

/-- The left part of a row over the concatenated schema `a ++ b` (the
    split depends only on `a`, so it is total without casts). -/
def Row.splitLeft {b : Schema} : (a : Schema) → Row (a ++ b) → Row a
  | [], _ => .nil
  | (_, _, _) :: rest, r =>
      match r with
      | .cons c rest' => .cons c (Row.splitLeft rest rest')

/-- The right part of a row over the concatenated schema `a ++ b`. -/
def Row.splitRight {b : Schema} : (a : Schema) → Row (a ++ b) → Row b
  | [], r => r
  | (_, _, _) :: rest, r =>
      match r with
      | .cons _ rest' => Row.splitRight rest rest'

/-! ## expression evaluation -/

/-- Read an i64 payload from a runtime argument (none for null or
    other-typed). -/
def argI64 : (Σ t, Option (Value t)) → Option Int64
  | Sigma.mk .i64 (some (.i64 x)) => some x
  | _ => none

/-- Read a bool payload from a runtime argument. -/
def argBool : (Σ t, Option (Value t)) → Option Bool
  | Sigma.mk .bool (some (.bool b)) => some b
  | _ => none

/-- Read a u64 payload from a runtime argument (the bridge kernels'
    reader — `Query.TypedBridge`'s predicate lowering consumes). -/
def argU64 : (Σ t, Option (Value t)) → Option UInt64
  | Sigma.mk .u64 (some (.u64 x)) => some x
  | _ => none

/-- Read a string payload from a runtime argument (the bridge kernels'
    reader). -/
def argString : (Σ t, Option (Value t)) → Option String
  | Sigma.mk .string (some (.string s)) => some s
  | _ => none

/-- A two-argument scalar kernel: read both args (NULL or other-typed →
    NULL out — the SQL null-propagation), combine, wrap. The evalFunc
    arms are this ONE shape (the legacy's binKernel, ported). -/
def binKernel (args : List (Σ t, Option (Value t)))
    (read : (Σ t, Option (Value t)) → Option α)
    (op : α → α → β) (wrap : β → Value r) :
    Except String (Option (Value r)) :=
  match args with
  | [a, b] =>
      match read a, read b with
      | some x, some y => .ok (some (wrap (op x y)))
      | _, _ => .ok none
  | _ => .error "eval: kernel expects two arguments"

/-- The built-in scalar kernels: add/subtract over i64, gt/lt/equal
    over i64, and/or over bool, plus the bridge kernels (u64/string/
    bool equality, u64 gt, not — `Query.TypedBridge`'s Pred lowering
    is the consumer). Anything else fails loudly (the
    extension catalogue is out of scope — the legacy's discipline). -/
def evalFunc (sig : FunctionSig) (args : List (Σ t, Option (Value t))) :
    Except String (Option (Value sig.ret)) :=
  match sig.name, sig.ret with
  | "add", .i64 => binKernel args argI64 (· + ·) Value.i64
  | "subtract", .i64 => binKernel args argI64 (· - ·) Value.i64
  | "gt", .bool => binKernel args argI64 (fun x y => decide (x > y)) Value.bool
  | "lt", .bool => binKernel args argI64 (fun x y => decide (x < y)) Value.bool
  | "equal", .bool => binKernel args argI64 (fun x y => x == y) Value.bool
  | "and", .bool => binKernel args argBool (fun x y => x && y) Value.bool
  | "or", .bool => binKernel args argBool (fun x y => x || y) Value.bool
  -- the bridge kernels (`Query.TypedBridge`'s Pred lowering is the
  -- consumer; one name per argument TYPE so the dispatch is injective
  -- in the compared columns' type — a mixed-type comparison cannot
  -- share a kernel name, and the lowering refuses where it cannot
  -- name one)
  | "u64equal", .bool => binKernel args argU64 (fun x y => x == y) Value.bool
  | "u64gt", .bool => binKernel args argU64 (fun x y => decide (x > y)) Value.bool
  | "strequal", .bool => binKernel args argString (fun x y => x == y) Value.bool
  | "boolequal", .bool => binKernel args argBool (fun x y => x == y) Value.bool
  | "not", .bool =>
      match args with
      | [a] =>
          match argBool a with
          | some b => .ok (some (Value.bool (!b)))
          | none => .ok none
      | _ => .error "eval: not expects one argument"
  | name, _ => .error s!"eval: function {name} not implemented in the evaluator"

-- Evaluate an argument spine to runtime values (mutual with
-- `Expr.evalCell`; plain matches — the monad-combinator spelling is
-- kernel-opaque and kills the bridges, the module header's note).
mutual
  /-- Evaluate a scalar expression over a row (NULL-propagating). -/
  def Expr.evalCell : Expr s t n → (row : Row s) →
      Except String (Option (Value t))
    | .literal _ v, _ => .ok (some v)
    | .field _ t _ hcol, row =>
        match row.get hcol.index with
        | some ⟨t', v⟩ =>
            match v with
            | none => .ok none
            | some w =>
                match castVal t ⟨t', w⟩ with
                | some w' => .ok (some w')
                | none => .error "eval: cell type mismatch"
        | none => .error "eval: column index out of range"
    | .call sig args, row =>
        match args.eval row with
        | .ok vs => evalFunc sig vs
        | .error e => .error e

  def Args.eval : Args s ts → (row : Row s) →
      Except String (List (Σ t, Option (Value t)))
    | .nil, _ => .ok []
    | .cons t _ e rest, row =>
        match e.evalCell row with
        | .error e1 => .error e1
        | .ok v =>
            match rest.eval row with
            | .error e2 => .error e2
            | .ok vs => .ok ((Sigma.mk t v : Σ t, Option (Value t)) :: vs)
end

/-- Evaluate a packaged expression (the grouping keys' walk). -/
def evalAnyExpr {s : Schema} (ae : AnyExpr s) (row : Row s) :
    Except String (Σ t, Option (Value t)) :=
  match ae with
  | .mk t _ e =>
      match e.evalCell row with
      | .ok v => .ok ⟨t, v⟩
      | .error e2 => .error e2

/-! ## the projection walk -/

/-- The projections' computed cells for one row (the extras list —
    `none` elements are NULL cells). -/
def projectionCells {p : Schema} (row : Row p) :
    List (Projection p) → Except String (List (Option (Σ t, Value t)))
  | [] => .ok []
  | pr :: rest =>
      match pr.expr.evalCell row with
      | .error e => .error e
      | .ok v =>
          match projectionCells row rest with
          | .error e => .error e
          | .ok vs => .ok (v.map (fun c => Sigma.mk pr.dtype c) :: vs)

/-- Evaluate a typed projection over a table of the input schema (the
    `p ++ …` append shape makes this the schema-CHANGING pipeline
    step; the evalRel project arm routes here). The return type spells
    the append DIRECTLY (the same term `projectOut`'s body is — the
    rel arm's expected type crosses by delta, never by a fresh
    elaboration). -/
def evalProject {p : Schema} (outs : List (Projection p)) :
    Table p →
    Except String (Table (p ++ outs.map (fun pr => (pr.name, pr.dtype, pr.nullable))))
  | [] => .ok []
  | row :: rest =>
      match projectionCells row outs, evalProject outs rest with
      | .ok extras, .ok more =>
          .ok (Row.appendCells row
            (outs.map (fun pr => (pr.name, pr.dtype, pr.nullable))) extras :: more)
      | .error e, _ => .error e
      | _, .error e => .error e

/-! ## the filter walk (the query lane's `select` reading) -/

/-- The Except-valued row filter, EXPLICIT recursion (the monad
    combinators are kernel-opaque — the bridge theorems need the
    equations). -/
def filterRowsM {s : Schema} (f : Row s → Except String Bool) :
    List (Row s) → Except String (List (Row s))
  | [] => .ok []
  | r :: rest =>
      match f r with
      | .error e => .error e
      | .ok true =>
          match filterRowsM f rest with
          | .ok out => .ok (r :: out)
          | .error e => .error e
      | .ok false => filterRowsM f rest

/-- THE FILTER BRIDGE, sound face (the query lane's `QSat.select`
    reading): every output row is an input row whose condition evaluated
    to true. Selection RESTRICTS — the executable filter never invents
    rows and never keeps a failing one. -/
theorem filterRowsM_ok_sound {s : Schema} (f : Row s → Except String Bool) :
    ∀ (rows out : List (Row s)),
    filterRowsM f rows = .ok out →
    ∀ r ∈ out, r ∈ rows ∧ f r = .ok true := by
  intro rows
  induction rows with
  | nil =>
      intro out h
      simp only [filterRowsM] at h
      cases h
      intro r hr
      cases hr
  | cons r0 rest ih =>
      intro out h
      simp only [filterRowsM] at h
      cases hf : f r0 with
      | error _ => rw [hf] at h; simp at h
      | ok b =>
          rw [hf] at h
          cases b with
          | false =>
              intro r hr
              obtain ⟨hm, ht⟩ := ih out h r hr
              exact ⟨List.mem_cons.mpr (Or.inr hm), ht⟩
          | true =>
              cases h2 : filterRowsM f rest with
              | error _ => rw [h2] at h; simp at h
              | ok out' =>
                  rw [h2] at h
                  simp only [Except.ok.injEq] at h
                  subst h
                  intro r hr
                  simp only [List.mem_cons] at hr
                  rcases hr with hr | hr
                  · rw [hr]
                    exact ⟨List.mem_cons.mpr (Or.inl rfl), hf⟩
                  · obtain ⟨hm, ht⟩ := ih out' h2 r hr
                    exact ⟨List.mem_cons.mpr (Or.inr hm), ht⟩

/-- THE FILTER BRIDGE, complete face: every input row whose condition
    evaluates to true IS in the output — the executable filter drops
    nothing it should keep. -/
theorem filterRowsM_ok_complete {s : Schema} (f : Row s → Except String Bool) :
    ∀ (rows out : List (Row s)),
    filterRowsM f rows = .ok out →
    ∀ r ∈ rows, f r = .ok true → r ∈ out := by
  intro rows
  induction rows with
  | nil =>
      intro out h r hr _ht
      simp only [filterRowsM] at h
      cases h
      cases hr
  | cons r0 rest ih =>
      intro out h
      simp only [filterRowsM] at h
      cases hf : f r0 with
      | error _ => rw [hf] at h; simp at h
      | ok b =>
          rw [hf] at h
          cases b with
          | false =>
              cases h2 : filterRowsM f rest with
              | error _ => rw [h2] at h; simp at h
              | ok out' =>
                  rw [h2] at h
                  simp only [Except.ok.injEq] at h
                  subst h
                  intro r hr ht
                  simp only [List.mem_cons] at hr
                  rcases hr with hr | hr
                  · rw [hr] at ht; simp [hf] at ht
                  · exact ih out' h2 r hr ht
          | true =>
              cases h2 : filterRowsM f rest with
              | error _ => rw [h2] at h; simp at h
              | ok out' =>
                  rw [h2] at h
                  simp only [Except.ok.injEq] at h
                  subst h
                  intro r hr ht
                  simp only [List.mem_cons] at hr
                  rcases hr with hr | hr
                  · rw [hr]
                    exact List.mem_cons.mpr (Or.inl rfl)
                  · exact List.mem_cons_of_mem _ (ih out' h2 r hr ht)

/-! ## the join walk (the query lane's `join` reading) -/

/-- The ON condition's Bool face: the condition over the appended row —
    `some (.bool true)` holds; NULL or false (or any error-free other
    payload) drops (the SQL refusal reading). -/
def condHolds {l' r' : Schema} {n : Bool} (cond : Expr (l' ++ r') .bool n)
    (l : Row l') (r : Row r') : Except String Bool :=
  match cond.evalCell (Row.append l r) with
  | .ok (some (.bool b)) => .ok b
  | .ok _ => .ok false
  | .error e => .error e

/-- The matching right rows for one left row, at the appended-pair
    shape (explicit recursion). -/
def matchedRow {l' r' : Schema} {n : Bool} (cond : Expr (l' ++ r') .bool n)
    (l : Row l') : Table r' → Except String (Table (l' ++ r'))
  | [] => .ok []
  | r :: rest =>
      match condHolds cond l r with
      | .error e => .error e
      | .ok true =>
          match matchedRow cond l rest with
          | .ok out => .ok (Row.append l r :: out)
          | .error e => .error e
      | .ok false => matchedRow cond l rest

/-- THE JOIN BRIDGE, per-left-row face: every produced pair is the left
    row appended to a PRESENT right row whose condition slot holds
    (the conjunctive reading's inner walk). -/
theorem matchedRow_ok_sound {l' r' : Schema} {n : Bool}
    (cond : Expr (l' ++ r') .bool n) (l : Row l') :
    ∀ (rrows : Table r') (m : Table (l' ++ r')),
    matchedRow cond l rrows = .ok m →
    ∀ x ∈ m, ∃ rb, x = Row.append l rb ∧ rb ∈ rrows ∧
      condHolds cond l rb = .ok true := by
  intro rrows
  induction rrows with
  | nil =>
      intro m hm x hx
      simp only [matchedRow] at hm
      cases hm
      cases hx
  | cons r0 rrest ih =>
      intro m hm x hx
      simp only [matchedRow] at hm
      cases hc : condHolds cond l r0 with
      | error _ => rw [hc] at hm; simp at hm
      | ok bb =>
          rw [hc] at hm
          cases bb with
          | false =>
              obtain ⟨rb, hxe, hrb, hcond⟩ := ih m hm x hx
              exact ⟨rb, hxe, List.mem_cons.mpr (Or.inr hrb), hcond⟩
          | true =>
              cases h3 : matchedRow cond l rrest with
              | error _ => rw [h3] at hm; simp at hm
              | ok m' =>
                  rw [h3] at hm
                  simp only [Except.ok.injEq] at hm
                  subst hm
                  simp only [List.mem_cons] at hx
                  rcases hx with hx | hx
                  · rw [hx]
                    exact ⟨r0, rfl, List.mem_cons.mpr (Or.inl rfl), hc⟩
                  · obtain ⟨rb, hxe, hrb, hcond⟩ := ih m' h3 x hx
                    exact ⟨rb, hxe, List.mem_cons.mpr (Or.inr hrb), hcond⟩

/-- The join's inner core: the appended pairs satisfying the ON
    condition (explicit double recursion). -/
def evalJoinPairs {l' r' : Schema} {n : Bool} (cond : Expr (l' ++ r') .bool n) :
    Table l' → Table r' → Except String (Table (l' ++ r'))
  | [], _ => .ok []
  | l :: lrest, rrows =>
      match matchedRow cond l rrows, evalJoinPairs cond lrest rrows with
      | .ok matched, .ok rest => .ok (matched ++ rest)
      | .error e, _ => .error e
      | _, .error e => .error e

/-- THE JOIN BRIDGE, sound face (the query lane's `QSat.join` reading):
    every produced row is an APPENDED PAIR whose sides are present and
    whose condition holds — the join is conjunctive, the executable
    core never invents pairs. The bidirectional face (completeness)
    is the named follow-up: its statement needs the pair-membership
    law of the `++`-append walk, which is the same content at the
    query lane's `QSat.join` clause — one of the two readings here is
    the seed's honest size. -/
theorem evalJoinPairs_ok_sound {l' r' : Schema} {n : Bool}
    (cond : Expr (l' ++ r') .bool n) :
    ∀ (lrows : Table l') (rrows : Table r') (out : Table (l' ++ r')),
    evalJoinPairs cond lrows rrows = .ok out →
    ∀ r ∈ out, ∃ la, ∃ rb, r = Row.append la rb ∧ la ∈ lrows ∧ rb ∈ rrows ∧
      condHolds cond la rb = .ok true := by
  intro lrows
  induction lrows with
  | nil =>
      intro rrows out h r hr
      simp only [evalJoinPairs] at h
      cases h
      cases hr
  | cons l lrest ih =>
      intro rrows out h r hr
      simp only [evalJoinPairs] at h
      cases hm : matchedRow cond l rrows with
      | error _ => rw [hm] at h; simp at h
      | ok matched =>
          rw [hm] at h
          cases hr2 : evalJoinPairs cond lrest rrows with
          | error _ => rw [hr2] at h; simp at h
          | ok rest =>
              rw [hr2] at h
              simp only [Except.ok.injEq] at h
              subst h
              simp only [List.mem_append] at hr
              rcases hr with hr | hr
              · obtain ⟨rb, hxe, hrb, hcond⟩ :=
                  matchedRow_ok_sound cond l rrows matched hm r hr
                exact ⟨l, rb, hxe, List.mem_cons.mpr (Or.inl rfl), hrb, hcond⟩
              · obtain ⟨la, rb, hxe, hla, hrb, hcond⟩ :=
                  ih rrows rest hr2 r hr
                exact ⟨la, rb, hxe, List.mem_cons.mpr (Or.inr hla), hrb, hcond⟩

/-- The any-match WALK (the mirrored pair's ONE recursion): a fixed
    row of the SECOND schema against a walked table of the FIRST —
    `holds` reads (fixed, walked), so the left arm's `anyMatch` and
    the right arm's `anyMatchR` are both instances. -/
def anyMatchOn {s1 s2 : Schema}
    (holds : Row s2 → Row s1 → Except String Bool) (fixed : Row s2) :
    Table s1 → Except String Bool
  | [] => .ok false
  | x :: rest =>
      match holds fixed x with
      | .error e => .error e
      | .ok true => .ok true
      | .ok false => anyMatchOn holds fixed rest

/-- The unmatched KEEP (the mirror pair's ONE recursion): keep the
    walked rows no `any` test matches (the outer arms' padding rows). -/
def unmatchedWith {s1 s2 : Schema}
    (any : Row s1 → Table s2 → Except String Bool) :
    Table s1 → Table s2 → Except String (Table s1)
  | [], _ => .ok []
  | x :: rest, fixed =>
      match any x fixed, unmatchedWith any rest fixed with
      | .ok false, .ok more => .ok (x :: more)
      | .ok true, .ok more => .ok more
      | .error e, _ => .error e
      | _, .error e => .error e

/-- The unmatched-left test for one left row (the `anyMatchOn`
    instance: the left row fixed, the right rows walked). -/
def anyMatch {l' r' : Schema} {n : Bool} (cond : Expr (l' ++ r') .bool n)
    (l : Row l') : Table r' → Except String Bool :=
  anyMatchOn (condHolds cond) l

/-- The left arm's keep walk (the `unmatchedWith` instance). -/
def unmatchedLeft {l' r' : Schema} {n : Bool} (cond : Expr (l' ++ r') .bool n) :
    Table l' → Table r' → Except String (Table l') :=
  unmatchedWith (anyMatch cond)

/-- The unmatched-RIGHT test (the mirror: the right row fixed, the
    left rows walked — the condition still reads left×right). -/
def anyMatchR {l' r' : Schema} {n : Bool} (cond : Expr (l' ++ r') .bool n)
    (r : Row r') : Table l' → Except String Bool :=
  anyMatchOn (fun fixed walked => condHolds cond walked fixed) r

/-- The right arm's keep walk (the `unmatchedWith` instance). -/
def unmatchedRight {l' r' : Schema} {n : Bool} (cond : Expr (l' ++ r') .bool n) :
    Table r' → Table l' → Except String (Table r') :=
  unmatchedWith (anyMatchR cond)

/-- The join's four narrow types: inner keeps the matched pairs;
    left/right/outer add the unmatched side padded with `none` cells
    (the `Row` type carries the full width regardless of nullability —
    the legacy's discipline). -/
def evalJoin {l' r' : Schema} {n : Bool} (jt : Proto.JoinType)
    (cond : Expr (l' ++ r') .bool n)
    (lrows : Table l') (rrows : Table r') :
    Except String (Table (l' ++ r')) :=
  match evalJoinPairs cond lrows rrows,
        unmatchedLeft cond lrows rrows,
        unmatchedRight cond rrows lrows with
  | .ok inner, .ok ul, .ok ur =>
      match jt with
      | .inner => .ok inner
      | .left => .ok (inner ++ ul.map (fun l => Row.append l (Row.padNone r')))
      | .right => .ok (inner ++ ur.map (fun r => Row.append (Row.padNone l') r))
      | .outer =>
          .ok (inner ++ ul.map (fun l => Row.append l (Row.padNone r'))
            ++ ur.map (fun r => Row.append (Row.padNone l') r))
  | .error e, _, _ => .error e
  | _, .error e, _ => .error e
  | _, _, .error e => .error e

/-! ## the aggregate walk -/

/-- Present a key value as an optional typed value (the aggregate
    output row's cell). -/
def optCellOf : (Σ t, Option (Value t)) → Option (Σ t, Value t)
  | ⟨_, none⟩ => none
  | ⟨t, some c⟩ => some ⟨t, c⟩

/-- The grouping-key cell equality — the SCALAR keys only (a
    non-scalar grouping key compares unequal at eval — the composite
    key discipline lands with its consumer; the seed's keys are
    scalars). -/
def keyCellEq : (Σ t, Option (Value t)) → (Σ t, Option (Value t)) → Bool
  | Sigma.mk .bool (some a), Sigma.mk .bool (some b) => a == b
  | Sigma.mk .u64 (some a), Sigma.mk .u64 (some b) => a == b
  | Sigma.mk .i64 (some a), Sigma.mk .i64 (some b) => a == b
  | Sigma.mk .string (some a), Sigma.mk .string (some b) => a == b
  | Sigma.mk _ none, Sigma.mk _ none => true
  | _, _ => false

/-- Key-list equality (pairwise `keyCellEq`). -/
def keyListEq : List (Σ t, Option (Value t)) →
    List (Σ t, Option (Value t)) → Bool
  | [], [] => true
  | x :: xs, y :: ys => keyCellEq x y && keyListEq xs ys
  | _, _ => false

/-- Insert a row into the correct key bucket (keys compared by
    `keyListEq`); buckets appear in first-seen key order. -/
def insertBucket {s : Schema} (k : List (Σ t, Option (Value t))) (row : Row s) :
    List (List (Σ t, Option (Value t)) × Table s) →
    List (List (Σ t, Option (Value t)) × Table s)
  | [] => [(k, [row])]
  | (k', rows) :: rest =>
      if keyListEq k k' then (k', rows ++ [row]) :: rest
      else (k', rows) :: insertBucket k row rest

/-- The non-null count's walk (the explicit accumulator recursion). -/
def countNonNull {s : Schema} (ae : AnyExpr s) : Table s → Int →
    Except String (Option (Σ t, Value t))
  | [], acc => .ok (some ⟨.i64, .i64 (Int64.ofInt acc)⟩)
  | row :: rest, acc =>
      match evalAnyExpr ae row with
      | .error e => .error e
      | .ok ⟨_, none⟩ => countNonNull ae rest acc
      | .ok ⟨_, some _⟩ => countNonNull ae rest (acc + 1)

/-- The i64 sum's walk (NULL cells skipped; an all-NULL group sums to
    NULL — the SQL aggregate rule). -/
def sumI64 {s : Schema} (ae : AnyExpr s) : Table s → Option Int64 →
    Except String (Option (Σ t, Value t))
  | [], acc =>
      match acc with
      | none => .ok none
      | some v => .ok (some ⟨.i64, .i64 v⟩)
  | row :: rest, acc =>
      match evalAnyExpr ae row with
      | .error e => .error e
      | .ok ⟨_, none⟩ => sumI64 ae rest acc
      | .ok ⟨_, some (.i64 v)⟩ => sumI64 ae rest (acc.map (· + v))
      | .ok ⟨_, some _⟩ => .error "eval: sum expects i64 arguments"

/-- Evaluate one aggregate measure over a group's rows — the narrow
    kernels: `count` (zero or one argument — with an argument it counts
    the non-null values) and `sum` over i64 (the seed's i64 fragment;
    min/max/avg port with their consumers). Anything else fails
    loudly. -/
def evalMeasure {s : Schema} (m : Measure s) (group : Table s) :
    Except String (Option (Σ t, Value t)) :=
  -- the (name, arg-list) dispatch over the LOOSE list (the Measure
  -- shape's face): the arity is checked HERE, loudly
  match m.sig.name, m.args with
  | "count", [] => .ok (some ⟨.i64, .i64 (Int64.ofInt (group.length : Int))⟩)
  | "count", [ae] => countNonNull ae group 0
  | "count", _ => .error "eval: count expects zero or one argument"
  | "sum", [ae] => sumI64 ae group none
  | "sum", _ => .error "eval: sum expects one argument"
  | name, _ => .error s!"eval: aggregate function {name} not implemented"

/-- The keys' evaluation per row (explicit map walk). -/
def keyedRows {s : Schema} (grouping : List (AnyExpr s)) :
    Table s → Except String (List (List (Σ t, Option (Value t)) × Row s))
  | [] => .ok []
  | row :: rest =>
      match keysOf grouping row, keyedRows grouping rest with
      | .error e, _ => .error e
      | _, .error e => .error e
      | .ok ks, .ok more => .ok ((ks, row) :: more)
where
  /-- One row's grouping keys. -/
  keysOf : List (AnyExpr s) → Row s →
      Except String (List (Σ t, Option (Value t)))
    | [], _ => .ok []
    | ae :: rest, row =>
        match evalAnyExpr ae row, keysOf rest row with
        | .error e, _ => .error e
        | _, .error e => .error e
        | .ok k, .ok ks => .ok (k :: ks)

/-- The measures' cells for one group. -/
def measureCells {s : Schema} (grp : Table s) :
    List (Measure s) → Except String (List (Option (Σ t, Value t)))
  | [] => .ok []
  | m :: rest =>
      match evalMeasure m grp, measureCells grp rest with
      | .error e, _ => .error e
      | _, .error e => .error e
      | .ok v, .ok vs => .ok (v :: vs)

/-- One bucket's output row (keys then measures), then the remaining
    buckets. -/
def groupRows {s : Schema} (grouping : List (AnyExpr s))
    (measures : List (Measure s)) :
    List (List (Σ t, Option (Value t)) × Table s) →
    Except String (Table (aggregateOut s grouping measures))
  | [] => .ok []
  | (k, grp) :: rest =>
      match measureCells grp measures, groupRows grouping measures rest with
      | .error e, _ => .error e
      | _, .error e => .error e
      | .ok ms, .ok more =>
          .ok (Row.ofCells (aggregateOut s grouping measures)
            (k.map optCellOf ++ ms) :: more)

/-- Evaluate an aggregate rel: bucket the rows by their evaluated
    grouping keys, then run each measure over its group. Each output
    row is the grouping-key cells followed by the measure cells (both
    in the constructor's list order); buckets appear in first-seen key
    order. -/
def evalAggregate {s : Schema} (grouping : List (AnyExpr s))
    (measures : List (Measure s)) (rows : Table s) :
    Except String (Table (aggregateOut s grouping measures)) :=
  match keyedRows grouping rows with
  | .error e => .error e
  | .ok keyed =>
      match groupRows grouping measures
        (keyed.foldl (fun acc p => insertBucket p.1 p.2 acc) []) with
      | .error e => .error e
      | .ok out => .ok out

/-! ## the fetch walk -/

/-- Apply limit/offset to a row list (the legacy's shape). -/
def applyFetch : Option Nat → Option Nat → List ρ → List ρ
  | limit, offset, xs =>
      let dropped := xs.drop (offset.getD 0)
      match limit with
      | some n => dropped.take n
      | none => dropped

/-! ## the relation evaluation -/

/--
THE EXECUTABLE EVALUATION (the second reading): structural over the
typed rels. Read resolves through the reader; filter restricts (the
bridge above); project computes the appended columns; keep DROPS (the
sublist-proof walk — total); join runs the
children over their split halves and pairs the matches; aggregate
buckets + measures; fetch windows; set appends (unionAll). The named
refusals: sort (no total cell order in the fragment) and
unionDistinct (deduplication is non-linear) — both loud, never lossy.
-/
def evalRel {s s' : Schema} (reader : Reader s) :
    Rel s s' → Table s → Except String (Table s')
  | .read table _, _ => reader table
  | .filter input cond, rows =>
      -- the input rel EVALUATES first (the legacy's recursion — the
      -- port had dropped it, discarding the sub-plan; the restoration
      -- is behavior-preserving for the seed's pins, whose filter sits
      -- over a read of the same table)
      match evalRel reader input rows with
      | .ok r =>
          filterRowsM (fun row =>
            match cond.evalCell row with
            | .ok (some (.bool b)) => .ok b
            | .ok _ => .ok false
            | .error e => .error e) r
      | .error e => .error e
  | .project input outs, rows =>
      match evalRel reader input rows with
      | .ok r => evalProject outs r
      | .error e => .error e
  | .keep input w, rows =>
      -- the drop projection: the walk is TOTAL (every kept cell exists
      -- by the type) — the refusals live in the LOWERING, never here
      match evalRel reader input rows with
      | .ok r => .ok (evalKeepW w r)
      | .error e => .error e
  | @Rel.join sl _sl' sr _sr' _ left right cond jt, rows =>
      -- the children read their own halves of the full-width stream
      -- (the legacy's reader-splitting discipline)
      let lread : Reader sl := fun name =>
        match reader name with
        | .error e => .error e
        | .ok t => .ok (t.map (fun r => Row.splitLeft sl r))
      let rread : Reader sr := fun name =>
        match reader name with
        | .error e => .error e
        | .ok t => .ok (t.map (fun r => Row.splitRight sl r))
      match evalRel lread left (rows.map (fun r => Row.splitLeft sl r)),
            evalRel rread right (rows.map (fun r => Row.splitRight sl r)) with
      | .ok lrows, .ok rrows => evalJoin jt cond lrows rrows
      | .error e, _ => .error e
      | _, .error e => .error e
  | .aggregate _ grouping measures, rows =>
      evalAggregate grouping measures rows
  | .sort _ _, _ =>
      .error "eval: sort — no total cell order in the evaluator's fragment (the ordering lane ports with its consumer)"
  | .fetch input limit offset, rows =>
      match evalRel reader input rows with
      | .ok r => .ok (applyFetch limit offset r)
      | .error e => .error e
  | .set op left right, rows =>
      match op with
      | .unionAll =>
          match evalRel reader left rows, evalRel reader right rows with
          | .ok l, .ok r => .ok (l ++ r)
          | .error e, _ => .error e
          | _, .error e => .error e
      | .unionDistinct =>
          .error "eval: unionDistinct — deduplication is non-linear (the named boundary; unionAll is the implemented op)"

end Substrait.Typed
