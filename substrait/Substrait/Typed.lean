/-
# Substrait.Typed — the schema-indexed typed layer, retargeted

Owner: the substrait port agent (the mandate tree, `substrait/`).
Provenance: ported FRESH from `legacy/lean/substrait/Substrait/Typed/*`
(the schema-indexed content), with THE RETARGET the doctrine demands
(notes/v3/14-build-map.md's substrait row + the query-fragment
precedent): the legacy's parallel `SType` universe DIES — the typed
layer indexes over SchemaCore's closed `Ty`, and literal payloads ARE
`SchemaCore.Value t` (the mismatched-payload-is-unconstructible GADT —
test vectors and validators come free). No `eqAns`/`beq` family ports:
`Ty`'s derived `DecidableEq` + `Value`'s `beq_refl` are the ONE
equality surface (the retarget's payoff).

SLICE-2 GROWTH (the aggregate/sort/fetch/set rows, ported from legacy
`Typed/Rel.lean`'s fuller shapes, every narrowing named):

- `AnyExpr` — the type-erased packaged expression (the legacy's shape,
  retargeted): heterogeneous expression LISTS not tied to a signature
  (the aggregate's grouping keys) ride it. Lean forbids `Σ`/nested
  inductives with local-variable parameters under the GADT — the
  flat package inductive is the encoding.
- `Measure` — a signature invocation over the aggregate input schema
  (the legacy's loose `List (AnyExpr)` args — the dependent spine
  cannot be matched at the measure's arity dispatch; named at the
  structure).
- `Rel` grows `aggregate` (output = grouping keys ++ measures), `sort`
  (keys + directions), `fetch` (limit/offset), `set` (BINARY — the
  typed layer's same-schema discipline; the legacy's N-input `SetRel`
  ports with its first consumer). The width bridge covers all four.
  LATER GROWTH: `keep` — the DROP projection (the caller-spelled
  output schema + the `Sublist` tie; `Query.TypedBridge`'s project
  lowering is the consumer). It has NO wire spelling (the wire's
  project node appends) — the lowering refuses; the width bridge's
  keep arm is the refusal tooth.

- `Schema` — a list of columns `name × Ty × nullable` (the legacy's
  shape, `Ty` in the type slot).
- `HasCol` — by-name column lookup through head/tail instance search,
  WITH the `resolves` proof field (the legacy's WF fix, kept): the
  instance search's answer is CHECKED — the resolved ordinal's column
  IS the looked-up triple.
- `Expr s t n` — typed expressions; `call` rides a `FunctionSig`
  (name + argument list + return) whose argument spine makes arity/
  type mismatches TYPE errors.
- `Rel inS outS` — the relation family (read/filter/project/join/
  aggregate/sort/fetch/set — the grown core — plus the fuller-plan
  rows: `cross` (the condition-free join) and `write` (the named
  write, schema-preserving, the alignment by construction); the ONLY
  exclusions left are the extension rels (the `Any` detail's opaque
  operator — no typed carrier) — every narrowing named in Proto's
  header).

THE TYPED-CORRECTNESS BRIDGE (the WF discipline): the lowering
`Expr.toProto` / `Rel.toProto` is `Except`-valued (types/literals
outside the wire fragment REFUSE loudly — `u64` has no substrait wire
spelling, the honest face of the retarget), and two theorems pin the
typed correctness of what it ACCEPTS:

- `Expr.toProto_ords` — every wire field ordinal a lowered expression
  references is in range (`< s.length`); the by-name discipline's
  correctness, standing on `HasCol.resolves`. The wire ordinal IS the
  instance's index by construction: the `field` constructor carries
  the NAME + the resolution proof, and the lowering emits
  `hcol.index` — the legacy's carried-`Column`-ordinal shape had a
  divergence hole (an ordinal independent of the instance); this port
  closes it.
- `Rel.toProto_width` — the wire width rule (`Proto.Rel.width`) agrees
  with the TYPED output schema's length; the computed-output-schema
  discipline survives the lowering.

The bridge theorems over the MUTUAL GADT are proof-carrying recursive
defs (the statement IS the return type's equation) — Lean's `induction`
tactic does not drive mutual inductives; the defs recurse structurally
(the legacy two-column pattern style, applied to proof content).

MECHANICS NOTES (06's trap discipline, paid once here):
- every lowering is a plain structural MATCH (no do-notation) — the
  equations reduce without monad-lemma plumbing;
- `Expr.field`'s `HasCol` proof is an EXPLICIT constructor argument
  (the instance-implicit spelling makes the proof inaccessible in
  downstream matches — the probe's finding); the authoring surface
  (`col`) hides it, the well-typedness discipline is unchanged: a
  field reference without its resolution proof is unconstructible;
- a docstring cannot precede a `mutual` block (the probe's finding) —
  plain `/- -/` comments there;
- the ordinals fold is the STRUCTURAL mutual family
  (`Proto.Expression.ordinals`/`ordinalsList`) — a flatMap spelling
  compiles to WF recursion, kernel-opaque, and the bridge's
  definitional reductions die (the probe's finding).

The five questions (notes/v3/01-core.md):
- root: Universe — the typed term families over the closed `Ty`.
- carrier grade: the GADT (a wrongly-typed plan is unconstructible);
  the bridge defs are the carrier's lowering face.
- spine reading: Typed → Proto (the wire) → Text (the canonical text).
- ladder rung: hand theorems of the small kind (structural recursion
  + `HasCol.resolves` + the lowering-length law).
- gate row: the axiom report (Substrait is gated); SubstraitTests
  carries the pins + the mandatory negative controls.
-/

import Substrait.Proto
import SchemaCore.Ty
import SchemaCore.Value

namespace Substrait.Typed

open SchemaCore

/-! ## schemas + by-name lookup -/

/-- A schema column: name × type × nullable (`nullable = true` means
    the wire NULLABLE; the typed layer never writes `unspecified`). -/
abbrev Col := String × Ty × Bool

/-- A schema is a list of columns, in ordinal order. -/
abbrev Schema := List Col

/-- The nth column of a schema, or `none` when out of range. -/
def Schema.get? : Schema → Nat → Option Col
  | [], _ => none
  | c :: _, 0 => some c
  | _ :: tl, n + 1 => Schema.get? tl n

/-- Column names only. -/
def Schema.names : Schema → List String
  | [] => []
  | (name, _, _) :: tl => name :: Schema.names tl

/-- A resolved column is IN RANGE: the lookup's index is a valid
    ordinal (the WF bridge's helper). -/
theorem Schema.get?_lt : ∀ (s : Schema) (i : Nat) (c : Col),
    Schema.get? s i = some c → i < s.length := by
  intro s
  induction s with
  | nil =>
      intro i c h
      simp [Schema.get?] at h
  | cons col tl ih =>
      intro i c h
      cases i with
      | zero =>
          simp only [Schema.get?] at h
          injection h with hc
          subst hc
          exact Nat.zero_lt_succ tl.length
      | succ n =>
          simp only [Schema.get?] at h
          exact Nat.succ_lt_succ (ih n c h)

/--
`HasCol s name t n` — evidence that column `name` sits at a known
ordinal in `s`, with type `t` and nullability `n`. Both `t` and `n` are
`outParam`s so `col "health" .i64 true` synthesizes the instance and
yields the ordinal. The search is purely syntactic (head/tail over
literal schema abbreviations); a misspelled column fails at elaboration
time. The `resolves` field is the WF discipline: the resolution is
CHECKED, not assumed (the legacy's fix, ported as content).
-/
class HasCol (s : Schema) (name : String) (t : outParam Ty) (n : outParam Bool) where
  /-- The ordinal of the column in `s`. -/
  index : Nat
  /-- The resolution is CORRECT: the schema's `index`-th column IS this
      (name, type, nullability) triple. -/
  resolves : Schema.get? s index = some (name, t, n)

instance (priority := high) : HasCol ((name, t, n) :: s) name t n where
  index := 0
  resolves := rfl

instance [h : HasCol s name t n] : HasCol ((name', t', n') :: s) name t n where
  index := h.index + 1
  resolves := h.resolves

/-! ## the typed expression family -/

/-- A scalar function signature: `name` identifies the extension
    function (the seed carries the name; the anchor ladder ports with
    the extensions section — the module header's note), `args` is the
    expected (type, nullability) list, `ret`/`retNullable` the result. -/
structure FunctionSig where
  name : String
  args : List (Ty × Bool)
  ret : Ty
  retNullable : Bool
deriving Repr, BEq, Inhabited

/- The expression family is a three-way mutual block: `Expr` calls
   `Args`; `Args` holds `Expr`s (the legacy's block shape, retargeted). -/
mutual
  /--
  `Expr s t n` — a well-typed expression over schema `s` returning a
  value of type `t` (SchemaCore's CLOSED `Ty`) with nullability `n`.
  `literal`'s payload IS `SchemaCore.Value t` — the legacy's parallel
  `LiteralValue` universe dies here (a mismatched payload is
  unconstructible, SchemaCore.Value's index discipline). `field` is a
  by-name column reference carrying its `HasCol` resolution proof
  EXPLICITLY (the mechanics note above); the WIRE ordinal is the
  instance's index — the lowering emits it, so the in-range property
  is by construction. `call` is a signature-typed scalar-function
  invocation whose argument spine matches the signature's argument
  list.
  -/
  inductive Expr (s : Schema) : Ty → Bool → Type where
    | literal : (n : Bool) → SchemaCore.Value t → Expr s t n
    | field : (name : String) → (t : Ty) → (n : Bool) → HasCol s name t n → Expr s t n
    | call : (sig : FunctionSig) → (args : Args s sig.args) → Expr s sig.ret sig.retNullable

  /--
  `Args s ts` — a heterogeneous argument spine indexed by the
  (type, nullability) sequence. The cons constructor pins `expr`'s
  `(t, n)` to the head of the index, so the spine's list is
  definitionally the signature's argument list.
  -/
  inductive Args (s : Schema) : List (Ty × Bool) → Type where
    | nil : Args s []
    | cons : (t : Ty) → (n : Bool) → Expr s t n → Args s rest → Args s ((t, n) :: rest)
end

/-- Smart constructor: a REQUIRED literal of type `t` from its value. -/
def litVal {s : Schema} {t : Ty} (v : SchemaCore.Value t) : Expr s t false :=
  Expr.literal false v

/-- A type-erased packaged expression: `(t, n, Expr s t n)` flattened
    (the legacy's `AnyExpr` shape, retargeted). Heterogeneous expression
    lists NOT tied to a signature — the aggregate's grouping keys —
    ride it: Lean forbids `Σ`/nested inductives with local-variable
    parameters under the GADT, so the flat package is the encoding. -/
inductive AnyExpr (s : Schema) : Type where
  | mk (t : Ty) (n : Bool) (e : Expr s t n)

/-- Package an expression with its indices. -/
def pack {s : Schema} {t : Ty} {n : Bool} (e : Expr s t n) : AnyExpr s :=
  AnyExpr.mk t n e

/-- The authoring surface's by-name column expression: `col "health"
    .i64 true` resolves through `HasCol` (head/tail instance search
    over the literal schema abbreviation); the resolution proof rides
    the term. -/
def col (name : String) (t : Ty) (n : Bool) [h : HasCol s name t n] : Expr s t n :=
  Expr.field name t n h

/-- Invoke a scalar function signature on a matching argument spine. -/
def call (sig : FunctionSig) (args : Args s sig.args) : Expr s sig.ret sig.retNullable :=
  Expr.call sig args

/-! ## the typed relation family -/

/-- An aggregate measure: a signature invocation over the aggregate
    input schema — the args are the legacy's LOOSE list (`List
    (AnyExpr s)`): the dependent `Args` spine cannot be matched at the
    measure's arity dispatch (the matcher's index-unification wall —
    the spine's index is a stuck projection), so the legacy's shape
    stays; the arity/refusal discipline moves to the evaluator (loud
    on mismatch). -/
structure Measure (s : Schema) where
  sig : FunctionSig
  args : List (AnyExpr s)

/-- A sort key: the ordering expression (type-erased) + its direction. -/
structure SortKey (s : Schema) where
  key : AnyExpr s
  direction : Proto.SortDirection

/-- A projection in `Rel.project`: a named output column backed by an
    expression over the projection's input schema. -/
structure Projection (sc : Schema) where
  name : String
  dtype : Ty
  nullable : Bool
  expr : Expr sc dtype nullable

/-- The output schema of a projection: input columns followed by the
    new columns (the COMPUTED output schema — 02-data-plane's
    relational center discipline). -/
def projectOut (p : Schema) (outs : List (Projection p)) : Schema :=
  p ++ outs.map (fun pr => (pr.name, pr.dtype, pr.nullable))

/-- The output schema of an aggregate: the grouping keys' (type,
    nullability) pairs, unnamed, then the measures' returns (the
    positions are the contract — the legacy's aggregateOut shape,
    retargeted). -/
def aggregateOut (s : Schema) (grouping : List (AnyExpr s))
    (measures : List (Measure s)) : Schema :=
  grouping.map (fun ae => match ae with | .mk t n _ => ("", t, n)) ++
    measures.map (fun m => ("", m.sig.ret, m.sig.retNullable))

/-! ## the keep witness (the drop projection's data spine) -/

/--
THE KEEP WITNESS — the Type-sorted face of an order-preserving
subselection. The wall-1 dissolve's carry: a `List.Sublist` proof is a
PROPOSITION, and the equation compiler refuses its elimination into
data (`Sublist.casesOn can only eliminate into Prop`) — a proof cannot
drive the kept-cells walk. The witness carries the SAME shape at
`Type`: `wdrop` skips an input column, `wkeep` keeps it onto the
output (the output index is the CALLER's spelled term, built by the
witness chain — never a transport). The invariant a `Sublist` proof
stated is here BY CONSTRUCTION: a `Keep s' outs` exists only as an
order-preserving subselection walk. `Keep.none` is the canonical
drop-everything witness (the `[] ⊆ s'` face, total — no proof needed
at the data level).
-/
inductive Keep : Schema → Schema → Type where
  | wnil : Keep [] []
  | wdrop (e : Col) : Keep s' outs → Keep (e :: s') outs
  | wkeep (e : Col) : Keep s' outs → Keep (e :: s') (e :: outs)

/-- The drop-everything witness: `[]`'s keep of ANY schema (the
canonical `subNil`'s data face — total, structural, proof-free). -/
def Keep.none : (s : Schema) → Keep s []
  | [] => .wnil
  | e :: s' => .wdrop e (Keep.none s')

/-- THE CONCATENATION WITNESS (the Keep pattern at the join — wall 2's
dissolve): the caller's spelled output schema IS the left schema's
elementwise append of the right — a `Type`-sorted walk, never a
transport. The Q bridge's join lowering spells `out := fieldsSchema
(ga ++ gb)` and builds the witness structurally (the `f :: rest`
append reduces definitionally), so the node's output index is the
spelled term and `evalRel`'s definitional match reductions survive
(the wall's teeth — the Keep precedent). The evaluator walks the
witness (`Row.appendW`, the data face). -/
inductive AppendCols : Schema → Schema → Schema → Type where
  | wnil : AppendCols [] r r
  | wcons (e : Col) : AppendCols s' r outs → AppendCols (e :: s') r (e :: outs)

/--
`Rel` — the schema-indexed relation family (read/filter/project/keep/
join/aggregate/sort/fetch/set/cross/write). `Rel inS outS` takes rows of `inS` and
produces rows of `outS`; each node's output schema is computed from its
arguments (read preserves, filter preserves, project appends, keep
DROPS to the caller's spelled subselection, join concatenates both
sides' outputs, join' concatenates over the SHARED input (the
caller-spelled output — the witness), aggregate returns grouping
keys ++ measures, sort/fetch preserve, set preserves the shared
output).
-/
inductive Rel : Schema → Schema → Type where
  | read (table : String) (schema : Schema) : Rel schema schema
  /-- The filter: ENDO ON THE ROW SCHEMA (the wire's width law — the
      filter node's output rows have exactly its input rows' schema),
      composition-honest on the PLAN: the sub-plan may be non-endo
      (the query bridge's select-over-join lowering is the consumer —
      the cond reads the sub-plan's OUTPUT schema `s`, the plan's
      input `inS` flows through). -/
  | filter (input : Rel inS s) (cond : Expr s .bool n) : Rel inS s
  | project (input : Rel s p) (outs : List (Projection p)) : Rel s (projectOut p outs)
  /-- THE DROP PROJECTION (the wall-1 dissolve, `Query.TypedBridge`'s
      project lowering is the consumer): the output schema is the
      CALLER'S spelling, carried by the keep witness `w : Keep s' outs`
      (the Type-sorted subselection walk above — a `List.Sublist`
      PROOF cannot drive the evaluator's data walk, its elimination
      into data is refused; the witness is the proof's data face). A
      keep that is not an order-preserving subselection is
      unconstructible, and the output index is the spelled term (never
      a transport), so `evalRel`'s definitional match reductions
      survive (the wall's teeth). The wire's project node APPENDS
      (`Proto.Rel.width`), so a keep has no wire spelling in the narrow
      fragment — the lowering refuses loudly (the emit lane ports with
      its consumer). -/
  | keep (input : Rel s s') (w : Keep s' outs) : Rel s outs
  | join (left : Rel sl sl') (right : Rel sr sr')
         (cond : Expr (sl' ++ sr') .bool n)
         (joinType : Proto.JoinType) : Rel (sl ++ sr) (sl' ++ sr')
  /-- THE SHARED-BASE JOIN (wall 2's dissolve, `Query.TypedBridge`'s
      equijoin lowering is the consumer): BOTH children read the SAME
      input stream — the query lane's reading (`Q.join`'s children
      share the base), no doubled stream, no per-node replication. The
      output schema is the CALLER'S spelling, carried by the
      concatenation witness `w : AppendCols sl' sr' outs` (the
      Keep-witness discipline: the Type-sorted data face, the spelled
      index — never a transport), so `evalRel`'s definitional match
      reductions survive. The wire spelling refuses loudly (the wire's
      join node's children own their inputs; the emit lane ports with
      its consumer — the keep precedent). WEIGHT FACE (02 §4, the F5
      note): the join node MULTIPLIES the children's weights at each
      ON-satisfying pair — over Bool the multiply is AND (set
      semantics, this evaluator's face); the weight-polymorphic
      reading is the query lane's `joinPairsW`, and the optimizer's
      equational theory (F5) consumes the semiring laws, never this
      list walk. -/
  | join' (left : Rel s sl') (right : Rel s sr')
          (w : AppendCols sl' sr' outs)
          (cond : Expr (sl' ++ sr') .bool n)
          (joinType : Proto.JoinType) : Rel s outs
  /-- Group + measure: the output schema is the grouping keys' types
      then the measures' return types (BOTH computed — the positions
      are the contract; the legacy's unnamed aggregate columns). -/
  | aggregate (input : Rel s s) (grouping : List (AnyExpr s))
              (measures : List (Measure s)) : Rel s (aggregateOut s grouping measures)
  /-- Order by keys (the row SET is unchanged — schema-preserving; the
      ORDER is not in the carrier: an evaluation-side discipline). -/
  | sort (input : Rel s s) (orderBy : List (SortKey s)) : Rel s s
  /-- Limit/offset window (schema-preserving). -/
  | fetch (input : Rel s s) (limit offset : Option Nat) : Rel s s
  /-- The binary set operation — BOTH sides take the same input rows
      and produce the same output schema (the typed layer's
      same-schema discipline makes two the honest arity). -/
  | set (op : Proto.SetOp) (left : Rel s s') (right : Rel s s') : Rel s s'
  /-- THE CROSS JOIN (the condition-free join — the wire's `CrossRel
      { left = 2, right = 3 }`): the `join` node at the always-true
      condition, no separate evaluation kernel (the evaluator rides
      `evalJoin` at the literal-true cond — the shared width rule's
      face). -/
  | cross (left : Rel sl sl') (right : Rel sr sr') : Rel (sl ++ sr) (sl' ++ sr')
  /-- THE WRITE (the wire's `WriteRel { named_table = 1, table_schema
      = 3, op = 4, input = 5 }`): write the input rows into the named
      table. THE ALIGNMENT BY CONSTRUCTION: the written table's schema
      IS the input's output schema (the proto's "must align with Rel
      input" discipline, forced — no separate schema datum to drift;
      the lowering WRITES the echo face, the decode REFUSES the
      disagreement — SS0012). SCHEMA-PRESERVING (the write's output
      reads back the written table — the spec's face; the width law's
      shared rule). The evaluator refuses loudly (the evaluator is
      read-only — the write executes at the consumer; the named
      boundary, never a fabricated side effect). -/
  | write (names : List String) (op : Proto.WriteOp) (input : Rel s s') : Rel s s'

/-! ## the lowering (Typed → Proto) — plain matches, `rfl` equations -/

/-- Lower a schema type to the wire (the NARROW fragment: `u64` has no
    substrait wire spelling and non-scalar types have no wire rows yet —
    both REFUSE loudly; the lowering is honest about its fragment,
    never lossy). -/
def toProtoType : Ty → Except String Proto.PType
  | .bool => .ok (.bool .required)
  | .i64 => .ok (.i64 .required)
  | .string => .ok (.string .required)
  | .list e =>
      match toProtoType e with
      | .ok p => .ok (.list p .required)
      | .error e => .error e
  | _ => .error "type outside the wire fragment (u64 has no substrait wire spelling; option/result/map/set/bounded port with their grammar rows)"

/-- Set the wire nullability of a lowered type (always explicit — the
    typed layer never writes `unspecified`). -/
def withNullable (n : Bool) (pt : Proto.PType) : Proto.PType :=
  pt.setNull (if n then .nullable else .required)

/-- Lower a typed literal payload (the retarget's face:
    `SchemaCore.Value t` → the wire literal, total over the narrow
    scalar fragment, refusing everything else). -/
def toProtoLiteral : (t : Ty) → SchemaCore.Value t → Except String Proto.LiteralType
  | .bool, .bool b => .ok (.bool b)
  | .i64, .i64 v => .ok (.i64 v.toInt)
  | .string, .string s => .ok (.string s)
  | _, _ => .error "literal payload outside the wire fragment"

/-- Lower ONE schema column to its wire type (explicit nullability). -/
def colType : Col → Except String Proto.PType
  | (_, t, n) =>
      match toProtoType t with
      | .ok pt => .ok (withNullable n pt)
      | .error e => .error e

/-- THE ONE EXCEPT LIST-WALK (the 15-patterns shape): walk a list
    positionally with a fallible per-element step, failing fast — the
    first error wins, else the ok's append. The lowering's five
    positional walks (cols / exprs / anyExprs / measures / sortKeys)
    are instances — ONE recursion, ONE length law. -/
def walkProto {α β : Type} (f : α → Except String β) :
    List α → Except String (List β)
  | [] => .ok []
  | x :: rest =>
      match f x, walkProto f rest with
      | .ok b, .ok bs => .ok (b :: bs)
      | .error e, _ => .error e
      | _, .error e => .error e

/-- The walk's length law: a successful walk produces EXACTLY one wire
    field per element (the width bridge's per-arm step, ONCE). -/
theorem walkProto_ok_length : ∀ {α β : Type} (f : α → Except String β)
    (xs : List α) (ys : List β), walkProto f xs = .ok ys →
    ys.length = xs.length := by
  intro α β f xs
  induction xs with
  | nil =>
      intro ys h
      injection h with h2
      subst h2
      rfl
  | cons x tl ih =>
      intro ys h
      simp only [walkProto] at h
      cases h1 : f x with
      | error _ => rw [h1] at h; simp at h
      | ok b =>
          rw [h1] at h
          cases h2 : walkProto f tl with
          | error _ => rw [h2] at h; simp at h
          | ok bs =>
              rw [h2] at h
              simp only [Except.ok.injEq] at h
              subst h
              simp [ih bs h2]

/-- Lower a schema's columns, positionally (the read arm's base-schema
    fields). -/
def colsToProto : List Col → Except String (List Proto.PType) :=
  walkProto colType

/-- The lowering's length law: a successful column lowering produces
    EXACTLY one wire field per column (the width bridge's read-arm
    step). -/
theorem colsToProto_ok_length : ∀ (xs : List Col) (ys : List Proto.PType),
    colsToProto xs = .ok ys → ys.length = xs.length :=
  fun xs ys h => walkProto_ok_length colType xs ys h

/- Lower a typed expression to the wire (ordinals are the data the
   instance search computed; the payload types refuse loudly). -/
mutual
  def Expr.toProto : {s : Schema} → {t : Ty} → {n : Bool} →
      Expr s t n → Except String Proto.Expression :=
    fun {_ _ _} e =>
      match e with
      | .literal n v =>
          match toProtoLiteral _ v with
          | .ok lt => .ok (.literal { literalType := lt, nullable := n })
          | .error e => .error e
      | .field nm _ _ hcol => .ok (.field { ordinal := hcol.index })
      | .call sig args =>
          match args.toProto with
          | .ok ps =>
              match toProtoType sig.ret with
              | .ok out =>
                  .ok (.scalarFunction sig.name ps (withNullable sig.retNullable out))
              | .error e => .error e
          | .error e => .error e

  def Args.toProto : {s : Schema} → {ts : List (Ty × Bool)} →
      Args s ts → Except String (List Proto.Expression) :=
    fun {_ _} a =>
      match a with
      | .nil => .ok []
      | .cons _ _ e rest =>
          match e.toProto with
          | .ok p =>
              match rest.toProto with
              | .ok ps => .ok (p :: ps)
              | .error e => .error e
          | .error e => .error e
end

/- THE WF BRIDGE (the by-name correctness): every wire field ordinal a
   lowered expression references is IN RANGE of its schema. The typed
   layer's by-name discipline is correct by construction — the theorem
   reads the construction back off the wire value. Proof-carrying
   recursive defs over the mutual GADT (the mechanics note above). -/
mutual
  theorem Expr.toProto_ords : {s : Schema} → {t : Ty} → {n : Bool} →
      (e : Expr s t n) → (p : Proto.Expression) → e.toProto = .ok p →
      Proto.Expression.ordsLt p s.length = true :=
    fun {s _ _} e =>
      match e with
      | .literal _ _ =>
          fun p hp => by
            simp only [Expr.toProto] at hp
            cases hl : toProtoLiteral _ _ with
            | error _ => rw [hl] at hp; simp at hp
            | ok lt =>
                rw [hl] at hp
                simp only [Except.ok.injEq] at hp
                subst hp
                simp [Proto.Expression.ordsLt, Proto.Expression.ordinals]
      | .field nm t' n' hcol =>
          fun p hp => by
            simp only [Expr.toProto] at hp
            simp only [Except.ok.injEq] at hp
            subst hp
            -- the ordinal is in range BY the HasCol resolution proof
            simp only [Proto.Expression.ordsLt, Proto.Expression.ordinals,
              List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨Schema.get?_lt s hcol.index (nm, t', n') hcol.resolves, trivial⟩
      | .call sig args =>
          fun p hp => by
            simp only [Expr.toProto] at hp
            cases ha : args.toProto with
            | error _ => rw [ha] at hp; simp at hp
            | ok ps =>
                rw [ha] at hp
                cases ho : toProtoType sig.ret with
                | error _ => rw [ho] at hp; simp at hp
                | ok out =>
                    rw [ho] at hp
                    simp only [Except.ok.injEq] at hp
                    subst hp
                    exact args.toProto_ords ps ha

  theorem Args.toProto_ords : {s : Schema} → {ts : List (Ty × Bool)} →
      (a : Args s ts) → (ps : List Proto.Expression) → a.toProto = .ok ps →
      Proto.Expression.ordsLtList ps s.length = true :=
    fun {s _} a =>
      match a with
      | .nil =>
          fun ps hp => by
            simp only [Args.toProto] at hp
            simp only [Except.ok.injEq] at hp
            subst hp
            simp [Proto.Expression.ordsLtList, Proto.Expression.ordinalsList]
      | .cons _ _ e rest =>
          fun ps hp => by
            simp only [Args.toProto] at hp
            cases he : e.toProto with
            | error _ => rw [he] at hp; simp at hp
            | ok p =>
                rw [he] at hp
                cases hr : rest.toProto with
                | error _ => rw [hr] at hp; simp at hp
                | ok ps' =>
                    rw [hr] at hp
                    simp only [Except.ok.injEq] at hp
                    subst hp
                    have h1 := e.toProto_ords p he
                    have h2 := rest.toProto_ords ps' hr
                    simp only [Proto.Expression.ordsLtList, Proto.Expression.ordinalsList,
                      List.all_append,
                      Bool.and_eq_true] at ⊢
                    exact ⟨h1, h2⟩
end

/-- Lower a packaged expression (the grouping keys' walk). -/
def AnyExpr.toProto {s : Schema} (ae : AnyExpr s) :
    Except String Proto.Expression :=
  match ae with
  | .mk _ _ e => e.toProto

/-- The projections' expressions, positionally (the project arm's list
    walk — the ONE list-map shape for the lowering). -/
def exprListToProto {p : Schema} : List (Projection p) →
    Except String (List Proto.Expression) :=
  walkProto (fun pr => pr.expr.toProto)

/-- The projections' length law (the width bridge's project-arm step). -/
theorem exprListToProto_ok_length : ∀ {p : Schema} (xs : List (Projection p))
    (ys : List Proto.Expression), exprListToProto xs = .ok ys →
    ys.length = xs.length :=
  fun xs ys h => walkProto_ok_length _ xs ys h

/-- The grouping keys' expressions, positionally (the aggregate arm's
    list walk — the same fold shape). -/
def anyExprListToProto {p : Schema} : List (AnyExpr p) →
    Except String (List Proto.Expression) :=
  walkProto AnyExpr.toProto

/-- The grouping walk's length law (the width bridge's aggregate-arm
    step, grouping half). -/
theorem anyExprListToProto_ok_length : ∀ {p : Schema} (xs : List (AnyExpr p))
    (ys : List Proto.Expression), anyExprListToProto xs = .ok ys →
    ys.length = xs.length :=
  fun xs ys h => walkProto_ok_length _ xs ys h

/-- Lower one aggregate measure: the sig invocation as a wire
    scalar-function expression over the LOOSE arg list (the
    `anyExprListToProto` walk — ONE lowering for the erased args). -/
def measureToProto {p : Schema} (m : Measure p) :
    Except String Proto.Expression :=
  match anyExprListToProto m.args with
  | .ok ps =>
      match toProtoType m.sig.ret with
      | .ok out =>
          .ok (.scalarFunction m.sig.name ps (withNullable m.sig.retNullable out))
      | .error e => .error e
  | .error e => .error e

/-- The measures, positionally. -/
def measureListToProto {p : Schema} : List (Measure p) →
    Except String (List Proto.Expression) :=
  walkProto measureToProto

/-- The measures' length law (the width bridge's aggregate-arm step,
    measure half). -/
theorem measureListToProto_ok_length : ∀ {p : Schema} (xs : List (Measure p))
    (ys : List Proto.Expression), measureListToProto xs = .ok ys →
    ys.length = xs.length :=
  fun xs ys h => walkProto_ok_length _ xs ys h

/-- Lower one sort key (the direction rides the wire field). -/
def sortKeyToProto {p : Schema} (k : SortKey p) :
    Except String Proto.SortField :=
  match k.key.toProto with
  | .ok e => .ok { expr := e, direction := k.direction }
  | .error err => .error err

/-- The sort keys, positionally. -/
def sortKeyListToProto {p : Schema} : List (SortKey p) →
    Except String (List Proto.SortField) :=
  walkProto sortKeyToProto

/-! ## the relation lowering + the width bridge -/

/-- Lower a typed rel to a wire rel (the computed schemas survive as
    the wire's base schema / expression lists). -/
def Rel.toProto : {inS : Schema} → {outS : Schema} →
    Rel inS outS → Except String Proto.Rel :=
  fun {_ _} rel =>
    match rel with
    | .read table schema =>
        match colsToProto schema with
        | .ok fields =>
            .ok (.read (.namedTable [table])
              (some { fields := fields, names := schema.names }))
        | .error e => .error e
    | .filter input cond =>
        match input.toProto with
        | .ok i =>
            match cond.toProto with
            | .ok c => .ok (.filter c i)
            | .error e => .error e
        | .error e => .error e
    | .project input outs =>
        match input.toProto with
        | .ok i =>
            match exprListToProto outs with
            | .ok es => .ok (.project es i)
            | .error e => .error e
        | .error e => .error e
    | .keep _ _ =>
        .error "typed: the keep projection (column drop) has no wire spelling — \
          the wire's project node appends (the emit lane ports with its consumer)"
    | .join left right cond jt =>
        match left.toProto, right.toProto, cond.toProto with
        | .ok l, .ok r, .ok c => .ok (.join jt l r c)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
    | .join' _ _ _ _ _ =>
        .error "typed: the shared-base join has no wire spelling — the wire's \
          join node's children own their inputs (the doubled-stream reading); \
          the shared-base reading is the query lane's, the emit lane ports \
          with its consumer (the keep precedent)"
    | .aggregate input grouping measures =>
        match input.toProto, anyExprListToProto grouping,
            measureListToProto measures with
        | .ok i, .ok gs, .ok ms => .ok (.aggregate gs ms i)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
    | .sort input keys =>
        match input.toProto, sortKeyListToProto keys with
        | .ok i, .ok ks => .ok (.sort ks i)
        | .error e, _ => .error e
        | _, .error e => .error e
    | .fetch input limit offset =>
        match input.toProto with
        | .ok i => .ok (.fetch limit offset i)
        | .error e => .error e
    | .set op left right =>
        match left.toProto, right.toProto with
        | .ok l, .ok r => .ok (.set op l r)
        | .error e, _ => .error e
        | _, .error e => .error e
    | .cross left right =>
        match left.toProto, right.toProto with
        | .ok l, .ok r => .ok (.cross l r)
        | .error e, _ => .error e
        | _, .error e => .error e
    | @Rel.write _ outS names op input =>
        match input.toProto with
        | .ok i =>
            match colsToProto outS with
            | .ok fields =>
                .ok (Proto.Rel.write names op
                  { fields := fields, names := outS.names } i)
            | .error e => .error e
        | .error e => .error e

/-- THE WF BRIDGE (the width agreement): the wire width rule
    (`Proto.Rel.width`) equals the TYPED output schema's length, for
    every rel the lowering accepts. The computed-output-schema
    discipline survives the lowering — the wire's width and the type's
    width cannot drift. -/
theorem Rel.toProto_width : ∀ {inS : Schema} {outS : Schema} (rel : Rel inS outS)
    (p : Proto.Rel), rel.toProto = .ok p → p.width = outS.length := by
  intro inS outS rel
  induction rel with
  | read table schema =>
      intro p hp
      simp only [Rel.toProto] at hp
      cases hf : colsToProto schema with
      | error _ => rw [hf] at hp; simp at hp
      | ok fields =>
          rw [hf] at hp
          simp only [Except.ok.injEq] at hp
          subst hp
          have hlen := colsToProto_ok_length schema fields hf
          simp [Proto.Rel.width, hlen]
  | filter input cond ih =>
      intro p hp
      simp only [Rel.toProto] at hp
      cases hi : input.toProto with
      | error _ => rw [hi] at hp; simp at hp
      | ok i =>
          rw [hi] at hp
          cases hc : cond.toProto with
          | error _ => rw [hc] at hp; simp at hp
          | ok c =>
              rw [hc] at hp
              simp only [Except.ok.injEq] at hp
              subst hp
              have hw := ih i hi
              simp [Proto.Rel.width, hw]
  | project input outs ih =>
      intro p hp
      simp only [Rel.toProto] at hp
      cases hi : input.toProto with
      | error _ => rw [hi] at hp; simp at hp
      | ok i =>
          rw [hi] at hp
          cases he : exprListToProto outs with
          | error _ => rw [he] at hp; simp at hp
          | ok es =>
              rw [he] at hp
              simp only [Except.ok.injEq] at hp
              subst hp
              have hw := ih i hi
              have helen := exprListToProto_ok_length outs es he
              simp [Proto.Rel.width, hw, helen, projectOut, List.length_map]
  | keep input _ ih =>
      -- the keep arm ALWAYS refuses (no wire spelling) — the width
      -- law's domain is the accepted rels; the refusal is the tooth
      intro p hp
      simp only [Rel.toProto] at hp
      simp at hp
  | join' _ _ _ _ _ ihl ihr =>
      -- the shared-base join ALWAYS refuses (no wire spelling) — same
      -- disposition as the keep arm above
      intro p hp
      simp only [Rel.toProto] at hp
      simp at hp
  | join left right cond jt ihl ihr =>
      intro p hp
      simp only [Rel.toProto] at hp
      cases hl : left.toProto with
      | error _ => rw [hl] at hp; simp at hp
      | ok l =>
          rw [hl] at hp
          cases hr : right.toProto with
          | error _ => rw [hr] at hp; simp at hp
          | ok r =>
              rw [hr] at hp
              cases hc : cond.toProto with
              | error _ => rw [hc] at hp; simp at hp
              | ok c =>
                  rw [hc] at hp
                  simp only [Except.ok.injEq] at hp
                  subst hp
                  have hwl := ihl l hl
                  have hwr := ihr r hr
                  simp [Proto.Rel.width, hwl, hwr, Proto.JoinType.width_add,
                    List.length_append]
  | aggregate input grouping measures ih =>
      intro p hp
      simp only [Rel.toProto] at hp
      cases hi : input.toProto with
      | error _ => rw [hi] at hp; simp at hp
      | ok i =>
          rw [hi] at hp
          cases hg : anyExprListToProto grouping with
          | error _ => rw [hg] at hp; simp at hp
          | ok gs =>
              rw [hg] at hp
              cases hm : measureListToProto measures with
              | error _ => rw [hm] at hp; simp at hp
              | ok ms =>
                  rw [hm] at hp
                  simp only [Except.ok.injEq] at hp
                  subst hp
                  have hw := ih i hi
                  have hgl := anyExprListToProto_ok_length grouping gs hg
                  have hml := measureListToProto_ok_length measures ms hm
                  simp [Proto.Rel.width, hgl, hml, aggregateOut,
                    List.length_map]
  | sort input keys ih =>
      intro p hp
      simp only [Rel.toProto] at hp
      cases hi : input.toProto with
      | error _ => rw [hi] at hp; simp at hp
      | ok i =>
          rw [hi] at hp
          cases hk : sortKeyListToProto keys with
          | error _ => rw [hk] at hp; simp at hp
          | ok ks =>
              rw [hk] at hp
              simp only [Except.ok.injEq] at hp
              subst hp
              have hw := ih i hi
              simp [Proto.Rel.width, hw]
  | fetch input _ _ ih =>
      intro p hp
      simp only [Rel.toProto] at hp
      cases hi : input.toProto with
      | error _ => rw [hi] at hp; simp at hp
      | ok i =>
          rw [hi] at hp
          simp only [Except.ok.injEq] at hp
          subst hp
          have hw := ih i hi
          simp [Proto.Rel.width, hw]
  | cross left right ihl ihr =>
      intro p hp
      simp only [Rel.toProto] at hp
      cases hl : left.toProto with
      | error _ => rw [hl] at hp; simp at hp
      | ok l =>
          rw [hl] at hp
          cases hr : right.toProto with
          | error _ => rw [hr] at hp; simp at hp
          | ok r =>
              rw [hr] at hp
              simp only [Except.ok.injEq] at hp
              subst hp
              have hwl := ihl l hl
              have hwr := ihr r hr
              simp [Proto.Rel.width, hwl, hwr, List.length_append]
  | write _ _ input ih =>
      intro p hp
      simp only [Rel.toProto] at hp
      cases hi : input.toProto with
      | error _ => rw [hi] at hp; simp at hp
      | ok i =>
          rw [hi] at hp
          cases hf : colsToProto _ with
          | error _ => rw [hf] at hp; simp at hp
          | ok fields =>
              rw [hf] at hp
              simp only [Except.ok.injEq] at hp
              subst hp
              have hw := ih i hi
              simp [Proto.Rel.width, hw]
  | set _ left right ihl _ihr =>
      -- BOTH sides produce the same output schema (the typed layer's
      -- same-schema discipline); the wire width reads the LEFT side's
      -- (the binary narrowing's rule — the right side's law is its
      -- twin, unused by the width rule)
      intro p hp
      simp only [Rel.toProto] at hp
      cases hl : left.toProto with
      | error _ => rw [hl] at hp; simp at hp
      | ok l =>
          rw [hl] at hp
          cases hr : right.toProto with
          | error _ => rw [hr] at hp; simp at hp
          | ok r =>
              rw [hr] at hp
              simp only [Except.ok.injEq] at hp
              subst hp
              have hwl := ihl l hl
              simp [Proto.Rel.width, hwl]

/-! ## the plan container -/

/-- First-use append (the dedup discipline: a name already present is
    kept at its FIRST position). Acc-first (the fold's argument
    order). -/
def addFn (acc : List String) (x : String) : List String :=
  if x ∈ acc then acc else acc ++ [x]

/-- addFn preserves membership (the collection law's step). -/
theorem mem_addFn_of_mem (x y : String) (acc : List String) (h : x ∈ acc) :
    x ∈ addFn acc y := by
  unfold addFn
  split <;> simp_all

/-- addFn ADDS its own argument (the collection law's tooth). -/
theorem mem_addFn_self (x : String) (acc : List String) : x ∈ addFn acc x := by
  unfold addFn
  split
  · rename_i hc; simp_all
  · simp

/-- First-use dedup over a name list (foldl of addFn). -/
def dedupFns (xs : List String) : List String :=
  xs.foldl addFn []

/- The scalar-function names an expression uses (the name before its
   arguments' — the legacy toCtx's dot-notation rule). -/
mutual
  def Expr.fns {s : Schema} {t : Ty} {n : Bool} (e : Expr s t n) : List String :=
    match e with
    | .literal _ _ => []
    | .field _ _ _ _ => []
    | .call sig args => sig.name :: args.fns

  def Args.fns {s : Schema} {ts : List (Ty × Bool)} (a : Args s ts) : List String :=
    match a with
    | .nil => []
    | .cons _ _ e rest => e.fns ++ rest.fns
end

/-- The scalar-function names a packaged expression uses (the
    grouping keys' walk's face). -/
def AnyExpr.fns {s : Schema} (ae : AnyExpr s) : List String :=
  match ae with
  | .mk _ _ e => e.fns

/-- The scalar-function names a rel uses, children first (the legacy
    toCtx's bottom-up discipline). -/
def Rel.fns {inS : Schema} {outS : Schema} (rel : Rel inS outS) : List String :=
  match rel with
  | .read _ _ => []
  | .filter input cond => input.fns ++ cond.fns
  | .project input outs => input.fns ++ outs.flatMap (fun pr => pr.expr.fns)
  | .keep input _ => input.fns
  | .join left right cond _ => left.fns ++ right.fns ++ cond.fns
  | .join' left right _ cond _ => left.fns ++ right.fns ++ cond.fns
  | .aggregate input grouping measures =>
      input.fns ++ grouping.flatMap AnyExpr.fns ++
        measures.flatMap (fun m => m.sig.name :: m.args.flatMap AnyExpr.fns)
  | .sort input keys => input.fns ++ keys.flatMap (fun k => k.key.fns)
  | .fetch input _ _ => input.fns
  | .set _ left right => left.fns ++ right.fns
  | .cross left right => left.fns ++ right.fns
  | .write _ _ input => input.fns

/-- Lower a typed rel to a full plan: the single top-level relation +
    the distinct function names (first-use order — the seed's stand-in
    for the wire's extension-declaration table). -/
def Rel.toPlan {inS : Schema} {outS : Schema} (rel : Rel inS outS) :
    Except String Proto.Plan :=
  match rel.toProto with
  | .ok p => .ok { functions := dedupFns rel.fns, relations := [.rel p] }
  | .error e => .error e

/-- The fold's LEFT law: the accumulator's members survive the fold
    (addFn never removes — mem_addFn_of_mem at each step). -/
theorem mem_foldl_addFn_left : ∀ (xs : List String) (acc : List String) (x : String),
    x ∈ acc → x ∈ xs.foldl addFn acc := by
  intro xs
  induction xs with
  | nil => intro acc x h; exact h
  | cons y tl ih =>
      intro acc x h
      show x ∈ tl.foldl addFn (addFn acc y)
      exact ih (addFn acc y) x (mem_addFn_of_mem x y acc h)

/-- The fold's RIGHT law: every collected name survives its own fold
    (the declaration law's engine); the accumulator is quantified
    INSIDE (the induction's shape requirement). -/
theorem mem_foldl_addFn_right : ∀ (xs : List String) (x : String), x ∈ xs →
    ∀ acc, x ∈ xs.foldl addFn acc := by
  intro xs
  induction xs with
  | nil => intro x h; cases h
  | cons y tl ih =>
      intro x h
      rcases List.mem_cons.mp h with hxy | htl
      · intro acc
        rw [hxy]
        exact mem_foldl_addFn_left tl (addFn acc y) y (mem_addFn_self y acc)
      · intro acc
        exact ih x htl (addFn acc y)

/-- THE DECLARATION LAW: every function name the rel uses is declared
    in its own plan (the anchor ladder's correctness face, at the
    seed's granularity: a plan's scalar functions are all declared,
    at their first-use position). -/
theorem Rel.toPlan_fns_declared : ∀ {inS : Schema} {outS : Schema} (rel : Rel inS outS)
    (plan : Proto.Plan), rel.toPlan = .ok plan →
    ∀ n ∈ rel.fns, n ∈ plan.functions := by
  intro inS outS rel plan hp
  cases hp0 : rel.toProto with
  | error _ =>
      rw [Rel.toPlan, hp0] at hp; simp at hp
  | ok p =>
      rw [Rel.toPlan, hp0] at hp
      simp only [Except.ok.injEq] at hp
      subst hp
      intro n hn
      exact mem_foldl_addFn_right rel.fns n hn []

end Substrait.Typed
