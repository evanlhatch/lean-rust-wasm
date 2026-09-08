/-
# Substrait.Eval

A minimal in-memory evaluator for the read side of the typed language — a
definitional second reading alongside `toProto` (the two-readings idea).  It
interprets `Read` (via a supplied `Reader`), `Filter`, `Sort`, `Fetch` and
`Set` (union) over rows; `Project` has a typed building block (`evalProject`)
and a pipeline that ends in a non-preserving schema must use it directly.
`Join` and `Aggregate` are interpreted (`evalJoin` / `evalAggregate`);
`Write` and `ExtensionSingle` are out of scope and fail loudly.

Nullability rule: a cell is `none` exactly when its typed nullability says so;
runtime evaluation treats a missing cell as SQL NULL (comparisons against NULL
yield false, arithmetic yields NULL).

The evaluator only knows the built-in kernels (add/sub/mul, comparisons,
and/or).  Any other function name fails loudly — the extension catalogue is
not consulted.

**Intent/cmd notes** (v0, Lean 4.33): `Sigma` patterns are written as
`Sigma.mk <TYPE> <value>` (leading-dot anonymous-ctor patterns like
`⟨.i32, …⟩` cannot elide the type here), and `Expr`/`Args` evaluation is a
`mutual` block with value-first signatures so dot notation (`e.evalCell row`,
`args.eval row`) resolves.
-/
import Substrait.Typed.Rel

namespace Substrait.Typed

/-! ## Runtime values -/

/-- A runtime cell value, indexed by its type. -/
inductive Cell : SType → Type where
  | bool   : Bool → Cell .bool
  | i8     : Int → Cell .i8
  | i16    : Int → Cell .i16
  | i32    : Int → Cell .i32
  | i64    : Int → Cell .i64
  | fp32   : Float → Cell .fp32
  | fp64   : Float → Cell .fp64
  | string : String → Cell .string
  | binary : List UInt8 → Cell .binary

/-- A runtime row: a heterogeneous list of cells indexed by the schema. -/
inductive Row : Schema → Type where
  | nil : Row []
  | cons : Option (Cell t) → Row s → Row ((name, t, n) :: s)

/-- A table is a list of rows. -/
abbrev Table (s : Schema) := List (Row s)

/-- The cell at ordinal `i` (with its runtime type), or `none` when out of range. -/
def Row.get : Row s → Nat → Option (Σ t, Option (Cell t))
  | .nil, _ => none
  | .cons c _, 0 => some ⟨_, c⟩
  | .cons _ r, k + 1 => r.get k

/-- Total comparison for a scalar type with `LT` (decidability pinned). -/
def cmpVia (a b : α) [LT α] [Decidable (a < b)] [Decidable (b < a)] : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

/-- Bool ordering: false < true. -/
def cmpBool (a b : Bool) : Ordering :=
  match a, b with
  | false, false => .eq | true, true => .eq
  | false, true  => .lt | true, false => .gt

/-- Compare two cells of the same (runtime) type.  Unusual types compare equal. -/
def Cell.cmp : Cell t → Cell t → Ordering
  | .bool a, .bool b       => cmpBool a b
  | .i8 a, .i8 b           => cmpVia a b
  | .i16 a, .i16 b         => cmpVia a b
  | .i32 a, .i32 b         => cmpVia a b
  | .i64 a, .i64 b         => cmpVia a b
  | .fp32 a, .fp32 b       => cmpVia a b
  | .fp64 a, .fp64 b       => cmpVia a b
  | .string a, .string b   => cmpVia a b
  | _, _ => .eq

/-- Compare two runtime-typed cells (pairwise match — no casts). -/
def Cell.cmp' : (Σ t, Cell t) → (Σ t, Cell t) → Ordering
  | Sigma.mk SType.bool (.bool a),   Sigma.mk SType.bool (.bool b)   => cmpBool a b
  | Sigma.mk SType.i8 (.i8 a),       Sigma.mk SType.i8 (.i8 b)       => cmpVia a b
  | Sigma.mk SType.i16 (.i16 a),     Sigma.mk SType.i16 (.i16 b)     => cmpVia a b
  | Sigma.mk SType.i32 (.i32 a),     Sigma.mk SType.i32 (.i32 b)     => cmpVia a b
  | Sigma.mk SType.i64 (.i64 a),     Sigma.mk SType.i64 (.i64 b)     => cmpVia a b
  | Sigma.mk SType.fp32 (.fp32 a),   Sigma.mk SType.fp32 (.fp32 b)   => cmpVia a b
  | Sigma.mk SType.fp64 (.fp64 a),   Sigma.mk SType.fp64 (.fp64 b)   => cmpVia a b
  | Sigma.mk SType.string (.string a), Sigma.mk SType.string (.string b) => cmpVia a b
  | _, _ => .eq

/-- Compare two rows at a column ordinal (null cells compare equal to everything). -/
def Row.cmpAt (a b : Row s) (ord : Nat) : Ordering :=
  match a.get ord, b.get ord with
  | some ⟨_, some v1⟩, some ⟨_, some v2⟩ => Cell.cmp' ⟨_, v1⟩ ⟨_, v2⟩
  | _, _ => .eq

/-- Compare two rows by a key list, in order (`.eq` falls through). -/
def Row.cmpKeys (keys : List (SortKey s)) (a b : Row s) : Ordering :=
  keys.foldl (fun acc k =>
    match acc with
    | .eq => Row.cmpAt a b k.col.ordinal
    | _ => acc) .eq

/-! ## Expression evaluation -/

/-- Interpret a literal payload as a cell. -/
def litToCell : LiteralValue t → Cell t
  | .bool b   => .bool b
  | .i8 v     => .i8 v
  | .i16 v    => .i16 v
  | .i32 v    => .i32 v
  | .i64 v    => .i64 v
  | .fp32 v   => .fp32 v
  | .fp64 v   => .fp64 v
  | .string s => .string s
  | .binary b => .binary b

/-- Cast a runtime cell to a pinned type, checking the runtime type. -/
def castCell (t : SType) (x : Σ u, Cell u) : Option (Cell t) :=
  match t, x with
  | SType.bool,   Sigma.mk SType.bool v   => some v
  | SType.i8,     Sigma.mk SType.i8 v     => some v
  | SType.i16,    Sigma.mk SType.i16 v    => some v
  | SType.i32,    Sigma.mk SType.i32 v    => some v
  | SType.i64,    Sigma.mk SType.i64 v    => some v
  | SType.fp32,   Sigma.mk SType.fp32 v   => some v
  | SType.fp64,   Sigma.mk SType.fp64 v   => some v
  | SType.string, Sigma.mk SType.string v => some v
  | SType.binary, Sigma.mk SType.binary v => some v
  | _, _ => none

/-- A same-type cast is the identity — the runtime cast can only fail when
    the row's cell type mismatches the schema. -/
theorem castCell_self (t : SType) (v : Cell t) : castCell t ⟨t, v⟩ = some v := by
  cases t <;> cases v <;> rfl

/-- A row cell at a resolved ordinal carries the schema's type — the row is
    indexed by the schema, so `Row.get` at a `HasCol`-resolved index returns
    the claimed (name, type) triple's cell. This is what `HasCol.resolves`
    (added when the class gained its proof field) BUYS the evaluator: the
    field read's type is proved, not cast-checked. -/
theorem Row.get_resolves {s : Schema} {name : String} {t : SType} {n : Bool}
    (h : HasCol s name t n) (row : Row s) :
    ∃ c : Option (Cell t), row.get h.index = some ⟨t, c⟩ := by
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
        obtain ⟨c, hc⟩ := ih { index := k, resolves := hres } rest
        refine ⟨c, ?_⟩
        rw [hk]
        exact hc

/-- Read an i32 payload from a runtime argument (none for null/other-type). -/
def argI32 : (Σ t, Option (Cell t)) → Option Int
  | Sigma.mk SType.i32 (some (Cell.i32 x)) => some x
  | _ => none

/-- Read a bool payload from a runtime argument (none for null/other-type). -/
def argBool : (Σ t, Option (Cell t)) → Option Bool
  | Sigma.mk SType.bool (some (Cell.bool b)) => some b
  | _ => none

/--
Built-in scalar kernels.  Only the set the typed layer's operators default to;
anything else fails loudly (the extension catalogue is out of scope here).
-/
def evalFunc (sig : FunctionSig) (args : List (Σ t, Option (Cell t))) :
    Except String (Option (Cell sig.ret)) :=
  match sig.name, sig.ret with
  | "add", .i32 =>
      match args with
      | [a, b] => match argI32 a, argI32 b with
                    | some x, some y => pure (some (Cell.i32 (x + y)))
                    | _, _ => pure none
      | _ => throw s!"eval: add expects two non-null i32 arguments"
  | "subtract", .i32 =>
      match args with
      | [a, b] => match argI32 a, argI32 b with
                    | some x, some y => pure (some (Cell.i32 (x - y)))
                    | _, _ => pure none
      | _ => throw s!"eval: subtract expects two non-null i32 arguments"
  | "multiply", .i32 =>
      match args with
      | [a, b] => match argI32 a, argI32 b with
                    | some x, some y => pure (some (Cell.i32 (x * y)))
                    | _, _ => pure none
      | _ => throw s!"eval: multiply expects two non-null i32 arguments"
  | "gt", .bool =>
      match args with
      | [a, b] => match argI32 a, argI32 b with
                    | some x, some y => pure (some (Cell.bool (x > y)))
                    | _, _ => pure none   -- NULL comparison → NULL
      | _ => throw s!"eval: gt expects two i32 arguments"
  | "lt", .bool =>
      match args with
      | [a, b] => match argI32 a, argI32 b with
                    | some x, some y => pure (some (Cell.bool (x < y)))
                    | _, _ => pure none
      | _ => throw s!"eval: lt expects two i32 arguments"
  | "equal", .bool =>
      match args with
      | [a, b] => match argI32 a, argI32 b with
                    | some x, some y => pure (some (Cell.bool (x == y)))
                    | _, _ => pure none
      | _ => throw s!"eval: equal expects two i32 arguments"
  | "and", .bool =>
      match args with
      | [a, b] => match argBool a, argBool b with
                    | some x, some y => pure (some (Cell.bool (x && y)))
                    | _, _ => pure none
      | _ => throw s!"eval: and expects two boolean arguments"
  | "or", .bool =>
      match args with
      | [a, b] => match argBool a, argBool b with
                    | some x, some y => pure (some (Cell.bool (x || y)))
                    | _, _ => pure none
      | _ => throw s!"eval: or expects two boolean arguments"
  | name, _ => throw s!"eval: function {name} not implemented in the skeleton evaluator"

/-! Evaluate an argument spine to runtime values (mutual with `Expr.evalCell`). -/
mutual
  /-- Evaluate a scalar expression over a row (NULL-propagating).  Value-first for dot notation. -/
  def Expr.evalCell : Expr s t n → (row : Row s) → Except String (Option (Cell t))
    | .literal _ _ v, _ => pure (some (litToCell v))
    | @Expr.field _ c _ _ _, row =>
        match row.get c.ordinal with
        | some (Sigma.mk t' v) => pure (v.bind (fun w => castCell t (Sigma.mk t' w)))
        | none => throw s!"eval: column index {c.ordinal} out of range"
    | .call sig args, row => do
        let vs ← Args.eval args row
        evalFunc sig vs

  /-- Evaluate a `Args` spine to a value list.  Value-first for dot notation. -/
  def Args.eval : Args s ts → (row : Row s) → Except String (List (Σ t, Option (Cell t)))
    | .nil, _ => pure []
    | .cons t n e rest, row => do
        let v ← Expr.evalCell e row
        let vs ← Args.eval rest row
        pure ((Sigma.mk t v : Σ t, Option (Cell t)) :: vs)
end

/-! ## Row building -/

/-- Build a row from a schema and runtime cells (missing cells become NULL). -/
def Row.ofCells : (schema : Schema) → List (Option (Σ t, Cell t)) → Row schema
  | [], _ => .nil
  | (_, t, _) :: rest, es =>
      match es with
      | [] => .cons none (Row.ofCells rest [])
      | e :: es' => .cons (e.bind (fun w => castCell t w)) (Row.ofCells rest es')

/--
Append extra cells to a row, extending the schema by `extraSchema`.  The
recursion unfolds the *base row first* so the appended schema stays on the
tail (`(p′₂ ++ extra)` is definitionally the result of `p ++ extra`), which
keeps the function total without casts.
-/
def Row.appendCells (r : Row p) : (extra : Schema) → List (Option (Σ t, Cell t)) → Row (p ++ extra) :=
  match r with
  | .nil => fun extra cells => Row.ofCells extra cells
  | .cons c base => fun extra cells => .cons c (Row.appendCells base extra cells)

/-- Concatenate two rows, extending the schema by list append (`a ++ b`).  The
recursion unfolds the base row first, so `rest ++ b` stays on the tail. -/
def Row.append {a b : Schema} : Row a → Row b → Row (a ++ b)
  | .nil, r => r
  | .cons c base, r => .cons c (Row.append base r)

/-- An all-`none` row of the given schema (used for outer-join padding). -/
def Row.padNone : (s : Schema) → Row s
  | [] => .nil
  | (_, _, _) :: rest => .cons none (Row.padNone rest)

/-- The left part of a row over the concatenated schema `a ++ b` (the split
depends only on `a`, so it is total without casts). -/
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

/-! ## Relation evaluation -/

/-- The source-resolver: table name → rows. -/
abbrev Reader (s : Schema) := String → Except String (Table s)

/--
`![cells]` — a row literal: cells are `some (Sigma.mk SType.i32 (Cell.i32 5))`
/ `none` terms; the schema is inferred from the expected `Row s` type.
-/
scoped syntax "![ " sepBy(term, ", ") " ]" : term

macro_rules
  | `(![ $cells,* ]) => `(Row.ofCells _ [ $cells,* ])

/--
Evaluate a typed projection over a table of the input schema (the `p ++ …`
append shape means this is the schema-*changing* pipeline step; use it
directly on the final columns).
-/
def evalProject {p : Schema} (outs : List (Projection p)) :
    Table p → Except String (Table (projectOut p outs)) :=
  fun rows =>
    rows.mapM (fun row => do
      let extra : List (Option (Σ t, Cell t)) ←
        outs.mapM (fun pr => do
          let v ← pr.expr.evalCell row
          pure (v.map (fun c => (Sigma.mk pr.dtype c : Sigma (fun t => Cell t)))))
      let cols : Schema := outs.map fun pr => ((pr.name, pr.dtype, pr.nullable) : SchemaCol)
      pure (row.appendCells cols extra))

/-- Stable insertion of a row into a sorted list (`lessEq x y`: x placed before y). -/
def stableInsert (lessEq : Row s → Row s → Bool) (x : Row s) : List (Row s) → List (Row s)
  | [] => [x]
  | y :: ys => if lessEq x y then x :: y :: ys else y :: stableInsert lessEq x ys

/-- Whether an ordering is not `.gt` (with the lexicographic fold). -/
def isNotGt : Ordering → Bool
  | .gt => false | _ => true

/-- Sort rows stably by the given keys. -/
def sortByKeys (keys : List (SortKey s)) (rows : List (Row s)) : List (Row s) :=
  let le (a b : Row s) : Bool := isNotGt (Row.cmpKeys keys a b)
  rows.foldl (fun acc x => stableInsert le x acc) []

/-- Apply limit/offset to a list. -/
def applyFetch : Option Nat → Option Nat → List ρ → List ρ
  | limit, offset, xs =>
      let dropped := xs.drop (offset.getD 0)
      match limit with
      | some n => dropped.take n
      | none   => dropped

/-! ## Join and aggregate -/

/-- Total equality for two cells of the same runtime type. -/
def Cell.eq : Cell t → Cell t → Bool
  | .bool a, .bool b => a == b
  | .i8 a, .i8 b => a == b
  | .i16 a, .i16 b => a == b
  | .i32 a, .i32 b => a == b
  | .i64 a, .i64 b => a == b
  | .fp32 a, .fp32 b => a == b
  | .fp64 a, .fp64 b => a == b
  | .string a, .string b => a == b
  | .binary a, .binary b => a == b

/-- Option equality via a cell equality. -/
def sameOpt (f : Cell t → Cell t → Bool) : Option (Cell t) → Option (Cell t) → Bool
  | some x, some y => f x y
  | none, none => true
  | _, _ => false

/--
Erased key equality: two runtime-typed cells are equal when their `SType`
indices agree *and* the payloads compare equal (bool/i8/i16/i32/i64 compare
by `Int` equality, fp32/fp64 by `Float`, string by `String`, binary by
`UInt8` list).  Different `SType` indices are always unequal.
-/
def keyEq (a b : Σ t, Option (Cell t)) : Bool :=
  match a, b with
  | Sigma.mk SType.bool a', Sigma.mk SType.bool b' => sameOpt Cell.eq a' b'
  | Sigma.mk SType.i8 a', Sigma.mk SType.i8 b' => sameOpt Cell.eq a' b'
  | Sigma.mk SType.i16 a', Sigma.mk SType.i16 b' => sameOpt Cell.eq a' b'
  | Sigma.mk SType.i32 a', Sigma.mk SType.i32 b' => sameOpt Cell.eq a' b'
  | Sigma.mk SType.i64 a', Sigma.mk SType.i64 b' => sameOpt Cell.eq a' b'
  | Sigma.mk SType.fp32 a', Sigma.mk SType.fp32 b' => sameOpt Cell.eq a' b'
  | Sigma.mk SType.fp64 a', Sigma.mk SType.fp64 b' => sameOpt Cell.eq a' b'
  | Sigma.mk SType.string a', Sigma.mk SType.string b' => sameOpt Cell.eq a' b'
  | Sigma.mk SType.binary a', Sigma.mk SType.binary b' => sameOpt Cell.eq a' b'
  | _, _ => false

/-- Key-list equality (pairwise `keyEq`). -/
def keyListEq : List (Σ t, Option (Cell t)) → List (Σ t, Option (Cell t)) → Bool
  | [], [] => true
  | x :: xs, y :: ys => keyEq x y && keyListEq xs ys
  | _, _ => false

/-- Present a key value as an optional typed cell (for an aggregate output row). -/
def optCellOf : (Σ t, Option (Cell t)) → Option (Σ t, Cell t)
  | Sigma.mk _ none => none
  | Sigma.mk t (some c) => some (Sigma.mk t c)

/-- Evaluate a packaged `AnyExpr` over a row. -/
def evalAnyExpr (ae : AnyExpr s) (row : Row s) : Except String (Σ t, Option (Cell t)) :=
  match ae with
  | AnyExpr.mk t _ e => (e.evalCell row).map (fun v => Sigma.mk t v)

/-- Integer aggregate fold (sum/min/max/avg); an empty set aggregates to NULL (`none`). -/
def aggInt (f : String) (wrap : Int → Σ t, Cell t) (xs : List Int) : Option (Σ t, Cell t) :=
  match f, xs with
  | _, [] => none
  | "sum", xs => some (wrap (xs.foldl (· + ·) 0))
  | "min", x :: rest => some (wrap (rest.foldl (fun a b => if b < a then b else a) x))
  | "max", x :: rest => some (wrap (rest.foldl (fun a b => if b > a then b else a) x))
  | "avg", xs =>
      let (total, n) := xs.foldl (fun (a, n) x => (a + x, n + 1)) ((0 : Int), (0 : Int))
      some (wrap (total / n))
  | _, _ => none

/-- Floating-point aggregate fold (sum/min/max/avg); empty set → NULL. -/
def aggFloat (f : String) (wrap : Float → Σ t, Cell t) (xs : List Float) : Option (Σ t, Cell t) :=
  match f, xs with
  | _, [] => none
  | "sum", xs => some (wrap (xs.foldl (· + ·) 0))
  | "min", x :: rest => some (wrap (rest.foldl (fun a b => if b < a then b else a) x))
  | "max", x :: rest => some (wrap (rest.foldl (fun a b => if b > a then b else a) x))
  | "avg", xs =>
      let (total, n) := xs.foldl (fun (a, n) x => (a + x, n + 1)) ((0 : Float), (0 : Float))
      some (wrap (total / n))
  | _, _ => none

/--
Evaluate one aggregate measure over a group's rows.  Supported: `count`
(zero or one argument — with an argument it counts non-null values), plus
`sum`/`min`/`max`/`avg` over the numeric cell types (the result cell has the
argument's type — no substrait widening).  Anything else fails loudly.
-/
def evalMeasure (m : Measure s) (group : Table s) : Except String (Option (Σ t, Cell t)) := do
  match m.sig.name with
  | "count" => do
      match m.args with
      | [] => pure (some (Sigma.mk SType.i64 (Cell.i64 (group.length : Int))))
      | [ae] => do
          let nonNull ← group.filterM (fun row => do
            let v ← evalAnyExpr ae row
            pure (match v with
                  | Sigma.mk _ (some _) => true
                  | _ => false))
          pure (some (Sigma.mk SType.i64 (Cell.i64 (nonNull.length : Int))))
      | _ => throw s!"eval: count expects zero or one argument"
  | "sum" | "min" | "max" | "avg" => do
      match m.args with
      | [ae] => do
          let vs ← group.mapM (fun row => evalAnyExpr ae row)
          let kept := vs.filter (fun v => match v with
                                          | Sigma.mk _ (some _) => true
                                          | _ => false)
          match kept with
          | [] => pure none
          | Sigma.mk SType.i8 (some (Cell.i8 _)) :: _ =>
              pure (aggInt m.sig.name (fun x => Sigma.mk SType.i8 (Cell.i8 x))
                (kept.filterMap (fun v => match v with
                  | Sigma.mk SType.i8 (some (Cell.i8 x)) => some x | _ => none)))
          | Sigma.mk SType.i16 (some (Cell.i16 _)) :: _ =>
              pure (aggInt m.sig.name (fun x => Sigma.mk SType.i16 (Cell.i16 x))
                (kept.filterMap (fun v => match v with
                  | Sigma.mk SType.i16 (some (Cell.i16 x)) => some x | _ => none)))
          | Sigma.mk SType.i32 (some (Cell.i32 _)) :: _ =>
              pure (aggInt m.sig.name (fun x => Sigma.mk SType.i32 (Cell.i32 x))
                (kept.filterMap (fun v => match v with
                  | Sigma.mk SType.i32 (some (Cell.i32 x)) => some x | _ => none)))
          | Sigma.mk SType.i64 (some (Cell.i64 _)) :: _ =>
              pure (aggInt m.sig.name (fun x => Sigma.mk SType.i64 (Cell.i64 x))
                (kept.filterMap (fun v => match v with
                  | Sigma.mk SType.i64 (some (Cell.i64 x)) => some x | _ => none)))
          | Sigma.mk SType.fp32 (some (Cell.fp32 _)) :: _ =>
              pure (aggFloat m.sig.name (fun x => Sigma.mk SType.fp32 (Cell.fp32 x))
                (kept.filterMap (fun v => match v with
                  | Sigma.mk SType.fp32 (some (Cell.fp32 x)) => some x | _ => none)))
          | Sigma.mk SType.fp64 (some (Cell.fp64 _)) :: _ =>
              pure (aggFloat m.sig.name (fun x => Sigma.mk SType.fp64 (Cell.fp64 x))
                (kept.filterMap (fun v => match v with
                  | Sigma.mk SType.fp64 (some (Cell.fp64 x)) => some x | _ => none)))
          | hd :: _ =>
              match hd with
              | Sigma.mk t' _ => throw s!"eval: {m.sig.name}: unsupported argument type {repr t'}"
      | _ => throw s!"eval: {m.sig.name} expects one argument"
  | name => throw s!"eval: aggregate function {name} not implemented"

/-- Insert a row into the correct key bucket (keys compared by `keyListEq`);
buckets appear in first-seen key order. -/
def insertBucket {s : Schema} (k : List (Σ t, Option (Cell t))) (row : Row s) :
    List (List (Σ t, Option (Cell t)) × Table s) → List (List (Σ t, Option (Cell t)) × Table s)
  | [] => [(k, [row])]
  | (k', rows) :: rest =>
      if keyListEq k k' then (k', rows ++ [row]) :: rest
      else (k', rows) :: insertBucket k row rest

/--
Evaluate an aggregate rel: bucket the rows by their evaluated grouping keys,
then run each measure over its group.  Each output row is the grouping key
cells followed by the measure cells (both in the constructor's list order);
buckets appear in first-seen key order.
-/
def evalAggregate {s : Schema} (grouping : List (AnyExpr s)) (measures : List (Measure s))
    (rows : Table s) : Except String (Table (aggregateOut s grouping measures)) := do
  let keyed ← rows.mapM (fun row => do
    let ks ← grouping.mapM (fun ae => evalAnyExpr ae row)
    pure (ks, row))
  let buckets := keyed.foldl (fun acc (k, r) => insertBucket k r acc) []
  let out ← buckets.mapM (fun (k, grp) => do
    let keyCells := k.map optCellOf
    let measCells ← measures.mapM (fun m => evalMeasure m grp)
    pure (Row.ofCells (aggregateOut s grouping measures) (keyCells ++ measCells)))
  pure out

/--
Evaluate a join rel.  `inner` keeps the matched product pairs (a pair matches
when the condition evaluates to `some true`; anything else — SQL NULL or
false — drops it).  `left`/`right`/`outer` additionally emit the unmatched
rows padded with `none` cells on the missing side (the `Row` type carries the
full width regardless of the nullability flags).  Other join types
(semi/anti/mark/single) fail loudly.
-/
def evalJoin {l' r' : Schema} {n : Bool} (jt : Proto.JoinType)
    (cond : Expr (l' ++ r') .bool n)
    (lrows : Table l') (rrows : Table r') : Except String (Table (l' ++ r')) := do
  let pairMatches : Row l' → Row r' → Except String Bool := fun l r => do
    let c ← cond.evalCell (Row.append l r)
    pure (match c with
          | some (Cell.bool true) => true
          | _ => false)
  let iterInner : Table (l' ++ r') ←
    (lrows.mapM (fun l => do
      let rs ← rrows.filterM (fun r => pairMatches l r)
      pure (rs.map (fun r => Row.append l r)))).map List.flatten
  let unmatchedL ← lrows.filterM (fun l => do
    let m ← rrows.anyM (fun r => pairMatches l r)
    pure (!m))
  let unmatchedR ← rrows.filterM (fun r => do
    let m ← lrows.anyM (fun l => pairMatches l r)
    pure (!m))
  match jt with
  | .inner => pure iterInner
  | .left => pure (iterInner ++ unmatchedL.map (fun l => Row.append l (Row.padNone r')))
  | .right => pure (iterInner ++ unmatchedR.map (fun r => Row.append (Row.padNone l') r))
  | .outer => pure (iterInner
                    ++ unmatchedL.map (fun l => Row.append l (Row.padNone r'))
                    ++ unmatchedR.map (fun r => Row.append (Row.padNone l') r))
  | other => throw s!"eval: join type {repr other} not implemented (inner/left/right/outer only)"

/--
Evaluate a typed rel over a table.  The output schema is an index (so
schema-changing rels — `Project`, `Aggregate`, `Join`, `Write`,
`ExtensionSingle` — exist in the type; `Project` has `evalProject`, `Join` and
`Aggregate` are interpreted, `Write` and `ExtensionSingle` hard-fail at
runtime).
-/
def eval {s s' : Schema} (reader : Reader s) : Rel s s' → Table s → Except String (Table s')
  | .read table _, _ =>
      reader table
  | .filter input cond, rows => do
      let r ← eval reader input rows
      r.filterM (fun row => do
        let c ← cond.evalCell row
        pure (match c with
              | some (Cell.bool true) => true
              | _ => false))
  | .sort input keys, rows => do
      let r ← eval reader input rows
      pure (sortByKeys keys r)
  | .fetch input limit offset, rows => do
      let r ← eval reader input rows
      pure (applyFetch limit offset r)
  | .set op left right, rows =>
      match op with
      | .unionAll => do
          let l ← eval reader left rows
          let r ← eval reader right rows
          pure (l ++ r)
      | _ => throw s!"eval: set op {repr op} not implemented (only UnionAll)"
  | .project _ _ _, _ =>
      throw "eval: project — use Eval.evalProject (schema-changing output)"
  | @Rel.join sl sl' sr sr' _n left right cond jt, rows => do
      -- The join's input schema is the concatenation of its sides; split each
      -- row so the children see their own halves (the reader serves the same
      -- full-width stream).
      let lread : Reader sl := fun name => (reader name).map (fun t => t.map (fun r => Row.splitLeft sl r))
      let rread : Reader sr := fun name => (reader name).map (fun t => t.map (fun r => Row.splitRight sl r))
      let lrows ← eval lread left (rows.map (fun r => Row.splitLeft sl r))
      let rrows ← eval rread right (rows.map (fun r => Row.splitRight sl r))
      evalJoin jt cond lrows rrows
  | .aggregate input grouping measures, rows => do
      let r ← eval reader input rows
      evalAggregate grouping measures r
  | .write _ _ _ _, _ =>
      throw "eval: write not implemented in the skeleton evaluator"
  | .extensionSingle _ _, _ =>
      throw "eval: extensionSingle not implemented in the skeleton evaluator"

end Substrait.Typed
