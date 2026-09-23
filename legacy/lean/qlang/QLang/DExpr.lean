/-
# QLang.DExpr

The dynamic expression tree and its compiler to the *typed* layer. Ported
from the flatland lineage's `FlatlandDsl.DslExpr` (core-only: the flatland
original's mathlib dep was vestigial — this module uses none of it).

`DExpr` is schema-free: column references are plain names, function calls
carry a `FunctionSig` (the "registry" that knows a function's argument
types).  `compile : Schema → DExpr → Except String (Typed s)` resolves
column names against the *supplied* schema value (unknown name or type
mismatch → `Except`, never a panic) and reifies the result as a typed
`Expr s t n` — the same expression family the typed layer uses, so the DSL
touches zero new expression machinery.

THE PATTERN (the flatland dig's headline): the `HasCol` instance is
constructed AS DATA from the resolved ordinal — `HasCol.ofIndex` packages
the found ordinal plus its resolution proof into an instance value. Instance
search is bypassed at runtime; "instance-as-data, not search". The fold in
`compileCol` carries the resolution PROOF, so a buggy resolution cannot
fabricate a column — the proof obligation is checked by `decide`-level
`rfl` at each step.

Nullability semantics mirror the typed operators (`Expr.add : Expr s .i32 n1
→ Expr s .i32 n2 → Expr s .i32 (n1 || n2)`): a call's output is nullable
iff any argument is nullable; `sig.retNullable` is recomputed from the
compiled arguments at `compile` time (signature `args` nullability is ignored
for the check — only the *types* matter, matching "argument types match the
function signature").
-/
import Substrait.Typed
import QLang.Error

namespace QLang

open Substrait.Typed

/-! ## The dynamic expression tree -/

/--
A schema-free expression.  `lit` is kernel-checked (the literal payload's
type is pinned to the stored `t`); `col` is resolved at compile time against
the pipeline schema; `call` invokes a known `FunctionSig` on a plain list of
sub-expressions (types checked at compile time).
-/
inductive DExpr where
  | lit (t : SType) (n : Bool) (v : LiteralValue t)
  | col (name : String)
  | call (sig : FunctionSig) (args : List DExpr)

/-! ## The authoring surface (plain functions, no syntax) -/

/-- `col "health"` — a by-name column reference (ordinal resolved at compile). -/
def col (name : String) : DExpr := DExpr.col name

/-- An `i32` literal. -/
def litI32 (v : Int) : DExpr := DExpr.lit SType.i32 false (LiteralValue.i32 v)

/-- A boolean literal. -/
def litBool (b : Bool) : DExpr := DExpr.lit SType.bool false (LiteralValue.bool b)

/-- Invoke a signature on argument expressions. -/
def call (sig : FunctionSig) (args : List DExpr) : DExpr := DExpr.call sig args

/-- `add(a, b)` — i32 addition (types i32/i32; nullability computed at compile). -/
def add (a b : DExpr) : DExpr :=
  DExpr.call (opAddSig false false) [a, b]

/-- `subtract(a, b)`. -/
def sub (a b : DExpr) : DExpr :=
  DExpr.call (opSubSig false false) [a, b]

/-- `multiply(a, b)`. -/
def mul (a b : DExpr) : DExpr :=
  DExpr.call (opMulSig false false) [a, b]

/-- `gt(a, b)` — i32 greater-than. -/
def gt (a b : DExpr) : DExpr :=
  DExpr.call (opGtSig false false) [a, b]

/-- `lt(a, b)`. -/
def lt (a b : DExpr) : DExpr :=
  DExpr.call (opLtSig false false) [a, b]

/-- `equal(a, b)`. -/
def eq (a b : DExpr) : DExpr :=
  DExpr.call (opEqSig false false) [a, b]

/-- `and(a, b)`. -/
def and (a b : DExpr) : DExpr :=
  DExpr.call (opAndSig false false) [a, b]

/-- `or(a, b)`. -/
def or (a b : DExpr) : DExpr :=
  DExpr.call (opOrSig false false) [a, b]

/-! ## Compilation to the typed layer -/

/-- A compiled, typed expression packaged with its type. -/
structure Typed (s : Schema) where
  t : SType
  n : Bool
  e : Expr s t n

/-- A `HasCol` instance from a *resolved* ordinal (the DSL resolves ordinals
at runtime against the registry — the instance is plain data, not search,
which is exactly what `Expr.field` carries). -/
@[instance_reducible]
def HasCol.ofIndex {s : Schema} (name : String) (t : SType) (n : Bool)
    (index : Nat) (hres : Schema.get? s index = some (name, t, n)) :
    HasCol s name t n := { index := index, resolves := hres }

/-- Resolve a column name against a schema value and build a typed field
reference (mirrors `Substrait.Typed.col`, but the instance/ordinal are
data-resolved). Unknown names fail with the did-you-mean rendering. -/
def compileCol (s : Schema) (name : String) : Except String (Typed s) := do
  -- the fold carries the resolution PROOF: the found ordinal is checked
  -- against the schema by `decide`, so a buggy `go` can't fabricate a column
  let rec go : (rest : Schema) → Except String (Σ' t n ord, Schema.get? rest ord = some (name, t, n))
    | [] => throw (QLangError.unknownColumnMsg name (Schema.names s))
    | (nm, ty, n) :: rest =>
      if h : nm = name then
        pure ⟨ty, n, 0, by rw [Schema.get?]; simp [h]⟩
      else
        match go rest with
        | .error e => .error e
        | .ok ⟨t, n, ord, hprf⟩ => .ok ⟨t, n, ord + 1, by simpa [Schema.get?] using hprf⟩
  let ⟨t, n, ord, hprf⟩ ← go s
  -- `go` proves resolution within the SUFFIX it recursed into; rebase to `s`:
  -- the fold starts at s itself, so hprf is already stated against s
  pure { t := t, n := n, e := @Expr.field s { name := name, ordinal := ord } t n (HasCol.ofIndex name t n ord hprf) }

/-- Resolve a column NAME to its ordinal (no expression built) — the sort
key's shape, which carries a `Column`, not an `Expr`. -/
def colOrdinal (s : Schema) (name : String) : Except String Nat :=
  let rec go : Nat → Schema → Except String Nat
    | _, [] => throw (QLangError.unknownColumnMsg name (Schema.names s))
    | i, (nm, _, _) :: rest => if nm == name then pure i else go (i + 1) rest
  go 0 s

/-- Build the dependent `Args` spine over the *actual* compiled argument types
(no reindexing: `(c.t, c.n)` is the spine index by construction). -/
def compileSpine {s : Schema} : List (Typed s) → (Σ ts : List (SType × Bool), Args s ts)
  | [] => ⟨[], Args.nil⟩
  | c :: cs =>
      let ⟨rest, restSpine⟩ := compileSpine cs
      ⟨(c.t, c.n) :: rest, Args.cons c.t c.n c.e restSpine⟩

/-- Whether every compiled argument's *type* matches the signature's expected
types (nullability deliberately unchecked — it propagates to the output). -/
def typesMatch {s : Schema} (expected : List (SType × Bool)) (actual : List (Typed s)) : Bool :=
  (expected.zip actual).all (fun ((et, _), c) =>
    match SType.eqAns c.t et with
    | .yes _ => true
    | .no => false)

/--
Compile a `DExpr` against a schema value into the typed layer.  Failure is an
`Except String` (unknown column, unknown/arity-mismatched call, type
mismatch) — never a panic; the query log records these and surfaces them at
`Query.checked`.

Nullability semantics mirror the typed operators: a call's output is nullable
iff any argument is nullable (`sig.retNullable := any`), and the signature's
arg list is replaced by the *actual* compiled types (the DSL's signature
placeholders only pin types).
-/
def compile (s : Schema) : DExpr → Except String (Typed s)
  | .lit t n v => pure { t := t, n := n, e := Expr.literal t n v }
  | .col name => compileCol s name
  | .call sig args => do
      if args.length != sig.args.length then
        throw s!"function '{sig.name}': arity {args.length} does not match signature arity {sig.args.length}"
      let cs ← args.mapM (fun d => compile s d)
      if !typesMatch sig.args cs then
        throw s!"function '{sig.name}': argument type mismatch: expected {repr (sig.args.map (fun (t, _) => t))}, got {repr (cs.map (fun c => c.t))}"
      let ⟨actual, spine⟩ := compileSpine cs
      let anyNull : Bool := cs.any (fun c => c.n)
      let sig' := { sig with args := actual, retNullable := anyNull }
      pure { t := sig'.ret, n := sig'.retNullable, e := Expr.call sig' spine }

end QLang
