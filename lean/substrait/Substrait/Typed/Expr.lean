/-
# Substrait.Typed.Expr

The typed expression family.

`Expr (s : Schema) (t : SType) (n : Bool)` is a well-typed expression over the
schema `s` returning a value of type `t` with nullability `n`.  Columns are
referenced **by name** via `HasCol`; the ordinal is computed at `toProto` time.

Function calls go through a `FunctionSig` (name + URN + argument types +
return type + determinism/session-dependence/nullability).  `call` takes an
`Args s sig.args` — a heterogeneous *indexed spine* that makes the arguments'
(t, n) sequence definitionally equal to the signature's argument list, so
mismatched arity/types are type errors.  Wire anchors are computed at
emission (see `Substrait.Typed.ToProto`).

Operator sugar (`+.`, `-.`, `<.`, `==.`, `&&.`, ...) is a dotted family so it
does not collide with `==`.  Nullability propagates per the substrait function
semantics: arithmetic/comparison return null when any argument is null
(`n1 || n2`).

`AnyExpr s` erases the (t, n) indices for heterogeneous lists that are *not*
tied to a signature (aggregate grouping keys): Lean forbids `Σ`/nested
inductives under the GADT, so the sigma-pair is encoded as its own inductive.
-/
import Substrait.Typed.Schema

namespace Substrait.Typed

/--
A scalar function signature.  `urn + name` identify the extension function;
`args` is the expected argument (type, nullability) list; `ret` /
`retNullable` is the result.  `deterministic` / `sessionDependent` are the
extension-YAML properties (metadata today).
-/
structure FunctionSig where
  name : String
  urn : String
  args : List (SType × Bool)
  ret : SType
  retNullable : Bool
  deterministic : Bool
  sessionDependent : Bool := false
deriving Repr, BEq, Inhabited

/-- Helper: contract a function signature. -/
def FunctionSig.mkSig (name urn : String) (args : List (SType × Bool))
    (ret : SType) (retNullable deterministic : Bool) : FunctionSig :=
  { name := name, urn := urn, args := args, ret := ret, retNullable := retNullable,
    deterministic := deterministic, sessionDependent := false }

/-- Helper: a binary-operator signature `name(t, t) → ret`, null when any
    argument is null. -/
def mkBinSig (name urn : String) (t ret : SType) (n1 n2 : Bool) : FunctionSig :=
  FunctionSig.mkSig name urn [(t, n1), (t, n2)] ret (n1 || n2) true

/-- The value payload of a typed literal, indexed by the literal's type. -/
inductive LiteralValue : SType → Type where
  | bool   : Bool → LiteralValue .bool
  | i8     : Int → LiteralValue .i8
  | i16    : Int → LiteralValue .i16
  | i32    : Int → LiteralValue .i32
  | i64    : Int → LiteralValue .i64
  | fp32   : Float → LiteralValue .fp32
  | fp64   : Float → LiteralValue .fp64
  | string : String → LiteralValue .string
  | binary : List UInt8 → LiteralValue .binary

/-
The expression family is a three-way mutual block: `Expr` calls `Args`;
`Args` holds `Expr`s; `AnyExpr` (the type-erased package) holds `Expr`s.
Lean needs the mutual block for the circularity.
-/
mutual
  /--
  `Expr s` — the typed expression family over schema `s`.  `literal` carries
  its (t, n) index; `field` is a by-name column reference resolved by `HasCol`;
  `call` is a signature-typed scalar-function invocation whose argument spine
  matches the signature's argument list.  `s` is an explicit parameter (not an
  index) so all three mutual members share the same parameter count.
  -/
  inductive Expr (s : Schema) : SType → Bool → Type where
    | literal : (t : SType) → (n : Bool) → LiteralValue t → Expr s t n
    | field : (c : Column) → (t : SType) → (n : Bool) → [HasCol s c.name t n] → Expr s t n
    | call : (sig : FunctionSig) → (args : Args s sig.args) → Expr s sig.ret sig.retNullable

  /--
  `Args s ts` — a heterogeneous argument spine indexed by the type sequence.
  The cons constructor pins `expr`'s `(t, n)` to the head of the index, so the
  spine's type list is definitionally the sequence of argument types.
  -/
  inductive Args (s : Schema) : List (SType × Bool) → Type where
    | nil : Args s []
    | cons : (t : SType) → (n : Bool) → Expr s t n → Args s rest → Args s ((t, n) :: rest)

  /-- A type-erased packaged expression: `(t, n, Expr s t n)` flattened. -/
  inductive AnyExpr (s : Schema) : Type where
    | mk (t : SType) (n : Bool) (e : Expr s t n)
end

/-- Smart constructor: an i32 literal `0`. -/
def litI32 (v : Int) : Expr s .i32 false := Expr.literal .i32 false (LiteralValue.i32 v)

/-- Smart constructor: an i64 literal. -/
def litI64 (v : Int) : Expr s .i64 false := Expr.literal .i64 false (LiteralValue.i64 v)

/-- Smart constructor: a boolean literal. -/
def litBool (b : Bool) : Expr s .bool false := Expr.literal .bool false (LiteralValue.bool b)

/-- Package an expression with its indices. -/
def pack {s : Schema} {t : SType} {n : Bool} (e : Expr s t n) : AnyExpr s :=
  AnyExpr.mk t n e

/--
The authoring surface's by-name column expression: `col "health" .i32 true`
is an `Expr s .i32 true` resolved through `HasCol` (head/tail instance search
over the literal schema abbreviation).  Uses the instance directly (like
`sortKey`) — re-running instance search would be stuck since `Expr.field`
needs `s`/`t`/`n` pinned.
-/
def col (name : String) (t : SType) (n : Bool) [h : HasCol s name t n] : Expr s t n :=
  Expr.field { name := name, ordinal := h.index } t n

/-- The one-argument spine. -/
def oneArg {s : Schema} {t : SType} {n : Bool} (e : Expr s t n) : Args s [(t, n)] :=
  Args.cons t n e Args.nil

/-- Prepend an argument to a spine. -/
def pushArg {s : Schema} {t : SType} {n : Bool} (e : Expr s t n) (rest : Args s ts) : Args s ((t, n) :: ts) :=
  Args.cons t n e rest

/-- The empty spine. -/
def noArgs {s : Schema} : Args s [] := Args.nil

/--
`call` — invoke a scalar function signature on a matching argument spine.
Anchors are resolved at emission from the plan's declaration list.
-/
def call (sig : FunctionSig) (args : Args s sig.args) : Expr s sig.ret sig.retNullable :=
  Expr.call sig args

/-- The standard arithmetic extension URN (substrait core function catalogue). -/
def standardArithmeticUrn : String := "extension:io.substrait:functions_arithmetic"

/-- The standard comparison extension URN (substrait core function catalogue). -/
def standardComparisonUrn : String := "extension:io.substrait:functions_comparison"

/-- `add(i32, i32) -> i32`, null when any argument is null. -/
def opAddSig (n1 n2 : Bool) : FunctionSig := mkBinSig "add" standardArithmeticUrn .i32 .i32 n1 n2

/-- `subtract(i32, i32) -> i32`. -/
def opSubSig (n1 n2 : Bool) : FunctionSig := mkBinSig "subtract" standardArithmeticUrn .i32 .i32 n1 n2

/-- `multiply(i32, i32) -> i32`. -/
def opMulSig (n1 n2 : Bool) : FunctionSig := mkBinSig "multiply" standardArithmeticUrn .i32 .i32 n1 n2

/-- `gt(i32, i32) -> bool`. -/
def opGtSig (n1 n2 : Bool) : FunctionSig := mkBinSig "gt" standardComparisonUrn .i32 .bool n1 n2

/-- `lt(i32, i32) -> bool`. -/
def opLtSig (n1 n2 : Bool) : FunctionSig := mkBinSig "lt" standardComparisonUrn .i32 .bool n1 n2

/-- `equal(i32, i32) -> bool`. -/
def opEqSig (n1 n2 : Bool) : FunctionSig := mkBinSig "equal" standardComparisonUrn .i32 .bool n1 n2

/-- `and(bool, bool) -> bool`. -/
def opAndSig (n1 n2 : Bool) : FunctionSig := mkBinSig "and" "extension:io.substrait:functions_boolean" .bool .bool n1 n2

/-- `or(bool, bool) -> bool`. -/
def opOrSig (n1 n2 : Bool) : FunctionSig := mkBinSig "or" "extension:io.substrait:functions_boolean" .bool .bool n1 n2

namespace Expr

/-- `call` of a two-argument operator signature on matching-typed arguments.
    The signature's argument list must be exactly the two `(t, n)` pairs —
    checked by `rfl` at each use. -/
def binCall (sig : FunctionSig) (a : Expr s t n1) (b : Expr s t n2)
    (h : sig.args = [(t, n1), (t, n2)] := by rfl) : Expr s sig.ret sig.retNullable :=
  Expr.call sig (h.symm ▸ Args.cons t n1 a (Args.cons t n2 b Args.nil))

/-- `a +. b` — i32 addition. -/
def add (a : Expr s .i32 n1) (b : Expr s .i32 n2) : Expr s .i32 (n1 || n2) :=
  binCall (opAddSig n1 n2) a b

/-- `a -. b` — i32 subtraction. -/
def sub (a : Expr s .i32 n1) (b : Expr s .i32 n2) : Expr s .i32 (n1 || n2) :=
  binCall (opSubSig n1 n2) a b

/-- `a *. b` — i32 multiplication. -/
def mul (a : Expr s .i32 n1) (b : Expr s .i32 n2) : Expr s .i32 (n1 || n2) :=
  binCall (opMulSig n1 n2) a b

/-- `a >. b` — i32 greater-than. -/
def gt (a : Expr s .i32 n1) (b : Expr s .i32 n2) : Expr s .bool (n1 || n2) :=
  binCall (opGtSig n1 n2) a b

/-- `a <. b` — i32 less-than. -/
def lt (a : Expr s .i32 n1) (b : Expr s .i32 n2) : Expr s .bool (n1 || n2) :=
  binCall (opLtSig n1 n2) a b

/-- `a ==. b` — i32 equality. -/
def eq (a : Expr s .i32 n1) (b : Expr s .i32 n2) : Expr s .bool (n1 || n2) :=
  binCall (opEqSig n1 n2) a b

/-- `a &&. b` — logical conjunction. -/
def and (a : Expr s .bool n1) (b : Expr s .bool n2) : Expr s .bool (n1 || n2) :=
  binCall (opAndSig n1 n2) a b

/-- `a ||. b` — logical disjunction. -/
def or (a : Expr s .bool n1) (b : Expr s .bool n2) : Expr s .bool (n1 || n2) :=
  binCall (opOrSig n1 n2) a b

end Expr

-- Infix operator sugar.  Dotted to avoid colliding with `=`/`==`.

/-- `a +. b` — i32 addition. -/
scoped infixl:65 " +. " => Expr.add

/-- `a -. b` — i32 subtraction. -/
scoped infixl:65 " -. " => Expr.sub

/-- `a *. b` — i32 multiplication. -/
scoped infixl:70 " *. " => Expr.mul

/-- `a >. b` — i32 greater-than. -/
scoped infix:50 " >. " => Expr.gt

/-- `a <. b` — i32 less-than. -/
scoped infix:50 " <. " => Expr.lt

/-- `a ==. b` — i32 equality. -/
scoped infix:50 " ==. " => Expr.eq

/-- `a &&. b` — logical conjunction. -/
scoped infixr:35 " &&. " => Expr.and

/-- `a ||. b` — logical disjunction. -/
scoped infixr:30 " ||. " => Expr.or

end Substrait.Typed
