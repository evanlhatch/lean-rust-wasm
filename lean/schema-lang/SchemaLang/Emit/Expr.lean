/-
# SchemaLang.Emit.Expr — VExpr → Rust expression lowering, once, against the interface

The expression fragment every expression-consuming emitter shares
(W7.2 phase 2): the u64-leaf Rust text and the boolean Rust algebra,
written ONCE against the `SchemaLang.ExprLang` interface
(`HasU64.view` for the leaves, `HasBool.fold` for the recursion —
the fold owns the recursion, the algebras are leaf-pure). The VExpr
GADT stays at authoring (SchemaLang.Validate); this module is a
CONSUMER: it reads the interface's `U64Node`/`BoolNode` views and
never pattern-matches `VExpr`.

Provenance: phase 1 wrote these algebras inside Emit.Invariant (the
driving consumer); phase 2's Emit.Update port made them shared, so
they move here — ONE lowering, two lanes, byte-tie preserved (the
rendered text is definitionally the phase-1 text).

Ownership: the EMISSION reading only (String payloads — `ref`, the
`Ident → String` rendering key, is the consumer's; the boxed row
projections the nodes carry are the evaluation readings' half and are
ignored here). The EVALUATION readings live in `ExprLang` itself
(`evalSpecI`/`evalRawI`/`validatesI`).

Deliberate exclusions: no `Item` assembly here (the lanes own their
fn/module shapes — Emit.Invariant's check fns, Emit.Update's apply
fns); no new capabilities (a `HasString` joins when a consumer needs
one — capabilities follow consumers; Emit.Update's string-write
`.col` match stays GADT-direct until then, by justification).
-/

module

public import SchemaLang.ExprLang

@[expose] public section

namespace SchemaLang.Emit.Expr

/-- The u64 operand's Rust text — the EMISSION reading of the
    `U64Node` view: the name is the rendering key, the boxed
    projection the node carries is the evaluation readings' half
    (ignored here). `ref` renders a field ref (the record's struct
    field — `rustIdent`-mangled by the caller). -/
def u64RustI (L : ExprLang) [HasU64 L] (ref : L.Ident → String)
    (e : L.Expr .u64) : String :=
  match HasU64.view e with
  | .lit v => s!"{v}u64"
  | .col n _ => ref n
  | .strlenCol n _ => s!"({ref n}).len() as u64"

/-- The boolean's Rust text ALGEBRA (children arrive pre-folded to
    text — the fold owns the recursion). -/
def boolRustAlg {I R : Type} (ref : I → String) :
    BoolNode I R String String → String
  | .col n _ => s!"({ref n}) as u64 == 1"
  | .gt a b => s!"({a} > {b})"
  | .eq a b => s!"({a} == {b})"
  | .and a b => s!"({a} && {b})"
  | .not a => s!"(!({a}))"

/-- The boolean's Rust text: the fold at the emission algebras. -/
def boolRustI (L : ExprLang) [HasU64 L] [HasBool L] (ref : L.Ident → String)
    (e : L.Expr .bool) : String :=
  HasBool.fold (u64RustI L ref) (boolRustAlg ref) e

end SchemaLang.Emit.Expr
