/-
# Substrait.Typed.Binop — `declare_binop`: one table entry per binary operator

Owner of the `declare_binop` elaboration command (guide 4.4).  One entry

    /-- `<fn>(<t>, <t>) -> <ret>` doc for the sig def. -/
    /-- `a <op>. b` doc for the `Expr` wrapper. -/
    declare_binop add "add", standardArithmeticUrn, .i32, .i32

generates, at the use site's namespace, the two declarations that used to be
hand-written per operator in `Substrait.Typed.Expr`:

    def opAddSig (n1 n2 : Bool) : FunctionSig :=
      mkBinSig "add" standardArithmeticUrn .i32 .i32 n1 n2

    def Expr.add {s : Schema} {n1 n2 : Bool} (a : Expr s .i32 n1) (b : Expr s .i32 n2) :
        Expr s .i32 (n1 || n2) :=
      Expr.binCall (opAddSig n1 n2) a b

The sig name is `op` + Capitalized(entry) + `Sig`; the wrapper is
`Expr.<entry>`.  The implicit telescope `{s} {n1 n2}` is written explicitly
so the generated telescope is byte-identical to what auto-bound implicits
produced in the hand-written version (occurrence order s, n1, n2).

Deliberate exclusions:
- The eval kernels (`Substrait.Eval.evalFunc` match arms) stay hand-written —
  already factored through `binKernel` (guide 4.2), and a command cannot
  splice arms into an existing `match`.
- The `scoped infix*` sugar block stays in `Substrait/Typed/Expr.lean`:
  fixity and precedence vary per operator and the lines are one-liners.
- No registry, no environment extension: this is a pure two-def generator.

Mechanics (the lessons, so they are not re-paid):
- A `macro` is impossible — the declaration names are COMPUTED from the entry
  ident — and `elab_rules`'s kind inference rejects bare command-quotation
  patterns, so this is an `@[command_elab]` handler, mirroring core's
  `aux_def` (`Lean/Elab/AuxDef.lean`).
- Template references are spliced as PRERESOLVED idents (`mkCIdentFrom` with
  a single-backtick name).  Plain or `_root_.`-quoted template identifiers
  carry this module's quotation macro scopes, and resolution of scoped
  identifiers silently fails when the elaborator itself has a dotted
  declaration name (empirically verified on v4.33.0).  Preresolved idents
  skip name resolution entirely.
- The DECLARED names (`opAddSig`, `Expr.add`) are scope-free
  (`mkIdentFrom`), so they resolve against the use site's namespace —
  entries must be written inside `namespace Substrait.Typed`.
- Docstrings are spliced as syntax (the two stacked `/-- -/`s before the
  keyword), never synthesized from strings — the Verso doc parser needs real
  source positions.

Core-only: imports `Lean` (elaboration machinery) and nothing else.  This
module deliberately does NOT import `Substrait.Typed.Expr` (the command must
be usable FROM it); the referenced constants are named, not imported.
-/
import Lean

namespace Substrait.Meta

open Lean Lean.Parser.Command Lean.Elab.Command

/--
`declare_binop` — declare a binary operator's `FunctionSig` def and its
typed `Expr` wrapper from one table entry:

```
/-- <sig docstring> -/
/-- <wrapper docstring> -/
declare_binop <wrapperIdent> "<function name>", <urn>, <argType>, <retType>
```

See the module header for the generated shapes.
-/
syntax (name := declareBinop) docComment ? docComment ?
  "declare_binop " ident str ", " term ", " term ", " term : command

@[command_elab declareBinop]
def elabDeclareBinop : CommandElab := fun stx => do
  match stx with
  | `($[$sigDoc?:docComment]? $[$wrapDoc?:docComment]?
      declare_binop $op:ident $fn:str, $urn:term, $t:term, $ret:term) => do
    let opStr := op.getId.eraseMacroScopes.getString!
    -- Scope-free declaration names: resolve at the use site's namespace.
    let sigId := mkIdentFrom op (Name.mkSimple ("op" ++ opStr.capitalize ++ "Sig"))
    let wrapId := mkIdentFrom op (Name.mkStr (.mkSimple "Expr") opStr)
    -- Preresolved template references (see the module header for why).
    let FunctionSigId := mkCIdentFrom op `Substrait.Typed.FunctionSig
    let mkBinSigId := mkCIdentFrom op `Substrait.Typed.mkBinSig
    let SchemaId := mkCIdentFrom op `Substrait.Typed.Schema
    let ExprId := mkCIdentFrom op `Substrait.Typed.Expr
    let binCallId := mkCIdentFrom op `Substrait.Typed.Expr.binCall
    elabCommand (← `($[$sigDoc?:docComment]?
      def $sigId:ident (n1 n2 : Bool) : $FunctionSigId :=
        $mkBinSigId $fn $urn $t $ret n1 n2))
    elabCommand (← `($[$wrapDoc?:docComment]?
      def $wrapId:ident {s : $SchemaId} {n1 n2 : Bool}
          (a : $ExprId s $t n1) (b : $ExprId s $t n2) : $ExprId s $ret (n1 || n2) :=
        $binCallId ($sigId n1 n2) a b))
  | _ => Lean.Elab.throwUnsupportedSyntax

end Substrait.Meta
