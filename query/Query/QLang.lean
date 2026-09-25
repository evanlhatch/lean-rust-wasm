/-
# Query.QLang — the qlang! surface (the Lean-embedded query language)

The user-facing surface (design-forward-surface §3.2, landed as the
term-elab macro the note's seam paragraph named): a `qlang!{ … }`
QUOTATION — Lean terms, NOT a textkit grammar — elaborating directly
to the query lane's typed `Q`. The tree's term-elab precedents are
`Kit.Lane`'s `register_lane` + `Kit.Derive.Common`'s driver; the
parser is Lean's own (the pipeline is syntax-cat data, the elaborator
is a `TermElab`).

THE PIPELINE (v0 fragment = the bridge's join-free fragment):

```
qlang!{ from <schema> then select (<pred>) then project [.col, …]
       then union qlang!{ … } }
```

(The stage pipe is `then`, not the note's `|>` sketch: Lean 4.33's
syntax rules refuse `|>` twice over — a reserved parser token cannot
head a string atom, and `▸` is Lean's own term token (the cases
abbreviation), which the `from` term swallows. `then` is neither;
the pipeline reading is unchanged.)

- `from <schema>` — the base: a CLOSED `List Field` term, evaluated at
  elaboration (`evalExpr` — the `Kit.Lane.evalLaneItem` precedent);
  every later column reference resolves against its VALUE.
- `select (<pred>)` — the qpred mini-grammar: `col == "str"`,
  `col == 5`, `col > 5`, `col == col'` (u64), `&&`/`||`/`!` — the
  columns resolve BY NAME at ELABORATION time (first-name-match, the
  query lane's discipline); a miss is the closed-world Diag (QL0002 —
  the did-you-mean engine's face); a literal of the wrong type for the
  resolved column is QL0003.
- `project [.col, …]` — the order-preserving drop: the listed columns
  must be DISTINCT (QL0004) — the elaborator builds the `Cols`
  keep/skip chain positionally (the v2 `Cols`: proof-free, the result
  schema typing free — the `Q` index). A REORDERING projection is the
  named narrowing (the surface's pipes select in schema order; the
  wire's project node appends — the bridge header's note).
- `union qlang!{ … }` — the nested branch must read the SAME base
  schema and yield the SAME result schema (QL0005; the values are
  compared, the terms need not be).

Every refusal is a structured `Kit.Diag` rendered through the ONE
envelope; the codes are the QL family of the persisted registry
(`notes/code-registry.txt`). The elaborated term is SELF-TYPED (the
top-level ascription `: Q fs gs` pins every intermediate schema), so a
mis-typed query fails at ELABORATION, never at evaluation.

The five questions (notes/v3/01-core.md):
- **Root**: META — the surface stage over the typed core (the third
  layer of design-forward-surface §3.2; the typed core is `Q`, the
  lowering is `Query.TypedBridge.qToRel`).
- **Carrier grade**: none of its own — the elaborated form IS `Q` (the
  GADT + the by-name resolution are the typechecker).
- **Spine reading**: the surface stage — syntax → resolution → the
  typed term; the E-codes ride the one envelope.
- **Ladder rung**: none (the agreement theorems live at the bridge;
  the elaborator's refusals are the #guard_msgs teeth in
  QueryTests.QLangSpecs).
- **Gate row**: the code-registry gate (the QL family's rows) +
  QueryTests' qlang suite (the elaboration successes + the mis-typed
  refusals + the end-to-end agreement through `qToRel`).

Cone: imports Lean + Kit.Diag/Kit.Derive.Common (the META modules'
allowance — the Kit.Lane precedent) + Query.TypedBridge. NOT imported
by `Query.TypedBridge` (the bridge stays core); `Query.lean` mounts
the surface.
-/

import Lean
import Kit.Diag
import Kit.Derive.Common
import Query.TypedBridge

namespace Query.QLang

open Lean Elab Meta SchemaCore

/-! ## The QL family (the surface's E-codes; QL0001 is the bridge's) -/

def eQL0002 : Kit.ECode := ⟨"QL0002"⟩
def eQL0003 : Kit.ECode := ⟨"QL0003"⟩
def eQL0004 : Kit.ECode := ⟨"QL0004"⟩
def eQL0005 : Kit.ECode := ⟨"QL0005"⟩

/-! ## The syntax -/

/-- The predicate atoms: column-vs-literal and column-vs-column. -/
declare_syntax_cat qpred
syntax ident " == " str : qpred
syntax ident " == " num : qpred
syntax ident " > " num : qpred
syntax ident " == " ident : qpred
syntax:40 qpred:41 " || " qpred:40 : qpred
syntax:50 qpred:51 " && " qpred:50 : qpred
syntax:max "!" qpred:max : qpred
syntax:max "(" qpred ")" : qpred

/-- One pipeline stage. (The atoms are single words/symbols: Lean's
    syntax-atom rule forbids interior whitespace after trim — the
    pipe `then` is its own atom, the payloads their own.) -/
declare_syntax_cat qcol
syntax "." ident : qcol

declare_syntax_cat qlangItem
syntax "from " term : qlangItem
syntax "then" "select" "(" qpred ")" : qlangItem
syntax "then" "project" "[" qcol,* "]" : qlangItem
syntax "then" "union" "qlang!" "{" qlangItem* "}" : qlangItem

/-- THE SURFACE: `qlang!{ from s then select (…) then … }` — elaborates to
    the typed `Q fs gs`. -/
syntax (name := qlangBlock) "qlang!" "{" qlangItem* "}" : term

/-! ## The resolution kit (elaboration-time, over the evaluated schema) -/

/-- First-name-match resolution: the column's ordinal + its type —
    the query lane's `RowVals.project?` discipline at elaboration. -/
def findCol (fs : List Field) (n : String) : Option (Nat × Ty) :=
  match fs with
  | [] => none
  | f :: rest =>
      if f.name == n then some (0, f.ty)
      else (findCol rest n).map (fun p => (p.1 + 1, p.2))

/-- The schema's names (the closed-world's valid space). -/
def schemaNames (fs : List Field) : List String := fs.map (·.name)

/-- The unknown-column refusal: the closed-world Diag — got + the
    valid space + the ONE engine's did-you-mean (unforgable). -/
def unknownColDiag (got : String) (fs : List Field) : Kit.Diag :=
  Kit.Diag.closedWorld eQL0002
    s!"qlang: column `{got}` does not resolve in the current schema"
    .error got (schemaNames fs)

/-- Evaluate a closed `List Field` term at elaboration (the
    `Kit.Lane.evalLaneItem` precedent — the compiler's interpreter). A
    non-closed or ill-typed schema term refuses. -/
unsafe def evalSchema (stx : Syntax) : TermElabM (List Field) := do
  let tyE := Lean.Expr.app (Lean.Expr.const `List [Lean.Level.zero])
    (Lean.Expr.const `SchemaCore.Field [])
  let e ← withRef stx <| Lean.Elab.Term.elabTerm stx tyE
  try
    Lean.Meta.evalExpr (List Field) tyE e
  catch e =>
    let _ := e
    Kit.Derive.Common.throwDiag eQL0005
      "qlang: the base schema must be a closed `List Field` term — \
      the surface resolves columns against the schema's VALUE"

/-! ## The elaborator -/

/-- The pipeline state: the Q term under construction + the base
    schema (term + value) + the current schema (term + value). -/
structure QStk where
  q : Syntax
  fsStx : Syntax
  fsVal : List Field
  gsStx : Syntax
  gsVal : List Field

/-- The kept-schema VALUE of a keep-list (the selected ordinals,
    ascending) over the current schema. -/
def keptFields (gsVal : List Field) (ps : List Nat) : List Field :=
  ps.foldr (fun i acc =>
    match gsVal[i]? with
    | some f => f :: acc
    | none => acc) []

/-- The column's resolution at the throwing face (the atom arms'
    shared plumbing): a miss is the closed-world Diag (QL0002). -/
private def resolveColOrThrow (fs : List Field) (x : Syntax) :
    TermElabM (Nat × Ty) :=
  match findCol fs x.getId.toString with
  | none => throwError m!"{unknownColDiag x.getId.toString fs}"
  | some r => pure r

/-- The pred application's term face (the monadically-bound quote,
    ONCE): the ctor + the bare splices (the antiq-splice grammar has no
    `: T` ascription form). -/
private def mkPredApp (ctor : Name) (args : Array Lean.Term) : TermElabM Syntax := do
  let c : Lean.Term := Lean.mkIdent ctor
  let t ← `($c $args*)
  pure t.raw

/-- The predicate elaboration: resolve every column against the
    current schema's VALUE, check the literal's type against the
    resolved column's type, emit the `Pred` constructor. -/
private unsafe def elabPred (fs : List Field) (p : Syntax) : TermElabM Syntax :=
  match p with
  | `(qpred| $x:ident == $s:str) => do
      let r ← resolveColOrThrow fs x
      match r with
      | (_, .string) =>
          mkPredApp `SchemaCore.Pred.strEqLit
            #[⟨Lean.Syntax.mkStrLit x.getId.toString⟩, ⟨s⟩]
      | (_, ty) =>
          Kit.Derive.Common.throwDiag eQL0003
            s!"qlang: column `{x.getId.toString}` has type {repr ty}, not string — \
              the `== \"…\"` form needs a string column"
  | `(qpred| $x:ident == $k:num) => do
      let r ← resolveColOrThrow fs x
      match r with
      | (_, .u64) =>
          mkPredApp `SchemaCore.Pred.u64EqLit
            #[⟨Lean.Syntax.mkStrLit x.getId.toString⟩, ⟨k⟩]
      | (_, ty) =>
          Kit.Derive.Common.throwDiag eQL0003
            s!"qlang: column `{x.getId.toString}` has type {repr ty}, not u64 — \
              the `== <num>` form needs a u64 column"
  | `(qpred| $x:ident > $k:num) => do
      let r ← resolveColOrThrow fs x
      match r with
      | (_, .u64) =>
          mkPredApp `SchemaCore.Pred.u64GtLit
            #[⟨Lean.Syntax.mkStrLit x.getId.toString⟩, ⟨k⟩]
      | (_, ty) =>
          Kit.Derive.Common.throwDiag eQL0003
            s!"qlang: column `{x.getId.toString}` has type {repr ty}, not u64 — \
              the `> <num>` form needs a u64 column"
  | `(qpred| $x:ident == $y:ident) => do
      let rx ← resolveColOrThrow fs x
      let ry ← resolveColOrThrow fs y
      match rx, ry with
      | (_, .u64), (_, .u64) =>
          mkPredApp `SchemaCore.Pred.u64Eq
            #[⟨Lean.Syntax.mkStrLit x.getId.toString⟩,
              ⟨Lean.Syntax.mkStrLit y.getId.toString⟩]
      | (_, t1), (_, t2) =>
          Kit.Derive.Common.throwDiag eQL0003
            s!"qlang: the column equality needs two u64 columns, got \
              `{x.getId.toString}` : {repr t1} and `{y.getId.toString}` : {repr t2}"
  | `(qpred| $a:qpred && $b:qpred) => do
      mkPredApp `SchemaCore.Pred.and
        #[(⟨← elabPred fs a⟩ : Term), (⟨← elabPred fs b⟩ : Term)]
  | `(qpred| $a:qpred || $b:qpred) => do
      mkPredApp `SchemaCore.Pred.or
        #[(⟨← elabPred fs a⟩ : Term), (⟨← elabPred fs b⟩ : Term)]
  | `(qpred| !$p:qpred) => do
      mkPredApp `SchemaCore.Pred.not #[(⟨← elabPred fs p⟩ : Term)]
  | `(qpred| ($p:qpred)) => elabPred fs p
  | _ => Kit.Derive.Common.throwDiag eQL0005 "qlang: malformed predicate — valid forms: \
      `col == \"str\"`, `col == <num>`, `col > <num>`, `col == col` (u64), \
      combined with `&&`, `||`, `!`"

-- One stage's step + the union branch's body elaboration — MUTUAL
-- (the branch's stages recurse into the same step fold).
mutual

private unsafe def elabItem (stk : QStk) (it : Syntax) : TermElabM QStk :=
  match it with
  | `(qlangItem| then select ($p:qpred)) => do
      let pStx ← elabPred stk.gsVal p
      let qSel : Lean.Term := Lean.mkIdent `Query.Q.select
      let pT : Lean.Term := ⟨pStx⟩
      let qT : Lean.Term := ⟨stk.q⟩
      let q ← `($qSel $pT $qT)
      pure { stk with q := q.raw }
  | `(qlangItem| then project [$[$cols:qcol],*]) => do
      -- resolve every listed column (first-name-match), DISTINCT (the
      -- drop projection's named narrowing: no duplicates)
      let mut ps : List Nat := []
      for c in cols do
        let cname : String :=
          match c with | `(qcol| .$ci:ident) => ci.getId.toString | _ => ""
        match findCol stk.gsVal cname with
        | none => throwError m!"{unknownColDiag cname stk.gsVal}"
        | some (i, _) =>
            if ps.contains i then
              (Kit.Derive.Common.throwDiag eQL0004
                s!"qlang: column `{cname}` is listed twice — \
                  the drop projection is duplicate-free (the bag reading \
                  of duplicates is the named boundary)")
            else
              ps := ps ++ [i]
      -- build the keep/skip chain positionally, from the DEEPEST
      -- position out (the chain's outermost ctor is the source's head)
      let mut pending := ps
      let mut chain : Lean.Term := ⟨Lean.mkIdent `Query.Cols.nil⟩
      let mut p := stk.gsVal.length
      while p > 0 do
        p := p - 1
        let keepThis := match pending.getLast? with
          | some q => q == p
          | none => false
        if keepThis then
          pending := pending.take (pending.length - 1)
          let k : Lean.Term := Lean.mkIdent `Query.Cols.keep
          let next ← `($k $chain)
          chain := next
        else
          let k : Lean.Term := Lean.mkIdent `Query.Cols.skip
          let next ← `($k $chain)
          chain := next
      let qProj : Lean.Term := Lean.mkIdent `Query.Q.project
      let chT : Lean.Term := chain
      let qT : Lean.Term := ⟨stk.q⟩
      let q ← `($qProj $chT $qT)
      let fld : Lean.Term := Lean.mkIdent `Query.Cols.fields
      let gsT : Lean.Term := ⟨stk.gsStx⟩
      let gs ← `($fld $gsT $chT)
      pure ({ stk with q := q.raw, gsStx := gs.raw, gsVal := keptFields stk.gsVal ps })
  | `(qlangItem| then union qlang!{$nested*}) => do
      -- the nested branch: SAME base, SAME result schema (the VALUES
      -- compared; the terms need not be)
      let nst ← elabNested stk.fsStx stk.fsVal (nested.toList.map (·.raw))
      if !(nst.2 == stk.gsVal) then
        (Kit.Derive.Common.throwDiag eQL0005
          s!"qlang: the union's branch's result schema differs from the \
            running query's — valid: the current schema's shape \
            ({schemaNames stk.gsVal})")
      let qUnion : Lean.Term := Lean.mkIdent `Query.Q.union
      let qT : Lean.Term := ⟨stk.q⟩
      let nT : Lean.Term := ⟨nst.1⟩
      let q ← `($qUnion $qT $nT)
      pure { stk with q := q.raw }
  | _ => (Kit.Derive.Common.throwDiag eQL0005 "qlang: malformed pipeline stage — valid: \
      `from <schema>`, `then select (<pred>)`, `then project [.col, …]`, \
      `then union qlang!{ … }`")

/-- The nested body's elaboration (the union branch): its own `from`
    must evaluate to the OUTER base's value; the result is the nested
    Q term + its result schema's value. -/
private unsafe def elabNested (fsStx : Syntax) (fsVal : List Field)
    (items : List Syntax) : TermElabM (Syntax × List Field) :=
  match items with
  | it :: rest =>
      match it with
      | `(qlangItem| from $schemaT:term) => do
          let nfsVal ← evalSchema schemaT
          if !(nfsVal == fsVal) then
            Kit.Derive.Common.throwDiag eQL0005
              s!"qlang: the union's branch reads a different base schema — \
                valid: the enclosing query's base"
          let stk0 : QStk :=
            ({ q := Lean.mkIdent `Query.Q.table, fsStx := fsStx, fsVal := fsVal, gsStx := fsStx, gsVal := nfsVal })
          let stk ← rest.foldlM (fun acc r => elabItem acc r) stk0
          pure (stk.q, stk.gsVal)
      | _ => (Kit.Derive.Common.throwDiag eQL0005
          "qlang: the union's branch must start with `from <schema>`")
  | [] => (Kit.Derive.Common.throwDiag eQL0005 "qlang: empty union branch")

end

/-- The stage fold over the post-`from` items. -/
private unsafe def elabItems (stk : QStk) (items : List Syntax) :
    TermElabM QStk :=
  match items with
  | [] => pure stk
  | it :: rest => do
      let stk' ← elabItem stk it
      elabItems stk' rest

@[term_elab Query.QLang.qlangBlock]
unsafe def elabQLang : Lean.Elab.Term.TermElab
  | `(qlang!{$[$items:qlangItem]*}), _ => do
      match items.toList.map (·.raw) with
      | it :: rest =>
          match it with
          | `(qlangItem| from $schemaT:term) => do
              let fsVal ← evalSchema schemaT
              let stk0 : QStk :=
                ({ q := Lean.mkIdent `Query.Q.table, fsStx := schemaT, fsVal := fsVal, gsStx := schemaT, gsVal := fsVal })
              let stk ← elabItems stk0 rest
              -- THE SELF-TYPING PIN: the pipeline term elaborates
              -- AGAINST `Q fs gs` as its expected type — the computed
              -- result schema pins every intermediate one (the
              -- determinacy typing free; the pin rides expectedType,
              -- not an ascription — the quote-antiq grammar owns `:`)
              let qAs : Lean.Term := ⟨stk.q⟩
              let fsAs : Lean.Term := ⟨stk.fsStx⟩
              let gsAs : Lean.Term := ⟨stk.gsStx⟩
              let tyQ ← `(Query.Q $fsAs $gsAs)
              let tyE ← Lean.Elab.Term.elabType tyQ
              Lean.Elab.Term.elabTerm qAs.raw (some tyE)
          | _ => (Kit.Derive.Common.throwDiag eQL0005
              "qlang: the pipeline must start with `from <schema>`")
      | [] => (Kit.Derive.Common.throwDiag eQL0005
          "qlang: empty body — valid usage: \
          `qlang!{ from <schema> then select (…) then project […] }`")
  | _, _ => throwUnsupportedSyntax

end Query.QLang
