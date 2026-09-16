/-
# Substrait.Emit.Text

The canonical text emitter for `Proto.Plan`, replicating the substrait-explain
0.8 text format **byte-for-byte** (the round-trip contract: `parse → format`
is text-identity, so an emitter that matches the format producer yields text
the parser accepts and reformats identically).

Grammar facts this module encodes (cross-checked against the substrait-explain
0.8.0 source and `notes/research-substrait-explain.md`):

- Top level: `=== Extensions` (URNs, then Functions/Types/Type Variations),
  `=== Plan`, then the relations (one blank line between plan rels).
- Extensions section: `@{anchor:3}: {urn}`, `#{anchor:3} @{urnRef:3}: {name}`,
  sorted by anchor; sections with no entries are omitted; an empty extension
  set omits the whole section.
- Relation headers: `Read[units => health:i32?, regen:i32?]`,
  `Filter[gt($0, 0:i32):bool? => $0, $1]`,
  `Project[$0, $1, add($0, $1):i32?]`, `Sort[($0, &AscNullsFirst) => $0, $1]`,
  `Fetch[limit=10 => $0, $1]`, `Join[&Inner, cond => $0, $1, $2]`,
  `Set[&UnionAll => $0, $1]`, `Cross[$0, $1, $2]`.  Children indented by
  2 spaces per level.
- Expressions: `$n` refs, `42:i32` literals (type suffix per syntax default),
  `add($0, $1):i32?` calls (anchors suppressed when names are unique).
- Nullability: `?` = nullable, nothing = required; `Unspecified` is a hard
  error — the emitter never writes `⁉`.

Write/Update/Ddl and Extension* rels are **not in the grammar**: any plan
containing them is rejected with an `Except` error — this emitter is
intentionally strict, matching the parser's hard-failure style.
-/
import Substrait.Proto.Plan
import Substrait.Grammar
open Substrait.Grammar

namespace Substrait.Emit.Text

/-! ## Primitive formatting -/

/-- Repeat a string `n` times (core has no `String.replicate` — checked
    the 4.33 toolchain's Init/Data/String: only `List.replicate` exists). -/
def replicate (s : String) (n : Nat) : String :=
  (List.range n).foldl (fun acc _ => acc ++ s) ""

/-- Right-align a nat in a field of width `n` (textify's `{anchor:3}`). -/
def rightJustify (n : Nat) (x : Nat) : String :=
  let s := toString x
  if s.length ≥ n then s else replicate " " (n - s.length) ++ s

/-- Is `c` a plain ASCII graphic-identifier character? -/
def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_'

/-- Is `s` a valid bare identifier (ASCII letter first, alnum/underscore after)? -/
def isIdentifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => c.isAlpha && rest.all isIdentChar

/-- Escape a string for quoted identifiers and string literals (textify `escaped`). -/
def escape (s : String) : String :=
  s.toList.foldl (fun acc c =>
    acc ++ match c with
    | '\n' => "\\n" | '\t' => "\\t" | '\r' => "\\r"
    | '\\' => "\\\\" | '"' => "\\\"" | '\'' => "\\'"
    | c => toString c) ""

/-- `Name` — bare when an identifier, else double-quoted. -/
def name (n : String) : String :=
  if isIdentifier n then n else "\"" ++ escape n ++ "\""

/-- Join a list with a separator.  `abbrev` (reducible): proofs rewrite through
    to core `String.intercalate` lemmas directly. -/
abbrev sep (d : String) (xs : List String) : String := String.intercalate d xs

/-- `$n`. -/
def fieldRef (ord : Nat) : String := dollarTok ++ toString ord

/-! ## Types (mirrors textify/types.rs) -/

/-- Nullability suffix: `?` / `` — never `⁉`. -/
def nullSuffix : Proto.Nullability → Except String String
  | .nullable     => pure "?"
  | .required     => pure ""
  | .unspecified  => throw "cannot emit Unspecified nullability — the text emitter writes explicit nullability only"

/-- A parameter list `<a, b>` (empty → nothing). -/
def params (ps : List (Except String String)) : Except String String := do
  let vs ← ps.mapM id
  if vs.isEmpty then pure "" else pure ("<" ++ sep sepTok vs ++ gtTok)

/-! Render loop of the type text: `typeTextBase` is the outer shape without the
outer nullability suffix (nested elements keep their own nullability, so
`list<i32?>` and `map<i8, string?>` render exactly); `typeText` appends the
outer `?`.  (`mutual` needed: bases recurse through full element texts.) -/
mutual
  /-- The *outer* shape of a `Proto.PType` — `bool i8 … binary`, `decimal<P,S>`,
  `list<T>`, `map<K,V>`, `struct<T,…>`.  User-defined types cannot be rendered
  without a registry (extensions-only); they hard-error here.  The scalar
  prefixes come from `ScalarCtor.prefix` — the SAME table the
  decoder's `parseScalarType` folds, so emitter and parser cannot drift. -/
  def typeTextBase : Proto.PType → Except String String
    | .bool _         => pure (ScalarCtor.prefix .bool)
    | .i8 _           => pure (ScalarCtor.prefix .i8)
    | .i16 _          => pure (ScalarCtor.prefix .i16)
    | .i32 _          => pure (ScalarCtor.prefix .i32)
    | .i64 _          => pure (ScalarCtor.prefix .i64)
    | .fp32 _         => pure (ScalarCtor.prefix .fp32)
    | .fp64 _         => pure (ScalarCtor.prefix .fp64)
    | .string _       => pure (ScalarCtor.prefix .string)
    | .binary _       => pure (ScalarCtor.prefix .binary)
    | .decimal p s _  => pure (TCtor.prefix .decimal ++ toString p ++ commaTok ++ toString s ++ gtTok)
    | .list e _       => do let es ← typeText e; pure (TCtor.prefix .list ++ es ++ gtTok)
    | .map k v _      => do
        let ks ← typeText k; let vs ← typeText v
        pure (TCtor.prefix .map ++ ks ++ sepTok ++ vs ++ gtTok)
    | .struct fs _    => do
        let f' ← fs.mapM (fun t => typeText t)
        pure (TCtor.prefix .struct ++ sep sepTok f' ++ gtTok)
    | .userDefined anchor _ _ =>
        throw s!"cannot emit user-defined type with anchor {anchor} (no extension registry in Emit.Text)"

  /--
  Render a `Proto.PType` with its explicit nullability suffix: `bool?`, `i32`, …
  (`Proto.PType.nullability` feeds `nullSuffix`).  This is the type text the
  wire grammar writes for column types and call output types, so `health:i32?`
  and `add($0, $1):i32?` render exactly.
  -/
  def typeText (t : Proto.PType) : Except String String := do
    let base ← typeTextBase t
    let n ← nullSuffix (Proto.PType.nullability t)
    pure (base ++ n)
end

/-- **The load-bearing stitch**: the emitter's scalar output IS the table's
    prefix — the same table `Decode.parseScalarType` folds. The decode∘emit
    round-trip now goes through ONE shared definition on both sides; a table
    edit moves emitter and parser together, and this theorem tracks it. -/
theorem typeTextBase_scalar (c : ScalarCtor) (n : Proto.Nullability) :
    typeTextBase (ScalarCtor.toPType c n) = .ok (ScalarCtor.prefix c) := by
  cases c <;> simp [typeTextBase, ScalarCtor.toPType,
    ScalarCtor.prefix]
  all_goals rfl

/-! ## The plan extension context -/

/-- Extension lookup for a plan (mirrors `SimpleExtensions`). -/
structure Ctx where
  urns : List (Nat × String)
  -- (urnRef, kind, anchor, name); kind: 0=function, 1=type, 2=typeVariation
  extensions : List (Nat × Nat × Nat × String)
deriving Inhabited

namespace Ctx

/-- urnAnchor → urn. -/
def urnOf (c : Ctx) (a : Nat) : Option String :=
  (c.urns.find? (fun (u, _) => u == a)).map fun x => x.2

/-- (kind, anchor) → name. -/
def nameOf (c : Ctx) (kind : Nat) (a : Nat) : Option String :=
  (c.extensions.find? (fun (_, k, x, _) => k == kind && x == a)).map fun x => x.2.2.2

/-- All declared names of a kind (uniqueness checks). -/
def namesOf (c : Ctx) (kind : Nat) : List String :=
  (c.extensions.filter (fun (_, k, _, _) => k == kind)).map fun x => x.2.2.2

/-- Build the context from a plan. The kind numbers come from the shared
    `Grammar.extKindGrammar` table (`ExtKind.num` — the SAME rows the
    decoder's `parseDeclBlocks` reconstructs). -/
def ofPlan (p : Proto.Plan) : Ctx :=
  { urns := p.extensionUrns.map fun u => (u.extensionUrnAnchor, u.urn)
    extensions := p.extensions.map fun d =>
      match d with
      | .function u a n => (u, ExtKind.num .function, a, n)
      | .extType u a n  => (u, ExtKind.num .extType, a, n)
      | .typeVariation u a n => (u, ExtKind.num .typeVariation, a, n) }

/--
A function's rendered name (± `:sig`, ± `#anchor`): mirrors `NamedAnchor`
(unique names and unique base names are suppressed).
-/
def functionName (c : Ctx) (a : Nat) : Except String String :=
  match c.nameOf (ExtKind.num .function) a with
  | none => throw s!"function anchor {a} is not declared in this plan's extensions"
  | some fullName =>
      let base := (fullName.splitOn ":").headD fullName
      let all := c.namesOf (ExtKind.num .function)
      let uniqueMatches := all.filter (fun n => n == fullName)
      let baseMatches := all.filter (fun n => (n.splitOn ":").headD n == base)
      let unique := uniqueMatches.length == 1
      let baseUnique := baseMatches.length == 1
      let showSignature := !baseUnique
      let needsAnchor := !unique || ((!fullName.contains ':') && !baseUnique)
      pure ((if showSignature then fullName else base) ++ (if needsAnchor then ("#" ++ toString a) else ""))

end Ctx

/-! ## Expressions (mirrors textify/expressions.rs) -/

/-- The literal type-suffix name — the shared table's token
    (`Substrait.Grammar.literalTypeToken`): the nine scalar literal types
    carry their `ScalarCtor.prefix` (the SAME table `parseType` lexes), so
    emitter and decoder cannot drift; `null` is the literal-only token. -/
def literalTypeName (lt : Proto.LiteralType) : String := literalTypeToken lt

/-- Literal kinds whose value syntax needs no type suffix. -/
def isDefaultForSyntax : Proto.LiteralType → Bool
  | .bool _ | .string _ | .binary _ | .i64 _ | .fp64 _ => true
  | _ => false

/-- The value text of a literal (no type suffix). -/
def literalValue : Proto.LiteralType → String
  | .bool b       => if b then "true" else "false"
  | .i8 v | .i16 v | .i32 v | .i64 v => toString v
  | .fp32 v | .fp64 v => toString v
  | .string s     => "'" ++ escape s ++ "'"
  | .binary _     => binarySentinel         -- show_literal_binaries=false default
                                       -- the token is single-sourced in
                                       -- `Substrait.Grammar.binarySentinel` (a VALUE
                                       -- sentinel, not a name-table row);
                                       -- `Decode.Expr.parseLiteral` scans the same
                                       -- constant.
  | .null _       => "null"   -- value word; `parseLiteral` pattern-matches it
                              -- (char patterns cannot consume a constant — noted)

/-- Render a literal with its type suffix (mirrors `Literal::textify`). -/
def literal : Proto.Literal → Except String String
  | { literalType := .null t, nullable := _ } => do
      let ts ← typeText t
      pure ("null" ++ colonTok ++ ts)
  | { literalType := lt, nullable := n } =>
      let suffix : String :=
        if n || !isDefaultForSyntax lt then
          colonTok ++ literalTypeName lt ++ (if n then "?" else "")
        else ""
      pure (literalValue lt ++ suffix)

/-- The `:type` suffix of a function call's output type (mandatory in the grammar). -/
def typeSuffix (t : Proto.PType) : Except String String := do
  let ts ← typeText t
  pure (colonTok ++ ts)

/-- A scalar-function call renders as `name(args...)suffix` — shared by
    `expr`'s `.scalarFunction` arm and `measure`. `rec` = the caller's
    expression recursion (broken out so the helper can live next to
    `measure`, below `expr`, without a mutual block). -/
def callText (ctx : Ctx) (rec : Proto.Expression → Except String String)
    (anchor : Nat) (args : List Proto.Expression)
    (out : Proto.PType) : Except String String := do
  let na ← Ctx.functionName ctx anchor
  let as' ← args.mapM rec
  let fs ← typeSuffix out
  pure (na ++ lparenTok ++ sep sepTok as' ++ rparenTok ++ fs)

/-- Render any expression. -/
-- v0: emitter; totality not required
partial def expr (ctx : Ctx) : Proto.Expression → Except String String
  | .literal lit   => literal lit
  | .field ref     => pure (fieldRef ref.ordinal)
  | .scalarFunction fr args out => callText ctx (expr ctx) fr args out
  | .ifThen ifs elseE => do
      let cs ← ifs.mapM (fun (ifc, thenc) => do
        let i ← expr ctx ifc; let t ← expr ctx thenc
        pure (i ++ ifArrowTok ++ t))
      let e ← expr ctx elseE
      pure (kwIfThen ++ sep sepTok cs ++ sepTok ++ ifElseTok ++ e ++ rparenTok)
  | .cast input targetType fb => do
      let i ← expr ctx input
      let t ← typeText targetType
      let fbTxt := match CastFbCtor.ofBehavior fb with
        | some c => c.token
        | none => ""
      pure (lparenTok ++ i ++ rparenTok ++ castTok ++ fbTxt ++ t)
  | .subquery _ _  => throw "cannot emit subqueries in the text format"

/-- An aggregate measure renders like a scalar function. -/
def measure (ctx : Ctx) (m : Proto.AggregateFunction) : Except String String :=
  callText ctx (expr ctx) m.functionReference m.args m.outputType


/-! ## Relation rendering -/

/-- The emit kind of a rel's `common`. -/
def emitOf (c : Option Proto.RelCommon) : Option Proto.EmitKind :=
  c.bind fun r => r.emit

/-- A rendered output column. -/
inductive Col where
  | ref (ord : Nat)
  | namedField (nm ty : String)
  | e (txt : String)
deriving Repr

/-- The column at index `i`, or an error (core has no `List.get?` —
    checked the 4.33 toolchain: the modern spelling is `List.getElem?`,
    whose error TEXT we control here). -/
def colAt (cols : List Col) (i : Nat) : Except String Col :=
  let rec go : List Col → Nat → Except String Col
    | [], _ => throw s!"column index {i} out of range (width {cols.length})"
    | c :: _, 0 => pure c
    | _ :: rest, k + 1 => go rest k
  go cols i

/-- Render a column. -/
def colText : Col → String
  | .ref ord        => fieldRef ord
  | .namedField n t => name n ++ colonTok ++ t
  | .e txt          => txt

/-- Direct (pre-emit) output columns as text. -/
def directCols (cols : List Col) : String := sep sepTok (cols.map colText)

/--
The emit/output clause of a rel (mirrors `Emitted::write_output_clause`),
LEADING SPACE INCLUDED — the clause IS `Grammar.arrowTok`/`plusArrowTok`
(± the `pipeTok` mapping tail) plus the columns, so the caller concatenates
header ++ clause directly and the decoder's `expect arrowTok` consumes
exactly this (`Grammar.emptyGroupTok_arrowTok` pins the empty-group fusion).
`implicit` selects `=>` vs `+>` (Direct/Implicit relations use `=>`; Read's
explicit output uses `+>`).
-/
def outputClause (implicit : Bool) (cols : List Col) (emit : Option Proto.EmitKind) : Except String String :=
  let direct := directCols cols
  if implicit then
    match emit with
    | none            => pure (arrowTok ++ direct)
    | some .direct    => pure (arrowTok ++ direct)
    | some (.emit m)  => pure (arrowTok ++ sep sepTok (m.map fieldRef))
  else
    match emit with
    | none            => pure (plusArrowTok ++ direct)
    | some .direct    => pure (plusArrowTok ++ direct)
    | some (.emit m)  => pure (plusArrowTok ++ direct ++ pipeTok ++ sep sepTok (m.map fieldRef))

/-- The emitted width of a rel (how many output columns its parent sees). -/
-- v0: emitter; totality not required
partial def relWidth : Proto.Rel → Except String Nat
  | .read r      => pure (match r.baseSchema with | some s => s.fields.length | none => 0)
  | .filter r    => relWidth r.input
  | .project r   => do
      let w ← relWidth r.input
      match emitOf r.common with
      | some (.emit m) => pure m.length
      | _ => pure (w + r.expressions.length)
  | .aggregate r => pure (r.groupingExpressions.length + r.measures.length)
  | .sort r      => relWidth r.input
  | .fetch r     => relWidth r.input
  | .join r      => do
      let l ← relWidth r.left; let rw ← relWidth r.right
      pure (r.joinType.width l rw)
  | .cross r     => do let l ← relWidth r.left; let rw ← relWidth r.right; pure (l + rw)
  | .set r       => do
      if r.inputs.isEmpty then pure 0
      else
        let ws ← r.inputs.mapM (fun rl => relWidth rl)
        pure ((List.foldl (fun acc w => acc + w) 0 ws) / ws.length)
  | .write _          => throw "cannot compute output width of WriteRel in the text format"
  | .extensionLeaf _  => throw "cannot emit ExtensionLeafRel in the text format"
  | .extensionSingle _=> throw "cannot emit ExtensionSingleRel in the text format"
  | .extensionMulti _ => throw "cannot emit ExtensionMultiRel in the text format"

/-- Join type display names (`&Inner`, …) — the emitter half of
    `Substrait.Grammar.joinGrammar`. `unspecified` has no row and
    hard-errors. -/
def joinTypeName (j : Proto.JoinType) : Except String String :=
  match JoinCtor.ofJoinType j with
  | some c => pure c.name
  | none => throw "cannot emit Unspecified join type in the text format"

/-- Set op display names (`&UnionAll`, …) — the emitter half of
    `Substrait.Grammar.setGrammar`. `unspecified` has no row and
    hard-errors. -/
def setOpName (op : Proto.SetOp) : Except String String :=
  match SetCtor.ofSetOp op with
  | some c => pure c.name
  | none => throw "cannot emit Unspecified set op in the text format"

/-- Sort direction display name (no `&`; the caller adds it) — the emitter
    half of `Substrait.Grammar.sortDirGrammar`. `unspecified` has no row;
    the caller rejects it before rendering, so the fallback token never
    reaches the wire. -/
def sortDirName (d : Proto.SortDirection) : String :=
  match SortDirCtor.ofSortDirection d with
  | some c => c.name
  | none => "Unspecified"  -- the caller rejects Unspecified instead

/-- A rel's output clause over its full width of indirect refs — the
    Filter/Sort/Fetch arms' shared piece (a ref-clause with no mapping).
    -/
def refOutput (w : Nat) (common : Option Proto.RelCommon) : Except String String :=
  outputClause true ((List.range w).map .ref) (emitOf common)

/-- A rel's header over its indented child's lines — the unary-rel arms'
    shared `child` recursion (the `rec`-style: the caller passes
    `relLines` itself, breaking what would otherwise be a helper⇄relLines
    cycle). -/
def wrapChild (rec : Ctx → String → Proto.Rel → Except String (List String))
    (ctx : Ctx) (indent : String) (input : Proto.Rel) (header : String) :
    Except String (List String) := do
  let child ← rec ctx (indent ++ indentUnit) input
  pure ([header] ++ child)

/-- Render a relation (headers + children) as indented lines. -/
-- v0: emitter; totality not required
partial def relLines (ctx : Ctx) (indent : String) : Proto.Rel → Except String (List String)
  | .read r => do
      match r.readType with
      | .namedTable names =>
          let tableName := sep dotTok (names.map name)
          let fields : List Col ← match r.baseSchema with
            | some s => do
                let ft ← (s.fields.zip s.names).mapM (fun (ty, nm) => do
                  let ts ← typeText ty
                  pure (.namedField nm ts : Col))
                if ft.isEmpty then pure [.e "_"] else pure ft
            | none => pure [.e "_"]
          let out ← match emitOf r.common with
            | none => outputClause true fields none
            | some e => outputClause false fields (some e)
          pure [indent ++ kwRead ++ tableName ++ out ++ "]"]
      | .virtualTable _ _ => throw "Read:Virtual is not yet supported by the typed emitter"
  | .filter r => do
      let c ← expr ctx r.condition
      let w ← relWidth r.input
      let out ← refOutput w r.common
      wrapChild relLines ctx indent r.input (indent ++ kwFilter ++ c ++ out ++ "]")
  | .project r => do
      let w ← relWidth r.input
      let ex ← r.expressions.mapM (expr ctx)
      let cols : List Col := (List.range w).map .ref ++ ex.map .e
      -- textify `write_implicit_columns` (textify/rels.rs): for a Project with
      -- an explicit `Emit.output_mapping` the *argument list is the mapping-*
      -- selected direct columns (the grammar's `project_argument_list` has no
      -- emit clause, so textify bakes the mapping into the args).
      let shown ← match emitOf r.common with
        | some (.emit m) => m.mapM (fun i => colAt cols i)
        | _ => pure cols
      let child ← relLines ctx (indent ++ indentUnit) r.input
      pure ([indent ++ kwProject ++ directCols shown ++ "]"] ++ child)
  | .aggregate r => do
      let groupArgs : List String ←
        if r.groupingExpressions.isEmpty then pure [emptyGroupTok]
        else r.groupingExpressions.mapM (expr ctx)
      let ms ← r.measures.mapM (fun m => measure ctx m.measure)
      let gexprs : List String ← r.groupingExpressions.mapM (expr ctx)
      let cols : List Col := gexprs.map .e ++ ms.map .e
      let out ← outputClause true cols (emitOf r.common)
      let child ← relLines ctx (indent ++ indentUnit) r.input
      pure ([indent ++ kwAggregate ++ sep sepTok groupArgs ++ out ++ "]"] ++ child)
  | .sort r => do
      let sortArgs ← r.sorts.mapM (fun sf => do
        let rn ← match sf.expr with
          | .field f => pure (fieldRef f.ordinal)
          | _ => throw "SortField must be a field reference in the text grammar"
        match sf.direction with
        | .unspecified => throw "cannot emit Unspecified sort direction in the text format"
        | d => pure (lparenTok ++ rn ++ sortAmpTok ++ sortDirName d ++ rparenTok))
      let w ← relWidth r.input
      let out ← refOutput w r.common
      wrapChild relLines ctx indent r.input (indent ++ kwSort ++ sep sepTok sortArgs ++ out ++ "]")
  | .fetch r => do
      let named : List String :=
        (r.limit.map (fun n => fetchLimitName ++ eqTok ++ toString n)).toList ++
        (r.offset.map (fun n => fetchOffsetName ++ eqTok ++ toString n)).toList
      let argsText := if named.isEmpty then emptyGroupTok else sep sepTok named
      let w ← relWidth r.input
      let out ← refOutput w r.common
      wrapChild relLines ctx indent r.input (indent ++ kwFetch ++ argsText ++ out ++ "]")
  | .join r => do
      let jt ← joinTypeName r.joinType
      let c ← expr ctx r.condition
      let l ← relWidth r.left; let rw ← relWidth r.right
      let total := r.joinType.width l rw
      let out ← outputClause true ((List.range total).map .ref) (emitOf r.common)
      let childL ← relLines ctx (indent ++ indentUnit) r.left
      let childR ← relLines ctx (indent ++ indentUnit) r.right
      pure ([indent ++ kwJoin ++ ampTok ++ jt ++ sepTok ++ c ++ out ++ "]"] ++ childL ++ childR)
  | .set r => do
      let w ← relWidth (.set r)
      let out ← outputClause true ((List.range w).map .ref) (emitOf r.common)
      let op ← setOpName r.op
      let children ← r.inputs.mapM (fun rl => relLines ctx (indent ++ indentUnit) rl)
      pure ([indent ++ kwSet ++ ampTok ++ op ++ out ++ "]"] ++ children.flatten)
  | .cross r => do
      let l ← relWidth r.left; let rw ← relWidth r.right
      let childL ← relLines ctx (indent ++ indentUnit) r.left
      let childR ← relLines ctx (indent ++ indentUnit) r.right
      let cols := (List.range (l + rw)).map .ref
      pure ([indent ++ kwCross ++ directCols cols ++ "]"] ++ childL ++ childR)
  | .write _          => throw "WriteRel is not part of the substrait-explain grammar — refusing to emit"
  | .extensionLeaf _  => throw "ExtensionLeafRel is not part of the substrait-explain grammar — refusing to emit"
  | .extensionSingle _=> throw "ExtensionSingleRel is not part of the substrait-explain grammar — refusing to emit"
  | .extensionMulti _ => throw "ExtensionMultiRel is not part of the substrait-explain grammar — refusing to emit"

/-! ## Extension section -/

/-- The anchor of an extension declaration. -/
def declAnchor : Proto.ExtensionDeclaration → Nat
  | .function _ an _ => an | .extType _ an _ => an | .typeVariation _ an _ => an

/-- The URN reference of an extension declaration. -/
def declUrnRef : Proto.ExtensionDeclaration → Nat
  | .function u _ _ => u | .extType u _ _ => u | .typeVariation u _ _ => u

/-- The name of an extension declaration. -/
def declName : Proto.ExtensionDeclaration → String
  | .function _ _ n => n | .extType _ _ n => n | .typeVariation _ _ n => n

/-- Stable insertion into a sorted list. -/
def insertDecl (lt : Proto.ExtensionDeclaration → Proto.ExtensionDeclaration → Bool)
    (x : Proto.ExtensionDeclaration) : List Proto.ExtensionDeclaration → List Proto.ExtensionDeclaration
  | [] => [x]
  | y :: ys => if lt y x then y :: insertDecl lt x ys else x :: y :: ys

/-- Extensions sorted by (anchor, kind), matching textify's BTreeMap order. -/
def sortedDeclarations (p : Proto.Plan) : List Proto.ExtensionDeclaration :=
  let lt (a b : Proto.ExtensionDeclaration) : Bool :=
    let sa := (declAnchor a, (ExtKind.ofDecl a).num)
    let sb := (declAnchor b, (ExtKind.ofDecl b).num)
    sa.1 < sb.1 || (sa.1 == sb.1 && sa.2 < sb.2)
  p.extensions.foldl (fun acc x => insertDecl lt x acc) []

/-- One URN entry line (`  @{anchor:3}: {urn}`) — the emitter half of the
    row shape `Decode.parseUrnEntry` inverts
    (`Decode.parseUrnEntry_urnLine`). -/
def urnLine (a : Nat) (urn : String) : String :=
  urnEntryPfx ++ rightJustify 3 a ++ colonSpTok ++ urn

/-- One declaration entry line (`  #{anchor:3} @{urnRef:3}: {name}`) — the
    emitter half of the row shape `Decode.parseDeclEntry` inverts
    (`Decode.parseDeclEntry_declLine`). The `" @"` separator's decoder half
    is a char-level space-skip + `'@'` pattern (a resistant site — noted). -/
def declLine (urnRef anchor : Nat) (nm : String) : String :=
  declEntryPfx ++ rightJustify 3 anchor ++ " @" ++ rightJustify 3 urnRef ++ colonSpTok ++ nm

/-- Render a kind's section (header + entries), or nothing when empty. The
    header comes from the shared `Grammar.extKindGrammar` table — the SAME
    rows the decoder's block loop looks up. -/
def kindSection (k : ExtKind) (list : List Proto.ExtensionDeclaration) : List String :=
  if list.isEmpty then []
  else k.header :: (list.map fun d => declLine (declUrnRef d) (declAnchor d) (declName d))

/-- The `=== Extensions` lines of a plan (nothing when the plan declares nothing). -/
def extensionsLines (p : Proto.Plan) : List String :=
  if p.extensionUrns.isEmpty && p.extensions.isEmpty then []
  else
    let urnBlock : List String :=
      if p.extensionUrns.isEmpty then []
      else urnsHeader :: (p.extensionUrns.map fun u => urnLine u.extensionUrnAnchor u.urn)
    let decls := sortedDeclarations p
    let fnS := kindSection .function (decls.filter (fun d => ExtKind.ofDecl d == .function))
    let tyS := kindSection .extType (decls.filter (fun d => ExtKind.ofDecl d == .extType))
    let tvS := kindSection .typeVariation (decls.filter (fun d => ExtKind.ofDecl d == .typeVariation))
    [sectionExtensions] ++ urnBlock ++ fnS ++ tyS ++ tvS

/-! ## Version + relations + driver -/

/-- The `=== Version` lines (only when the version is present and non-empty).
    The line shapes are the `Grammar.versionPfx`/`dotTok`/`producerPfx`/
    `gitHashPfx` tokens — `Decode.parseVersion_versionLines` inverts them. -/
def versionLines (v : Proto.Version) : List String :=
  let header := versionPfx ++ toString v.majorNumber ++ dotTok ++ toString v.minorNumber ++ dotTok ++ toString v.patchNumber
  let producer := if v.producer.isEmpty then [] else [producerPfx ++ v.producer]
  let git := if v.gitHash.isEmpty then [] else [gitHashPfx ++ v.gitHash]
  header :: (producer ++ git)

/-- Render all plan rels; one blank line separates consecutive rels. -/
def relationsLines (ctx : Ctx) : List Proto.PlanRel → Except String (List String)
  | [] => pure []
  | r :: rest => do
      let cur ← match r with
        | .rel rel => relLines ctx "" rel
        | .root names input => do
            let namesTxt := sep sepTok (names.map name)
            let inp ← relLines ctx indentUnit input
            pure ([kwRoot ++ namesTxt ++ "]"] ++ inp)
      let tail ← relationsLines ctx rest
      pure (cur ++ (if rest.isEmpty then [] else [""]) ++ tail)

/--
The full canonical text of a plan.  Hard-fails on rel shapes the grammar
cannot represent, and never emits Unspecified nullability.
-/
def emit (plan : Proto.Plan) : Except String String := do
  let ctx := Ctx.ofPlan plan
  let mut lines : List String := []
  if let some v := plan.version then
    if !v.isEmpty then lines := lines ++ versionLines v
  let ext := extensionsLines plan
  if !ext.isEmpty then
    lines := lines ++ ext
    lines := lines ++ [""]
  lines := lines ++ [sectionPlan]
  let rels ← relationsLines ctx plan.relations
  lines := lines ++ rels
  pure (sep "\n" lines ++ "\n")
