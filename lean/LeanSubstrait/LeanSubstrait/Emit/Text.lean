/-
# LeanSubstrait.Emit.Text

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
import LeanSubstrait.Proto.Plan
import LeanSubstrait.Substrait.Grammar

namespace LeanSubstrait.Emit.Text

/-! ## Primitive formatting -/

/-- Repeat a string `n` times (core has no `String.replicate`). -/
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

/-- Join a list with a separator. -/
def sep (d : String) (xs : List String) : String := String.intercalate d xs

/-- `$n`. -/
def fieldRef (ord : Nat) : String := "$" ++ toString ord

/-! ## Types (mirrors textify/types.rs) -/

/-- Nullability suffix: `?` / `` — never `⁉`. -/
def nullSuffix : Proto.Nullability → Except String String
  | .nullable     => pure "?"
  | .required     => pure ""
  | .unspecified  => throw "cannot emit Unspecified nullability — the text emitter writes explicit nullability only"

/-- A parameter list `<a, b>` (empty → nothing). -/
def params (ps : List (Except String String)) : Except String String := do
  let vs ← ps.mapM id
  if vs.isEmpty then pure "" else pure ("<" ++ sep ", " vs ++ ">")

/-! Render loop of the type text: `typeTextBase` is the outer shape without the
outer nullability suffix (nested elements keep their own nullability, so
`list<i32?>` and `map<i8, string?>` render exactly); `typeText` appends the
outer `?`.  (`mutual` needed: bases recurse through full element texts.) -/
mutual
  /-- The *outer* shape of a `Proto.PType` — `bool i8 … binary`, `decimal<P,S>`,
  `list<T>`, `map<K,V>`, `struct<T,…>`.  User-defined types cannot be rendered
  without a registry (extensions-only); they hard-error here.  The scalar
  prefixes come from `Substrait.ScalarCtor.prefix` — the SAME table the
  decoder's `parseScalarType` folds, so emitter and parser cannot drift. -/
  def typeTextBase : Proto.PType → Except String String
    | .bool _         => pure (Substrait.ScalarCtor.prefix .bool)
    | .i8 _           => pure (Substrait.ScalarCtor.prefix .i8)
    | .i16 _          => pure (Substrait.ScalarCtor.prefix .i16)
    | .i32 _          => pure (Substrait.ScalarCtor.prefix .i32)
    | .i64 _          => pure (Substrait.ScalarCtor.prefix .i64)
    | .fp32 _         => pure (Substrait.ScalarCtor.prefix .fp32)
    | .fp64 _         => pure (Substrait.ScalarCtor.prefix .fp64)
    | .string _       => pure (Substrait.ScalarCtor.prefix .string)
    | .binary _       => pure (Substrait.ScalarCtor.prefix .binary)
    | .decimal p s _  => pure (Substrait.TCtor.prefix .decimal ++ toString p ++ "," ++ toString s ++ ">")
    | .list e _       => do let es ← typeText e; pure (Substrait.TCtor.prefix .list ++ es ++ ">")
    | .map k v _      => do
        let ks ← typeText k; let vs ← typeText v
        pure (Substrait.TCtor.prefix .map ++ ks ++ ", " ++ vs ++ ">")
    | .struct fs _    => do
        let f' ← fs.mapM (fun t => typeText t)
        pure (Substrait.TCtor.prefix .struct ++ sep ", " f' ++ ">")
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
theorem typeTextBase_scalar (c : Substrait.ScalarCtor) (n : Proto.Nullability) :
    typeTextBase (Substrait.ScalarCtor.toPType c n) = .ok (Substrait.ScalarCtor.prefix c) := by
  cases c <;> simp [typeTextBase, Substrait.ScalarCtor.toPType,
    Substrait.ScalarCtor.prefix, Except.ok]
  all_goals rfl

/-- A single `Proto.PParam`. -/
def param : Proto.PParam → Except String String
  | .boolean b   => pure (if b then "true" else "false")
  | .integer i   => pure (toString i)
  | .string s    => pure s
  | .enum e      => pure e
  | .dataType t  => typeText t
  | .null t      => do let ts ← typeText t; pure ("null" ++ ts)

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

/-- Build the context from a plan. -/
def ofPlan (p : Proto.Plan) : Ctx :=
  { urns := p.extensionUrns.map fun u => (u.extensionUrnAnchor, u.urn)
    extensions := p.extensions.map fun d =>
      match d with
      | .function u a n => (u, 0, a, n)
      | .extType u a n  => (u, 1, a, n)
      | .typeVariation u a n => (u, 2, a, n) }

/--
A function's rendered name (± `:sig`, ± `#anchor`): mirrors `NamedAnchor`
(unique names and unique base names are suppressed).
-/
def functionName (c : Ctx) (a : Nat) : Except String String :=
  match c.nameOf 0 a with
  | none => throw s!"function anchor {a} is not declared in this plan's extensions"
  | some fullName =>
      let base := (fullName.splitOn ":").headD fullName
      let all := c.namesOf 0
      let uniqueMatches := all.filter (fun n => n == fullName)
      let baseMatches := all.filter (fun n => (n.splitOn ":").headD n == base)
      let unique := uniqueMatches.length == 1
      let baseUnique := baseMatches.length == 1
      let showSignature := !baseUnique
      let needsAnchor := !unique || ((!fullName.contains ':') && !baseUnique)
      pure ((if showSignature then fullName else base) ++ (if needsAnchor then ("#" ++ toString a) else ""))

end Ctx

/-! ## Expressions (mirrors textify/expressions.rs) -/

/-- The literal type-suffix name. -/
def literalTypeName : Proto.LiteralType → String
  | .bool _   => "boolean" | .i8 _ => "i8" | .i16 _ => "i16"
  | .i32 _    => "i32" | .i64 _ => "i64" | .fp32 _ => "fp32"
  | .fp64 _   => "fp64" | .string _ => "string" | .binary _ => "binary"
  | .null _   => "null"

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
  | .binary _     => "{{binary}}"          -- show_literal_binaries=false default
  | .null _       => "null"

/-- Render a literal with its type suffix (mirrors `Literal::textify`). -/
def literal : Proto.Literal → Except String String
  | { literalType := .null t, nullable := _ } => do
      let ts ← typeText t
      pure ("null" ++ ":" ++ ts)
  | { literalType := lt, nullable := n } =>
      let suffix : String :=
        if n || !isDefaultForSyntax lt then
          ":" ++ literalTypeName lt ++ (if n then "?" else "")
        else ""
      pure (literalValue lt ++ suffix)

/-- The `:type` suffix of a function call's output type (mandatory in the grammar). -/
def typeSuffix (t : Proto.PType) : Except String String := do
  let ts ← typeText t
  pure (":" ++ ts)

/-- Render any expression. -/
-- v0: emitter; totality not required
partial def expr (ctx : Ctx) : Proto.Expression → Except String String
  | .literal lit   => literal lit
  | .field ref     => pure (fieldRef ref.ordinal)
  | .scalarFunction fr args out => do
      let na ← Ctx.functionName ctx fr
      let as' ← args.mapM (fun e => expr ctx e)
      let fs ← typeSuffix out
      pure (na ++ "(" ++ sep ", " as' ++ ")" ++ fs)
  | .ifThen ifs elseE => do
      let cs ← ifs.mapM (fun (ifc, thenc) => do
        let i ← expr ctx ifc; let t ← expr ctx thenc
        pure (i ++ " -> " ++ t))
      let e ← expr ctx elseE
      pure ("if_then(" ++ sep ", " cs ++ ", _ -> " ++ e ++ ")")
  | .cast input targetType fb => do
      let i ← expr ctx input
      let t ← typeText targetType
      let fbTxt := match fb with | .returnNull => "?" | .throwException => "!" | _ => ""
      pure ("(" ++ i ++ ")::" ++ fbTxt ++ t)
  | .subquery _ _  => throw "cannot emit subqueries in the text format"

/-- An aggregate measure renders like a scalar function. -/
def measure (ctx : Ctx) (m : Proto.AggregateFunction) : Except String String := do
  let na ← Ctx.functionName ctx m.functionReference
  let as' ← m.args.mapM (expr ctx)
  let fs ← typeSuffix m.outputType
  pure (na ++ "(" ++ sep ", " as' ++ ")" ++ fs)


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

/-- The column at index `i`, or an error (core has no `List.get?`). -/
def colAt (cols : List Col) (i : Nat) : Except String Col :=
  let rec go : List Col → Nat → Except String Col
    | [], _ => throw s!"column index {i} out of range (width {cols.length})"
    | c :: _, 0 => pure c
    | _ :: rest, k + 1 => go rest k
  go cols i

/-- Render a column. -/
def colText : Col → String
  | .ref ord        => fieldRef ord
  | .namedField n t => name n ++ ":" ++ t
  | .e txt          => txt

/-- Direct (pre-emit) output columns as text. -/
def directCols (cols : List Col) : String := sep ", " (cols.map colText)

/--
The emit/output clause of a rel (mirrors `Emitted::write_output_clause`).
`implicit` selects `=>` vs `+>` (Direct/Implicit relations use `=>`; Read's
explicit output uses `+>`).
-/
def outputClause (implicit : Bool) (cols : List Col) (emit : Option Proto.EmitKind) : Except String String :=
  let direct := directCols cols
  if implicit then
    match emit with
    | none            => pure ("=> " ++ direct)
    | some .direct    => pure ("=> " ++ direct)
    | some (.emit m)  => pure ("=> " ++ sep ", " (m.map fieldRef))
  else
    match emit with
    | none            => pure ("+> " ++ direct)
    | some .direct    => pure ("+> " ++ direct)
    | some (.emit m)  => pure ("+> " ++ direct ++ " |> " ++ sep ", " (m.map fieldRef))

/-- The output width of a join for a join type. -/
def joinWidth (jt : Proto.JoinType) (l rw : Nat) : Nat :=
  match jt with
  | .leftSemi | .leftAnti | .leftSingle => l
  | .rightSemi | .rightAnti | .rightSingle => rw
  | .leftMark => l + 1
  | .rightMark => rw + 1
  | _ => l + rw

/-- The empty group argument display: `_`. -/
def emptyGroup : String := "_"

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
      pure (joinWidth r.joinType l rw)
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

/-- Join type display names (`&Inner`, …). -/
def joinTypeName : Proto.JoinType → Except String String
  | .inner => pure "Inner" | .outer => pure "Outer" | .left => pure "Left" | .right => pure "Right"
  | .leftSemi => pure "LeftSemi" | .rightSemi => pure "RightSemi"
  | .leftAnti => pure "LeftAnti" | .rightAnti => pure "RightAnti"
  | .leftSingle => pure "LeftSingle" | .rightSingle => pure "RightSingle"
  | .leftMark => pure "LeftMark" | .rightMark => pure "RightMark"
  | .unspecified => throw "cannot emit Unspecified join type in the text format"

/-- Set op display names (`&UnionAll`, …). -/
def setOpName : Proto.SetOp → Except String String
  | .unionAll => pure "UnionAll" | .unionDistinct => pure "UnionDistinct"
  | .minusPrimary => pure "MinusPrimary" | .minusPrimaryAll => pure "MinusPrimaryAll"
  | .minusMultiset => pure "MinusMultiset"
  | .intersectionPrimary => pure "IntersectionPrimary"
  | .intersectionMultiset => pure "IntersectionMultiset"
  | .intersectionMultisetAll => pure "IntersectionMultisetAll"
  | .unspecified => throw "cannot emit Unspecified set op in the text format"

/-- Sort direction display name (no `&`; the caller adds it). -/
def sortDirName : Proto.SortDirection → String
  | .ascNullsFirst   => "AscNullsFirst"
  | .ascNullsLast    => "AscNullsLast"
  | .descNullsFirst  => "DescNullsFirst"
  | .descNullsLast   => "DescNullsLast"
  | .clustered       => "Clustered"
  | .unspecified     => "Unspecified"  -- the caller rejects Unspecified instead

/-- Render a relation (headers + children) as indented lines. -/
-- v0: emitter; totality not required
partial def relLines (ctx : Ctx) (indent : String) : Proto.Rel → Except String (List String)
  | .read r => do
      match r.readType with
      | .namedTable names =>
          let tableName := sep "." (names.map name)
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
          pure [indent ++ "Read[" ++ tableName ++ " " ++ out ++ "]"]
      | .virtualTable _ _ => throw "Read:Virtual is not yet supported by the typed emitter"
  | .filter r => do
      let c ← expr ctx r.condition
      let w ← relWidth r.input
      let out ← outputClause true ((List.range w).map .ref) (emitOf r.common)
      let child ← relLines ctx (indent ++ "  ") r.input
      pure ([indent ++ "Filter[" ++ c ++ " " ++ out ++ "]"] ++ child)
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
      let child ← relLines ctx (indent ++ "  ") r.input
      pure ([indent ++ "Project[" ++ directCols shown ++ "]"] ++ child)
  | .aggregate r => do
      let groupArgs : List String ←
        if r.groupingExpressions.isEmpty then pure [emptyGroup]
        else r.groupingExpressions.mapM (expr ctx)
      let ms ← r.measures.mapM (fun m => measure ctx m.measure)
      let gexprs : List String ← r.groupingExpressions.mapM (expr ctx)
      let cols : List Col := gexprs.map .e ++ ms.map .e
      let out ← outputClause true cols (emitOf r.common)
      let child ← relLines ctx (indent ++ "  ") r.input
      pure ([indent ++ "Aggregate[" ++ sep ", " groupArgs ++ " " ++ out ++ "]"] ++ child)
  | .sort r => do
      let sortArgs ← r.sorts.mapM (fun sf => do
        let rn ← match sf.expr with
          | .field f => pure (fieldRef f.ordinal)
          | _ => throw "SortField must be a field reference in the text grammar"
        match sf.direction with
        | .unspecified => throw "cannot emit Unspecified sort direction in the text format"
        | d => pure ("(" ++ rn ++ ", &" ++ sortDirName d ++ ")"))
      let w ← relWidth r.input
      let out ← outputClause true ((List.range w).map .ref) (emitOf r.common)
      let child ← relLines ctx (indent ++ "  ") r.input
      pure ([indent ++ "Sort[" ++ sep ", " sortArgs ++ " " ++ out ++ "]"] ++ child)
  | .fetch r => do
      let named : List String :=
        (r.limit.map (fun n => "limit=" ++ toString n)).toList ++
        (r.offset.map (fun n => "offset=" ++ toString n)).toList
      let argsText := if named.isEmpty then emptyGroup else sep ", " named
      let w ← relWidth r.input
      let out ← outputClause true ((List.range w).map .ref) (emitOf r.common)
      let child ← relLines ctx (indent ++ "  ") r.input
      pure ([indent ++ "Fetch[" ++ argsText ++ " " ++ out ++ "]"] ++ child)
  | .join r => do
      let jt ← joinTypeName r.joinType
      let c ← expr ctx r.condition
      let l ← relWidth r.left; let rw ← relWidth r.right
      let total := joinWidth r.joinType l rw
      let out ← outputClause true ((List.range total).map .ref) (emitOf r.common)
      let childL ← relLines ctx (indent ++ "  ") r.left
      let childR ← relLines ctx (indent ++ "  ") r.right
      pure ([indent ++ "Join[&" ++ jt ++ ", " ++ c ++ " " ++ out ++ "]"] ++ childL ++ childR)
  | .set r => do
      let w ← relWidth (.set r)
      let out ← outputClause true ((List.range w).map .ref) (emitOf r.common)
      let op ← setOpName r.op
      let children ← r.inputs.mapM (fun rl => relLines ctx (indent ++ "  ") rl)
      pure ([indent ++ "Set[&" ++ op ++ " " ++ out ++ "]"] ++ children.flatten)
  | .cross r => do
      let l ← relWidth r.left; let rw ← relWidth r.right
      let childL ← relLines ctx (indent ++ "  ") r.left
      let childR ← relLines ctx (indent ++ "  ") r.right
      let cols := (List.range (l + rw)).map .ref
      pure ([indent ++ "Cross[" ++ directCols cols ++ "]"] ++ childL ++ childR)
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

/-- The kind number (0 function, 1 type, 2 type variation). -/
def declKindNum : Proto.ExtensionDeclaration → Nat
  | .function _ _ _ => 0 | .extType _ _ _ => 1 | .typeVariation _ _ _ => 2

/-- Stable insertion into a sorted list. -/
def insertDecl (lt : Proto.ExtensionDeclaration → Proto.ExtensionDeclaration → Bool)
    (x : Proto.ExtensionDeclaration) : List Proto.ExtensionDeclaration → List Proto.ExtensionDeclaration
  | [] => [x]
  | y :: ys => if lt y x then y :: insertDecl lt x ys else x :: y :: ys

/-- Extensions sorted by (anchor, kind), matching textify's BTreeMap order. -/
def sortedDeclarations (p : Proto.Plan) : List Proto.ExtensionDeclaration :=
  let lt (a b : Proto.ExtensionDeclaration) : Bool :=
    let sa := (declAnchor a, declKindNum a)
    let sb := (declAnchor b, declKindNum b)
    sa.1 < sb.1 || (sa.1 == sb.1 && sa.2 < sb.2)
  p.extensions.foldl (fun acc x => insertDecl lt x acc) []

/-- Render a kind's section (header + entries), or nothing when empty. -/
def kindSection (header : String) (list : List Proto.ExtensionDeclaration) : List String :=
  if list.isEmpty then []
  else header :: (list.map fun d =>
    "  #" ++ rightJustify 3 (declAnchor d) ++ " @" ++ rightJustify 3 (declUrnRef d) ++ ": " ++ declName d)

/-- The `=== Extensions` lines of a plan (nothing when the plan declares nothing). -/
def extensionsLines (p : Proto.Plan) : List String :=
  if p.extensionUrns.isEmpty && p.extensions.isEmpty then []
  else
    let urnBlock : List String :=
      if p.extensionUrns.isEmpty then []
      else "URNs:" :: (p.extensionUrns.map fun u => "  @" ++ rightJustify 3 u.extensionUrnAnchor ++ ": " ++ u.urn)
    let decls := sortedDeclarations p
    let fnS := kindSection "Functions:" (decls.filter (fun d => declKindNum d == 0))
    let tyS := kindSection "Types:" (decls.filter (fun d => declKindNum d == 1))
    let tvS := kindSection "Type Variations:" (decls.filter (fun d => declKindNum d == 2))
    ["=== Extensions"] ++ urnBlock ++ fnS ++ tyS ++ tvS

/-! ## Version + relations + driver -/

/-- The `=== Version` lines (only when the version is present and non-empty). -/
def versionLines (v : Proto.Version) : List String :=
  let header := "=== Version " ++ toString v.majorNumber ++ "." ++ toString v.minorNumber ++ "." ++ toString v.patchNumber
  let producer := if v.producer.isEmpty then [] else ["  producer: " ++ v.producer]
  let git := if v.gitHash.isEmpty then [] else ["  git_hash: " ++ v.gitHash]
  header :: (producer ++ git)

/-- Render all plan rels; one blank line separates consecutive rels. -/
def relationsLines (ctx : Ctx) : List Proto.PlanRel → Except String (List String)
  | [] => pure []
  | r :: rest => do
      let cur ← match r with
        | .rel rel => relLines ctx "" rel
        | .root names input => do
            let namesTxt := sep ", " (names.map name)
            let inp ← relLines ctx "  " input
            pure (["Root[" ++ namesTxt ++ "]"] ++ inp)
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
  lines := lines ++ ["=== Plan"]
  let rels ← relationsLines ctx plan.relations
  lines := lines ++ rels
  pure (sep "\n" lines ++ "\n")
