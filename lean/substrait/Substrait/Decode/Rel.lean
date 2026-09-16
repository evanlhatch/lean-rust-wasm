/-
# Substrait.Decode.Rel — the relation line-tree parsers

W5.3 phase 1: split of the monolithic Decode.lean along its section
structure (pure code-motion; statements unchanged).
W5.3 phase 2a: `joinTypeOfName`/`setOpOfName`/`sortDirOfName` are exact-match
lookups over the shared `Substrait.Grammar` name tables (the hand tables
died); the per-family `parse (emit x) = some x` round trips are at the
bottom.
-/
import Substrait.Decode.Expr

namespace Substrait.Decode

-- ── relations (the line tree) ───────────────────────────────────────────────

/-- Decode-side output width (total; mirrors the emitter's `relWidth`). -/
def relWidthD : Nat → Proto.Rel → Nat
  | 0, _ => 0
  | _ + 1, .read r => (r.baseSchema.map (·.fields.length)).getD 0
  | fuel + 1, .filter r => relWidthD fuel r.input
  | fuel + 1, .project r => relWidthD fuel r.input + r.expressions.length
  | _, .aggregate r => r.groupingExpressions.length + r.measures.length
  | fuel + 1, .sort r => relWidthD fuel r.input
  | fuel + 1, .fetch r => relWidthD fuel r.input
  | fuel + 1, .join r => r.joinType.width (relWidthD fuel r.left) (relWidthD fuel r.right)
  | fuel + 1, .cross r => relWidthD fuel r.left + relWidthD fuel r.right
  | fuel + 1, .set r => (r.inputs.head?).map (relWidthD fuel) |>.getD 0
  | _, .write _ | _, .extensionLeaf _ | _, .extensionSingle _ | _, .extensionMulti _ => 0

/-- The leading whitespace count of a line. -/
def indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length

/-- Split a line's tail into top-level `, `-separated items (depth-tracked
    over `()<>`; v0 limitation: a quoted name containing ", " inside an
    output column splits wrongly — the corpus has none). -/
def splitTopLevel : List Char → Nat → List Char → List (List Char)
  | [], _, cur => [cur.reverse]
  | ',' :: ' ' :: rest, 0, cur => cur.reverse :: splitTopLevel rest 0 []
  | c :: rest, d, cur =>
    let d' := if c == '(' || c == '<' || c == '[' then d + 1
              else if c == ')' || c == '>' || c == ']' then d - 1
              else d
    splitTopLevel rest d' (c :: cur)

/-- Split on the FIRST top-level ` |> ` (Read's explicit mapping). -/
def splitOnPipe : List Char → List Char → Option (List Char × List Char)
  | _, [] => none
  | acc, ' ' :: '|' :: '>' :: ' ' :: rest => some (acc.reverse, rest)
  | acc, c :: rest => splitOnPipe (c :: acc) rest

/-- A whole-item field ref `$n` (nothing else). -/
def parseRefItem : List Char → Option Nat
  | '$' :: rest => match scanNat rest with
    | some (n, []) => some n
    | _ => none
  | _ => none

/-- Join-type name → constructor: the decoder half of
    `Substrait.Grammar.joinGrammar` (exact-match lookup; row names distinct
    by `joinGrammar_name_nodup`). -/
def joinTypeOfName (s : String) : Option Proto.JoinType :=
  (Grammar.JoinCtor.ofName s).map Grammar.JoinCtor.toJoinType

/-- Set-op name → constructor: the decoder half of
    `Substrait.Grammar.setGrammar`. -/
def setOpOfName (s : String) : Option Proto.SetOp :=
  (Grammar.SetCtor.ofName s).map Grammar.SetCtor.toSetOp

/-- Sort-direction name → constructor: the decoder half of
    `Substrait.Grammar.sortDirGrammar`. -/
def sortDirOfName (s : String) : Option Proto.SortDirection :=
  (Grammar.SortDirCtor.ofName s).map Grammar.SortDirCtor.toSortDirection

/-- The output-clause tail: refs-only items become the emit mapping
    (identity canonicalizes to `none` — the text does not distinguish
    `.direct` from no-emit; documented lossiness); typed/expression columns
    are redundant with the rel's own structure and yield `none`. -/
def outputMappingOf (width : Nat) (items : List (List Char)) : Option (List Nat) :=
  let refs := items.map parseRefItem
  if refs.any (· == none) then none
  else
    let m := refs.filterMap id
    if m == List.range width then none else some m

/-- The common record for a parsed mapping. -/
def commonOfMapping : Option (List Nat) → Option Proto.RelCommon
  | none => none
  | some m => some { emit := some (.emit m), advancedExtension := none }

/-- A `name:type` column (Read's output fields). -/
def parseNamedCol (cs : List Char) : Option (String × Proto.PType × List Char) :=
  match scanName cs with
  | some (nm, r1) =>
    match expect ":" r1 with
    | some r2 => (parseType (r2.length + 1) r2).map (fun (t, r3) => (nm, t, r3))
    | none => none
  | none => none

/-- A sort field `($n, &Dir)`, consuming and returning the rest. -/
def parseSortField : List Char → Option (Proto.SortField × List Char)
  | '(' :: '$' :: rest =>
    match scanNat rest with
    | some (n, r1) =>
      match expect ", &" r1 with
      | some r2 =>
        match scanIdent r2 with
        | some (dn, r3) =>
          match expect ")" r3 with
          | some r4 =>
            (sortDirOfName dn).map fun d =>
              ({ expr := .field { ordinal := n, segment := none }, direction := d }, r4)
          | none => none
        | none => none
      | none => none
    | none => none
  | _ => none

/-- The parsed header of one rel line: a constructor waiting for children
    (continuations may fail — the line is rejected). -/
inductive HeaderShape where
  | done (r : Proto.Rel)
  | one (mk : Proto.Rel → Option Proto.Rel)
  | two (mk : Proto.Rel → Proto.Rel → Option Proto.Rel)
  | many (mk : List Proto.Rel → Option Proto.Rel)

/-- Parse Read's named-column list into the base schema (`_` = none). -/
def parseReadCols (cs : List Char) : Option (Option Proto.NamedStruct) :=
  if cs == ['_'] then some none
  else
    let items := splitTopLevel cs 0 []
    let cols := items.map parseNamedCol
    if cols.any (· == none) then none
    else
      let cs' := cols.filterMap id
      some (some { fields := cs'.map (·.2.1), names := cs'.map (·.1) })

/-- The Read header: dotted table name, then ` => cols` or
    ` +> cols |> $mapping`. -/
def parseReadHeader (cs : List Char) : Option Proto.ReadRel :=
  match scanName cs with
  | some (tn, r1) =>
    let rec dots (acc : List String) : Nat → List Char → Option (List String × List Char)
      | 0, _ => none
      | dfuel + 1, '.' :: rest => match scanName rest with
        | some (n2, r2) => dots (acc ++ [n2]) dfuel r2
        | none => none
      | _, rr => some (acc, rr)
    match dots [tn] (r1.length + 1) r1 with
    | some (names, r2) =>
      match expect " => " r2 with
      | some r3 =>
        (parseReadCols r3).map fun baseSchema =>
          { readType := .namedTable names, baseSchema, common := none }
      | none =>
        match expect " +> " r2 with
        | some r3 =>
          match splitOnPipe [] r3 with
          | some (colText, mapText) =>
            match parseReadCols colText with
            | some baseSchema =>
              let mitems := splitTopLevel mapText 0 []
              let rs := mitems.map parseRefItem
              if rs.any (· == none) then none
              else some { readType := .namedTable names, baseSchema
                        , common := some { emit := some (.emit (rs.filterMap id))
                                         , advancedExtension := none } }
            | none => none
          | none =>
            (parseReadCols r3).map fun baseSchema =>
              { readType := .namedTable names, baseSchema, common := none }
        | none => none
    | none => none
  | none => none

/-- The Aggregate header: `groups => cols`; `_` is the empty group. The
    output cols repeat the group exprs then the measures (`name(...):ty`).
    A refs-only output clause is an emit mapping — v0 rejects it (not in
    the corpus; the width is not knowable before the measures). -/
def parseAggregateHeader (ctx : FnCtx) (cs : List Char) : Option HeaderShape := do
  let rec groups (lfuel : Nat) (acc : List Proto.Expression) (cc : List Char) :
      Option (List Proto.Expression × List Char) :=
    match lfuel with
    | 0 => none
    | lf + 1 =>
      if startsWith cc "_ => " then some (acc.reverse, cc.drop 5)
      else match parseExpr (cc.length + 1) ctx cc with
        | some (e, r1) =>
          match expect ", " r1 with
          | some r2 => groups lf (e :: acc) r2
          | none =>
            match expect " => " r1 with
            | some r2 => some ((e :: acc).reverse, r2)
            | none => none
        | none => none
  let (gs, r2) ← groups (cs.length + 1) [] cs
  let items := splitTopLevel r2 0 []
  some (.one fun child =>
    let g := gs.length
    let colExprs := items.map (parseExpr (cs.length + 1) ctx · |>.map (·.1))
    if colExprs.any (· == none) then none  -- the refs-only gap (documented)
    else
      let all := colExprs.filterMap id
      let rec toMeasures : List Proto.Expression → Option (List Proto.AggregateMeasure)
        | [] => some []
        | .scalarFunction fr args outTy :: rest =>
          (toMeasures rest).map (fun ms =>
            { measure := { functionReference := fr, args := args, outputType := outTy } } :: ms)
        | _ => none
      match toMeasures (all.drop g) with
      | some mss =>
        some (.aggregate { groupingExpressions := gs, measures := mss
                         , input := child, common := none })
      | none => none)

/-- The Sort header: `($n, &Dir), … => cols`. -/
def parseSortHeader (_ctx : FnCtx) (cs : List Char) : Option HeaderShape := do
  let rec sorts (lfuel : Nat) (acc : List Proto.SortField) (cc : List Char) :
      Option (List Proto.SortField × List Char) :=
    match lfuel with
    | 0 => none
    | lf + 1 =>
      match parseSortField cc with
      | some (sf, r1) =>
        match expect ", " r1 with
        | some r2 => sorts lf (sf :: acc) r2
        | none =>
          match expect " => " r1 with
          | some r2 => some ((sf :: acc).reverse, r2)
          | none => none
      | none => none
  let (sfs, r2) ← sorts (cs.length + 1) [] cs
  let items := splitTopLevel r2 0 []
  some (.one fun child =>
    some (.sort { sorts := sfs, input := child
                , common := commonOfMapping (outputMappingOf (relWidthD (cs.length + 1) child) items) }))

/-- The Fetch header: `limit=N, offset=M => cols` or `_ => cols`. -/
def parseFetchHeader (cs : List Char) : Option HeaderShape := do
  let named (cc : List Char) : Option (String × Nat × List Char) :=
    match scanIdent cc with
    | some (nm, r1) =>
      match expect "=" r1 with
      | some r2 => (scanNat r2).map (fun (n, r3) => (nm, n, r3))
      | none => none
    | none => none
  let rec args (lfuel : Nat) (acc : List (String × Nat)) (cc : List Char) :
      Option (List (String × Nat) × List Char) :=
    match lfuel with
    | 0 => none
    | lf + 1 =>
      match named cc with
      | some (nm, n, r1) =>
        match expect ", " r1 with
        | some r2 => args lf ((nm, n) :: acc) r2
        | none => match expect " => " r1 with
          | some r2 => some (((nm, n) :: acc).reverse, r2)
          | none => none
      | none => none
  if startsWith cs "_ => " then
    let items := splitTopLevel (cs.drop 5) 0 []
    some (.one fun child =>
      some (.fetch { limit := none, offset := none, input := child
                   , common := commonOfMapping (outputMappingOf (relWidthD (cs.length + 1) child) items) }))
  else
    let (nameds, r2) ← args (cs.length + 1) [] cs
    let items := splitTopLevel r2 0 []
    let lim := nameds.lookup "limit"
    let off := nameds.lookup "offset"
    some (.one fun child =>
      some (.fetch { limit := lim, offset := off, input := child
                   , common := commonOfMapping (outputMappingOf (relWidthD (cs.length + 1) child) items) }))

/-- Parse one rel line's header (content after the indent). -/
def parseHeader (ctx : FnCtx) (cs : List Char) : Option HeaderShape :=
  if startsWith cs "Read[" then
    (parseReadHeader (cs.drop 5)).map (.done ∘ .read)
  else if startsWith cs "Filter[" then
    match parseExpr (cs.length + 1) ctx (cs.drop 7) with
    | some (cond, r1) =>
      match expect " => " r1 with
      | some r2 =>
        let items := splitTopLevel r2 0 []
        some (.one fun child =>
          some (.filter { condition := cond, input := child
                        , common := commonOfMapping (outputMappingOf (relWidthD (cs.length + 1) child) items) }))
      | none => none
    | none => none
  else if startsWith cs "Project[" then
    let items := splitTopLevel (cs.drop 8) 0 []
    some (.one fun child =>
      let w := relWidthD (cs.length + 1) child
      let parsed := items.map (parseExpr (cs.length + 1) ctx · |>.map (·.1))
      if parsed.any (· == none) then none
      else
        let es : List Proto.Expression := parsed.filterMap id
        let prefixOk := (List.range w).all fun i =>
          match es[i]? with
          | some (.field ref) => ref.ordinal == i && ref.segment == none
          | _ => false
        if !prefixOk || es.length < w then none  -- explicit-emit Project: the v0 gap
        else some (.project { expressions := es.drop w, input := child, common := none }))
  else if startsWith cs "Aggregate[" then
    parseAggregateHeader ctx (cs.drop 9)
  else if startsWith cs "Sort[" then
    parseSortHeader ctx (cs.drop 5)
  else if startsWith cs "Fetch[" then
    parseFetchHeader (cs.drop 6)
  else if startsWith cs "Join[" then
    match expect "&" (cs.drop 5) with
    | some r0 =>
      match scanIdent r0 with
      | some (jn, r1) =>
        match joinTypeOfName jn with
        | some jt =>
          match expect ", " r1 with
          | some r2 =>
            match parseExpr (cs.length + 1) ctx r2 with
            | some (cond, r3) =>
              match expect " => " r3 with
              | some r4 =>
                let items := splitTopLevel r4 0 []
                some (.two fun l r =>
                    let w := jt.width (relWidthD (cs.length + 1) l)
                      (relWidthD (cs.length + 1) r)
                    let cm := commonOfMapping (outputMappingOf w items)
                    some (.join { joinType := jt, left := l, right := r, condition := cond, postJoinFilter := none, common := cm }))
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  else if startsWith cs "Set[" then
    match expect "&" (cs.drop 4) with
    | some r0 =>
      match scanIdent r0 with
      | some (sn, r1) =>
        match setOpOfName sn with
        | some op =>
          match expect " => " r1 with
          | some r2 =>
            let items := splitTopLevel r2 0 []
            some (.many fun cs' =>
              match cs' with
              | [] => none
              | x :: _ =>
                let cm := commonOfMapping (outputMappingOf (relWidthD (cs.length + 1) x) items)
                some (.set { op := op, inputs := cs', common := cm }))
          | none => none
        | none => none
      | none => none
    | none => none
  else if startsWith cs "Cross[" then
    let items := splitTopLevel (cs.drop 6) 0 []
    if items.map parseRefItem |>.any (· == none) then none
    else some (.two fun l r => some (.cross { left := l, right := r, common := none }))
  else none

mutual

/-- Parse as many children at the given indent as present. -/
def parseChildren (ctx : FnCtx) : Nat → Nat → List String → Option (List Proto.Rel × List String)
  | 0, _, rest => some ([], rest)
  | fuel + 1, ind, rest =>
    match rest with
    | [] => some ([], [])
    | l :: _ =>
      if indentOf l == ind then
        match parseRelTree ctx fuel ind rest with
        | some (c, rest') =>
          (parseChildren ctx fuel ind rest').map fun (cs, r2) => (c :: cs, r2)
        | none => none
      else some ([], rest)

/-- Parse one rel node and its subtree. `fuel` bounds tree depth. -/
def parseRelTree (ctx : FnCtx) : Nat → Nat → List String → Option (Proto.Rel × List String)
  | 0, _, _ => none
  | _, _, [] => none
  | fuel + 1, ind, l :: rest =>
    if indentOf l == ind then
      match parseHeader ctx (l.toList.drop ind) with
      | some (.done r) => some (r, rest)
      | some (.one mk) =>
        match parseRelTree ctx fuel (ind + 2) rest with
        | some (c, rest') => (mk c).map (·, rest')
        | none => none
      | some (.two mk) =>
        match parseRelTree ctx fuel (ind + 2) rest with
        | some (c1, r1) =>
          match parseRelTree ctx fuel (ind + 2) r1 with
          | some (c2, r2) => (mk c1 c2).map (·, r2)
          | none => none
        | none => none
      | some (.many mk) =>
        match parseChildren ctx fuel (ind + 2) rest with
        | some (cs', rest') => (mk cs').map (·, rest')
        | none => none
      | none => none
    else none

end

-- ── the name-family round trips (W5.3 phase 2a) ────────────────────────────

/-- **Join-name round trip** (`parse (emit x) = some x`): emitter and
    decoder read ONE table (`Grammar.joinGrammar`), so this is a table
    lookup composed with its inverse — the per-family lemma is mechanical. -/
theorem joinTypeOfName_joinTypeName (j : Proto.JoinType) (s : String)
    (h : Emit.Text.joinTypeName j = .ok s) : joinTypeOfName s = some j := by
  unfold Emit.Text.joinTypeName at h
  cases hj : Grammar.JoinCtor.ofJoinType j with
  | none =>
    rw [hj] at h
    have h' : (Except.error "cannot emit Unspecified join type in the text format"
        : Except String String) = .ok s := h
    cases h'
  | some c =>
    rw [hj] at h
    have hs : s = c.name := (Except.ok.inj h).symm
    subst hs
    show (Grammar.JoinCtor.ofName c.name).map Grammar.JoinCtor.toJoinType = some j
    rw [Grammar.JoinCtor.ofName_self]
    exact congrArg some (Grammar.JoinCtor.toJoinType_ofJoinType j c hj)

/-- **Set-op round trip** (`parse (emit x) = some x`) over
    `Grammar.setGrammar`. -/
theorem setOpOfName_setOpName (op : Proto.SetOp) (s : String)
    (h : Emit.Text.setOpName op = .ok s) : setOpOfName s = some op := by
  unfold Emit.Text.setOpName at h
  cases hj : Grammar.SetCtor.ofSetOp op with
  | none =>
    rw [hj] at h
    have h' : (Except.error "cannot emit Unspecified set op in the text format"
        : Except String String) = .ok s := h
    cases h'
  | some c =>
    rw [hj] at h
    have hs : s = c.name := (Except.ok.inj h).symm
    subst hs
    show (Grammar.SetCtor.ofName c.name).map Grammar.SetCtor.toSetOp = some op
    rw [Grammar.SetCtor.ofName_self]
    exact congrArg some (Grammar.SetCtor.toSetOp_ofSetOp op c hj)

/-- **Sort-direction round trip** (`parse (emit x) = some x`) over
    `Grammar.sortDirGrammar`. The emitter's Sort arm throws on
    `unspecified` before rendering, so the emit side is quantified over the
    non-unspecified ctors; the fallback token `"Unspecified"` never parses
    back (`Grammar.SortDirCtor.ofName_unspecified`). -/
theorem sortDirOfName_sortDirName (d : Proto.SortDirection) (hd : d ≠ .unspecified) :
    sortDirOfName (Emit.Text.sortDirName d) = some d := by
  cases hj : Grammar.SortDirCtor.ofSortDirection d with
  | none =>
    exact absurd (Grammar.SortDirCtor.eq_unspecified_of_ofSortDirection_none hj) hd
  | some c =>
    have hname : Emit.Text.sortDirName d = c.name := by
      unfold Emit.Text.sortDirName
      rw [hj]
    rw [hname]
    show (Grammar.SortDirCtor.ofName c.name).map Grammar.SortDirCtor.toSortDirection = some d
    rw [Grammar.SortDirCtor.ofName_self]
    exact congrArg some (Grammar.SortDirCtor.toSortDirection_of d c hj)



end Substrait.Decode
