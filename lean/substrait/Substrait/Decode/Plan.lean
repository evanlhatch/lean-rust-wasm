/-
# Substrait.Decode.Plan — the plan driver and the parser-layer inversion theorems

W5.3 phase 1: split of the monolithic Decode.lean along its section
structure (pure code-motion; statements unchanged).
-/
import Substrait.Decode.Rel

namespace Substrait.Decode

-- ── the plan driver ─────────────────────────────────────────────────────────

/-- `@  1: urn` — a URN entry (anchors right-justified to width 3). -/
def parseUrnEntry (cs : List Char) : Option Proto.SimpleExtensionUrn :=
  let cs := cs.dropWhile (· == ' ')
  match cs with
  | '@' :: rest =>
    let rest := rest.dropWhile (· == ' ')
    match scanNat rest with
    | some (a, r1) =>
      match expect ":" r1 with
      | some r2 => some { extensionUrnAnchor := a, urn := String.ofList (r2.drop 1) }
      | none => none
    | none => none
  | _ => none

/-- `#  1 @  1: name` — a declaration entry. -/
def parseDeclEntry (kind : Nat) (cs : List Char) : Option Proto.ExtensionDeclaration :=
  let cs := cs.dropWhile (· == ' ')
  match cs with
  | '#' :: rest =>
    let rest := rest.dropWhile (· == ' ')
    match scanNat rest with
    | some (anchor, r1) =>
      let r1 := r1.dropWhile (· == ' ')
      match r1 with
      | '@' :: r2 =>
        let r2 := r2.dropWhile (· == ' ')
        match scanNat r2 with
        | some (urnRef, r3) =>
          match expect ":" r3 with
          | some r4 =>
            let nm := String.ofList (r4.drop 1)
            match kind with
            | 0 => some (.function urnRef anchor nm)
            | 1 => some (.extType urnRef anchor nm)
            | _ => some (.typeVariation urnRef anchor nm)
          | none => none
        | none => none
      | _ => none
    | none => none
  | _ => none

/-- The extensions section: URN entries, then Functions/Types/Type
    Variations blocks. Returns the plan fields and the FnCtx. -/
def parseExtensions : List String → Option (List Proto.SimpleExtensionUrn × List Proto.ExtensionDeclaration × FnCtx × List String)
  | [] => none
  | "URNs:" :: rest =>
    let urns := rest.takeWhile (fun l => l.startsWith "  @")
    let urnVals := urns.map (parseUrnEntry ·.toList)
    if urnVals.any (· == none) then none
    else parseDeclBlocks [] [] (rest.length + 1) (rest.drop urns.length) |>.map fun (ds, rest') =>
      (urnVals.filterMap id, ds, fnCtxOf ds, rest')
  | rest => parseDeclBlocks [] [] (rest.length + 1) rest |>.map fun (ds, rest') =>
      ([], ds, fnCtxOf ds, rest')
where
  /-- The function declarations → (name, anchor) pairs — the FnCtx both
      sections build (one helper, used twice). -/
  fnCtxOf (ds : List Proto.ExtensionDeclaration) : FnCtx :=
    ds.filterMap fun d => match d with | .function _ a n => some (n, a) | _ => none
  /-- The block header → its declaration kind number (0 = functions, 1 =
      types, 2 = type variations) — one table instead of three arms. -/
  kindOf (l : String) : Option Nat :=
    if l == "Functions:" then some 0
    else if l == "Types:" then some 1
    else if l == "Type Variations:" then some 2
    else none
  parseDeclBlocks (acc : List Proto.ExtensionDeclaration) (curKind : List Proto.ExtensionDeclaration) :
      Nat → List String → Option (List Proto.ExtensionDeclaration × List String)
    | 0, _ => none
    | bfuel + 1, l :: rest =>
      match kindOf l with
      | none => some (acc, l :: rest)
      | some k =>
          let es := rest.takeWhile (fun l => l.startsWith "  #")
          let vs := es.map (parseDeclEntry k ·.toList)
          if vs.any (· == none) then none
          else parseDeclBlocks (acc ++ vs.filterMap id) curKind bfuel (rest.drop es.length)
    | _ + 1, [] => some (acc, [])

/-- The `=== Version X.Y.Z` header plus optional producer/git_hash lines. -/
def parseVersion : List String → Option (Proto.Version × List String)
  | l :: rest =>
    match expect "=== Version " l.toList with
    | some r1 =>
      match scanNat r1 with
      | some (mj, r2) => match expect "." r2 with
        | some r3 => match scanNat r3 with
          | some (mn, r4) => match expect "." r4 with
            | some r5 => match scanNat r5 with
              | some (pt, []) =>
                let producer := match rest with
                  | p :: _ =>
                    if p.startsWith "  producer: " then [p.drop 12] else []
                  | _ => []
                let afterP := if producer.isEmpty then rest else rest.drop 1
                let git := match afterP with
                  | g :: _ =>
                    if g.startsWith "  git_hash: " then [g.drop 12] else []
                  | _ => []
                let afterG := if git.isEmpty then afterP else afterP.drop 1
                some ({ majorNumber := mj, minorNumber := mn, patchNumber := pt
                      , producer := (producer.headD "").toString, gitHash := (git.headD "").toString }, afterG)
              | _ => none
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  | [] => none

/-- The `=== Plan` body: plan rels separated by blank lines. A `Root[…]`
    line takes an indented child. -/
def parsePlanRels (ctx : FnCtx) : Nat → List String → Option (List Proto.PlanRel)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, "" :: rest => parsePlanRels ctx fuel rest
  | fuel + 1, l :: rest =>
    if l.startsWith "Root[" then
      -- names between Root[ and ]
      let inner := (l.toList.drop 5).takeWhile (· ≠ ']')
      let names := (splitTopLevel inner 0 []).map fun item =>
        (scanName item).map (·.1)
      if names.any (· == none) then none
      else
        match parseRelTree ctx (rest.length + 1) 2 rest with
        | some (input, rest') =>
          (parsePlanRels ctx fuel rest').map
            (.root (names.filterMap id) input :: ·)
        | none => none
    else
      match parseRelTree ctx (rest.length + 1) 0 (l :: rest) with
      | some (r, rest') => (parsePlanRels ctx fuel rest').map (.rel r :: ·)
      | none => none

/-- **The decoder**: text → `Proto.Plan`. The inverse of `Emit.Text.emit`
    (for plans whose rels are all in the grammar; the lossy spots — explicit
    `.direct` vs absent emit kinds, `advancedExtension`, unsorted extension
    declarations — are documented in the module doc). -/
def parsePlan (text : String) : Option Proto.Plan := do
  let lines := text.splitOn "\n"
  let lines := match lines.getLast? with
    | some "" => lines.dropLast
    | _ => lines
  let (version, rest1) := match lines with
    | l :: _ =>
      if l.startsWith "=== Version" then
        match parseVersion lines with
        | some (v, r) => (some v, r)
        | none => (none, lines)
      else (none, lines)
    | [] => (none, [])
  match rest1 with
  | "=== Extensions" :: rest2 =>
    let (urns, decls, fctx, rest3) ← parseExtensions rest2
    let rest4 := match rest3 with | "" :: r => r | r => r
    match rest4 with
    | "=== Plan" :: rest5 =>
      let rels ← parsePlanRels fctx (rest5.length + 1) rest5
      some { version, extensionUrns := urns, extensions := decls, relations := rels }
    | _ => none
  | "=== Plan" :: rest2 =>
    let rels ← parsePlanRels [] (rest2.length + 1) rest2
    some { version, extensionUrns := [], extensions := [], relations := rels }
  | _ => none

/-! ## relations: the inversion theorems (the last parser layer) -/

/- The relation layer is multi-line; the emitter (`Emit.Text.relLines`) writes
   indented lines and the parser (`parseRelTree`/`parseChildren`) recovers the
   indentation tree.  These theorems invert that layer for the well-formed
   fragment: Read (named table with a non-empty schema of plain-typed
   columns), Filter (a field-ref condition), Project (field-ref expressions),
   all with `common = none` (the documented lossiness — explicit emit
   mappings print identically to none and are canonicalized away). -/

/-- A character that `splitTopLevel` passes through unchanged (not the `, `
    separator and not a depth-tracked bracket). -/
def plainChar (c : Char) : Prop :=
  c ≠ ',' ∧ c ≠ '(' ∧ c ≠ ')' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '[' ∧ c ≠ ']'

/-- A char list all of whose chars are plain. -/
def Plain (cs : List Char) : Prop := ∀ c ∈ cs, plainChar c

-- The seven `plainChar` guards (`,` `(` `)` `<` `>` `[` `]`) are used as the
-- raw conjunction projections `h.1`, `h.2.1`, … at the split sites below.

/-- A plain char has `c == '(' = false`, etc. (the depth tests fail). -/
private theorem plain_beq_open (c : Char) (h : plainChar c) :
    (c == '(' || c == '<' || c == '[') = false := by
  have h1 : (c == '(') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.1 (beq_iff_eq.mp j)
  have h2 : (c == '<') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.2.2.1 (beq_iff_eq.mp j)
  have h3 : (c == '[') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.2.2.2.2.1 (beq_iff_eq.mp j)
  rw [h1, h2, h3]
  rfl

/-- A plain char has `c == ')' = false`, etc. (the close tests fail). -/
private theorem plain_beq_close (c : Char) (h : plainChar c) :
    (c == ')' || c == '>' || c == ']') = false := by
  have h1 : (c == ')') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.2.1 (beq_iff_eq.mp j)
  have h2 : (c == '>') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.2.2.2.1 (beq_iff_eq.mp j)
  have h3 : (c == ']') = false := by
    apply Bool.eq_false_iff.mpr
    intro j
    exact h.2.2.2.2.2.2 (beq_iff_eq.mp j)
  rw [h1, h2, h3]
  rfl

/-- A plain prefix is accumulated into `cur` by `splitTopLevel` (no splits
    at depth 0, no depth changes). -/
theorem splitTopLevel_plain_prefix (x rest cur : List Char) (hplain : Plain x) :
    splitTopLevel (x ++ rest) 0 cur = splitTopLevel rest 0 (x.reverse ++ cur) := by
  induction x generalizing cur with
  | nil => simp
  | cons c cs ih =>
    have hp := hplain c (by simp)
    have hcs : Plain cs := by
      intro a ha
      exact hplain a (by simp [ha])
    rw [List.cons_append]
    rw [splitTopLevel.eq_3 0 cur c (cs ++ rest) (by
      intro rest' h0 hc hrest
      exact (hp.1 hc).elim)]
    rw [plain_beq_open c hp, plain_beq_close c hp]
    simp
    rw [ih (c :: cur) hcs]

/-- `splitTopLevel` on a lone `]` just accumulates it (the depth saturates
    at 0 for Nat subtraction). -/
theorem splitTopLevel_rbracket_cur (cur : List Char) :
    splitTopLevel [']'] 0 cur = [cur.reverse ++ [']']] := by
  rw [splitTopLevel.eq_3 0 cur ']' [] (by
    intro rest' h0 hc hrest
    cases hrest)]
  have hbr := show (']' == '(' || ']' == '<' || ']' == '[') = false by decide
  have hbc := show (']' == ')' || ']' == '>' || ']' == ']') = true by decide
  rw [hbr, hbc]
  simp
  rw [splitTopLevel.eq_1 0 (']' :: cur)]
  simp [List.reverse_cons]

/-- A single plain item followed by `]` stays one item (the `]` merges in). -/
theorem splitTopLevel_plain_rbracket (x : List Char) (hplain : Plain x) :
    splitTopLevel (x ++ [']']) 0 [] = [x ++ [']']] := by
  rw [splitTopLevel_plain_prefix x [']'] [] hplain]
  simp
  rw [splitTopLevel_rbracket_cur x.reverse]
  simp [List.reverse_reverse]

/-- A plain head followed by the `, ` separator splits off the head. -/
theorem splitTopLevel_comma_head (x rest : List Char) (hplain : Plain x) :
    splitTopLevel (x ++ ([',', ' '] ++ rest)) 0 [] = x :: splitTopLevel rest 0 [] := by
  rw [splitTopLevel_plain_prefix x ([',', ' '] ++ rest) [] hplain]
  change splitTopLevel (',' :: ' ' :: rest) 0 (x.reverse ++ []) = x :: splitTopLevel rest 0 []
  rw [splitTopLevel.eq_2 (x.reverse ++ []) rest]
  simp [List.reverse_reverse]

/-- `splitTopLevel` over the joined items: the head goes to the result, the
    last item absorbs the tail (`]`). -/
def splitAppend (xss : List (List Char)) (tail : List Char) : List (List Char) :=
  match xss with
  | [] => []
  | [x] => [x ++ tail]
  | x :: rest => x :: splitAppend rest tail

/-- The rendered `name:type` column text. -/
def colText (n b : String) : String := Emit.Text.name n ++ ":" ++ b

/-- **The named-column inversion**: `name:type` scans back to the name and
    the parsed type (the type text is consumed via the length-fuel
    inversion). -/
theorem parseNamedCol_emitted (n : String) (t : Proto.PType) (b : String)
    (rest : List Char) (hemit : Emit.Text.typeText t = .ok b)
    (hrest : rest.head? ≠ some '?') :
    parseNamedCol ((colText n b).toList ++ rest) = some (n, t, rest) := by
  unfold parseNamedCol colText
  rw [String.toList_append, String.toList_append]
  -- scanName ((name n).toList ++ ":".toList ++ b.toList ++ rest)
  have hsc' : scanName ((Emit.Text.name n).toList ++ (":".toList ++ (b.toList ++ rest))) =
      some (n, ":".toList ++ (b.toList ++ rest)) := by
    have hs := scanName_name n (":".toList ++ (b.toList ++ rest))
      (Or.inr ⟨':', b.toList ++ rest, rfl, by decide⟩)
    exact hs
  -- normalize the goal's left-nested append chain to the hsc' form
  have hassoc : (Emit.Text.name n).toList ++ ":".toList ++ b.toList ++ rest =
      (Emit.Text.name n).toList ++ (":".toList ++ (b.toList ++ rest)) := by
    simp [List.append_assoc]
  rw [hassoc]
  rw [hsc']
  -- the match over `some` reduces
  -- reduce the outer match (the scanName result is some), then the expect
  -- match, then the type inversion; the final map over some reduces by rfl
  dsimp only
  rw [expect_self ":" (b.toList ++ rest)]
  simp only []
  rw [parseType_len_invert t b rest hrest hemit]
  rfl

/-- The `, `-joined column text of a column list. -/
def colsText (cols : List (String × String)) : String :=
  Emit.Text.sep ", " (cols.map (fun x => colText x.1 x.2))

/-- Elementwise inversion of `splitAppend`: the i-th element of the result
    is the i-th input, extended by `tail` exactly at the last index. -/
theorem splitAppend_getElem? : ∀ (xss : List (List Char)) (tail : List Char)
    (i : Nat) (hi : i < xss.length),
    (splitAppend xss tail)[i]? = some (xss[i]'hi ++ if i = xss.length - 1 then tail else []) := by
  intro xss
  induction xss with
  | nil => intro tail i hi; simp at hi
  | cons x rest ih =>
      intro tail i hi
      cases rest with
      | nil =>
          have hi' : i < 1 := by simpa using hi
          have hi0 : i = 0 := by omega
          subst i
          simp [splitAppend]
      | cons y rest' =>
          cases i with
          | zero =>
              simp [splitAppend]
          | succ j =>
              have hj : j < (y :: rest').length := Nat.lt_of_succ_lt_succ hi
              have hiff :
                  (j + 1 = (x :: y :: rest').length - 1 ↔
                   j = (y :: rest').length - 1) := by
                have hlen : (x :: y :: rest').length = (y :: rest').length + 1 := by
                  simp [List.length_cons]
                have hgt0 : 0 < (y :: rest').length := by simp
                constructor
                · intro h; omega
                · intro h; omega
              have hc : (y :: rest')[j]'hj = (x :: y :: rest')[j+1]'hi := by
                rw [List.getElem_cons_succ]
              have hif : (if j = (y :: rest').length - 1 then tail else []) =
                  (if j + 1 = (x :: y :: rest').length - 1 then tail else []) := by
                by_cases hJ : j = (y :: rest').length - 1
                · have hpos : j + 1 = (x :: y :: rest').length - 1 := hiff.mpr hJ
                  simp [hJ]
                · have hnj : ¬ j + 1 = (x :: y :: rest').length - 1 := by
                    intro h
                    exact hJ (hiff.mp h)
                  simp
              simp only [splitAppend, List.getElem?_cons_succ]
              rw [ih tail j hj]
              rw [hc]
              rw [hif]

/-- The map over a column list, positioned: the i-th mapped element is the
    `colText` of the i-th `(name, b)` pair. -/
theorem colTexts_getElem (cols : List (String × String)) (i : Nat)
    (h : i < cols.length) (h' : i < (cols.map (fun x => (colText x.1 x.2).toList)).length) :
    (cols.map (fun x => (colText x.1 x.2).toList))[i]'h' =
      (colText (cols[i]'h).1 (cols[i]'h).2).toList := by
  simp [List.getElem_map]

/-- **The column-list inversion** (indexed restate): the `, `-joined column
    texts, `splitAppend`-ed with the trailing `]` of the header close, parse
    back to the per-column `(name, type, rest)` triples, where the rest is
    `[']']` exactly at the last index and `[]` elsewhere. – The original draft
    stated this by value equality (`rest = …`), which needs
    `DecidableEq Proto.PType` (mutual inductives don't derive it on this
    toolchain); the indexed formulation with `i = cols.length - 1` dodges it
    entirely. -/
theorem splitAppend_map_parseNamedCol
    (cols : List (String × String))
    (htype : ∀ x ∈ cols, ∃ t : Proto.PType, Emit.Text.typeText t = .ok x.2)
    (i : Nat) (hi : i < cols.length) :
    ((splitAppend (cols.map (fun x => (colText x.1 x.2).toList)) [']']).map parseNamedCol)[i]?
      = some (some ((cols[i]'hi).1,
          (htype (cols[i]'hi) (List.getElem_mem (l := cols) hi)).choose,
          if i = cols.length - 1 then [']'] else [])) := by
  let texts : List (List Char) := cols.map (fun x => (colText x.1 x.2).toList)
  have hlen : texts.length = cols.length := by simp [texts]
  have hlen' : texts.length - 1 = cols.length - 1 := by omega
  have hcond : (i = texts.length - 1 ↔ i = cols.length - 1) := by
    constructor
    · intro h; omega
    · intro h; omega
  have htext : texts[i]'(by simpa [hlen] using hi) =
      (colText (cols[i]'hi).1 (cols[i]'hi).2).toList := by
    simp [texts]
  by_cases hlast : i = cols.length - 1
  · let t : Proto.PType := (htype (cols[i]'hi) (List.getElem_mem (l := cols) hi)).choose
    have hemit : Emit.Text.typeText t = .ok (cols[i]'hi).2 :=
      (htype (cols[i]'hi) (List.getElem_mem (l := cols) hi)).choose_spec
    have hlteq : i = texts.length - 1 := hcond.2 hlast
    rw [List.getElem?_map]
    rw [splitAppend_getElem? texts [']'] i (by simpa [hlen] using hi)]
    simp only [Option.map_some]
    rw [if_pos hlteq]
    rw [htext]
    rw [parseNamedCol_emitted (cols[i]'hi).1 t (cols[i]'hi).2 [']'] hemit (by decide)]
    rw [if_pos hlast]
  · -- the not-last column: the rest is `[]`
    let t : Proto.PType := (htype (cols[i]'hi) (List.getElem_mem (l := cols) hi)).choose
    have hemit : Emit.Text.typeText t = .ok (cols[i]'hi).2 :=
      (htype (cols[i]'hi) (List.getElem_mem (l := cols) hi)).choose_spec
    have hnotlteq : ¬ i = texts.length - 1 := by
      intro h
      exact hlast (hcond.1 h)
    rw [List.getElem?_map]
    rw [splitAppend_getElem? texts [']'] i (by simpa [hlen] using hi)]
    simp only [Option.map_some]
    rw [if_neg hnotlteq]
    rw [htext]
    rw [parseNamedCol_emitted (cols[i]'hi).1 t (cols[i]'hi).2 [] hemit (by simp)]
    rw [if_neg hlast]

-- ── the typed layer: Proto.Expression → Typed.Expr ──────────────────────

/-!

The wire → typed direction: `Proto.Expression` (what the wire/text carries)
decoded back into the schema-indexed `Substrait.Typed.Expr` GADT — the
inverse of `Typed.Expr.toProto` / `Typed.Args.toProto`.

Deliberate exclusions (the typed grammar has no syntax for them):
- `ifThen` / `cast` / `subquery`: `Typed.Expr` has only `literal`, `field`,
  `call` — the composite proto forms decode to `none`.
- `.null` literal payloads: `LiteralValue` has no null constructor.
- `userDefined` output types: the wire carries an anchor; recovering the
  `(urn, name)` pair needs a type registry the decode context (functions
  only) does not have — `stOfPType` returns `none`.
- `segment != none` field refs: the text grammar has no segment rule and the
  typed layer never produces one.
- `deterministic` / `sessionDependent` sig metadata: `Expr.toProto` erases
  both; decode reconstructs `deterministic := true`, `sessionDependent :=
  false`.  The round-trip statements compare at the Proto level (re-lowering
  the decoded expression), where the erasure is invisible.

Anchors: the decode-side function context `FnInv` is `(anchor, urn, name)`
triples — `fnInvOf` inverts `ExtCtx`'s 1-based `indexOf1` anchoring.

-/


end Substrait.Decode
