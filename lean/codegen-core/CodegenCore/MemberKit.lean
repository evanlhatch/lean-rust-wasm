/-
# CodegenCore.MemberKit — `declare_member_class`: the indexed member-class family, generated

Further-concepts C1: the INDEXED MEMBER-CLASS pattern. The schema-lang
validator lane has three hand-written pairs of (elaboration-resolution
class + constructor-path inductive + head/tail instances) — `HasCol`/
`ColPath`, `HasCase`/`CaseTag`, `HasPayload`/`CasePath` — whose ONLY
differences are the index list kind, the element shape, and the type
slot's binding mode. This module is the ONE generation command those
three instantiations call (`SchemaLang.Validate`):

    declare_member_class HasCol (List Field) ColPath here there where
      index := (n : String) (t : Ty)
      head  := {name := n, ty := t}
      tail  := {f : Field}
      field := path

generates, in the caller's namespace (every generated decl carries the
`@[derived]` stamp — the generating-command convention):
  (a) the path inductive `ColPath n t : List Field → Type`, with the
      head rule `here : {cs} → ColPath n t (HEAD :: cs)` (the HEAD term
      binds the query name in the list-constructor pattern — the
      misspelled-member elaboration gate) and the tail rule `there`
      (the recursive step);
  (b) the two-parameter class `HasCol (index) (n) (t : outParam Ty)`
      with the caller-named field (`path : ColPath n t index`);
  (c) the `priority := 100` head instance (`hasColHead` — the
      same-name-shadows-to-first rule) and a default-priority tail
      instance (`hasColTail`).

The per-instantiation VARIANCE (the honest reports):

- `index := (i : Ty)*` names the QUERY binder AND, in param mode, the
  type slot binder. The slot binder's presence selects the two modes:
  - `param` mode (`index := (n : String) (t : Ty)`): the slot is the
    path's second parameter AND the class's `outParam` (HasCol,
    HasPayload);
  - `ctor` mode (`index := (n : String)` + `slot := (t : Option Ty)`):
    the slot is a fresh binder of the path's HEAD rule and the head
    instance only — the path has ONE parameter, the class TWO
    (HasCase).
- `head :=` / `tail :=` are the ELEMENT SHAPES, spelled in the
  caller's scope. The head term is a TEMPLATE over the index binder
  idents — it binds the query name and type inside the list-
  constructor pattern (HasCol writes `{name := n, ty := t}`, CaseTag
  `(n, t)`, CasePath `(n, some t)`). The tail binders name the
  non-head element's binder sequence: `{f : Field}` = the element
  itself; `{m : String} {u : Option Ty}` = the pair `(m, u)`.
- `miss :=` (HasPayload only) is the arm-typed accessor's 0-analog
  table — one (Ty literal | miss VALUE) pair per valueable type —
  generating one `priority := 100` head instance per entry with the
  head template's type slot substituted by the literal (a STRUCTURAL
  ident substitution on the caller's syntax, then reprint). `val :=`
  names the VALUE type of the class's miss field (`Value` in
  SchemaLang — the clause exists because CodegenCore cannot import
  SchemaLang).

What stays per-instantiation (this module's contract, deliberately):
`@[guest_std]` marks and the path-walk function bodies (`ColPath.get`)
consume data NOT generated here; the list kind is `List` with
`::`/`[]` (a custom list family would parameterize nil/cons); the
class field name is a parameter (`path`/`tag` — consumers project it:
`h.path`); binder spellings are `(i : ty)` / `{i : ty}` exactly
(paren and brace — strict `⦃i : ty⦄` is a deliberate exclusion; no
instantiation needs it).

Placement: codegen-core core-only, `import Lean` only — NO SchemaLang
name appears in this module; every SchemaLang-flavored ident in the
generated decls (Field, VariantCase, Ty, Value, Option) is caller-
scope-resolved when the generated source is elaborated in the caller's
file (the macro hygiene rule: idents that do not exist in the macro's
module stay unresolved until the generated syntax is elaborated at
the call site). Generation route: the EnumWire `elabGenerated`
string route, built from the caller's syntactically faithful
`reprint`s (verified: `reprint` is the source text; the interpolated-
string route is deliberately avoided — `{x}.field` continuations
corrupt it).

THE GRAMMAR'S CONTRACT (the parser mechanics, pinned by probes):
- Atoms are single tokens: a syntax-decl atom may not contain internal
  whitespace (`"index := "` is invalid — `index` and `:=` must be
  separate atoms). 
- A bare `term` slot chains applications (`(List Field) Path` parses
  as ONE term) — the IndexList is paren-wrapped in the grammar, so the
  caller's `(List Field)` binds exactly the parenthesized term.
- The `binder` slots ride a LOCAL `binder` syntax category (declared
  here — Lean core has none; checked: `grep -rn \"declare_syntax_cat
  binder\" src/lean/` in the v4.33.0 toolchain src returns nothing):
  present optional groups are `null`-kind nodes with nonempty args;
  absent optionals have zero args — the impl reads presence
  arithmetically, never by kind.
- The mode matrix: `param` vs `ctor` are exclusive; `miss :=` requires
  `val :=` AND param mode; `val :=` requires `miss :=`.

W8 resume note: the saved-pack build errors are FIXED here — (1) the
`"index := "`-style atoms split into single-token atoms (they failed
with "invalid atom"); (2) `binder` was not a category — declared + the
binder extraction is STRUCTURAL (kind + child indices), no typed
quotation; (3) `termLastIdent` is `partial` (the mutual recursion over
`toList` has no structural measure); (4) the impl reads the FIXED
26-child arity directly (no cursor walking, no do-less if branches);
(5) the generated class header binds the caller's OWN index ident
(`(n : …)`, not a renamed `name`) so the field type's reference
resolves.
-/

module

public import Lean
public import Lean.Elab.Command
public import CodegenCore.GenKit
import LintKit.PackageNamespace

-- the `binder` syntax category parks in Lean's namespace BY DESIGN
-- (syntax cats cannot live in a library namespace — the Validate
-- `vexpr` precedent)
set_option linter.guestlang.packageNamespace false -- because declare_syntax_cat parks the binder category in Lean's namespace by design (syntax cats cannot live in a library namespace)

@[expose] public section

open Lean Elab Command Parser

namespace CodegenCore.MemberKit

/-- The CALLER's two binder shapes — the category this module generates
    (`(i : ty)` explicit, `{i : ty}` implicit; strict braces are the
    deliberate exclusion). Registered as a category so the command's
    `binder` slots parse exactly these; their node kinds ARE the rule
    names, so the impl's binder extraction is structural. -/
declare_syntax_cat binder

syntax (name := memberBinderParen) "(" ident ":" term ")" : binder
syntax (name := memberBinderBrace) "{" ident ":" term "}" : binder

/-- The invocation grammar: the task signature's positional head
    (`Cl`, `(IndexList)`, `Path`, `HeadCtor`, `TailCtor`) plus the
    `where` block naming the variance (module header: the modes). The
    parser contract, pinned by probes: (1) every term slot is paren-
    WRAPPED — a bare `term` chains applications into the next slot
    (`{name := n, ty := t}` followed by any ident becomes an
    application — a struct instance is no exception); (2) the
    where-block KEYS are `member_`-PREFIXED atoms (`member_index`/
    `member_slot`/`member_head`/`member_tail`/`member_field`/
    `member_val`/`member_miss`). The prefix is the lexer-pollution
    contract (the `prefix`-trap lesson): an atom like `"index "`
    REGISTERS the word as a lexer token, so `index`/`field`/… would
    stop working as ordinary identifiers in EVERY module that imports
    this one; a `member_`-compound word has no such collision. An
    `ident`-key alternative was probed and rejected: with ident keys
    the optional sections are shape-ambiguous (`ident := binder`
    matches the following section) and the binder cat's paren rule
    throws a hard error on the wrapped head-parenthesis. Every other
    atom (`declare_member_class`, `where`, `:=`, `(`, `)`, `|`) is a
    pre-existing token — the only new reservations are the
    `member_`-compounds and the command's lead atom. -/
syntax (name := declareMemberClass)
  "declare_member_class " ident "(" term ")" ident ident ident " where "
  "member_index " ":=" binder (binder)?
  ("member_slot " ":=" binder)?
  "member_head " ":=" "(" term ")"
  "member_tail " ":=" binder (binder)?
  "member_field " ":=" ident
  ("member_val " ":=" "(" term ")")?
  ("member_miss " ":=" ("(" term "|" term ")")+)?
  : command

/-- The caller's syntax as source text (`reprint` — faithful for
    source-parsed syntax; the trailing newline the reprint carries is
    trimmed: whitespace inside generated decls is harmless anyway). -/
private meta def render (stx : Syntax) : CommandElabM String := do
  match stx.reprint with
  | some s => return s.trim
  | none => throwError "declare_member_class: internal: cannot reprint {stx}"

/-- Structural node access — the TOTAL route (`Syntax.asNode` never
    fails; atom/ident args read as the empty null node). -/
private meta def argCount (s : Syntax) : Nat := (s.asNode).getNumArgs

private meta def argAt (s : Syntax) (i : Nat) : Syntax := (s.asNode).getArg i

/-- A parsed (ident, type) binder — extracted STRUCTURALLY (the rule's
    fixed child shape `⟨(, ident, :, term, )⟩`), so the caller's
    spelling round-trips without brace/paren munging. (The old typed
    quotation `(binder| …)` cannot resolve — the parser-category
    quotation form is unavailable for locally declared cats in this
    env; kind + indices are the deterministic route.) -/
private meta def binderIdentType (b : Syntax) : CommandElabM (String × String) :=
  let k := b.getKind.eraseMacroScopes
  if k == `CodegenCore.MemberKit.memberBinderParen || k == `CodegenCore.MemberKit.memberBinderBrace then
    return ((argAt b 1).getId.toString, ← render (argAt b 3))
  else
    throwError "declare_member_class: a binder must be `(i : Ty)` or `\{i : Ty}` — got kind {k}, node \{b}"

/-- Lowercase the first character (`HasCol` → `hasCol` — the replaced
    shops' instance-name leaf; `Char.toLower` is the core case-fold). -/
private meta def lcFirst (s : String) : String :=
  if s.isEmpty then s else (s.get 0).toLower.toString ++ s.drop 1

/-- The last ident in a term — the miss table's Ty literal leaf (`.u64`
    → `u64`), the head-instance name suffix (`hasPayloadHead_u64`).
    PARTIAL: the recursion walks `getArgs.toList` (a kernel-opaque
    projection — no structural measure; a helper for elaboration, no
    kernel surface). -/
private meta partial def termLastIdent : Syntax → Name
  | s =>
      if s.isIdent then s.getId
      else
        let args := (s.asNode).getArgs
        if args.isEmpty then Name.anonymous
        else match args.toList with
             | [] => Name.anonymous
             | _ :: rest => termLastIdentOf rest
where
  termLastIdentOf : List Syntax → Name
    | [] => Name.anonymous
    | [x] => termLastIdent x
    | _ :: rest => termLastIdentOf rest

/-- The generated instance-leaf names: `HasCol`+`Head` → `hasColHead`. -/
private meta def instLeaf (cl : Syntax) (suffix : String) : String :=
  (lcFirst cl.getId.toString) ++ suffix

/-- Replace every ident `orig` in `s` with the syntax `to` — the miss
    head instance's slot substitution (`(n, some t)` → `(n, some .u64)`).
    STRUCTURAL (no string matching): the head template names its type
    slot by the index binder's id, so ident equality is the contract.
    (Reserved word learned: the binder must be named `orig`, not
    `from`.) -/
private meta partial def substIdent (orig : Name) (to : Syntax) : Syntax → Syntax
  | s =>
      if s.isIdent then
        if s.getId == orig then to else s
      else if s.getArgs.isEmpty then s
      else s.modifyArgs (Array.map (substIdent orig to))

/-- The tail element built from the tail binders (the element-shape
    contract): one binder = the element itself (`f`); two = the pair
    (`m, u`). -/
private meta def tailElemS (binders : List (String × String)) : String :=
  match binders with
  | [(x, _)] => x
  | [(x, _), (y, _)] => "(" ++ x ++ ", " ++ y ++ ")"
  | _ => ""

/-- The implicit-binder spine `{f : T} → {u : U} →` of the tail binders
    (the tail ctor's premise — the element binder sequence). -/
private meta def binderSpineS : List (String × String) → String
  | [] => ""
  | bs =>
      let spines := bs.map fun (i, ty) => "{" ++ i ++ " : " ++ ty ++ "}"
      String.intercalate " → " spines

/-- The generated constructor application `PATH.CTOR` (dotted raw names
    — resolved in the caller's namespace, the EnumWire `{n}.toTag`
    rule). -/
private meta def ctorName (path : Syntax) (ctor : Syntax) : String :=
  path.getId.toString ++ "." ++ ctor.getId.toString

/-- The generated declaration sources, in emission order (path, class,
    head instance(s), tail instance). Every SchemaLang ident is the
    caller's own spelling, only re-rendered; the substitution is done
    on the caller's SYNTAX before rendering. -/
private meta def genSrcs (cl : Syntax) (idx : String) (path : Syntax)
    (headCtor tailCtor : Syntax) (n : String × String)
    (tB? : Option (String × String)) (slotB? : Option (String × String))
    (headElemS : String)
    (tailBs : List (String × String)) (fld : String)
    (valTy? : Option String)
    (misses : List (String × String × String × String)) :
    List String :=
  let (nId, nTy) := n
  let col := path.getId.toString
  let hC := headCtor.getId.toString
  let tC := tailCtor.getId.toString
  let cls := cl.getId.toString
  let tailE := tailElemS tailBs
  let tailSpine := binderSpineS tailBs
  let headCtorApp := ctorName path headCtor
  let tailCtorApp := ctorName path tailCtor
  -- the path inductive
  let pathSrc : String :=
    match tB? with
    | some (tId, tTy) =>
      "inductive " ++ col ++ " (" ++ nId ++ " : " ++ nTy ++ ") (" ++ tId ++ " : " ++ tTy ++ ") : " ++ idx ++ " → Type where\n" ++
      "  | " ++ hC ++ " : {cs : " ++ idx ++ "} → " ++ col ++ " " ++ nId ++ " " ++ tId ++ " ((" ++ headElemS ++ ") :: cs)\n" ++
      "  | " ++ tC ++ " : " ++ tailSpine ++ " → {cs : " ++ idx ++ "} → " ++ col ++ " " ++ nId ++ " " ++ tId ++ " cs → " ++ col ++ " " ++ nId ++ " " ++ tId ++ " (" ++ tailE ++ " :: cs)"
    | none =>
      let (sId, sTy) := slotB?.get!
      "inductive " ++ col ++ " (" ++ nId ++ " : " ++ nTy ++ ") : " ++ idx ++ " → Type where\n" ++
      "  | " ++ hC ++ " : {" ++ sId ++ " : " ++ sTy ++ "} → {cs : " ++ idx ++ "} → " ++ col ++ " " ++ nId ++ " ((" ++ headElemS ++ ") :: cs)\n" ++
      "  | " ++ tC ++ " : " ++ tailSpine ++ " → {cs : " ++ idx ++ "} → " ++ col ++ " " ++ nId ++ " cs → " ++ col ++ " " ++ nId ++ " (" ++ tailE ++ " :: cs)"
  -- the class (the header binds the CALLER's index idents — the field
  -- type's references resolve against them)
  let missField : String :=
    match valTy?, tB? with
    | some valTy, some (tId, _) => "\n  miss : " ++ valTy ++ " " ++ tId
    | _, _ => ""
  let clsSrc : String :=
    match tB? with
    | some (tId, tTy) =>
      "@[derived] class " ++ cls ++ " (index : " ++ idx ++ ") (" ++ nId ++ " : " ++ nTy ++ ") (" ++ tId ++ " : outParam " ++ tTy ++ ") where\n" ++
      "  " ++ fld ++ " : " ++ col ++ " " ++ nId ++ " " ++ tId ++ " index" ++ missField
    | none =>
      "@[derived] class " ++ cls ++ " (index : " ++ idx ++ ") (" ++ nId ++ " : " ++ nTy ++ ") where\n" ++
      "  " ++ fld ++ " : " ++ col ++ " " ++ nId ++ " index"
  -- the head instance(s)
  let headSrcs : List String :=
    if misses.isEmpty then
      [match tB? with
       | some (tId, tTy) =>
         "@[derived] instance (priority := 100) " ++ instLeaf cl "Head" ++ " {" ++ nId ++ " : " ++ nTy ++ "} {" ++ tId ++ " : " ++ tTy ++ "} {cs : " ++ idx ++ "} :\n" ++
         "  " ++ cls ++ " ((" ++ headElemS ++ ") :: cs) " ++ nId ++ " " ++ tId ++ " := ⟨" ++ headCtorApp ++ "⟩"
       | none =>
         let (sId, sTy) := slotB?.get!
         "@[derived] instance (priority := 100) " ++ instLeaf cl "Head" ++ " {" ++ nId ++ " : " ++ nTy ++ "} {" ++ sId ++ " : " ++ sTy ++ "} {cs : " ++ idx ++ "} :\n" ++
         "  " ++ cls ++ " ((" ++ headElemS ++ ") :: cs) " ++ nId ++ " := ⟨" ++ headCtorApp ++ "⟩"]
    else
      misses.map fun (leaf, subS, tyLitS, missValS) =>
        "@[derived] instance (priority := 100) " ++ instLeaf cl ("Head_" ++ leaf) ++ " {" ++ nId ++ " : " ++ nTy ++ "} {cs : " ++ idx ++ "} :\n" ++
        "  " ++ cls ++ " ((" ++ subS ++ ") :: cs) " ++ nId ++ " " ++ tyLitS ++ " := ⟨" ++ headCtorApp ++ ", " ++ missValS ++ "⟩"
  -- the tail instance (binder order: one element binder → elem, cs,
  -- n, (t); a pair → n, m, u, cs, (t) — the replaced shops' exact
  -- surfaces)
  let tailSrc : String :=
    let missProj := if valTy?.isSome then ", h.miss" else ""
    match tB? with
    | some (tId, tTy) =>
      match tailBs with
      | [(f, fTy)] =>
        "instance " ++ instLeaf cl "Tail" ++ " {" ++ f ++ " : " ++ fTy ++ "} {cs : " ++ idx ++ "} {" ++ nId ++ " : " ++ nTy ++ "} {" ++ tId ++ " : " ++ tTy ++ "} [h : " ++ cls ++ " cs " ++ nId ++ " " ++ tId ++ "] :\n" ++
        "  " ++ cls ++ " (" ++ tailE ++ " :: cs) " ++ nId ++ " " ++ tId ++ " := ⟨" ++ tailCtorApp ++ " h." ++ fld ++ missProj ++ "⟩"
      | [(m, mTy), (u, uTy)] =>
        "instance " ++ instLeaf cl "Tail" ++ " {" ++ nId ++ " : " ++ nTy ++ "} {" ++ m ++ " : " ++ mTy ++ "} {" ++ u ++ " : " ++ uTy ++ "} {cs : " ++ idx ++ "} {" ++ tId ++ " : " ++ tTy ++ "} [h : " ++ cls ++ " cs " ++ nId ++ " " ++ tId ++ "] :\n" ++
        "  " ++ cls ++ " (" ++ tailE ++ " :: cs) " ++ nId ++ " " ++ tId ++ " := ⟨" ++ tailCtorApp ++ " h." ++ fld ++ missProj ++ "⟩"
      | _ => ""
    | none =>
      match tailBs with
      | [(f, fTy)] =>
        "instance " ++ instLeaf cl "Tail" ++ " {" ++ f ++ " : " ++ fTy ++ "} {cs : " ++ idx ++ "} {" ++ nId ++ " : " ++ nTy ++ "} [h : " ++ cls ++ " cs " ++ nId ++ "] :\n" ++
        "  " ++ cls ++ " (" ++ tailE ++ " :: cs) " ++ nId ++ " := ⟨" ++ tailCtorApp ++ " h." ++ fld ++ missProj ++ "⟩"
      | [(m, mTy), (u, uTy)] =>
        "instance " ++ instLeaf cl "Tail" ++ " {" ++ nId ++ " : " ++ nTy ++ "} {" ++ m ++ " : " ++ mTy ++ "} {" ++ u ++ " : " ++ uTy ++ "} {cs : " ++ idx ++ "} [h : " ++ cls ++ " cs " ++ nId ++ "] :\n" ++
        "  " ++ cls ++ " (" ++ tailE ++ " :: cs) " ++ nId ++ " := ⟨" ++ tailCtorApp ++ " h." ++ fld ++ missProj ++ "⟩"
      | _ => ""
  [pathSrc, clsSrc] ++ headSrcs ++ [tailSrc]

@[command_elab declareMemberClass]
meta def declareMemberClassImpl : CommandElab := fun stx => do
  -- the FIXED 28-child arity (the grammar's flat children). Every
  -- optional slot is a null-kind node: PRESENT iff nonempty (absent
  -- optionals have zero args). The where-block keys are `member_`-ATOMS
  -- (grammar contract — the lexer-pollution rule); the positions are
  -- fixed by the grammar, so the keys need no re-check here.
  let cl := argAt stx 1
  let idx := argAt stx 3
  let path := argAt stx 5
  let headCtor := argAt stx 6
  let tailCtor := argAt stx 7
  let idxB1 := argAt stx 11
  let idxB2? : Option Syntax :=
    if argCount (argAt stx 12) > 0 then some (argAt (argAt stx 12) 0) else none
  let slotB? : Option Syntax := if argCount (argAt stx 13) > 0 then some (argAt (argAt stx 13) 2) else none
  let headElem := argAt stx 17
  let tailB1 := argAt stx 21
  let tailB2? : Option Syntax :=
    if argCount (argAt stx 22) > 0 then some (argAt (argAt stx 22) 0) else none
  let fld := argAt stx 25
  let valS? : Option String ←
    if argCount (argAt stx 26) > 0 then
      some <$> render (argAt (argAt stx 26) 3)
    else
      pure none
  let missEnts : List (Syntax × Syntax) ←
    if argCount (argAt stx 27) > 0 then
      let entries := (argAt stx 27).asNode.getArg 2
      pure (entries.asNode.getArgs.toList.map fun e =>
        ((e.asNode).getArg 1, (e.asNode).getArg 3))
    else
      pure []
  -- assemble the modes
  let n ← binderIdentType idxB1
  let tB? ← match idxB2? with
    | none => pure none
    | some b => some <$> binderIdentType b
  let slotB? ← match slotB? with
    | none => pure none
    | some b => some <$> binderIdentType b
  let b1 ← binderIdentType tailB1
  let tailBs : List (String × String) ←
    match tailB2? with
    | none => pure [b1]
    | some b2 => do
        let b2' ← binderIdentType b2
        pure [b1, b2']
  let fldName := fld.getId.toString
  let idxS ← render idx
  -- validation (the mode matrix)
  if tB?.isSome && slotB?.isSome then
    throwError "declare_member_class: param mode (`index` type binder) and ctor mode (`slot`) are exclusive"
  if tB?.isNone && slotB?.isNone then
    throwError "declare_member_class: needs the type slot — `member_index := (n : …) (t : Ty)` (param mode) or `member_slot := (t : …)` (ctor mode)"
  if missEnts.isEmpty && valS?.isSome then
    throwError "declare_member_class: `member_val :=` requires the `member_miss :=` table"
  if !missEnts.isEmpty && valS?.isNone then
    throwError "declare_member_class: `member_miss :=` requires the value type — `member_val := (Value)`"
  if !missEnts.isEmpty && tB?.isNone then
    throwError "declare_member_class: `member_miss :=` requires param mode (the outParam slot)"
  -- pre-render the miss table (the substitution is structural: on the
  -- caller's head-element SYNTAX, at the slot id, then reprint)
  let headElemS ← render headElem
  let missPrepared : List (String × String × String × String) ←
    match tB? with
    | none => pure []
    | some (tId, _) => do
        let mut out : List (String × String × String × String) := []
        for (tyLit, missVal) in missEnts do
          let leaf := (termLastIdent tyLit).toString
          let subS ← render (substIdent (Name.mkSimple tId) tyLit headElem)
          let tyLitS ← render tyLit
          let missValS ← render missVal
          out := out ++ [(leaf, subS, tyLitS, missValS)]
        pure out
  for src in genSrcs cl idxS path headCtor tailCtor n tB? slotB? headElemS tailBs fldName valS? missPrepared do
    CodegenCore.elabGenerated (src ++ "\n")

end CodegenCore.MemberKit
