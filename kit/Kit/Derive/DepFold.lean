/-
# Kit.Derive.DepFold — the DEPENDENT fold generator (`declare_dependent_fold`)

`declare_dependent_fold <Ind>` over an INDEXED family `Ind : I → Type`
(a GADT — the shape `SchemaCore.Value` has) — or over the HEAD of a
MUTUAL sibling block (`Value`/`VList`/`VMap`) — generates the
DEPENDENT fold's whole entourage MECHANICALLY (06 §2: the motive rides
the index). This is the named extension `Kit.Derive.Fold`'s
`declare_fold` refused (its eKD0002 names this module); the generated
surface is the hand `foldValue` entourage's, one level up:

- `<Head>Alg (P₁ … Pₙ)` — the DEPENDENT algebra record: ONE record for
  the whole block, one MOTIVE parameter per sibling in block order
  (`ValueAlg P Q R`), one field per constructor — a row per
  (sibling, ctor), keyed by that sibling's motive (each row's RESULT
  riding its result index, a recursive child's slot the CHILD's
  sibling's motive at the child's index, every other argument passing
  through raw; the constructor's implicit index binders ride the row
  as implicit binders — the `ValueAlg.some : {t : Ty} → P t →
  P (.option t)` shape). The row NAME is the constructor's base name,
  except that a CO-SIBLING's rows carry the sibling's lowercased
  initial (`VList.nil` → `vnil`, `VMap.cons` → `mcons`) — the hand
  `ValueAlg`'s discipline, keeping the one record's fields distinct.
  Exhaustiveness in the type, as in V1.
- `fold<Ind>`, `fold<Sib>…` — THE FOLD per sibling: `alg → <indices> →
  Ind … → P …`, total, structural, kernel-visible (the hand
  `foldValue` shape: the match on the index AND the value, every
  arm's index pattern ctor-headed). The HEAD sibling's index binders
  are explicit (the entry point — callers name the index, the codec's
  `foldValue valEncAlg k.toTy v` shape); the CO-SIBLINGS' are implicit
  (the index rides the value — the hand `foldVList`/`foldVMap`
  shape). For a block the defs emit as ONE `mutual` fold block — the
  siblings' structural recursion is joint — as a singleton def
  otherwise. The fold's body is the EXPLICIT-MATCH form
  (`fun <indices> x => match <indices>, x with …`) — structural on
  (index, value), so the equation lemmas close by `rfl`.
- `fold<Sib>_<ctor>` — the equation set (06 §5), all `rfl` (the
  recursion is structural, so the equations are kernel reduction).
- `fold<Sib>_unique` — THE INITIALITY LAW per sibling: a function that
  commutes with the algebra on that sibling's every constructor IS
  the fold — one `Sib.rec` application with the target motive `fun i
  x => f i x = fold<Sib> alg i x`, the co-siblings' motives `True`
  (their commutations are NOT needed: every hypothesis is stated with
  the FULL folds on the row's cross-sibling children, so each minor
  closes by `rw [h_<ctor>, ihs…, fold<Sib>_<ctor>]` — the same
  template `foldTy_unique` rides; 06 §10).

THE EMISSION IS THE PARSE ROUTE: the generated commands are rendered
to SOURCE TEXT and parsed by the real parser
(`Lean.Parser.runParserCategory`), then elaborated — never spliced as
quotation syntax. THE NAMED WALL (two defeats recorded, the second
forcing this design): a quotation-spliced match — whether the
def-equation spelling or the explicit `match` — elaborates its GADT
index patterns to PROJECTION garbage in the generated context
(`.result ok err` → `ok.result err`; qualified `SchemaCore.Ty.result
ok err` fared no better) or dies silently to the elaborator's sorry
recovery, while the BYTE-IDENTICAL hand spelling elaborates clean;
the discriminator is the quotation's hygiene scopes, not the
spelling. The parse route removes the dependence: the generated
surface IS source text, elaborated exactly like hand code — and the
generated statements carry the hand spellings verbatim (the
strongest form of the migration's byte-tie).

HONEST FRAGMENT (each refusal is a curated `Kit.Diag`, the unsupported
shape NAMED — 05 §4). The fragment is exactly the shape the probe
proofs certified:

- per sibling: `Type`-sorted, ≥ 1 index, no type parameters, nonempty
  ctors — the shared codes name each (the KINDS are V1's, the
  dependent spelling);
- every constructor's RESULT SLOTS are PATTERNS: constructor-headed or
  literal — a non-constructor head (`n * 2`) is not a pattern at all;
  a BARE-VARIABLE slot is the wildcard shape: refused for the
  single-family entry (its fold's explicit index demands a pattern —
  eKD0019), allowed for the block's siblings (the hand `foldVList`'s
  `| _, .nil` arms — the index rides the value, the column is a
  wildcard and the `rfl` equations live);
- every IMPLICIT constructor binder and every recursive child's index
  must be DETERMINED BY the result slots (the fold arm can only name
  what the index patterns bind);
- recursive constructor arguments are EXPLICIT (an implicit recursive
  arg has no place to bind its child's index in the pattern);
- constructor argument types in the flat delaboratable fragment
  (constant / application / non-dependent arrow) — the same delab
  fragment V1's `tyToSyntax` owns, now WITH the constructor's own
  binders (a GADT's `Fin cap` arg is the bread-and-butter shape).

Type parameters, empty constructor sets, nested occurrences, and
non-explicit NON-index constructor arguments keep their V1 refusals
(the shared codes — the same KINDS, the dependent spelling).

The proof discipline is V1's: the generated theorems are
recursor-driven templates over the ctor data — a shape the template
cannot carry fails to elaborate (wrongness does not elaborate). The
whole fragment is pinned by KitTests' dependent-fold fixtures (the
`V2` GADT + the mutual `F1`/`F2` sibling pair + the two-arg
index-ctor GADT: the equations by `rfl`, the initiality laws
axiom-free, the migration pins hand-fold ≡ generated fold, the
refusals byte-pinned).

E-codes: `KD0015`–`KD0019` (the KD family's dependent-fold rows —
allocated from the PERSISTED registry; the constants are the family's
DECLARATION, the sites use them, never a bare string). The reused
V1 codes (`eKD0001`–`eKD0005`, `eKD0008`, `eKD0009`) are
Kit.Derive.Fold's rows — the same refusal kinds, this driver's
message spellings.

Core-only (imports Lean + Kit.Diag + Kit.Derive.Common — the cone
rule). META module: the generated decls are ordinary core-level
definitions + theorems.

Five questions (notes/v3/01-core.md):
- root: META — the initial-algebra discipline's DEPENDENT generator
  face (01 §1 one level up: the motive rides the index, 06 §2).
- carrier grade: none of its own; the generated surface is the
  dependent algebra record + the folds (the consumers' algebras are
  the carriers).
- spine reading: the SHARED recursion stage — one fold per indexed
  universe, consumers as algebras.
- ladder rung: the generated laws are recursor templates + `rfl`
  equations (kernel-visible; zero axioms — pinned by KitTests).
- gate row: KitTests' dependent-fold suite (the fixtures' entourages +
  the refusal teeth + the axiom pins).
-/

module

public meta import Lean
public meta import Kit.Diag
public meta import Kit.Derive.Common
public meta import Kit.Derive.Fold

public meta section

namespace Kit.Derive.DepFold

open Lean Elab Command Meta

open Kit.Derive.Common (throwDiag resolveConst?)
open Kit.Derive.Fold
  (baseNameOf eKD0001 eKD0002 eKD0003 eKD0004 eKD0005 eKD0008 eKD0009)

/-! ## The curated failures -/

/-- The KD dependent-fold rows (allocated from the persisted registry;
    the declaration IS the family's extension — see the module
    header). -/
def eKD0015 : Kit.ECode := ⟨"KD0015"⟩
def eKD0016 : Kit.ECode := ⟨"KD0016"⟩
def eKD0017 : Kit.ECode := ⟨"KD0017"⟩
def eKD0018 : Kit.ECode := ⟨"KD0018"⟩
def eKD0019 : Kit.ECode := ⟨"KD0019"⟩

/-! ## The inductive analysis -/

/-- One constructor binder's analyzed shape: its fvar (the analysis
    telescope's key), the GENERATED name (minted fresh — the one ident
    every generated quotation shares), its type, and its binder info
    (implicit index binders ride the rows as implicits — the
    `ValueAlg.some` shape). -/
structure DepBinder where
  fvarId : FVarId
  name : Name
  type : Expr
  info : BinderInfo deriving Inhabited

/-- One constructor's analyzed shape: the ctor's full name, its
    ALGEBRA-ROW name (the base name; a co-sibling's rows carry the
    sibling's lowercased initial — `vnil`, `mcons`), the binders in
    telescope order, the RESULT SLOTS (one expression per index slot
    of the ctor's return), the positions of the RECURSIVE arguments,
    and — parallel to `recArgs` — each recursive child's SIBLING
    position and its own index slots (the `P` slot's indices). -/
structure DepCtorShape where
  name : Name
  field : String
  binders : Array DepBinder
  resultSlots : Array Expr
  recArgs : Array Nat
  recSib : Array Nat
  recIdx : Array (Array Expr) deriving Inhabited

/-- One SIBLING of the (possibly singleton) block: its inductive, its
    base name, its index types (in order — the motive's telescope),
    and its constructors' analyzed shapes. -/
structure SibShape where
  name : Name
  base : String
  idxTys : Array Expr
  ctors : Array DepCtorShape deriving Inhabited

/-- The fvars occurring in `e` (the generator's own collector —
    binder scoping ignored: an over-approximation only risks a refusal,
    never a wrongness). -/
partial def collectFVarIds (e : Expr) (acc : Array FVarId) : Array FVarId :=
  match e with
  | .fvar id => if acc.contains id then acc else acc.push id
  | .app f a => collectFVarIds a (collectFVarIds f acc)
  | .lam _ d b _ => collectFVarIds b (collectFVarIds d acc)
  | .forallE _ d b _ => collectFVarIds b (collectFVarIds d acc)
  | .letE _ t v b _ => collectFVarIds b (collectFVarIds t (collectFVarIds v acc))
  | .mdata _ e => collectFVarIds e acc
  | .proj _ _ e => collectFVarIds e acc
  | _ => acc

/-- A fresh binder name: the ctor's own userName when it is a usable
    plain string and unclaimed, else a synthesized `j<k>` — the
    generated quotations' binder names cannot collide (the token
    discipline's mint). -/
def freshBinderName (used : Array Name) (u : Name) : Name :=
  let ok := match u with
    | .str _ s => !s.isEmpty && !u.isInaccessibleUserName && !s.startsWith "_"
    | _ => false
  if ok && !used.contains u then u
  else
    -- the synthesized search is FUEL-BOUNDED: by `k = used.size + 1` a
    -- free `j<k>` is certain (only `used.size` names are claimed)
    let rec go : Nat → Nat → Name := fun fuel k =>
      let c := Name.mkSimple s!"j{k}"
      if used.contains c then
        match fuel with
        | 0 => c
        | f + 1 => go f (k + 1)
      else c
    go (used.size + 1) 1

/-- The index-binder name an index TYPE mints: the type's base name's
    lowercased initial (`Ty` → `t`, `KeyTy` → `k`, `Ix` → `i`) — the
    hand `foldValue (t : Ty)` / `foldVMap {k : KeyTy}` spellings. -/
def idxNameOf (ty : Expr) : Name :=
  match ty with
  | .const c _ =>
      match (baseNameOf c).toList with
      | ch :: _ => Name.mkSimple (String.singleton ch.toLower)
      | [] => `i
  | _ => `i

/-- Is `c` a constructor (the index pattern's allowed head)? -/
def isCtorConst (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.ctorInfo _) => true
  | _ => false

/-- THE INDEX-PATTERN CHECK: the result slot must elaborate as a
    PATTERN — constructor-headed or literal — never a non-constructor
    application (`n * 2` is not a pattern). A bare variable at the TOP
    level is the wildcard shape: refused for the single-family entry
    (`eKD0019` — the explicit index demands a pattern; a variable
    index forces the matcher to split and the `rfl` equations die —
    probe-certified), allowed inside a MUTUAL block (the siblings'
    index columns ride their values as wildcards — the hand
    `foldVList`'s `| _, .nil` shape). -/
partial def checkIdxPattern (ind : TSyntax `ident) (ctorName : Name)
    (top : Bool) (mutualOk : Bool) (e : Expr) : CommandElabM Unit := do
  let env ← getEnv
  let fail (why : String) : CommandElabM Unit :=
    throwDiag eKD0019
      s!"declare_dependent_fold {ind.getId}: constructor `{ctorName}`'s \
        result index is {why} — the fragment's index patterns are \
        constructor-headed or literal (a variable index forces the \
        matcher to split and the rfl equations die); the \
        variable-index shape is the named extension"
  match e with
  | .lit _ => pure ()
  | .fvar _ => if top && !mutualOk then fail "a bare variable"
  | .const c _ =>
      unless isCtorConst env c do
        fail s!"headed by `{c}`, which is not a constructor"
  | .app _ _ =>
      match e.getAppFn with
      | .const c _ =>
          unless isCtorConst env c do
            fail s!"headed by `{c}`, which is not a constructor"
      | _ => fail "a non-constructor application"
      for a in e.getAppArgs do
        match a with
        | .fvar _ => pure ()   -- the pattern variable
        | _ => checkIdxPattern ind ctorName false mutualOk a
  | _ => fail "outside the pattern fragment"

/-- The per-ctor analysis: the ctor's telescope (binders minted fresh),
    the result slots, the recursive positions (+ each child's sibling
    and its index slots), and the fragment checks (implicit recursive
    args, undetermined binders, the index-pattern fragment, nested
    occurrences). `sibs` are the block's sibling names, `sibPos` this
    ctor's own sibling's position, `pfx` the row-name prefix
    (empty for the head sibling, the sibling's lowercased initial
    otherwise). -/
def analyzeCtor (ind : TSyntax `ident) (sibs : Array Name) (sibPos : Nat)
    (numIdx : Nat) (pfx : String) (reserved : Array Name) (ctorName : Name) :
    CommandElabM DepCtorShape := do
  let env ← getEnv
  let some cci := env.find? ctorName |
    throwDiag eKD0001
      s!"declare_dependent_fold {ind.getId}: missing constructor `{ctorName}`"
  let (binders, result) ← liftTermElabM do
    forallTelescope cci.type fun args result => do
      -- the ctor binders' names cannot collide with the generated
      -- surface's fixed idents (the motives, the index binders, alg/f/x)
      let mut used : Array Name := reserved
      let mut bs : Array DepBinder := #[]
      for k in [0:args.size] do
        let d ← getFVarLocalDecl args[k]!
        let nm := freshBinderName used d.userName
        used := used.push nm
        bs := bs.push { fvarId := d.fvarId, name := nm
                        type := d.type, info := d.binderInfo }
      pure (bs, result)
  unless result.getAppFn.isConstOf sibs[sibPos]! do
    throwDiag eKD0002
      s!"declare_dependent_fold {ind.getId}: constructor `{ctorName}` does \
        not return its own sibling inductive"
  unless result.getAppNumArgs == numIdx do
    throwDiag eKD0002
      s!"declare_dependent_fold {ind.getId}: constructor `{ctorName}` does \
        not return the inductive at its declared index arity — the \
        analysis is inconsistent"
  let resultSlots := result.getAppArgs
  -- the recursive positions + their child siblings and index slots
  let mut recArgs : Array Nat := #[]
  let mut recSib : Array Nat := #[]
  let mut recIdx : Array (Array Expr) := #[]
  for k in [0:binders.size] do
    let ty := binders[k]!.type
    -- the child's SIBLING: the spine's head const (a two-index child
    -- — the `VMap k v` shape — buries the const in the application
    -- spine; `getAppFn` reaches it)
    let childSib? : Option Nat :=
      match ty.getAppFn with
      | .const c _ => sibs.findIdx? (· == c)
      | _ => none
    match childSib? with
    | some j =>
        unless binders[k]!.info == .default do
          throwDiag eKD0017
            s!"declare_dependent_fold {ind.getId}: constructor \
              `{ctorName}`'s argument {k} is a RECURSIVE argument in an \
              implicit binder — the generated pattern cannot name the \
              child's index; the implicit-recursive fragment is the \
              named extension"
        recArgs := recArgs.push k
        recSib := recSib.push j
        recIdx := recIdx.push ty.getAppArgs
    | none =>
        if (ty.find? (fun e => sibs.any (e.isConstOf ·))).isSome then
          throwDiag eKD0005
            s!"declare_dependent_fold {ind.getId}: constructor \
              `{ctorName}`'s argument {k} mentions a sibling below the \
              root — the NESTED fragment is out of scope"
  -- every IMPLICIT binder must be determined by the result slots (the
  -- fold arm names it through the index patterns)
  let mut idxFVars : Array FVarId := #[]
  for s in resultSlots do
    idxFVars := collectFVarIds s idxFVars
  for b in binders do
    if b.info != .default && !(idxFVars.contains b.fvarId) then
      throwDiag eKD0018
        s!"declare_dependent_fold {ind.getId}: constructor `{ctorName}`'s \
          implicit binder `{b.name}` is not determined by the result \
          index — the generated fold arm can only name what the index \
          pattern binds; the undetermined-binder fragment is the named \
          extension"
  -- every recursive child's index slots must be determined by the
  -- result slots
  for s in recIdx do
    for a in s do
      for fv in collectFVarIds a #[] do
        unless idxFVars.contains fv do
          throwDiag eKD0018
            s!"declare_dependent_fold {ind.getId}: constructor \
              `{ctorName}`'s recursive child's index is not determined \
              by the result index — the generated fold arm can only \
              name what the index pattern binds; the \
              undetermined-child-index fragment is the named extension"
  for s in resultSlots do
    checkIdxPattern ind ctorName true (sibs.size > 1) s
  liftIO do
  pure { name := ctorName, field := pfx ++ baseNameOf ctorName
         binders := binders, resultSlots := resultSlots
         recArgs := recArgs, recSib := recSib, recIdx := recIdx }

/-- Analyze the `declare_dependent_fold` target: resolve it, refuse
    every shape outside the dependent fragment, and return the head
    inductive's value + the block's sibling shapes (block order). -/
def analyzeDepInd (ind : TSyntax `ident) :
    CommandElabM (InductiveVal × Array SibShape × Array (Array Name)) := do
  let some indName := ← resolveConst? ind |
    throwDiag eKD0001
      s!"declare_dependent_fold {ind.getId}: unknown constant — valid \
        usage: `declare_dependent_fold <Ind>` over a one-index \
        (`I → Type`) GADT family or the head of a mutual sibling block"
  let env ← getEnv
  let some ci := env.find? indName |
    throwDiag eKD0001
      s!"declare_dependent_fold {ind.getId}: `{indName}` is not a \
        declaration — valid usage: `declare_dependent_fold <Ind>` over \
        a one-index (`I → Type`) GADT family or the head of a mutual \
        sibling block"
  let ii? : Option InductiveVal :=
    match ci with
    | .inductInfo ii => some ii
    | _ => none
  let some ii := ii? |
    throwDiag eKD0001
      s!"declare_dependent_fold {ind.getId}: `{indName}` is not an \
        inductive — valid usage: `declare_dependent_fold <Ind>` over a \
        one-index (`I → Type`) GADT family or the head of a mutual \
        sibling block"
  let single := ii.all.length == 1
  let sibNames : Array Name := ii.all.toArray
  -- PASS 1: the per-sibling checks + index types (no ctor analysis yet —
  -- the ctor binders' names must avoid the index binders', so the index
  -- names are minted first)
  let heads : Array (InductiveVal × Array Expr × Nat) ←
    sibNames.mapM fun sibName => do
    let some sci := env.find? sibName |
      throwDiag eKD0001
        s!"declare_dependent_fold {ind.getId}: `{sibName}` is not a \
          declaration"
    let sii? : Option InductiveVal :=
      match sci with
      | .inductInfo sii => some sii
      | _ => none
    let some sii := sii? |
      throwDiag eKD0001
        s!"declare_dependent_fold {ind.getId}: `{sibName}` is not an \
          inductive"
    let sibPos : Nat := sibNames.findIdx? (· == sibName) |>.get!
    -- the params check FIRST: a parameterized family may report
    -- `numIndices == 0` too (the parameterization is the sharper refusal)
    if sii.numParams != 0 then
      throwDiag eKD0003
        s!"declare_dependent_fold {ind.getId}: `{sii.name}` has type \
          parameters — the parameter-threaded fragment is the named \
          extension; the dependent scope is the parameter-free family"
    if sii.numIndices == 0 then
      throwDiag eKD0015
        s!"declare_dependent_fold {ind.getId}: `{sii.name}` has no type \
          indices — the index-free shape is `declare_fold`'s \
          (Kit.Derive.Fold); the dependent generator is the indexed face"
    if single && sii.numIndices > 1 then
      throwDiag eKD0015
        s!"declare_dependent_fold {ind.getId}: `{sii.name}` has \
          {sii.numIndices} indices — the fragment is the ONE-index \
          family (`I → Type`); the multi-index shape is the named \
          extension"
    if sii.ctors.isEmpty then
      throwDiag eKD0004
        s!"declare_dependent_fold {ind.getId}: `{sii.name}` has no \
          constructors — the empty universe's fold is `nomatch`, which \
          an algebra record cannot carry"
    let (idxTys, sortIsType) ← liftTermElabM do
      forallTelescope sci.type fun args result => do
        let mut idxTys : Array Expr := #[]
        for m in [0:sii.numIndices] do
          idxTys := idxTys.push (← getFVarLocalDecl args[m]!).type
        let sortIsType :=
          match result with
          | .sort l => l == Level.ofNat 1
          | _ => false
        pure (idxTys, sortIsType)
    unless sortIsType do
      throwDiag eKD0016
        s!"declare_dependent_fold {ind.getId}: `{sii.name}`'s sort is \
          not `Type` — the fragment's algebras are `P : I → Type`-valued; \
          the `Prop`/`Type u` families are the named extension"
    pure (sii, idxTys, sibPos)
  -- PASS 1.5: the row-name prefixes: the head sibling plain; each
  -- CO-SIBLING's rows carry the first letter of its base name that no
  -- earlier sibling claimed (`VList` → `v`, then `VMap` → `m` — the
  -- hand `ValueAlg`'s `vnil`/`mcons` spellings, reproduced mechanically;
  -- the whole-base fallback when the letters are exhausted)
  let mut taken : Array Char := #[]
  let mut pfxs : Array String := #[]
  for h in heads do
    if h.2.2 == 0 then
      pfxs := pfxs.push ""
    else
      let b := baseNameOf h.1.name
      let pfx : String :=
        match b.toList.find? (fun ch => !taken.contains ch.toLower) with
        | some ch => String.singleton ch.toLower
        | none => b.toLower
      taken := taken.push pfx.toList.head!
      pfxs := pfxs.push pfx
  let letters := "PQRSTUVWXYZ".toList
  -- PASS 2: the index-binder names (each index type's base name's
  -- lowercased initial, deduped against the motives and each other)
  let mut idxNms : Array (Array Name) := #[]
  let reservedBase : Array Name :=
    ((Array.range heads.size).map fun k =>
      Name.mkSimple (letters[k]!.toString)) ++ #[`alg, `f, `x]
  let mut reservedAll : Array Name := reservedBase
  for h in heads do
    let _sii := h.1
    let idxTys := h.2.1
    let mut nms : Array Name := #[]
    for ty in idxTys do
      let nm := freshBinderName reservedAll (idxNameOf ty)
      reservedAll := reservedAll.push nm
      nms := nms.push nm
    idxNms := idxNms.push nms
  -- PASS 3: the ctor analysis — the ctor binders keep their OWN names
  -- (the hand rows' `{t : Ty}`/`{ok err : Ty}` spellings — the row
  -- binders are the CONSUMERS' named-argument face —
  -- `valEncAlg.vnil (t := t)`); a ctor binder only avoids the motives
  -- and the alg/f/x fixed idents, never the index binders (a pattern
  -- binder legitimately shadows a fun binder)
  let sibs : Array SibShape ←
    ((heads.zip idxNms).zip pfxs) |>.mapM fun p => do
      let h := p.1.1
      let sii := h.1
      let idxTys := h.2.1
      let sibPos := h.2.2
      let _nms := p.1.2
      let pfx := p.2
      let ctors ←
        (sii.ctors.mapM
          (analyzeCtor ind sibNames sibPos sii.numIndices
            pfx reservedBase) :
          CommandElabM (List DepCtorShape))
      pure { name := sii.name, base := baseNameOf sii.name
             idxTys := idxTys, ctors := ctors.toArray }
  pure (ii, (sibs, idxNms))

/-! ## The string emission (the parse route)

The generated commands are rendered to SOURCE TEXT and parsed by the
REAL parser (`Lean.Parser.runParserCategory`), then elaborated. The
quotation route died on a hygiene wall this module now names: a
quotation-spliced match (def-equation or explicit `match`) elaborates
its dotted/qualified GADT patterns to PROJECTION garbage (`.result ok
err` → `ok.result err`) or dies to the elaborator's sorry recovery —
while the byte-identical hand spelling and the freshly parsed spelling
elaborate clean. The parse route removes the dependence: the generated
surface IS source text, elaborated exactly like hand code — and the
generated statements can (and do) carry the hand spellings verbatim,
which is the strongest form of the migration's byte-tie. -/

/-- The generated commands' shared renderer context: ONE command
    syntax (the shared macro scope — the token discipline), the
    telescope's fvar ids, and the minted names, position-parallel. -/
structure DelabEnv where
  stx : Syntax
  fvarIds : Array FVarId
  names : Array Name

def DelabEnv.ident (env : DelabEnv) (id : FVarId) :
    CommandElabM String := do
  match env.fvarIds.findIdx? (· == id) with
  | some k => pure env.names[k]!.toString
  | none =>
    throwDiag eKD0009
      s!"declare_dependent_fold: a constructor binder escaped its \
        telescope — the generated surface cannot name it (the \
        renderer's invariant broke)"

/-- Is `s` an atomic render (no parens needed as an argument)? -/
private def atomicS (s : String) : Bool :=
  let bad := s.any (fun ch => ch == ' ' || ch == '(')
  !bad

/-- Parenthesize a non-atomic slot render (a multi-arg index ctor's
    slot — `P .result ok err` is `((P .result) ok) err`; the slot must
    ride as ONE argument: `P (.result ok err)`). -/
private def parenSlotS (s : String) : String :=
  if atomicS s then s else "(" ++ s ++ ")"

/-- THE RENDERER (type + index expressions, one fragment): fvars (the
    minted binder names, or WILDCARD holes in the arm-column mode),
    literals, dot-form constructor heads (the hand spellings — the
    parser resolves them fresh, so the namespace shadowing that kills
    quotation-spelled dots cannot recur), plain constants (full names;
    a child's `KeyTy.toTy k` slot), applications (non-atomic arguments
    parenthesized). -/
private partial def renderExprS (env : DelabEnv) (wild : Bool) (e : Expr) :
    CommandElabM String := do
  match e with
  | .fvar id =>
      if wild then
        pure "_"
      else
        env.ident id
  | .lit l =>
      match l with
      | .natVal n => pure (toString n)
      | _ =>
        throwDiag eKD0009
          s!"declare_dependent_fold: index literal `{e}` is outside the \
            generator's renderable fragment"
  | .const c _ =>
      let envC ← getEnv
      if isCtorConst envC c then
        pure ("." ++ baseNameOf c)
      else
        pure c.toString
  | .app f a => do
      let fS ← renderExprS env wild f
      let aS ← renderExprS env wild a
      if atomicS aS then
        pure (fS ++ " " ++ aS)
      else
        pure (fS ++ " (" ++ aS ++ ")")
  | .mdata _ e => renderExprS env wild e
  | _ =>
    throwDiag eKD0009
      s!"declare_dependent_fold: type expression `{e}` is outside the \
        generator's renderable fragment (constant / application / \
        non-dependent arrow shapes)"

/-- One binder's text: implicit brace, explicit paren, the type the
    slot's own (a recursive row slot's type is the CHILD's motive at
    the child's index slots — `P t`, `R k v`; `none` = the raw
    type). -/
private def renderBinderS (env : DelabEnv) (slotTy : Option String)
    (b : DepBinder) : CommandElabM String := do
  let ty : String ←
    match slotTy with
    | some t => pure t
    | none => renderExprS env false b.type
  let nm := b.name.toString
  if b.info == .default then
    pure s!"({nm} : {ty})"
  else
    pure (s!"\{{nm} : {ty}" ++ "}")

/-- The arrow telescope, outermost first. -/
private def renderArrowsS (bs : List String) (body : String) : String :=
  bs.foldr (fun b acc => s!"{b} → {acc}") body

/-- Parse ONE generated command with the real parser and elaborate it.
    A parse failure is a curated diagnostic (the generator's own
    bug — named, never silent). -/
private def elabParsed (ind : TSyntax `ident) (src : String) :
    CommandElabM Unit := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `command src (fileName := "<gen>") with
  | .ok s => elabCommand s
  | .error e =>
    throwDiag eKD0009
      s!"declare_dependent_fold {ind.getId}: the generated command \
        failed to parse — the emission is out of the fragment: {e}"

/-- Everything the builders need for one ctor, computed ONCE (string
    face). -/
structure CtorViewS where
  c : DepCtorShape
  env : DelabEnv
  argNames : Array String            -- ALL binders, telescope order
  explicitNames : Array String       -- the explicit binders only
  ihNames : Array String             -- one per recursive arg
  colsWild : Array String            -- the fold arm's index columns
                                     -- (bare leaves wildcarded in the
                                     -- mutual mode)
  colsSpell : Array String           -- the result slots, fully spelled
  ctorPat : String                   -- `.ok j1` (dot + explicit args)
  recSlotSs : Array (Array String)   -- per recursive arg: the child's
                                     -- spelled index slots

private def buildCtorViewS (stx : Syntax) (isMutual : Bool)
    (c : DepCtorShape) : CommandElabM CtorViewS := do
  let env : DelabEnv :=
    { stx := stx, fvarIds := c.binders.map (·.fvarId)
      names := c.binders.map (·.name) }
  let argNames ← c.binders.mapM (fun b => env.ident b.fvarId)
  let explicitNames : Array String ←
    (Array.range c.binders.size).filterMapM fun k =>
      pure (if c.binders[k]!.info == .default then some argNames[k]! else none)
  let ihNames : Array String :=
    (Array.range c.recArgs.size).map (fun a => s!"ih{a + 1}")
  let colsWild ← c.resultSlots.mapM (renderExprS env isMutual)
  let colsSpell ← c.resultSlots.mapM (renderExprS env false)
  -- the PATTERN carries the CONSTRUCTOR's base name (the record's row
  -- name may be mangled for a co-sibling: `vnil`, `mcons`)
  let head := "." ++ baseNameOf c.name
  let ctorPat : String :=
    if explicitNames.isEmpty then head
    else head ++ " " ++ String.intercalate " " explicitNames.toList
  let recSlotSs ← c.recIdx.mapM (fun s => s.mapM (renderExprS env false))
  pure { c := c, env := env, argNames := argNames
         explicitNames := explicitNames, ihNames := ihNames
         colsWild := colsWild, colsSpell := colsSpell, ctorPat := ctorPat
         recSlotSs := recSlotSs }

/-- Where a recursive child's re-entering call is built: `arm` = the
    fold def's own match arm (the mutual mode wildcards the head
    sibling's index slots — the hand `foldValue alg _ v` shape), `eq` =
    the equation lemma's rhs (the slots spelled — the hand
    `foldValue alg t v` shape), `hyp t` = the initiality law's
    commutation for sibling `t` (the TARGET's own children re-enter
    through `f`, the other siblings' through the full folds). -/
inductive RecMode where
  | arm | eq | hyp (target : Nat)

/-- The recursive child's re-entering call (string face). -/
private def renderRecAppS (isMutual : Bool) (headArity : Nat)
    (foldNames : Array String) (fS : String) (algS : String)
    (mode : RecMode) (childSib : Nat) (childSlots : Array String)
    (argS : String) : String :=
  if childSib == 0 then
    match mode with
    | .arm =>
        if isMutual then
          let holes := (Array.range headArity).map (fun _ => "_")
          s!"{foldNames[0]!} {algS} {String.intercalate " " holes.toList} {argS}"
        else
          s!"{foldNames[0]!} {algS} {String.intercalate " " (childSlots.toList.map parenSlotS)} {argS}"
    | .eq => s!"{foldNames[0]!} {algS} {String.intercalate " " (childSlots.toList.map parenSlotS)} {argS}"
    | .hyp t =>
        if t == 0 then
          s!"{fS} {String.intercalate " " (childSlots.toList.map parenSlotS)} {argS}"
        else
          s!"{foldNames[0]!} {algS} {String.intercalate " " (childSlots.toList.map parenSlotS)} {argS}"
  else
    let foldSib := foldNames[childSib]!
    match mode with
    | .hyp t =>
        if t == childSib then s!"{fS} {argS}"
        else s!"{foldSib} {algS} {argS}"
    | _ => s!"{foldSib} {algS} {argS}"

/-- The row-application rhs: the algebra's field applied to the
    EXPLICIT arguments (the implicit index binders ride the row's
    type, inferred from the result index), a recursive child
    re-entering via `renderRecAppS`. -/
private def renderRowRhsS (v : CtorViewS) (algS : String) (rowFn : String)
    (recApp : Nat → Array String → String → String) : String :=
  let explicitPos : Array Nat :=
    (Array.range v.c.binders.size).filter (fun k => v.c.binders[k]!.info == .default)
  let parts : Array String := explicitPos.map fun k =>
    match v.c.recArgs.findIdx? (· == k) with
    -- a recursive child's re-entering call is NON-ATOMIC — it rides as
    -- ONE parenthesized argument (the hand `alg.ok (foldValue alg ok v)`
    -- shape)
    | some m => parenSlotS (recApp v.c.recSib[m]! v.recSlotSs[m]! v.argNames[k]!)
    | none => v.argNames[k]!
  s!"{rowFn} {algS} {String.intercalate " " parts.toList}"

/-- The motive TYPE text for sibling `j` (`Ty → Type`,
    `KeyTy → Ty → Type`, …). -/
private def renderMotTyS (idxTySs : Array String) : String :=
  String.intercalate " → " (idxTySs.toList ++ ["Type"])

/-- Nested anonymous lambdas (the discarder minors' and the `True`
    motives' shape): one `_` (explicit) or `{_}` (implicit) binder per
    info, outermost first. -/
private def renderAnonLambdasS (infos : Array BinderInfo) (body : String) : String :=
  let rec go : Nat → String → String
    | 0, b => b
    | k + 1, b =>
        let inner := go k b
        if infos[infos.size - k - 1]! == .default then
          s!"fun _ => {inner}"
        else
          s!"fun \{_} => {inner}"
  go infos.size body

/-! ## The command -/

syntax (name := declareDepFoldCmd) "declare_dependent_fold " ident : command

/-- THE DEPENDENT FOLD GENERATOR: `declare_dependent_fold <Ind>` — see
    the module header for the generated surface + the honest fragment. -/
@[command_elab Kit.Derive.DepFold.declareDepFoldCmd]
def elabDeclareDepFold : CommandElab
  | stx@`(command| declare_dependent_fold $ind:ident) => do
    let (ii, sibs, idxNms) ← analyzeDepInd ind
    let isMutual := sibs.size > 1
    let headBase := baseNameOf ii.name
    let algName := Name.mkSimple s!"{headBase}Alg"
    -- the motive names: P, Q, R, … in block order (the hand ValueAlg's
    -- `P Q R` spellings)
    let letters := "PQRSTUVWXYZ".toList
    if sibs.size > letters.length then
      throwDiag eKD0008
        s!"declare_dependent_fold {ind.getId}: the mutual block has \
          {sibs.size} siblings — the generated motive names (P, Q, R, …) \
          cover {letters.length}; the nameless-sibling shape is out of \
          scope"
    let motiveNms : Array Name :=
      (Array.range sibs.size).map fun k => Name.mkSimple (letters[k]!.toString)
    let envEmpty : DelabEnv := { stx := stx, fvarIds := #[], names := #[] }
    let views ← sibs.mapM (fun s => s.ctors.mapM (buildCtorViewS stx isMutual))
    let algS := algName.toString
    let fS := "f"
    let xS := "x"
    -- the separators (string literals cannot nest inside an
    -- interpolated string's interpolation)
    let sp := " "
    let cm := ", "
    let sibNameS : Array String := sibs.map (fun s => s.name.toString)
    let foldNames : Array String :=
      sibs.map (fun s => s!"fold{s.base}")
    let idxNameSs : Array (Array String) :=
      idxNms.map (fun nms => nms.map (fun n => n.toString))
    let idxTySs : Array (Array String) ←
      sibs.mapM fun s => s.idxTys.mapM (renderExprS envEmpty false)
    let motTySs : Array String := idxTySs.map renderMotTyS
    -- the motive parameter list on the record (`(P : Ty → Type) (Q : …)`)
    let recMotParams : String :=
      String.intercalate " "
        (motTySs.zip motiveNms |>.toList.map
          (fun p => s!"({p.2} : {p.1})"))
    -- the motive binders on the folds/theorems (`{P : Ty → Type} …`)
    let impMotBindersS : String :=
      String.intercalate " "
        (motTySs.zip motiveNms |>.toList.map
          (fun p => s!"\{{p.2} : {p.1}" ++ "}"))
    let algTyS : String :=
      s!"{algS} {String.intercalate sp (motiveNms.map (·.toString)).toList}"
    let sibAppSOf (j : Nat) : String :=
      s!"{sibNameS[j]!} {String.intercalate sp (idxNameSs[j]!).toList}"
    let motAppSOf (j : Nat) : String :=
      s!"{motiveNms[j]!} {String.intercalate sp (idxNameSs[j]!).toList}"
    let recAppS (mode : RecMode) (childSib : Nat) (childSlots : Array String)
        (argS : String) : String :=
      renderRecAppS isMutual sibs[0]!.idxTys.size foldNames fS "alg" mode
        childSib childSlots argS
    -- THE ALGEBRA RECORD: one field per (sibling, ctor), the rows
    -- riding the sibling's motive.
    let mut fieldLines : List String := []
    for j in [0:sibs.size] do
      for v in views[j]! do
        let binders : Array String ←
          (Array.range v.c.binders.size).mapM fun k => do
            let slotTy : Option String ←
              match v.c.recArgs.findIdx? (· == k) with
              | none => pure none
              | some m => do
                let mt := motiveNms[v.c.recSib[m]!]!.toString
                let sts := v.recSlotSs[m]!
                pure (s!"{mt} {String.intercalate sp (sts.toList.map parenSlotS)}")
            renderBinderS v.env slotTy v.c.binders[k]!
        let retT : String :=
          s!"{motiveNms[j]!} {String.intercalate sp (v.colsSpell.toList.map parenSlotS)}"
        let rowTy := renderArrowsS binders.toList retT
        let fid := v.c.field
        fieldLines := fieldLines ++ [s!"  {fid} : {rowTy}"]
    let recSrc : String :=
      "/-- GENERATED by `declare_dependent_fold` — the DEPENDENT algebra\n" ++
      "    record: ONE record for the whole (possibly mutual) sibling\n" ++
      "    block, one motive per sibling in block order, one field per\n" ++
      "    (sibling, ctor) — each row's result riding its index, a\n" ++
      "    recursive child's slot the child's motive at the child's\n" ++
      "    index. A new family ctor refuses to compile until every\n" ++
      "    algebra grows its row (15-patterns #15). -/\n" ++
      s!"structure {algS} {recMotParams} where\n" ++
      String.intercalate "\n" fieldLines ++ "\n"
    elabParsed ind recSrc
    -- THE FOLDS: one per sibling, the motive riding the index — as ONE
    -- `mutual` fold block for a block (the siblings' structural
    -- recursion is joint), one def for the singleton. The body is the
    -- EXPLICIT-MATCH form `fun <indices> x => match <indices>, x with`
    -- — structural on (index, value), so the equation lemmas close by
    -- `rfl` (kernel delta+beta+iota over concrete ctors).
    let mut foldParts : List String := []
    for j in [0:sibs.size] do
      -- the def's index binders: the head sibling's explicit, the
      -- co-siblings' implicit
      let idxBs : Array String :=
        (Array.range sibs[j]!.idxTys.size).map fun m =>
          if j == 0 then
            s!"({idxNameSs[j]![m]!} : {idxTySs[j]![m]!})"
          else
            s!"\{{idxNameSs[j]![m]!} : {idxTySs[j]![m]!}" ++ "}"
      let resTy := renderArrowsS idxBs.toList
        (s!"{sibAppSOf j} → {motAppSOf j}")
      let arms : Array String ←
        views[j]!.mapM fun v => do
          let rowFn := s!"{algS}.{v.c.field}"
          let rhs := renderRowRhsS v "alg" rowFn (recAppS .arm)
          let cols :
              Array String :=
            (if isMutual then v.colsWild else v.colsSpell) ++ #[v.ctorPat]
          pure (s!"  | {String.intercalate cm cols.toList} => {rhs}")
      let funBinds : String :=
        String.intercalate " "
          (((idxNameSs[j]!).toList.map (fun nm =>
            if j == 0 then nm else s!"\{{nm}" ++ "}")) ++ [xS])
      let defSrc : String :=
        "/-- GENERATED by `declare_dependent_fold` — THE FOLD: the\n" ++
        "    sibling's one walk (01 §1's initial-algebra face, the\n" ++
        "    motive riding the index, 06 §2; joint structural recursion\n" ++
        "    with the block's other siblings). Total, structural,\n" ++
        "    kernel-visible. -/\n" ++
        s!"def {foldNames[j]!} {impMotBindersS} (alg : {algTyS}) :\n" ++
        s!"    {resTy} :=\n" ++
        s!"  fun {funBinds} =>\n" ++
        s!"    match {String.intercalate cm ((idxNameSs[j]!).toList ++ [xS])} with\n" ++
        (String.intercalate "\n" arms.toList) ++ "\n"
      foldParts := foldParts ++ [defSrc]
    let foldSrc : String :=
      if isMutual then
        "mutual\n" ++ String.intercalate "" foldParts ++ "end"
      else
        String.intercalate "" foldParts
    elabParsed ind foldSrc
    -- THE EQUATION SET: all `rfl` (structural recursion = kernel
    -- reduction; 06 §5 — consumers prove against these).
    for j in [0:sibs.size] do
      for v in views[j]! do
        let eqName := s!"fold{sibs[j]!.base}_{baseNameOf v.c.name}"
        let binders : Array String ←
          (Array.range v.c.binders.size).mapM fun k =>
            renderBinderS v.env none v.c.binders[k]!
        let rowFn := s!"{algS}.{v.c.field}"
        let rhs := renderRowRhsS v "alg" rowFn (recAppS .eq)
        let lhs : String :=
          if j == 0 then
            s!"{foldNames[j]!} alg {String.intercalate sp ((v.colsSpell.toList.map parenSlotS) ++ [parenSlotS v.ctorPat])}"
          else
            s!"{foldNames[j]!} alg ({v.ctorPat} : {sibNameS[j]!} {String.intercalate sp (v.colsSpell.toList.map parenSlotS)})"
        let eqSrc : String :=
          "/-- GENERATED by `declare_dependent_fold` — one arm of the\n" ++
          "    equation set (06 §5): kernel reduction, cited by the\n" ++
          "    initiality law's template. -/\n" ++
          s!"theorem {eqName} {impMotBindersS} \{alg : {algTyS}" ++ "} " ++
          s!"{String.intercalate sp binders.toList} :\n" ++
          s!"    {lhs} = {rhs} := rfl\n"
        elabParsed ind eqSrc
    -- THE INITIALITY LAWS: per sibling, the recursor template — per
    -- ctor, `rw [h_<ctor>, ihs…, fold<Sib>_<ctor>]` (06 §10: the
    -- template, never grind). The co-siblings' motives are `True` —
    -- every hypothesis is stated with the FULL folds on the row's
    -- cross-sibling children, so no cross-sibling IH is ever needed.
    for j in [0:sibs.size] do
      let mut hypLines : List String := []
      let mut minors : Array String := #[]
      for m in [0:sibs.size] do
        for v in views[m]! do
          let eqName := s!"fold{sibs[m]!.base}_{baseNameOf v.c.name}"
          if m == j then
            -- the target sibling's minor: the commutation + the
            -- same-sibling IHs + the equation lemma
            let hypName := s!"h_{v.c.field}"
            let binders : Array String ←
              (Array.range v.c.binders.size).mapM fun k =>
                renderBinderS v.env none v.c.binders[k]!
            let rowFn := s!"{algS}.{v.c.field}"
            let rhs := renderRowRhsS v "alg" rowFn (recAppS (.hyp j))
            let lhs : String :=
              if m == 0 then
                s!"{fS} {String.intercalate sp ((v.colsSpell.toList.map parenSlotS) ++ [parenSlotS v.ctorPat])}"
              else
                s!"{fS} ({v.ctorPat} : {sibNameS[m]!} {String.intercalate sp (v.colsSpell.toList.map parenSlotS)})"
            let hypTy := renderArrowsS binders.toList (s!"{lhs} = {rhs}")
            hypLines := hypLines ++ [s!"  ({hypName} : {hypTy})"]
            -- the minor's binders: the ctor's binders (implicit ones
            -- BRACED — the recursor's minor telescope preserves the
            -- binder infos) + the recursive args' ihs (the
            -- same-sibling ones idented, the cross-sibling ones
            -- `True`-typed and unused)
            let ctorFbs : Array String ←
              (Array.range v.c.binders.size).mapM fun k =>
                renderBinderS v.env none v.c.binders[k]!
            let ihFbs : Array String :=
              (Array.range v.c.recArgs.size).map fun a =>
                if v.c.recSib[a]! == j then v.ihNames[a]!
                else "(_ : True)"
            let rwTerms : Array String :=
              #[hypName] ++
                ((Array.range v.c.recArgs.size).filterMap fun a =>
                  if v.c.recSib[a]! == j then some v.ihNames[a]! else none) ++
                #[eqName]
            let rwTac :=
              s!"by rw [{String.intercalate cm rwTerms.toList}]"
            -- a NULLARY ctor's minor has an EMPTY telescope — `fun =>`
            -- is not a term (the parser demands a binder or `|`); the
            -- minor is just the tactic
            minors := minors.push
              (if (ctorFbs ++ ihFbs).isEmpty then
                s!"({rwTac})"
              else
                s!"(fun {String.intercalate sp (ctorFbs ++ ihFbs).toList} => {rwTac})")
          else
            -- the co-sibling motive is `True`: the minor discards its
            -- whole telescope (one anonymous binder per ctor binder +
            -- one per recursive arg)
            let infos :=
              (v.c.binders.map (·.info))
                ++ (Array.range v.c.recArgs.size |>.map (fun _ => .default))
            minors := minors.push (renderAnonLambdasS infos "True.intro")
      -- the motive terms: the target sibling's equation, the others
      -- `True` — passed as the rec's NAMED motive arguments (one motive
      -- per block sibling; the single family's lone motive param is
      -- named `motive`, the mutual block's are `motive_1 … motive_n`)
      let mut motiveArgs : Array String := #[]
      for m in [0:sibs.size] do
        let idxNsM := idxNameSs[m]!
        let foldApp : String :=
          if m == 0 then
            s!"{foldNames[m]!} alg {String.intercalate sp idxNsM.toList} {xS}"
          else
            s!"{foldNames[m]!} alg {xS}"
        let mt : String :=
          if m == j then
            if m == 0 then
              s!"fun {String.intercalate sp idxNsM.toList} {xS} => {fS} {String.intercalate sp idxNsM.toList} {xS} = {foldApp}"
            else
              -- the co-sibling target's `f` carries its indices
              -- implicitly — tie them to the motive's binders (`@f`)
              s!"fun {String.intercalate sp idxNsM.toList} {xS} => @{fS} {String.intercalate sp idxNsM.toList} {xS} = {foldApp}"
          else
            let infos : Array BinderInfo :=
              (Array.range (idxNsM.size + 1)).map (fun _ => .default)
            renderAnonLambdasS infos "True"
        let mArgName : Name :=
          if isMutual then Name.mkSimple s!"motive_{m + 1}" else `motive
        motiveArgs := motiveArgs.push
          s!"({mArgName} := {mt})"
      -- the conclusion: the index binders ride implicitly, the value
      -- explicitly
      let conclBinders : Array String :=
        (Array.range sibs[j]!.idxTys.size).map fun m =>
          s!"\{{idxNameSs[j]![m]!} : {idxTySs[j]![m]!}" ++ "}"
      let xBinder := s!"({xS} : {sibAppSOf j})"
      let concl : String :=
        if j == 0 then
          s!"{fS} {String.intercalate sp (idxNameSs[j]!).toList} {xS} = {foldNames[j]!} alg {String.intercalate sp (idxNameSs[j]!).toList} {xS}"
        else
          s!"{fS} {xS} = {foldNames[j]!} alg {xS}"
      -- the initiality function's type (the head sibling's indices
      -- explicit — the entry point fold — the co-siblings' implicit)
      let fBs : Array String :=
        (Array.range sibs[j]!.idxTys.size).map fun m =>
          if j == 0 then
            s!"({idxNameSs[j]![m]!} : {idxTySs[j]![m]!})"
          else
            s!"\{{idxNameSs[j]![m]!} : {idxTySs[j]![m]!}" ++ "}"
      let fTy := renderArrowsS fBs.toList (s!"{sibAppSOf j} → {motAppSOf j}")
      let recId := s!"{sibNameS[j]!}.rec"
      let uniqName := s!"fold{sibs[j]!.base}_unique"
      let hypBlock : String :=
        if hypLines.isEmpty then ""
        else "\n" ++ String.intercalate "\n" hypLines
      let uniqSrc : String :=
        "/-- GENERATED by `declare_dependent_fold` — THE INITIALITY LAW: a\n" ++
        "    function that commutes with the algebra on the sibling's\n" ++
        "    every constructor IS the fold (one `Sib.rec` application\n" ++
        "    with the motive riding the index, the co-siblings' motives\n" ++
        "    `True` — the `foldValue` shape's law — cited by every\n" ++
        "    migrated consumer). -/\n" ++
        s!"theorem {uniqName} {impMotBindersS} \{alg : {algTyS}" ++ "}" ++
        s!" \{f : {fTy}" ++ "}" ++ hypBlock ++ "\n" ++
        s!"    {String.intercalate sp conclBinders.toList} {xBinder} :\n" ++
        s!"    {concl} :=\n" ++
        let minorsS : Array String := minors.map (fun m => "(" ++ m ++ ")")
        s!"  {recId} {String.intercalate sp motiveArgs.toList} " ++
        s!"{String.intercalate sp minorsS.toList} {xS}\n"
      elabParsed ind uniqSrc
  | _ => Elab.throwUnsupportedSyntax

end Kit.Derive.DepFold

end -- public meta section