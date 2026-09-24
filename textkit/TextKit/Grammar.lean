/-
# TextKit.Grammar — the typed bidirectional grammar value

The design of record: `notes/design-grammar-layer.md` (Phase 4's core).
ONE `Grammar α` value drives the derived parser + printer
(`TextKit/Grammar/Parse.lean`), the predictive-fragment certificate
(`TextKit/Grammar/Check.lean`), and the round-trip laws
(`TextKit/Grammar/Laws.lean`) — per-format work becomes rows.

MODULE FORM (the placement note): this is a NON-`module` file — the
`rel` node rides `Kit.Codec` (design §0.1: parse∘print needs
`decode (encode x) = some x`, Codec's law exactly; `Kit.Retraction` was
rejected — its `inv` is total but the real semantic mappings are
partial), and a `module` file cannot import the pre-`module` Kit files
(probe-verified). The textkit→kit direction is build-impossible for
`module` files; a NON-module file in textkit/ imports both TextKit's
modules and Kit's pre-module files, so the layer lives at
`TextKit/Grammar*.lean` in this form. Consequence: the umbrella
`TextKit.lean` (a `module` file) does not re-export it — consumers
`import TextKit.Grammar` directly.

THE RECURSION SCHEME (the senior reformulation — this wave's delta):
the previous shape put `self : Grammar R` in the ONE inductive and
carried a shape skeleton (`GSkel`) + the `SelfPath` relation + the
`SvCanonical` smart-constructor bookkeeping on `fix`. That shape was
PROOF-BLOCKED: the parse's `self` arm needs the enclosing `fix`'s
payload as an environment, and in the single-inductive shape the
environment's type is polymorphic in the walk's index (the seq case
recurses at a different payload type) — the equation compiler's
index-refinement wall, precisely. THE REFORMULATION (the previous
agent's "fix-body-as-function" suggestion, first-ordered): the body of
a `fix` lives in a SEPARATE OPEN FAMILY —

  `GrammarE R A` — grammars whose `selfE` refers to the enclosing
  fix's payload `R`, at EXACTLY that type (`selfE : GrammarE R R`).

`Grammar.fix (measure) (body : GrammarE R R) (decrease)` is the one
binder (design §1.2's dynamic scoping); there is no `self` node in
`Grammar` and no nested `fix` inside `GrammarE` (no migration target
nests — the leftover rule). The skeleton machinery DISSOLVES:
`SelfPathE` is declared directly over `GrammarE` (the family precedes
`Grammar`, so `fix`'s decrease field cites it with no knot-break), and
the fix-carried skeleton/`SvCanonical`/`fixS` are gone — the body IS
the body. The environment the parse needed is now the CLOSED term
`body : GrammarE R R` itself (the "fix-body-as-function",
defunctionalized): `selfE`'s parse arm re-enters `body` at one less
fuel — no polymorphic env anywhere.

The folds' `selfE` cases are the conservative constants
(`nullableE selfE := false`, `firstE selfE := none`, `guardE selfE
:= false`) plus the ONCE-UNFOLD parameters for the tail folds
(`tailFirstE`/`tailMunchE`/`tailOkE` take the enclosing body's value
as a parameter — design §2.1's "self unfolds the enclosing fix ONCE;
a second hit rejects", made a depth-1 parameter instead of a fuel).
The certificate's WF-FIX row (Check.lean) carries the real
guardedness discipline: `firstE body ≠ none`, `nullableE body =
false` (the rep-progress consumption lemma stands on it), and
`tailSelfFreeE body` (the body's tail positions are self-free — the
junction lemma's once-unfold corner; grammars needing deeper unfolds
are the design's flagged conservative corner).

The node set (design §0.2): `Grammar` has `atom seq alt rep opt label
rel fix` (8); the open family adds `selfE` — 9 node shapes total.
`Lexeme` keeps `scan_off` (the offset bookkeeping `print_parse`'s
second conjunct stands on).

Core-only (no mathlib/Batteries). The five questions (notes/v3/01-core.md):
- root: Universe — pure data over `List Char`/`String`/`Nat`.
- carrier grade: none of its own — `rel`/`relE` RIDE `Kit.Codec`
  (01 §4: the one semantic-mapping node; the grammar is the
  accepted-byte policy).
- spine reading: none — the value the parse/print/certificate/laws
  folds walk; it is read and emitted by its own layer.
- ladder rung: rung 1 — the folds are direct structural definitions;
  `AccD` is the Type-valued accessibility certificate the printer's
  measure recursion consumes.
- gate row: none yet — TextKit is outside Gates.Packages' gated set;
  TextKitTests pins the fixture grammar's round trips + the
  certificate's teeth (the sabotage negative controls).
-/

import TextKit.Error
import TextKit.Combinators
import Kit.Correspondence

namespace TextKit

/-! ## the head specs (the FIRST-set entries) -/

/-- A FIRST-set entry: a literal head or a char-class head. The
    disjointness discipline over these is the certificate's decidable
    fragment (design §2). -/
inductive HeadSpec where
  | lit (s : String)
  | cls (p : Char → Bool)

/-- Does a head spec match the text at this point? -/
def HeadSpec.matches : HeadSpec → List Char → Bool
  | .lit s, cs => s.toList.isPrefixOf cs
  | .cls p, cs => cs.head?.any p

/-! ## the well-founded certificate as data (the printer's engine) -/

/-- Type-valued accessibility: the printer's self-re-entry certificate.
    (Core's `Acc` is Prop-valued — no large elimination; this twin
    eliminates into `String`/`Bool`.) -/
inductive AccD (m : α → Nat) : α → Type where
  | intro (x : α) : (∀ y, m y < m x → AccD m y) → AccD m x

/-- The certificate from a fuel bound: `m x < fuel` gives `AccD m x`,
    by induction on the fuel. ALWAYS constructible with
    `fuel := m x + 1`. -/
def AccD.ofFuel (m : α → Nat) : (x : α) → (fuel : Nat) → m x < fuel → AccD m x
  | x, 0, h => absurd h (by omega)
  | x, fuel + 1, h =>
      .intro x fun y hy =>
        ofFuel m y fuel (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_succ h))

/-! ## the typed leaf (the lexeme) -/

/-- The typed leaf: a total scanner + its printer + the leaf laws.
    `munch` is the maximal-munch discipline as DATA: `some p` means the
    character AFTER the token must fail `p`. Every lexeme consumes
    ≥ 1 char on success and fails on a head mismatch — the two facts
    the generic exclusion lemma stands on (design §1.1). `scan_off` is
    the offset bookkeeping `print_parse`'s second conjunct stands on. -/
structure Lexeme (R : Type) where
  scan : GParser R
  print : R → String
  /-- The write-side gate (the nameOk discipline's home). -/
  pre : R → Bool
  head : HeadSpec
  munch : Option (Char → Bool)
  scan_post : ∀ cur r cur', scan cur = .ok (r, cur') → pre r = true
  scan_exact : ∀ cur r cur', scan cur = .ok (r, cur') →
    cur.cs = (print r).toList ++ cur'.cs
  scan_off : ∀ cur r cur', scan cur = .ok (r, cur') →
    cur'.off = cur.off + (print r).length
  scan_head : ∀ cur r cur', scan cur = .ok (r, cur') →
    head.matches cur.cs = true
  head_fail : ∀ cur, head.matches cur.cs = false →
    ∃ e, scan cur = .error e
  print_scan : ∀ k r sfx, pre r = true →
    (munch.all fun p => sfx.head?.all (fun c => !p c)) →
    scan ⟨k, (print r).toList ++ sfx⟩ = .ok (r, ⟨k + (print r).length, sfx⟩)
  consumes : ∀ cur r cur', scan cur = .ok (r, cur') →
    cur'.cs.length < cur.cs.length

/-! ## the open family (the fix body) + the self-value relation -/

/-- The OPEN grammar family: grammars whose `selfE` refers to the
    enclosing `fix`'s payload `R` — at exactly that type (the module
    header's reformulation note). One binder, no nesting (no
    `fixE`/`embedE` — the leftover rule: no migration target needs
    them). -/
inductive GrammarE (R : Type) : Type → Type 1 where
  | atomE : Lexeme A → GrammarE R A
  | seqE : GrammarE R A → GrammarE R B → GrammarE R (A × B)
  | altE : GrammarE R A → GrammarE R A → GrammarE R A
  | repE : GrammarE R A → GrammarE R (List A)
  | optE : GrammarE R A → GrammarE R (Option A)
  | labelE (name : String) : GrammarE R A → GrammarE R A
  | relE (m : Kit.Codec Raw A) (owns : A → Bool)
        (decode_owns : ∀ raw r, m.decode raw = Option.some r → owns r = true)
        (exact : ∀ raw r, m.decode raw = Option.some r → m.encode r = raw)
        (name : String) (valid : List String) :
        GrammarE R Raw → GrammarE R A
  | selfE : GrammarE R R

/-- The self-value relation: `SelfPathE g x y` reads "the `selfE` sites
    inside `g` receive `y` when it prints `x`" — the relational form of
    the design's `selfVals` fold. `altE` is the conservative union over
    both branches (the printer picks one; the relation over-approximates,
    which only WIDENS `fix`'s decrease obligation — sound). -/
inductive SelfPathE : {R A : Type} → GrammarE R A → A → R → Prop where
  | selfP {R : Type} (x : R) : SelfPathE .selfE x x
  | seqL {A B R : Type} {a : GrammarE R A} {b : GrammarE R B} {p : A} {q : B} {y : R} :
      SelfPathE a p y → SelfPathE (.seqE a b) (p, q) y
  | seqR {A B R : Type} {a : GrammarE R A} {b : GrammarE R B} {p : A} {q : B} {y : R} :
      SelfPathE b q y → SelfPathE (.seqE a b) (p, q) y
  | altL {R A : Type} {a b : GrammarE R A} {x : A} {y : R} :
      SelfPathE a x y → SelfPathE (.altE a b) x y
  | altR {R A : Type} {a b : GrammarE R A} {x : A} {y : R} :
      SelfPathE b x y → SelfPathE (.altE a b) x y
  | repP {R A : Type} {a : GrammarE R A} {xs : List A} {z : A} {y : R} :
      z ∈ xs → SelfPathE a z y → SelfPathE (.repE a) xs y
  | optP {R A : Type} {a : GrammarE R A} {z : A} {y : R} :
      SelfPathE a z y → SelfPathE (.optE a) (Option.some z) y
  | labelP {R A : Type} {n : String} {a : GrammarE R A} {x : A} {y : R} :
      SelfPathE a x y → SelfPathE (.labelE n a) x y
  | relP {Raw R A : Type} {m : Kit.Codec Raw A} {owns : A → Bool}
      {don : ∀ raw r, m.decode raw = Option.some r → owns r = true}
      {ex : ∀ raw r, m.decode raw = Option.some r → m.encode r = raw}
      {nm : String} {vld : List String} {sub : GrammarE R Raw} {x : A} {y : R} :
      SelfPathE sub (m.encode x) y → SelfPathE (.relE m owns don ex nm vld sub) x y

/-! ## the grammar (the closed value) -/

/-- The typed bidirectional grammar. Pure data at the nodes (no proof
    fields — the certificate is computed OVER the value) except `fix`'s
    payload measure + decrease proof, the honest payment for print
    totality (design §1.3). `alt` is SAME-PAYLOAD ordered choice; `rel`
    is the ONE semantic-mapping node; `fix`'s body is the open family's
    `selfE`-carrier (the module header's reformulation note). -/
inductive Grammar : Type → Type 1 where
  | atom : Lexeme R → Grammar R
  | seq : Grammar A → Grammar B → Grammar (A × B)
  | alt : Grammar R → Grammar R → Grammar R
  | rep : Grammar R → Grammar (List R)
  | opt : Grammar R → Grammar (Option R)
  | label (name : String) : Grammar R → Grammar R
  | rel (m : Kit.Codec Raw R) (owns : R → Bool)
        (decode_owns : ∀ raw r, m.decode raw = Option.some r → owns r = true)
        (exact : ∀ raw r, m.decode raw = Option.some r → m.encode r = raw)
        (name : String) (valid : List String) :
        Grammar Raw → Grammar R
  | fix (measure : R → Nat) (body : GrammarE R R) :
        (∀ x y, SelfPathE body x y → measure y < measure x) → Grammar R

/-! ## the computed folds (pure, total, over the grammar value) -/
-- The folds are match-definitions with POLYMORPHIC RECURSION (the seq
-- case recurses at a different payload index) — the equation compiler
-- handles this via the dependent motive (brecOn); the folds compile and
-- the equations are `rfl`.

/-- Can `g` match the empty text? `selfE := false` is sound because
    `selfE` is guarded (the certificate's WF-FIX row rejects unguarded
    recursion AND nullable bodies). -/
def GrammarE.nullableE : {R A : Type} → GrammarE R A → Bool :=
  fun {_ _} g => match g with
  | .atomE _ => false
  | .seqE a b => nullableE a && nullableE b
  | .altE a b => nullableE a || nullableE b
  | .repE _ => true
  | .optE _ => true
  | .labelE _ a => nullableE a
  | .relE _ _ _ _ _ _ sub => nullableE sub
  | .selfE => false

/-- The FIRST set; `none` = a `selfE` in FIRST position (the
    guardedness failure surface — WF-FIX rejects a body whose FIRST
    fails). -/
def GrammarE.firstE : {R A : Type} → GrammarE R A → Option (List HeadSpec) :=
  fun {_ _} g => match g with
  | .atomE L => Option.some [L.head]
  | .seqE a b =>
      match firstE a with
      | none => none
      | Option.some ha =>
          if nullableE a then
            match firstE b with
            | none => none
            | Option.some hb => Option.some (ha ++ hb)
          else Option.some ha
  | .altE a b =>
      match firstE a, firstE b with
      | Option.some ha, Option.some hb => Option.some (ha ++ hb)
      | _, _ => none
  | .repE a => firstE a
  | .optE a => firstE a
  | .labelE _ a => firstE a
  | .relE _ _ _ _ _ _ sub => firstE sub
  | .selfE => none

/-- The EFFECTIVE first set under the enclosing fix body: like
    `firstE` but `selfE` contributes the body's own firsts `fs` (the
    once-unfolding at `selfE`-led nodes). Every nonempty print of `g`
    starts with a head of `effFirstE fs g` (Laws.lean's
    `printHeadE`). -/
def GrammarE.effFirstE : {R A : Type} → (fs : List HeadSpec) → GrammarE R A → List HeadSpec :=
  fun {_ _} fs g => match g with
  | .atomE L => [L.head]
  | .seqE a b => effFirstE fs a ++ (if nullableE a then effFirstE fs b else [])
  | .altE a b => effFirstE fs a ++ effFirstE fs b
  | .repE a => effFirstE fs a
  | .optE a => effFirstE fs a
  | .labelE _ a => effFirstE fs a
  | .relE _ _ _ _ _ _ sub => effFirstE fs sub
  | .selfE => fs

/-- The guard fold: every `selfE` in `g` sits behind a guaranteed
    consumer on every print path. The fuel accounting of
    `parse_print`'s fix case stands on it; WF-FIX's `firstE body ≠
    none` implies it (Laws.lean's `firstE_some_guardE`). -/
def GrammarE.guardE : {R A : Type} → GrammarE R A → Bool :=
  fun {_ _} g => match g with
  | .atomE _ => true
  | .seqE a b => guardE a && (if nullableE a then guardE b else true)
  | .altE a b => guardE a && guardE b
  | .repE a => guardE a
  | .optE a => guardE a
  | .labelE _ a => guardE a
  | .relE _ _ _ _ _ _ sub => guardE sub
  | .selfE => false

/-- The tail-self-freedom fold: no `selfE` in a TAIL position of `g`
    (the positions the tail folds consult: seq rights, seq lefts of
    nullable rights, alt branches, rep/opt bodies, label/rel bodies).
    WF-FIX requires it of the body — the junction lemma's once-unfold
    corner (the module header's scheme note). -/
def GrammarE.tailSelfFreeE : {R A : Type} → GrammarE R A → Bool :=
  fun {_ _} g => match g with
  | .atomE _ => true
  | .seqE a b => tailSelfFreeE b && (if nullableE b then tailSelfFreeE a else true)
  | .altE a b => tailSelfFreeE a && tailSelfFreeE b
  | .repE a => tailSelfFreeE a
  | .optE a => tailSelfFreeE a
  | .labelE _ a => tailSelfFreeE a
  | .relE _ _ _ _ _ _ sub => tailSelfFreeE sub
  | .selfE => false

/-- The munch predicates exposed at the grammar's tail. `selfE` takes
    the enclosing body's value `tm` (the once-unfolding — with
    tail-self-free bodies the parameter is only consulted through the
    body's own first unfold). `seqE` takes the right's tail, falling
    back to the left's when the right is nullable; `altE` unions
    (through `none`). -/
def GrammarE.tailMunchE : {R A : Type} → (tm : Option (List (Char → Bool))) →
    GrammarE R A → Option (List (Char → Bool)) :=
  fun {_ _} tm g => match g with
    | .atomE L => Option.some (L.munch.toList)
    | .seqE a b =>
        match tailMunchE tm b with
        | none => none
        | Option.some hb =>
            if nullableE b then
              match tailMunchE tm a with
              | none => none
              | Option.some ha => Option.some (ha ++ hb)
            else Option.some hb
    | .altE a b =>
        match tailMunchE tm a, tailMunchE tm b with
        | Option.some ha, Option.some hb => Option.some (ha ++ hb)
        | _, _ => none
    | .repE a => tailMunchE tm a
    | .optE a => tailMunchE tm a
    | .labelE _ a => tailMunchE tm a
    | .relE _ _ _ _ _ _ sub => tailMunchE tm sub
    | .selfE => tm

/-- The FIRST heads of `g`'s nullable-tail STOP positions (the
    positions where an `optE`/`repE` decides to stop and the
    continuation begins — plus, at an `altE` whose right branch is
    nullable, the LEFT branch's firsts: a right-branch empty print
    means the continuation's text is offered to the left branch's
    exclusion, the alt law's branch-selection content). The
    certificate's WF-SEQ/WF-REP rows quantify these against the
    continuation's effective firsts. `selfE` takes the enclosing
    body's tail-firsts `tf` (the once-unfolding); the rep/opt stop
    positions contribute the body's EFFECTIVE firsts `fs`. -/
def GrammarE.tailFirstE : {R A : Type} → (fs tf : List HeadSpec) → GrammarE R A → List HeadSpec :=
  fun {_ _} fs tf g => match g with
  | .atomE _ => []
  | .seqE a b => tailFirstE fs tf b ++ (if nullableE b then tailFirstE fs tf a else [])
  | .altE a b =>
      tailFirstE fs tf a ++ tailFirstE fs tf b ++
        (if nullableE b then effFirstE fs a else [])
  | .repE a => effFirstE fs a ++ tailFirstE fs tf a
  | .optE a => effFirstE fs a ++ tailFirstE fs tf a
  | .labelE _ a => tailFirstE fs tf a
  | .relE _ _ _ _ _ _ sub => tailFirstE fs tf sub
  | .selfE => tf

/-- The membership-threaded `all` (the path-carrying folds' rep
    engine: each element's check sees its membership proof). -/
def GrammarE.allWalk {A : Type} : (xs : List A) → ((z : A) → z ∈ xs → Bool) → Bool
  | [], _ => true
  | z :: zs, f => f z (List.Mem.head zs) && allWalk zs (fun w hw => f w (List.Mem.tail z hw))

@[simp] theorem GrammarE.allWalk_nil {A : Type} (f : (z : A) → z ∈ ([] : List A) → Bool) :
    allWalk [] f = true := rfl

@[simp] theorem GrammarE.allWalk_cons {A : Type} (z : A) (zs : List A)
    (f : (w : A) → w ∈ z :: zs → Bool) :
    allWalk (z :: zs) f =
      (f z (List.Mem.head zs) && allWalk zs (fun w hw => f w (List.Mem.tail z hw))) := rfl

/-- allWalk respects pointwise-equal checks. -/
theorem GrammarE.allWalk_congr {A : Type} : (xs : List A) →
    (f g : (z : A) → z ∈ xs → Bool) →
    (∀ z hz, f z hz = g z hz) → allWalk xs f = allWalk xs g
  | [], _, _, _ => rfl
  | z :: zs, f, g, h => by
      rw [allWalk_cons, allWalk_cons, h z (List.Mem.head zs),
        allWalk_congr zs _ _ (fun w hw => h w (List.Mem.tail z hw))]

/-- allWalk's truth, pointwise. -/
theorem GrammarE.allWalk_true {A : Type} : (xs : List A) → (f : (z : A) → z ∈ xs → Bool) →
    allWalk xs f = true → ∀ z (hz : z ∈ xs), f z hz = true
  | [], _, _, _, hz => nomatch hz
  | z :: zs, f, h, w, hw => by
      rw [allWalk_cons] at h
      simp only [Bool.and_eq_true] at h
      cases hw with
      | head => exact h.1
      | tail _ hw' => exact allWalk_true zs _ h.2 w hw'

/-- The value-side precondition fold for the open family (the nameOk
    discipline, generic): `atomE := lex.pre`; `seqE := both`; `altE :=
    either` (this is also the printer's branch discriminator); `optE
    none := true`; `repE := allWalk`; `relE := owns x && walk sub
    (encode x)`; `labelE` passes through; `selfE` defers to the
    handler `H` — called with the path witnessing the self-value
    (the printer's certificate threading and `fixValueOk`'s closure
    both stand on the path). -/
def GrammarE.valueOkWalk : {R A : Type} → (g : GrammarE R A) → (x : A) →
    ((y : R) → SelfPathE g x y → Bool) → Bool :=
  fun {_ _} g x H => match g, x, H with
  | .atomE L, x, _ => L.pre x
  | .seqE a b, (p, q), H =>
      valueOkWalk a p (fun y path => H y (.seqL path)) &&
      valueOkWalk b q (fun y path => H y (.seqR path))
  | .altE a b, x, H =>
      valueOkWalk a x (fun y path => H y (.altL path)) ||
      valueOkWalk b x (fun y path => H y (.altR path))
  | .repE a, xs, H =>
      allWalk xs (fun z hz => valueOkWalk a z (fun y path => H y (.repP hz path)))
  | .optE a, x, H =>
      match x with
      | Option.some z => valueOkWalk a z (fun y path => H y (.optP path))
      | Option.none => true
  | .labelE _ a, x, H => valueOkWalk a x (fun y path => H y (.labelP path))
  | .relE m owns _ _ _ _ sub, x, H =>
      owns x && valueOkWalk sub (m.encode x) (fun y path => H y (.relP path))
  | .selfE, x, H => H x (.selfP x)

/-! valueOkWalk's per-node equations (iota; the congruence lemma's
    rewrite surface) -/
theorem GrammarE.valueOkWalk_seqE (a : GrammarE R A) (b : GrammarE R B)
    (p : A) (q : B) (H) :
    valueOkWalk (.seqE a b) (p, q) H =
      (valueOkWalk a p (fun y path => H y (.seqL path)) &&
       valueOkWalk b q (fun y path => H y (.seqR path))) := rfl

theorem GrammarE.valueOkWalk_altE (a b : GrammarE R A) (x : A) (H) :
    valueOkWalk (.altE a b) x H =
      (valueOkWalk a x (fun y path => H y (.altL path)) ||
       valueOkWalk b x (fun y path => H y (.altR path))) := rfl

theorem GrammarE.valueOkWalk_repE (a : GrammarE R A) (xs : List A) (H) :
    valueOkWalk (.repE a) xs H =
      allWalk xs (fun z hz => valueOkWalk a z (fun y path => H y (.repP hz path))) := rfl

theorem GrammarE.valueOkWalk_optE_some (a : GrammarE R A) (z : A) (H) :
    valueOkWalk (.optE a) (Option.some z) H =
      valueOkWalk a z (fun y path => H y (.optP path)) := rfl

theorem GrammarE.valueOkWalk_optE_none (a : GrammarE R A) (H) :
    valueOkWalk (.optE a) Option.none H = true := rfl

theorem GrammarE.valueOkWalk_labelE (n : String) (a : GrammarE R A) (x : A) (H) :
    valueOkWalk (.labelE n a) x H =
      valueOkWalk a x (fun y path => H y (.labelP path)) := rfl

theorem GrammarE.valueOkWalk_relE (m : Kit.Codec Raw A) (owns : A → Bool)
    (don : ∀ raw r, m.decode raw = Option.some r → owns r = true)
    (ex : ∀ raw r, m.decode raw = Option.some r → m.encode r = raw)
    (nm : String) (vld : List String) (sub : GrammarE R Raw) (x : A) (H) :
    valueOkWalk (.relE m owns don ex nm vld sub) x H =
      (owns x && valueOkWalk sub (m.encode x) (fun y path => H y (.relP path))) := rfl

/-- valueOkWalk respects pointwise-equal handlers. -/
theorem GrammarE.valueOkWalk_congr {R : Type} : {A : Type} → (g : GrammarE R A) → (x : A) →
    (H₁ H₂ : (y : R) → SelfPathE g x y → Bool) →
    (∀ y path, H₁ y path = H₂ y path) → valueOkWalk g x H₁ = valueOkWalk g x H₂ := by
  intro A g
  induction g with
  | atomE L => intro x H₁ H₂ h; rfl
  | seqE a b iha ihb =>
      intro x H₁ H₂ h
      obtain ⟨p, q⟩ := x
      rw [valueOkWalk_seqE a b p q H₁, valueOkWalk_seqE a b p q H₂,
        iha p _ _ (fun y path => h y (.seqL path)),
        ihb q _ _ (fun y path => h y (.seqR path))]
  | altE a b iha ihb =>
      intro x H₁ H₂ h
      rw [valueOkWalk_altE a b x H₁, valueOkWalk_altE a b x H₂,
        iha x _ _ (fun y path => h y (.altL path)),
        ihb x _ _ (fun y path => h y (.altR path))]
  | repE a iha =>
      intro xs H₁ H₂ h
      rw [valueOkWalk_repE a xs H₁, valueOkWalk_repE a xs H₂]
      exact allWalk_congr xs _ _ (fun z hz => iha z _ _ (fun y path => h y (.repP hz path)))
  | optE a iha =>
      intro x H₁ H₂ h
      cases x with
      | none => rfl
      | some z =>
          rw [valueOkWalk_optE_some a z H₁, valueOkWalk_optE_some a z H₂]
          exact iha z _ _ (fun y path => h y (.optP path))
  | labelE n a iha =>
      intro x H₁ H₂ h
      rw [valueOkWalk_labelE n a x H₁, valueOkWalk_labelE n a x H₂]
      exact iha x _ _ (fun y path => h y (.labelP path))
  | relE m owns don ex nm vld sub ih =>
      intro x H₁ H₂ h
      rw [valueOkWalk_relE m owns don ex nm vld sub x H₁,
        valueOkWalk_relE m owns don ex nm vld sub x H₂,
        ih (m.encode x) _ _ (fun y path => h y (.relP path))]
  | selfE => intro x H₁ H₂ h; exact h x (.selfP x)

/-- The fix-payload value discipline, ONE step of the AccD recursion:
    the body's walk with the closure at the self-values. -/
def Grammar.fixValueOkGo (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) :
    (x : R) → AccD m x → Bool
  | x, .intro _ h =>
      GrammarE.valueOkWalk sb x (fun y path => fixValueOkGo m sb dec y (h y (dec x y path)))

/-- The certificate is irrelevant: the fold's value does not depend on
    the AccD derivation. -/
theorem Grammar.fixValueOkGo_irrel (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) :
    (x : R) → (acc : AccD m x) → ∀ acc', fixValueOkGo m sb dec x acc = fixValueOkGo m sb dec x acc' := by
  intro x acc
  induction acc using AccD.rec with
  | intro x h ih =>
      intro acc'
      cases acc' with
      | intro _ h' =>
          show GrammarE.valueOkWalk sb x
                (fun y path => fixValueOkGo m sb dec y (h y (dec x y path))) =
               GrammarE.valueOkWalk sb x
                (fun y path => fixValueOkGo m sb dec y (h' y (dec x y path)))
          exact GrammarE.valueOkWalk_congr sb x _ _
            (fun y path => ih y (dec x y path) (h' y (dec x y path)))

/-- The value-side closure at a fix payload: the body's walk with the
    closure at every self-value (the design's env fold, made total by
    the carried measure — `selfE`'s "true" is the honest reading ONLY
    under this closure: every self-descendant satisfies the body
    discipline). -/
def Grammar.fixValueOk (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) (x : R) : Bool :=
  fixValueOkGo m sb dec x (AccD.ofFuel m x (m x + 1) (Nat.lt_succ_self _))

/-- The one-step unfold of the closure (the laws' fix-case entry). -/
theorem Grammar.fixValueOk_unfold (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) (x : R) :
    fixValueOk m sb dec x =
      GrammarE.valueOkWalk sb x (fun y _ => fixValueOk m sb dec y) := by
  show fixValueOkGo m sb dec x (AccD.ofFuel m x (m x + 1) _) = _
  have h1 : AccD.ofFuel m x (m x + 1) (Nat.lt_succ_self _) =
      AccD.intro x (fun y hy => AccD.ofFuel m y (m x)
        (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_succ (Nat.lt_succ_self _)))) := rfl
  rw [h1]
  show GrammarE.valueOkWalk sb x (fun y path =>
        fixValueOkGo m sb dec y (AccD.ofFuel m y (m x) _)) = _
  exact GrammarE.valueOkWalk_congr sb x _ _
    (fun y _ => fixValueOkGo_irrel m sb dec y _ _)

/-- The value-side precondition fold (the nameOk discipline, generic):
    the fix arm is the closure (`fixValueOk`). -/
def Grammar.valueOk : {A : Type} → Grammar A → A → Bool :=
  fun {A} g x => match g, x with
  | .atom L, x => L.pre x
  | .seq a b, (x, y) => valueOk a x && valueOk b y
  | .alt a b, x => valueOk a x || valueOk b x
  | .rep a, xs => xs.all (fun z => valueOk a z)
  | .opt a, x => match x with | Option.some y => valueOk a y | none => true
  | .label _ a, x => valueOk a x
  | .rel m owns _ _ _ _ sub, x => owns x && valueOk sub (m.encode x)
  | .fix m sb dec, x => fixValueOk m sb dec x

/-! ## the tail-adequacy fold (law 1's suffix condition, design §3.2) -/

/-- `tailOkE m sb dec fs tok g x sfx`: the suffix `sfx` is a safe
    FOLLOW for printing the VALUE `x` through `g` — every tail munch
    broken, every tail stop-position's effective firsts failing on
    `sfx`. VALUE-DEPENDENT (the wave's honest delta from design §3.2's
    value-free sketch): at `altE` only the PRINTED branch's tail
    condition holds of the value — the unprinted branch's internal
    junction facts route through value-dependent print-head lemmas and
    are not establishable from the certificate's rows — so the fold
    follows the printer's discriminator (the SAME `fixValueOk` closure
    the printer consults — branch agreement by construction). The
    `optE none` case carries the stop-exactness heads-fail; the `some`
    case is the body's own adequacy (the certificate's WF-OPT row
    supplies the body's non-nullability for the none-case exclusion).
    `selfE` defers to `tok` (the enclosing body's tail-adequacy at the
    self-value, the once-unfolding). -/
def GrammarE.tailOkE {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x)
    (fs : List HeadSpec) (tok : (y : R) → List Char → Bool) :
    {A : Type} → (g : GrammarE R A) → A → List Char → Bool :=
  fun {_} g x sfx => match g, x, sfx with
  | .atomE L, _, sfx => L.munch.all (fun p => sfx.head?.all (fun c => !p c))
  | .seqE a b, (p, q), sfx =>
      tailOkE m sb dec fs tok b q sfx &&
        (if nullableE b then tailOkE m sb dec fs tok a p sfx else true)
  | .altE a b, x, sfx =>
      if valueOkWalk a x (fun y _ => Grammar.fixValueOk m sb dec y)
      then tailOkE m sb dec fs tok a x sfx
      else tailOkE m sb dec fs tok b x sfx &&
        (if nullableE b then (effFirstE fs a).all (fun h => !h.matches sfx) else true)
  | .repE a, xs, sfx =>
      ((effFirstE fs a).all (fun h => !h.matches sfx)) &&
        xs.all (fun z => tailOkE m sb dec fs tok a z sfx)
  | .optE a, x, sfx =>
      match x with
      | Option.some z => tailOkE m sb dec fs tok a z sfx
      | Option.none => (effFirstE fs a).all (fun h => !h.matches sfx)
  | .labelE _ a, x, sfx => tailOkE m sb dec fs tok a x sfx
  | .relE mm _ _ _ _ _ sub, x, sfx => tailOkE m sb dec fs tok sub (mm.encode x) sfx
  | .selfE, x, sfx => tok x sfx

/-! ## the closed-level folds (delegating at `fix`) -/

/-- Can `g` match the empty text? The fix arm delegates to the body. -/
def Grammar.nullable : {A : Type} → Grammar A → Bool :=
  fun {_} g => match g with
  | .atom _ => false
  | .seq a b => nullable a && nullable b
  | .alt a b => nullable a || nullable b
  | .rep _ => true
  | .opt _ => true
  | .label _ a => nullable a
  | .rel _ _ _ _ _ _ sub => nullable sub
  | .fix _ body _ => GrammarE.nullableE body

/-- The FIRST set; the fix arm delegates (`none` = the guardedness
    failure surface). -/
def Grammar.first : {A : Type} → Grammar A → Option (List HeadSpec) :=
  fun {_} g => match g with
  | .atom L => Option.some [L.head]
  | .seq a b =>
      match first a with
      | none => none
      | Option.some ha =>
          if nullable a then
            match first b with
            | none => none
            | Option.some hb => Option.some (ha ++ hb)
          else Option.some ha
  | .alt a b =>
      match first a, first b with
      | Option.some ha, Option.some hb => Option.some (ha ++ hb)
      | _, _ => none
  | .rep a => first a
  | .opt a => first a
  | .label _ a => first a
  | .rel _ _ _ _ _ _ sub => first sub
  | .fix _ body _ => GrammarE.firstE body

/-- The effective firsts (no `selfE` at this level except under `fix`,
    which unfolds once). -/
def Grammar.effFirst : {A : Type} → Grammar A → List HeadSpec :=
  fun {_} g => match g with
  | .atom L => [L.head]
  | .seq a b => effFirst a ++ (if nullable a then effFirst b else [])
  | .alt a b => effFirst a ++ effFirst b
  | .rep a => effFirst a
  | .opt a => effFirst a
  | .label _ a => effFirst a
  | .rel _ _ _ _ _ _ sub => effFirst sub
  | .fix _ body _ => GrammarE.effFirstE ((GrammarE.firstE body).getD []) body

/-- The guard fold (every self behind a guaranteed consumer); the fix
    arm delegates. -/
def Grammar.guard : {A : Type} → Grammar A → Bool :=
  fun {_} g => match g with
  | .atom _ => true
  | .seq a b => guard a && (if nullable a then guard b else true)
  | .alt a b => guard a && guard b
  | .rep a => guard a
  | .opt a => guard a
  | .label _ a => guard a
  | .rel _ _ _ _ _ _ sub => guard sub
  | .fix _ body _ => GrammarE.guardE body

/-- The tail munch; the fix arm is the body's once-unfolded value. -/
def Grammar.tailMunch : {A : Type} → Grammar A → Option (List (Char → Bool)) :=
  fun {_} g => match g with
    | .atom L => Option.some (L.munch.toList)
    | .seq a b =>
        match tailMunch b with
        | none => none
        | Option.some hb =>
            if nullable b then
              match tailMunch a with
              | none => none
              | Option.some ha => Option.some (ha ++ hb)
            else Option.some hb
    | .alt a b =>
        match tailMunch a, tailMunch b with
        | Option.some ha, Option.some hb => Option.some (ha ++ hb)
        | _, _ => none
    | .rep a => tailMunch a
    | .opt a => tailMunch a
    | .label _ a => tailMunch a
    | .rel _ _ _ _ _ _ sub => tailMunch sub
    | .fix _ body _ =>
        GrammarE.tailMunchE (GrammarE.tailMunchE Option.none body) body

/-- The nullable-tail stop positions' firsts; the fix arm is the body's
    once-unfolded value. -/
def Grammar.tailFirst : {A : Type} → Grammar A → List HeadSpec :=
  fun {_} g => match g with
  | .atom _ => []
  | .seq a b => tailFirst b ++ (if nullable b then tailFirst a else [])
  | .alt a b => tailFirst a ++ tailFirst b ++ (if nullable b then effFirst a else [])
  | .rep a => effFirst a ++ tailFirst a
  | .opt a => effFirst a ++ tailFirst a
  | .label _ a => tailFirst a
  | .rel _ _ _ _ _ _ sub => tailFirst sub
  | .fix _ body _ =>
      GrammarE.tailFirstE ((GrammarE.firstE body).getD [])
        (GrammarE.tailFirstE ((GrammarE.firstE body).getD []) [] body) body

/-- The tail-adequacy fold (law 1's suffix condition),
    VALUE-DEPENDENT (the alt clause follows the printer's branch —
    `GrammarE.tailOkE`'s docstring); the fix arm is the body's
    once-unfolded value. -/
def Grammar.tailOk : {A : Type} → (g : Grammar A) → A → List Char → Bool :=
  fun {_} g x sfx => match g, x, sfx with
  | .atom L, _, sfx => L.munch.all (fun p => sfx.head?.all (fun c => !p c))
  | .seq a b, (p, q), sfx =>
      tailOk b q sfx && (if nullable b then tailOk a p sfx else true)
  | .alt a b, x, sfx =>
      if valueOk a x then tailOk a x sfx
      else tailOk b x sfx &&
        (if nullable b then (effFirst a).all (fun h => !h.matches sfx) else true)
  | .rep a, xs, sfx =>
      ((effFirst a).all (fun h => !h.matches sfx)) &&
        xs.all (fun z => tailOk a z sfx)
  | .opt a, x, sfx =>
      match x with
      | Option.some z => tailOk a z sfx
      | Option.none => (effFirst a).all (fun h => !h.matches sfx)
  | .label _ a, x, sfx => tailOk a x sfx
  | .rel mm _ _ _ _ _ sub, x, sfx => tailOk sub (mm.encode x) sfx
  | .fix m body dec, x, sfx =>
      GrammarE.tailOkE m body dec ((GrammarE.firstE body).getD [])
        (fun y sfx' => GrammarE.tailOkE m body dec ((GrammarE.firstE body).getD [])
          (fun _ _ => false) body y sfx')
        body x sfx

/-! tailOkE's per-node equations (iota; the folds' rewrite surface) -/
theorem GrammarE.tailOkE_atomE {R : Type} (m : R → Nat) (sb : GrammarE R R) dec fs tok
    (L : Lexeme A) (x : A) (sfx : List Char) :
    tailOkE m sb dec fs tok (.atomE L) x sfx =
      L.munch.all (fun p => sfx.head?.all (fun c => !p c)) := rfl

theorem GrammarE.tailOkE_seqE {R : Type} (m : R → Nat) (sb : GrammarE R R) dec fs tok
    (a : GrammarE R A) (b : GrammarE R B) (p : A) (q : B) (sfx : List Char) :
    tailOkE m sb dec fs tok (.seqE a b) (p, q) sfx =
      (tailOkE m sb dec fs tok b q sfx &&
        (if nullableE b then tailOkE m sb dec fs tok a p sfx else true)) := rfl

theorem GrammarE.tailOkE_altE {R : Type} (m : R → Nat) (sb : GrammarE R R) dec fs tok
    (a b : GrammarE R A) (x : A) (sfx : List Char) :
    tailOkE m sb dec fs tok (.altE a b) x sfx =
      (if valueOkWalk a x (fun y _ => Grammar.fixValueOk m sb dec y)
       then tailOkE m sb dec fs tok a x sfx
       else tailOkE m sb dec fs tok b x sfx &&
         (if nullableE b then (effFirstE fs a).all (fun h => !h.matches sfx) else true)) := rfl

theorem GrammarE.tailOkE_repE {R : Type} (m : R → Nat) (sb : GrammarE R R) dec fs tok
    (a : GrammarE R A) (xs : List A) (sfx : List Char) :
    tailOkE m sb dec fs tok (.repE a) xs sfx =
      (((effFirstE fs a).all (fun h => !h.matches sfx)) &&
        xs.all (fun z => tailOkE m sb dec fs tok a z sfx)) := rfl

theorem GrammarE.tailOkE_optE_some {R : Type} (m : R → Nat) (sb : GrammarE R R) dec fs tok
    (a : GrammarE R A) (z : A) (sfx : List Char) :
    tailOkE m sb dec fs tok (.optE a) (Option.some z) sfx =
      tailOkE m sb dec fs tok a z sfx := rfl

theorem GrammarE.tailOkE_optE_none {R : Type} (m : R → Nat) (sb : GrammarE R R) dec fs tok
    (a : GrammarE R A) (sfx : List Char) :
    tailOkE m sb dec fs tok (.optE a) Option.none sfx =
      (effFirstE fs a).all (fun h => !h.matches sfx) := rfl

theorem GrammarE.tailOkE_selfE {R : Type} (m : R → Nat) (sb : GrammarE R R) dec fs tok
    (x : R) (sfx : List Char) :
    tailOkE m sb dec fs tok (.selfE) x sfx = tok x sfx := rfl

/-- The tok parameter is irrelevant on tail-self-free grammars (the
    once-unfold corner's consistency bridge — the laws' selfE case). -/
theorem GrammarE.tailOkE_tok_irrel {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) (fs : List HeadSpec) :
    {A : Type} → (g : GrammarE R A) → tailSelfFreeE g = true →
    ∀ (tok₁ tok₂ : (y : R) → List Char → Bool) (x : A) (sfx : List Char),
      tailOkE m sb dec fs tok₁ g x sfx = tailOkE m sb dec fs tok₂ g x sfx := by
  intro A g
  induction g with
  | atomE L => intro _ tok₁ tok₂ x sfx; rfl
  | seqE a b iha ihb =>
      intro htsf tok₁ tok₂ x sfx
      obtain ⟨p, q⟩ := x
      simp only [tailSelfFreeE, Bool.and_eq_true] at htsf
      rw [tailOkE_seqE, tailOkE_seqE, ihb htsf.1 tok₁ tok₂ q sfx]
      cases hb : nullableE b with
      | false => rfl
      | true =>
          simp only [hb, if_true] at htsf ⊢
          rw [iha htsf.2 tok₁ tok₂ p sfx]
  | altE a b iha ihb =>
      intro htsf tok₁ tok₂ x sfx
      simp only [tailSelfFreeE, Bool.and_eq_true] at htsf
      rw [tailOkE_altE, tailOkE_altE]
      split
      · exact iha htsf.1 tok₁ tok₂ x sfx
      · rw [ihb htsf.2 tok₁ tok₂ x sfx]
  | repE a iha =>
      intro htsf tok₁ tok₂ xs sfx
      simp only [tailSelfFreeE] at htsf
      rw [tailOkE_repE, tailOkE_repE]
      have hcong : xs.all (fun z => tailOkE m sb dec fs tok₁ a z sfx) =
          xs.all (fun z => tailOkE m sb dec fs tok₂ a z sfx) := by
        induction xs with
        | nil => rfl
        | cons z zs ih =>
            simp only [List.all_cons]
            rw [iha htsf tok₁ tok₂ z sfx, ih]
      rw [hcong]
  | optE a iha =>
      intro htsf tok₁ tok₂ x sfx
      simp only [tailSelfFreeE] at htsf
      cases x with
      | none => rfl
      | some z =>
          rw [tailOkE_optE_some, tailOkE_optE_some]
          exact iha htsf tok₁ tok₂ z sfx
  | labelE n a iha => intro htsf tok₁ tok₂ x sfx; exact iha htsf tok₁ tok₂ x sfx
  | relE mm owns don ex nm vld sub ih =>
      intro htsf tok₁ tok₂ x sfx
      simp only [tailSelfFreeE] at htsf
      exact ih htsf tok₁ tok₂ (mm.encode x) sfx
  | selfE => intro htsf; simp [tailSelfFreeE] at htsf

/-! ## the simp equations the proofs consume -/

@[simp] theorem GrammarE.nullableE_atomE (L : Lexeme A) :
    (GrammarE.atomE L : GrammarE R A).nullableE = false := rfl
@[simp] theorem GrammarE.nullableE_selfE :
    (GrammarE.selfE : GrammarE R R).nullableE = false := rfl
@[simp] theorem GrammarE.firstE_atomE (L : Lexeme A) :
    (GrammarE.atomE L : GrammarE R A).firstE = Option.some [L.head] := rfl
@[simp] theorem GrammarE.firstE_selfE :
    (GrammarE.selfE : GrammarE R R).firstE = none := rfl
@[simp] theorem GrammarE.guardE_selfE :
    (GrammarE.selfE : GrammarE R R).guardE = false := rfl
@[simp] theorem GrammarE.guardE_atomE (L : Lexeme A) :
    (GrammarE.atomE L : GrammarE R A).guardE = true := rfl
@[simp] theorem GrammarE.valueOkWalk_atomE (L : Lexeme A) (x : A) (H) :
    (GrammarE.atomE L : GrammarE R A).valueOkWalk x H = L.pre x := rfl
@[simp] theorem GrammarE.valueOkWalk_selfE (x : R) (H) :
    (GrammarE.selfE : GrammarE R R).valueOkWalk x H = H x (.selfP x) := rfl

@[simp] theorem Grammar.nullable_atom (L : Lexeme R) : (Grammar.atom L).nullable = false := rfl
@[simp] theorem Grammar.nullable_fix (m : R → Nat) (body : GrammarE R R)
    (dec : ∀ x y, SelfPathE body x y → m y < m x) :
    (Grammar.fix m body dec).nullable = body.nullableE := rfl
@[simp] theorem Grammar.first_fix (m : R → Nat) (body : GrammarE R R)
    (dec : ∀ x y, SelfPathE body x y → m y < m x) :
    (Grammar.fix m body dec).first = body.firstE := rfl
@[simp] theorem Grammar.valueOk_atom (L : Lexeme R) (x : R) :
    (Grammar.atom L).valueOk x = L.pre x := rfl
@[simp] theorem Grammar.valueOk_fix (m : R → Nat) (body : GrammarE R R)
    (dec : ∀ x y, SelfPathE body x y → m y < m x) (x : R) :
    (Grammar.fix m body dec).valueOk x = Grammar.fixValueOk m body dec x := rfl

end TextKit
