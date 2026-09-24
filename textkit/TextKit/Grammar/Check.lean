/-
# TextKit.Grammar.Check — the predictive-fragment certificate

Design §2: a semantic Prop (`Predictive`/`PredictiveE`), a Bool
checker (`wfCheck`/`wfCheckE`) with the failure-facing twin
(`wfDiagnose` — one Diag per failed row, NAMING the row), and the
PROVED soundness bridge. Completeness stays LOUDLY absent (the cls/cls
conservatism, the once-unfold tail corners, WF-ALT-2 — grammars
outside the decidable fragment hand-prove `Predictive` directly and
cite the same laws).

THE ROWS (design §2.2, this wave's completion — the previous wave
landed only the alt/rep/fix skeleton): at every `seq a b`, WF-SEQ-1
(every nullable-tail stop head of `a` disjoint from every effective
first of `b`) and WF-SEQ-2 (every tail munch of `a` broken by every
effective first of `b`); at every `rep a`, WF-REP-1 (progress:
`nullable a = false`) and WF-REP-2 (the iteration self-junction:
WF-SEQ-1/WF-SEQ-2 applied to `(a, a)`); at every `alt a b`, WF-ALT-1
(FIRST-prefix freedom over the EFFECTIVE firsts) and WF-ALT-2 (no
nullable left); at every `fix`, WF-FIX (guardedness: `firstE body ≠
none`) strengthened by `nullableE body = false` (the rep-progress
consumption lemma stands on it) and `tailSelfFreeE body` (the
junction lemma's once-unfold corner — Grammar.lean's header). The
effective-firsts/tail folds take the fix body's once-unfold values as
parameters (Grammar.lean); `PredictiveE`'s rows cite them.

The semantic head disjointness (`SemDisj`, the matches-level mutual
exclusion the first-exclusion lemma stands on) and the sound bridges
(`disj_sound`, `breaks_sound`) live in Laws.lean with the lemma
family; the certificate's rows ride the decidable shadows.

Core-only. Five questions:
- root: none — the certificate is a computed Prop over the grammar.
- carrier grade: the soundness-mandatory bridge (15 #1); completeness
  loudly absent — the constructor choice is the declaration.
- spine reading: none — the discharge site's route to the laws'
  premise.
- ladder rung: the bridge is the mechanical fold kind (01 §7).
- gate row: none yet — TextKitTests pins the teeth (the sabotaged
  grammars must each fail `wfCheck` with the named row).
-/

import TextKit.Grammar
import Kit.Diag

namespace TextKit

/-- The decidable head disjointness (design §2.2): lit/lit — neither is
    a prefix of the other; lit/cls (either side) — the literal is
    NONEMPTY and its head char fails the class predicate (the empty
    literal matches everything, so it is never disjoint from a class —
    the previous wave's `head?.any` form was unsound there);
    cls/cls — conservative reject. -/
def HeadSpec.disj : HeadSpec → HeadSpec → Bool
  | .lit s1, .lit s2 => !(s1.toList.isPrefixOf s2.toList || s2.toList.isPrefixOf s1.toList)
  | .lit s, .cls p => (match s.toList with | [] => false | c :: _ => !p c)
  | .cls p, .lit s => (match s.toList with | [] => false | c :: _ => !p c)
  | .cls _, .cls _ => false

/-- The decidable munch-break: the head is a NONEMPTY literal whose
    first char fails the munch predicate (`lit "": false` — the empty
    literal gives no char to break on; `cls`: conservative reject —
    design §2.2's WF-SEQ-2). -/
def HeadSpec.breaks : HeadSpec → (Char → Bool) → Bool
  | .lit s, p => (match s.toList with | [] => false | c :: _ => !p c)
  | .cls _, _ => false

/-- The semantic head disjointness: on ANY text, at most one of the two
    heads matches (the mutual exclusion the first-exclusion lemma stands
    on — design §3.4). -/
def HeadSpec.SemDisj (h1 h2 : HeadSpec) : Prop :=
  ∀ cs, h1.matches cs = true → h2.matches cs = false

/-! ## the body's once-unfold values (the E-rows' parameters) -/

/-- The fix body's own firsts (the `selfE` effective-firsts value). -/
def GrammarE.bodyFirsts (sb : GrammarE R R) : List HeadSpec := (firstE sb).getD []

/-- The fix body's tail-stop firsts (the `selfE` tail-firsts value). -/
def GrammarE.bodyTailFirsts (sb : GrammarE R R) : List HeadSpec :=
  tailFirstE (bodyFirsts sb) [] sb

/-- The fix body's tail munches (the `selfE` tail-munch value). -/
def GrammarE.bodyTailMunch (sb : GrammarE R R) : Option (List (Char → Bool)) :=
  tailMunchE Option.none sb

/-! ## the semantic rows -/

/-- The well-formedness rows for the open family (design §2.2, cited
    over the once-unfold folds of the enclosing body `sb`). A
    PROP-VALUED FOLD (not an inductive family): the laws invert the
    rows by the fold's `rfl` equations — an inductive family's
    inversion over the `Type 1` index fights dependent elimination
    (the `(A × B) = (A' × B')` unification the `cases` tactic cannot
    solve); the fold IS the semantic Prop of record (15 #1's P). -/
def GrammarE.PredictiveE (sb : GrammarE R R) : {A : Type} → GrammarE R A → Prop
  | _, .atomE _ => True
  | _, .seqE a b => PredictiveE sb a ∧ PredictiveE sb b ∧
      (∀ s1 ∈ tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) a,
        ∀ s2 ∈ effFirstE (bodyFirsts sb) b, HeadSpec.disj s1 s2 = true) ∧
      (∀ p ∈ (tailMunchE (bodyTailMunch sb) a).getD [],
        ∀ s2 ∈ effFirstE (bodyFirsts sb) b, s2.breaks p = true)
  | _, .altE a b => PredictiveE sb a ∧ PredictiveE sb b ∧
      (∀ s1 ∈ effFirstE (bodyFirsts sb) a,
        ∀ s2 ∈ effFirstE (bodyFirsts sb) b, HeadSpec.disj s1 s2 = true) ∧
      nullableE a = false
  | _, .repE a => PredictiveE sb a ∧ nullableE a = false ∧
      (∀ p ∈ (tailMunchE (bodyTailMunch sb) a).getD [],
        ∀ s2 ∈ effFirstE (bodyFirsts sb) a, s2.breaks p = true) ∧
      (∀ s1 ∈ tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) a,
        ∀ s2 ∈ effFirstE (bodyFirsts sb) a, s1.disj s2 = true)
  | _, .optE a => PredictiveE sb a ∧ nullableE a = false
  | _, .labelE _ a => PredictiveE sb a
  | _, .relE _ _ _ _ _ _ sub => PredictiveE sb sub
  | _, .selfE => True

/-- The semantic well-formedness (the closed level; a Prop-valued fold
    — see `PredictiveE`'s note). WF-OPT (`opt`'s body non-nullable)
    is this wave's honest addition to design §2.2's row list: an
    `opt` with a nullable body mis-parses `none` (the body's empty
    success is re-wrapped `some`) — the none-case exclusion stands on
    it. -/
def Grammar.Predictive : {A : Type} → Grammar A → Prop
  | _, .atom _ => True
  | _, .seq a b => Predictive a ∧ Predictive b ∧
      (∀ s1 ∈ tailFirst a, ∀ s2 ∈ effFirst b, HeadSpec.disj s1 s2 = true) ∧
      (∀ p ∈ (tailMunch a).getD [], ∀ s2 ∈ effFirst b, s2.breaks p = true)
  | _, .alt a b => Predictive a ∧ Predictive b ∧
      (∀ s1 ∈ effFirst a, ∀ s2 ∈ effFirst b, HeadSpec.disj s1 s2 = true) ∧
      nullable a = false
  | _, .rep a => Predictive a ∧ nullable a = false ∧
      (∀ p ∈ (tailMunch a).getD [], ∀ s2 ∈ effFirst a, s2.breaks p = true) ∧
      (∀ s1 ∈ tailFirst a, ∀ s2 ∈ effFirst a, s1.disj s2 = true)
  | _, .opt a => Predictive a ∧ nullable a = false
  | _, .label _ a => Predictive a
  | _, .rel _ _ _ _ _ _ sub => Predictive sub
  | _, .fix _ body _ => GrammarE.PredictiveE body body ∧
      body.firstE ≠ none ∧ body.nullableE = false ∧ body.tailSelfFreeE = true

/-! ## the checker (the row-naming problem walk; wfCheck = no problems) -/

/-- The certificate's E-code slot (ALLOCATED from the persisted
    registry — `notes/code-registry.txt`, row TK0901). -/
def Grammar.wfCode : ECode := ⟨"TK0901"⟩

/-- The problem walk for the open family: the list of FAILED row names
    (each naming its junction's label chain). The checker is
    `isEmpty` of this — the check/diagnose consistency is by
    construction (design §2.3's note). -/
def GrammarE.wfProblemsE {R : Type} (sb : GrammarE R R) :
    (path : List String) → GrammarE R A → List String :=
  fun path g => match g with
  | .atomE _ => []
  | .seqE a b =>
      let row1 := (tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) a).all
        (fun s1 => (effFirstE (bodyFirsts sb) b).all (fun s2 => s1.disj s2))
      let row2 := ((tailMunchE (bodyTailMunch sb) a).getD []).all
        (fun p => (effFirstE (bodyFirsts sb) b).all (fun s2 => s2.breaks p))
      wfProblemsE sb path a ++ wfProblemsE sb path b ++
        (if row1 then [] else [s!"WF-SEQ-1 at {path}"]) ++
        (if row2 then [] else [s!"WF-SEQ-2 at {path}"])
  | .altE a b =>
      let row1 := (effFirstE (bodyFirsts sb) a).all
        (fun s1 => (effFirstE (bodyFirsts sb) b).all (fun s2 => s1.disj s2))
      wfProblemsE sb path a ++ wfProblemsE sb path b ++
        (if row1 then [] else [s!"WF-ALT-1 at {path}"]) ++
        (if nullableE a then [s!"WF-ALT-2 at {path}"] else [])
  | .repE a =>
      let row2 := (((tailMunchE (bodyTailMunch sb) a).getD []).all
          (fun p => (effFirstE (bodyFirsts sb) a).all (fun s2 => s2.breaks p))) &&
        ((tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) a).all
          (fun s1 => (effFirstE (bodyFirsts sb) a).all (fun s2 => s1.disj s2)))
      wfProblemsE sb path a ++
        (if nullableE a then [s!"WF-REP-1 at {path}"] else []) ++
        (if row2 then [] else [s!"WF-REP-2 at {path}"])
  | .optE a =>
      wfProblemsE sb path a ++
        (if nullableE a then [s!"WF-OPT at {path}"] else [])
  | .labelE n a => wfProblemsE sb (n :: path) a
  | .relE _ _ _ _ _ _ sub => wfProblemsE sb path sub
  | .selfE => []

/-- The check for the open family: no problems. -/
def GrammarE.wfCheckE {R : Type} (sb : GrammarE R R) (g : GrammarE R A) : Bool :=
  (wfProblemsE sb [] g).isEmpty

/-- wfProblemsE's seqE equation (iota through the lets). -/
theorem GrammarE.wfProblemsE_seqE {R : Type} (sb : GrammarE R R) (path : List String)
    (a : GrammarE R A) (b : GrammarE R B) :
    wfProblemsE sb path (.seqE a b) =
      wfProblemsE sb path a ++ wfProblemsE sb path b ++
        (if (tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) a).all
            (fun s1 => (effFirstE (bodyFirsts sb) b).all (fun s2 => s1.disj s2))
         then [] else [s!"WF-SEQ-1 at {path}"]) ++
        (if ((tailMunchE (bodyTailMunch sb) a).getD []).all
            (fun p => (effFirstE (bodyFirsts sb) b).all (fun s2 => s2.breaks p))
         then [] else [s!"WF-SEQ-2 at {path}"]) := rfl

/-- wfProblemsE's altE equation. -/
theorem GrammarE.wfProblemsE_altE {R : Type} (sb : GrammarE R R) (path : List String)
    (a b : GrammarE R A) :
    wfProblemsE sb path (.altE a b) =
      wfProblemsE sb path a ++ wfProblemsE sb path b ++
        (if (effFirstE (bodyFirsts sb) a).all
            (fun s1 => (effFirstE (bodyFirsts sb) b).all (fun s2 => s1.disj s2))
         then [] else [s!"WF-ALT-1 at {path}"]) ++
        (if nullableE a then [s!"WF-ALT-2 at {path}"] else []) := rfl

/-- wfProblemsE's repE equation. -/
theorem GrammarE.wfProblemsE_repE {R : Type} (sb : GrammarE R R) (path : List String)
    (a : GrammarE R A) :
    wfProblemsE sb path (.repE a) =
      wfProblemsE sb path a ++
        (if nullableE a then [s!"WF-REP-1 at {path}"] else []) ++
        (if (((tailMunchE (bodyTailMunch sb) a).getD []).all
              (fun p => (effFirstE (bodyFirsts sb) a).all (fun s2 => s2.breaks p))) &&
            ((tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) a).all
              (fun s1 => (effFirstE (bodyFirsts sb) a).all (fun s2 => s1.disj s2)))
         then [] else [s!"WF-REP-2 at {path}"]) := rfl

/-- The problem walk for the closed level. -/
def Grammar.wfProblems : (path : List String) → Grammar A → List String :=
  fun path g => match g with
  | .atom _ => []
  | .seq a b =>
      let row1 := (tailFirst a).all
        (fun s1 => (effFirst b).all (fun s2 => s1.disj s2))
      let row2 := ((tailMunch a).getD []).all
        (fun p => (effFirst b).all (fun s2 => s2.breaks p))
      wfProblems path a ++ wfProblems path b ++
        (if row1 then [] else [s!"WF-SEQ-1 at {path}"]) ++
        (if row2 then [] else [s!"WF-SEQ-2 at {path}"])
  | .alt a b =>
      let row1 := (effFirst a).all
        (fun s1 => (effFirst b).all (fun s2 => s1.disj s2))
      wfProblems path a ++ wfProblems path b ++
        (if row1 then [] else [s!"WF-ALT-1 at {path}"]) ++
        (if nullable a then [s!"WF-ALT-2 at {path}"] else [])
  | .rep a =>
      let row2 := (((tailMunch a).getD []).all
          (fun p => (effFirst a).all (fun s2 => s2.breaks p))) &&
        ((tailFirst a).all
          (fun s1 => (effFirst a).all (fun s2 => s1.disj s2)))
      wfProblems path a ++
        (if nullable a then [s!"WF-REP-1 at {path}"] else []) ++
        (if row2 then [] else [s!"WF-REP-2 at {path}"])
  | .opt a =>
      wfProblems path a ++
        (if nullable a then [s!"WF-OPT at {path}"] else [])
  | .label n a => wfProblems (n :: path) a
  | .rel _ _ _ _ _ _ sub => wfProblems path sub
  | .fix _ body _ =>
      GrammarE.wfProblemsE body path body ++
        (if (GrammarE.firstE body).isSome && !GrammarE.nullableE body &&
            GrammarE.tailSelfFreeE body
         then [] else [s!"WF-FIX at {path}"])

/-- wfProblems's seq equation (iota through the lets). -/
theorem Grammar.wfProblems_seq (path : List String) (a : Grammar A) (b : Grammar B) :
    wfProblems path (.seq a b) =
      wfProblems path a ++ wfProblems path b ++
        (if (tailFirst a).all (fun s1 => (effFirst b).all (fun s2 => s1.disj s2))
         then [] else [s!"WF-SEQ-1 at {path}"]) ++
        (if ((tailMunch a).getD []).all (fun p => (effFirst b).all (fun s2 => s2.breaks p))
         then [] else [s!"WF-SEQ-2 at {path}"]) := rfl

/-- wfProblems's alt equation. -/
theorem Grammar.wfProblems_alt (path : List String) (a b : Grammar A) :
    wfProblems path (.alt a b) =
      wfProblems path a ++ wfProblems path b ++
        (if (effFirst a).all (fun s1 => (effFirst b).all (fun s2 => s1.disj s2))
         then [] else [s!"WF-ALT-1 at {path}"]) ++
        (if nullable a then [s!"WF-ALT-2 at {path}"] else []) := rfl

/-- wfProblems's rep equation. -/
theorem Grammar.wfProblems_rep (path : List String) (a : Grammar A) :
    wfProblems path (.rep a) =
      wfProblems path a ++
        (if nullable a then [s!"WF-REP-1 at {path}"] else []) ++
        (if (((tailMunch a).getD []).all
              (fun p => (effFirst a).all (fun s2 => s2.breaks p))) &&
            ((tailFirst a).all (fun s1 => (effFirst a).all (fun s2 => s1.disj s2)))
         then [] else [s!"WF-REP-2 at {path}"]) := rfl

/-- wfProblems's fix equation. -/
theorem Grammar.wfProblems_fix (path : List String) (m : R → Nat) (body : GrammarE R R)
    (dec : ∀ x y, SelfPathE body x y → m y < m x) :
    wfProblems path (.fix m body dec) =
      GrammarE.wfProblemsE body path body ++
        (if (GrammarE.firstE body).isSome && !GrammarE.nullableE body &&
            GrammarE.tailSelfFreeE body
         then [] else [s!"WF-FIX at {path}"]) := rfl

/-- The checker: no problems. -/
def Grammar.wfCheck (g : Grammar A) : Bool := (wfProblems [] g).isEmpty

/-- The failure-facing twin: one Diag per failed row, NAMING the row
    and the junction's label chain. Build-time errors (dsl!/the
    discharge site), never parse errors. -/
def Grammar.wfDiagnose (g : Grammar R) : List Kit.Diag :=
  (wfProblems [] g).map fun row =>
    Kit.Diag.closedWorld wfCode s!"grammar rejected: {row}" .error "grammar" []

/-! ## the soundness bridge -/

-- List.isEmpty/append/if plumbing (small hand kind).
private theorem isEmpty_append {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).isEmpty = true → l₁.isEmpty = true ∧ l₂.isEmpty = true := by
  cases l₁ <;> cases l₂ <;> simp_all

private theorem isEmpty_ite_nil (c : Bool) (s : String) :
    ((if c then [] else [s]) : List String).isEmpty = true → c = true := by
  cases c <;> simp_all

private theorem isEmpty_ite_singleton (c : Bool) (s : String) :
    ((if c then [s] else []) : List String).isEmpty = true → c = false := by
  cases c <;> simp_all

private theorem all₂ {α : Type} {p : α → Bool} {l : List α} (h : l.all p = true) :
    ∀ x ∈ l, p x = true :=
  List.all_eq_true.mp h

/-- The open-family soundness bridge. -/
theorem GrammarE.wfCheckE_sound {R : Type} (sb : GrammarE R R) :
    {A : Type} → (g : GrammarE R A) →
    (path : List String) → (wfProblemsE sb path g).isEmpty = true → PredictiveE sb g := by
  intro A g
  induction g with
  | atomE L => intro _ _; exact trivial
  | seqE a b iha ihb =>
      intro path h
      rw [wfProblemsE_seqE] at h
      obtain ⟨h12, h2i⟩ := isEmpty_append _ _ h
      obtain ⟨hab, h1i⟩ := isEmpty_append _ _ h12
      obtain ⟨ha, hb⟩ := isEmpty_append _ _ hab
      refine ⟨iha path ha, ihb path hb, ?_, ?_⟩
      · intro s1 hs1 s2 hs2
        exact all₂ (all₂ (isEmpty_ite_nil _ _ h1i) s1 hs1) s2 hs2
      · intro p hp s2 hs2
        exact all₂ (all₂ (isEmpty_ite_nil _ _ h2i) p hp) s2 hs2
  | altE a b iha ihb =>
      intro path h
      rw [wfProblemsE_altE] at h
      obtain ⟨h12, h2i⟩ := isEmpty_append _ _ h
      obtain ⟨hab, h1i⟩ := isEmpty_append _ _ h12
      obtain ⟨ha, hb⟩ := isEmpty_append _ _ hab
      refine ⟨iha path ha, ihb path hb, ?_, isEmpty_ite_singleton _ _ h2i⟩
      intro s1 hs1 s2 hs2
      exact all₂ (all₂ (isEmpty_ite_nil _ _ h1i) s1 hs1) s2 hs2
  | repE a iha =>
      intro path h
      rw [wfProblemsE_repE] at h
      obtain ⟨ha12, h2i⟩ := isEmpty_append _ _ h
      obtain ⟨ha, h1i⟩ := isEmpty_append _ _ ha12
      refine ⟨iha path ha, isEmpty_ite_singleton _ _ h1i, ?_, ?_⟩
      · intro p hp s2 hs2
        have h2 := isEmpty_ite_nil _ _ h2i
        simp only [Bool.and_eq_true] at h2
        exact all₂ (all₂ h2.1 p hp) s2 hs2
      · intro s1 hs1 s2 hs2
        have h2 := isEmpty_ite_nil _ _ h2i
        simp only [Bool.and_eq_true] at h2
        exact all₂ (all₂ h2.2 s1 hs1) s2 hs2
  | optE a iha =>
      intro path h
      obtain ⟨ha, hoi⟩ := isEmpty_append _ _ h
      exact ⟨iha path ha, isEmpty_ite_singleton _ _ hoi⟩
  | labelE n a iha => intro path h; exact iha (n :: path) h
  | relE m owns don ex nm vld sub ih =>
      intro path h
      exact ih path h
  | selfE => intro _ _; exact trivial

/-- The closed-level soundness bridge, path-general form. -/
theorem Grammar.wfCheck_sound' : (g : Grammar A) →
    (path : List String) → (wfProblems path g).isEmpty = true → Predictive g := by
  intro g
  induction g with
  | atom L => intro _ _; exact trivial
  | seq a b iha ihb =>
      intro path h
      rw [wfProblems_seq] at h
      obtain ⟨h12, h2i⟩ := isEmpty_append _ _ h
      obtain ⟨hab, h1i⟩ := isEmpty_append _ _ h12
      obtain ⟨ha, hb⟩ := isEmpty_append _ _ hab
      refine ⟨iha path ha, ihb path hb, ?_, ?_⟩
      · intro s1 hs1 s2 hs2
        exact all₂ (all₂ (isEmpty_ite_nil _ _ h1i) s1 hs1) s2 hs2
      · intro p hp s2 hs2
        exact all₂ (all₂ (isEmpty_ite_nil _ _ h2i) p hp) s2 hs2
  | alt a b iha ihb =>
      intro path h
      rw [wfProblems_alt] at h
      obtain ⟨h12, h2i⟩ := isEmpty_append _ _ h
      obtain ⟨hab, h1i⟩ := isEmpty_append _ _ h12
      obtain ⟨ha, hb⟩ := isEmpty_append _ _ hab
      refine ⟨iha path ha, ihb path hb, ?_, isEmpty_ite_singleton _ _ h2i⟩
      intro s1 hs1 s2 hs2
      exact all₂ (all₂ (isEmpty_ite_nil _ _ h1i) s1 hs1) s2 hs2
  | rep a iha =>
      intro path h
      rw [wfProblems_rep] at h
      obtain ⟨ha12, h2i⟩ := isEmpty_append _ _ h
      obtain ⟨ha, h1i⟩ := isEmpty_append _ _ ha12
      refine ⟨iha path ha, isEmpty_ite_singleton _ _ h1i, ?_, ?_⟩
      · intro p hp s2 hs2
        have h2 := isEmpty_ite_nil _ _ h2i
        simp only [Bool.and_eq_true] at h2
        exact all₂ (all₂ h2.1 p hp) s2 hs2
      · intro s1 hs1 s2 hs2
        have h2 := isEmpty_ite_nil _ _ h2i
        simp only [Bool.and_eq_true] at h2
        exact all₂ (all₂ h2.2 s1 hs1) s2 hs2
  | opt a iha =>
      intro path h
      obtain ⟨ha, hoi⟩ := isEmpty_append _ _ h
      exact ⟨iha path ha, isEmpty_ite_singleton _ _ hoi⟩
  | label n a iha => intro path h; exact iha (n :: path) h
  | rel m owns don ex nm vld sub ih =>
      intro path h
      exact ih path h
  | fix m body dec =>
      intro path h
      rw [wfProblems_fix] at h
      obtain ⟨hb, hfi⟩ := isEmpty_append _ _ h
      have hf : ((GrammarE.firstE body).isSome && !GrammarE.nullableE body &&
          GrammarE.tailSelfFreeE body) = true :=
        isEmpty_ite_nil _ _ hfi
      have hfs : (GrammarE.firstE body).isSome = true := by
        cases c1 : (GrammarE.firstE body).isSome <;> simp_all
      have hnn : GrammarE.nullableE body = false := by
        cases c2 : GrammarE.nullableE body <;> simp_all
      have htf : GrammarE.tailSelfFreeE body = true := by
        cases c3 : GrammarE.tailSelfFreeE body <;> simp_all
      refine ⟨GrammarE.wfCheckE_sound body body path hb, ?_, hnn, htf⟩
      cases hfsb : GrammarE.firstE body with
      | none => simp [hfsb] at hfs
      | some _ => simp

/-- The closed-level soundness bridge (15 #1's sound field). -/
theorem Grammar.wfCheck_sound (g : Grammar A) (h : wfCheck g = true) : Predictive g :=
  wfCheck_sound' g [] h

end TextKit
