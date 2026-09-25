/-
# TextKit.Grammar.Laws — the two generic round-trip laws (05 §1's point)

The design of record: `notes/design-grammar-layer-v2.md` (round two;
v1's `notes/design-grammar-layer.md` §3.2–3.4 stays as history). Under
the certificate (`Predictive`, the PROVED `wfCheck_sound` route), ONE
`Grammar` value's derived parser and printer round-trip BOTH ways:

- `Grammar.parse_print` (law 1, append form, 15 #2): under
  `valueOk`-discipline + the GUARD-AWARE fuel slack (`guardSlack`, v2
  §6.1) + the tail-adequacy fold `tailOk`, parsing the print returns
  the value and leaves the suffix.
- `Grammar.print_parse` (law 2, exactness): a successful parse
  consumed EXACTLY the print of its result, with the offsets and the
  parsed-values-are-owned conjunct, under the semantic `altCoherent`
  premise (the round-one discovery: two rel-branches whose codecs
  decode different spellings INTO the same value are first-disjoint,
  accepted, and exactness-false). The migration targets discharge it
  by ctor discrimination (`altCoherent_alt_rel_rel`).
  `print_run` (accepted text IS canonical) needs it too.

THE PROOF ARCHITECTURE (v2 §6's per-node tables, executed):
- §0: the small hand lemmas + v2 §6.2's additions (`disj_symm`,
  `firstE_head_ne`, `tailMunchE_isSome`, `bodyTailMunch_isSome`);
- §1: the print-head-vs-FIRST family (`printBundleE`/`printFixBundle`)
  — the wall-1 kit's print half;
- §2: the parse-side duals (`parseMonoE`/`parseConsumeE`);
- §3: law 2 open (`print_parse_E`) under the `altCoherentE` fold;
- §4: the parse head/exclusion family (`parseHeadE`/`parseExcludeE`);
- §5: the closed family + law 2 closed (`print_parse`);
- §6 (v2 §6): the fuel slack + the JUNCTION family
  (`junctionE`/`junctionEG`/`junctionG`) + law 1 open+closed
  (`parse_print_E`/`parse_print`/`run_print`) + `tailOk_nil` +
  `predictive_guard` + the coherence discharge kit;
- §6.7: the closed law 1 over the FIX-FREE fragment (the flat formats'
  face — the closed junction `junctionG_fixFree` +
  `parse_print_fixFree`/`run_print_fixFree` + `FixFree`).

Core-only. Five questions:
- root: none — the laws over the grammar value.
- carrier grade: 15 #2's append-form round trips (the layer's reason
  to exist).
- spine reading: none.
- ladder rung: the lemma family is the small-generic kind (01 §7);
  the laws are the generic theorems the formats specialize (05 §3's
  thin-wrapper rule).
- gate row: none yet — TextKitTests pins the fixture instances +
  axiom pins.
-/

import TextKit.Grammar.Parse
import TextKit.Grammar.Check
import Kit.CheckedProp

namespace TextKit

/-! ## §0: the small list/string hand lemmas (01 §7's rung) -/

/-- Prefixes of a common extension are comparable (the disj bridge's
    lit/lit content). -/
theorem prefix_total {l₁ l₂ cs : List Char} :
    l₁ <+: cs → l₂ <+: cs → l₁ <+: l₂ ∨ l₂ <+: l₁ := by
  intro h1 h2
  induction l₁ generalizing l₂ cs with
  | nil => exact Or.inl ⟨l₂, rfl⟩
  | cons a as ih =>
      cases l₂ with
      | nil => exact Or.inr ⟨a :: as, rfl⟩
      | cons b bs =>
          obtain ⟨t₁, e₁⟩ := h1
          obtain ⟨t₂, e₂⟩ := h2
          have hab : a = b ∧ as ++ t₁ = bs ++ t₂ :=
            List.cons.inj (e₁.trans e₂.symm)
          obtain ⟨rfl, h2'⟩ := hab
          rcases ih (cs := bs ++ t₂) ⟨t₁, h2'⟩ ⟨t₂, rfl⟩ with ⟨t, e⟩ | ⟨t, e⟩
          · exact Or.inl ⟨t, by rw [List.cons_append, e]⟩
          · exact Or.inr ⟨t, by rw [List.cons_append, e]⟩

/-- A list is a prefix of its right-extensions. -/
theorem isPrefixOf_append_right (l r : List Char) :
    l.isPrefixOf (l ++ r) = true :=
  List.isPrefixOf_iff_prefix.mpr ⟨r, rfl⟩

/-- Head matching is extension-stable. -/
theorem HeadSpec.matches_append (h : HeadSpec) (cs ds : List Char) :
    h.matches cs = true → h.matches (cs ++ ds) = true := by
  cases h with
  | lit s =>
      intro hm
      show s.toList.isPrefixOf (cs ++ ds) = true
      have : s.toList <+: cs := List.isPrefixOf_iff_prefix.mp hm
      obtain ⟨t, e⟩ := this
      rw [List.isPrefixOf_iff_prefix]
      exact ⟨t ++ ds, by rw [← e, List.append_assoc]⟩
  | cls p =>
      intro hm
      show (cs ++ ds).head?.any p = true
      rw [List.head?_append]
      cases hcs : cs.head? with
      | none =>
          have h2 : cs.head?.any p = true := hm
          rw [hcs] at h2
          simp at h2
      | some c =>
          have hc : p c = true := by
            have h2 : cs.head?.any p = true := hm
            rw [hcs] at h2
            exact h2
          exact hc

/-- The decidable disjointness implies the semantic one (the
    certificate's bridge, the small hand kind). -/
theorem HeadSpec.disj_sound {h1 h2 : HeadSpec} :
    h1.disj h2 = true → HeadSpec.SemDisj h1 h2 := by
  intro hd cs hm
  cases h1 with
  | lit s1 =>
      cases h2 with
      | lit s2 =>
          show s2.toList.isPrefixOf cs = false
          have hd' : (s1.toList.isPrefixOf s2.toList ||
              s2.toList.isPrefixOf s1.toList) = false := by
            cases h : (s1.toList.isPrefixOf s2.toList ||
                s2.toList.isPrefixOf s1.toList) with
            | false => rfl
            | true => simp [disj, h] at hd
          have hd'' := Bool.or_eq_false_iff.mp hd'
          cases hm2 : s2.toList.isPrefixOf cs with
          | false => rfl
          | true =>
              have hp1 : s1.toList <+: cs := List.isPrefixOf_iff_prefix.mp hm
              have hp2 : s2.toList <+: cs := List.isPrefixOf_iff_prefix.mp hm2
              rcases prefix_total hp1 hp2 with ⟨t, e⟩ | ⟨t, e⟩
              · have h11 : s1.toList.isPrefixOf s2.toList = true :=
                  List.isPrefixOf_iff_prefix.mpr ⟨t, e⟩
                simp [h11] at hd''
              · have h22 : s2.toList.isPrefixOf s1.toList = true :=
                  List.isPrefixOf_iff_prefix.mpr ⟨t, e⟩
                simp [h22] at hd''
      | cls p =>
          show cs.head?.any p = false
          cases hs : s1.toList with
          | nil => simp [disj, hs] at hd
          | cons c s' =>
              simp [disj, hs] at hd
              have h2 : s1.toList.isPrefixOf cs = true := hm
              rw [hs] at h2
              have hp : (c :: s') <+: cs := List.isPrefixOf_iff_prefix.mp h2
              obtain ⟨t, e⟩ := hp
              have hcs : cs.head? = Option.some c := by rw [← e]; rfl
              rw [hcs]
              exact hd
  | cls p1 =>
      cases h2 with
      | lit s2 =>
          show s2.toList.isPrefixOf cs = false
          cases hs : s2.toList with
          | nil => simp [disj, hs] at hd
          | cons c s' =>
              simp [disj, hs] at hd
              cases hcs : cs.head? with
              | none =>
                  have h2 : cs.head?.any p1 = true := hm
                  rw [hcs] at h2
                  simp at h2
              | some c' =>
                  have hpc : p1 c' = true := by
                    have h2 : cs.head?.any p1 = true := hm
                    rw [hcs] at h2
                    exact h2
                  cases hpre : (c :: s').isPrefixOf cs with
                  | false => rfl
                  | true =>
                      have hp : (c :: s') <+: cs := List.isPrefixOf_iff_prefix.mp hpre
                      obtain ⟨t, e⟩ := hp
                      have hc' : cs.head? = Option.some c := by rw [← e]; rfl
                      rw [hc'] at hcs
                      injection hcs with hcc
                      rw [hcc] at hd
                      simp [hd] at hpc
      | cls p2 => simp [disj] at hd

/-- The decidable munch-break is sound: a broken head never matches a
    text whose head char passes the munch predicate. -/
theorem HeadSpec.breaks_sound {h : HeadSpec} {p : Char → Bool} {cs : List Char} :
    h.breaks p = true → h.matches cs = true →
    cs.head?.all (fun c => !p c) = true := by
  intro hb hm
  cases h with
  | lit s =>
      cases hs : s.toList with
      | nil => simp [breaks, hs] at hb
      | cons c s' =>
          simp [breaks, hs] at hb
          have h2 : s.toList.isPrefixOf cs = true := hm
          rw [hs] at h2
          have hp : (c :: s') <+: cs := List.isPrefixOf_iff_prefix.mp h2
          obtain ⟨t, e⟩ := hp
          have hcs : cs.head? = Option.some c := by rw [← e]; rfl
          rw [hcs]
          show (!p c) = true
          simp [hb]
  | cls p' => simp [breaks] at hb

/-- Nonempty left factor makes a nonempty append. -/
theorem String.append_left_ne_empty {s t : String} (h : s ≠ "") : s ++ t ≠ "" := by
  intro heq
  have h2 := congrArg String.toList heq
  rw [String.toList_append] at h2
  simp [List.append_eq_nil_iff] at h2
  exact h (String.toList_injective (by simp [h2.1]))

/-- Nonempty right factor makes a nonempty append. -/
theorem String.append_right_ne_empty {s t : String} (h : t ≠ "") : s ++ t ≠ "" := by
  intro heq
  have h2 := congrArg String.toList heq
  rw [String.toList_append] at h2
  simp [List.append_eq_nil_iff] at h2
  exact h (String.toList_injective (by simp [h2.2]))

/-- A nonempty string has positive length. -/
theorem String.ne_empty_length {s : String} (h : s ≠ "") : 0 < s.length := by
  cases hs : s.toList with
  | nil => exact absurd (String.toList_injective (by simp [hs])) h
  | cons c cs' =>
      have : s.length = (c :: cs').length := by rw [← String.length_toList, hs]
      simp [this]

/-- A nonempty string's toList is nonempty. -/
theorem String.ne_empty_toList {s : String} (h : s ≠ "") : s.toList ≠ [] := by
  intro heq
  exact h (String.toList_injective (by simp [heq]))

/-! ## §1: the print-head-vs-FIRST family -/

/-- effFirstE agrees with firstE when the latter succeeds (the
    selfE-unfold parameter never surfaces under a concrete FIRST). -/
theorem GrammarE.effFirstE_of_firstE {R : Type} :
    {A : Type} → (g : GrammarE R A) → (fs hs : List HeadSpec) →
    firstE g = Option.some hs → effFirstE fs g = hs := by
  intro A g
  induction g with
  | atomE L => intro fs hs h; simp [firstE] at h; rw [← h]; rfl
  | seqE a b iha ihb =>
      intro fs hs h
      simp only [firstE] at h
      cases hfa : firstE a with
      | none => rw [hfa] at h; simp at h
      | some ha =>
          rw [hfa] at h
          cases hna : nullableE a with
          | false =>
              simp [hna] at h
              subst h
              show effFirstE fs a ++ (if nullableE a then effFirstE fs b else []) = ha
              rw [hna]
              simp
              exact iha fs ha hfa
          | true =>
              simp [hna] at h
              cases hfb : firstE b with
              | none => rw [hfb] at h; simp at h
              | some hb =>
                  rw [hfb] at h
                  simp at h
                  subst h
                  show effFirstE fs a ++ (if nullableE a then effFirstE fs b else []) = ha ++ hb
                  rw [hna, iha fs ha hfa, ihb fs hb hfb]
                  simp
  | altE a b iha ihb =>
      intro fs hs h
      simp only [firstE] at h
      cases hfa : firstE a with
      | none => rw [hfa] at h; simp at h
      | some ha =>
          cases hfb : firstE b with
          | none => rw [hfa, hfb] at h; simp at h
          | some hb =>
              rw [hfa, hfb] at h
              simp at h
              subst h
              show effFirstE fs a ++ effFirstE fs b = ha ++ hb
              rw [iha fs ha hfa, ihb fs hb hfb]
  | repE a iha =>
      intro fs hs h
      simp only [firstE] at h
      show effFirstE fs a = hs
      exact iha fs hs h
  | optE a iha =>
      intro fs hs h
      simp only [firstE] at h
      show effFirstE fs a = hs
      exact iha fs hs h
  | labelE n a iha =>
      intro fs hs h
      simp only [firstE] at h
      show effFirstE fs a = hs
      exact iha fs hs h
  | relE m owns don ex nm vld sub ih =>
      intro fs hs h
      simp only [firstE] at h
      show effFirstE fs sub = hs
      exact ih fs hs h
  | selfE => intro fs hs h; simp [firstE] at h

/-- WF-FIX's guardedness implies the guard fold (every selfE behind a
    guaranteed consumer). -/
theorem GrammarE.firstE_some_guardE {R : Type} :
    {A : Type} → (g : GrammarE R A) → firstE g ≠ none → guardE g = true := by
  intro A g
  induction g with
  | atomE L => intro _; rfl
  | seqE a b iha ihb =>
      intro hf
      have hfa : firstE a ≠ none := fun h => hf (by simp [firstE, h])
      have hga := iha hfa
      cases hna : nullableE a with
      | false =>
          show (guardE a && (if nullableE a then guardE b else true)) = true
          rw [hna]; simp [hga]
      | true =>
          have hfb : firstE b ≠ none := fun h => hf (by
            cases hfa' : firstE a with
            | none => exact absurd hfa' hfa
            | some ha => simp [firstE, hfa', hna, h])
          have hgb := ihb hfb
          show (guardE a && (if nullableE a then guardE b else true)) = true
          rw [hna]; simp [hga, hgb]
  | altE a b iha ihb =>
      intro hf
      have hfa : firstE a ≠ none := fun h => hf (by simp [firstE, h])
      have hfb : firstE b ≠ none := fun h => hf (by simp [firstE, h])
      show (guardE a && guardE b) = true
      simp [iha hfa, ihb hfb]
  | repE a iha => intro hf; exact iha (by simpa [firstE] using hf)
  | optE a iha => intro hf; exact iha (by simpa [firstE] using hf)
  | labelE n a iha => intro hf; exact iha (by simpa [firstE] using hf)
  | relE m owns don ex nm vld sub ih => intro hf; exact ih (by simpa [firstE] using hf)
  | selfE => intro hf; simp [firstE] at hf

/-- A nonempty print-list starts with the head of its first nonempty
    element (the rep case's list induction, standalone). -/
theorem GrammarE.printList_head {A : Type} {fs : List HeadSpec} :
    ∀ (ys : List A) (f : (z : A) → z ∈ ys → String),
    (∀ z hz, f z hz ≠ "" → ∀ cs, ∃ h ∈ fs, h.matches ((f z hz).toList ++ cs) = true) →
    printList ys f ≠ "" →
    ∀ cs, ∃ h ∈ fs, h.matches ((printList ys f).toList ++ cs) = true := by
  intro ys
  induction ys with
  | nil => intro f _ hne; simp [printList_nil] at hne
  | cons z zs ih =>
      intro f hf hne cs
      rw [printList_cons] at hne ⊢
      by_cases hz0 : f z (List.Mem.head zs) = ""
      · have hne' : printList zs (fun w hw => f w (List.Mem.tail z hw)) ≠ "" := by
          intro h0
          rw [hz0, h0] at hne
          exact hne (by simp)
        obtain ⟨h, hmem, hm⟩ := ih _ (fun w hw => hf w (List.Mem.tail z hw)) hne' cs
        refine ⟨h, hmem, ?_⟩
        have hsimpl : (f z (List.Mem.head zs) ++
            printList zs (fun w hw => f w (List.Mem.tail z hw))).toList ++ cs =
            (printList zs (fun w hw => f w (List.Mem.tail z hw))).toList ++ cs := by
          rw [hz0]; simp
        rw [hsimpl]; exact hm
      · obtain ⟨h, hmem, hm⟩ := hf z (List.Mem.head zs) hz0
          ((printList zs (fun w hw => f w (List.Mem.tail z hw))).toList ++ cs)
        refine ⟨h, hmem, ?_⟩
        have hsimpl : (f z (List.Mem.head zs) ++
            printList zs (fun w hw => f w (List.Mem.tail z hw))).toList ++ cs =
            (f z (List.Mem.head zs)).toList ++
              ((printList zs (fun w hw => f w (List.Mem.tail z hw))).toList ++ cs) := by
          rw [String.toList_append, List.append_assoc]
        rw [hsimpl]; exact hm

/-- The body's effective firsts ARE its firsts (the once-unfold value
    computed) — under WF-FIX guardedness. -/
theorem GrammarE.effFirstE_bodyFirsts {R : Type} (sb : GrammarE R R)
    (hf : sb.firstE ≠ none) :
    effFirstE sb.bodyFirsts sb = sb.bodyFirsts := by
  cases hf' : sb.firstE with
  | none => exact absurd hf' hf
  | some hs =>
      have h1 := effFirstE_of_firstE sb sb.bodyFirsts hs hf'
      rw [h1]
      simp [bodyFirsts, hf']

/-- The closed fix node's effective firsts are the body's. -/
theorem Grammar.effFirst_fix {R : Type} (m : R → Nat) (body : GrammarE R R)
    (dec : ∀ x y, SelfPathE body x y → m y < m x) (hf : body.firstE ≠ none) :
    effFirst (Grammar.fix m body dec) = body.bodyFirsts :=
  GrammarE.effFirstE_bodyFirsts body hf

/-- THE print-head-vs-FIRST kit (the seq-case wall's lemma family),
    both conjuncts in one induction: (1) a non-nullable grammar prints
    nonempty; (2) a nonempty print starts with an effective-first head.
    The HSB bundle is the self-leaves' interface to the fix-level
    instance (`Grammar.printFixBundle`). -/
theorem GrammarE.printBundleE {R : Type} :
    {A : Type} → (g : GrammarE R A) → (x : A) →
    (Hb : (y : R) → SelfPathE g x y → Bool) →
    (H : (y : R) → SelfPathE g x y → String) →
    (fs : List HeadSpec) →
    valueOkWalk g x Hb = true →
    (∀ y (path : SelfPathE g x y), Hb y path = true →
      (H y path ≠ "") ∧ ∀ cs, ∃ h ∈ fs, h.matches ((H y path).toList ++ cs) = true) →
    (nullableE g = false → printWalk g x Hb H ≠ "") ∧
    (printWalk g x Hb H ≠ "" →
      ∀ cs, ∃ h ∈ effFirstE fs g, h.matches ((printWalk g x Hb H).toList ++ cs) = true) := by
  intro A g
  induction g with
  | atomE L =>
      intro x Hb H fs hok HSB
      have hpre : L.pre x = true := hok
      have hmunch : (L.munch.all fun p => ([] : List Char).head?.all (fun c => !p c)) = true := by
        cases L.munch with
        | none => rfl
        | some p => simp
      have hscan := L.print_scan 0 x [] hpre hmunch
      have hcs : (L.print x).toList ++ [] = (L.print x).toList := List.append_nil _
      refine ⟨?_, ?_⟩
      · intro _
        intro hne
        have hne' : L.print x = "" := hne
        have hc := L.consumes _ _ _ hscan
        have hl : (L.print x).toList = [] := by rw [hne']; rfl
        simp [hl] at hc
      · intro hne cs
        have hhead := L.scan_head _ _ _ hscan
        refine ⟨L.head, by show L.head ∈ [L.head]; exact List.Mem.head [], ?_⟩
        show L.head.matches ((L.print x).toList ++ cs) = true
        apply HeadSpec.matches_append
        have := hhead
        rw [hcs] at this
        exact this
  | seqE a b iha ihb =>
      intro x Hb H fs hok HSB
      obtain ⟨p, q⟩ := x
      have hok' : valueOkWalk a p (fun y path => Hb y (.seqL path)) = true ∧
          valueOkWalk b q (fun y path => Hb y (.seqR path)) = true := by
        have := hok
        rw [valueOkWalk_seqE] at this
        simpa [Bool.and_eq_true] using this
      have HSBA : ∀ y (path : SelfPathE a p y),
          (fun y path => Hb y (.seqL path)) y path = true →
          ((fun y path => H y (.seqL path)) y path ≠ "") ∧
          ∀ cs, ∃ h ∈ fs, h.matches (((fun y path => H y (.seqL path)) y path).toList ++ cs) = true :=
        fun y path h => HSB y (.seqL path) h
      have HSBB : ∀ y (path : SelfPathE b q y),
          (fun y path => Hb y (.seqR path)) y path = true →
          ((fun y path => H y (.seqR path)) y path ≠ "") ∧
          ∀ cs, ∃ h ∈ fs, h.matches (((fun y path => H y (.seqR path)) y path).toList ++ cs) = true :=
        fun y path h => HSB y (.seqR path) h
      obtain ⟨neA, headA⟩ := iha p _ _ fs hok'.1 HSBA
      obtain ⟨neB, headB⟩ := ihb q _ _ fs hok'.2 HSBB
      have hneA : nullableE a = false →
          printWalk a p (fun y path => Hb y (.seqL path))
            (fun y path => H y (.seqL path)) ≠ "" := neA
      refine ⟨?_, ?_⟩
      · intro hnn
        rw [printWalk_seqE]
        cases hna : nullableE a with
        | false => exact String.append_left_ne_empty (hneA hna)
        | true =>
            have hnb : nullableE b = false := by
              have : nullableE (GrammarE.seqE a b) = false := hnn
              simp only [nullableE, hna, Bool.true_and] at this
              exact this
            exact String.append_right_ne_empty (neB hnb)
      · intro hne cs
        rw [printWalk_seqE] at hne ⊢
        by_cases hep : printWalk a p (fun y path => Hb y (.seqL path))
            (fun y path => H y (.seqL path)) = ""
        · have hna : nullableE a = true := by
            cases h : nullableE a with
            | false => exact absurd hep (hneA h)
            | true => rfl
          have hneB : printWalk b q (fun y path => Hb y (.seqR path))
              (fun y path => H y (.seqR path)) ≠ "" := by
            intro hb0
            rw [hep, hb0] at hne
            exact hne (by simp)
          obtain ⟨h, hmem, hm⟩ := headB hneB cs
          refine ⟨h, ?_, ?_⟩
          · show h ∈ effFirstE fs a ++ (if nullableE a then effFirstE fs b else [])
            rw [hna]
            exact List.mem_append_right _ hmem
          · have hsimpl : (printWalk a p (fun y path => Hb y (.seqL path))
                  (fun y path => H y (.seqL path)) ++
                printWalk b q (fun y path => Hb y (.seqR path))
                  (fun y path => H y (.seqR path))).toList ++ cs =
                (printWalk b q (fun y path => Hb y (.seqR path))
                  (fun y path => H y (.seqR path))).toList ++ cs := by
              rw [hep]
              simp
            rw [hsimpl]
            exact hm
        · obtain ⟨h, hmem, hm⟩ := headA hep ((printWalk b q
              (fun y path => Hb y (.seqR path)) (fun y path => H y (.seqR path))).toList ++ cs)
          refine ⟨h, ?_, ?_⟩
          · show h ∈ effFirstE fs a ++ (if nullableE a then effFirstE fs b else [])
            exact List.mem_append_left _ hmem
          · have hsimpl : (printWalk a p (fun y path => Hb y (.seqL path))
                  (fun y path => H y (.seqL path)) ++
                printWalk b q (fun y path => Hb y (.seqR path))
                  (fun y path => H y (.seqR path))).toList ++ cs =
                (printWalk a p (fun y path => Hb y (.seqL path))
                  (fun y path => H y (.seqL path))).toList ++
                ((printWalk b q (fun y path => Hb y (.seqR path))
                  (fun y path => H y (.seqR path))).toList ++ cs) := by
              rw [String.toList_append, List.append_assoc]
            rw [hsimpl]
            exact hm
  | altE a b iha ihb =>
      intro x Hb H fs hok HSB
      have HSBA : ∀ y (path : SelfPathE a x y),
          (fun y path => Hb y (.altL path)) y path = true →
          ((fun y path => H y (.altL path)) y path ≠ "") ∧
          ∀ cs, ∃ h ∈ fs, h.matches (((fun y path => H y (.altL path)) y path).toList ++ cs)
            = true :=
        fun y path h => HSB y (.altL path) h
      have HSBB : ∀ y (path : SelfPathE b x y),
          (fun y path => Hb y (.altR path)) y path = true →
          ((fun y path => H y (.altR path)) y path ≠ "") ∧
          ∀ cs, ∃ h ∈ fs, h.matches (((fun y path => H y (.altR path)) y path).toList ++ cs)
            = true :=
        fun y path h => HSB y (.altR path) h
      have hd : (valueOkWalk a x (fun y path => Hb y (.altL path)) ||
          valueOkWalk b x (fun y path => Hb y (.altR path))) = true := by
        have h3 := hok
        rw [valueOkWalk_altE] at h3
        exact h3
      have hb2_of : valueOkWalk a x (fun y path => Hb y (.altL path)) = false →
          valueOkWalk b x (fun y path => Hb y (.altR path)) = true := by
        intro h1
        cases h2 : valueOkWalk b x (fun y path => Hb y (.altR path)) with
        | true => rfl
        | false => simp [h1, h2] at hd
      refine ⟨?_, ?_⟩
      · intro hnn
        rw [printWalk_altE]
        have hnn' : nullableE a = false ∧ nullableE b = false := by
          have : nullableE (GrammarE.altE a b) = false := hnn
          simp only [nullableE, Bool.or_eq_false_iff] at this
          exact this
        cases hd1 : valueOkWalk a x (fun y path => Hb y (.altL path)) with
        | true =>
            rw [if_pos rfl]
            exact (iha x _ _ fs hd1 HSBA).1 hnn'.1
        | false =>
            rw [if_neg (show ¬ ((false : Bool) = true) from by simp)]
            exact (ihb x _ _ fs (hb2_of hd1) HSBB).1 hnn'.2
      · intro hne cs
        rw [printWalk_altE] at hne ⊢
        cases hd1 : valueOkWalk a x (fun y path => Hb y (.altL path)) with
        | true =>
            rw [if_pos hd1] at hne
            rw [if_pos (show (true : Bool) = true from rfl)]
            obtain ⟨h, hmem, hm⟩ := (iha x _ _ fs hd1 HSBA).2 hne cs
            exact ⟨h, List.mem_append_left _ hmem, hm⟩
        | false =>
            rw [if_neg (by simp [hd1])] at hne
            rw [if_neg (show ¬((false : Bool) = true) from by simp)]
            obtain ⟨h, hmem, hm⟩ := (ihb x _ _ fs (hb2_of hd1) HSBB).2 hne cs
            exact ⟨h, List.mem_append_right _ hmem, hm⟩
  | repE a iha =>
      intro xs Hb H fs hok HSB
      have hokAll : ∀ z (hz : z ∈ xs),
          valueOkWalk a z (fun y path => Hb y (.repP hz path)) = true := by
        have := hok
        rw [valueOkWalk_repE] at this
        exact allWalk_true xs _ this
      have HSBel : ∀ z (hz : z ∈ xs) y (path : SelfPathE a z y),
          (fun y path => Hb y (.repP hz path)) y path = true →
          ((fun y path => H y (.repP hz path)) y path ≠ "") ∧
          ∀ cs, ∃ h ∈ fs, h.matches (((fun y path => H y (.repP hz path)) y path).toList ++ cs)
            = true :=
        fun z hz y path h => HSB y (.repP hz path) h
      refine ⟨?_, ?_⟩
      · intro hnn
        simp [nullableE] at hnn
      · intro hne cs
        rw [printWalk_repE] at hne ⊢
        exact printList_head xs _
          (fun z hz hz0 => (iha z _ _ fs (hokAll z hz) (HSBel z hz)).2 hz0) hne cs
  | optE a iha =>
      intro x Hb H fs hok HSB
      refine ⟨?_, ?_⟩
      · intro hnn
        simp [nullableE] at hnn
      · intro hne cs
        cases x with
        | none =>
            rw [printWalk_optE_none] at hne
            exact absurd rfl hne
        | some z =>
            rw [printWalk_optE_some] at hne ⊢
            have hok' : valueOkWalk a z (fun y path => Hb y (.optP path)) = true := by
              have := hok
              rw [valueOkWalk_optE_some] at this
              exact this
            obtain ⟨h, hmem, hm⟩ := (iha z _ _ fs hok'
              (fun y path h => HSB y (.optP path) h)).2 hne cs
            exact ⟨h, hmem, hm⟩
  | labelE n a iha =>
      intro x Hb H fs hok HSB
      have hok' : valueOkWalk a x (fun y path => Hb y (.labelP path)) = true := by
        have := hok
        rw [valueOkWalk_labelE] at this
        exact this
      obtain ⟨ne1, hd1⟩ := iha x _ _ fs hok' (fun y path h => HSB y (.labelP path) h)
      refine ⟨?_, ?_⟩
      · intro hnn
        rw [printWalk_labelE]
        exact ne1 hnn
      · intro hne cs
        rw [printWalk_labelE] at hne ⊢
        exact hd1 hne cs
  | relE mm owns don ex nm vld sub ih =>
      intro x Hb H fs hok HSB
      have hok2 : owns x = true ∧
          valueOkWalk sub (mm.encode x) (fun y path => Hb y (.relP path)) = true := by
        have h3 := hok
        rw [valueOkWalk_relE] at h3
        exact Eq.mp (Bool.and_eq_true _ _) h3
      have hok' := hok2.2
      obtain ⟨ne1, hd1⟩ := ih (mm.encode x) _ _ fs hok'
        (fun y path h => HSB y (.relP path) h)
      refine ⟨?_, ?_⟩
      · intro hnn
        rw [printWalk_relE]
        exact ne1 hnn
      · intro hne cs
        rw [printWalk_relE] at hne ⊢
        exact hd1 hne cs
  | selfE =>
      intro x Hb H fs hok HSB
      have hok' : Hb x (.selfP x) = true := hok
      obtain ⟨hne1, hhd1⟩ := HSB x (.selfP x) hok'
      refine ⟨?_, ?_⟩
      · intro _
        rw [printWalk_selfE]
        exact hne1
      · intro _ cs
        rw [printWalk_selfE]
        obtain ⟨h, hmem, hm⟩ := hhd1 cs
        exact ⟨h, hmem, hm⟩

-- the `acc` binder is the induction's own face (`intro x acc; induction acc`)
-- and the statement is byte-pinned by the E/G transfer's consumers
set_option linter.unusedVariables false in
/-- The fix-level print bundle (the AccD instance of printBundleE —
    the HSB is the measure-smaller self-values' own bundles). -/
theorem Grammar.printFixBundle {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x)
    (hn : sb.nullableE = false) (hf : sb.firstE ≠ none) :
    ∀ x (acc : AccD m x), fixValueOk m sb dec x = true →
      (printFix m sb dec x ≠ "") ∧
      ∀ cs, ∃ h ∈ sb.bodyFirsts,
        h.matches ((printFix m sb dec x).toList ++ cs) = true := by
  intro x acc
  induction acc with
  | intro x h ih =>
      intro hok
      have hok' : GrammarE.valueOkWalk sb x (fun y _ => fixValueOk m sb dec y) = true := by
        have h2 := hok
        rw [fixValueOk_unfold] at h2
        exact h2
      have hb := GrammarE.printBundleE sb x
        (fun y _ => fixValueOk m sb dec y) (fun y _ => printFix m sb dec y)
        sb.bodyFirsts hok' (fun y path hok_y => ih y (dec x y path) hok_y)
      have hfs : GrammarE.effFirstE sb.bodyFirsts sb = sb.bodyFirsts :=
        GrammarE.effFirstE_bodyFirsts sb hf
      rw [printFix_unfold]
      constructor
      · exact hb.1 hn
      · intro cs
        obtain ⟨h', hmem, hm⟩ := hb.2 (hb.1 hn) cs
        rw [hfs] at hmem
        exact ⟨h', hmem, hm⟩

/-! ## §2: the parse-side duals -/

/-- The ok-inversion pair (the parse-case splits' shared shape). -/
-- The ok-inversion (ONE copy at the root: both families' proofs
-- consume it — the E/G pair's shared bookkeeping, formerly duplicated
-- as `GrammarE.ok_cur_inv` and `Grammar.ok_cur_inv`).
private theorem ok_cur_inv {A : Type} {w : A × Cursor} {v : A} {c : Cursor}
    (h : (Except.ok w : Except ParseError (A × Cursor)) = Except.ok (v, c)) : w.2 = c :=
  (Prod.mk.inj (Except.ok.inj h)).2

/-! ## §4b: the twin carrier (the E/G law transfer's substrate)

`GrammarE` (open) and `Grammar` (closed) share SEVEN node shapes; the
law pairs (mono/splits/consume/head/exclude/printBundle/print_parse)
were per-node re-proofs differing only in the terminal case — the open
crossing `selfE` vs the closed `fix` (whose arm IS the E-fold:
`parseG (.fix ..) = GrammarE.parseE body body`, a defeq). The carrier
`GG` carries BOTH families' node shapes — the shared nodes ONCE,
`selfG` for the open crossing, `fixG` for the closed one — so each law
is proved ONCE over `GG` and discharged to BOTH families by the
injection bridges (`injE`/`injG` + the fold agreements). The `fixG`
arm delegates to the E-fold directly, which makes the carrier's law
SELF-CONTAINED: the `fixG` case re-enters the carrier's own induction
at the body's E-IMAGE `injE body` — one step smaller under `mu`
(the measure that prices a `fixG` node as its body's image). This is
`junctionEG`'s discharge pattern (closed FROM open), generalized from
the junction to the whole law family. -/

/-- The twin carrier: the shared nodes once, plus the two terminal
cases. `fixG` keeps the closed certificate's data (the measure + the
decrease proof + the E-typed body) — its ARM is the E-fold. -/
inductive GG (R : Type) : Type → Type 1 where
  | atomG : Lexeme A → GG R A
  | seqG : GG R A → GG R B → GG R (A × B)
  | altG : GG R A → GG R A → GG R A
  | repG : GG R A → GG R (List A)
  | optG : GG R A → GG R (Option A)
  | labelG (name : String) : GG R A → GG R A
  | relG (m : Kit.Codec Raw A) (owns : A → Bool)
      (decode_owns : ∀ raw r, m.decode raw = Option.some r → owns r = true)
      (exact : ∀ raw r, m.decode raw = Option.some r → m.encode r = raw)
      (name : String) (valid : List String) : GG R Raw → GG R A
  | selfG : GG R R
  -- the closed terminal: its payload is the FIX's own (auto-bound `a`)
  -- — the closed family's payloads vary per node (seq's children, rel's
  -- raw), so the fix node must not constrain the carrier's self type
  | fixG (measure : a → Nat) (body : GrammarE a a)
      (decrease : ∀ x y, SelfPathE body x y → measure y < measure x) : GG R a

/-- The open family's injection into the carrier. -/
def GG.injE {R : Type} : {A : Type} → GrammarE R A → GG R A :=
  fun {A} g => match g with
  | .atomE L => .atomG L
  | .seqE a b => .seqG (injE a) (injE b)
  | .altE a b => .altG (injE a) (injE b)
  | .repE a => .repG (injE a)
  | .optE a => .optG (injE a)
  | .labelE n a => .labelG n (injE a)
  | .relE m owns don ex nm vld sub => .relG m owns don ex nm vld (injE sub)
  | .selfE => .selfG

/-- The closed family's injection into the carrier (`fix` keeps its
certificate; the body stays an E-value — `fixG`'s arm IS the closed
parser's fix arm, a defeq). The self payload is the grammar's OWN
payload (`fixG`'s certificate is E-typed at it) — so the image lives
at `GG A A`; the closed folds never consult the context outside
`fixG`, whose arm hardcodes the body. -/
def GG.injG {R : Type} : {A : Type} → Grammar A → GG R A :=
  fun {A} g => match g with
  | .atom L => .atomG L
  | .seq a b => .seqG (injG a) (injG b)
  | .alt a b => .altG (injG a) (injG b)
  | .rep a => .repG (injG a)
  | .opt a => .optG (injG a)
  | .label n a => .labelG n (injG a)
  | .rel m owns don ex nm vld sub => .relG m owns don ex nm vld (injG sub)
  | .fix m body dec => .fixG m body dec

/-- The carrier's measure: the same-fuel induction's second dimension.
A `fixG` node is priced as its body's IMAGE plus one — exactly the
one-step room the `fixG` case's re-entry consumes. -/
def GG.nodeCountE {R : Type} : {A : Type} → GrammarE R A → Nat :=
  fun {A} g => match g with
  | .atomE _ => 1
  | .seqE a b => 1 + nodeCountE a + nodeCountE b
  | .altE a b => 1 + nodeCountE a + nodeCountE b
  | .repE a => 1 + nodeCountE a
  | .optE a => 1 + nodeCountE a
  | .labelE _ a => 1 + nodeCountE a
  | .relE _ _ _ _ _ _ sub => 1 + nodeCountE sub
  | .selfE => 1

def GG.mu {R : Type} : {A : Type} → GG R A → Nat :=
  fun {A} g => match g with
  | .atomG _ => 1
  | .seqG a b => 1 + mu a + mu b
  | .altG a b => 1 + mu a + mu b
  | .repG a => 1 + mu a
  | .optG a => 1 + mu a
  | .labelG _ a => 1 + mu a
  | .relG _ _ _ _ _ _ sub => 1 + mu sub
  | .selfG => 1
  | .fixG _ body _ => 1 + nodeCountE body

-- The carrier's parser: the two folds' shared arms once, `selfG`
-- re-entering the context at one less fuel (the open crossing), `fixG`
-- entering the body through the E-fold (the closed arm — the defeq the
-- bridges ride on).
mutual
def GG.parseGG {R A : Type} (sb : GG R R) : GG R A → Nat → GParser A :=
  fun g fuel => match g, fuel with
  | .atomG L, _ => fun cur => L.scan cur
  | .seqG a b, fuel => fun cur =>
      match parseGG sb a fuel cur with
      | .error e => .error e
      | .ok (x, cur1) =>
          match parseGG sb b fuel cur1 with
          | .error e => .error e
          | .ok (y, cur2) => .ok ((x, y), cur2)
  | .altG a b, fuel => fun cur =>
      match parseGG sb a fuel cur with
      | .ok r => .ok r
      | .error e =>
          match parseGG sb b fuel cur with
          | .ok r => .ok r
          | .error e' => .error (ParseError.farther e e')
  | .repG a, fuel => fun cur => parseManyGG sb a fuel cur
  | .optG a, fuel => fun cur =>
      match parseGG sb a fuel cur with
      | .error _ => .ok (Option.none, cur)
      | .ok (x, cur') => .ok (Option.some x, cur')
  | .labelG n a, fuel => fun cur =>
      match parseGG sb a fuel cur with
      | .error e =>
          .error { e with valid := [n], message := s!"expected {n}",
                          context := TextKit.Label.at n :: e.context }
      | .ok r => .ok r
  | .relG m _ _ _ nm vld sub, fuel => fun cur =>
      match parseGG sb sub fuel cur with
      | .error e => .error e
      | .ok (raw, cur') =>
          match m.decode raw with
          | .some r => .ok (r, cur')
          | .none =>
              let got := String.ofList (cur.cs.take (cur.cs.length - cur'.cs.length))
              .error ({ Diag.closedWorld parseCode s!"invalid {nm}" .error got vld
                        with pos := cur.off })
  | .selfG, 0 => fun cur => .error (ParseError.base cur.off ["<recursion limit>"])
  | .selfG, fuel + 1 => fun cur => parseGG sb sb fuel cur
  | .fixG _ body _, fuel => fun cur => GrammarE.parseE body body fuel cur
termination_by g fuel => (fuel, sizeOf g, 0)

/-- The carrier's repetition engine (the two engines' shared shape). -/
def GG.parseManyGG {R A : Type} (sb : GG R R) (a : GG R A) :
    Nat → GParser (List A) :=
  fun fuel cur =>
    match fuel, cur with
    | 0, cur => .ok ([], cur)
    | fuel + 1, cur =>
        match parseGG sb a (fuel + 1) cur with
        | .error _ => .ok ([], cur)
        | .ok (x, cur') =>
            if cur'.cs.length < cur.cs.length then
              match parseManyGG sb a fuel cur' with
              | .ok (xs, cur'') => .ok (x :: xs, cur'')
              | .error e => .error e
            else .ok ([x], cur')
termination_by fuel => (fuel, sizeOf a, 1)
end

/-- The open fold's agreement: `parseE` IS the carrier's parse at the
injection. Strong fuel induction (the `selfE` crossing re-enters at
the same grammar), structural inside; the second conjunct carries the
repetition engine's agreement (the `repE` arm IS the engine — the
carrier's `repG` arm too — so the pair shares one induction). -/
theorem GrammarE.parseE_inj :
    ∀ (fuel : Nat) {R : Type} (sb : GrammarE R R) {A : Type} (g : GrammarE R A),
      sb.parseE g fuel = GG.parseGG (GG.injE sb) (GG.injE g) fuel
      ∧ (∀ f, f ≤ fuel →
          sb.parseManyE g f = GG.parseManyGG (GG.injE sb) (GG.injE g) f) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      intro R sb A g
      have hEall : ∀ {C : Type} (t : GrammarE R C),
          sb.parseE t F = GG.parseGG (GG.injE sb) (GG.injE t) F := by
        intro C t
        induction t with
        | atomE L => simp only [GrammarE.parseE, GG.parseGG, GG.injE]
        | seqE a b iha ihb =>
            simp only [GrammarE.parseE, GG.parseGG, GG.injE, iha, ihb]; rfl
        | altE a b iha ihb =>
            simp only [GrammarE.parseE, GG.parseGG, GG.injE, iha, ihb]; rfl
        | repE a iha =>
            have hmany : sb.parseManyE a F =
                GG.parseManyGG (GG.injE sb) (GG.injE a) F := by
              funext cur
              cases F with
              | zero => simp only [GrammarE.parseManyE, GG.parseManyGG]
              | succ f =>
                  have hm := (IH f (Nat.lt_succ_self f) sb a).2 f (Nat.le_refl f)
                  simp only [GrammarE.parseManyE, GG.parseManyGG, iha, hm]; rfl
            simp only [GrammarE.parseE, GG.injE, GG.parseGG, hmany]
        | optE a iha =>
            simp only [GrammarE.parseE, GG.parseGG, GG.injE, iha]; rfl
        | labelE n a iha =>
            simp only [GrammarE.parseE, GG.parseGG, GG.injE, iha]; rfl
        | relE m owns don ex nm vld sub ih =>
            simp only [GrammarE.parseE, GG.parseGG, GG.injE, ih]; rfl
        | selfE =>
            funext cur
            cases F with
            | zero => simp only [GrammarE.parseE, GG.parseGG, GG.injE]
            | succ f =>
                simp only [GrammarE.parseE, GG.parseGG, GG.injE]
                exact congrFun (IH f (Nat.lt_succ_self f) sb sb).1 cur
      refine ⟨hEall g, ?_⟩
      intro f hf
      cases f with
      | zero =>
          funext cur
          simp only [GrammarE.parseManyE, GG.parseManyGG]
      | succ f' =>
          have hE : sb.parseE g (f' + 1) =
              GG.parseGG (GG.injE sb) (GG.injE g) (f' + 1) := by
            match Nat.eq_or_lt_of_le hf with
            | .inl he => rw [he]; exact hEall g
            | .inr hlt => exact (IH (f' + 1) (by omega) sb g).1
          have hmany : sb.parseManyE g f' =
              GG.parseManyGG (GG.injE sb) (GG.injE g) f' :=
            (IH f' (by omega) sb g).2 f' (Nat.le_refl f')
          funext cur
          simp only [GrammarE.parseManyE, GG.parseManyGG, hE, hmany]; rfl

/-- The image's measure IS the body's node count (the `fixG` case's
re-entry consumes exactly the one-step room `mu` prices the node). -/
theorem GG.mu_injE {R : Type} : {A : Type} → (g : GrammarE R A) → GG.mu (GG.injE g) = GG.nodeCountE g := by
  intro A g
  induction g with
  | atomE _ => simp [GG.injE, GG.mu, GG.nodeCountE]
  | seqE a b iha ihb => simp [GG.injE, GG.mu, GG.nodeCountE, iha, ihb]
  | altE a b iha ihb => simp [GG.injE, GG.mu, GG.nodeCountE, iha, ihb]
  | repE a iha => simp [GG.injE, GG.mu, GG.nodeCountE, iha]
  | optE a iha => simp [GG.injE, GG.mu, GG.nodeCountE, iha]
  | labelE _ a iha => simp [GG.injE, GG.mu, GG.nodeCountE, iha]
  | relE _ _ _ _ _ _ sub ih => simp [GG.injE, GG.mu, GG.nodeCountE, ih]
  | selfE => simp [GG.injE, GG.mu, GG.nodeCountE]

/-- The closed engine's agreement (the engine recursion needs the
element fold's agreement only — no circularity with the main bridge). -/
theorem Grammar.parseManyG_inj {R : Type} (c : GG R R) {A : Type} (g : Grammar A)
    (hP : ∀ fuel, parseG g fuel = GG.parseGG c (GG.injG g) fuel) :
    ∀ f, parseManyG g f = GG.parseManyGG c (GG.injG g) f := by
  intro f
  induction f with
  | zero => funext cur; simp only [Grammar.parseManyG, GG.parseManyGG]
  | succ f ih =>
      funext cur
      simp only [Grammar.parseManyG, GG.parseManyGG, hP, ih]; rfl

/-- The closed fold's agreement: `parseG` IS the carrier's parse at
the injection (ANY context — the closed image never consults it: the
`fixG` arm hardcodes the body). -/
theorem Grammar.parseG_inj {R : Type} (c : GG R R) :
    ∀ {A : Type} (g : Grammar A) (fuel : Nat),
      parseG g fuel = GG.parseGG c (GG.injG g) fuel := by
  intro A g
  induction g with
  | atom L => intro fuel; funext cur; simp only [Grammar.parseG, GG.parseGG, GG.injG]
  | seq a b iha ihb =>
      intro fuel; funext cur
      simp only [Grammar.parseG, GG.parseGG, GG.injG, iha, ihb]; rfl
  | alt a b iha ihb =>
      intro fuel; funext cur
      simp only [Grammar.parseG, GG.parseGG, GG.injG, iha, ihb]; rfl
  | rep a ih =>
      intro fuel; funext cur
      have hm := parseManyG_inj c a ih fuel
      simp only [Grammar.parseG, GG.parseGG, GG.injG, hm]
  | opt a ih =>
      intro fuel; funext cur
      simp only [Grammar.parseG, GG.parseGG, GG.injG, ih]; rfl
  | label n a ih =>
      intro fuel; funext cur
      simp only [Grammar.parseG, GG.parseGG, GG.injG, ih]; rfl
  | rel m owns don ex nm vld sub ih =>
      intro fuel; funext cur
      simp only [Grammar.parseG, GG.parseGG, GG.injG, ih]; rfl
  | fix m body dec =>
      intro fuel; funext cur
      simp only [Grammar.parseG, GG.parseGG, GG.injG]

/-- THE carrier's monotonicity — the mono case table PROVED ONCE (the
two families' per-node re-proofs differ only in the terminal case:
`selfG` re-enters the context at one less fuel; `fixG` enters the body
through the E-fold, whose agreement (`parseE_inj`) re-enters THIS
induction at the body's image — one step smaller under `mu`). Both
family laws below are one-line discharges through the bridges. -/
theorem GG.parseMonoGG :
    ∀ (fuel : Nat) {R : Type} (sb : GG R R) {A : Type} (g : GG R A),
      ∀ {x : A} {cur cur' : Cursor},
      parseGG sb g fuel cur = .ok (x, cur') → cur'.cs.length ≤ cur.cs.length := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      have key : ∀ (n : Nat) {R : Type} (sb : GG R R) {A : Type} (g : GG R A),
          GG.mu g < n → ∀ {x : A} {cur cur' : Cursor},
          parseGG sb g F cur = .ok (x, cur') → cur'.cs.length ≤ cur.cs.length := by
        intro n
        induction n with
        | zero => intro R sb A g hn; exact absurd hn (Nat.not_lt_zero _)
        | succ n IHn =>
            intro R sb A g
            cases g with
            | atomG L =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                exact Nat.le_of_lt (L.consumes _ _ _ h)
            | seqG a b =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu a < n ∧ GG.mu b < n := by
                  simp [GG.mu] at hn; exact ⟨by omega, by omega⟩
                cases ha : parseGG sb a F cur with
                | error e => simp only [ha] at h; simp at h
                | ok r =>
                    obtain ⟨x₁, cur₁⟩ := r
                    cases hb : parseGG sb b F cur₁ with
                    | error e => simp only [ha, hb] at h; simp at h
                    | ok r₂ =>
                        obtain ⟨y, cur₂⟩ := r₂
                        simp only [ha, hb] at h
                        rw [← ok_cur_inv h]
                        exact Nat.le_trans (IHn sb b hna.2 hb)
                          (IHn sb a hna.1 ha)
            | altG a b =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu a < n ∧ GG.mu b < n := by
                  simp [GG.mu] at hn; exact ⟨by omega, by omega⟩
                cases ha : parseGG sb a F cur with
                | ok r =>
                    obtain ⟨x₁, cur₁⟩ := r
                    simp only [ha] at h
                    rw [← ok_cur_inv h]
                    exact IHn sb a hna.1 ha
                | error e =>
                    simp only [ha] at h
                    cases hb : parseGG sb b F cur with
                    | ok r =>
                        obtain ⟨x₂, cur₂⟩ := r
                        simp only [hb] at h
                        rw [← ok_cur_inv h]
                        exact IHn sb b hna.2 hb
                    | error e' => simp only [hb] at h; simp at h
            | repG a =>
                intro hn xs cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu a < n := by simp [GG.mu] at hn; omega
                have manyMono : ∀ f, f ≤ F → ∀ ys c c',
                    parseManyGG sb a f c = .ok (ys, c') → c'.cs.length ≤ c.cs.length := by
                  intro f
                  induction f with
                  | zero =>
                      intro hf ys c c' h0
                      simp only [parseManyGG] at h0
                      rw [← ok_cur_inv h0]
                      exact Nat.le_refl _
                  | succ f ih' =>
                      intro hf ys c c' h0
                      simp only [parseManyGG] at h0
                      cases hb : parseGG sb a (f+1) c with
                      | error e =>
                          simp only [hb] at h0
                          rw [← ok_cur_inv h0]
                          exact Nat.le_refl _
                      | ok r =>
                          obtain ⟨z, c₁⟩ := r
                          simp only [hb] at h0
                          have hbody : c₁.cs.length ≤ c.cs.length := by
                            by_cases hf1 : f + 1 = F
                            · subst hf1
                              exact IHn sb a hna hb
                            · exact IH (f+1) (by omega) sb a hb
                          by_cases hprog : c₁.cs.length < c.cs.length
                          · rw [if_pos hprog] at h0
                            cases hr : parseManyGG sb a f c₁ with
                            | error e => simp [hr] at h0
                            | ok r₂ =>
                                obtain ⟨zs, c₂⟩ := r₂
                                simp only [hr] at h0
                                rw [← ok_cur_inv h0]
                                exact Nat.le_trans (ih' (by omega) zs c₁ c₂ hr) hbody
                          · rw [if_neg hprog] at h0
                            rw [← ok_cur_inv h0]
                            exact hbody
                exact manyMono F (Nat.le_refl F) xs cur cur' h
            | optG a =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu a < n := by simp [GG.mu] at hn; omega
                cases ha : parseGG sb a F cur with
                | error e =>
                    simp only [ha] at h
                    rw [← ok_cur_inv h]
                    exact Nat.le_refl _
                | ok r =>
                    obtain ⟨z, c₁⟩ := r
                    simp only [ha] at h
                    rw [← ok_cur_inv h]
                    exact IHn sb a hna ha
            | labelG nm a =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu a < n := by simp [GG.mu] at hn; omega
                cases ha : parseGG sb a F cur with
                | error e => simp [ha] at h
                | ok r =>
                    obtain ⟨z, c₁⟩ := r
                    simp only [ha] at h
                    simp only [Except.ok.injEq, Prod.mk.injEq] at h
                    rw [← h.2]
                    exact IHn sb a hna ha
            | relG mm owns don ex nm vld sub =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu sub < n := by simp [GG.mu] at hn; omega
                cases ha : parseGG sb sub F cur with
                | error e => simp only [ha] at h; simp at h
                | ok r =>
                    obtain ⟨raw, c₁⟩ := r
                    simp only [ha] at h
                    cases hd : mm.decode raw with
                    | none => simp [hd] at h
                    | some r =>
                        simp only [hd] at h
                        rw [← ok_cur_inv h]
                        exact IHn sb sub hna ha
            | selfG =>
                intro hn x cur cur' h
                cases F with
                | zero => simp [parseGG] at h
                | succ f =>
                    simp only [parseGG] at h
                    exact IH f (Nat.lt_succ_self f) sb sb h
            | fixG m body dec =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hE := (GrammarE.parseE_inj F body body).1
                rw [hE] at h
                have hna : GG.mu (GG.injE body) < n := by
                  rw [GG.mu_injE]
                  simp [GG.mu] at hn; omega
                exact IHn (GG.injE body) (GG.injE body) hna h
      intro R sb A g
      exact key (GG.mu g + 1) sb g (by omega)


theorem GrammarE.parseMonoE {R : Type} (sb : GrammarE R R) :
    ∀ (fuel : Nat) {A : Type} {g : GrammarE R A} {x : A} {cur cur' : Cursor},
      parseE sb g fuel cur = .ok (x, cur') → cur'.cs.length ≤ cur.cs.length := by
    -- THE TRANSFER: discharged from the carrier's law (GG.parseMonoGG) at the
    -- open injection — the E case table lives ONCE in the carrier.
    intro fuel A g x cur cur' h
    rw [(parseE_inj fuel sb g).1] at h
    exact GG.parseMonoGG fuel (GG.injE sb) (GG.injE g) h
theorem GrammarE.parseMonoManyE {R : Type} (sb : GrammarE R R)
    {A : Type} (a : GrammarE R A) :
    ∀ (fuel : Nat) {xs : List A} {cur cur' : Cursor},
      parseManyE sb a fuel cur = .ok (xs, cur') → cur'.cs.length ≤ cur.cs.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs cur cur' h
      simp only [parseManyE] at h
      rw [← ok_cur_inv h]
      exact Nat.le_refl _
  | succ f ih =>
      intro xs cur cur' h
      simp only [parseManyE] at h
      cases hb : parseE sb a (f+1) cur with
      | error e =>
          simp only [hb] at h
          rw [← ok_cur_inv h]
          exact Nat.le_refl _
      | ok r =>
          obtain ⟨z, c₁⟩ := r
          simp only [hb] at h
          have hbody : c₁.cs.length ≤ cur.cs.length := parseMonoE sb (f+1) hb
          by_cases hprog : c₁.cs.length < cur.cs.length
          · rw [if_pos hprog] at h
            cases hr : parseManyE sb a f c₁ with
            | error e => simp [hr] at h
            | ok r₂ =>
                obtain ⟨zs, c₂⟩ := r₂
                simp only [hr] at h
                rw [← ok_cur_inv h]
                exact Nat.le_trans (ih hr) hbody
          · rw [if_neg hprog] at h
            rw [← ok_cur_inv h]
            exact hbody

/-- The carrier's nullability (the two folds' shared arms once; the
    `fixG` arm is the E-body's own fold — the closed `nullable
    (.fix ..) = body.nullableE` defeq). -/
def GG.nullableGG {R : Type} : {A : Type} → GG R A → Bool :=
  fun {A} g => match g with
  | .atomG _ => false
  | .seqG a b => nullableGG a && nullableGG b
  | .altG a b => nullableGG a || nullableGG b
  | .repG _ => true
  | .optG _ => true
  | .labelG _ a => nullableGG a
  | .relG _ _ _ _ _ _ sub => nullableGG sub
  | .selfG => false
  | .fixG _ body _ => GrammarE.nullableE body

/-- The open fold's nullability agreement. -/
theorem GG.nullableE_injE {R : Type} : {A : Type} → (g : GrammarE R A) →
    GrammarE.nullableE g = GG.nullableGG (GG.injE g) := by
  intro A g
  induction g with
  | atomE _ => rfl
  | seqE a b iha ihb => simp [GrammarE.nullableE, GG.injE, GG.nullableGG, iha, ihb]
  | altE a b iha ihb => simp [GrammarE.nullableE, GG.injE, GG.nullableGG, iha, ihb]
  | repE _ => rfl
  | optE _ => rfl
  | labelE _ a iha => simp [GrammarE.nullableE, GG.injE, GG.nullableGG, iha]
  | relE _ _ _ _ _ _ sub ih => simp [GrammarE.nullableE, GG.injE, GG.nullableGG, ih]
  | selfE => rfl

/-- The closed fold's nullability agreement (the `fix` arm IS the
    E-body's fold — a defeq). -/
theorem GG.nullableG_injG : ∀ {A : Type} (g : Grammar A) (R : Type),
    Grammar.nullable g = GG.nullableGG (GG.injG (R := R) g) := by
  intro A g
  induction g with
  | atom _ => intro R; rfl
  | seq a b iha ihb =>
      intro R
      simp only [Grammar.nullable, GG.injG, GG.nullableGG]
      rw [iha R, ihb R]
  | alt a b iha ihb =>
      intro R
      simp only [Grammar.nullable, GG.injG, GG.nullableGG]
      rw [iha R, ihb R]
  | rep _ => intro R; rfl
  | opt _ => intro R; rfl
  | label _ a iha => intro R; exact iha R
  | rel _ _ _ _ _ _ sub ih =>
      intro R; exact ih R
  | fix _ _ _ => intro R; rfl

/-- THE carrier's consumption lemma — the consume case table PROVED
    ONCE (the pairs' shared content; the terminal cases as in
    `parseMonoGG`: the `selfG` crossing consumes the CONTEXT's
    non-nullability, the `fixG` case re-enters at the body's image —
    whose nullability is the node's own premise via the fold
    agreement). Both family laws below are one-line discharges through
    the bridges. -/
theorem GG.parseConsumeGG :
    ∀ (fuel : Nat) {R : Type} (sb : GG R R), nullableGG sb = false →
      ∀ {A : Type} (g : GG R A) {x : A} {cur cur' : Cursor},
      parseGG sb g fuel cur = .ok (x, cur') →
      nullableGG g = false → cur'.cs.length < cur.cs.length := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      have key : ∀ (n : Nat) {R : Type} (sb : GG R R), nullableGG sb = false →
          {A : Type} → (g : GG R A) → GG.mu g < n → ∀ {x : A} {cur cur' : Cursor},
          parseGG sb g F cur = .ok (x, cur') →
          nullableGG g = false → cur'.cs.length < cur.cs.length := by
        intro n
        induction n with
        | zero => intro R sb _ A g hn; exact absurd hn (Nat.not_lt_zero _)
        | succ n IHn =>
            intro R sb hsb A g
            cases g with
            | atomG L =>
                intro hn x cur cur' h _
                simp only [parseGG] at h
                exact L.consumes _ _ _ h
            | seqG a b =>
                intro hn x cur cur' h hnn
                simp only [parseGG] at h
                have hmu : GG.mu a < n ∧ GG.mu b < n := by
                  simp [GG.mu] at hn; exact ⟨by omega, by omega⟩
                have hnn' : (nullableGG a && nullableGG b) = false := hnn
                cases ha : parseGG sb a F cur with
                | error e => simp only [ha] at h; simp at h
                | ok r =>
                    obtain ⟨x₁, cur₁⟩ := r
                    cases hb : parseGG sb b F cur₁ with
                    | error e => simp only [ha, hb] at h; simp at h
                    | ok r₂ =>
                        obtain ⟨y, cur₂⟩ := r₂
                        simp only [ha, hb] at h
                        rw [← ok_cur_inv h]
                        cases hna : nullableGG a with
                        | false =>
                            have h1 : cur₁.cs.length < cur.cs.length :=
                              IHn sb hsb a hmu.1 ha hna
                            have h2 : cur₂.cs.length ≤ cur₁.cs.length :=
                              GG.parseMonoGG F sb b hb
                            exact Nat.lt_of_le_of_lt h2 h1
                        | true =>
                            have hnb : nullableGG b = false := by
                              cases h2 : nullableGG b with
                              | true => simp [hna, h2] at hnn'
                              | false => rfl
                            have h1 : cur₁.cs.length ≤ cur.cs.length :=
                              GG.parseMonoGG F sb a ha
                            have h2 : cur₂.cs.length < cur₁.cs.length :=
                              IHn sb hsb b hmu.2 hb hnb
                            exact Nat.lt_of_lt_of_le h2 h1
            | altG a b =>
                intro hn x cur cur' h hnn
                simp only [parseGG] at h
                have hmu : GG.mu a < n ∧ GG.mu b < n := by
                  simp [GG.mu] at hn; exact ⟨by omega, by omega⟩
                have hnn' : (nullableGG a || nullableGG b) = false := hnn
                simp only [Bool.or_eq_false_iff] at hnn'
                cases ha : parseGG sb a F cur with
                | ok r =>
                    obtain ⟨x₁, cur₁⟩ := r
                    simp only [ha] at h
                    rw [← ok_cur_inv h]
                    exact IHn sb hsb a hmu.1 ha hnn'.1
                | error e =>
                    simp only [ha] at h
                    cases hb : parseGG sb b F cur with
                    | ok r =>
                        obtain ⟨x₂, cur₂⟩ := r
                        simp only [hb] at h
                        rw [← ok_cur_inv h]
                        exact IHn sb hsb b hmu.2 hb hnn'.2
                    | error e' => simp only [hb] at h; simp at h
            | repG a =>
                intro hn x cur cur' h hnn
                simp [GG.nullableGG] at hnn
            | optG a =>
                intro hn x cur cur' h hnn
                simp [GG.nullableGG] at hnn
            | labelG nm a =>
                intro hn x cur cur' h hnn
                simp only [parseGG] at h
                have hmu : GG.mu a < n := by simp [GG.mu] at hn; omega
                cases ha : parseGG sb a F cur with
                | error e => simp [ha] at h
                | ok r =>
                    obtain ⟨z, c₁⟩ := r
                    simp only [ha] at h
                    simp only [Except.ok.injEq, Prod.mk.injEq] at h
                    rw [← h.2]
                    exact IHn sb hsb a hmu ha hnn
            | relG mm owns don ex nm vld sub =>
                intro hn x cur cur' h hnn
                simp only [parseGG] at h
                have hmu : GG.mu sub < n := by simp [GG.mu] at hn; omega
                cases ha : parseGG sb sub F cur with
                | error e => simp only [ha] at h; simp at h
                | ok r =>
                    obtain ⟨raw, c₁⟩ := r
                    simp only [ha] at h
                    cases hd : mm.decode raw with
                    | none => simp [hd] at h
                    | some r =>
                        simp only [hd] at h
                        rw [← ok_cur_inv h]
                        exact IHn sb hsb sub hmu ha hnn
            | selfG =>
                intro hn x cur cur' h _
                cases F with
                | zero => simp [parseGG] at h
                | succ f =>
                    simp only [parseGG] at h
                    exact IH f (Nat.lt_succ_self f) sb hsb sb h hsb
            | fixG m body dec =>
                intro hn x cur cur' h hnn
                simp only [parseGG] at h
                have hE := (GrammarE.parseE_inj F body body).1
                rw [hE] at h
                have hmu : GG.mu (GG.injE body) < n := by
                  rw [GG.mu_injE]
                  simp [GG.mu] at hn; omega
                have hnnE : nullableGG (GG.injE body) = false := by
                  rw [← GG.nullableE_injE body]
                  exact hnn
                exact IHn (GG.injE body) hnnE (GG.injE body) hmu h hnnE
      intro R sb hsb A g
      exact key (GG.mu g + 1) sb hsb g (by omega)

/-- The consumption lemma (the rep-progress content): a non-nullable
    grammar's success shortens the input — the body's own
    non-nullability (`hn`, the strengthened WF-FIX row) is what the
    selfE crossing consumes. THE TRANSFER: discharged from the
    carrier's law at the open injection — the E case table lives ONCE
    in the carrier. -/
theorem GrammarE.parseConsumeE {R : Type} (sb : GrammarE R R)
    (hn : sb.nullableE = false) :
    ∀ (fuel : Nat) {A : Type} {g : GrammarE R A} {x : A} {cur cur' : Cursor},
      parseE sb g fuel cur = .ok (x, cur') →
      nullableE g = false → cur'.cs.length < cur.cs.length := by
  intro fuel A g x cur cur' h hnn
  rw [(parseE_inj fuel sb g).1] at h
  rw [GG.nullableE_injE sb] at hn
  rw [GG.nullableE_injE g] at hnn
  exact GG.parseConsumeGG fuel (GG.injE sb) hn (GG.injE g) h hnn

/-! ## §3: law 2 (exactness), open level -/

/-- The branch-coherence fold (law 2's alt content — the wave's
    documented delta from the design's "unconditional" claim: the
    printed branch is chosen by `valueOk`, the parsed branch by the
    text; exactness needs them to agree, and a first-disjoint grammar
    can still overlap VALUES through its rel codecs — the premise is
    semantic, the migration targets discharge it by ctor
    discrimination). Path-free handlers (the liftings agree by
    `valueOkWalk_congr`). -/
def GrammarE.altCoherentE {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) :
    {A : Type} → GrammarE R A → Prop :=
  fun {_} g => match g with
  | .atomE _ => True
  | .seqE a b => altCoherentE m sb dec a ∧ altCoherentE m sb dec b
  | .altE a b =>
      (∀ x, valueOkWalk a x (fun y _ => Grammar.fixValueOk m sb dec y) = true →
        valueOkWalk b x (fun y _ => Grammar.fixValueOk m sb dec y) = false) ∧
      altCoherentE m sb dec a ∧ altCoherentE m sb dec b
  | .repE a => altCoherentE m sb dec a
  | .optE a => altCoherentE m sb dec a
  | .labelE _ a => altCoherentE m sb dec a
  | .relE _ _ _ _ _ _ sub => altCoherentE m sb dec sub
  | .selfE => True

/-- The closed branch-coherence fold. -/
def Grammar.altCoherent : {A : Type} → Grammar A → Prop :=
  fun {_} g => match g with
  | .atom _ => True
  | .seq a b => altCoherent a ∧ altCoherent b
  | .alt a b =>
      (∀ x, valueOk a x = true → valueOk b x = false) ∧
      altCoherent a ∧ altCoherent b
  | .rep a => altCoherent a
  | .opt a => altCoherent a
  | .label _ a => altCoherent a
  | .rel _ _ _ _ _ _ sub => altCoherent sub
  | .fix m body dec => GrammarE.altCoherentE m body dec body

open Grammar in
/-- THE exactness law, open level (design §3.3): a successful parse
    consumed EXACTLY the print of its result — the two conjuncts plus
    the parsed-values-are-owned third. NO certificate premise (the
    leaf/rel fields carry it); the coherence premise is the alt
    branch-agreement (see `altCoherentE`). The repE case is an inner
    induction on the repetition fuel. -/
theorem GrammarE.print_parse_E {R : Type} (sb : GrammarE R R) (m : R → Nat)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x)
    (hcoh : GrammarE.altCoherentE m sb dec sb) :
    ∀ (fuel : Nat) {A : Type} {g : GrammarE R A} {x : A} {cur cur' : Cursor},
      altCoherentE m sb dec g →
      parseE sb g fuel cur = .ok (x, cur') →
      cur.cs = (printWalk g x (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => printFix m sb dec y)).toList ++ cur'.cs ∧
      cur'.off = cur.off + (printWalk g x (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => printFix m sb dec y)).length ∧
      valueOkWalk g x (fun y _ => Grammar.fixValueOk m sb dec y) = true := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      intro A g
      induction g with
      | atomE L =>
          intro x cur cur' _ h
          simp only [parseE] at h
          rw [printWalk_atomE]
          exact ⟨L.scan_exact _ _ _ h, L.scan_off _ _ _ h, L.scan_post _ _ _ h⟩
      | seqE a b iha ihb =>
          intro x cur cur' hco h
          obtain ⟨hcohA, hcohB⟩ := hco
          simp only [parseE] at h
          cases ha : parseE sb a F cur with
          | error e => simp only [ha] at h; simp at h
          | ok r =>
              obtain ⟨x₁, cur₁⟩ := r
              cases hb : parseE sb b F cur₁ with
              | error e => simp only [ha, hb] at h; simp at h
              | ok r₂ =>
                  obtain ⟨y, cur₂⟩ := r₂
                  simp only [ha, hb] at h
                  have hcc := Prod.mk.inj (Except.ok.inj h)
                  obtain ⟨hx1, hx2, hx3⟩ := iha hcohA ha
                  obtain ⟨hy1, hy2, hy3⟩ := ihb hcohB hb
                  rw [← hcc.1, ← hcc.2]
                  rw [printWalk_seqE]
                  have hbrA : printWalk a x₁ (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => printFix m sb dec y) =
                      printWalk a x₁
                        (fun y' path => Grammar.fixValueOk m sb dec y')
                        (fun y' path => printFix m sb dec y') :=
                    printWalk_congr a x₁ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
                  have hbrB : printWalk b y (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => printFix m sb dec y) =
                      printWalk b y
                        (fun y' path => Grammar.fixValueOk m sb dec y')
                        (fun y' path => printFix m sb dec y') :=
                    printWalk_congr b y _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
                  rw [← hbrA, ← hbrB]
                  have hbrAB : valueOkWalk a x₁
                      (fun y' path => Grammar.fixValueOk m sb dec y') =
                      valueOkWalk a x₁ (fun y _ => Grammar.fixValueOk m sb dec y) :=
                    valueOkWalk_congr a x₁ _ _ (fun _ _ => rfl)
                  have hbrBB : valueOkWalk b y
                      (fun y' path => Grammar.fixValueOk m sb dec y') =
                      valueOkWalk b y (fun y _ => Grammar.fixValueOk m sb dec y) :=
                    valueOkWalk_congr b y _ _ (fun _ _ => rfl)
                  refine ⟨?_, ?_, ?_⟩
                  · rw [hx1, hy1, String.toList_append, List.append_assoc]
                  · rw [hy2, hx2, String.length_append]
                    omega
                  · rw [valueOkWalk_seqE, ← hbrAB, ← hbrBB]
                    simp [hx3, hy3]
      | altE a b iha ihb =>
          intro x cur cur' hco h
          obtain ⟨hcohab, hcohA, hcohB⟩ := hco
          simp only [parseE] at h
          cases ha : parseE sb a F cur with
          | ok r =>
              obtain ⟨x₁, cur₁⟩ := r
              simp only [ha] at h
              have hcc := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨hx1, hx2, hx3⟩ := iha hcohA ha
              rw [← hcc.1, ← hcc.2]
              rw [printWalk_altE]
              have hd : valueOkWalk a x₁ (fun y path =>
                  Grammar.fixValueOk m sb dec y) = true := by
                have h2 := hx3
                rw [valueOkWalk_congr a x₁ _ _ (fun y path => rfl :
                  ∀ y path, (fun y' _ => Grammar.fixValueOk m sb dec y') y path =
                    (fun y' path => Grammar.fixValueOk m sb dec y') y path)] at h2
                exact h2
              rw [if_pos hd]
              have hbrA : printWalk a x₁ (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => printFix m sb dec y) =
                  printWalk a x₁
                    (fun y' path => Grammar.fixValueOk m sb dec y')
                    (fun y' path => printFix m sb dec y') :=
                printWalk_congr a x₁ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
              rw [← hbrA]
              refine ⟨hx1, hx2, ?_⟩
              rw [valueOkWalk_altE]
              simp [hx3]
          | error e =>
              simp only [ha] at h
              cases hb : parseE sb b F cur with
              | ok r =>
                  obtain ⟨x₂, cur₂⟩ := r
                  simp only [hb] at h
                  have hcc := Prod.mk.inj (Except.ok.inj h)
                  obtain ⟨hx1, hx2, hx3⟩ := ihb hcohB hb
                  rw [← hcc.1, ← hcc.2]
                  rw [printWalk_altE]
                  have hbB : valueOkWalk b x₂ (fun y _ =>
                      Grammar.fixValueOk m sb dec y) = true := by
                    have h2 := hx3
                    rw [valueOkWalk_congr b x₂ _ _ (fun y path => rfl :
                      ∀ y path, (fun y' _ => Grammar.fixValueOk m sb dec y') y path =
                        (fun y' path => Grammar.fixValueOk m sb dec y') y path)] at h2
                    exact h2
                  have hdA : valueOkWalk a x₂ (fun y _ =>
                      Grammar.fixValueOk m sb dec y) = false := by
                    cases hda : valueOkWalk a x₂ (fun y _ => Grammar.fixValueOk m sb dec y) with
                    | true =>
                        have := hcohab x₂ hda
                        simp [hbB] at this
                    | false => rfl
                  have hd : valueOkWalk a x₂ (fun y path =>
                      Grammar.fixValueOk m sb dec y) = false := by
                    have h2 := hdA
                    rw [valueOkWalk_congr a x₂ _ _ (fun y path => rfl :
                      ∀ y path, (fun y' _ => Grammar.fixValueOk m sb dec y') y path =
                        (fun y' path => Grammar.fixValueOk m sb dec y') y path)]
                    exact h2
                  rw [if_neg (by simp [hd])]
                  have hbrB : printWalk b x₂ (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => printFix m sb dec y) =
                      printWalk b x₂
                        (fun y' path => Grammar.fixValueOk m sb dec y')
                        (fun y' path => printFix m sb dec y') :=
                    printWalk_congr b x₂ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
                  rw [← hbrB]
                  refine ⟨hx1, hx2, ?_⟩
                  rw [valueOkWalk_altE]
                  simp [hx3]
              | error e' => simp only [hb] at h; simp at h
      | repE a iha =>
          intro xs cur cur' hco h
          simp only [parseE] at h
          have L : ∀ f, f ≤ F → ∀ ys c c',
              parseManyE sb a f c = .ok (ys, c') →
              c.cs = (printList ys (fun z hz =>
                  printWalk a z (fun y path => Grammar.fixValueOk m sb dec y)
                    (fun y path => printFix m sb dec y))).toList ++ c'.cs ∧
              c'.off = c.off + (printList ys (fun z hz =>
                  printWalk a z (fun y path => Grammar.fixValueOk m sb dec y)
                    (fun y path => printFix m sb dec y))).length ∧
              allWalk ys (fun z hz =>
                valueOkWalk a z (fun y path => Grammar.fixValueOk m sb dec y)) = true := by
            intro f
            induction f with
            | zero =>
                intro hf ys c c' h0
                simp only [parseManyE] at h0
                have hcc := Prod.mk.inj (Except.ok.inj h0)
                rw [← hcc.1, ← hcc.2]
                simp [printList_nil, allWalk_nil]
            | succ f ih' =>
                intro hf ys c c' h0
                simp only [parseManyE] at h0
                cases hb : parseE sb a (f+1) c with
                | error e =>
                    simp only [hb] at h0
                    have hcc := Prod.mk.inj (Except.ok.inj h0)
                    rw [← hcc.1, ← hcc.2]
                    simp [printList_nil, allWalk_nil]
                | ok r =>
                    obtain ⟨z, c₁⟩ := r
                    simp only [hb] at h0
                    have hbody := (show f + 1 = F ∨ f + 1 < F from by omega).elim
                      (fun hf1 => iha hco (hf1 ▸ hb)) (fun hlt => IH (f+1) hlt hco hb)
                    obtain ⟨hz1, hz2, hz3⟩ := hbody
                    by_cases hprog : c₁.cs.length < c.cs.length
                    · rw [if_pos hprog] at h0
                      cases hr : parseManyE sb a f c₁ with
                      | error e => simp [hr] at h0
                      | ok r₂ =>
                          obtain ⟨zs, c₂⟩ := r₂
                          simp only [hr] at h0
                          have hcc := Prod.mk.inj (Except.ok.inj h0)
                          obtain ⟨hzs1, hzs2, hzs3⟩ := ih' (by omega) zs c₁ c₂ hr
                          rw [← hcc.1, ← hcc.2]
                          rw [printList_cons, allWalk_cons]
                          refine ⟨?_, ?_, ?_⟩
                          · rw [hz1, hzs1, String.toList_append, List.append_assoc]
                          · rw [hzs2, hz2, String.length_append]
                            omega
                          · simp [hz3, hzs3]
                    · rw [if_neg hprog] at h0
                      have hcc := Prod.mk.inj (Except.ok.inj h0)
                      rw [← hcc.1, ← hcc.2]
                      rw [printList_cons, printList_nil, allWalk_cons, allWalk_nil]
                      refine ⟨?_, ?_, ?_⟩
                      · rw [hz1]
                        simp
                      · rw [hz2]
                        simp
                      · simp [hz3]
          obtain ⟨L1, L2, L3⟩ := L F (Nat.le_refl F) xs cur cur' h
          rw [printWalk_repE]
          refine ⟨L1, L2, ?_⟩
          rw [valueOkWalk_repE]
          exact L3
      | optE a iha =>
          intro x cur cur' hco h
          simp only [parseE] at h
          cases ha : parseE sb a F cur with
          | error e =>
              simp only [ha] at h
              have hcc := Prod.mk.inj (Except.ok.inj h)
              rw [← hcc.1, ← hcc.2]
              rw [printWalk_optE_none]
              simp [valueOkWalk_optE_none]
          | ok r =>
              obtain ⟨z, c₁⟩ := r
              simp only [ha] at h
              have hcc := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨hz1, hz2, hz3⟩ := iha hco ha
              rw [← hcc.1, ← hcc.2]
              rw [printWalk_optE_some]
              have hbr : printWalk a z (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => printFix m sb dec y) =
                  printWalk a z
                    (fun y' path => Grammar.fixValueOk m sb dec y')
                    (fun y' path => printFix m sb dec y') :=
                printWalk_congr a z _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
              rw [← hbr] at hz1 hz2
              refine ⟨hz1, hz2, ?_⟩
              rw [valueOkWalk_optE_some]
              have hbrB : valueOkWalk a z
                  (fun y' path => Grammar.fixValueOk m sb dec y') =
                  valueOkWalk a z (fun y _ => Grammar.fixValueOk m sb dec y) :=
                valueOkWalk_congr a z _ _ (fun _ _ => rfl)
              rw [← hbrB] at hz3
              exact hz3
      | labelE n a iha =>
          intro x cur cur' hco h
          simp only [parseE] at h
          cases ha : parseE sb a F cur with
          | error e => simp [ha] at h
          | ok r =>
              obtain ⟨z, c₁⟩ := r
              simp only [ha] at h
              have hcc := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨hz1, hz2, hz3⟩ := iha hco ha
              rw [← hcc.1, ← hcc.2]
              rw [printWalk_labelE]
              have hbr : printWalk a z (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => printFix m sb dec y) =
                  printWalk a z
                    (fun y' path => Grammar.fixValueOk m sb dec y')
                    (fun y' path => printFix m sb dec y') :=
                printWalk_congr a z _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
              rw [← hbr] at hz1 hz2
              refine ⟨hz1, hz2, ?_⟩
              rw [valueOkWalk_labelE]
              have hbrB : valueOkWalk a z
                  (fun y' path => Grammar.fixValueOk m sb dec y') =
                  valueOkWalk a z (fun y _ => Grammar.fixValueOk m sb dec y) :=
                valueOkWalk_congr a z _ _ (fun _ _ => rfl)
              rw [← hbrB] at hz3
              exact hz3
      | relE mm owns don ex nm vld sub ih =>
          intro x cur cur' hco h
          simp only [parseE] at h
          cases ha : parseE sb sub F cur with
          | error e => simp only [ha] at h; simp at h
          | ok r =>
              obtain ⟨raw, c₁⟩ := r
              simp only [ha] at h
              cases hd : mm.decode raw with
              | none => simp [hd] at h
              | some r =>
                  simp only [hd] at h
                  have hcc := Prod.mk.inj (Except.ok.inj h)
                  obtain ⟨hz1, hz2, hz3⟩ := ih hco ha
                  rw [← hcc.1, ← hcc.2]
                  have hex : mm.encode r = raw := ex raw r hd
                  have hown : owns r = true := don raw r hd
                  rw [printWalk_relE]
                  have hbr : printWalk sub (mm.encode r)
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => printFix m sb dec y) =
                      printWalk sub raw
                        (fun y' path => Grammar.fixValueOk m sb dec y')
                        (fun y' path => printFix m sb dec y') := by
                    rw [hex]
                  rw [hbr]
                  refine ⟨hz1, hz2, ?_⟩
                  rw [valueOkWalk_relE]
                  have hbrB : valueOkWalk sub (mm.encode r)
                      (fun y' path => Grammar.fixValueOk m sb dec y') =
                      valueOkWalk sub raw (fun y _ => Grammar.fixValueOk m sb dec y) := by
                    rw [hex]
                  rw [hbrB]
                  simp [hown, hz3]
      | selfE =>
          intro x cur cur' _ h
          cases F with
          | zero => simp [parseE] at h
          | succ f =>
              simp only [parseE] at h
              obtain ⟨hx1, hx2, hx3⟩ := IH f (Nat.lt_succ_self f) hcoh h
              rw [printWalk_selfE]
              have hbr : printFix m sb dec x =
                  printWalk sb x (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => printFix m sb dec y) :=
                printFix_unfold m sb dec x
              rw [hbr]
              refine ⟨hx1, hx2, ?_⟩
              have h4 : Grammar.fixValueOk m sb dec x =
                  valueOkWalk sb x (fun y _ => Grammar.fixValueOk m sb dec y) :=
                Grammar.fixValueOk_unfold m sb dec x
              rw [valueOkWalk_selfE]
              show Grammar.fixValueOk m sb dec x = true
              rw [h4]
              exact hx3

/-! ## §4: the parse-side head/exclusion family -/

/-- THE carrier's splits law — the splits case table PROVED ONCE (the
pairs' shared content; the terminal cases as in `parseMonoGG`). -/
theorem GG.parseSplitsGG :
    ∀ (fuel : Nat) {R : Type} (sb : GG R R) {A : Type} (g : GG R A),
      ∀ {x : A} {cur cur' : Cursor},
      parseGG sb g fuel cur = .ok (x, cur') → ∃ pre, cur.cs = pre ++ cur'.cs := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      have key : ∀ (n : Nat) {R : Type} (sb : GG R R) {A : Type} (g : GG R A),
          GG.mu g < n → ∀ {x : A} {cur cur' : Cursor},
          parseGG sb g F cur = .ok (x, cur') → ∃ pre, cur.cs = pre ++ cur'.cs := by
        intro n
        induction n with
        | zero => intro R sb A g hn; exact absurd hn (Nat.not_lt_zero _)
        | succ n IHn =>
            intro R sb A g
            cases g with
            | atomG L =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                exact ⟨(L.print x).toList, L.scan_exact _ _ _ h⟩
            | seqG a b =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu a < n ∧ GG.mu b < n := by
                  simp [GG.mu] at hn; exact ⟨by omega, by omega⟩
                cases ha : parseGG sb a F cur with
                | error e => simp only [ha] at h; simp at h
                | ok r =>
                    obtain ⟨x₁, cur₁⟩ := r
                    cases hb : parseGG sb b F cur₁ with
                    | error e => simp only [ha, hb] at h; simp at h
                    | ok r₂ =>
                        obtain ⟨y, cur₂⟩ := r₂
                        simp only [ha, hb] at h
                        rw [← ok_cur_inv h]
                        obtain ⟨pa, hpa⟩ := IHn sb a hna.1 ha
                        obtain ⟨pb, hpb⟩ := IHn sb b hna.2 hb
                        exact ⟨pa ++ pb, by rw [hpa, hpb, List.append_assoc]⟩
            | altG a b =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu a < n ∧ GG.mu b < n := by
                  simp [GG.mu] at hn; exact ⟨by omega, by omega⟩
                cases ha : parseGG sb a F cur with
                | ok r =>
                    obtain ⟨x₁, cur₁⟩ := r
                    simp only [ha] at h
                    rw [← ok_cur_inv h]
                    exact IHn sb a hna.1 ha
                | error e =>
                    simp only [ha] at h
                    cases hb : parseGG sb b F cur with
                    | ok r =>
                        obtain ⟨x₂, cur₂⟩ := r
                        simp only [hb] at h
                        rw [← ok_cur_inv h]
                        exact IHn sb b hna.2 hb
                    | error e' => simp only [hb] at h; simp at h
            | repG a =>
                intro hn xs cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu a < n := by simp [GG.mu] at hn; omega
                have splits : ∀ f, f ≤ F → ∀ ys c c',
                    parseManyGG sb a f c = .ok (ys, c') → ∃ pre, c.cs = pre ++ c'.cs := by
                  intro f
                  induction f with
                  | zero =>
                      intro hf ys c c' h0
                      simp only [parseManyGG] at h0
                      rw [← ok_cur_inv h0]
                      exact ⟨[], rfl⟩
                  | succ f ih' =>
                      intro hf ys c c' h0
                      simp only [parseManyGG] at h0
                      cases hb : parseGG sb a (f+1) c with
                      | error e =>
                          simp only [hb] at h0
                          rw [← ok_cur_inv h0]
                          exact ⟨[], rfl⟩
                      | ok r =>
                          obtain ⟨z, c₁⟩ := r
                          simp only [hb] at h0
                          have hbody : ∃ pre, c.cs = pre ++ c₁.cs := by
                            by_cases hf1 : f + 1 = F
                            · subst hf1
                              exact IHn sb a hna hb
                            · exact IH (f+1) (by omega) sb a hb
                          by_cases hprog : c₁.cs.length < c.cs.length
                          · rw [if_pos hprog] at h0
                            cases hr : parseManyGG sb a f c₁ with
                            | error e => simp [hr] at h0
                            | ok r₂ =>
                                obtain ⟨zs, c₂⟩ := r₂
                                simp only [hr] at h0
                                rw [← ok_cur_inv h0]
                                obtain ⟨p1, hp1⟩ := hbody
                                obtain ⟨p2, hp2⟩ := ih' (by omega) zs c₁ c₂ hr
                                exact ⟨p1 ++ p2, by rw [hp1, hp2, List.append_assoc]⟩
                          · rw [if_neg hprog] at h0
                            rw [← ok_cur_inv h0]
                            exact hbody
                exact splits F (Nat.le_refl F) xs cur cur' h
            | optG a =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu a < n := by simp [GG.mu] at hn; omega
                cases ha : parseGG sb a F cur with
                | error e =>
                    simp only [ha] at h
                    rw [← ok_cur_inv h]
                    exact ⟨[], rfl⟩
                | ok r =>
                    obtain ⟨z, c₁⟩ := r
                    simp only [ha] at h
                    rw [← ok_cur_inv h]
                    exact IHn sb a hna ha
            | labelG nm a =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu a < n := by simp [GG.mu] at hn; omega
                cases ha : parseGG sb a F cur with
                | error e => simp [ha] at h
                | ok r =>
                    obtain ⟨z, c₁⟩ := r
                    simp only [ha] at h
                    simp only [Except.ok.injEq, Prod.mk.injEq] at h
                    rw [← h.2]
                    exact IHn sb a hna ha
            | relG mm owns don ex nm vld sub =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hna : GG.mu sub < n := by simp [GG.mu] at hn; omega
                cases ha : parseGG sb sub F cur with
                | error e => simp only [ha] at h; simp at h
                | ok r =>
                    obtain ⟨raw, c₁⟩ := r
                    simp only [ha] at h
                    cases hd : mm.decode raw with
                    | none => simp [hd] at h
                    | some r =>
                        simp only [hd] at h
                        rw [← ok_cur_inv h]
                        exact IHn sb sub hna ha
            | selfG =>
                intro hn x cur cur' h
                cases F with
                | zero => simp [parseGG] at h
                | succ f =>
                    simp only [parseGG] at h
                    exact IH f (Nat.lt_succ_self f) sb sb h
            | fixG m body dec =>
                intro hn x cur cur' h
                simp only [parseGG] at h
                have hE := (GrammarE.parseE_inj F body body).1
                rw [hE] at h
                have hna : GG.mu (GG.injE body) < n := by
                  rw [GG.mu_injE]
                  simp [GG.mu] at hn; omega
                exact IHn (GG.injE body) (GG.injE body) hna h
      intro R sb A g
      exact key (GG.mu g + 1) sb g (by omega)

/-- A successful parse splits the input at the final cursor (the
    unconditional split fact — the exactness law's cs conjunct without
    the print). Discharged from the carrier's law at the open injection. -/
theorem GrammarE.parseSplitsE {R : Type} (sb : GrammarE R R) :
    ∀ (fuel : Nat) {A : Type} {g : GrammarE R A} {x : A} {cur cur' : Cursor},
      parseE sb g fuel cur = .ok (x, cur') → ∃ pre, cur.cs = pre ++ cur'.cs := by
    -- THE TRANSFER: discharged from the carrier's law at the open injection.
    intro fuel A g x cur cur' h
    rw [(parseE_inj fuel sb g).1] at h
    exact GG.parseSplitsGG fuel (GG.injE sb) (GG.injE g) h
/-- The parse-side head lemma (the print-head-vs-FIRST family's dual):
    a CONSUMING success starts with an effective-first head. -/
theorem GrammarE.parseHeadE {R : Type} (sb : GrammarE R R)
    (hn : sb.nullableE = false) (hf : sb.firstE ≠ none) :
    ∀ (fuel : Nat) {A : Type} {g : GrammarE R A} {x : A} {cur cur' : Cursor},
      parseE sb g fuel cur = .ok (x, cur') → cur'.cs.length < cur.cs.length →
      ∃ h ∈ effFirstE sb.bodyFirsts g, h.matches cur.cs = true := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      intro A g
      induction g with
      | atomE L =>
          intro x cur cur' h _
          simp only [parseE] at h
          exact ⟨L.head, by show L.head ∈ [L.head]; exact List.Mem.head [],
            L.scan_head _ _ _ h⟩
      | seqE a b iha ihb =>
          intro x cur cur' h hlt
          simp only [parseE] at h
          cases ha : parseE sb a F cur with
          | error e => simp only [ha] at h; simp at h
          | ok r =>
              obtain ⟨x₁, cur₁⟩ := r
              cases hb : parseE sb b F cur₁ with
              | error e => simp only [ha, hb] at h; simp at h
              | ok r₂ =>
                  obtain ⟨y, cur₂⟩ := r₂
                  simp only [ha, hb] at h
                  rw [← ok_cur_inv h] at hlt
                  by_cases h1 : cur₁.cs.length < cur.cs.length
                  · obtain ⟨hh, hmem, hm⟩ := iha ha h1
                    exact ⟨hh, List.mem_append_left _ hmem, hm⟩
                  · have hmono := parseMonoE sb F ha
                    have heq0 : cur₁.cs.length = cur.cs.length :=
                      Nat.le_antisymm hmono (Nat.le_of_not_lt h1)
                    obtain ⟨pre, hpre⟩ := parseSplitsE sb F ha
                    have hlen : pre.length = 0 := by
                      have h3 := congrArg List.length hpre
                      rw [List.length_append, heq0] at h3
                      omega
                    have hpre0 : pre = [] := List.length_eq_zero_iff.mp hlen
                    have hcs : cur₁.cs = cur.cs := by
                      rw [hpre0] at hpre
                      simp at hpre
                      exact hpre.symm
                    have hlt' : cur₂.cs.length < cur.cs.length := hlt
                    have hlt2 : cur₂.cs.length < cur₁.cs.length := by omega
                    obtain ⟨hh, hmem, hm⟩ := ihb hb hlt2
                    have hna : nullableE a = true := by
                      cases h2 : nullableE a with
                      | false =>
                          have h2c : cur₁.cs.length < cur.cs.length :=
                            parseConsumeE sb hn F ha h2
                          omega
                      | true => rfl
                    refine ⟨hh, ?_, ?_⟩
                    · show hh ∈ effFirstE sb.bodyFirsts a ++
                          (if nullableE a then effFirstE sb.bodyFirsts b else [])
                      rw [hna]
                      exact List.mem_append_right _ hmem
                    · rw [hcs] at hm; exact hm
      | altE a b iha ihb =>
          intro x cur cur' h hlt
          simp only [parseE] at h
          cases ha : parseE sb a F cur with
          | ok r =>
              obtain ⟨x₁, cur₁⟩ := r
              simp only [ha] at h
              rw [← ok_cur_inv h] at hlt
              obtain ⟨hh, hmem, hm⟩ := iha ha hlt
              exact ⟨hh, List.mem_append_left _ hmem, hm⟩
          | error e =>
              simp only [ha] at h
              cases hb : parseE sb b F cur with
              | ok r =>
                  obtain ⟨x₂, cur₂⟩ := r
                  simp only [hb] at h
                  rw [← ok_cur_inv h] at hlt
                  obtain ⟨hh, hmem, hm⟩ := ihb hb hlt
                  exact ⟨hh, List.mem_append_right _ hmem, hm⟩
              | error e' => simp only [hb] at h; simp at h
      | repE a iha =>
          intro xs cur cur' h hlt
          simp only [parseE] at h
          have heads : ∀ f, f ≤ F → ∀ ys c c',
              parseManyE sb a f c = .ok (ys, c') → c'.cs.length < c.cs.length →
              ∃ h ∈ effFirstE sb.bodyFirsts a, h.matches c.cs = true := by
            intro f
            induction f with
            | zero =>
                intro hf ys c c' h0 hlt0
                simp only [parseManyE] at h0
                rw [← ok_cur_inv h0] at hlt0
                simp at hlt0
            | succ f ih' =>
                intro hf ys c c' h0 hlt0
                simp only [parseManyE] at h0
                cases hb : parseE sb a (f+1) c with
                | error e =>
                    simp only [hb] at h0
                    rw [← ok_cur_inv h0] at hlt0
                    simp at hlt0
                | ok r =>
                    obtain ⟨z, c₁⟩ := r
                    simp only [hb] at h0
                    by_cases hprog : c₁.cs.length < c.cs.length
                    · rw [if_pos hprog] at h0
                      cases hr : parseManyE sb a f c₁ with
                      | error e => simp [hr] at h0
                      | ok r₂ =>
                          obtain ⟨zs, c₂⟩ := r₂
                          simp only [hr] at h0
                          rw [← ok_cur_inv h0] at hlt0
                          by_cases hf1 : f + 1 = F
                          · exact iha (hf1 ▸ hb) hprog
                          · exact IH (f+1) (by omega) hb hprog
                    · rw [if_neg hprog] at h0
                      rw [← ok_cur_inv h0] at hlt0
                      exact absurd hlt0 hprog
          exact heads F (Nat.le_refl F) xs cur cur' h hlt
      | optE a iha =>
          intro x cur cur' h hlt
          simp only [parseE] at h
          cases ha : parseE sb a F cur with
          | error e =>
              simp only [ha] at h
              rw [← ok_cur_inv h] at hlt
              simp at hlt
          | ok r =>
              obtain ⟨z, c₁⟩ := r
              simp only [ha] at h
              rw [← ok_cur_inv h] at hlt
              exact iha ha hlt
      | labelE n a iha =>
          intro x cur cur' h hlt
          simp only [parseE] at h
          cases ha : parseE sb a F cur with
          | error e => simp [ha] at h
          | ok r =>
              obtain ⟨z, c₁⟩ := r
              simp only [ha] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2] at hlt
              exact iha ha hlt
      | relE mm owns don ex nm vld sub ih =>
          intro x cur cur' h hlt
          simp only [parseE] at h
          cases ha : parseE sb sub F cur with
          | error e => simp only [ha] at h; simp at h
          | ok r =>
              obtain ⟨raw, c₁⟩ := r
              simp only [ha] at h
              cases hd : mm.decode raw with
              | none => simp [hd] at h
              | some r =>
                  simp only [hd] at h
                  rw [← ok_cur_inv h] at hlt
                  exact ih ha hlt
      | selfE =>
          intro x cur cur' h hlt
          cases F with
          | zero => simp [parseE] at h
          | succ f =>
              simp only [parseE] at h
              obtain ⟨hh, hmem, hm⟩ := IH f (Nat.lt_succ_self f) h hlt
              have hfs : effFirstE sb.bodyFirsts sb = sb.bodyFirsts :=
                effFirstE_bodyFirsts sb hf
              rw [hfs] at hmem
              exact ⟨hh, hmem, hm⟩

/-- The first-exclusion lemma (design §3.4's alt content): a
    non-nullable grammar whose effective heads all fail the text fails
    on it. -/
theorem GrammarE.parseExcludeE {R : Type} (sb : GrammarE R R)
    (hn : sb.nullableE = false) (hf : sb.firstE ≠ none) :
    ∀ (fuel : Nat) {A : Type} {g : GrammarE R A} (k : Nat) (cs : List Char),
      nullableE g = false →
      (∀ h ∈ effFirstE sb.bodyFirsts g, h.matches cs = false) →
      ∃ e, parseE sb g fuel ⟨k, cs⟩ = .error e := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      intro A g
      induction g with
      | atomE L =>
          intro k cs hnn hfail
          have h1 : L.head.matches cs = false :=
            hfail L.head (by show L.head ∈ [L.head]; exact List.Mem.head [])
          obtain ⟨e, he⟩ := L.head_fail ⟨k, cs⟩ h1
          exact ⟨e, by simp only [parseE]; exact he⟩
      | seqE a b iha ihb =>
          intro k cs hnn hfail
          have hnn' : (nullableE a && nullableE b) = false := hnn
          cases ha : parseE sb a F ⟨k, cs⟩ with
          | error e =>
              exact ⟨e, by simp only [parseE]; rw [ha]⟩
          | ok r =>
              obtain ⟨x₁, cur₁⟩ := r
              by_cases hcons : cur₁.cs.length < cs.length
              · obtain ⟨hh, hmem, hm⟩ := parseHeadE sb hn hf F ha hcons
                have hbad : hh.matches cs = false :=
                  hfail hh (List.mem_append_left _ hmem)
                simp [hm] at hbad
              · have hmono : cur₁.cs.length ≤ cs.length := parseMonoE sb F ha
                have heq0 : cur₁.cs.length = cs.length :=
                  Nat.le_antisymm hmono (Nat.le_of_not_lt hcons)
                obtain ⟨pre, hpre⟩ := parseSplitsE sb F ha
                have hpre' : cs = pre ++ cur₁.cs := hpre
                have hlen : pre.length = 0 := by
                  have h3 := congrArg List.length hpre'
                  rw [List.length_append, heq0] at h3
                  omega
                have hpre0 : pre = [] := List.length_eq_zero_iff.mp hlen
                have hcs : cur₁.cs = cs := by
                  rw [hpre0] at hpre'
                  simp at hpre'
                  exact hpre'.symm
                have hna : nullableE a = true := by
                  cases h2 : nullableE a with
                  | false =>
                      have h2c : cur₁.cs.length < cs.length := parseConsumeE sb hn F ha h2
                      omega
                  | true => rfl
                have hnb : nullableE b = false := by
                  cases h2 : nullableE b with
                  | true => simp [hna, h2] at hnn'
                  | false => rfl
                have hfailB : ∀ h ∈ effFirstE sb.bodyFirsts b, h.matches cur₁.cs = false := by
                  intro hh hmem
                  have hmem2 : hh ∈ effFirstE sb.bodyFirsts a ++
                      (if nullableE a then effFirstE sb.bodyFirsts b else []) := by
                    rw [hna]
                    exact List.mem_append_right _ hmem
                  rw [hcs]
                  exact hfail hh hmem2
                obtain ⟨e, he⟩ := ihb cur₁.off cur₁.cs hnb hfailB
                have he' : parseE sb b F cur₁ = .error e := he
                exact ⟨e, by simp only [parseE, ha, he']⟩
      | altE a b iha ihb =>
          intro k cs hnn hfail
          have hnn' : (nullableE a || nullableE b) = false := hnn
          simp only [Bool.or_eq_false_iff] at hnn'
          have hfailA : ∀ h ∈ effFirstE sb.bodyFirsts a, h.matches cs = false :=
            fun hh hmem => hfail hh (List.mem_append_left _ hmem)
          have hfailB : ∀ h ∈ effFirstE sb.bodyFirsts b, h.matches cs = false :=
            fun hh hmem => hfail hh (List.mem_append_right _ hmem)
          obtain ⟨ea, hea⟩ := iha k cs hnn'.1 hfailA
          obtain ⟨eb, heb⟩ := ihb k cs hnn'.2 hfailB
          exact ⟨ParseError.farther ea eb, by simp only [parseE, hea, heb]⟩
      | repE a iha =>
          intro k cs hnn _
          simp [nullableE] at hnn
      | optE a iha =>
          intro k cs hnn _
          simp [nullableE] at hnn
      | labelE n a iha =>
          intro k cs hnn hfail
          obtain ⟨e, he⟩ := iha k cs hnn hfail
          have hthis : parseE sb (.labelE n a) F ⟨k, cs⟩ =
              .error { e with valid := [n], message := s!"expected {n}", context := TextKit.Label.at n :: e.context } := by
            simp only [parseE, he]
          exact ⟨_, hthis⟩
      | relE mm owns don ex nm vld sub ih =>
          intro k cs hnn hfail
          obtain ⟨e, he⟩ := ih k cs hnn hfail
          exact ⟨e, by simp only [parseE, he]⟩
      | selfE =>
          intro k cs _ hfail
          cases F with
          | zero =>
              exact ⟨ParseError.base k ["<recursion limit>"], by simp [parseE]⟩
          | succ f =>
              have hfs : effFirstE sb.bodyFirsts sb = sb.bodyFirsts :=
                effFirstE_bodyFirsts sb hf
              have hfail' : ∀ h ∈ effFirstE sb.bodyFirsts sb, h.matches cs = false := by
                intro hh hmem
                rw [hfs] at hmem
                exact hfail hh hmem
              obtain ⟨e, he⟩ := IH f (Nat.lt_succ_self f) k cs hn hfail'
              refine ⟨e, ?_⟩
              show parseE sb .selfE (f + 1) ⟨k, cs⟩ = .error e
              simp only [parseE]
              exact he

/-! ## the closed-level print bundle -/

/-- printG's per-node equations (iota). -/
theorem Grammar.printG_atom (L : Lexeme R) (x : R) :
    printG (.atom L) x = L.print x := rfl
theorem Grammar.printG_seq (a : Grammar A) (b : Grammar B) (p : A) (q : B) :
    printG (.seq a b) (p, q) = (printG a p ++ printG b q) := rfl
theorem Grammar.printG_alt (a b : Grammar R) (x : R) :
    printG (.alt a b) x = (if valueOk a x then printG a x else printG b x) := rfl
theorem Grammar.printG_rep (a : Grammar A) (xs : List A) :
    printG (.rep a) xs = xs.foldr (fun z acc => printG a z ++ acc) "" := rfl
theorem Grammar.printG_opt_some (a : Grammar A) (z : A) :
    printG (.opt a) (Option.some z) = printG a z := rfl
theorem Grammar.printG_opt_none (a : Grammar A) :
    printG (.opt a) Option.none = "" := rfl
theorem Grammar.printG_label (n : String) (a : Grammar A) (x : A) :
    printG (.label n a) x = printG a x := rfl
theorem Grammar.printG_rel (m : Kit.Codec Raw R) (owns : R → Bool)
    (don : ∀ raw r, m.decode raw = Option.some r → owns r = true)
    (ex : ∀ raw r, m.decode raw = Option.some r → m.encode r = raw)
    (nm : String) (vld : List String) (sub : Grammar Raw) (x : R) :
    printG (.rel m owns don ex nm vld sub) x = printG sub (m.encode x) := rfl
theorem Grammar.printG_fix (m : R → Nat) (body : GrammarE R R)
    (dec : ∀ x y, SelfPathE body x y → m y < m x) (x : R) :
    printG (.fix m body dec) x = printFix m body dec x := rfl

/-- valueOk's per-node equations (iota). -/
theorem Grammar.valueOk_seq (a : Grammar A) (b : Grammar B) (p : A) (q : B) :
    valueOk (.seq a b) (p, q) = (valueOk a p && valueOk b q) := rfl
theorem Grammar.valueOk_alt (a b : Grammar R) (x : R) :
    valueOk (.alt a b) x = (valueOk a x || valueOk b x) := rfl
theorem Grammar.valueOk_rep (a : Grammar A) (xs : List A) :
    valueOk (.rep a) xs = xs.all (fun z => valueOk a z) := rfl
theorem Grammar.valueOk_opt_some (a : Grammar A) (z : A) :
    valueOk (.opt a) (Option.some z) = valueOk a z := rfl
theorem Grammar.valueOk_opt_none (a : Grammar A) :
    valueOk (.opt a) Option.none = true := rfl
theorem Grammar.valueOk_label (n : String) (a : Grammar A) (x : A) :
    valueOk (.label n a) x = valueOk a x := rfl
theorem Grammar.valueOk_rel (m : Kit.Codec Raw R) (owns : R → Bool)
    (don : ∀ raw r, m.decode raw = Option.some r → owns r = true)
    (ex : ∀ raw r, m.decode raw = Option.some r → m.encode r = raw)
    (nm : String) (vld : List String) (sub : Grammar Raw) (x : R) :
    valueOk (.rel m owns don ex nm vld sub) x = (owns x && valueOk sub (m.encode x)) := rfl

/-- A nonempty foldr-print starts with the head of its first nonempty
    element (the closed rep case's list induction). -/
theorem Grammar.foldr_append_head {A : Type} {fs : List HeadSpec} :
    ∀ (ys : List A) (f : A → String),
    (∀ z, z ∈ ys → f z ≠ "" → ∀ cs, ∃ h ∈ fs, h.matches ((f z).toList ++ cs) = true) →
    ys.foldr (fun z acc => f z ++ acc) "" ≠ "" →
    ∀ cs, ∃ h ∈ fs, h.matches (((ys.foldr (fun z acc => f z ++ acc) "")).toList ++ cs) = true := by
  intro ys
  induction ys with
  | nil => intro f _ hne; simp at hne
  | cons z zs ih =>
      intro f hf hne cs
      show ∃ h ∈ fs, h.matches (((f z ++ zs.foldr (fun w acc => f w ++ acc) "")).toList ++ cs)
        = true
      by_cases hz0 : f z = ""
      · have hne' : zs.foldr (fun w acc => f w ++ acc) "" ≠ "" := by
          intro h0
          apply hne
          show (f z ++ zs.foldr (fun w acc => f w ++ acc) "") = ""
          rw [hz0, h0]
          simp
        obtain ⟨h, hmem, hm⟩ := ih _ (fun w hw => hf w (List.Mem.tail z hw)) hne' cs
        refine ⟨h, hmem, ?_⟩
        have hsimpl : ((f z ++ zs.foldr (fun w acc => f w ++ acc) "")).toList ++ cs =
            (zs.foldr (fun w acc => f w ++ acc) "").toList ++ cs := by
          rw [hz0]; simp
        rw [hsimpl]; exact hm
      · obtain ⟨h, hmem, hm⟩ := hf z (List.Mem.head zs) hz0
          ((zs.foldr (fun w acc => f w ++ acc) "").toList ++ cs)
        refine ⟨h, hmem, ?_⟩
        have hsimpl : ((f z ++ zs.foldr (fun w acc => f w ++ acc) "")).toList ++ cs =
            (f z).toList ++ ((zs.foldr (fun w acc => f w ++ acc) "").toList ++ cs) := by
          rw [String.toList_append, List.append_assoc]
        rw [hsimpl]; exact hm

/-- The closed print bundle: the print-head-vs-FIRST kit at the closed
    level (the seq-case wall's closed half). -/
theorem Grammar.printBundleG :
    {A : Type} → (g : Grammar A) → Predictive g → (x : A) →
    valueOk g x = true →
    (nullable g = false → printG g x ≠ "") ∧
    (printG g x ≠ "" → ∀ cs, ∃ h ∈ effFirst g, h.matches ((printG g x).toList ++ cs) = true) := by
  intro A g
  induction g with
  | atom L =>
      intro _ x hok
      have hpre : L.pre x = true := hok
      have hmunch : (L.munch.all fun p => ([] : List Char).head?.all (fun c => !p c)) = true := by
        cases L.munch with
        | none => rfl
        | some p => simp
      have hscan := L.print_scan 0 x [] hpre hmunch
      refine ⟨?_, ?_⟩
      · intro _
        intro hne
        have hne' : L.print x = "" := hne
        have hc := L.consumes _ _ _ hscan
        have hl : (L.print x).toList = [] := by rw [hne']; rfl
        simp [hl] at hc
      · intro hne cs
        have hhead := L.scan_head _ _ _ hscan
        refine ⟨L.head, by show L.head ∈ [L.head]; exact List.Mem.head [], ?_⟩
        show L.head.matches ((L.print x).toList ++ cs) = true
        apply HeadSpec.matches_append
        have h2 := hhead
        simp only [] at h2
        have h3 : L.head.matches ((L.print x).toList ++ []) = true := h2
        rw [List.append_nil] at h3
        exact h3
  | seq a b iha ihb =>
      intro hp x hok
      obtain ⟨p, q⟩ := x
      have hp' : Predictive a ∧ Predictive b ∧
          (∀ s1 ∈ tailFirst a, ∀ s2 ∈ effFirst b, HeadSpec.disj s1 s2 = true) ∧
          (∀ p' ∈ (tailMunch a).getD [], ∀ s2 ∈ effFirst b, s2.breaks p' = true) := hp
      obtain ⟨hpa, hpb, h1, h2⟩ := hp'
      {  -- the seq content
          have hok' : valueOk a p = true ∧ valueOk b q = true := by
            have h3 := hok
            rw [valueOk_seq] at h3
            simpa [Bool.and_eq_true] using h3
          obtain ⟨neA, headA⟩ := iha hpa p hok'.1
          obtain ⟨neB, headB⟩ := ihb hpb q hok'.2
          refine ⟨?_, ?_⟩
          · intro hnn
            rw [printG_seq]
            have hnn' : (nullable a && nullable b) = false := hnn
            cases hna : nullable a with
            | false => exact String.append_left_ne_empty (neA hna)
            | true =>
                have hnb : nullable b = false := by
                  cases h : nullable b with
                  | true => simp [hna, h] at hnn'
                  | false => rfl
                exact String.append_right_ne_empty (neB hnb)
          · intro hne cs
            rw [printG_seq] at hne ⊢
            by_cases hep : printG a p = ""
            · have hna : nullable a = true := by
                cases h : nullable a with
                | false => exact absurd hep (neA h)
                | true => rfl
              have hneB : printG b q ≠ "" := by
                intro hb0
                rw [hep, hb0] at hne
                exact hne (by simp)
              obtain ⟨h, hmem, hm⟩ := headB hneB cs
              refine ⟨h, ?_, ?_⟩
              · show h ∈ effFirst a ++ (if nullable a then effFirst b else [])
                rw [hna]
                exact List.mem_append_right _ hmem
              · have hsimpl : (printG a p ++ printG b q).toList ++ cs =
                    (printG b q).toList ++ cs := by
                  rw [hep]; simp
                rw [hsimpl]; exact hm
            · obtain ⟨h, hmem, hm⟩ := headA hep ((printG b q).toList ++ cs)
              refine ⟨h, ?_, ?_⟩
              · show h ∈ effFirst a ++ (if nullable a then effFirst b else [])
                exact List.mem_append_left _ hmem
              · have hsimpl : (printG a p ++ printG b q).toList ++ cs =
                    (printG a p).toList ++ ((printG b q).toList ++ cs) := by
                  rw [String.toList_append, List.append_assoc]
                rw [hsimpl]; exact hm
      }
  | alt a b iha ihb =>
      intro hp x hok
      have hp' : Predictive a ∧ Predictive b ∧
          (∀ s1 ∈ effFirst a, ∀ s2 ∈ effFirst b, HeadSpec.disj s1 s2 = true) ∧
          nullable a = false := hp
      obtain ⟨hpa, hpb, h1, h2⟩ := hp'
      {  -- the alt content
          have hd : (valueOk a x || valueOk b x) = true := by
            have h3 := hok
            rw [valueOk_alt] at h3
            exact h3
          have hb2_of : valueOk a x = false → valueOk b x = true := by
            intro h0
            cases h4 : valueOk b x with
            | true => rfl
            | false => simp [h0, h4] at hd
          refine ⟨?_, ?_⟩
          · intro hnn
            rw [printG_alt]
            have hnn' : nullable a = false ∧ nullable b = false := by
              have h3 : (nullable a || nullable b) = false := hnn
              simp only [Bool.or_eq_false_iff] at h3
              exact h3
            cases hd1 : valueOk a x with
            | true =>
                rw [if_pos (show (true : Bool) = true from rfl)]
                exact (iha hpa x hd1).1 hnn'.1
            | false =>
                rw [if_neg (show ¬((false : Bool) = true) from by simp)]
                exact (ihb hpb x (hb2_of hd1)).1 hnn'.2
          · intro hne cs
            rw [printG_alt] at hne ⊢
            cases hd1 : valueOk a x with
            | true =>
                rw [if_pos hd1] at hne
                rw [if_pos (show (true : Bool) = true from rfl)]
                obtain ⟨h, hmem, hm⟩ := (iha hpa x hd1).2 hne cs
                exact ⟨h, List.mem_append_left _ hmem, hm⟩
            | false =>
                rw [if_neg (by simp [hd1])] at hne
                rw [if_neg (show ¬((false : Bool) = true) from by simp)]
                obtain ⟨h, hmem, hm⟩ := (ihb hpb x (hb2_of hd1)).2 hne cs
                exact ⟨h, List.mem_append_right _ hmem, hm⟩
      }
  | rep a iha =>
      intro hp xs hok
      have hp' : Predictive a ∧ nullable a = false ∧
          (∀ p' ∈ (tailMunch a).getD [], ∀ s2 ∈ effFirst a, s2.breaks p' = true) ∧
          (∀ s1 ∈ tailFirst a, ∀ s2 ∈ effFirst a, HeadSpec.disj s1 s2 = true) := hp
      obtain ⟨hpa, h1, h2, h3⟩ := hp'
      {  -- the rep content
          have hokAll : ∀ z, z ∈ xs → valueOk a z = true := by
            have h4 := hok
            rw [valueOk_rep] at h4
            exact List.all_eq_true.mp h4
          refine ⟨?_, ?_⟩
          · intro hnn
            simp [nullable] at hnn
          · intro hne cs
            rw [printG_rep] at hne ⊢
            show ∃ h ∈ effFirst a, h.matches
                ((xs.foldr (fun z acc => printG a z ++ acc) "").toList ++ cs) = true
            exact foldr_append_head xs (fun z => printG a z)
              (fun z hz hz0 => (iha hpa z (hokAll z hz)).2 hz0) hne cs
      }
  | opt a iha =>
      intro hp x hok
      have hp' : Predictive a ∧ nullable a = false := hp
      obtain ⟨hpa, hnnp⟩ := hp'
      {  -- the opt content
          refine ⟨?_, ?_⟩
          · intro hnn
            simp [nullable] at hnn
          · intro hne cs
            cases x with
            | none =>
                rw [printG_opt_none] at hne
                exact absurd rfl hne
            | some z =>
                rw [printG_opt_some] at hne ⊢
                have hok' : valueOk a z = true := by
                  have h3 := hok
                  rw [valueOk_opt_some] at h3
                  exact h3
                obtain ⟨h, hmem, hm⟩ := (iha hpa z hok').2 hne cs
                exact ⟨h, hmem, hm⟩
      }
  | label n a iha =>
      intro hp x hok
      have hpa : Predictive a := hp
      {  -- the label content
          have hok' : valueOk a x = true := by
            have h3 := hok
            rw [valueOk_label] at h3
            exact h3
          obtain ⟨ne1, hd1⟩ := iha hpa x hok'
          refine ⟨?_, ?_⟩
          · intro hnn
            rw [printG_label]
            exact ne1 hnn
          · intro hne cs
            rw [printG_label] at hne ⊢
            exact hd1 hne cs
      }
  | rel mm owns don ex nm vld sub ih =>
      intro hp x hok
      have hps : Predictive sub := hp
      {  -- the rel content
          have hok2 : owns x = true ∧ valueOk sub (mm.encode x) = true := by
            have h3 := hok
            rw [valueOk_rel] at h3
            exact Eq.mp (Bool.and_eq_true _ _) h3
          obtain ⟨ne1, hd1⟩ := ih hps (mm.encode x) hok2.2
          refine ⟨?_, ?_⟩
          · intro hnn
            rw [printG_rel]
            exact ne1 hnn
          · intro hne cs
            rw [printG_rel] at hne ⊢
            exact hd1 hne cs
      }
  | fix m body dec =>
      intro hp x hok
      have hp' : GrammarE.PredictiveE body body ∧
          body.firstE ≠ none ∧ body.nullableE = false ∧ body.tailSelfFreeE = true := hp
      obtain ⟨hps, hf, hn, ht⟩ := hp'
      {  -- the fix content
          have hok' : fixValueOk m body dec x = true := hok
          obtain ⟨ne1, hd1⟩ := printFixBundle m body dec hn hf x
            (AccD.ofFuel m x (m x + 1) (Nat.lt_succ_self _)) hok'
          rw [printG_fix]
          refine ⟨fun _ => ne1, ?_⟩
          · intro hne cs
            obtain ⟨h, hmem, hm⟩ := hd1 cs
            have hfs : effFirst (Grammar.fix m body dec) = body.bodyFirsts :=
              Grammar.effFirst_fix m body dec hf
            rw [hfs]
            exact ⟨h, hmem, hm⟩
      }
/-! ## §5: the closed-level family -/

/-- The closed monotonicity. -/
theorem Grammar.parseMonoG :
    ∀ (fuel : Nat) {A : Type} {g : Grammar A} {x : A} {cur cur' : Cursor},
      parseG g fuel cur = .ok (x, cur') → cur'.cs.length ≤ cur.cs.length := by
    -- THE TRANSFER: discharged from the carrier's law at the closed injection —
    -- the closed case table lives ONCE in the carrier (the fix arm IS the
    -- E-fold, so the carrier's fixG case already rode the open twin).
    intro fuel A g x cur cur' h
    have h2 := parseG_inj (c := GG.selfG (R := A)) g fuel
    rw [h2] at h
    exact GG.parseMonoGG fuel (GG.selfG (R := A)) (GG.injG g) h
/-- The closed consumption lemma (the rep-progress content). THE
    TRANSFER: discharged from the carrier's law at the closed
    injection — the closed case table lives ONCE in the carrier (the
    `fixG` arm IS the E-fold, so the carrier's fixG case already rode
    the open twin; the inert `selfG` context's nullability is a
    defeq). The `Predictive` premise is the certificate's carrier —
    the law's content needs only the per-node nullability. -/
theorem Grammar.parseConsumeG :
    ∀ (fuel : Nat) {A : Type} {g : Grammar A}, Predictive g →
      ∀ {x : A} {cur cur' : Cursor},
      parseG g fuel cur = .ok (x, cur') →
      nullable g = false → cur'.cs.length < cur.cs.length := by
  intro fuel A g _ x cur cur' h hnn
  have h2 := parseG_inj (c := GG.selfG (R := A)) g fuel
  rw [h2] at h
  rw [GG.nullableG_injG g A] at hnn
  exact GG.parseConsumeGG fuel GG.selfG rfl (GG.injG g) h hnn
/-- The closed split fact. -/
theorem Grammar.parseSplitsG :
    ∀ (fuel : Nat) {A : Type} {g : Grammar A} {x : A} {cur cur' : Cursor},
      parseG g fuel cur = .ok (x, cur') → ∃ pre, cur.cs = pre ++ cur'.cs := by
    -- THE TRANSFER: discharged from the carrier's law at the closed injection
    -- (the closed splits case table lives ONCE in the carrier).
    intro fuel A g x cur cur' h
    have h2 := parseG_inj (c := GG.selfG (R := A)) g fuel
    rw [h2] at h
    exact GG.parseSplitsGG fuel (GG.selfG (R := A)) (GG.injG g) h
/-! ## §5b: the closed head/exclusion/exactness family -/

/-- The closed parse-head lemma. -/
theorem Grammar.parseHeadG :
    ∀ (fuel : Nat) {A : Type} {g : Grammar A}, Predictive g →
      ∀ {x : A} {cur cur' : Cursor},
      parseG g fuel cur = .ok (x, cur') → cur'.cs.length < cur.cs.length →
      ∃ h ∈ effFirst g, h.matches cur.cs = true := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      intro A g
      induction g with
      | atom L =>
          intro _ x cur cur' h _
          simp only [parseG] at h
          exact ⟨L.head, by show L.head ∈ [L.head]; exact List.Mem.head [],
            L.scan_head _ _ _ h⟩
      | seq a b iha ihb =>
          intro hp x cur cur' h hlt
          have hp' : Predictive a ∧ Predictive b ∧ _ ∧ _ := hp
          obtain ⟨hpa, hpb, _, _⟩ := hp'
          simp only [parseG] at h
          cases ha : parseG a F cur with
          | error e => simp only [ha] at h; simp at h
          | ok r =>
              obtain ⟨x₁, cur₁⟩ := r
              cases hb : parseG b F cur₁ with
              | error e => simp only [ha, hb] at h; simp at h
              | ok r₂ =>
                  obtain ⟨y, cur₂⟩ := r₂
                  simp only [ha, hb] at h
                  rw [← ok_cur_inv h] at hlt
                  by_cases h1 : cur₁.cs.length < cur.cs.length
                  · obtain ⟨hh, hmem, hm⟩ := iha hpa ha h1
                    exact ⟨hh, List.mem_append_left _ hmem, hm⟩
                  · have hmono := parseMonoG F ha
                    have heq0 : cur₁.cs.length = cur.cs.length :=
                      Nat.le_antisymm hmono (Nat.le_of_not_lt h1)
                    obtain ⟨pre, hpre⟩ := parseSplitsG F ha
                    have hlen : pre.length = 0 := by
                      have h3 := congrArg List.length hpre
                      rw [List.length_append, heq0] at h3
                      omega
                    have hpre0 : pre = [] := List.length_eq_zero_iff.mp hlen
                    have hcs : cur₁.cs = cur.cs := by
                      rw [hpre0] at hpre
                      simp at hpre
                      exact hpre.symm
                    have hlt' : cur₂.cs.length < cur.cs.length := hlt
                    have hlt2 : cur₂.cs.length < cur₁.cs.length := by omega
                    obtain ⟨hh, hmem, hm⟩ := ihb hpb hb hlt2
                    have hna : nullable a = true := by
                      cases h2 : nullable a with
                      | false =>
                          have h2c : cur₁.cs.length < cur.cs.length :=
                            parseConsumeG F hpa ha h2
                          omega
                      | true => rfl
                    refine ⟨hh, ?_, ?_⟩
                    · show hh ∈ effFirst a ++ (if nullable a then effFirst b else [])
                      rw [hna]
                      exact List.mem_append_right _ hmem
                    · rw [hcs] at hm; exact hm
      | alt a b iha ihb =>
          intro hp x cur cur' h hlt
          have hp' : Predictive a ∧ Predictive b ∧ _ ∧ _ := hp
          obtain ⟨hpa, hpb, _, _⟩ := hp'
          simp only [parseG] at h
          cases ha : parseG a F cur with
          | ok r =>
              obtain ⟨x₁, cur₁⟩ := r
              simp only [ha] at h
              rw [← ok_cur_inv h] at hlt
              obtain ⟨hh, hmem, hm⟩ := iha hpa ha hlt
              exact ⟨hh, List.mem_append_left _ hmem, hm⟩
          | error e =>
              simp only [ha] at h
              cases hb : parseG b F cur with
              | ok r =>
                  obtain ⟨x₂, cur₂⟩ := r
                  simp only [hb] at h
                  rw [← ok_cur_inv h] at hlt
                  obtain ⟨hh, hmem, hm⟩ := ihb hpb hb hlt
                  exact ⟨hh, List.mem_append_right _ hmem, hm⟩
              | error e' => simp only [hb] at h; simp at h
      | rep a iha =>
          intro hp xs cur cur' h hlt
          have hp' : Predictive a ∧ nullable a = false ∧ _ ∧ _ := hp
          obtain ⟨hpa, hnn, _, _⟩ := hp'
          simp only [parseG] at h
          have heads : ∀ f, f ≤ F → ∀ ys c c',
              parseManyG a f c = .ok (ys, c') → c'.cs.length < c.cs.length →
              ∃ h ∈ effFirst a, h.matches c.cs = true := by
            intro f
            induction f with
            | zero =>
                intro hf ys c c' h0 hlt0
                simp only [parseManyG] at h0
                rw [← ok_cur_inv h0] at hlt0
                simp at hlt0
            | succ f ih' =>
                intro hf ys c c' h0 hlt0
                simp only [parseManyG] at h0
                cases hb : parseG a (f+1) c with
                | error e =>
                    simp only [hb] at h0
                    rw [← ok_cur_inv h0] at hlt0
                    simp at hlt0
                | ok r =>
                    obtain ⟨z, c₁⟩ := r
                    simp only [hb] at h0
                    by_cases hprog : c₁.cs.length < c.cs.length
                    · rw [if_pos hprog] at h0
                      cases hr : parseManyG a f c₁ with
                      | error e => simp [hr] at h0
                      | ok r₂ =>
                          obtain ⟨zs, c₂⟩ := r₂
                          simp only [hr] at h0
                          rw [← ok_cur_inv h0] at hlt0
                          by_cases hf1 : f + 1 = F
                          · exact iha hpa (hf1 ▸ hb) hprog
                          · exact IH (f+1) (by omega) hpa hb hprog
                    · rw [if_neg hprog] at h0
                      rw [← ok_cur_inv h0] at hlt0
                      exact absurd hlt0 hprog
          exact heads F (Nat.le_refl F) xs cur cur' h hlt
      | opt a iha =>
          intro hp x cur cur' h hlt
          have hpa : Predictive a ∧ nullable a = false := hp
          simp only [parseG] at h
          cases ha : parseG a F cur with
          | error e =>
              simp only [ha] at h
              rw [← ok_cur_inv h] at hlt
              simp at hlt
          | ok r =>
              obtain ⟨z, c₁⟩ := r
              simp only [ha] at h
              rw [← ok_cur_inv h] at hlt
              exact iha hpa.1 ha hlt
      | label n a iha =>
          intro hp x cur cur' h hlt
          have hpa : Predictive a := hp
          simp only [parseG] at h
          cases ha : parseG a F cur with
          | error e => simp [ha] at h
          | ok r =>
              obtain ⟨z, c₁⟩ := r
              simp only [ha] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2] at hlt
              exact iha hpa ha hlt
      | rel mm owns don ex nm vld sub ih =>
          intro hp x cur cur' h hlt
          have hps : Predictive sub := hp
          simp only [parseG] at h
          cases ha : parseG sub F cur with
          | error e => simp only [ha] at h; simp at h
          | ok r =>
              obtain ⟨raw, c₁⟩ := r
              simp only [ha] at h
              cases hd : mm.decode raw with
              | none => simp [hd] at h
              | some r =>
                  simp only [hd] at h
                  rw [← ok_cur_inv h] at hlt
                  exact ih hps ha hlt
      | fix m body dec =>
          intro hp x cur cur' h hlt
          have hp' : GrammarE.PredictiveE body body ∧ body.firstE ≠ none ∧
              body.nullableE = false ∧ body.tailSelfFreeE = true := hp
          obtain ⟨hps, hf, hn, ht⟩ := hp'
          simp only [parseG] at h
          obtain ⟨hh, hmem, hm⟩ := GrammarE.parseHeadE body hn hf F h hlt
          have hfsE : GrammarE.effFirstE body.bodyFirsts body = body.bodyFirsts :=
            GrammarE.effFirstE_bodyFirsts body hf
          rw [hfsE] at hmem
          rw [Grammar.effFirst_fix m body dec hf]
          exact ⟨hh, hmem, hm⟩

/-- The closed first-exclusion lemma. -/
theorem Grammar.parseExcludeG :
    ∀ (fuel : Nat) {A : Type} {g : Grammar A}, Predictive g →
      ∀ (k : Nat) (cs : List Char),
      nullable g = false →
      (∀ h ∈ effFirst g, h.matches cs = false) →
      ∃ e, parseG g fuel ⟨k, cs⟩ = .error e := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      intro A g
      induction g with
      | atom L =>
          intro _ k cs hnn hfail
          have h1 : L.head.matches cs = false :=
            hfail L.head (by show L.head ∈ [L.head]; exact List.Mem.head [])
          obtain ⟨e, he⟩ := L.head_fail ⟨k, cs⟩ h1
          exact ⟨e, by simp only [parseG]; exact he⟩
      | seq a b iha ihb =>
          intro hp k cs hnn hfail
          have hp' : Predictive a ∧ Predictive b ∧ _ ∧ _ := hp
          obtain ⟨hpa, hpb, _, _⟩ := hp'
          have hnn' : (nullable a && nullable b) = false := hnn
          cases ha : parseG a F ⟨k, cs⟩ with
          | error e =>
              exact ⟨e, by simp only [parseG]; rw [ha]⟩
          | ok r =>
              obtain ⟨x₁, cur₁⟩ := r
              have hsplit := parseSplitsG F ha
              by_cases hcons : cur₁.cs.length < cs.length
              · obtain ⟨hh, hmem, hm⟩ := parseHeadG F hpa ha hcons
                have hbad : hh.matches cs = false :=
                  hfail hh (List.mem_append_left _ hmem)
                simp [hm] at hbad
              · have hmono : cur₁.cs.length ≤ cs.length := parseMonoG F ha
                have heq0 : cur₁.cs.length = cs.length :=
                  Nat.le_antisymm hmono (Nat.le_of_not_lt hcons)
                obtain ⟨pre, hpre⟩ := hsplit
                have hpre' : cs = pre ++ cur₁.cs := hpre
                have hlen : pre.length = 0 := by
                  have h3 := congrArg List.length hpre'
                  rw [List.length_append, heq0] at h3
                  omega
                have hpre0 : pre = [] := List.length_eq_zero_iff.mp hlen
                have hcs : cur₁.cs = cs := by
                  rw [hpre0] at hpre'
                  simp at hpre'
                  exact hpre'.symm
                have hna : nullable a = true := by
                  cases h2 : nullable a with
                  | false =>
                      have h2c : cur₁.cs.length < cs.length := parseConsumeG F hpa ha h2
                      omega
                  | true => rfl
                have hnb : nullable b = false := by
                  cases h2 : nullable b with
                  | true => simp [hna, h2] at hnn'
                  | false => rfl
                have hfailB : ∀ h ∈ effFirst b, h.matches cur₁.cs = false := by
                  intro hh hmem
                  have hmem2 : hh ∈ effFirst a ++
                      (if nullable a then effFirst b else []) := by
                    rw [hna]
                    exact List.mem_append_right _ hmem
                  rw [hcs]
                  exact hfail hh hmem2
                obtain ⟨e, he⟩ := ihb hpb cur₁.off cur₁.cs hnb hfailB
                have he' : parseG b F cur₁ = .error e := he
                exact ⟨e, by simp only [parseG, ha, he']⟩
      | alt a b iha ihb =>
          intro hp k cs hnn hfail
          have hp' : Predictive a ∧ Predictive b ∧ _ ∧ _ := hp
          obtain ⟨hpa, hpb, _, _⟩ := hp'
          have hnn' : (nullable a || nullable b) = false := hnn
          simp only [Bool.or_eq_false_iff] at hnn'
          have hfailA : ∀ h ∈ effFirst a, h.matches cs = false :=
            fun hh hmem => hfail hh (List.mem_append_left _ hmem)
          have hfailB : ∀ h ∈ effFirst b, h.matches cs = false :=
            fun hh hmem => hfail hh (List.mem_append_right _ hmem)
          obtain ⟨ea, hea⟩ := iha hpa k cs hnn'.1 hfailA
          obtain ⟨eb, heb⟩ := ihb hpb k cs hnn'.2 hfailB
          exact ⟨ParseError.farther ea eb, by simp only [parseG, hea, heb]⟩
      | rep a iha =>
          intro hp k cs hnn _
          simp [nullable] at hnn
      | opt a iha =>
          intro hp k cs hnn _
          simp [nullable] at hnn
      | label n a iha =>
          intro hp k cs hnn hfail
          have hpa : Predictive a := hp
          obtain ⟨e, he⟩ := iha hpa k cs hnn hfail
          have hthis : parseG (.label n a) F ⟨k, cs⟩ =
              .error { e with valid := [n], message := s!"expected {n}", context := TextKit.Label.at n :: e.context } := by
            simp only [parseG, he]
          exact ⟨_, hthis⟩
      | rel mm owns don ex nm vld sub ih =>
          intro hp k cs hnn hfail
          have hps : Predictive sub := hp
          obtain ⟨e, he⟩ := ih hps k cs hnn hfail
          exact ⟨e, by simp only [parseG, he]⟩
      | fix m body dec =>
          intro hp k cs hnn hfail
          have hp' : GrammarE.PredictiveE body body ∧ body.firstE ≠ none ∧
              body.nullableE = false ∧ body.tailSelfFreeE = true := hp
          obtain ⟨hps, hf, hn, ht⟩ := hp'
          have hnnE : GrammarE.nullableE body = false := hn
          have hfailE : ∀ h ∈ GrammarE.effFirstE body.bodyFirsts body,
              h.matches cs = false := by
            intro hh hmem
            apply hfail
            rw [Grammar.effFirst_fix m body dec hf]
            rw [GrammarE.effFirstE_bodyFirsts body hf] at hmem
            exact hmem
          obtain ⟨e, he⟩ := GrammarE.parseExcludeE body hnnE hf F k cs hnnE hfailE
          exact ⟨e, by simp only [parseG]; exact he⟩
/-! ## §5c: law 2 (exactness), closed level -/

/-- print_parse's auxiliary: the payload type UNDER the fuel's ∀ (the
    inner structural induction's generalization requirement — the parked
    file's compile fix: with A fixed at the surface, the fuel-IH gets
    captured into the structural IHs and the seq case's payload
    unification fails). -/
private theorem Grammar.print_parse_aux :
    ∀ (fuel : Nat) {R : Type} (g : Grammar R),
    altCoherent g →
      ∀ {x : R} {cur cur' : Cursor},
      parseG g fuel cur = .ok (x, cur') →
      cur.cs = (printG g x).toList ++ cur'.cs ∧
      cur'.off = cur.off + (printG g x).length ∧
      valueOk g x = true := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      intro R g
      induction g with
      | atom L =>
          intro hco x cur cur' h
          simp only [parseG] at h
          rw [printG_atom]
          exact ⟨L.scan_exact _ _ _ h, L.scan_off _ _ _ h, L.scan_post _ _ _ h⟩
      | seq a b iha ihb =>
          intro hco x cur cur' h
          obtain ⟨hcohA, hcohB⟩ := hco
          simp only [parseG] at h
          cases ha : parseG a F cur with
          | error e => simp only [ha] at h; simp at h
          | ok r =>
              obtain ⟨x₁, cur₁⟩ := r
              cases hb : parseG b F cur₁ with
              | error e => simp only [ha, hb] at h; simp at h
              | ok r₂ =>
                  obtain ⟨y, cur₂⟩ := r₂
                  simp only [ha, hb] at h
                  have hcc := Prod.mk.inj (Except.ok.inj h)
                  obtain ⟨hx1, hx2, hx3⟩ := iha hcohA ha
                  obtain ⟨hy1, hy2, hy3⟩ := ihb hcohB hb
                  rw [← hcc.1, ← hcc.2]
                  rw [printG_seq]
                  refine ⟨?_, ?_, ?_⟩
                  · rw [hx1, hy1, String.toList_append, List.append_assoc]
                  · rw [hy2, hx2, String.length_append]
                    omega
                  · rw [valueOk_seq]
                    simp [hx3, hy3]
      | alt a b iha ihb =>
          intro hco x cur cur' h
          obtain ⟨hcohab, hcohA, hcohB⟩ := hco
          simp only [parseG] at h
          cases ha : parseG a F cur with
          | ok r =>
              obtain ⟨x₁, cur₁⟩ := r
              simp only [ha] at h
              have hcc := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨hx1, hx2, hx3⟩ := iha hcohA ha
              rw [← hcc.1, ← hcc.2]
              rw [printG_alt]
              rw [if_pos hx3]
              refine ⟨hx1, hx2, ?_⟩
              rw [valueOk_alt]
              simp [hx3]
          | error e =>
              simp only [ha] at h
              cases hb : parseG b F cur with
              | ok r =>
                  obtain ⟨x₂, cur₂⟩ := r
                  simp only [hb] at h
                  have hcc := Prod.mk.inj (Except.ok.inj h)
                  obtain ⟨hx1, hx2, hx3⟩ := ihb hcohB hb
                  rw [← hcc.1, ← hcc.2]
                  rw [printG_alt]
                  have hdA : valueOk a x₂ = false := by
                    cases hda : valueOk a x₂ with
                    | true =>
                        have := hcohab x₂ hda
                        simp [hx3] at this
                    | false => rfl
                  rw [if_neg (by simp [hdA])]
                  refine ⟨hx1, hx2, ?_⟩
                  rw [valueOk_alt]
                  simp [hx3]
              | error e' => simp only [hb] at h; simp at h
      | rep a iha =>
          intro hco xs cur cur' h
          simp only [parseG] at h
          have L : ∀ f, f ≤ F → ∀ ys c c',
              parseManyG a f c = .ok (ys, c') →
              c.cs = (ys.foldr (fun z acc => printG a z ++ acc) "").toList ++ c'.cs ∧
              c'.off = c.off + (ys.foldr (fun z acc => printG a z ++ acc) "").length ∧
              ys.all (fun z => valueOk a z) = true := by
            intro f
            induction f with
            | zero =>
                intro hf ys c c' h0
                simp only [parseManyG] at h0
                have hcc := Prod.mk.inj (Except.ok.inj h0)
                rw [← hcc.1, ← hcc.2]
                simp
            | succ f ih' =>
                intro hf ys c c' h0
                simp only [parseManyG] at h0
                cases hb : parseG a (f+1) c with
                | error e =>
                    simp only [hb] at h0
                    have hcc := Prod.mk.inj (Except.ok.inj h0)
                    rw [← hcc.1, ← hcc.2]
                    simp
                | ok r =>
                    obtain ⟨z, c₁⟩ := r
                    simp only [hb] at h0
                    have hbody := (show f + 1 = F ∨ f + 1 < F from by omega).elim
                      (fun hf1 => iha hco (hf1 ▸ hb))
                      (fun hlt => IH (f+1) hlt (g := a) hco hb)
                    obtain ⟨hz1, hz2, hz3⟩ := hbody
                    by_cases hprog : c₁.cs.length < c.cs.length
                    · rw [if_pos hprog] at h0
                      cases hr : parseManyG a f c₁ with
                      | error e => simp [hr] at h0
                      | ok r₂ =>
                          obtain ⟨zs, c₂⟩ := r₂
                          simp only [hr] at h0
                          have hcc := Prod.mk.inj (Except.ok.inj h0)
                          obtain ⟨hzs1, hzs2, hzs3⟩ := ih' (by omega) zs c₁ c₂ hr
                          rw [← hcc.1, ← hcc.2]
                          show (c.cs = ((printG a z ++ zs.foldr (fun w acc => printG a w ++ acc) "")).toList ++ c₂.cs ∧
                                c₂.off = c.off + (printG a z ++ zs.foldr (fun w acc => printG a w ++ acc) "").length ∧
                                ((z :: zs).all fun w => valueOk a w) = true)
                          refine ⟨?_, ?_, ?_⟩
                          · rw [hz1, hzs1, String.toList_append, List.append_assoc]
                          · rw [hzs2, hz2, String.length_append]
                            omega
                          · simp [hz3, hzs3]
                    · rw [if_neg hprog] at h0
                      have hcc := Prod.mk.inj (Except.ok.inj h0)
                      rw [← hcc.1, ← hcc.2]
                      show (c.cs = ((printG a z ++ [].foldr (fun w acc => printG a w ++ acc) "")).toList ++ c₁.cs ∧
                            c₁.off = c.off + (printG a z ++ [].foldr (fun w acc => printG a w ++ acc) "").length ∧
                            ([z].all fun w => valueOk a w) = true)
                      refine ⟨?_, ?_, ?_⟩
                      · rw [hz1]
                        simp
                      · rw [hz2]
                        simp
                      · simp [hz3]
          obtain ⟨L1, L2, L3⟩ := L F (Nat.le_refl F) xs cur cur' h
          rw [printG_rep]
          exact ⟨L1, L2, by rw [valueOk_rep]; exact L3⟩
      | opt a iha =>
          intro hco x cur cur' h
          simp only [parseG] at h
          cases ha : parseG a F cur with
          | error e =>
              simp only [ha] at h
              have hcc := Prod.mk.inj (Except.ok.inj h)
              rw [← hcc.1, ← hcc.2]
              rw [printG_opt_none, valueOk_opt_none]
              simp
          | ok r =>
              obtain ⟨z, c₁⟩ := r
              simp only [ha] at h
              have hcc := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨hz1, hz2, hz3⟩ := iha hco ha
              rw [← hcc.1, ← hcc.2]
              rw [printG_opt_some, valueOk_opt_some]
              exact ⟨hz1, hz2, hz3⟩
      | label n a iha =>
          intro hco x cur cur' h
          simp only [parseG] at h
          cases ha : parseG a F cur with
          | error e => simp [ha] at h
          | ok r =>
              obtain ⟨z, c₁⟩ := r
              simp only [ha] at h
              have hcc := Prod.mk.inj (Except.ok.inj h)
              obtain ⟨hz1, hz2, hz3⟩ := iha hco ha
              rw [← hcc.1, ← hcc.2]
              rw [printG_label, valueOk_label]
              exact ⟨hz1, hz2, hz3⟩
      | rel mm owns don ex nm vld sub ih =>
          intro hco x cur cur' h
          simp only [parseG] at h
          cases ha : parseG sub F cur with
          | error e => simp only [ha] at h; simp at h
          | ok r =>
              obtain ⟨raw, c₁⟩ := r
              simp only [ha] at h
              cases hd : mm.decode raw with
              | none => simp [hd] at h
              | some r =>
                  simp only [hd] at h
                  have hcc := Prod.mk.inj (Except.ok.inj h)
                  obtain ⟨hz1, hz2, hz3⟩ := ih hco ha
                  rw [← hcc.1, ← hcc.2]
                  have hex : mm.encode r = raw := ex raw r hd
                  have hown : owns r = true := don raw r hd
                  rw [printG_rel, valueOk_rel]
                  rw [hex]
                  exact ⟨hz1, hz2, by simp [hown, hz3]⟩
      | fix m body dec =>
          intro hco x cur cur' h
          simp only [parseG] at h
          have hcoE : GrammarE.altCoherentE m body dec body := hco
          obtain ⟨hx1, hx2, hx3⟩ := GrammarE.print_parse_E body m dec hcoE F hcoE h
          rw [printG_fix]
          have hbr : printFix m body dec x =
              GrammarE.printWalk body x (fun y _ => fixValueOk m body dec y)
                (fun y _ => printFix m body dec y) :=
            printFix_unfold m body dec x
          rw [hbr]
          refine ⟨hx1, hx2, ?_⟩
          have h4 : fixValueOk m body dec x =
              GrammarE.valueOkWalk body x (fun y _ => fixValueOk m body dec y) :=
            fixValueOk_unfold m body dec x
          show Grammar.fixValueOk m body dec x = true
          rw [h4]
          exact hx3

/-- THE exactness law, closed level (design v2 §5): a successful parse
    consumed EXACTLY the print of its result, with the offsets and the
    parsed-values-are-owned conjunct. Premises: the branch-coherence
    fold ONLY (the round-one discovery — see `altCoherent`'s docstring:
    two rel-branches whose codecs decode different spellings INTO the
    same value are first-disjoint, accepted, and exactness-false). The
    migration targets discharge it by ctor discrimination
    (`altCoherent_alt_rel_rel`). -/
theorem Grammar.print_parse {A : Type} :
    ∀ (g : Grammar A) (fuel : Nat), altCoherent g →
      ∀ {x : A} {cur cur' : Cursor},
      parseG g fuel cur = .ok (x, cur') →
      cur.cs = (printG g x).toList ++ cur'.cs ∧
      cur'.off = cur.off + (printG g x).length ∧
      valueOk g x = true :=
  fun g fuel => print_parse_aux fuel g

/-! ## §6: law 1 (parse∘print) — the fuel slack + the junction family -/

/-- The decidable disjointness is SYMMETRIC (v2 §6.2): the junction's
    and the alt case's direction flip (the row gives `disj s1 s2`; the
    text exhibits `s2` matching; the conclusion needs `s1` failing). -/
theorem HeadSpec.disj_symm (h1 h2 : HeadSpec) : h1.disj h2 = h2.disj h1 := by
  cases h1 <;> cases h2 <;> simp [disj, Bool.or_comm]

/-- Under the lexemes' `head_ne`, every head in `firstE g` fails the
    empty text (v2 §6.2; the `none` cases vacuous). -/
theorem GrammarE.firstE_head_ne {R : Type} :
    {A : Type} → (g : GrammarE R A) → (hs : List HeadSpec) →
    firstE g = Option.some hs → ∀ h ∈ hs, h.matches [] = false := by
  intro A g
  induction g with
  | atomE L =>
      intro hs h
      simp only [firstE] at h
      cases h
      intro h2 hmem
      rw [show h2 = L.head from List.mem_singleton.mp hmem]
      exact L.head_ne
  | seqE a b iha ihb =>
      intro hs h
      simp only [firstE] at h
      cases hfa : firstE a with
      | none => rw [hfa] at h; simp at h
      | some ha =>
          rw [hfa] at h
          cases hna : nullableE a with
          | false =>
              simp [hna] at h
              subst h
              intro h2 hmem
              exact iha ha hfa h2 hmem
          | true =>
              simp [hna] at h
              cases hfb : firstE b with
              | none => rw [hfb] at h; simp at h
              | some hb =>
                  rw [hfb] at h
                  simp only [Option.some.injEq] at h
                  subst h
                  intro h2 hmem
                  rcases List.mem_append.mp hmem with h1 | h2'
                  · exact iha ha hfa h2 h1
                  · exact ihb hb hfb h2 h2'
  | altE a b iha ihb =>
      intro hs h
      simp only [firstE] at h
      cases hfa : firstE a with
      | none => rw [hfa] at h; simp at h
      | some ha =>
          cases hfb : firstE b with
          | none => rw [hfa, hfb] at h; simp at h
          | some hb =>
              rw [hfa, hfb] at h
              simp only [Option.some.injEq] at h
              subst h
              intro h2 hmem
              rcases List.mem_append.mp hmem with h1 | h2'
              · exact iha ha hfa h2 h1
              · exact ihb hb hfb h2 h2'
  | repE a iha => intro hs h; simp only [firstE] at h; exact iha hs h
  | optE a iha => intro hs h; simp only [firstE] at h; exact iha hs h
  | labelE n a iha => intro hs h; simp only [firstE] at h; exact iha hs h
  | relE m owns don ex nm vld sub ih => intro hs h; simp only [firstE] at h; exact ih hs h
  | selfE => intro hs h; simp [firstE] at h

/-- The effective firsts' heads fail `[]` when the parameter's do
    (v2 §6.2's corollary face). -/
theorem GrammarE.effFirstE_head_ne {R : Type} :
    {A : Type} → (g : GrammarE R A) → (fs : List HeadSpec) →
    (∀ h ∈ fs, h.matches [] = false) → ∀ h ∈ effFirstE fs g, h.matches [] = false := by
  intro A g
  induction g with
  | atomE L =>
      intro fs _ h2 hmem
      have h2' : h2 = L.head := List.mem_singleton.mp hmem
      rw [h2']
      exact L.head_ne
  | seqE a b iha ihb =>
      intro fs hfs h2 hmem
      have hmem' : h2 ∈ effFirstE fs a ++ (if nullableE a then effFirstE fs b else []) := hmem
      rcases List.mem_append.mp hmem' with h1 | h1
      · exact iha fs hfs h2 h1
      · cases hna : nullableE a with
        | false => simp [hna] at h1
        | true => simp only [hna] at h1; exact ihb fs hfs h2 h1
  | altE a b iha ihb =>
      intro fs hfs h2 hmem
      have hmem' : h2 ∈ effFirstE fs a ++ effFirstE fs b := hmem
      rcases List.mem_append.mp hmem' with h1 | h1
      · exact iha fs hfs h2 h1
      · exact ihb fs hfs h2 h1
  | repE a iha => intro fs hfs h2 hmem; exact iha fs hfs h2 hmem
  | optE a iha => intro fs hfs h2 hmem; exact iha fs hfs h2 hmem
  | labelE n a iha => intro fs hfs h2 hmem; exact iha fs hfs h2 hmem
  | relE m owns don ex nm vld sub ih => intro fs hfs h2 hmem; exact ih fs hfs h2 hmem
  | selfE => intro fs hfs h2 hmem; exact hfs h2 hmem

/-- The closed effective firsts' heads fail `[]` (v2 §6.2's closed
    twin — the `fix` arm rides `firstE_head_ne` + `effFirstE_head_ne`). -/
theorem Grammar.effFirst_head_ne :
    {A : Type} → (g : Grammar A) → ∀ h ∈ effFirst g, h.matches [] = false := by
  intro A g
  induction g with
  | atom L =>
      intro h2 hmem
      have h2' : h2 = L.head := List.mem_singleton.mp hmem
      rw [h2']
      exact L.head_ne
  | seq a b iha ihb =>
      intro h2 hmem
      have hmem' : h2 ∈ effFirst a ++ (if nullable a then effFirst b else []) := hmem
      rcases List.mem_append.mp hmem' with h1 | h1
      · exact iha h2 h1
      · cases hna : nullable a with
        | false => simp [hna] at h1
        | true => simp only [hna] at h1; exact ihb h2 h1
  | alt a b iha ihb =>
      intro h2 hmem
      have hmem' : h2 ∈ effFirst a ++ effFirst b := hmem
      rcases List.mem_append.mp hmem' with h1 | h1
      · exact iha h2 h1
      · exact ihb h2 h1
  | rep a iha => intro h2 hmem; exact iha h2 hmem
  | opt a iha => intro h2 hmem; exact iha h2 hmem
  | label n a iha => intro h2 hmem; exact iha h2 hmem
  | rel m owns don ex nm vld sub ih => intro h2 hmem; exact ih h2 hmem
  | fix m body dec =>
      intro h2 hmem
      have hmem' : h2 ∈ GrammarE.effFirstE ((GrammarE.firstE body).getD []) body := hmem
      cases hfsb : GrammarE.firstE body with
      | none =>
          rw [hfsb] at hmem'
          exact GrammarE.effFirstE_head_ne body [] (fun h3 h3m => absurd h3m (by simp)) h2 hmem'
      | some hs =>
          have hmem'' : h2 ∈ GrammarE.effFirstE hs body := by rw [hfsb] at hmem'; exact hmem'
          have hbf : hs = body.bodyFirsts := by simp [GrammarE.bodyFirsts, hfsb]
          rw [hbf] at hmem'' hfsb
          have hne : GrammarE.firstE body ≠ none := by rw [hfsb]; simp
          have hEq : GrammarE.effFirstE body.bodyFirsts body = body.bodyFirsts :=
            GrammarE.effFirstE_bodyFirsts body hne
          rw [hEq] at hmem''
          exact GrammarE.firstE_head_ne body body.bodyFirsts hfsb h2 hmem''

/-- The munch fold preserves `isSome` (v2 §6.2): atoms are always
    `some`, the combinators preserve — the junction's `getD []`
    membership restrictions stand on this. -/
theorem GrammarE.tailMunchE_isSome {R : Type} :
    {A : Type} → (tm : Option (List (Char → Bool))) → (g : GrammarE R A) →
    tm.isSome = true → (tailMunchE tm g).isSome = true := by
  intro A tm g
  induction g with
  | atomE L => intro _; rfl
  | seqE a b iha ihb =>
      intro ht
      show (match tailMunchE tm b with
        | Option.none => Option.none
        | Option.some hb => if nullableE b then match tailMunchE tm a with
            | Option.none => Option.none
            | Option.some ha => Option.some (ha ++ hb)
          else Option.some hb).isSome = true
      have hb := ihb ht
      cases hmb : tailMunchE tm b with
      | none => rw [hmb] at hb; simp at hb
      | some hb' =>
          cases hna : nullableE b with
          | false => rfl
          | true =>
              have ha := iha ht
              cases hma : tailMunchE tm a with
              | none => rw [hma] at ha; simp at ha
              | some ha' => simp
  | altE a b iha ihb =>
      intro ht
      show (match tailMunchE tm a, tailMunchE tm b with
        | Option.some ha, Option.some hb => Option.some (ha ++ hb)
        | _, _ => Option.none).isSome = true
      have ha := iha ht
      have hb := ihb ht
      cases hma : tailMunchE tm a with
      | none => rw [hma] at ha; simp at ha
      | some ha' =>
          cases hmb : tailMunchE tm b with
          | none => rw [hmb] at hb; simp at hb
          | some hb' => simp
  | repE a iha => intro ht; simp only [tailMunchE]; exact iha ht
  | optE a iha => intro ht; simp only [tailMunchE]; exact iha ht
  | labelE n a iha => intro ht; simp only [tailMunchE]; exact iha ht
  | relE m owns don ex nm vld sub ih => intro ht; simp only [tailMunchE]; exact ih ht
  | selfE => intro ht; exact ht

/-- The tail-self-free body's munch fold is `some` (v2 §6.2's
    `bodyTailMunch_isOne` — the none seed is never read: the only
    none-producing leaf is `selfE`, which `tailSelfFreeE` excludes). -/
theorem GrammarE.tailSelfFreeE_munch_isSome {R : Type} :
    {A : Type} → (g : GrammarE R A) → tailSelfFreeE g = true →
    (tailMunchE Option.none g).isSome = true := by
  intro A g
  induction g with
  | atomE L => intro _; rfl
  | seqE a b iha ihb =>
      intro htsf
      simp only [tailSelfFreeE, Bool.and_eq_true] at htsf
      show (match tailMunchE Option.none b with
        | Option.none => Option.none
        | Option.some hb => if nullableE b then match tailMunchE Option.none a with
            | Option.none => Option.none
            | Option.some ha => Option.some (ha ++ hb)
          else Option.some hb).isSome = true
      have hb := ihb htsf.1
      cases hmb : tailMunchE Option.none b with
      | none => rw [hmb] at hb; simp at hb
      | some hb' =>
          cases hna : nullableE b with
          | false => rfl
          | true =>
              rw [hna] at htsf
              have ha := iha htsf.2
              cases hma : tailMunchE Option.none a with
              | none => rw [hma] at ha; simp at ha
              | some ha' => simp
  | altE a b iha ihb =>
      intro htsf
      simp only [tailSelfFreeE, Bool.and_eq_true] at htsf
      show (match tailMunchE Option.none a, tailMunchE Option.none b with
        | Option.some ha, Option.some hb => Option.some (ha ++ hb)
        | _, _ => Option.none).isSome = true
      have ha := iha htsf.1
      have hb := ihb htsf.2
      cases hma : tailMunchE Option.none a with
      | none => rw [hma] at ha; simp at ha
      | some ha' =>
          cases hmb : tailMunchE Option.none b with
          | none => rw [hmb] at hb; simp at hb
          | some hb' => simp
  | repE a iha => intro htsf; simp only [tailSelfFreeE] at htsf; simp only [tailMunchE]; exact iha htsf
  | optE a iha => intro htsf; simp only [tailSelfFreeE] at htsf; simp only [tailMunchE]; exact iha htsf
  | labelE n a iha => intro htsf; simp only [tailSelfFreeE] at htsf; simp only [tailMunchE]; exact iha htsf
  | relE m owns don ex nm vld sub ih => intro htsf; simp only [tailSelfFreeE] at htsf; simp only [tailMunchE]; exact ih htsf
  | selfE => intro htsf; simp [tailSelfFreeE] at htsf

/-- The fix body's tail munches are `some` (the junction's row-TM
    honesty lemma, v2 §6.2). -/
theorem GrammarE.bodyTailMunch_isSome {R : Type} (sb : GrammarE R R)
    (htf : sb.tailSelfFreeE = true) : (bodyTailMunch sb).isSome = true :=
  tailSelfFreeE_munch_isSome sb htf

/-- The guard-aware fuel slack (v2 §6.1): an UNGUARDED node (a
    `selfE` reachable without consumption) needs one extra unit;
    guarded nodes ride the input bound. WF-FIX makes every reachable
    re-entry guarded (`firstE_some_guardE`). -/
def GrammarE.guardSlack (g : GrammarE R A) : Nat := if guardE g then 1 else 2

/-- The closed-level slack (always 1 under the certificate —
    `predictive_guard`). -/
def Grammar.guardSlack (g : Grammar R) : Nat := if guard g then 1 else 2

/-- The certificate's guard content: every predictive grammar is
    guarded (v2 §6.1 — the fix case via `firstE_some_guardE`; the
    fix-free nodes have no `false` source in the guard fold). -/
theorem Grammar.predictive_guard :
    {A : Type} → (g : Grammar A) → Predictive g → guard g = true := by
  intro A g
  induction g with
  | atom L => intro _; rfl
  | seq a b iha ihb =>
      intro hp
      obtain ⟨hpa, hpb, _, _⟩ := hp
      show (guard a && (if nullable a then guard b else true)) = true
      cases hna : nullable a with
      | false => simp [iha hpa]
      | true => simp [iha hpa, ihb hpb]
  | alt a b iha ihb =>
      intro hp
      obtain ⟨hpa, hpb, _, _⟩ := hp
      show (guard a && guard b) = true
      simp [iha hpa, ihb hpb]
  | rep a iha => intro hp; obtain ⟨hpa, _, _, _⟩ := hp; exact iha hpa
  | opt a iha => intro hp; obtain ⟨hpa, _⟩ := hp; exact iha hpa
  | label n a iha => intro hp; exact iha hp
  | rel m owns don ex nm vld sub ih => intro hp; exact ih hp
  | fix m body dec =>
      intro hp
      obtain ⟨_, hf, _, _⟩ := hp
      show GrammarE.guardE body = true
      exact GrammarE.firstE_some_guardE body hf

/-- The empty suffix is always an adequate tail for the OPEN family's
    tail-self-free nodes (v2 §6.6): every effective-first head fails
    `[]` (the `head_ne` family), and `tailSelfFreeE` makes the tok
    irrelevant — the `selfE` leaves are never consulted. -/
theorem GrammarE.tailOkE_nil {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) (fs : List HeadSpec)
    (hfs : ∀ h ∈ fs, h.matches [] = false) :
    {A : Type} → (g : GrammarE R A) → tailSelfFreeE g = true →
    ∀ (x : A), tailOkE m sb dec fs (fun _ _ => false) g x [] = true := by
  intro A g
  induction g with
  | atomE L =>
      intro _ x
      rw [GrammarE.tailOkE_atomE]
      cases L.munch with
      | none => rfl
      | some p => simp
  | seqE a b iha ihb =>
      intro htsf x
      obtain ⟨p, q⟩ := x
      have htsf' := htsf
      simp only [tailSelfFreeE, Bool.and_eq_true] at htsf'
      rw [GrammarE.tailOkE_seqE]
      rw [ihb htsf'.1 q]
      cases hb : nullableE b with
      | false => rfl
      | true =>
          have hta : a.tailSelfFreeE = true := by
            have h3 := htsf'.2
            rw [hb] at h3
            simpa using h3
          rw [iha hta p]
          simp
  | altE a b iha ihb =>
      intro htsf x
      have htsf' := htsf
      simp only [tailSelfFreeE, Bool.and_eq_true] at htsf'
      obtain ⟨ht1, ht2⟩ := htsf'
      rw [GrammarE.tailOkE_altE]
      split
      · exact iha ht1 x
      · rw [ihb ht2 x]
        cases hb : nullableE b with
        | false => rfl
        | true =>
            have hall : (effFirstE fs a).all (fun h => !h.matches []) = true :=
              List.all_eq_true.mpr (fun h2 h2m => by
                have h4 := GrammarE.effFirstE_head_ne a fs hfs h2 h2m
                simp [h4])
            simp [hall]
  | repE a iha =>
      intro htsf xs
      rw [GrammarE.tailOkE_repE, Bool.and_eq_true]
      exact ⟨List.all_eq_true.mpr (fun h2 h2m => by
          have h4 := GrammarE.effFirstE_head_ne a fs hfs h2 h2m
          simp [h4]),
        List.all_eq_true.mpr (fun z _ => iha htsf z)⟩
  | optE a iha =>
      intro htsf x
      cases x with
      | none =>
          rw [GrammarE.tailOkE_optE_none]
          exact List.all_eq_true.mpr (fun h2 h2m => by
            have h4 := GrammarE.effFirstE_head_ne a fs hfs h2 h2m
            simp [h4])
      | some z =>
          rw [GrammarE.tailOkE_optE_some]
          exact iha htsf z
  | labelE n a iha => intro htsf x; exact iha htsf x
  | relE mm owns don ex nm vld sub ih => intro htsf x; exact ih htsf (mm.encode x)
  | selfE => intro htsf; simp [tailSelfFreeE] at htsf

/-- THE empty-suffix law (v2 §6.6), closed level. The `fix` arm rides
    the certificate's `tailSelfFreeE` row (the dead tok is irrelevant
    on a tail-self-free body — `tailOkE_tok_irrel` against the trivial
    `fun _ _ => true`), so no AccD recursion is needed. -/
theorem Grammar.tailOk_nil :
    {A : Type} → (g : Grammar A) → Predictive g → ∀ x : A, tailOk g x [] = true := by
  intro A g
  induction g with
  | atom L =>
      intro _ x
      simp only [Grammar.tailOk]
      cases L.munch with
      | none => rfl
      | some p => simp
  | seq a b iha ihb =>
      intro hp x
      obtain ⟨p, q⟩ := x
      obtain ⟨hpa, hpb, _, _⟩ := hp
      simp only [Grammar.tailOk]
      rw [ihb hpb q]
      cases hb : nullable b with
      | false => rfl
      | true => rw [iha hpa p]; simp
  | alt a b iha ihb =>
      intro hp x
      obtain ⟨hpa, hpb, _, _⟩ := hp
      simp only [Grammar.tailOk]
      split
      · exact iha hpa x
      · rw [ihb hpb x]
        cases hb : nullable b with
        | false => rfl
        | true =>
            have hall : (effFirst a).all (fun h => !h.matches []) = true :=
              List.all_eq_true.mpr (fun h2 h2m => by
                have h4 := Grammar.effFirst_head_ne a h2 h2m
                simp [h4])
            simp [hall]
  | rep a iha =>
      intro hp xs
      obtain ⟨hpa, _, _, _⟩ := hp
      simp only [Grammar.tailOk]
      rw [Bool.and_eq_true]
      exact ⟨List.all_eq_true.mpr (fun h2 h2m => by
          have h4 := Grammar.effFirst_head_ne a h2 h2m
          simp [h4]),
        List.all_eq_true.mpr (fun z _ => iha hpa z)⟩
  | opt a iha =>
      intro hp x
      obtain ⟨hpa, _⟩ := hp
      simp only [Grammar.tailOk]
      cases x with
      | none =>
          exact List.all_eq_true.mpr (fun h2 h2m => by
            have h4 := Grammar.effFirst_head_ne a h2 h2m
            simp [h4])
      | some z => exact iha hpa z
  | label n a iha => intro hp x; exact iha hp x
  | rel mm owns don ex nm vld sub ih => intro hp x; exact ih hp (mm.encode x)
  | fix m body dec =>
      intro hp x
      obtain ⟨_, hf, _, htf⟩ := hp
      simp only [Grammar.tailOk]
      rw [GrammarE.tailOkE_tok_irrel m body dec ((GrammarE.firstE body).getD []) body htf
        (fun y sfx' => GrammarE.tailOkE m body dec ((GrammarE.firstE body).getD [])
          (fun _ _ => false) body y sfx') (fun _ _ => false) x []]
      have hfails : ∀ h3 ∈ (GrammarE.firstE body).getD [], h3.matches [] = false := by
        intro h3 h3m
        cases hfsb : GrammarE.firstE body with
        | none => rw [hfsb] at h3m; simp at h3m
        | some hs =>
            have h3' : h3 ∈ hs := by rw [hfsb] at h3m; simpa using h3m
            exact GrammarE.firstE_head_ne body hs hfsb h3 h3'
      exact GrammarE.tailOkE_nil m body dec ((GrammarE.firstE body).getD []) hfails body htf x

/-! ## §6.3's membership helpers (the junction's row-restriction surface) -/

-- The folds' seq/alt/rep/opt shapes put the sub-folds under `if`s and
-- appends; the junction's induction restricts the (seq/alt/rep, b) rows
-- to the sub-junction rows through these. `if_pos` does the
-- Bool-coercion reduction (the folds' if-conditions are `nullable = true`).

theorem GrammarE.tailFirstE_seqR {R : Type} :
    ∀ {A B : Type} (fs tf : List HeadSpec) (a : GrammarE R A) (b : GrammarE R B),
    ∀ s ∈ tailFirstE fs tf b, s ∈ tailFirstE fs tf (.seqE a b) := by
  intro A B fs tf a b s hs
  show s ∈ tailFirstE fs tf b ++ (if nullableE b then tailFirstE fs tf a else [])
  exact List.mem_append_left _ hs

theorem GrammarE.tailFirstE_seqL {R : Type} :
    ∀ {A B : Type} (fs tf : List HeadSpec) (a : GrammarE R A) (b : GrammarE R B),
    nullableE b = true → ∀ s ∈ tailFirstE fs tf a, s ∈ tailFirstE fs tf (.seqE a b) := by
  intro A B fs tf a b hb s hs
  show s ∈ tailFirstE fs tf b ++ (if nullableE b then tailFirstE fs tf a else [])
  rw [if_pos hb]
  exact List.mem_append_right _ hs

theorem GrammarE.tailFirstE_altL {R : Type} :
    ∀ {A : Type} (fs tf : List HeadSpec) (a b : GrammarE R A),
    ∀ s ∈ tailFirstE fs tf a, s ∈ tailFirstE fs tf (.altE a b) := by
  intro A fs tf a b s hs
  show s ∈ tailFirstE fs tf a ++ tailFirstE fs tf b ++
    (if nullableE b then effFirstE fs a else [])
  exact List.mem_append_left _ (List.mem_append_left (tailFirstE fs tf b) hs)

theorem GrammarE.tailFirstE_altR {R : Type} :
    ∀ {A : Type} (fs tf : List HeadSpec) (a b : GrammarE R A),
    ∀ s ∈ tailFirstE fs tf b, s ∈ tailFirstE fs tf (.altE a b) := by
  intro A fs tf a b s hs
  show s ∈ tailFirstE fs tf a ++ tailFirstE fs tf b ++
    (if nullableE b then effFirstE fs a else [])
  exact List.mem_append_left _ (List.mem_append_right (tailFirstE fs tf a) hs)

/-- The alt's third clause: the LEFT branch's effective firsts join the
    tail-firsts exactly when the right branch is nullable (the
    value-dependent alt clause's exclusion surface). -/
theorem GrammarE.tailFirstE_alt_third {R : Type} :
    ∀ {A : Type} (fs tf : List HeadSpec) (a b : GrammarE R A),
    nullableE b = true → ∀ s ∈ effFirstE fs a, s ∈ tailFirstE fs tf (.altE a b) := by
  intro A fs tf a b hb s hs
  show s ∈ tailFirstE fs tf a ++ tailFirstE fs tf b ++
    (if nullableE b then effFirstE fs a else [])
  rw [if_pos hb]
  exact List.mem_append_right (tailFirstE fs tf a ++ tailFirstE fs tf b) hs

theorem GrammarE.tailFirstE_rep {R : Type} :
    ∀ {A : Type} (fs tf : List HeadSpec) (a : GrammarE R A),
    ∀ s ∈ tailFirstE fs tf a, s ∈ tailFirstE fs tf (.repE a) := by
  intro A fs tf a s hs
  show s ∈ effFirstE fs a ++ tailFirstE fs tf a
  exact List.mem_append_right _ hs

theorem GrammarE.tailFirstE_opt {R : Type} :
    ∀ {A : Type} (fs tf : List HeadSpec) (a : GrammarE R A),
    ∀ s ∈ tailFirstE fs tf a, s ∈ tailFirstE fs tf (.optE a) := by
  intro A fs tf a s hs
  show s ∈ effFirstE fs a ++ tailFirstE fs tf a
  exact List.mem_append_right _ hs

/-- The stop-head surface for the rep/opt stop conjuncts: the body's
    effective firsts are tail-firsts of the rep/opt node. -/
theorem GrammarE.tailFirstE_rep_eff {R : Type} :
    ∀ {A : Type} (fs tf : List HeadSpec) (a : GrammarE R A),
    ∀ s ∈ effFirstE fs a, s ∈ tailFirstE fs tf (.repE a) := by
  intro A fs tf a s hs
  show s ∈ effFirstE fs a ++ tailFirstE fs tf a
  exact List.mem_append_left _ hs

theorem GrammarE.tailFirstE_opt_eff {R : Type} :
    ∀ {A : Type} (fs tf : List HeadSpec) (a : GrammarE R A),
    ∀ s ∈ effFirstE fs a, s ∈ tailFirstE fs tf (.optE a) := by
  intro A fs tf a s hs
  show s ∈ effFirstE fs a ++ tailFirstE fs tf a
  exact List.mem_append_left _ hs

theorem GrammarE.tailMunchE_seqR {R : Type} :
    ∀ {A B : Type} (tm : Option (List (Char → Bool))) (a : GrammarE R A) (b : GrammarE R B),
    tm.isSome = true →
    ∀ p ∈ (tailMunchE tm b).getD [], p ∈ (tailMunchE tm (.seqE a b)).getD [] := by
  intro A B tm a b ht p hp
  have hd : (tailMunchE tm b).isSome = true := tailMunchE_isSome tm b ht
  cases hdd : tailMunchE tm b with
  | none => rw [hdd] at hd; simp at hd
  | some hb =>
      cases hna : nullableE b with
      | false =>
          have hval : tailMunchE tm (.seqE a b) = Option.some hb := by
            simp [tailMunchE, hdd, hna]
          rw [hval]
          rw [hdd] at hp
          simpa using hp
      | true =>
          have hc : (tailMunchE tm a).isSome = true := tailMunchE_isSome tm a ht
          cases hcc : tailMunchE tm a with
          | none => rw [hcc] at hc; simp at hc
          | some ha =>
              have hval : tailMunchE tm (.seqE a b) = Option.some (ha ++ hb) := by
                simp [tailMunchE, hdd, hna, hcc]
              rw [hval]
              have hp' : p ∈ hb := by rw [hdd] at hp; simpa using hp
              exact List.mem_append_right _ hp'

theorem GrammarE.tailMunchE_seqL {R : Type} :
    ∀ {A B : Type} (tm : Option (List (Char → Bool))) (a : GrammarE R A) (b : GrammarE R B),
    tm.isSome = true → nullableE b = true →
    ∀ p ∈ (tailMunchE tm a).getD [], p ∈ (tailMunchE tm (.seqE a b)).getD [] := by
  intro A B tm a b ht hb p hp
  have hd : (tailMunchE tm b).isSome = true := tailMunchE_isSome tm b ht
  cases hdd : tailMunchE tm b with
  | none => rw [hdd] at hd; simp at hd
  | some hb' =>
      have hc : (tailMunchE tm a).isSome = true := tailMunchE_isSome tm a ht
      cases hcc : tailMunchE tm a with
      | none => rw [hcc] at hc; simp at hc
      | some ha =>
          have hval : tailMunchE tm (.seqE a b) = Option.some (ha ++ hb') := by
            simp [tailMunchE, hdd, hb, hcc]
          rw [hval]
          have hp' : p ∈ ha := by rw [hcc] at hp; simpa using hp
          exact List.mem_append_left _ hp'

theorem GrammarE.tailMunchE_altL {R : Type} :
    ∀ {A : Type} (tm : Option (List (Char → Bool))) (a b : GrammarE R A),
    tm.isSome = true →
    ∀ p ∈ (tailMunchE tm a).getD [], p ∈ (tailMunchE tm (.altE a b)).getD [] := by
  intro A tm a b ht p hp
  have ha : (tailMunchE tm a).isSome = true := tailMunchE_isSome tm a ht
  have hb : (tailMunchE tm b).isSome = true := tailMunchE_isSome tm b ht
  cases hma : tailMunchE tm a with
  | none => rw [hma] at ha; simp at ha
  | some ma =>
      cases hmb : tailMunchE tm b with
      | none => rw [hmb] at hb; simp at hb
      | some mb =>
          have hval : tailMunchE tm (.altE a b) = Option.some (ma ++ mb) := by
            simp [tailMunchE, hma, hmb]
          rw [hval]
          have hp' : p ∈ ma := by rw [hma] at hp; simpa using hp
          exact List.mem_append_left _ hp'

theorem GrammarE.tailMunchE_altR {R : Type} :
    ∀ {A : Type} (tm : Option (List (Char → Bool))) (a b : GrammarE R A),
    tm.isSome = true →
    ∀ p ∈ (tailMunchE tm b).getD [], p ∈ (tailMunchE tm (.altE a b)).getD [] := by
  intro A tm a b ht p hp
  have ha : (tailMunchE tm a).isSome = true := tailMunchE_isSome tm a ht
  have hb : (tailMunchE tm b).isSome = true := tailMunchE_isSome tm b ht
  cases hma : tailMunchE tm a with
  | none => rw [hma] at ha; simp at ha
  | some ma =>
      cases hmb : tailMunchE tm b with
      | none => rw [hmb] at hb; simp at hb
      | some mb =>
          have hval : tailMunchE tm (.altE a b) = Option.some (ma ++ mb) := by
            simp [tailMunchE, hma, hmb]
          rw [hval]
          have hp' : p ∈ mb := by rw [hmb] at hp; simpa using hp
          exact List.mem_append_right _ hp'

def GrammarE.tokStar (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) (y : R) (sfx : List Char) : Bool :=
  GrammarE.tailOkE m sb dec (GrammarE.bodyFirsts sb) (fun _ _ => false) sb y sfx

/-! ## §6.3: THE JUNCTION FAMILY (the wall-1 lemma set) -/

set_option linter.unusedVariables false in
-- the `path` binder inside the `HSJ` hypothesis is the statement's own
-- spelling (byte-pinned by the E/G transfer's consumers) — unused in the body
open Grammar in
/-- THE junction lemma, open level (v2 §6.3). Induction on `a` (the
    LEFT grammar; `b` fixed). The two row premises are EXPLICIT
    quantified facts (not the `PredictiveE` bundle) so the induction
    re-derives sub-junction rows from the outer row by list-membership
    restriction. `HSJ` is the `selfE`-leaf interface — the
    `printBundleE`/`printFixBundle` pattern — carrying the closure
    hypothesis the AccD recursion at the fix level consumes (each self
    value is measure-smaller, so `junctionEG`'s IH applies exactly
    under it). The `hnull` premise is the caller's exact second
    conjunct (v2 §6.3's caller-side note): the empty-print branch of
    the goal reads it AT the whole-`a` node. -/

theorem GrammarE.junctionE {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x)
    (hn : sb.nullableE = false) (hf : sb.firstE ≠ none)
    (htf : sb.tailSelfFreeE = true) :
    ∀ {A : Type} (a : GrammarE R A) {B : Type} (b : GrammarE R B) (x : A) (y : B)
      (sfx : List Char),
    PredictiveE sb a → PredictiveE sb b →
    (rowTF : ∀ s1 ∈ tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) a,
      ∀ s2 ∈ effFirstE (bodyFirsts sb) b, HeadSpec.disj s1 s2 = true) →
    (rowTM : ∀ p ∈ (tailMunchE (bodyTailMunch sb) a).getD [],
      ∀ s2 ∈ effFirstE (bodyFirsts sb) b, s2.breaks p = true) →
    valueOkWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y') = true →
    tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) b y sfx = true →
    (hbne : printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
      (fun y' _ => printFix m sb dec y') ≠ "") →
    (hvalA : valueOkWalk a x (fun y' _ => Grammar.fixValueOk m sb dec y') = true) →
    (HSJ : ∀ y' (path : SelfPathE a x y'),
      Grammar.fixValueOk m sb dec y' = true →
      tokStar m sb dec y'
        ((printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
            (fun y' _ => printFix m sb dec y')).toList ++ sfx) = true) →
    tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) a x
      ((printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
          (fun y' _ => printFix m sb dec y')).toList ++ sfx) = true := by
  intro A a
  induction a with
  | atomE L =>
      intro B b x y sfx _ _ rowTF rowTM hval hB hbne hvalA HSJ
      have HSB : ∀ (y' : R) (path : SelfPathE b y y'),
          (fun y' _ => Grammar.fixValueOk m sb dec y') y' path = true →
          ((fun y' _ => printFix m sb dec y') y' path ≠ "") ∧
          ∀ cs, ∃ h ∈ bodyFirsts sb,
            h.matches (((fun y' _ => printFix m sb dec y') y' path).toList ++ cs) = true := by
        intro y' path hok
        exact printFixBundle m sb dec hn hf y'
          (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok
      show L.munch.all
        (fun p => ((printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
          (fun y' _ => printFix m sb dec y')).toList ++ sfx).head?.all (fun c => !p c)) = true
      by_cases hep : printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
        (fun y' _ => printFix m sb dec y') = ""
      · exact absurd hep hbne
      · obtain ⟨h2, h2mem, h2m⟩ := (printBundleE b y (fun y' _ => Grammar.fixValueOk m sb dec y')
          (fun y' _ => printFix m sb dec y') (bodyFirsts sb) hval HSB).2 hep sfx
        -- h2m : h2.matches ((printWalk b y …).toList ++ sfx) = true
        cases hLm : L.munch with
        | none => rfl
        | some p =>
            have hrow : h2.breaks p = true := rowTM p (by
              show p ∈ (tailMunchE (bodyTailMunch sb) (.atomE L)).getD []
              show p ∈ L.munch.toList
              rw [hLm]
              exact List.Mem.head []) h2 h2mem
            exact HeadSpec.breaks_sound hrow h2m
  | seqE c d ihc ihd =>
      intro B b x y sfx hpa hpb rowTF rowTM hval hB hbne hvalA HSJ
      obtain ⟨p, q⟩ := x
      obtain ⟨hpc, hpd, _, _⟩ := hpa
      -- the b-print's bundle
      have HSB : ∀ (y' : R) (path : SelfPathE b y y'),
          (fun y' _ => Grammar.fixValueOk m sb dec y') y' path = true →
          ((fun y' _ => printFix m sb dec y') y' path ≠ "") ∧
          ∀ cs, ∃ h ∈ bodyFirsts sb,
            h.matches (((fun y' _ => printFix m sb dec y') y' path).toList ++ cs) = true := by
        intro y' path hok
        exact printFixBundle m sb dec hn hf y'
          (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok
      by_cases hep : printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
        (fun y' _ => printFix m sb dec y') = ""
      · exact absurd hep hbne
      · obtain ⟨h2, h2mem, h2m⟩ := (printBundleE b y (fun y' _ => Grammar.fixValueOk m sb dec y')
          (fun y' _ => printFix m sb dec y') (bodyFirsts sb) hval HSB).2 hep sfx
        have htmSome : (bodyTailMunch sb).isSome = true := bodyTailMunch_isSome sb htf
        -- the rows restricted to (d, b) and (c, b)
        have rowTFd : ∀ s1 ∈ tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) d,
          ∀ s2 ∈ effFirstE (bodyFirsts sb) b, HeadSpec.disj s1 s2 = true :=
          fun s1 h1 => rowTF s1 (tailFirstE_seqR _ _ c d s1 h1)
        have rowTMd : ∀ p' ∈ (tailMunchE (bodyTailMunch sb) d).getD [],
          ∀ s2 ∈ effFirstE (bodyFirsts sb) b, s2.breaks p' = true :=
          fun p' hp' => rowTM p' (tailMunchE_seqR _ c d htmSome p' hp')
        have hvalD : valueOkWalk d q (fun y' _ => Grammar.fixValueOk m sb dec y') = true := by
          have h3 := hvalA
          rw [valueOkWalk_seqE] at h3
          exact (Bool.and_eq_true _ _).mp h3 |>.2
        rw [GrammarE.tailOkE_seqE]
        rw [ihd b q y sfx hpd hpb rowTFd rowTMd hval hB hbne hvalD
          (fun y' path hok => HSJ y' (.seqR path) hok)]
        cases hnd : nullableE d with
        | false => rfl
        | true =>
            have rowTFc : ∀ s1 ∈ tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) c,
              ∀ s2 ∈ effFirstE (bodyFirsts sb) b, HeadSpec.disj s1 s2 = true :=
              fun s1 h1 => rowTF s1 (tailFirstE_seqL _ _ c d hnd s1 h1)
            have rowTMc : ∀ p' ∈ (tailMunchE (bodyTailMunch sb) c).getD [],
              ∀ s2 ∈ effFirstE (bodyFirsts sb) b, s2.breaks p' = true :=
              fun p' hp' => rowTM p' (tailMunchE_seqL _ c d htmSome hnd p' hp')
            have hvalC : valueOkWalk c p (fun y' _ => Grammar.fixValueOk m sb dec y') = true := by
              have h3 := hvalA
              rw [valueOkWalk_seqE] at h3
              exact (Bool.and_eq_true _ _).mp h3 |>.1
            exact ihc b p y sfx hpc hpb rowTFc rowTMc hval hB hbne hvalC
              (fun y' path hok => HSJ y' (.seqL path) hok)
  | altE c d ihc ihd =>
      intro B b x y sfx hpa hpb rowTF rowTM hval hB hbne hvalA HSJ
      obtain ⟨hpc, hpd, _, hnal⟩ := hpa
      -- the b-print's bundle
      have HSB : ∀ (y' : R) (path : SelfPathE b y y'),
          (fun y' _ => Grammar.fixValueOk m sb dec y') y' path = true →
          ((fun y' _ => printFix m sb dec y') y' path ≠ "") ∧
          ∀ cs, ∃ h ∈ bodyFirsts sb,
            h.matches (((fun y' _ => printFix m sb dec y') y' path).toList ++ cs) = true := by
        intro y' path hok
        exact printFixBundle m sb dec hn hf y'
          (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok
      by_cases hep : printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
        (fun y' _ => printFix m sb dec y') = ""
      · exact absurd hep hbne
      · obtain ⟨h2, h2mem, h2m⟩ := (printBundleE b y (fun y' _ => Grammar.fixValueOk m sb dec y')
          (fun y' _ => printFix m sb dec y') (bodyFirsts sb) hval HSB).2 hep sfx
        have htmSome : (bodyTailMunch sb).isSome = true := bodyTailMunch_isSome sb htf
        -- the alt's OR: the branch discriminator agrees with the split
        have hOr : (valueOkWalk c x (fun y' _ => Grammar.fixValueOk m sb dec y') ||
            valueOkWalk d x (fun y' _ => Grammar.fixValueOk m sb dec y')) = true := by
          have h3 := hvalA
          rw [valueOkWalk_altE] at h3
          exact h3
        have rowTFc : ∀ s1 ∈ tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) c,
          ∀ s2 ∈ effFirstE (bodyFirsts sb) b, HeadSpec.disj s1 s2 = true :=
          fun s1 h1 => rowTF s1 (tailFirstE_altL _ _ c d s1 h1)
        have rowTMc : ∀ p' ∈ (tailMunchE (bodyTailMunch sb) c).getD [],
          ∀ s2 ∈ effFirstE (bodyFirsts sb) b, s2.breaks p' = true :=
          fun p' hp' => rowTM p' (tailMunchE_altL _ c d htmSome p' hp')
        have rowTFd : ∀ s1 ∈ tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) d,
          ∀ s2 ∈ effFirstE (bodyFirsts sb) b, HeadSpec.disj s1 s2 = true :=
          fun s1 h1 => rowTF s1 (tailFirstE_altR _ _ c d s1 h1)
        have rowTMd : ∀ p' ∈ (tailMunchE (bodyTailMunch sb) d).getD [],
          ∀ s2 ∈ effFirstE (bodyFirsts sb) b, s2.breaks p' = true :=
          fun p' hp' => rowTM p' (tailMunchE_altR _ c d htmSome p' hp')
        rw [GrammarE.tailOkE_altE]
        cases hcond : valueOkWalk c x (fun y' _ => Grammar.fixValueOk m sb dec y') with
        | true =>
            -- printed LEFT: the IH on c
            exact ihc b x y sfx hpc hpb rowTFc rowTMc hval hB hbne hcond
              (fun y' path hok => HSJ y' (.altL path) hok)
        | false =>
            -- printed RIGHT: the IH on d + the alt-third exclusion for c
            have hcondD : valueOkWalk d x (fun y' _ => Grammar.fixValueOk m sb dec y') = true := by
              cases h4 : valueOkWalk d x (fun y' _ => Grammar.fixValueOk m sb dec y') with
              | true => rfl
              | false => simp [hcond, h4] at hOr
            rw [ihd b x y sfx hpd hpb rowTFd rowTMd hval hB hbne hcondD
              (fun y' path hok => HSJ y' (.altR path) hok)]
            cases hnd : nullableE d with
            | false => rfl
            | true =>
                -- the sub-conjunct: c's effective firsts all fail pfx
                have hall : ∀ s1 ∈ effFirstE (bodyFirsts sb) c,
                  s1.matches ((printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
                    (fun y' _ => printFix m sb dec y')).toList ++ sfx) = false := by
                  intro s1 h1
                  have hd1 := rowTF s1
                    (tailFirstE_alt_third (bodyFirsts sb) (bodyTailFirsts sb) c d hnd s1 h1)
                    h2 h2mem
                  have h2d : h2.disj s1 = true := by rw [HeadSpec.disj_symm]; exact hd1
                  exact HeadSpec.disj_sound h2d _ h2m
                exact List.all_eq_true.mpr (fun x hx => by simp [hall x hx])
  | repE c ihc =>
      intro B b xs y sfx hpa hpb rowTF rowTM hval hB hbne hvalA HSJ
      obtain ⟨hpc, hnc, _, _⟩ := hpa
      have HSB : ∀ (y' : R) (path : SelfPathE b y y'),
          (fun y' _ => Grammar.fixValueOk m sb dec y') y' path = true →
          ((fun y' _ => printFix m sb dec y') y' path ≠ "") ∧
          ∀ cs, ∃ h ∈ bodyFirsts sb,
            h.matches (((fun y' _ => printFix m sb dec y') y' path).toList ++ cs) = true := by
        intro y' path hok
        exact printFixBundle m sb dec hn hf y'
          (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok
      by_cases hep : printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
        (fun y' _ => printFix m sb dec y') = ""
      · exact absurd hep hbne
      · obtain ⟨h2, h2mem, h2m⟩ := (printBundleE b y (fun y' _ => Grammar.fixValueOk m sb dec y')
          (fun y' _ => printFix m sb dec y') (bodyFirsts sb) hval HSB).2 hep sfx
        have hall : ∀ s1 ∈ effFirstE (bodyFirsts sb) c,
          s1.matches ((printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
            (fun y' _ => printFix m sb dec y')).toList ++ sfx) = false := by
          intro s1 h1
          have hd1 := rowTF s1 (tailFirstE_rep_eff _ _ c s1 h1) h2 h2mem
          have h2d : h2.disj s1 = true := by rw [HeadSpec.disj_symm]; exact hd1
          exact HeadSpec.disj_sound h2d _ h2m
        -- the per-element premises (the WF-REP-2 rows at (c, c))
        have rowTFc : ∀ s1 ∈ tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) c,
          ∀ s2 ∈ effFirstE (bodyFirsts sb) b, HeadSpec.disj s1 s2 = true :=
          fun s1 h1 => rowTF s1 (tailFirstE_rep _ _ c s1 h1)
        have rowTMc : ∀ p' ∈ (tailMunchE (bodyTailMunch sb) c).getD [],
          ∀ s2 ∈ effFirstE (bodyFirsts sb) b, s2.breaks p' = true :=
          fun p' hp' => rowTM p' hp'
        have hvalC : ∀ z (hz : z ∈ xs),
            valueOkWalk c z (fun y' _ => Grammar.fixValueOk m sb dec y') = true := by
          have h3 := hvalA
          rw [valueOkWalk_repE] at h3
          exact allWalk_true xs _ h3
        rw [GrammarE.tailOkE_repE, Bool.and_eq_true]
        refine ⟨List.all_eq_true.mpr (fun x hx => by simp [hall x hx]), ?_⟩
        exact List.all_eq_true.mpr (fun z hz =>
          ihc b z y sfx hpc hpb rowTFc rowTMc hval hB hbne (hvalC z hz)
            (fun y' path hok => HSJ y' (.repP hz path) hok))
  | optE c ihc =>
      intro B b x y sfx hpa hpb rowTF rowTM hval hB hbne hvalA HSJ
      obtain ⟨hpc, hnc⟩ := hpa
      have HSB : ∀ (y' : R) (path : SelfPathE b y y'),
          (fun y' _ => Grammar.fixValueOk m sb dec y') y' path = true →
          ((fun y' _ => printFix m sb dec y') y' path ≠ "") ∧
          ∀ cs, ∃ h ∈ bodyFirsts sb,
            h.matches (((fun y' _ => printFix m sb dec y') y' path).toList ++ cs) = true := by
        intro y' path hok
        exact printFixBundle m sb dec hn hf y'
          (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok
      by_cases hep : printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
        (fun y' _ => printFix m sb dec y') = ""
      · exact absurd hep hbne
      · obtain ⟨h2, h2mem, h2m⟩ := (printBundleE b y (fun y' _ => Grammar.fixValueOk m sb dec y')
          (fun y' _ => printFix m sb dec y') (bodyFirsts sb) hval HSB).2 hep sfx
        cases x with
        | none =>
            -- the stop conjunct: c's effective firsts all fail pfx
            have hall : ∀ s1 ∈ effFirstE (bodyFirsts sb) c,
              s1.matches ((printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
                (fun y' _ => printFix m sb dec y')).toList ++ sfx) = false := by
              intro s1 h1
              have hd1 := rowTF s1 (tailFirstE_opt_eff _ _ c s1 h1) h2 h2mem
              have h2d : h2.disj s1 = true := by rw [HeadSpec.disj_symm]; exact hd1
              exact HeadSpec.disj_sound h2d _ h2m
            rw [GrammarE.tailOkE_optE_none]
            exact List.all_eq_true.mpr (fun x hx => by simp [hall x hx])
        | some z =>
            have rowTFc : ∀ s1 ∈ tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) c,
              ∀ s2 ∈ effFirstE (bodyFirsts sb) b, HeadSpec.disj s1 s2 = true :=
              fun s1 h1 => rowTF s1 (tailFirstE_opt _ _ c s1 h1)
            have rowTMc : ∀ p' ∈ (tailMunchE (bodyTailMunch sb) c).getD [],
              ∀ s2 ∈ effFirstE (bodyFirsts sb) b, s2.breaks p' = true :=
              fun p' hp' => rowTM p' hp'
            have hvalC : valueOkWalk c z (fun y' _ => Grammar.fixValueOk m sb dec y') = true := by
              have h3 := hvalA
              rw [valueOkWalk_optE_some] at h3
              exact h3
            rw [GrammarE.tailOkE_optE_some]
            exact ihc b z y sfx hpc hpb rowTFc rowTMc hval hB hbne hvalC
              (fun y' path hok => HSJ y' (.optP path) hok)
  | labelE n c ihc =>
      intro B b x y sfx hpa hpb rowTF rowTM hval hB hbne hvalA HSJ
      have hpc : PredictiveE sb c := hpa
      show tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) c x
        ((printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
            (fun y' _ => printFix m sb dec y')).toList ++ sfx) = true
      exact ihc b x y sfx hpc hpb rowTF rowTM hval hB hbne hvalA
        (fun y' path hok => HSJ y' (.labelP path) hok)
  | relE mm owns don ex nm vld sub ihc =>
      intro B b x y sfx hpa hpb rowTF rowTM hval hB hbne hvalA HSJ
      have hpc : PredictiveE sb sub := hpa
      have hvalS : valueOkWalk sub (mm.encode x) (fun y' _ => Grammar.fixValueOk m sb dec y') = true := by
        have h3 := hvalA
        rw [valueOkWalk_relE] at h3
        exact (Bool.and_eq_true _ _).mp h3 |>.2
      show tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) sub (mm.encode x)
        ((printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
            (fun y' _ => printFix m sb dec y')).toList ++ sfx) = true
      exact ihc b (mm.encode x) y sfx hpc hpb rowTF rowTM hval hB hbne hvalS
        (fun y' path hok => HSJ y' (.relP path) hok)
  | selfE =>
      intro B b x y sfx _ _ rowTF rowTM hval hB hbne hvalA HSJ
      exact HSJ x (.selfP x) hvalA

open Grammar in
/-! ## §6.3's closed membership helpers (junctionG's row-restriction surface) -/

theorem Grammar.tailMunch_isSome : ∀ {A : Type} (g : Grammar A), Predictive g →
    (tailMunch g).isSome = true := by
  intro A g
  induction g with
  | atom L => intro _; rfl
  | seq a b iha ihb =>
      intro hp
      obtain ⟨hpa, hpb, _, _⟩ := hp
      have ha := iha hpa
      have hb := ihb hpb
      show (match tailMunch b with
        | Option.none => Option.none
        | Option.some hb => if nullable b then match tailMunch a with
            | Option.none => Option.none
            | Option.some ha => Option.some (ha ++ hb)
          else Option.some hb).isSome = true
      cases hdd : tailMunch b with
      | none => rw [hdd] at hb; simp at hb
      | some hb' =>
          cases hna : nullable b with
          | false => rfl
          | true =>
              have ha' := ha
              cases hcc : tailMunch a with
              | none => rw [hcc] at ha; simp at ha
              | some hac => simp
  | alt a b iha ihb =>
      intro hp
      obtain ⟨hpa, hpb, _, _⟩ := hp
      have ha := iha hpa
      have hb := ihb hpb
      show (match tailMunch a, tailMunch b with
        | Option.some ha, Option.some hb => Option.some (ha ++ hb)
        | _, _ => Option.none).isSome = true
      cases hma : tailMunch a with
      | none => rw [hma] at ha; simp at ha
      | some ma =>
          cases hmb : tailMunch b with
          | none => rw [hmb] at hb; simp at hb
          | some mb => simp
  | rep a iha => intro hp; obtain ⟨hpa, _, _, _⟩ := hp; show (tailMunch a).isSome = true; exact iha hpa
  | opt a iha => intro hp; obtain ⟨hpa, _⟩ := hp; show (tailMunch a).isSome = true; exact iha hpa
  | label n a iha => intro hp; show (tailMunch a).isSome = true; exact iha hp
  | rel m owns don ex nm vld sub ih => intro hp; show (tailMunch sub).isSome = true; exact ih hp
  | fix m body dec =>
      intro hp
      obtain ⟨_, _, _, htf⟩ := hp
      have h1 := GrammarE.tailSelfFreeE_munch_isSome body htf
      show (GrammarE.tailMunchE (GrammarE.tailMunchE Option.none body) body).isSome = true
      cases h1v : GrammarE.tailMunchE Option.none body with
      | none => rw [h1v] at h1; simp at h1
      | some v =>
          exact GrammarE.tailMunchE_isSome _ body (by simp)

theorem Grammar.tailFirst_seqR {A B : Type} (a : Grammar A) (b : Grammar B) :
    ∀ s ∈ tailFirst b, s ∈ tailFirst (.seq a b) := by
  intro s hs
  show s ∈ tailFirst b ++ (if nullable b then tailFirst a else [])
  exact List.mem_append_left _ hs

theorem Grammar.tailFirst_seqL {A B : Type} (a : Grammar A) (b : Grammar B)
    (hb : nullable b = true) :
    ∀ s ∈ tailFirst a, s ∈ tailFirst (.seq a b) := by
  intro s hs
  show s ∈ tailFirst b ++ (if nullable b then tailFirst a else [])
  rw [if_pos hb]
  exact List.mem_append_right _ hs

theorem Grammar.tailFirst_altL {A : Type} (a b : Grammar A) :
    ∀ s ∈ tailFirst a, s ∈ tailFirst (.alt a b) := by
  intro s hs
  show s ∈ tailFirst a ++ tailFirst b ++ (if nullable b then effFirst a else [])
  exact List.mem_append_left _ (List.mem_append_left _ hs)

theorem Grammar.tailFirst_altR {A : Type} (a b : Grammar A) :
    ∀ s ∈ tailFirst b, s ∈ tailFirst (.alt a b) := by
  intro s hs
  show s ∈ tailFirst a ++ tailFirst b ++ (if nullable b then effFirst a else [])
  exact List.mem_append_left _ (List.mem_append_right _ hs)

theorem Grammar.tailFirst_alt_third {A : Type} (a b : Grammar A) (hb : nullable b = true) :
    ∀ s ∈ effFirst a, s ∈ tailFirst (.alt a b) := by
  intro s hs
  show s ∈ tailFirst a ++ tailFirst b ++ (if nullable b then effFirst a else [])
  rw [if_pos hb]
  exact List.mem_append_right (tailFirst a ++ tailFirst b) hs

theorem Grammar.tailFirst_rep {A : Type} (a : Grammar A) :
    ∀ s ∈ tailFirst a, s ∈ tailFirst (.rep a) := by
  intro s hs
  show s ∈ effFirst a ++ tailFirst a
  exact List.mem_append_right _ hs

theorem Grammar.tailFirst_opt {A : Type} (a : Grammar A) :
    ∀ s ∈ tailFirst a, s ∈ tailFirst (.opt a) := by
  intro s hs
  show s ∈ effFirst a ++ tailFirst a
  exact List.mem_append_right _ hs

theorem Grammar.tailFirst_rep_eff {A : Type} (a : Grammar A) :
    ∀ s ∈ effFirst a, s ∈ tailFirst (.rep a) := by
  intro s hs
  show s ∈ effFirst a ++ tailFirst a
  exact List.mem_append_left _ hs

theorem Grammar.tailFirst_opt_eff {A : Type} (a : Grammar A) :
    ∀ s ∈ effFirst a, s ∈ tailFirst (.opt a) := by
  intro s hs
  show s ∈ effFirst a ++ tailFirst a
  exact List.mem_append_left _ hs
theorem Grammar.tailMunch_seqR {A B : Type} (a : Grammar A) (b : Grammar B)
    (ha : (tailMunch a).isSome = true) (hb : (tailMunch b).isSome = true) :
    ∀ p ∈ (tailMunch b).getD [], p ∈ (tailMunch (.seq a b)).getD [] := by
  intro p hp
  cases hdd : tailMunch b with
  | none => rw [hdd] at hb; simp at hb
  | some hb' =>
      rw [hdd] at hp
      cases hna : nullable b with
      | false =>
          have hval : tailMunch (.seq a b) = Option.some hb' := by
            simp [tailMunch, hdd, hna]
          rw [hval]
          simpa using hp
      | true =>
          cases hcc : tailMunch a with
          | none => rw [hcc] at ha; simp at ha
          | some hac =>
              have hval : tailMunch (.seq a b) = Option.some (hac ++ hb') := by
                simp [tailMunch, hdd, hna, hcc]
              rw [hval]
              simpa using List.mem_append_right _ hp

theorem Grammar.tailMunch_seqL {A B : Type} (a : Grammar A) (b : Grammar B)
    (ha : (tailMunch a).isSome = true) (hb : (tailMunch b).isSome = true)
    (hnb : nullable b = true) :
    ∀ p ∈ (tailMunch a).getD [], p ∈ (tailMunch (.seq a b)).getD [] := by
  intro p hp
  cases hdd : tailMunch b with
  | none => rw [hdd] at hb; simp at hb
  | some hb' =>
      cases hcc : tailMunch a with
      | none => rw [hcc] at ha; simp at ha
      | some hac =>
          have hval : tailMunch (.seq a b) = Option.some (hac ++ hb') := by
            simp [tailMunch, hdd, hnb, hcc]
          rw [hval]
          rw [hcc] at hp
          simpa using List.mem_append_left _ hp

theorem Grammar.tailMunch_altL {A : Type} (a b : Grammar A)
    (ha : (tailMunch a).isSome = true) (hb : (tailMunch b).isSome = true) :
    ∀ p ∈ (tailMunch a).getD [], p ∈ (tailMunch (.alt a b)).getD [] := by
  intro p hp
  cases hma : tailMunch a with
  | none => rw [hma] at ha; simp at ha
  | some ma =>
      cases hmb : tailMunch b with
      | none => rw [hmb] at hb; simp at hb
      | some mb =>
          have hval : tailMunch (.alt a b) = Option.some (ma ++ mb) := by
            simp [tailMunch, hma, hmb]
          rw [hval]
          rw [hma] at hp
          simpa using List.mem_append_left _ hp

theorem Grammar.tailMunch_altR {A : Type} (a b : Grammar A)
    (ha : (tailMunch a).isSome = true) (hb : (tailMunch b).isSome = true) :
    ∀ p ∈ (tailMunch b).getD [], p ∈ (tailMunch (.alt a b)).getD [] := by
  intro p hp
  cases hma : tailMunch a with
  | none => rw [hma] at ha; simp at ha
  | some ma =>
      cases hmb : tailMunch b with
      | none => rw [hmb] at hb; simp at hb
      | some mb =>
          have hval : tailMunch (.alt a b) = Option.some (ma ++ mb) := by
            simp [tailMunch, hma, hmb]
          rw [hval]
          rw [hmb] at hp
          simpa using List.mem_append_right _ hp
open GrammarE in
/-- The fix-level junction instance (v2 §6.3): `junctionE` at `a := sb`,
    the HSJ discharged by `AccD` recursion over the carried measure —
    each `selfE` leaf's value is measure-smaller (`dec`), so its own
    body-junction is the IH. EXACTLY `printFixBundle`'s shape, one more
    AccD instance. -/
theorem Grammar.junctionEG {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x)
    (hpred : GrammarE.PredictiveE sb sb) (hn : sb.nullableE = false)
    (hf : sb.firstE ≠ none) (htf : sb.tailSelfFreeE = true) :
    ∀ (x : R), Grammar.fixValueOk m sb dec x = true →
    ∀ {B : Type} (b : GrammarE R B) (y : B) (sfx : List Char),
    GrammarE.PredictiveE sb b →
    (rowTF : ∀ s1 ∈ GrammarE.tailFirstE (GrammarE.bodyFirsts sb) (GrammarE.bodyTailFirsts sb) sb,
      ∀ s2 ∈ GrammarE.effFirstE (GrammarE.bodyFirsts sb) b, HeadSpec.disj s1 s2 = true) →
    (rowTM : ∀ p ∈ (GrammarE.tailMunchE (GrammarE.bodyTailMunch sb) sb).getD [],
      ∀ s2 ∈ GrammarE.effFirstE (GrammarE.bodyFirsts sb) b, s2.breaks p = true) →
    GrammarE.valueOkWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y') = true →
    GrammarE.tailOkE m sb dec (GrammarE.bodyFirsts sb) (GrammarE.tokStar m sb dec) b y sfx = true →
    (hbne : GrammarE.printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
      (fun y' _ => Grammar.printFix m sb dec y') ≠ "") →
    GrammarE.tailOkE m sb dec (GrammarE.bodyFirsts sb) (GrammarE.tokStar m sb dec) sb x
      ((GrammarE.printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
          (fun y' _ => Grammar.printFix m sb dec y')).toList ++ sfx) = true := by
  intro x hok
  have acc : AccD m x := AccD.ofFuel m x (m x + 1) (Nat.lt_succ_self _)
  induction acc with
  | intro x h ih =>
      intro B b y sfx hpb rowTF rowTM hval hB hbne
      have hvalA : GrammarE.valueOkWalk sb x (fun y' _ => Grammar.fixValueOk m sb dec y') = true := by
        rw [← Grammar.fixValueOk_unfold]; exact hok
      exact junctionE m sb dec hn hf htf sb b x y sfx hpred hpb rowTF rowTM hval hB hbne hvalA
        (fun y' path hok' => by
          have hi := ih y' (dec x y' path) hok' b y sfx hpb rowTF rowTM hval hB hbne
          rw [GrammarE.tailOkE_tok_irrel m sb dec (GrammarE.bodyFirsts sb) sb htf
            (GrammarE.tokStar m sb dec) (fun _ _ => false) y'
              ((GrammarE.printWalk b y (fun y' _ => Grammar.fixValueOk m sb dec y')
                (fun y' _ => Grammar.printFix m sb dec y')).toList ++ sfx)] at hi
          exact hi)

/-- THE discharge kit for law 2's coherence premise (design v2 §5):
    two `rel`-branches whose owns-predicates are disjoint are coherent —
    the formats discharge the semantic premise by the AST's
    no-confusion (`owns x = true → owns₂ x = false` at the ctor
    discriminators) and the valueOk-rel equation does the rest. -/
theorem Grammar.altCoherent_alt_rel_rel {R₁ R₂ A : Type}
    (m₁ : Kit.Codec R₁ A) (owns₁ : A → Bool)
    (don₁ : ∀ raw r, m₁.decode raw = Option.some r → owns₁ r = true)
    (ex₁ : ∀ raw r, m₁.decode raw = Option.some r → m₁.encode r = raw)
    (nm₁ : String) (v₁ : List String) (sub₁ : Grammar R₁)
    (m₂ : Kit.Codec R₂ A) (owns₂ : A → Bool)
    (don₂ : ∀ raw r, m₂.decode raw = Option.some r → owns₂ r = true)
    (ex₂ : ∀ raw r, m₂.decode raw = Option.some r → m₂.encode r = raw)
    (nm₂ : String) (v₂ : List String) (sub₂ : Grammar R₂)
    (h : ∀ x, owns₁ x = true → owns₂ x = false)
    (h₁ : Grammar.altCoherent (.rel m₁ owns₁ don₁ ex₁ nm₁ v₁ sub₁))
    (h₂ : Grammar.altCoherent (.rel m₂ owns₂ don₂ ex₂ nm₂ v₂ sub₂)) :
    Grammar.altCoherent (.alt (.rel m₁ owns₁ don₁ ex₁ nm₁ v₁ sub₁)
      (.rel m₂ owns₂ don₂ ex₂ nm₂ v₂ sub₂)) := by
  refine ⟨?_, h₁, h₂⟩
  intro x hx
  rw [valueOk_rel] at hx
  have h1 : owns₁ x = true := (Bool.and_eq_true _ _).mp hx |>.1
  rw [valueOk_rel]
  simp [h x h1]

/-! ## §6.4: law 1 (parse-print), open level — the premise discipline -/

/-- The law-1 row context: at every `seqE a b`, the `(sb, b)` pair
    (`tailFirstE sb` vs `effFirstE b` disjointness + the munch row);
    at every `repE a`, the `(sb, a)` pair (the per-element stacking's
    `junctionEG` rows); recursively closed (the sub-calls' own
    `rowCtx` rides the IH). Value-free — a Prop fold over the grammar. -/
def GrammarE.rowCtx {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x) :
    {A : Type} → GrammarE R A → Prop :=
  fun {_} g => match g with
  | .atomE _ => True
  | .seqE a b => rowCtx m sb dec a ∧ rowCtx m sb dec b ∧
      (∀ s1 ∈ GrammarE.tailFirstE (GrammarE.bodyFirsts sb)
          (GrammarE.bodyTailFirsts sb) sb,
        ∀ s2 ∈ GrammarE.effFirstE (GrammarE.bodyFirsts sb) b,
          HeadSpec.disj s1 s2 = true) ∧
      (∀ p ∈ (GrammarE.tailMunchE (GrammarE.bodyTailMunch sb) sb).getD [],
        ∀ s2 ∈ GrammarE.effFirstE (GrammarE.bodyFirsts sb) b, s2.breaks p = true)
  | .altE a b => rowCtx m sb dec a ∧ rowCtx m sb dec b
  | .repE a => rowCtx m sb dec a ∧
      (∀ s1 ∈ GrammarE.tailFirstE (GrammarE.bodyFirsts sb)
          (GrammarE.bodyTailFirsts sb) sb,
        ∀ s2 ∈ GrammarE.effFirstE (GrammarE.bodyFirsts sb) a,
          HeadSpec.disj s1 s2 = true) ∧
      (∀ p ∈ (GrammarE.tailMunchE (GrammarE.bodyTailMunch sb) sb).getD [],
        ∀ s2 ∈ GrammarE.effFirstE (GrammarE.bodyFirsts sb) a, s2.breaks p = true)
  | .optE a => rowCtx m sb dec a
  | .labelE _ a => rowCtx m sb dec a
  | .relE _ _ _ _ _ _ sub => rowCtx m sb dec sub
  | .selfE => True

/-- The guard-slack propagation helper (§6.5's slack table's face). -/
theorem GrammarE.guardSlack_mono {R A₁ A₂ : Type} (g₁ : GrammarE R A₁)
    (g₂ : GrammarE R A₂) (h : guardE g₂ = true → guardE g₁ = true) :
    guardSlack g₁ ≤ guardSlack g₂ := by
  unfold guardSlack
  cases h1 : guardE g₁ with
  | true => cases h2 : guardE g₂ <;> simp
  | false =>
      cases h2 : guardE g₂ with
      | false => simp
      | true =>
          have h3 := h h2
          rw [h1] at h3
          simp at h3

/-- The seq node's left slack (the guard fold's `&&` left face). -/
theorem GrammarE.guardSlack_seqL {R : Type} {A B : Type} (a : GrammarE R A)
    (b : GrammarE R B) : guardSlack a ≤ guardSlack (GrammarE.seqE a b) :=
  guardSlack_mono a (GrammarE.seqE a b) (fun hb => by
    have h2 : (guardE a && (if nullableE a then guardE b else true)) = true := hb
    exact (Bool.and_eq_true _ _).mp h2 |>.1)

/-- The seq node's right slack under a nullable left (§6.5's table). -/
theorem GrammarE.guardSlack_seqR_nullable {R : Type} {A B : Type} (a : GrammarE R A)
    (b : GrammarE R B) (ha : nullableE a = true) :
    guardSlack b ≤ guardSlack (GrammarE.seqE a b) :=
  guardSlack_mono b (GrammarE.seqE a b) (fun hb => by
    have h2 : (guardE a && (if nullableE a then guardE b else true)) = true := hb
    have h3 := (Bool.and_eq_true _ _).mp h2 |>.2
    rw [ha] at h3
    exact h3)

/-- The alt node's left slack. -/
theorem GrammarE.guardSlack_altL {R : Type} {A : Type} (a b : GrammarE R A) :
    guardSlack a ≤ guardSlack (GrammarE.altE a b) :=
  guardSlack_mono a (GrammarE.altE a b) (fun hb => by
    have h2 : (guardE a && guardE b) = true := hb
    exact (Bool.and_eq_true _ _).mp h2 |>.1)

/-- The alt node's right slack. -/
theorem GrammarE.guardSlack_altR {R : Type} {A : Type} (a b : GrammarE R A) :
    guardSlack b ≤ guardSlack (GrammarE.altE a b) :=
  guardSlack_mono b (GrammarE.altE a b) (fun hb => by
    have h2 : (guardE a && guardE b) = true := hb
    exact (Bool.and_eq_true _ _).mp h2 |>.2)

/-- THE round-trip law, open level (design §6.5's case table; 05 §1's
    point, 15 #2's append form). Under `valueOkWalk`-discipline + the
    guard-aware fuel slack + the tail-adequacy fold + the `rowCtx`
    premise (§6.4's discipline), parsing the print returns the value
    and leaves the suffix. NO coherence premise (the branch agreement
    is one-sided here: the printer's discriminator picks the branch,
    and the parser tries that branch FIRST — the exclusion removes the
    other). The repE case is the §6.4 engine (a local fuel induction
    with the per-element shifted tails stacked by `junctionE a a` +
    `junctionEG`). -/
theorem GrammarE.parse_print_E {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x)
    (hn : sb.nullableE = false) (hf : sb.firstE ≠ none)
    (htf : sb.tailSelfFreeE = true) (hpred : GrammarE.PredictiveE sb sb)
    (hctxSb : GrammarE.rowCtx m sb dec sb) :
    ∀ (fuel : Nat) {A : Type} (g : GrammarE R A) (x : A) (sfx : List Char)
        (cur : Cursor),
      GrammarE.PredictiveE sb g →
      GrammarE.rowCtx m sb dec g →
      GrammarE.valueOkWalk g x (fun y _ => Grammar.fixValueOk m sb dec y) = true →
      GrammarE.tailOkE m sb dec (GrammarE.bodyFirsts sb) (GrammarE.tokStar m sb dec)
        g x sfx = true →
      cur.cs = (GrammarE.printWalk g x (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx →
      ((GrammarE.printWalk g x (fun y _ => Grammar.fixValueOk m sb dec y)
          (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx).length
          + guardSlack g ≤ fuel →
      GrammarE.parseE sb g fuel cur
        = .ok (x, ⟨cur.off + (GrammarE.printWalk g x
              (fun y _ => Grammar.fixValueOk m sb dec y)
              (fun y _ => Grammar.printFix m sb dec y)).length, sfx⟩) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ F IH =>
      intro A g
      induction g with
      | atomE L =>
          intro x sfx cur _ _ hval ht hcs _hfuel
          simp only [GrammarE.printWalk_atomE, GrammarE.valueOkWalk_atomE] at hcs hval ⊢
          simp only [GrammarE.tailOkE_atomE] at ht
          cases cur with
          | mk k cs =>
              have hcs' : cs = (L.print x).toList ++ sfx := hcs
              simp only [GrammarE.parseE, hcs']
              exact L.print_scan k x sfx hval ht
      | seqE a b iha ihb =>
          intro x sfx cur hpa hctx hval ht hcs hfuel
          obtain ⟨p, q⟩ := x
          obtain ⟨hpaA, hpaB, hrowABTF, hrowABTM⟩ := hpa
          obtain ⟨hctxA, hctxB, hctxSbB_TF, hctxSbB_TM⟩ := hctx
          rw [GrammarE.valueOkWalk_seqE] at hval
          obtain ⟨hvalA, hvalB⟩ := (Bool.and_eq_true _ _).mp hval
          rw [GrammarE.tailOkE_seqE] at ht
          obtain ⟨htB, htAcond⟩ := (Bool.and_eq_true _ _).mp ht
          -- the junction for a's shifted tail, by the right print's emptiness
          have htailA : tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) a p
              ((printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx) = true := by
            by_cases hep : printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
              (fun y _ => Grammar.printFix m sb dec y) = ""
            · have hnb : nullableE b = true := by
                cases h : nullableE b with
                | true => rfl
                | false =>
                    exact absurd hep ((GrammarE.printBundleE b q
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y) (bodyFirsts sb) hvalB
                      (fun y' path hok => Grammar.printFixBundle m sb dec hn hf y'
                        (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok)).1 h)
              have hep' : (printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx = sfx := by
                rw [hep]; simp
              rw [hep']
              rw [if_pos hnb] at htAcond
              exact htAcond
            · exact GrammarE.junctionE m sb dec hn hf htf a b p q sfx hpaA hpaB
                hrowABTF hrowABTM hvalB htB hep hvalA
                (fun y' path hok => by
                  have hstar : GrammarE.tokStar m sb dec y'
                      ((printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                        (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx)
                    = tailOkE m sb dec (bodyFirsts sb) (fun _ _ => false) sb y'
                      ((printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                        (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx) := rfl
                  rw [hstar, GrammarE.tailOkE_tok_irrel m sb dec (bodyFirsts sb) sb htf
                    (fun _ _ => false) (tokStar m sb dec) y'
                    ((printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx)]
                  exact Grammar.junctionEG m sb dec hpred hn hf htf y' hok b q sfx hpaB
                    hctxSbB_TF hctxSbB_TM hvalB htB hep)
          -- the fuel decompositions
          rw [GrammarE.printWalk_seqE] at hcs hfuel ⊢
          have hdecomp : ((printWalk a p (fun y _ => Grammar.fixValueOk m sb dec y)
                (fun y _ => Grammar.printFix m sb dec y) ++
              printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx).length
              = (printWalk a p (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y)).toList.length
                + ((printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y)).toList.length + sfx.length) := by
            rw [String.toList_append, List.length_append, List.length_append]
            omega
          have hlenId : ((printWalk a p (fun y _ => Grammar.fixValueOk m sb dec y)
                (fun y _ => Grammar.printFix m sb dec y)).toList ++
              ((printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx)).length
              = (printWalk a p (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y)).toList.length
                + ((printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y)).toList.length + sfx.length) := by
            rw [List.length_append, List.length_append]
          have hgs1 : 1 ≤ guardSlack (GrammarE.seqE a b) := by
            unfold guardSlack; split <;> omega
          have hfuelA : ((printWalk a p (fun y _ => Grammar.fixValueOk m sb dec y)
                (fun y _ => Grammar.printFix m sb dec y)).toList ++
              ((printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx)).length
              + guardSlack a ≤ F := by
            rw [hlenId]
            have hsl := guardSlack_seqL a b
            omega
          have hfuelB : ((printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx).length
              + guardSlack b ≤ F := by
            rw [List.length_append]
            cases hna : nullableE a with
            | true =>
                have hsl := guardSlack_seqR_nullable a b hna
                omega
            | false =>
                have hPA : printWalk a p (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y) ≠ "" :=
                  (GrammarE.printBundleE a p (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y) (bodyFirsts sb) hvalA
                    (fun y' path hok => Grammar.printFixBundle m sb dec hn hf y'
                      (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok)).1 hna
                have hlen : 0 < (printWalk a p (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)).toList.length := by
                  have h2 := String.ne_empty_length hPA
                  rw [← String.length_toList] at h2
                  exact h2
                have h2b : guardSlack b ≤ 2 := by unfold guardSlack; split <;> omega
                have hrel : guardSlack (GrammarE.seqE a b) = guardSlack a := by
                  have h2 : guardE (GrammarE.seqE a b) = guardE a := by
                    show (guardE a && (if nullableE a then guardE b else true))
                      = guardE a
                    rw [hna]; simp
                  unfold guardSlack
                  rw [h2]
                omega
          -- the a-parse (the IH)
          have hcsA : cur.cs = (printWalk a p (fun y _ => Grammar.fixValueOk m sb dec y)
                (fun y _ => Grammar.printFix m sb dec y)).toList ++
              ((printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx) := by
            rw [hcs, String.toList_append, List.append_assoc]
          have h1 := iha p _ cur hpaA hctxA hvalA htailA hcsA hfuelA
          simp only [GrammarE.parseE, h1]
          -- the b-parse (the IH)
          have h2 := ihb q sfx ⟨cur.off + (printWalk a p
              (fun y _ => Grammar.fixValueOk m sb dec y)
              (fun y _ => Grammar.printFix m sb dec y)).length,
            (printWalk b q (fun y _ => Grammar.fixValueOk m sb dec y)
              (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx⟩
            hpaB hctxB hvalB htB rfl hfuelB
          simp only [h2, String.length_append, Nat.add_assoc]
      | altE a b iha ihb =>
          intro x sfx cur hpa hctx hval ht hcs hfuel
          obtain ⟨hpaA, hpaB, hrowALT, hnnA⟩ := hpa
          obtain ⟨hctxA, hctxB⟩ := hctx
          rw [GrammarE.valueOkWalk_altE] at hval
          rw [GrammarE.tailOkE_altE] at ht
          rw [GrammarE.printWalk_altE] at hcs hfuel ⊢
          cases hdisc : valueOkWalk a x (fun y _ => Grammar.fixValueOk m sb dec y) with
          | true =>
              -- printed LEFT: the IH at a
              rw [if_pos hdisc] at ht hfuel hcs
              show parseE sb (GrammarE.altE a b) F cur
                = .ok (x, ⟨cur.off + (printWalk a x
                    (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)).length, sfx⟩)
              have hfuelA : ((printWalk a x (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx).length
                  + guardSlack a ≤ F := by
                have hsl := guardSlack_altL a b
                omega
              have h1 := iha x sfx cur hpaA hctxA hdisc ht hcs hfuelA
              simp only [GrammarE.parseE, h1]
          | false =>
              -- printed RIGHT: a fails, then the IH at b
              rw [if_neg (by simp [hdisc])] at ht hfuel hcs
              show parseE sb (GrammarE.altE a b) F cur
                = .ok (x, ⟨cur.off + (printWalk b x
                    (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)).length, sfx⟩)
              have hvalB : valueOkWalk b x (fun y _ => Grammar.fixValueOk m sb dec y)
                  = true := by
                simp only [hdisc, Bool.false_or] at hval
                exact hval
              obtain ⟨htB, htStop⟩ := (Bool.and_eq_true _ _).mp ht
              -- the exclusion of a
              have hfail : ∀ h ∈ effFirstE (bodyFirsts sb) a,
                  h.matches cur.cs = false := by
                intro h hmem
                by_cases hep : printWalk b x (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y) = ""
                · -- the empty right print: b is nullable; ht's own exclusion conjunct
                  have hnb : nullableE b = true := by
                    cases h : nullableE b with
                    | true => rfl
                    | false =>
                        exact absurd hep ((GrammarE.printBundleE b x
                          (fun y _ => Grammar.fixValueOk m sb dec y)
                          (fun y _ => Grammar.printFix m sb dec y) (bodyFirsts sb) hvalB
                          (fun y' path hok => Grammar.printFixBundle m sb dec hn hf y'
                            (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok)).1 h)
                  rw [if_pos hnb] at htStop
                  have hall := List.all_eq_true.mp htStop
                  have hep' : (printWalk b x (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx = sfx := by
                    rw [hep]; simp
                  rw [hcs, hep']
                  simpa using hall h hmem
                · -- the nonempty right print: WF-ALT-1 + the print bundle's head
                  obtain ⟨h', h'mem, h'm⟩ := (GrammarE.printBundleE b x
                    (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y) (bodyFirsts sb) hvalB
                    (fun y' path hok => Grammar.printFixBundle m sb dec hn hf y'
                      (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok)).2 hep sfx
                  have hd1 := hrowALT h hmem h' h'mem
                  have h2d : h'.disj h = true := by rw [HeadSpec.disj_symm]; exact hd1
                  rw [hcs]
                  exact HeadSpec.disj_sound h2d _ h'm
              obtain ⟨e, he⟩ := parseExcludeE sb hn hf F cur.off cur.cs hnnA hfail
              have he' : parseE sb a F cur = .error e := he
              have hfuelB : ((printWalk b x (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx).length
                  + guardSlack b ≤ F := by
                have hsl := guardSlack_altR a b
                omega
              have h2 := ihb x sfx cur hpaB hctxB hvalB htB hcs hfuelB
              simp only [GrammarE.parseE, he', h2]
      | repE a iha =>
          intro xs sfx cur hpa hctx hval ht hcs hfuel
          obtain ⟨hpaA, hnnA, hrowTMaa, hrowTFaa⟩ := hpa
          obtain ⟨hctxA, hctxSbA_TF, hctxSbA_TM⟩ := hctx
          rw [GrammarE.printWalk_repE] at hcs hfuel ⊢
          rw [GrammarE.tailOkE_repE] at ht
          obtain ⟨hstop, hbase⟩ := (Bool.and_eq_true _ _).mp ht
          -- the canonical element printer (the handlers discard the proofs)
          have hPcongr : printList xs
              (fun z hz => printWalk a z
                (fun y path => (fun y _ => Grammar.fixValueOk m sb dec y) y
                  (SelfPathE.repP hz path))
                (fun y path => (fun y _ => Grammar.printFix m sb dec y) y
                  (SelfPathE.repP hz path)))
            = printList xs (fun z _ => printWalk a z
                (fun y _ => Grammar.fixValueOk m sb dec y)
                (fun y _ => Grammar.printFix m sb dec y)) :=
            printList_congr xs _ _ (fun z hz => rfl)
          rw [hPcongr] at hcs hfuel ⊢
          have hbase' : ∀ w (_ : w ∈ xs),
              tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) a w sfx = true :=
            fun w hw => List.all_eq_true.mp hbase w hw
          have hval' : ∀ w (_ : w ∈ xs),
              valueOkWalk a w (fun y _ => Grammar.fixValueOk m sb dec y) = true := by
            intro w hw
            have h3 := hval
            rw [GrammarE.valueOkWalk_repE] at h3
            exact GrammarE.allWalk_true xs _ h3 w hw
          -- the stacking lemma: shift a's tail by the print of a whole list
          have shiftBy : ∀ (ws) (sfx' : List Char),
              (∀ w, w ∈ ws → valueOkWalk a w
                (fun y _ => Grammar.fixValueOk m sb dec y) = true) →
              (∀ w, w ∈ ws → tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec)
                a w sfx' = true) →
              ∀ (z),
              valueOkWalk a z (fun y _ => Grammar.fixValueOk m sb dec y) = true →
              tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) a z sfx' = true →
              tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) a z
                ((printList ws (fun z _ => printWalk a z
                    (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx') = true := by
            intro ws
            induction ws with
            | nil =>
                intro sfx' _ _ z _ hz
                simp only [GrammarE.printList_nil]
                exact hz
            | cons w ws ih =>
                intro sfx' hvalW hbaseW z hvalZ hzTail
                -- step 1: the IH at w (shift by ws's print)
                have hw1 := ih sfx' (fun v hv => hvalW v (List.Mem.tail w hv))
                  (fun v hv => hbaseW v (List.Mem.tail w hv)) w
                  (hvalW w (List.Mem.head ws))
                  (hbaseW w (List.Mem.head ws))
                -- step 2: junctionE a a at (z, w), suffix shifted by ws's print
                have hbw : printWalk a w (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y) ≠ "" :=
                  (GrammarE.printBundleE a w (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y) (bodyFirsts sb)
                    (hvalW w (List.Mem.head ws))
                    (fun y' path hok => Grammar.printFixBundle m sb dec hn hf y'
                      (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok)).1 hnnA
                have hstep := GrammarE.junctionE m sb dec hn hf htf a a z w
                  ((printList ws (fun z _ => printWalk a z
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx')
                  hpaA hpaA hrowTFaa hrowTMaa
                  (hvalW w (List.Mem.head ws)) hw1 hbw hvalZ
                  (fun y' path hok => by
                    have hstar : GrammarE.tokStar m sb dec y'
                        ((printWalk a w (fun y _ => Grammar.fixValueOk m sb dec y)
                          (fun y _ => Grammar.printFix m sb dec y)).toList ++
                          ((printList ws (fun z _ => printWalk a z
                              (fun y _ => Grammar.fixValueOk m sb dec y)
                              (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx'))
                      = tailOkE m sb dec (bodyFirsts sb) (fun _ _ => false) sb y'
                        ((printWalk a w (fun y _ => Grammar.fixValueOk m sb dec y)
                          (fun y _ => Grammar.printFix m sb dec y)).toList ++
                          ((printList ws (fun z _ => printWalk a z
                              (fun y _ => Grammar.fixValueOk m sb dec y)
                              (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx')) := rfl
                    rw [hstar, GrammarE.tailOkE_tok_irrel m sb dec (bodyFirsts sb) sb htf
                      (fun _ _ => false) (tokStar m sb dec) y'
                      ((printWalk a w (fun y _ => Grammar.fixValueOk m sb dec y)
                        (fun y _ => Grammar.printFix m sb dec y)).toList ++
                        ((printList ws (fun z _ => printWalk a z
                            (fun y _ => Grammar.fixValueOk m sb dec y)
                            (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx'))]
                    exact Grammar.junctionEG m sb dec hpred hn hf htf y' hok a w
                      ((printList ws (fun z _ => printWalk a z
                          (fun y _ => Grammar.fixValueOk m sb dec y)
                          (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx')
                      hpaA hctxSbA_TF hctxSbA_TM
                      (hvalW w (List.Mem.head ws)) hw1 hbw)
                show tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) a z
                  ((printList (w :: ws) (fun z _ => printWalk a z
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx') = true
                rw [GrammarE.printList_cons, String.toList_append, List.append_assoc]
                exact hstep
          -- the engine (§6.4's local fuel induction)
          have engine : ∀ (f : Nat), f ≤ F → ∀ (ys) (c : Cursor),
              (∀ w, w ∈ ys → valueOkWalk a w
                (fun y _ => Grammar.fixValueOk m sb dec y) = true) →
              (∀ w, w ∈ ys → tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec)
                a w sfx = true) →
              ((effFirstE (bodyFirsts sb) a).all
                (fun h => !h.matches sfx)) = true →
              c.cs.length + guardSlack a ≤ f →
              c.cs = (printList ys (fun z _ => printWalk a z
                  (fun y _ => Grammar.fixValueOk m sb dec y)
                  (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx →
              parseManyE sb a f c
                = .ok (ys, ⟨c.off + (printList ys (fun z _ => printWalk a z
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y))).length, sfx⟩) := by
            intro f hfF
            induction f with
            | zero =>
                intro ys c hvalY hbaseY hstopY hf0 hcsE
                cases ys with
                | nil =>
                    simp only [GrammarE.parseManyE]
                    rw [GrammarE.printList_nil] at hcsE
                    cases c with
                    | mk off cs =>
                        have hcs'' : cs = sfx := hcsE
                        simp [hcs'']
                | cons z zs =>
                    have hPz : printWalk a z (fun y _ => Grammar.fixValueOk m sb dec y)
                        (fun y _ => Grammar.printFix m sb dec y) ≠ "" :=
                      (GrammarE.printBundleE a z (fun y _ => Grammar.fixValueOk m sb dec y)
                        (fun y _ => Grammar.printFix m sb dec y) (bodyFirsts sb)
                        (hvalY z (List.Mem.head zs)) (fun y' path hok =>
                          Grammar.printFixBundle m sb dec hn hf y'
                            (AccD.ofFuel m y' (m y' + 1) (Nat.lt_succ_self _)) hok)).1 hnnA
                    have hlen : 0 < (printWalk a z
                        (fun y _ => Grammar.fixValueOk m sb dec y)
                        (fun y _ => Grammar.printFix m sb dec y)).toList.length := by
                      have h2 := String.ne_empty_length hPz
                      rw [← String.length_toList] at h2
                      exact h2
                    have h1g : 1 ≤ guardSlack a := by unfold guardSlack; split <;> omega
                    rw [hcsE, GrammarE.printList_cons, String.toList_append,
                      List.length_append, List.length_append] at hf0
                    exact absurd hf0 (by omega)
            | succ f ih =>
                intro ys c hvalY hbaseY hstopY hf1 hcsE
                cases ys with
                | nil =>
                    -- the stop: the body FAILS on sfx (heads-fail + WF-REP-1)
                    have hcs' : c.cs = sfx := by
                      rw [hcsE]; simp [GrammarE.printList_nil]
                    have hfail : ∀ h ∈ effFirstE (bodyFirsts sb) a,
                        h.matches c.cs = false := by
                      intro h hmem
                      rw [hcs']
                      simpa using List.all_eq_true.mp hstopY h hmem
                    obtain ⟨e, he⟩ := parseExcludeE sb hn hf (f + 1) c.off c.cs hnnA
                      hfail
                    have he' : parseE sb a (f + 1) c = .error e := he
                    simp only [GrammarE.parseManyE, he']
                    rw [GrammarE.printList_nil]
                    cases c with
                    | mk off cs =>
                        have hcs'' : cs = sfx := hcs'
                        simp [hcs'']
                | cons z zs =>
                    -- the shifted tail for z (the stacking lemma)
                    have hz1 : tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) a z
                        ((printList zs (fun z _ => printWalk a z
                            (fun y _ => Grammar.fixValueOk m sb dec y)
                            (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx)
                          = true := by
                      apply shiftBy zs sfx
                      · intro w hw; exact hvalY w (List.Mem.tail z hw)
                      · intro w hw; exact hbaseY w (List.Mem.tail z hw)
                      · exact hvalY z (List.Mem.head zs)
                      · exact hbaseY z (List.Mem.head zs)
                    -- the element parse (the outer law's IH at fuel f+1)
                    have hcsZ : c.cs = (printWalk a z
                        (fun y _ => Grammar.fixValueOk m sb dec y)
                        (fun y _ => Grammar.printFix m sb dec y)).toList ++
                        ((printList zs (fun z _ => printWalk a z
                            (fun y _ => Grammar.fixValueOk m sb dec y)
                            (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx) := by
                      rw [hcsE, GrammarE.printList_cons, String.toList_append,
                        List.append_assoc]
                    have hlenId : ((printWalk a z
                          (fun y _ => Grammar.fixValueOk m sb dec y)
                          (fun y _ => Grammar.printFix m sb dec y)).toList ++
                        ((printList zs (fun z _ => printWalk a z
                            (fun y _ => Grammar.fixValueOk m sb dec y)
                            (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx)).length
                        = c.cs.length := by rw [hcsZ]
                    have hfork : f + 1 = F ∨ f + 1 < F := by omega
                    have hbody : parseE sb a (f + 1) c = .ok (z, ⟨c.off +
                        (printWalk a z (fun y _ => Grammar.fixValueOk m sb dec y)
                          (fun y _ => Grammar.printFix m sb dec y)).length,
                        ((printList zs (fun z _ => printWalk a z
                            (fun y _ => Grammar.fixValueOk m sb dec y)
                            (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx)⟩) := by
                      rcases hfork with he | hlt
                      · rw [he]
                        have hf' : c.cs.length + guardSlack a ≤ F := by
                          rw [he] at hf1; exact hf1
                        exact iha z _ c hpaA hctxA (hvalY z (List.Mem.head zs)) hz1 hcsZ
                          (by rw [hlenId]; exact hf')
                      · exact IH (f + 1) hlt a z _ c hpaA hctxA
                          (hvalY z (List.Mem.head zs)) hz1 hcsZ
                          (by rw [hlenId]; exact hf1)
                    cases hb : parseE sb a (f + 1) c with
                    | error e => simp only [hb] at hbody; simp at hbody
                    | ok r =>
                        obtain ⟨z₁, c₁⟩ := r
                        simp only [hb] at hbody
                        obtain ⟨hzz, hcc2⟩ := Prod.mk.inj (Except.ok.inj hbody)
                        have hoff : c₁.off = c.off + (printWalk a z
                            (fun y _ => Grammar.fixValueOk m sb dec y)
                            (fun y _ => Grammar.printFix m sb dec y)).length := by
                          rw [hcc2]
                        have hcsR : c₁.cs = (printList zs (fun z _ => printWalk a z
                              (fun y _ => Grammar.fixValueOk m sb dec y)
                              (fun y _ => Grammar.printFix m sb dec y))).toList ++ sfx := by
                          rw [hcc2]
                        -- progress (WF-REP-1's consumption)
                        have hprog : c₁.cs.length < c.cs.length :=
                          parseConsumeE sb hn (f + 1) hb hnnA
                        simp only [GrammarE.parseManyE, hb, if_pos hprog]
                        -- the recursive engine call
                        have hbaseZ : ∀ w (_ : w ∈ zs),
                            tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) a w sfx
                              = true := by
                          intro w hw
                          exact hbaseY w (List.Mem.tail z hw)
                        have hvalZ : ∀ w (_ : w ∈ zs),
                            valueOkWalk a w (fun y _ => Grammar.fixValueOk m sb dec y)
                              = true := by
                          intro w hw
                          exact hvalY w (List.Mem.tail z hw)
                        have hfuelR : c₁.cs.length + guardSlack a ≤ f := by omega
                        have hrec := ih (by omega) zs c₁ hvalZ hbaseZ hstopY hfuelR hcsR
                        simp only [hrec, hzz, GrammarE.printList_cons,
                          String.length_append, hoff, Nat.add_assoc]
          -- the engine call at the case's own data
          have hfuelE : cur.cs.length + guardSlack a ≤ F := by
            have h1g : guardSlack (GrammarE.repE a) = guardSlack a := by
              show (if guardE (GrammarE.repE a) then 1 else 2)
                = (if guardE a then 1 else 2)
              rfl
            rw [h1g, ← hcs] at hfuel
            exact hfuel
          simp only [GrammarE.parseE]
          exact engine F (Nat.le_refl F) xs cur hval' hbase' hstop hfuelE hcs
      | optE a iha =>
          intro x sfx cur hpa hctx hval ht hcs hfuel
          obtain ⟨hpaA, hnnA⟩ := hpa
          cases x with
          | none =>
              rw [GrammarE.printWalk_optE_none] at hcs ⊢
              have hcs' : cur.cs = sfx := by simpa using hcs
              -- the body fails on sfx
              have hfail : ∀ h ∈ effFirstE (bodyFirsts sb) a,
                  h.matches cur.cs = false := by
                intro h hmem
                rw [GrammarE.tailOkE_optE_none] at ht
                rw [hcs']
                simpa using List.all_eq_true.mp ht h hmem
              obtain ⟨e, he⟩ := parseExcludeE sb hn hf F cur.off cur.cs hnnA hfail
              have he' : parseE sb a F cur = .error e := he
              simp only [GrammarE.parseE, he']
              cases cur with
              | mk off cs =>
                  have hcs'' : cs = sfx := hcs'
                  simp [hcs'']
          | some z =>
              rw [GrammarE.printWalk_optE_some] at hcs hfuel ⊢
              rw [GrammarE.tailOkE_optE_some] at ht
              have hfuelA : ((printWalk a z (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx).length
                  + guardSlack a ≤ F := by
                have hsl := guardSlack_mono a (GrammarE.optE a) (fun hb => hb)
                omega
              have h1 := iha z sfx cur hpaA hctx hval ht hcs hfuelA
              simp only [GrammarE.parseE, h1]
      | labelE n a iha =>
          intro x sfx cur hpa hctx hval ht hcs hfuel
          rw [GrammarE.printWalk_labelE] at hcs hfuel ⊢
          have h1 := iha x sfx cur hpa hctx hval ht hcs hfuel
          simp only [GrammarE.parseE, h1]
      | relE mm owns don ex nm vld sub ih =>
          intro x sfx cur hpa hctx hval ht hcs hfuel
          -- the rel node's folds pass through `encode` definitionally
          have hvalS : valueOkWalk sub (mm.encode x)
              (fun y _ => Grammar.fixValueOk m sb dec y) = true :=
            (Bool.and_eq_true _ _).mp hval |>.2
          have h1 := ih (mm.encode x) sfx cur hpa hctx hvalS ht hcs hfuel
          simp only [GrammarE.parseE, h1, Kit.Codec.decode_encode,
            GrammarE.printWalk_relE]
      | selfE =>
          intro x sfx cur _ _ hval ht hcs hfuel
          cases F with
          | zero =>
              have hgsE : guardSlack (GrammarE.selfE : GrammarE R R) = 2 := by
                unfold guardSlack; simp [GrammarE.guardE_selfE]
              rw [hgsE] at hfuel; omega
          | succ f =>
              -- the fuel-IH at g := sb
              have hgsb : guardE sb = true :=
                GrammarE.firstE_some_guardE (R := R) (A := R) sb hf
              have hgsb' : guardSlack sb = 1 := by
                unfold guardSlack; simp [hgsb]
              have hgsE : guardSlack (GrammarE.selfE : GrammarE R R) = 2 := by
                unfold guardSlack; simp [GrammarE.guardE_selfE]
              have hfix : printWalk GrammarE.selfE x
                    (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)
                  = printWalk sb x (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y) := by
                rw [GrammarE.printWalk_selfE, Grammar.printFix_unfold]
              have hval' : valueOkWalk sb x
                  (fun y _ => Grammar.fixValueOk m sb dec y) = true := by
                rw [← Grammar.fixValueOk_unfold]
                exact hval
              have ht' : tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) sb x sfx
                  = true := by
                rw [GrammarE.tailOkE_tok_irrel m sb dec (bodyFirsts sb) sb htf
                  (tokStar m sb dec) (fun _ _ => false) x sfx]
                rw [GrammarE.tailOkE_selfE] at ht
                exact ht
              have hfuel' : ((printWalk sb x (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx).length
                  + guardSlack sb ≤ f := by
                have h2 := hfuel
                rw [hgsE] at h2
                rw [hgsb']
                have h3 := hfix
                have hsp : ((printWalk GrammarE.selfE x
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx).length
                    = (printWalk GrammarE.selfE x
                        (fun y _ => Grammar.fixValueOk m sb dec y)
                        (fun y _ => Grammar.printFix m sb dec y)).toList.length
                      + sfx.length := by rw [List.length_append]
                have hss : ((printWalk sb x
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx).length
                    = (printWalk sb x
                        (fun y _ => Grammar.fixValueOk m sb dec y)
                        (fun y _ => Grammar.printFix m sb dec y)).toList.length
                      + sfx.length := by rw [List.length_append]
                have hfix2 : (printWalk GrammarE.selfE x
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y)).length
                  = (printWalk sb x (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y)).length := by
                  rw [← String.length_toList, ← String.length_toList, hfix]
                have hsp2 : (printWalk GrammarE.selfE x
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y)).length
                  = (printWalk GrammarE.selfE x
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y)).toList.length := by
                  rw [String.length_toList]
                have hss2 : (printWalk sb x
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y)).length
                  = (printWalk sb x
                      (fun y _ => Grammar.fixValueOk m sb dec y)
                      (fun y _ => Grammar.printFix m sb dec y)).toList.length := by
                  rw [String.length_toList]
                omega
              have hcs' : cur.cs = (printWalk sb x
                    (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)).toList ++ sfx := by
                rw [← hfix]
                exact hcs
              have h1 := IH f (Nat.lt_succ_self f) sb x sfx cur hpred hctxSb hval' ht'
                hcs' hfuel'
              have hfixlen : (printWalk GrammarE.selfE x
                    (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)).length
                = (printWalk sb x (fun y _ => Grammar.fixValueOk m sb dec y)
                    (fun y _ => Grammar.printFix m sb dec y)).length := by
                rw [← String.length_toList, ← String.length_toList, hfix]
              simp only [GrammarE.parseE, h1, hfixlen]

/-- THE round-trip law, closed level, the FIX-TOPPED face (the formats'
    shape — the migration targets are all single `fix` values, §8).
    The closed folds' `fix` arms ARE the once-unfolded E-values (the
    bridges `printG_fix`/`valueOk_fix`/the `parseG` fix arm are
    `rfl`-family), so this is `parse_print_E` at the body + the
    `tailOkE_tok_irrel` bridge (`tailSelfFreeE` makes the closed
    `tailOk`'s once-unfolded tok agree with `tokStar`) + the slack
    identity via `firstE_some_guardE`.

    HONEST BOUNDARY: the fully general closed law (law 1 at a `seq` of
    two recursive formats, say) needs the closed junction family with
    the right grammar CLOSED — `junctionEG`'s right-grammar parameter
    is open-typed, and there is no closed→open embedding, so the closed
    junction's fix arm is NOT dischargeable from the landed family.
    The formats' face here covers every RECURSIVE migration target; the
    general closed form is future work (it needs a mixed
    open-left/closed-right junction induction). The FLAT formats (a
    `rep`-top/`seq`-top value with no `fix`/`self` node) have their own
    closed face: §6.7's `parse_print_fixFree` (the E-family's assembly
    with the fix case absent — the closed junction `junctionG_fixFree`,
    the real node pairs, the structural induction). -/
theorem Grammar.parse_print_fix {R : Type} (m : R → Nat) (body : GrammarE R R)
    (dec : ∀ x y, SelfPathE body x y → m y < m x)
    (hp : Predictive (.fix m body dec))
    (hctx : GrammarE.rowCtx m body dec body) :
    ∀ (fuel : Nat) (x : R) (sfx : List Char) (k : Nat),
      valueOk (.fix m body dec) x = true →
      tailOk (.fix m body dec) x sfx = true →
      ((printG (.fix m body dec) x).toList ++ sfx).length
          + guardSlack (.fix m body dec) ≤ fuel →
      parseG (.fix m body dec) fuel ⟨k, (printG (.fix m body dec) x).toList ++ sfx⟩
        = .ok (x, ⟨k + (printG (.fix m body dec) x).length, sfx⟩) := by
  intro fuel x sfx k hval htail hfuel
  obtain ⟨hpred, hfe, hne, hte⟩ := hp
  have hfuel' : ((GrammarE.printWalk body x (fun y _ => Grammar.fixValueOk m body dec y)
        (fun y _ => Grammar.printFix m body dec y)).toList ++ sfx).length
      + GrammarE.guardSlack body ≤ fuel := by
    have hgs : GrammarE.guardSlack body = 1 := by
      have h1 : GrammarE.guardE body = true := GrammarE.firstE_some_guardE body hfe
      unfold GrammarE.guardSlack; rw [h1]; simp
    have hgs' : guardSlack (.fix m body dec) = 1 := by
      have h1 : guard (.fix m body dec) = GrammarE.guardE body := rfl
      have h2 : GrammarE.guardE body = true := GrammarE.firstE_some_guardE body hfe
      unfold guardSlack; rw [h1, h2]; simp
    have hpc : printG (.fix m body dec) x = GrammarE.printWalk body x
        (fun y _ => Grammar.fixValueOk m body dec y)
        (fun y _ => Grammar.printFix m body dec y) := by
      rw [printG_fix, Grammar.printFix_unfold]
    rw [hgs', hpc] at hfuel
    rw [hgs]
    exact hfuel
  have htail' : GrammarE.tailOkE m body dec (GrammarE.bodyFirsts body)
      (GrammarE.tokStar m body dec) body x sfx = true := by
    rw [GrammarE.tailOkE_tok_irrel m body dec (GrammarE.bodyFirsts body) body hte
      (GrammarE.tokStar m body dec)
      (fun y sfx' => GrammarE.tailOkE m body dec (GrammarE.bodyFirsts body)
        (fun _ _ => false) body y sfx') x sfx]
    exact htail
  have hval' : GrammarE.valueOkWalk body x (fun y _ => Grammar.fixValueOk m body dec y)
      = true := by
    rw [← Grammar.fixValueOk_unfold]
    exact hval
  have hcs : (⟨k, (printG (.fix m body dec) x).toList ++ sfx⟩ : Cursor).cs
      = (GrammarE.printWalk body x (fun y _ => Grammar.fixValueOk m body dec y)
          (fun y _ => Grammar.printFix m body dec y)).toList ++ sfx := by
    rw [printG_fix, Grammar.printFix_unfold]
  have hres := GrammarE.parse_print_E m body dec hne hfe hte hpred hctx fuel body x sfx
    ⟨k, (printG (.fix m body dec) x).toList ++ sfx⟩ hpred hctx hval' htail' hcs hfuel'
  rw [← Grammar.printFix_unfold, ← printG_fix] at hres
  simp only [Grammar.parseG]
  exact hres

/-- THE run corollary (design §6.6): the format's `run` accepts the
    print of any value-owned text. `run`'s fuel is `length + 1`, the
    slack is exactly 1 under the certificate, and the empty suffix is
    an adequate tail (`tailOk_nil`). -/
theorem Grammar.run_print {R : Type} (m : R → Nat) (body : GrammarE R R)
    (dec : ∀ x y, SelfPathE body x y → m y < m x)
    (hp : Predictive (.fix m body dec))
    (hctx : GrammarE.rowCtx m body dec body)
    (x : R) (hval : valueOk (.fix m body dec) x = true) :
    run (.fix m body dec) (print (.fix m body dec) x) = .ok x := by
  have htail := tailOk_nil (.fix m body dec) hp x
  have hprint : print (.fix m body dec) x = printG (.fix m body dec) x := rfl
  have hfuel : ((printG (.fix m body dec) x).toList ++ []).length
      + guardSlack (.fix m body dec)
      ≤ (print (.fix m body dec) x).length + 1 := by
    have hgs : guardSlack (.fix m body dec) = 1 := by
      have h1 : guard (.fix m body dec) = GrammarE.guardE body := rfl
      have h2 : GrammarE.guardE body = true := GrammarE.firstE_some_guardE body
        (by obtain ⟨_, hfe, _, _⟩ := hp; exact hfe)
      unfold guardSlack; rw [h1, h2]; simp
    have hlen : (print (.fix m body dec) x).length
        = (printG (.fix m body dec) x).toList.length := by
      rw [hprint, ← String.length_toList]
    rw [List.append_nil] at *
    omega
  have h1 := parse_print_fix m body dec hp hctx
    ((print (.fix m body dec) x).length + 1) x [] 0
    hval htail hfuel
  have hcur : (printG (.fix m body dec) x).toList ++ []
      = (print (.fix m body dec) x).toList := by
    rw [hprint, List.append_nil]
  rw [hcur] at h1
  have h1' : Grammar.parse (.fix m body dec) ((print (.fix m body dec) x).length + 1)
      ⟨0, (print (.fix m body dec) x).toList⟩
      = .ok (x, ⟨0 + (printG (.fix m body dec) x).length, ([] : List Char)⟩) := h1
  simp only [Grammar.run]
  rw [h1']

/-! ## §6.7: the closed law 1, the FIX-FREE fragment (the flat formats' face)

    The migration blocker's answer: the flat, recursion-free formats (a
    `rep`-top/`seq`-top grammar value with NO `fix` and no `self` node
    anywhere) had no landed law-1 face — `parse_print_fix` is the
    fix-topped face only. This section lands the closed law over the
    non-fix fragment:

    - `Grammar.FixFree` — the syntactic fold (the honest narrowing; the
      fully general closed law needs the closed junction's `fix` arm,
      the honest boundary documented at `parse_print_fix` above —
      unchanged).
    - the closed `tailOk` equations (the `printG_eqs` pattern);
    - `Grammar.junctionG_fixFree` — the closed junction, the E-level
      `junctionE`'s twin with the `selfE` leaves ABSENT: no `tokStar`
      handler, no AccD recursion, and no `(sb, ·)` virtual-seq rows —
      the rows are the REAL node pairs (`tailFirst a` vs `effFirst b`),
      exactly what the certificate's WF-SEQ/WF-REP rows carry;
    - `Grammar.parse_print_fixFree` — the closed law 1 over the
      fragment. Because a fix-free grammar has no `selfE` crossing, the
      E-family's strong-fuel induction DISSOLVES to a plain structural
      induction (the `selfE` case was the only consumer of the fuel
      IH), and the `rowCtx` premise dissolves with it: the fix-topped
      face's virtual-seq rows existed only for the recursion crossings,
      and the real node pairs ride `Predictive`. The guard-slack
      propagation of the fix-topped face also dissolves: every node of
      a predictive closed grammar is guarded (`predictive_guard`), so
      every slack is 1 — arithmetic.
    - `Grammar.run_print_fixFree` — the run corollary (§6.6's shape). -/

/-- `tailOk`'s per-node equations (iota; the closed law's rewrite
    surface — the `printG_eqs` pattern). -/
theorem Grammar.tailOk_atom (L : Lexeme R) (x : R) (sfx : List Char) :
    tailOk (.atom L) x sfx = L.munch.all (fun p => sfx.head?.all (fun c => !p c)) := rfl

theorem Grammar.tailOk_seq (a : Grammar A) (b : Grammar B) (p : A) (q : B) (sfx : List Char) :
    tailOk (.seq a b) (p, q) sfx =
      (tailOk b q sfx && (if nullable b then tailOk a p sfx else true)) := rfl

theorem Grammar.tailOk_alt (a b : Grammar R) (x : R) (sfx : List Char) :
    tailOk (.alt a b) x sfx =
      (if valueOk a x then tailOk a x sfx
       else tailOk b x sfx &&
         (if nullable b then (effFirst a).all (fun h => !h.matches sfx) else true)) := rfl

theorem Grammar.tailOk_rep (a : Grammar A) (xs : List A) (sfx : List Char) :
    tailOk (.rep a) xs sfx =
      (((effFirst a).all (fun h => !h.matches sfx)) && xs.all (fun z => tailOk a z sfx)) := rfl

theorem Grammar.tailOk_opt_some (a : Grammar A) (z : A) (sfx : List Char) :
    tailOk (.opt a) (Option.some z) sfx = tailOk a z sfx := rfl

theorem Grammar.tailOk_opt_none (a : Grammar A) (sfx : List Char) :
    tailOk (.opt a) Option.none sfx = (effFirst a).all (fun h => !h.matches sfx) := rfl

theorem Grammar.tailOk_label (n : String) (a : Grammar A) (x : A) (sfx : List Char) :
    tailOk (.label n a) x sfx = tailOk a x sfx := rfl

theorem Grammar.tailOk_rel (m : Kit.Codec Raw R) (owns : R → Bool)
    (don : ∀ raw r, m.decode raw = Option.some r → owns r = true)
    (ex : ∀ raw r, m.decode raw = Option.some r → m.encode r = raw)
    (nm : String) (vld : List String) (sub : Grammar Raw) (x : R) (sfx : List Char) :
    tailOk (.rel m owns don ex nm vld sub) x sfx = tailOk sub (m.encode x) sfx := rfl

/-- The fix-free fold: no `fix` node anywhere in the closed grammar
    (the honest narrowing of the closed law 1 — see §6.7's header). -/
def Grammar.FixFree : {A : Type} → Grammar A → Prop :=
  fun {_} g => match g with
  | .atom _ => True
  | .seq a b => FixFree a ∧ FixFree b
  | .alt a b => FixFree a ∧ FixFree b
  | .rep a => FixFree a
  | .opt a => FixFree a
  | .label _ a => FixFree a
  | .rel _ _ _ _ _ _ sub => FixFree sub
  | .fix _ _ _ => False

/-- The `fix` node is exactly what the fragment excludes (the
    fold's `fix` arm is `False` — a defeq). -/
theorem Grammar.fixFree_fix {R : Type} {m : R → Nat} {body : GrammarE R R}
    {dec : ∀ x y, SelfPathE body x y → m y < m x} :
    ¬ FixFree (.fix m body dec) := fun h => h

/-- Every predictive closed grammar is guarded, so its fuel slack is
    exactly 1 (§6.7's slack-dissolution face). -/
theorem Grammar.guardSlack_eq_one {A : Type} {g : Grammar A} (hp : Predictive g) :
    guardSlack g = 1 := by
  unfold guardSlack
  rw [if_pos (predictive_guard g hp)]

/-- THE junction lemma, closed level, fix-free fragment (§6.7). The
    E-level `junctionE`'s twin with the `selfE` leaves absent: no HSJ
    handler, no AccD, no `(sb, ·)` virtual rows — the rows are the REAL
    node pairs, and the sub-junction rows derive from the caller's rows
    by the closed membership helpers (§6.3's closed block). -/
theorem Grammar.junctionG_fixFree :
    {A : Type} → (a : Grammar A) → FixFree a →
    ∀ {B : Type} (b : Grammar B) (p : A) (q : B) (sfx : List Char),
    Predictive a → Predictive b →
    (rowTF : ∀ s1 ∈ tailFirst a, ∀ s2 ∈ effFirst b, HeadSpec.disj s1 s2 = true) →
    (rowTM : ∀ pp ∈ (tailMunch a).getD [], ∀ s2 ∈ effFirst b, s2.breaks pp = true) →
    valueOk b q = true → tailOk b q sfx = true →
    (hbne : printG b q ≠ "") → valueOk a p = true →
    tailOk a p ((printG b q).toList ++ sfx) = true := by
  intro A a
  induction a with
  | atom L =>
      intro _ B b p q sfx _ hpb rowTF rowTM hbval hbtail hbne hvalA
      rw [tailOk_atom]
      obtain ⟨h, hmem, hm⟩ := (printBundleG b hpb q hbval).2 hbne sfx
      cases hLm : L.munch with
      | none => rfl
      | some pp =>
          have hrow : h.breaks pp = true := rowTM pp (by
            show pp ∈ (tailMunch (.atom L)).getD []
            show pp ∈ L.munch.toList
            rw [hLm]
            exact List.Mem.head []) h hmem
          exact HeadSpec.breaks_sound hrow hm
  | seq c d ihc ihd =>
      intro hff B b p q sfx hp hpb rowTF rowTM hbval hbtail hbne hvalA
      obtain ⟨u, v⟩ := p
      obtain ⟨hpc, hpd, hrowCD_TF, hrowCD_TM⟩ := hp
      obtain ⟨hfc, hfd⟩ := hff
      rw [valueOk_seq] at hvalA
      obtain ⟨hvalC, hvalD⟩ := (Bool.and_eq_true _ _).mp hvalA
      have htmSomeC : (tailMunch c).isSome = true := tailMunch_isSome c hpc
      have htmSomeD : (tailMunch d).isSome = true := tailMunch_isSome d hpd
      have rowTFd : ∀ s1 ∈ tailFirst d, ∀ s2 ∈ effFirst b, s1.disj s2 = true :=
        fun s1 h1 => rowTF s1 (tailFirst_seqR c d s1 h1)
      have rowTMd : ∀ pp ∈ (tailMunch d).getD [], ∀ s2 ∈ effFirst b, s2.breaks pp = true :=
        fun pp hp' => rowTM pp (tailMunch_seqR c d htmSomeC htmSomeD pp hp')
      rw [tailOk_seq, ihd hfd b v q sfx hpd hpb rowTFd rowTMd hbval hbtail hbne hvalD]
      cases hnd : nullable d with
      | false => rfl
      | true =>
          have rowTFc : ∀ s1 ∈ tailFirst c, ∀ s2 ∈ effFirst b, s1.disj s2 = true :=
            fun s1 h1 => rowTF s1 (tailFirst_seqL c d hnd s1 h1)
          have rowTMc : ∀ pp ∈ (tailMunch c).getD [], ∀ s2 ∈ effFirst b, s2.breaks pp = true :=
            fun pp hp' => rowTM pp (tailMunch_seqL c d htmSomeC htmSomeD hnd pp hp')
          rw [if_pos rfl, Bool.true_and]
          exact ihc hfc b u q sfx hpc hpb rowTFc rowTMc hbval hbtail hbne hvalC
  | alt c d ihc ihd =>
      intro hff B b p q sfx hp hpb rowTF rowTM hbval hbtail hbne hvalA
      obtain ⟨hpc, hpd, hrowCD, _⟩ := hp
      obtain ⟨hfc, hfd⟩ := hff
      have htmSomeC : (tailMunch c).isSome = true := tailMunch_isSome c hpc
      have htmSomeD : (tailMunch d).isSome = true := tailMunch_isSome d hpd
      rw [valueOk_alt] at hvalA
      rw [tailOk_alt]
      cases hd : valueOk c p with
      | true =>
          rw [if_pos rfl]
          have rowTFc : ∀ s1 ∈ tailFirst c, ∀ s2 ∈ effFirst b, s1.disj s2 = true :=
            fun s1 h1 => rowTF s1 (tailFirst_altL c d s1 h1)
          have rowTMc : ∀ pp ∈ (tailMunch c).getD [], ∀ s2 ∈ effFirst b, s2.breaks pp = true :=
            fun pp hp' => rowTM pp (tailMunch_altL c d htmSomeC htmSomeD pp hp')
          exact ihc hfc b p q sfx hpc hpb rowTFc rowTMc hbval hbtail hbne hd
      | false =>
          have hdD : valueOk d p = true := by
            simp [hd] at hvalA
            exact hvalA
          rw [if_neg (by decide)]
          have rowTFd : ∀ s1 ∈ tailFirst d, ∀ s2 ∈ effFirst b, s1.disj s2 = true :=
            fun s1 h1 => rowTF s1 (tailFirst_altR c d s1 h1)
          have rowTMd : ∀ pp ∈ (tailMunch d).getD [], ∀ s2 ∈ effFirst b, s2.breaks pp = true :=
            fun pp hp' => rowTM pp (tailMunch_altR c d htmSomeC htmSomeD pp hp')
          rw [ihd hfd b p q sfx hpd hpb rowTFd rowTMd hbval hbtail hbne hdD]
          cases hnd : nullable d with
          | false => rfl
          | true =>
              rw [if_pos rfl]
              obtain ⟨h, hmem, hm⟩ := (printBundleG b hpb q hbval).2 hbne sfx
              exact List.all_eq_true.mpr (fun s1 h1 => by
                have hd1 := rowTF s1 (tailFirst_alt_third c d hnd s1 h1) h hmem
                have h2d : h.disj s1 = true := by rw [HeadSpec.disj_symm]; exact hd1
                simp [HeadSpec.disj_sound h2d _ hm])
  | rep c ihc =>
      intro hff B b xs q sfx hp hpb rowTF rowTM hbval hbtail hbne hvalA
      obtain ⟨hpc, _, _, _⟩ := hp
      rw [tailOk_rep, Bool.and_eq_true]
      refine ⟨?_, List.all_eq_true.mpr (fun z hz => ?_)⟩
      · obtain ⟨h, hmem, hm⟩ := (printBundleG b hpb q hbval).2 hbne sfx
        exact List.all_eq_true.mpr (fun s1 h1 => by
          have hd1 := rowTF s1 (tailFirst_rep_eff c s1 h1) h hmem
          have h2d : h.disj s1 = true := by rw [HeadSpec.disj_symm]; exact hd1
          simp [HeadSpec.disj_sound h2d _ hm])
      · have hvalZ : valueOk c z = true := by
          have h3 := hvalA
          rw [valueOk_rep] at h3
          exact List.all_eq_true.mp h3 z hz
        exact ihc hff b z q sfx hpc hpb
          (fun s1 h1 => rowTF s1 (tailFirst_rep c s1 h1))
          (fun pp hp' => rowTM pp hp')
          hbval hbtail hbne hvalZ
  | opt c ihc =>
      intro hff B b p q sfx hp hpb rowTF rowTM hbval hbtail hbne hvalA
      obtain ⟨hpc, _⟩ := hp
      cases p with
      | none =>
          rw [tailOk_opt_none]
          obtain ⟨h, hmem, hm⟩ := (printBundleG b hpb q hbval).2 hbne sfx
          exact List.all_eq_true.mpr (fun s1 h1 => by
            have hd1 := rowTF s1 (tailFirst_opt_eff c s1 h1) h hmem
            have h2d : h.disj s1 = true := by rw [HeadSpec.disj_symm]; exact hd1
            simp [HeadSpec.disj_sound h2d _ hm])
      | some z =>
          rw [tailOk_opt_some]
          have hvalC : valueOk c z = true := by
            have h3 := hvalA
            rw [valueOk_opt_some] at h3
            exact h3
          exact ihc hff b z q sfx hpc hpb
            (fun s1 h1 => rowTF s1 (tailFirst_opt c s1 h1))
            (fun pp hp' => rowTM pp hp')
            hbval hbtail hbne hvalC
  | label n c ihc =>
      intro hff B b p q sfx hpc hpb rowTF rowTM hbval hbtail hbne hvalA
      rw [tailOk_label]
      exact ihc hff b p q sfx hpc hpb rowTF rowTM hbval hbtail hbne hvalA
  | rel m owns don ex nm vld sub ihc =>
      intro hff B b p q sfx hpc hpb rowTF rowTM hbval hbtail hbne hvalA
      have hvalS : valueOk sub (m.encode p) = true := by
        have h3 := hvalA
        rw [valueOk_rel] at h3
        exact (Bool.and_eq_true _ _).mp h3 |>.2
      rw [tailOk_rel]
      exact ihc hff b (m.encode p) q sfx hpc hpb rowTF rowTM hbval hbtail hbne hvalS
  | fix m body dec =>
      intro hff
      exact absurd hff fixFree_fix

/-- THE round-trip law 1, closed level, the FIX-FREE fragment (§6.7's
    header): a fix-free grammar's derived parser accepts the print of
    every value-owned text and leaves the suffix. The per-node case
    table is §6.5's, executed over the CLOSED family
    (`printBundleG`/`parseExcludeG`/`parseConsumeG` + the closed
    junction above); no `rowCtx` premise (the virtual-seq rows existed
    only for the `selfE` crossings), no fuel-IH (no `selfE` crossing —
    a plain STRUCTURAL induction suffices), every slack 1
    (`guardSlack_eq_one`). The cursor rides as a variable + the `hcs`
    premise (the E-level `parse_print_E`'s discipline — the IHs
    rewrite syntactically). -/
theorem Grammar.parse_print_fixFree {A : Type} :
    ∀ (g : Grammar A), FixFree g → Predictive g →
    ∀ (fuel : Nat) (x : A) (sfx : List Char) (cur : Cursor),
      valueOk g x = true → tailOk g x sfx = true →
      cur.cs = (printG g x).toList ++ sfx →
      ((printG g x).toList ++ sfx).length + guardSlack g ≤ fuel →
      parseG g fuel cur = .ok (x, ⟨cur.off + (printG g x).length, sfx⟩) := by
  intro g
  induction g with
  | atom L =>
      intro _ _ fuel x sfx cur hval htail hcs _
      rw [tailOk_atom] at htail
      cases cur with
      | mk k cs =>
          have hcs' : cs = (L.print x).toList ++ sfx := hcs
          simp only [Grammar.parseG, hcs']
          exact L.print_scan k x sfx hval htail
  | seq a b iha ihb =>
      intro hff hp fuel x sfx cur hval htail hcs hfuel
      have hgs : guardSlack (.seq a b) = 1 := guardSlack_eq_one hp
      obtain ⟨p, q⟩ := x
      obtain ⟨hpa, hpb, hrowTF, hrowTM⟩ := hp
      obtain ⟨hfa, hfb⟩ := hff
      rw [valueOk_seq] at hval
      obtain ⟨hvalA, hvalB⟩ := (Bool.and_eq_true _ _).mp hval
      rw [tailOk_seq] at htail
      obtain ⟨htB, htAcond⟩ := (Bool.and_eq_true _ _).mp htail
      rw [printG_seq] at hcs hfuel ⊢
      -- a's shifted tail (the junction, with the emptiness sub-case)
      have htailA : tailOk a p ((printG b q).toList ++ sfx) = true := by
        by_cases hep : printG b q = ""
        · have hnb : nullable b = true := by
            cases h : nullable b with
            | true => rfl
            | false => exact absurd hep ((printBundleG b hpb q hvalB).1 h)
          have hep' : (printG b q).toList ++ sfx = sfx := by rw [hep]; simp
          rw [if_pos hnb] at htAcond
          rw [hep']
          exact htAcond
        · exact junctionG_fixFree a hfa b p q sfx hpa hpb hrowTF hrowTM
            hvalB htB hep hvalA
      -- the fuel (every slack 1)
      rw [hgs] at hfuel
      have hgsA : guardSlack a = 1 := guardSlack_eq_one hpa
      have hgsB : guardSlack b = 1 := guardSlack_eq_one hpb
      have hlen : ((printG a p ++ printG b q).toList ++ sfx).length
          = (printG a p).toList.length
            + ((printG b q).toList.length + sfx.length) := by
        rw [String.toList_append, List.length_append, List.length_append]
        omega
      rw [hlen] at hfuel
      have hfuelA : ((printG a p).toList ++ ((printG b q).toList ++ sfx)).length
          + guardSlack a ≤ fuel := by
        rw [hgsA, List.length_append, List.length_append]
        omega
      have hfuelB : ((printG b q).toList ++ sfx).length + guardSlack b ≤ fuel := by
        rw [hgsB, List.length_append]
        omega
      have hcsA : cur.cs = (printG a p).toList ++ ((printG b q).toList ++ sfx) := by
        rw [hcs, String.toList_append, List.append_assoc]
      have h1 := iha hfa hpa fuel p ((printG b q).toList ++ sfx) cur
        hvalA htailA hcsA hfuelA
      simp only [Grammar.parseG, h1]
      have h2 := ihb hfb hpb fuel q sfx ⟨cur.off + (printG a p).length,
        (printG b q).toList ++ sfx⟩ hvalB htB rfl hfuelB
      simp only [h2, String.length_append, Nat.add_assoc]
  | alt a b iha ihb =>
      intro hff hp fuel x sfx cur hval htail hcs hfuel
      have hgs : guardSlack (.alt a b) = 1 := guardSlack_eq_one hp
      obtain ⟨hpa, hpb, hrowALT, hnnA⟩ := hp
      obtain ⟨hfa, hfb⟩ := hff
      rw [valueOk_alt] at hval
      rw [tailOk_alt] at htail
      rw [printG_alt] at hcs hfuel ⊢
      cases hdisc : valueOk a x with
      | true =>
          rw [if_pos hdisc] at htail hcs
          rw [if_pos hdisc, hgs] at hfuel
          show parseG (.alt a b) fuel cur
            = .ok (x, ⟨cur.off + (printG a x).length, sfx⟩)
          have hfuelA : ((printG a x).toList ++ sfx).length + guardSlack a ≤ fuel := by
            rw [guardSlack_eq_one hpa]; exact hfuel
          have h1 := iha hfa hpa fuel x sfx cur hdisc htail hcs hfuelA
          simp only [Grammar.parseG, h1]
      | false =>
          have hdB : valueOk b x = true := by
            simp [hdisc] at hval
            exact hval
          rw [if_neg (by simp [hdisc])] at htail hcs
          rw [if_neg (by simp [hdisc]), hgs] at hfuel
          show parseG (.alt a b) fuel cur
            = .ok (x, ⟨cur.off + (printG b x).length, sfx⟩)
          obtain ⟨htB, htStop⟩ := (Bool.and_eq_true _ _).mp htail
          -- the exclusion of a
          have hfail : ∀ h ∈ effFirst a, h.matches cur.cs = false := by
            intro h hmem
            by_cases hep : printG b x = ""
            · have hnb : nullable b = true := by
                cases h : nullable b with
                | true => rfl
                | false => exact absurd hep ((printBundleG b hpb x hdB).1 h)
              have hep' : (printG b x).toList ++ sfx = sfx := by rw [hep]; simp
              rw [if_pos hnb] at htStop
              rw [hcs, hep']
              simpa using List.all_eq_true.mp htStop h hmem
            · obtain ⟨h', h'mem, h'm⟩ := (printBundleG b hpb x hdB).2 hep sfx
              rw [hcs]
              have hd1 := hrowALT h hmem h' h'mem
              have h2d : h'.disj h = true := by rw [HeadSpec.disj_symm]; exact hd1
              exact HeadSpec.disj_sound h2d _ h'm
          obtain ⟨e, he⟩ := parseExcludeG fuel hpa cur.off cur.cs hnnA hfail
          have he' : parseG a fuel cur = .error e := he
          have hfuelB : ((printG b x).toList ++ sfx).length + guardSlack b ≤ fuel := by
            rw [guardSlack_eq_one hpb]; exact hfuel
          have h2 := ihb hfb hpb fuel x sfx cur hdB htB hcs hfuelB
          simp only [Grammar.parseG, he', h2]
  | rep a iha =>
      intro hff hp fuel xs sfx cur hval htail hcs hfuel
      have hgr : guardSlack (.rep a) = guardSlack a := rfl
      obtain ⟨hpa, hnnA, hrowTMaa, hrowTFaa⟩ := hp
      rw [printG_rep] at hcs hfuel ⊢
      rw [tailOk_rep] at htail
      obtain ⟨hstop, hbase⟩ := (Bool.and_eq_true _ _).mp htail
      have hbase' : ∀ w (_ : w ∈ xs), tailOk a w sfx = true :=
        fun w hw => List.all_eq_true.mp hbase w hw
      have hval' : ∀ w (_ : w ∈ xs), valueOk a w = true := by
        intro w hw
        have h3 := hval
        rw [Grammar.valueOk_rep] at h3
        exact List.all_eq_true.mp h3 w hw
      -- the stacking lemma: shift a's tail by the print of a whole list
      have shiftBy : ∀ (ws) (sfx' : List Char),
          (∀ w, w ∈ ws → valueOk a w = true) →
          (∀ w, w ∈ ws → tailOk a w sfx' = true) →
          ∀ (z), valueOk a z = true → tailOk a z sfx' = true →
          tailOk a z
            ((List.foldr (fun w acc => printG a w ++ acc) "" ws).toList ++ sfx') = true := by
        intro ws
        induction ws with
        | nil =>
            intro sfx' _ _ z _ hz
            simp only [List.foldr_nil]
            exact hz
        | cons w ws ih =>
            intro sfx' hvalW hbaseW z hvalZ hzTail
            -- step 1: the IH at w (shift by ws's print)
            have hw1 := ih sfx' (fun v hv => hvalW v (List.Mem.tail w hv))
              (fun v hv => hbaseW v (List.Mem.tail w hv)) w
              (hvalW w (List.Mem.head ws))
              (hbaseW w (List.Mem.head ws))
            -- step 2: junctionG_fixFree at (z, w), suffix shifted by ws's print
            have hbw : printG a w ≠ "" :=
              (printBundleG a hpa w (hvalW w (List.Mem.head ws))).1 hnnA
            have hstep := junctionG_fixFree a hff a z w
              ((List.foldr (fun v acc => printG a v ++ acc) "" ws).toList ++ sfx')
              hpa hpa hrowTFaa hrowTMaa
              (hvalW w (List.Mem.head ws)) hw1 hbw hvalZ
            show tailOk a z
              ((List.foldr (fun v acc => printG a v ++ acc) "" (w :: ws)).toList
                ++ sfx') = true
            rw [List.foldr_cons, String.toList_append, List.append_assoc]
            exact hstep
      -- the engine (§6.4's local fuel induction)
      have engine : ∀ (f : Nat), f ≤ fuel → ∀ (ys) (c : Cursor),
          (∀ w, w ∈ ys → valueOk a w = true) →
          (∀ w, w ∈ ys → tailOk a w sfx = true) →
          ((effFirst a).all (fun h => !h.matches sfx)) = true →
          c.cs.length + guardSlack a ≤ f →
          c.cs = (List.foldr (fun z acc => printG a z ++ acc) "" ys).toList ++ sfx →
          parseManyG a f c
            = .ok (ys, ⟨c.off + (List.foldr (fun z acc => printG a z ++ acc) "" ys).length,
              sfx⟩) := by
        intro f hfF
        induction f with
        | zero =>
            intro ys c hvalY hbaseY hstopY hf0 hcsE
            cases ys with
            | nil =>
                simp only [Grammar.parseManyG]
                rw [List.foldr_nil] at hcsE
                cases c with
                | mk off cs => have hcs'' : cs = sfx := hcsE; simp [hcs'']
            | cons z zs =>
                have hPz : printG a z ≠ "" :=
                  (printBundleG a hpa z (hvalY z (List.Mem.head zs))).1 hnnA
                have h1g : 1 ≤ guardSlack a := by unfold guardSlack; split <;> omega
                have hlen : 0 < (printG a z).toList.length := by
                  have h2 := String.ne_empty_length hPz
                  rw [← String.length_toList] at h2
                  exact h2
                rw [hcsE, List.foldr_cons, String.toList_append,
                  List.length_append, List.length_append] at hf0
                exact absurd hf0 (by omega)
        | succ f ih =>
            intro ys c hvalY hbaseY hstopY hf1 hcsE
            cases ys with
            | nil =>
                -- the stop: the body FAILS on sfx (heads-fail + WF-REP-1)
                have hcs' : c.cs = sfx := by rw [hcsE]; simp [List.foldr_nil]
                have hfail : ∀ h ∈ effFirst a, h.matches c.cs = false := by
                  intro h hmem
                  rw [hcs']
                  simpa using List.all_eq_true.mp hstopY h hmem
                obtain ⟨e, he⟩ := parseExcludeG (f + 1) hpa c.off c.cs hnnA hfail
                have he' : parseG a (f + 1) c = .error e := he
                simp only [Grammar.parseManyG, he']
                rw [List.foldr_nil]
                cases c with
                | mk off cs => have hcs'' : cs = sfx := hcs'; simp [hcs'']
            | cons z zs =>
                -- the shifted tail for z (the stacking lemma)
                have hz1 : tailOk a z
                    ((List.foldr (fun w acc => printG a w ++ acc) "" zs).toList ++ sfx)
                  = true := by
                  apply shiftBy zs sfx
                  · intro w hw; exact hvalY w (List.Mem.tail z hw)
                  · intro w hw; exact hbaseY w (List.Mem.tail z hw)
                  · exact hvalY z (List.Mem.head zs)
                  · exact hbaseY z (List.Mem.head zs)
                -- the element parse (the outer law's IH at sub-grammar a)
                have hcsZ : c.cs = (printG a z).toList ++
                    ((List.foldr (fun w acc => printG a w ++ acc) "" zs).toList ++ sfx) := by
                  rw [hcsE, List.foldr_cons, String.toList_append, List.append_assoc]
                have hfuel' : ((printG a z).toList ++
                    ((List.foldr (fun w acc => printG a w ++ acc) "" zs).toList ++ sfx)).length
                    + guardSlack a ≤ f + 1 := by
                  rw [List.length_append, List.length_append]
                  have h1 := congrArg List.length hcsZ
                  rw [List.length_append, List.length_append] at h1
                  rw [h1] at hf1
                  omega
                have hbody := iha hff hpa (f + 1) z
                  ((List.foldr (fun w acc => printG a w ++ acc) "" zs).toList ++ sfx)
                  c (hvalY z (List.Mem.head zs)) hz1 hcsZ hfuel'
                cases hb : parseG a (f + 1) c with
                | error e => simp only [hb] at hbody; simp at hbody
                | ok r =>
                    obtain ⟨z₁, c₁⟩ := r
                    simp only [hb] at hbody
                    obtain ⟨hzz, hcc2⟩ := Prod.mk.inj (Except.ok.inj hbody)
                    have hoff : c₁.off = c.off + (printG a z).length := by
                      rw [hcc2]
                    have hcsR : c₁.cs = (List.foldr (fun w acc => printG a w ++ acc)
                        "" zs).toList ++ sfx := by
                      rw [hcc2]
                    -- progress (WF-REP-1's consumption)
                    have hprog : c₁.cs.length < c.cs.length :=
                      parseConsumeG (f + 1) hpa hb hnnA
                    simp only [Grammar.parseManyG, hb, if_pos hprog]
                    -- the recursive engine call
                    have hbaseZ : ∀ w (_ : w ∈ zs), tailOk a w sfx = true := by
                      intro w hw
                      exact hbaseY w (List.Mem.tail z hw)
                    have hvalZ : ∀ w (_ : w ∈ zs), valueOk a w = true := by
                      intro w hw
                      exact hvalY w (List.Mem.tail z hw)
                    have hfuelR : c₁.cs.length + guardSlack a ≤ f := by omega
                    have hrec := ih (by omega) zs c₁ hvalZ hbaseZ hstopY hfuelR hcsR
                    simp only [hrec, hzz, List.foldr_cons,
                      String.length_append, hoff, Nat.add_assoc]
      -- the engine call at the case's own data
      have hfuelE : cur.cs.length + guardSlack a ≤ fuel := by
        rw [hgr, ← hcs] at hfuel
        exact hfuel
      simp only [Grammar.parseG]
      exact engine fuel (Nat.le_refl fuel) xs cur hval' hbase' hstop hfuelE hcs
  | opt a iha =>
      intro hff hp fuel x sfx cur hval htail hcs hfuel
      have hgs : guardSlack (.opt a) = 1 := guardSlack_eq_one hp
      obtain ⟨hpa, hnnA⟩ := hp
      cases x with
      | none =>
          rw [printG_opt_none] at hcs hfuel ⊢
          rw [tailOk_opt_none] at htail
          have hcs' : cur.cs = sfx := by simpa using hcs
          have hfail : ∀ h ∈ effFirst a, h.matches cur.cs = false := by
            intro h hmem
            rw [hcs']
            simpa using List.all_eq_true.mp htail h hmem
          obtain ⟨e, he⟩ := parseExcludeG fuel hpa cur.off cur.cs hnnA hfail
          have he' : parseG a fuel cur = .error e := he
          simp only [Grammar.parseG, he']
          cases cur with
          | mk off cs => have hcs'' : cs = sfx := hcs'; simp [hcs'']
      | some z =>
          rw [printG_opt_some] at hcs hfuel ⊢
          rw [tailOk_opt_some] at htail
          rw [hgs] at hfuel
          have hfuelA : ((printG a z).toList ++ sfx).length + guardSlack a ≤ fuel := by
            rw [guardSlack_eq_one hpa]; exact hfuel
          have h1 := iha hff hpa fuel z sfx cur hval htail hcs hfuelA
          simp only [Grammar.parseG, h1]
  | label n a iha =>
      intro hff hp fuel x sfx cur hval htail hcs hfuel
      rw [printG_label] at hcs hfuel ⊢
      have h1 := iha hff hp fuel x sfx cur hval htail hcs hfuel
      simp only [Grammar.parseG, h1]
  | rel m owns don ex nm vld sub iha =>
      intro hff hp fuel x sfx cur hval htail hcs hfuel
      rw [printG_rel] at hcs hfuel ⊢
      rw [valueOk_rel] at hval
      have hvalS : valueOk sub (m.encode x) = true :=
        (Bool.and_eq_true _ _).mp hval |>.2
      have h1 := iha hff hp fuel (m.encode x) sfx cur hvalS htail hcs hfuel
      simp only [Grammar.parseG, h1, Kit.Codec.decode_encode]
  | fix m body dec =>
      intro hff
      exact absurd hff fixFree_fix

/-- THE run corollary over the fix-free fragment (§6.6's shape): the
    format's `run` accepts the print of any value-owned text. -/
theorem Grammar.run_print_fixFree {R : Type} (g : Grammar R)
    (hff : FixFree g) (hp : Predictive g) (x : R) (hval : valueOk g x = true) :
    run g (print g x) = .ok x := by
  have htail := tailOk_nil g hp x
  have hgs : guardSlack g = 1 := guardSlack_eq_one hp
  have hprint : print g x = printG g x := rfl
  have hfuel : ((printG g x).toList ++ []).length + guardSlack g
      ≤ (print g x).length + 1 := by
    rw [hgs, List.append_nil, hprint, ← String.length_toList]
    omega
  have h1 := parse_print_fixFree g hff hp ((print g x).length + 1) x []
    ⟨0, (print g x).toList⟩ hval htail (by rw [← hprint, List.append_nil]) hfuel
  have h1' : parse g ((print g x).length + 1) ⟨0, (print g x).toList⟩
      = .ok (x, ⟨0 + (printG g x).length, ([] : List Char)⟩) := h1
  simp only [Grammar.run]
  rw [h1']

/-! ## §7: the certificate's CheckedProp packaging (15 #1) -/

/-- The CheckedProp row (15 #1, v2 §4.2): the predictive fragment's
    decidable route. Sound PROVED (`wfCheck_sound`); completeness LOUDLY
    `.missing` (the cls/cls + conservative corners — forever). The
    universe is bumped (`CheckedProp.{u}`) because `Grammar R : Type 1`. -/
def Grammar.grammarPredictive {R : Type} : Kit.CheckedProp (Grammar R) where
  P := fun g => g.Predictive
  check := fun g => g.wfCheck
  sound := fun _ h => Grammar.wfCheck_sound _ h
  complete? := .missing

end TextKit
