/-
# TextKit.Grammar — the grammar AS DATA, not code

The substrait pattern (its `Grammar.lean` table precedent) lifted to the
generic level: a closed, data-level `Grammar` value for token-ish
languages, recognized over the existing `TextKit.Parser` monad, with the
emitter side (`emit`) and the recognizer side (`pOf`/`parseTokens`) both
derived from ONE value — they cannot drift.

The model is the TOKEN-STREAM grammar:

    Grammar := tok "…" | scanTo q | seq gs | alt gs | rep g | named name

- `.tok s`   — the literal token `s` (consumed byte-exactly).
- `.scanTo q` — the DATA-level scanner: the maximal run of characters
  BEFORE `q` (consumes zero or more chars, never `q` itself). This is the
  one scanner constructor — arbitrary string values (TOML string bodies,
  key runs) need it, and a `Char`-valued constructor keeps the
  data-deriving (BEq/Inhabited) intact. `scanTo`'s emission is not a
  constant (its text comes from the INPUT), so it is a CONSUMER-side
  grammar: it never participates in the inversion fragment. (Named
  `scanTo` — not `until` — because this toolchain rejects `until` as a
  bare case-label identifier: a parser fact, not a choice.)
- `.seq gs`  — sequencing (concatenation).
- `.alt gs`  — ordered choice (first success wins, with backtracking).
- `.rep g`   — repetition of `g`, FUELED by the input length (each
  iteration must consume — GWF's firstset rule — and the loop stops
  early on a no-progress iteration; the fuel is a plain structural index,
  so the termination proofs stay kernel-replayable, no well-founded
  measure).
- `.named name` — a NAMED REFERENCE to a production (mutual grammar
  recursion for a future consumer). DEFERRED in this module: recognition
  fails (`pOf`'s named case), the emission is `""`, GWF treats it
  leniently. W-C2 (the substrait lift-out's second consumer wave) lands
  the fixpoint machinery; see `rec_deferred`. (Not `rec` — Lean reserves
  `<Ind>.rec` for the generated recursor.)

The three SUPER-POWERS this module exists for:

1. `emit : Grammar → String` — the byte-exact printer.
2. `pOf : (String → Parser α) → Grammar → Parser (List α)` — payload
   recognition over `TextKit.Parser`; `parseTokens` is its α := String
   free function (the token-list lane). The composition collects each
   token's action result into a `List α` — a plain `α` has no combining
   operation, so the list accumulator is the honest generic shape
   (documented deviation from a hypothetical `Parser α`). The recursive
   combinators are INLINED in `pOf` (by-cases on the list arguments) so
   the termination is plain structural recursion — no drivers, no
   well-founded measures; `seqOf`/`altOf`/`repOf` remain for consumers
   who want the step-driven forms.
3. The INVERSION laws (`invert_tok`, `invert_core`, `invert_rep`,
   `invert_rep_behind_tok`): a GWF grammar recognizes its own emission —
   `pOfLift g (emit g ++ rest) = some (tokensOf g, rest)` — proof-shaped
   for the token-list fragment (`Core` grammars: tok/seq/alt; a rep of a
   Core body at the head or behind a token). `named` is excluded
   (deferred).

GWF (well-formedness) is the gate that makes recognition safe: every rep
body and seq part starts with a nonempty first set (so each rep iteration
consumes — the fuel rule), and alt branches have pairwise-disjoint first
sets (so the ordered choice is UNAMBIGUOUS — the W-C2 uniqueness pay-off).
`checkGWF` decides it; `checkGWF_eq_true_iff_GWF` bridges.

CORE-ONLY: imports only `TextKit.Basic` (itself import-free) — the
kernel-package discipline (this package sits below substrait; the proofs
reduce through core alone).
-/

module

public import TextKit.Basic

@[expose] public section

namespace TextKit

open TextKit.Parser

namespace Grammar

/-! ## the grammar -/

/-- The closed token-stream grammar. Growing a consumer = a VALUE of this
    type, not a hand-mirrored emitter/parser pair. -/
inductive Grammar where
  | tok (s : String)
  | scanTo (q : Char)
  | seq (gs : List Grammar)
  | alt (gs : List Grammar)
  | rep (g : Grammar)
  | named (name : String)
deriving Repr, BEq, Inhabited

/-! ## the emitter (the fold) -/

/-- The byte-exact printer: `tok s` writes its literal, `scanTo` writes
    nothing (its text is input-derived), `seq` folds its parts, `alt`/
    `rep` emit their canonical (first / one-iteration) shape, `named` is
    deferred (writes nothing). Structural recursion directly (the `.seq`
    tail is a smaller grammar — no helper/mutual machinery needed). -/
def emit : Grammar → String
  | .tok s => s
  | .scanTo _ => ""
  | .seq [] => ""
  | .seq (g :: gs) => emit g ++ emit (.seq gs)
  | .alt [] => ""
  | .alt (g :: _) => emit g
  | .rep g => emit g
  | .named _ => ""

/-- The token list a successful recognition of `g` collects: each tok
    contributes its literal; `seq` concatenates its parts; `alt`/`rep`
    contribute their canonical (first / one-iteration) shape; `scanTo`/
    `named` contribute nothing. -/
def tokensOf : Grammar → List String
  | .tok s => [s]
  | .scanTo _ => []
  | .seq [] => []
  | .seq (g :: gs) => tokensOf g ++ tokensOf (.seq gs)
  | .alt [] => []
  | .alt (g :: _) => tokensOf g
  | .rep g => tokensOf g
  | .named _ => []

/-! ## the first-set kit (token starts) -/

/-- The set of characters a successful match of `g` can START with
    (for `seq`/`alt` the component union — the SOUND direction for the
    disjointness check: if the unions are disjoint the actual first
    chars are disjoint; the deliverable sketch's `alt`-dedup is
    intentionally dropped so membership reasoning stays plain). `scanTo`
    can start with any char but its stop — complement-shaped, not a list —
    so it reports `[]` and is thereby excluded from GWF rep/seq/alt
    positions. -/
def firstSet : Grammar → List Char
  | .tok s => s.toList.take 1
  | .scanTo _ => []
  | .seq [] => []
  | .seq (g :: gs) => firstSet g ++ firstSet (.seq gs)
  | .alt [] => []
  | .alt (g :: gs) => firstSet g ++ firstSet (.alt gs)
  | .rep g => firstSet g
  | .named _ => []

/-! ## the recognition drivers

`seqOf`/`altOf`/`repOf` offer the step-driven composition for consumers;
`pOf` inlines the same recursion directly (by-cases on its list
arguments) so its termination is plain structural. `repAux` is the
fuel-fenced loop: at most as many iterations as input chars, one fuel per
iteration, stopping on a body failure or a zero-progress iteration (so
even a non-GWF body terminates). -/

/-- One-step sequencing: run `step` over a grammar list, concatenating
    payloads (recursion on the LIST). -/
def seqOf {α : Type} (step : Grammar → Parser (List α)) : List Grammar → Parser (List α)
  | [] => fun cs => some ([], cs)
  | g :: gs => fun cs =>
      match step g cs with
      | none => none
      | some (as, rest) =>
          match seqOf step gs rest with
          | none => none
          | some (bs, rest') => some (as ++ bs, rest')

/-- One-step ordered choice with backtracking: the first successful
    branch wins (recursion on the LIST). -/
def altOf {α : Type} (step : Grammar → Parser (List α)) : List Grammar → Parser (List α)
  | [] => fun _ => none
  | g :: gs => fun cs =>
      match step g cs with
      | some r => some r
      | none => altOf step gs cs

/-- The fuel-fenced repetition loop: guarded termination, the payload
    accumulates in consumption order. -/
def repAux {α : Type} (step : List Char → Option (List α × List Char)) :
    (fuel : Nat) → List α → List Char → Option (List α × List Char)
  | 0, acc, cs => some (acc, cs)
  | fuel + 1, acc, cs =>
      match step cs with
      | none => some (acc, cs)
      | some (bs, rest) =>
          if h : rest = cs then some (acc, cs)
          else repAux step fuel (acc ++ bs) rest

/-- Repetition with the input-length fuel. -/
def repOf {α : Type} (step : Grammar → Parser (List α)) (g : Grammar) : Parser (List α) :=
  fun cs => repAux (step g) cs.length [] cs

/-- The loop's reduction when the body fails: the collected payload
    stands. -/
theorem repAux_none {α : Type} (step : List Char → Option (List α × List Char))
    (fuel : Nat) (acc : List α) (cs : List Char)
    (h : step cs = none) :
    repAux step (fuel + 1) acc cs = some (acc, cs) := by
  cases fuel <;> simp [repAux, h]

/-- The loop's reduction when a (progressing) iteration succeeds. -/
theorem repAux_some {α : Type} (step : List Char → Option (List α × List Char))
    (fuel : Nat) (acc : List α) (cs rest : List Char) (bs : List α)
    (h1 : step cs = some (bs, rest)) (h2 : rest ≠ cs) :
    repAux step (fuel + 1) acc cs = repAux step fuel (acc ++ bs) rest := by
  simp [repAux, h1, h2]

/-- The loop's reduction on a zero-progress iteration: the payload stands
    (the guard the fuel rule documents). -/
theorem repAux_no_progress {α : Type} (step : List Char → Option (List α × List Char))
    (fuel : Nat) (acc : List α) (cs : List Char) (bs : List α)
    (h : step cs = some (bs, cs)) :
    repAux step (fuel + 1) acc cs = some (acc, cs) := by
  simp [repAux, h]

/-- The generic payload recognition: each `.tok` runs the action on its
    literal (the payload); `seq`/`alt`/`rep` compose with the monad
    (the recursion is inlined — by-cases on the list arguments — so
    termination is plain structural); `.scanTo` consumes its run WITHOUT
    a payload piece; `.named` fails (deferred — see the module header). -/
def pOf (act : String → Parser α) : Grammar → Parser (List α)
  | .tok s => fun cs =>
      match expect s cs with
      | none => none
      | some rest => match act s rest with
          | none => none
          | some (a, rest') => some ([a], rest')
  | .scanTo q => fun cs => some ([], cs.dropWhile (fun c => c != q))
  | .seq [] => fun cs => some ([], cs)
  | .seq (g :: gs) => fun cs =>
      match pOf act g cs with
      | none => none
      | some (as, rest) =>
          match pOf act (.seq gs) rest with
          | none => none
          | some (bs, rest') => some (as ++ bs, rest')
  | .alt [] => fun _ => none
  | .alt (g :: gs) => fun cs =>
      match pOf act g cs with
      | some r => some r
      | none => pOf act (.alt gs) cs
  | .rep g => fun cs => repAux (pOf act g) cs.length [] cs
  | .named _ => fun _ => none

/-- The lifted recognizer: `pOf` with the identity payload action (the
    deliverable's `pOfLift`). -/
def pOfLift (g : Grammar) : Parser (List String) := pOf (fun t => Parser.result t) g

/-- Token recognition as a free function: `parseTokens g cs = some (toks,
    rest)` — the token strings the grammar consumed and the unconsumed
    rest. -/
def parseTokens (g : Grammar) : Parser (List String) := pOfLift g

/-! ## the match-scrutinee reduction kit

`simp` cannot rewrite inside a `match` scrutinee in this toolchain, so the
parser compound's reductions are case-split EXPLICITLY here (the one
instance the case-split can replace: the head's parse term). -/

/-- The `.seq (g :: gs)` compound when the head's parse fails (the match
    collapses to `none`). -/
theorem pOfLift_seq_head_none (hd : Grammar) (tl : List Grammar) (cs : List Char)
    (h : pOfLift hd cs = none) : pOfLift (.seq (hd :: tl)) cs = none := by
  unfold pOfLift pOf
  cases heq : pOf (fun t => Parser.result t) hd cs with
  | none => rfl
  | some p =>
      have h' : pOf (fun t => Parser.result t) hd cs = none := by
        simpa [pOfLift] using h
      rw [h'] at heq
      cases heq

/-- The `.alt (g :: gs)` compound when the head fails: the fall-through is
    the ALT of the tail. -/
theorem pOfLift_alt_head_none (g : Grammar) (gs : List Grammar) (cs : List Char)
    (h : pOfLift g cs = none) (hs : pOfLift (.alt gs) cs = none) :
    pOfLift (.alt (g :: gs)) cs = none := by
  unfold pOfLift pOf
  cases heq : pOf (fun t => Parser.result t) g cs with
  | none =>
      simpa [pOfLift] using hs
  | some p =>
      have h' : pOf (fun t => Parser.result t) g cs = none := by
        simpa [pOfLift] using h
      rw [h'] at heq
      cases heq

/-- The `.alt (g :: gs)` compound when the head succeeds: the compound IS
    the head's result (ordered choice, first branch wins). -/
theorem pOfLift_alt_head_some (g : Grammar) (gs : List Grammar) (cs : List Char)
    (as : List String) (rest : List Char)
    (h : pOfLift g cs = some (as, rest)) :
    pOfLift (.alt (g :: gs)) cs = some (as, rest) := by
  unfold pOfLift pOf
  cases heq : pOf (fun t => Parser.result t) g cs with
  | none =>
      have h' : pOf (fun t => Parser.result t) g cs = some (as, rest) := by
        simpa [pOfLift] using h
      rw [h'] at heq
      cases heq
  | some p =>
      have h' : pOf (fun t => Parser.result t) g cs = some (as, rest) := by
        simpa [pOfLift] using h
      rw [h'] at heq
      exact heq.symm

/-- The `.seq (hd :: tl)` compound when BOTH parts succeed: the payloads
    concatenate and the rest threads through. -/
theorem pOfLift_seq_both_some (hd : Grammar) (tl : List Grammar) (inp : List Char)
    (as bs : List String) (mid rest : List Char)
    (hh : pOfLift hd inp = some (as, mid))
    (ht : pOfLift (.seq tl) mid = some (bs, rest)) :
    pOfLift (.seq (hd :: tl)) inp = some (as ++ bs, rest) := by
  unfold pOfLift pOf
  cases heq : pOf (fun t => Parser.result t) hd inp with
  | none =>
      have h' : pOf (fun t => Parser.result t) hd inp = some (as, mid) := by
        simpa [pOfLift] using hh
      rw [h'] at heq
      cases heq
  | some p =>
      have hpEq : p = (as, mid) := by
        have h' : pOf (fun t => Parser.result t) hd inp = some (as, mid) := by
          simpa [pOfLift] using hh
        rw [h'] at heq
        exact Option.some.inj heq.symm
      have hmid : p.snd = mid := by
        have h := congrArg Prod.snd hpEq
        simpa using h
      have ht' : pOf (fun t => Parser.result t) (.seq tl) p.snd = some (bs, rest) := by
        rw [hmid]
        simpa [pOfLift] using ht
      simp
      rw [ht']
      rw [hpEq]

/-- **The tok inversion law**: a literal token recognizes exactly its
    emission, from any continuation. -/
theorem invert_tok (s : String) (rest : List Char) :
    pOfLift (.tok s) (s.toList ++ rest) = some ([s], rest) := by
  unfold pOfLift pOf
  simp [expect_self, Parser.result]

/-! ## well-formedness (GWF) + the decide bridge -/

/-- First sets `a`, `b` are token-disjoint (no shared start char). -/
def Disjoint (a b : List Char) : Prop := ∀ c, c ∈ a → c ∉ b

/-- The Bool face of `Disjoint` (symmetric by construction — no a∈b
    ordering to get wrong). -/
def disjoint (a b : List Char) : Bool := b.all fun c => !(a.contains c)

/-- A list of first sets is pairwise-disjoint. -/
def PairwiseDisjoint : List (List Char) → Prop
  | [] => True
  | x :: xs => (∀ y ∈ xs, Disjoint x y) ∧ PairwiseDisjoint xs

/-- Pairwise-disjoint first sets, decidable. -/
def pairwiseDisjoint : List (List Char) → Bool
  | [] => true
  | x :: xs => xs.all (disjoint x) && pairwiseDisjoint xs

/-- GWF: every seq part and rep body makes progress (nonempty first set —
    the fuel rule), and every alt's branches start from pairwise-disjoint
    first sets (the unambiguous-choice rule). `.named` bodies are
    unchecked (deferred — the reference's WF is W-C2's fixpoint concern). -/
def GWF : Grammar → Prop
  | .tok _ => True
  | .scanTo _ => True
  | .seq gs => (∀ g ∈ gs, GWF g) ∧ (∀ g ∈ gs, firstSet g ≠ [])
  | .alt gs => (∀ g ∈ gs, GWF g) ∧ (∀ g ∈ gs, firstSet g ≠ []) ∧ PairwiseDisjoint (gs.map firstSet)
  | .rep g => GWF g ∧ firstSet g ≠ []
  | .named _ => True

/-- The GWF checker's nonempty face: ONE spelling for the guard (the
    `!`-on-Bool vs `decide`-elaboration differ textually — a single def
    keeps ALL bridge sites definitionally identical). -/
def nonemptyFS (g : Grammar) : Bool := !(firstSet g).isEmpty

/-- The nonempty bridge used by the GWF checker (the `g` must be applied
    before the projection — the un-applied name's type is a function). -/
theorem nonemptyFS_iff (g : Grammar) : nonemptyFS g = true ↔ firstSet g ≠ [] := by
  simp [nonemptyFS, List.isEmpty_eq_false_iff]

/-- The decidable face of GWF (inlined by-cases — same plain structural
    recursion as every other fold here). -/
def checkGWF : Grammar → Bool
  | .tok _ => true
  | .scanTo _ => true
  | .seq [] => true
  | .seq (g :: gs) =>
      checkGWF g && nonemptyFS g && checkGWF (.seq gs) && gs.all nonemptyFS
  | .alt [] => true
  | .alt (g :: gs) =>
      checkGWF g && nonemptyFS g && checkGWF (.alt gs)
        && gs.all nonemptyFS && pairwiseDisjoint ((g :: gs).map firstSet)
  | .rep g => checkGWF g && nonemptyFS g
  | .named _ => true

/-- The dispatch bridge: `disjoint` decides `Disjoint`. -/
theorem disjoint_iff (a b : List Char) : disjoint a b = true ↔ Disjoint a b := by
  unfold disjoint Disjoint
  constructor
  · intro h y hyinA hyinB
    have hb := (List.all_eq_true.mp h) y hyinB
    have hpos : List.contains a y = true := (List.contains_iff_mem (a := y) (as := a)).mpr hyinA
    rw [hpos] at hb
    exact False.elim (Bool.noConfusion hb)
  · intro h
    apply List.all_eq_true.mpr
    intro y hyinB
    have hn : ¬ List.contains a y = true := by
      intro hct
      have hyinA : y ∈ a := (List.contains_iff_mem (a := y) (as := a)).mp hct
      exact h y hyinA hyinB
    cases hb : List.contains a y with
    | false => simp [hb]
    | true => exact False.elim (hn hb)

/-- The pairwise dispatch bridge. -/
theorem pairwiseDisjoint_iff (xs : List (List Char)) :
    pairwiseDisjoint xs = true ↔ PairwiseDisjoint xs := by
  induction xs using List.rec with
  | nil => simp [pairwiseDisjoint, PairwiseDisjoint]
  | cons x xs ih =>
      unfold pairwiseDisjoint PairwiseDisjoint
      constructor
      · intro h
        have hb := (@Bool.and_eq_true_iff (xs.all (disjoint x)) (pairwiseDisjoint xs)).mp h
        constructor
        · intro y hy
          exact (disjoint_iff x y).mp (List.all_eq_true.mp hb.1 y hy)
        · exact ih.mp hb.2
      · intro h
        exact (@Bool.and_eq_true_iff (xs.all (disjoint x)) (pairwiseDisjoint xs)).mpr (by
          constructor
          · apply List.all_eq_true.mpr
            intro y hy
            exact (disjoint_iff x y).mpr (h.1 y hy)
          · exact ih.mpr h.2)

/-- The `&&`-chain assembler (the backward face of `Bool.and_eq_true`,
    named for use in the checker's reconstruction). -/
theorem and_eq_true_of {x y : Bool} (hx : x = true) (hy : y = true) : (x && y) = true := by
  simp [hx, hy]

/-- The GWF-of-a-SEQ conjunction, exposed (its `∧` components are not
    projectable through the `GWF` head — `simpa [GWF]` unwraps). -/
theorem GWF_seq_is_and (gs : List Grammar) (h : GWF (.seq gs)) :
    (∀ g ∈ gs, GWF g) ∧ (∀ g ∈ gs, firstSet g ≠ []) := by
  simpa [GWF] using h

/-- The GWF-of-an-ALT conjunction, exposed. -/
theorem GWF_alt_is_and (gs : List Grammar) (h : GWF (.alt gs)) :
    (∀ g ∈ gs, GWF g) ∧ (∀ g ∈ gs, firstSet g ≠ []) ∧ PairwiseDisjoint (gs.map firstSet) := by
  simpa [GWF] using h

/-- The GWF-of-a-REP conjunction, exposed. -/
theorem GWF_rep_is_and (g : Grammar) (h : GWF (.rep g)) :
    GWF g ∧ firstSet g ≠ [] := by
  simpa [GWF] using h

/-- The GWF-of-a-SEQ assembly, exposed (the backward direction of
    `GWF_seq_is_and`). -/
theorem GWF_seq_of_components (gs : List Grammar)
    (h : (∀ g ∈ gs, GWF g) ∧ (∀ g ∈ gs, firstSet g ≠ [])) : GWF (.seq gs) := by
  simpa [GWF] using h

/-- The GWF-of-an-ALT assembly, exposed. -/
theorem GWF_alt_of_components (gs : List Grammar)
    (h : (∀ g ∈ gs, GWF g) ∧ (∀ g ∈ gs, firstSet g ≠ []) ∧ PairwiseDisjoint (gs.map firstSet)) :
    GWF (.alt gs) := by
  simpa [GWF] using h

/-- The `checkGWF`/`GWF` bridge for one SEQ grammar, under member-wise
    bridge hypotheses (the list recursion `List.rec` — the `induction`
    tactic cannot split a list of nested-inductive elements). -/
theorem checkGWF_seq_iff (gs : List Grammar)
    (hih : ∀ g ∈ gs, checkGWF g = true ↔ GWF g) :
    checkGWF (.seq gs) = true ↔ GWF (.seq gs) := by
  induction gs using List.rec with
  | nil => simp [checkGWF, GWF]
  | cons g gs' ihs =>
      simp only [checkGWF, GWF]
      constructor
      · intro h
        rw [Bool.and_eq_true_iff] at h
        rcases h with ⟨h1, hall⟩
        rw [Bool.and_eq_true_iff] at h1
        rcases h1 with ⟨h2, hcgs⟩
        rw [Bool.and_eq_true_iff] at h2
        rcases h2 with ⟨hcg, hneg⟩
        have hgt : checkGWF (.seq gs') = true ↔ GWF (.seq gs') := ihs (fun x hx => hih x (by simp [hx]))
        have htG : GWF (.seq gs') := hgt.mp hcgs
        rcases GWF_seq_is_and gs' htG with ⟨hrG, hrN⟩
        constructor
        · intro x hx
          rw [List.mem_cons] at hx
          rcases hx with hxeq | hm
          · subst x
            exact (hih g (by simp)).mp hcg
          · exact hrG x hm
        · intro x hx
          rw [List.mem_cons] at hx
          rcases hx with hxeq | hm
          · subst x
            exact (by simpa [nonemptyFS, List.isEmpty_eq_false_iff] using hneg)
          · exact (by simpa [nonemptyFS, List.isEmpty_eq_false_iff] using (List.all_eq_true.mp hall) x hm)
      · intro h
        have hG : checkGWF g = true := (hih g (by simp)).mpr (h.1 g (by simp))
        have hN : nonemptyFS g = true := (nonemptyFS_iff g).mpr (h.2 g (by simp))
        have hS : checkGWF (.seq gs') = true := (ihs (fun x hx => hih x (by simp [hx]))).mpr
          (GWF_seq_of_components gs' (by
            constructor
            · intro x hx
              exact h.1 x (List.mem_cons_of_mem g hx)
            · intro x hx
              exact h.2 x (List.mem_cons_of_mem g hx)))
        have hA : gs'.all (fun x => nonemptyFS x) = true :=
          List.all_eq_true.mpr (fun x hx => (nonemptyFS_iff x).mpr (h.2 x (List.mem_cons_of_mem g hx)))
        exact and_eq_true_of (and_eq_true_of (and_eq_true_of hG hN) hS) hA

/-- The `checkGWF`/`GWF` bridge for one ALT grammar, under member-wise
    bridge hypotheses. -/
theorem checkGWF_alt_iff (gs : List Grammar)
    (hih : ∀ g ∈ gs, checkGWF g = true ↔ GWF g) :
    checkGWF (.alt gs) = true ↔ GWF (.alt gs) := by
  induction gs using List.rec with
  | nil => simp [checkGWF, GWF, PairwiseDisjoint]
  | cons g gs' ihs =>
      simp only [checkGWF, GWF]
      constructor
      · intro h
        rw [Bool.and_eq_true_iff] at h
        rcases h with ⟨h1, hpair⟩
        rw [Bool.and_eq_true_iff] at h1
        rcases h1 with ⟨h2, hall⟩
        rw [Bool.and_eq_true_iff] at h2
        rcases h2 with ⟨h3, hcga⟩
        rw [Bool.and_eq_true_iff] at h3
        rcases h3 with ⟨hcg, hneg⟩
        have hgt : checkGWF (.alt gs') = true ↔ GWF (.alt gs') := ihs (fun x hx => hih x (by simp [hx]))
        have htG : GWF (.alt gs') := hgt.mp hcga
        rcases GWF_alt_is_and gs' htG with ⟨hrG, hrN, _⟩
        constructor
        · intro x hx
          rw [List.mem_cons] at hx
          rcases hx with hxeq | hm
          · subst x
            exact (hih g (by simp)).mp hcg
          · exact hrG x hm
        · constructor
          · intro x hx
            rw [List.mem_cons] at hx
            rcases hx with hxeq | hm
            · subst x
              exact (by simpa [nonemptyFS, List.isEmpty_eq_false_iff] using hneg)
            · exact (by simpa [nonemptyFS, List.isEmpty_eq_false_iff] using (List.all_eq_true.mp hall) x hm)
          · exact (pairwiseDisjoint_iff ((g :: gs').map firstSet)).mp hpair
      · intro h
        have hG : checkGWF g = true := (hih g (by simp)).mpr (h.1 g (by simp))
        have hN : nonemptyFS g = true := (nonemptyFS_iff g).mpr (h.2.1 g (by simp))
        have hS : checkGWF (.alt gs') = true := (ihs (fun x hx => hih x (by simp [hx]))).mpr
          (GWF_alt_of_components gs' (by
            constructor
            · intro x hx
              exact h.1 x (List.mem_cons_of_mem g hx)
            · constructor
              · intro x hx
                exact h.2.1 x (List.mem_cons_of_mem g hx)
              · exact h.2.2.2))
        have hA : gs'.all (fun x => nonemptyFS x) = true :=
          List.all_eq_true.mpr (fun x hx => (nonemptyFS_iff x).mpr (h.2.1 x (List.mem_cons_of_mem g hx)))
        have hP : pairwiseDisjoint ((g :: gs').map firstSet) = true :=
          (pairwiseDisjoint_iff ((g :: gs').map firstSet)).mpr h.2.2
        exact and_eq_true_of (and_eq_true_of (and_eq_true_of (and_eq_true_of hG hN) hS) hA) hP

/-- **GWF is decided by `checkGWF`** (the deliverable's bridge; the Prop
    and the Bool share the same list operations, so the proof is a
    structural, per-part dispatch — via the grammar's generated mutual
    recursor). -/
theorem checkGWF_eq_true_iff_GWF (g : Grammar) : checkGWF g = true ↔ GWF g := by
  let m₂ : List Grammar → Prop := fun gs => ∀ g ∈ gs, checkGWF g = true ↔ GWF g
  change (checkGWF g = true ↔ GWF g)
  refine Grammar.rec (motive_1 := fun g => checkGWF g = true ↔ GWF g) (motive_2 := m₂)
    ?h_tok ?h_scan ?h_seq ?h_alt ?h_rep ?h_named ?h_nil ?h_cons g
  · intro s
    simp [checkGWF, GWF]
  · intro q
    simp [checkGWF, GWF]
  · intro gs hgs
    exact checkGWF_seq_iff gs hgs
  · intro gs hgs
    exact checkGWF_alt_iff gs hgs
  · intro g hrec
    simp only [checkGWF, GWF]
    constructor
    · intro h
      rw [Bool.and_eq_true_iff] at h
      rcases h with ⟨hcg, hne⟩
      constructor
      · exact hrec.mp hcg
      · exact (by simpa [nonemptyFS, List.isEmpty_eq_false_iff] using hne)
    · intro h
      exact and_eq_true_of (hrec.mpr h.1) ((by simpa [nonemptyFS, List.isEmpty_eq_false_iff] using h.2))
  · intro nm
    simp [checkGWF, GWF]
  · intro g hg
    simp at hg
  · intro g gs hgclaim ih h' hh'
    rw [List.mem_cons] at hh'
    rcases hh' with hbeq | hm
    · subst h'
      exact hgclaim
    · exact ih h' hm

/-! ## the inversion fragment + laws

The recognition-only fragment: `Core` = the deterministic non-repeating
grammars (tok/seq/alt — inverting from ANY continuation); the fragment
adds one rep of a Core body (whose tail must start outside its body's
first set — the `hsep` conditions). `named` deferred. -/

/-- The deterministic fragment: no `rep`/`scanTo`/`named` — recognition
    consumes exactly the emission, from any continuation. -/
inductive Core : Grammar → Prop where
  | tok (s : String) : Core (.tok s)
  | seq (gs : List Grammar) : (∀ g ∈ gs, Core g) → Core (.seq gs)
  | alt (g : Grammar) (gs : List Grammar) : Core g → (∀ h ∈ gs, Core h) → Core (.alt (g :: gs))

/-- A member of a tail of a first-set union is a member of the whole
    union (the `++`-shape of `firstSet (.alt gs)`/'`firstSet (.seq gs)`). -/
theorem mem_firstSet_tail (bs : List Grammar) (g : Grammar) (h : g ∈ bs) (c : Char)
    (hc : c ∈ firstSet g) : c ∈ firstSet (.alt bs) := by
  induction bs using List.rec with
  | nil => simp at h
  | cons b bs' ih =>
      rw [List.mem_cons] at h
      rcases h with hbeq | hm
      · subst g
        rw [firstSet]
        exact List.mem_append_left (firstSet (.alt bs')) hc
      · rw [firstSet]
        exact List.mem_append_right (firstSet b) (ih hm)

/-- A GWF grammar with nonempty first set emits a nonempty string (the
    fuel rule's payload side: a rep body consumes). Proved via the
    grammar's generated mutual recursor (`Grammar.rec` — the `induction`
    tactic cannot split a nested inductive; the list motive `m₂` gives the
    per-member claims). -/
theorem emit_ne_empty (g : Grammar) (hg : GWF g) (hne : firstSet g ≠ []) : emit g ≠ "" := by
  let m₂ : List Grammar → Prop := fun gs => ∀ g ∈ gs, GWF g → firstSet g ≠ [] → emit g ≠ ""
  refine Grammar.rec (motive_1 := fun g => GWF g → firstSet g ≠ [] → emit g ≠ "") (motive_2 := m₂)
    ?h_tok ?h_scan ?h_seq ?h_alt ?h_rep ?h_named ?h_nil ?h_cons g hg hne
  · intro s hg hne h0
    have hs0 : s = "" := by simpa [emit] using h0
    apply hne
    simp [firstSet, hs0]
  · intro q hg hne
    simp [firstSet] at hne
  · intro gs hgs hg hne
    cases gs with
    | nil => simp [firstSet] at hne
    | cons g gs' =>
        rcases GWF_seq_is_and (g :: gs') hg with ⟨hgwf, hneAll⟩
        have hg1 : GWF g := hgwf g (by simp)
        have hg2 : firstSet g ≠ [] := hneAll g (by simp)
        have hem : emit g ≠ "" := hgs g (by simp) hg1 hg2
        intro h0
        apply hem
        have ht := congrArg String.toList h0
        rw [emit, String.toList_append] at ht
        have hlead := (List.append_eq_nil_iff.mp ht).1
        have hem2 : emit g = "" := String.toList_inj.mp (by simpa using hlead)
        exact hem2
  · intro gs hgs hg hne
    cases gs with
    | nil => simp [firstSet] at hne
    | cons g gs' =>
        rcases GWF_alt_is_and (g :: gs') hg with ⟨hgwf, hneAll, _⟩
        have hg1 : GWF g := hgwf g (by simp)
        have hg2 : firstSet g ≠ [] := hneAll g (by simp)
        have hem : emit g ≠ "" := hgs g (by simp) hg1 hg2
        intro h0
        exact hem (by simpa [emit] using h0)
  · intro g hrec hg hne
    rcases GWF_rep_is_and g hg with ⟨hgwf, hneAll⟩
    have hg2 : firstSet g ≠ [] := by simpa [firstSet] using hneAll
    have hem : emit g ≠ "" := hrec hgwf hg2
    intro h0
    exact hem (by simpa [emit] using h0)
  · intro nm hg hne
    simp [firstSet] at hne
  · intro g hg
    simp at hg
  · intro g gs hgclaim ih g' hg'
    rw [List.mem_cons] at hg'
    rcases hg' with hbeq | hm
    · subst g'
      exact hgclaim
    · exact ih g' hm

/-- A Core grammar cannot match from an empty input (it must consume). -/
theorem fail_fast_empty (g : Grammar) (hc : Core g) (hg : GWF g) (hne : firstSet g ≠ []) :
    pOfLift g [] = none := by
  induction hc with
  | tok s =>
      have hs : s ≠ "" := by intro h0; apply hne; simp [firstSet, h0]
      unfold pOfLift pOf
      have hbay : s.toList.isPrefixOf [] = false := by
        cases hp : s.toList.isPrefixOf [] with
        | false => rfl
        | true =>
            have hpre := List.isPrefixOf_iff_prefix.mp hp
            rcases hpre with ⟨r, hr⟩
            have htl : s.toList = [] := (List.append_eq_nil_iff.mp hr).1
            have hs' : s = "" := String.toList_inj.mp (by simpa using htl)
            exact False.elim (hs hs')
      simp [pOf, expect, startsWith, hbay]
  | seq gs _ ihn =>
      cases gs with
      | nil => simp [firstSet] at hne
      | cons hd tl =>
          rcases GWF_seq_is_and (hd :: tl) hg with ⟨hgwf, hneAll⟩
          have hhdG : GWF hd := hgwf hd (by simp)
          have hhdN : firstSet hd ≠ [] := hneAll hd (by simp)
          have hhdF : pOfLift hd [] = none := ihn hd (by simp) hhdG hhdN
          exact pOfLift_seq_head_none hd tl [] hhdF
  | alt g gs _ _ ihn ihmgs =>
      have all_h (hb : Grammar) (hh : hb ∈ g :: gs) : pOfLift hb [] = none := by
        rw [List.mem_cons] at hh
        rcases hh with hbeq | hm
        · subst hb
          rcases GWF_alt_is_and (g :: gs) hg with ⟨hgwf, hneAll, _⟩
          have hgG : GWF g := hgwf g (by simp)
          have hgN : firstSet g ≠ [] := hneAll g (by simp)
          exact ihn hgG hgN
        · rcases GWF_alt_is_and (g :: gs) hg with ⟨hgwf, hneAll, _⟩
          have hhG : GWF hb := hgwf hb (List.mem_cons_of_mem g hm)
          have hhN : firstSet hb ≠ [] := hneAll hb (List.mem_cons_of_mem g hm)
          exact ihmgs hb hm hhG hhN
      have halt (gs' : List Grammar) (hgs' : ∀ h ∈ gs', h ∈ g :: gs) :
          pOfLift (.alt gs') [] = none := by
        induction gs' using List.rec with
        | nil => unfold pOfLift pOf; simp
        | cons h hs ihs =>
            have hhF : pOfLift h [] = none := all_h h (hgs' h (by simp))
            have hhsF : pOfLift (.alt hs) [] = none := ihs (fun h' hh' => hgs' h' (by simp [hh']))
            exact pOfLift_alt_head_none h hs [] hhF hhsF
      exact halt (g :: gs) (by intro h hh; exact hh)

/-- A Core grammar cannot match text whose head lies outside its first
    set (the alt/seq-union direction of first-set reasoning). -/
theorem fail_fast (g : Grammar) (cs : List Char)
    (hc : Core g) (hg : GWF g) (hne : firstSet g ≠ [])
    (hhead : cs = [] ∨ ∃ c cs', cs = c :: cs' ∧ ¬ c ∈ firstSet g) :
    pOfLift g cs = none := by
  cases hhead with
  | inl hc0 =>
      subst cs
      exact fail_fast_empty g hc hg hne
  | inr hcs =>
      rcases hcs with ⟨c, cs', hcs, hnc⟩
      subst cs
      induction hc with
      | tok s =>
          have hs : s ≠ "" := by intro h0; apply hne; simp [firstSet, h0]
          unfold pOfLift pOf
          have hbay : s.toList.isPrefixOf (c :: cs') = false := by
            cases hp : s.toList.isPrefixOf (c :: cs') with
            | false => rfl
            | true =>
                rcases (List.isPrefixOf_iff_prefix.mp hp) with ⟨r, hr⟩
                cases htl : s.toList with
                | nil =>
                    have hs0 : s = "" := String.toList_inj.mp (by simpa using htl)
                    exact False.elim (hs hs0)
                | cons hd tl =>
                    have hcEq : hd = c := by
                      simp [htl] at hr
                      exact hr.1
                    have hin : c ∈ s.toList.take 1 := by
                      rw [htl, hcEq]
                      simp
                    exact False.elim (hnc (by simpa [firstSet] using hin))
          simp [pOf, expect, startsWith, hbay]
      | seq gs _ ihn =>
          cases gs with
          | nil => simp [firstSet] at hne
          | cons hd tl =>
              rcases GWF_seq_is_and (hd :: tl) hg with ⟨hgwf, hneAll⟩
              have hhdG : GWF hd := hgwf hd (by simp)
              have hhdN : firstSet hd ≠ [] := hneAll hd (by simp)
              have hhdH : ¬ c ∈ firstSet hd := by
                intro hc0
                apply hnc
                rw [firstSet]
                exact List.mem_append_left (firstSet (.seq tl)) hc0
              have hhdF : pOfLift hd (c :: cs') = none := ihn hd (by simp) hhdG hhdN hhdH
              exact pOfLift_seq_head_none hd tl (c :: cs') hhdF
      | alt g gs _ _ ihn ihmgs =>
          have all_h (hb : Grammar) (hh : hb ∈ g :: gs) : pOfLift hb (c :: cs') = none := by
            rw [List.mem_cons] at hh
            rcases hh with hbeq | hm
            · subst hb
              rcases GWF_alt_is_and (g :: gs) hg with ⟨hgwf, hneAll, _⟩
              have hgG : GWF g := hgwf g (by simp)
              have hgN : firstSet g ≠ [] := hneAll g (by simp)
              have hgH : ¬ c ∈ firstSet g := by
                intro hc0
                apply hnc
                rw [firstSet]
                exact List.mem_append_left (firstSet (.alt gs)) hc0
              exact ihn hgG hgN hgH
            · rcases GWF_alt_is_and (g :: gs) hg with ⟨hgwf, hneAll, _⟩
              have hhG : GWF hb := hgwf hb (List.mem_cons_of_mem g hm)
              have hhN : firstSet hb ≠ [] := hneAll hb (List.mem_cons_of_mem g hm)
              have hhH : ¬ c ∈ firstSet hb := by
                intro hc0
                apply hnc
                rw [firstSet]
                exact List.mem_append_right (firstSet g) (mem_firstSet_tail gs hb hm c hc0)
              exact ihmgs hb hm hhG hhN hhH
          have halt (gs' : List Grammar) (hgs' : ∀ h ∈ gs', h ∈ g :: gs) :
              pOfLift (.alt gs') (c :: cs') = none := by
            induction gs' using List.rec with
            | nil => unfold pOfLift pOf; simp
            | cons h hs ihs =>
                have hhF : pOfLift h (c :: cs') = none := all_h h (hgs' h (by simp))
                have hhsF : pOfLift (.alt hs) (c :: cs') = none :=
                  ihs (fun h' hh' => hgs' h' (by simp [hh']))
                exact pOfLift_alt_head_none h hs (c :: cs') hhF hhsF
          exact halt (g :: gs) (by intro h hh; exact hh)

/-- **The Core inversion law**: a GWF Core grammar recognizes exactly its
    emission, from ANY continuation (tok/seq/alt — the deterministic
    fragment). -/
theorem invert_core : ∀ (g : Grammar) (rest : List Char), Core g → GWF g →
    pOfLift g ((emit g).toList ++ rest) = some (tokensOf g, rest) := by
  intro g rest hc
  induction hc generalizing rest with
  | tok s =>
      intro hg
      simpa [emit, tokensOf] using invert_tok s rest
  | seq gs hparts ih =>
      intro hg
      induction gs using List.rec with
      | nil =>
          unfold pOfLift pOf
          simp [emit, tokensOf]
      | cons h hs ihs =>
          rcases GWF_seq_is_and (h :: hs) hg with ⟨hgwf, hneAll⟩
          have hhG : GWF h := hgwf h (by simp)
          have htG : GWF (.seq hs) := GWF_seq_of_components hs (by
            constructor
            · intro g hg'; exact hgwf g (List.mem_cons_of_mem h hg')
            · intro g hg'; exact hneAll g (List.mem_cons_of_mem h hg'))
          have hhI : pOfLift h ((emit h).toList ++ ((emit (.seq hs)).toList ++ rest)) =
              some (tokensOf h, (emit (.seq hs)).toList ++ rest) := by
            simpa [List.append_assoc] using ih h (by simp) ((emit (.seq hs)).toList ++ rest) hhG
          have htI : pOfLift (.seq hs) ((emit (.seq hs)).toList ++ rest) =
              some (tokensOf (.seq hs), rest) :=
            ihs (fun g hg'' => hparts g (List.mem_cons_of_mem h hg''))
              (fun g hg'' r hgwf2 => ih g (List.mem_cons_of_mem h hg'') r hgwf2) htG
          have hIn : pOfLift (.seq (h :: hs)) ((emit (.seq (h :: hs))).toList ++ rest) =
              some (tokensOf (.seq (h :: hs)), rest) := by
            simpa [emit, tokensOf, List.append_assoc, String.toList_append] using
              (pOfLift_seq_both_some h hs ((emit (.seq (h :: hs))).toList ++ rest)
                (tokensOf h) (tokensOf (.seq hs)) ((emit (.seq hs)).toList ++ rest) rest
                (by simpa [emit, tokensOf, List.append_assoc, String.toList_append] using hhI)
                htI)
          exact hIn
  | alt g gs hcg hcgs ihm ihmgs =>
      intro hg
      rcases GWF_alt_is_and (g :: gs) hg with ⟨hgwf, hneAll, _⟩
      have hgG : GWF g := hgwf g (by simp)
      have hgI : pOfLift g ((emit g).toList ++ rest) = some (tokensOf g, rest) :=
        ihm rest hgG
      have hgIn : pOfLift (.alt (g :: gs)) ((emit (.alt (g :: gs))).toList ++ rest) =
          some (tokensOf (.alt (g :: gs)), rest) := by
        simpa [emit, tokensOf] using
          (pOfLift_alt_head_some g gs ((emit (.alt (g :: gs))).toList ++ rest)
            (tokensOf g) rest (by simpa [emit, tokensOf] using hgI))
      exact hgIn

/-- **The rep inversion law**: a repetition of a Core body recognizes one
    iteration of its emission, provided the trailing text starts outside
    the body's first set (the `hsep` condition). -/
theorem invert_rep (g : Grammar) (rest : List Char)
    (hc : Core g) (hg : GWF g) (hne : firstSet g ≠ [])
    (hsep : rest = [] ∨ ∃ c cs', rest = c :: cs' ∧ ¬ c ∈ firstSet g) :
    pOfLift (.rep g) ((emit g).toList ++ rest) = some (tokensOf g, rest) := by
  have hstep : pOfLift g ((emit g).toList ++ rest) = some (tokensOf g, rest) :=
    invert_core g rest hc hg
  have hstop : pOfLift g rest = none := fail_fast g rest hc hg hne hsep
  have hneEmit : (emit g).toList ≠ [] := by
    have he : emit g ≠ "" := emit_ne_empty g hg hne
    intro h0
    apply he
    exact String.toList_inj.mp (by simpa using h0)
  have hlen : ((emit g).toList ++ rest).length > 0 := by
    cases htl : (emit g).toList with
    | nil => exact False.elim (hneEmit htl)
    | cons c cs' =>
        simp [List.length_cons]
  unfold pOfLift pOf
  cases hlen0 : ((emit g).toList ++ rest).length with
  | zero => omega
  | succ n =>
      rw [repAux_some (fuel := n) (acc := []) (bs := tokensOf g)
        (cs := (emit g).toList ++ rest) (rest := rest)]
      · rw [List.nil_append]
        cases n with
        | zero => simp [repAux]
        | succ m =>
            change repAux (pOfLift g) (m + 1) (tokensOf g) rest = some (tokensOf g, rest)
            rw [repAux_none (fuel := m) (acc := tokensOf g) (cs := rest) (h := hstop)]
      · exact hstep
      · intro hc
        have hl := congrArg List.length hc
        have hlt : ((emit g).toList ++ rest).length = rest.length := hl.symm
        rw [List.length_append] at hlt
        have hl0 : (emit g).toList.length = 0 := by omega
        exact hneEmit (List.eq_nil_of_length_eq_zero hl0)

/-- **The rep-behind-token law** (the deliverable's practical shape): a
    token followed by a repetition recognizes the compound emission. -/
theorem invert_rep_behind_tok (t : String) (b : Grammar) (rest : List Char)
    (hc : Core b) (hg : GWF b) (hne : firstSet b ≠ [])
    (hsep : rest = [] ∨ ∃ c cs', rest = c :: cs' ∧ ¬ c ∈ firstSet b) :
    pOfLift (.seq [.tok t, .rep b]) ((t ++ emit b).toList ++ rest) =
      some ([t] ++ tokensOf b, rest) := by
  have htI : pOfLift (.tok t) (t.toList ++ ((emit b).toList ++ rest)) =
      some ([t], (emit b).toList ++ rest) :=
    invert_tok t ((emit b).toList ++ rest)
  have hbI : pOfLift (.seq [.rep b]) ((emit b).toList ++ rest) =
      some (tokensOf b, rest) := by
    have hbI0 : pOfLift (.rep b) ((emit b).toList ++ rest) = some (tokensOf b, rest) :=
      invert_rep b rest hc hg hne hsep
    have hnil : pOfLift (.seq []) rest = some ([], rest) := by
      unfold pOfLift pOf
      rfl
    have hbI' : pOfLift (.seq [.rep b]) ((emit b).toList ++ rest) =
        some (tokensOf b ++ [], rest) :=
      pOfLift_seq_both_some (.rep b) [] ((emit b).toList ++ rest)
        (tokensOf b) [] rest rest hbI0 hnil
    simpa using hbI'
  apply pOfLift_seq_both_some (.tok t) [.rep b] ((t ++ emit b).toList ++ rest)
    [t] (tokensOf b) ((emit b).toList ++ rest) rest
  · simpa [List.append_assoc, String.toList_append] using htI
  · exact hbI

/-! ## the deferrals -/

/-- `.named` is a NAMED REFERENCE, not a function: a production whose body
    lives in the consumer's fixpoint. This module defers it — recognition
    fails, the emission is empty, GWF is lenient — because the inversion
    law for a reference needs the fixpoint machinery (the W-C2 consumer
    wave). The token-fragment theorems above exclude it by construction
    (`Core` never mentions `.named`). -/
theorem rec_deferred (n : String) (cs : List Char) : pOfLift (.named n) cs = none := by
  unfold pOfLift pOf
  rfl

end Grammar

end TextKit

end -- @[expose] public section
