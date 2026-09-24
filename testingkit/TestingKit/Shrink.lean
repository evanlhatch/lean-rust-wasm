/-
# TestingKit.Shrink — the shrinking discipline as DATA + mechanics

Owned by: the TestingKit agent (the mandate tree, `testingkit/`).
Driving decisions: notes/v3/08-capabilities.md §11 (failing sweeps report
the minimal counterexample + the shrink path; VALIDITY-PRESERVING
shrinkers for refined types — shrinking `Packet.length` without `bytes`
is malformed, not smaller) + notes/v3/15-patterns.md #14 (the LCG
discipline: shrinking walks the VALUE, not the tape) + the
validity-preserving review content: a shrinker must preserve the type's
invariants, and validity / coverage / distribution / minimality are four
separate claims — proving the first does not imply the rest. THIS seed
pins validity + minimality (as pinned tests, never as a type claim it
cannot carry); coverage + distribution stay the LCG generator's concern
(Shrink.lean does not touch the tape's draw distribution).

Mined from: nothing in legacy/ had a shrinker — this is fresh, the
honest minimal seed for §11.

THE TWO HONEST CHOICES (stated once, here):

1. TERMINATION — the measured form, not fuel. A raw shrinker
   (`Shrinker α := α → List α`) is just mechanics; the loop over it is
   total ONLY if each candidate is provably strictly smaller. So the
   disciplined shrinker `ShrinkerV` carries `measure : α → Nat` and the
   proof `smaller : c ∈ shrink a → measure c < measure a`, and
   `shrinkTrail` recurses well-foundedly on the measure. No fuel, no
   "may diverge" asterisk: totality is proved, per shrinker, at
   construction. (A fuel variant would be honest too, but the measure
   is strictly stronger and costs one field.)

2. MINIMALITY — local, never claimed in the type. `shrinkTrail` is
   greedy descent (the FIRST failing candidate wins). Its last element
   is the minimal failing value found; for monotone predicates it is
   the global minimum (pinned in the tests), for arbitrary predicates
   only locally minimal. Minimality is a property of the
   (shrinker, predicate) PAIR — it is pinned by tests, never baked into
   a type that could not carry it honestly.

VALIDITY — in the type, where honest. `ShrinkerV {α} (P : α → Prop)`
carries `valid : ∀ a c, c ∈ shrink a → P c`: a shrinker FOR a refined
type must keep every candidate inside the refined space. The
Packet.length/bytes lesson is structural: the coupled shrinker
(`shrinkerDpair`) re-derives the dependent component from the candidate
first — the coupling is taken explicitly, and there is NO field-wise
composition combinator to misuse (shrinking one field without the other
is malformed, not smaller; the tests pin the naive field-wise shrinker
producing invalid candidates as the refused anti-pattern).

The four-way distinction (the review's teeth), one line each:
- validity: a candidate satisfies the refined type's invariant —
  ENFORCED here (`ShrinkerV.valid`).
- minimality: the final candidate is the smallest failing one — PINNED
  here for monotone predicates + the worked examples.
- coverage: the failing space is reachable at all — the GENERATOR's
  (Lcg + the Spec author's draw), not the shrinker's.
- distribution: the drawn cases spread over the failing space — also
  the generator's; a shrinker only ever narrows.

The five questions (notes/v3/01-core.md):
- root: none — the discipline layer's shrink shape over checkable
  properties.
- carrier grade: the ShrinkerV STRUCTURE — measure + smaller + valid as
  proof-carrying fields; an undisciplined shrinker is still expressible
  (raw `Shrinker`) but cannot ride the loop.
- spine reading: none — the evidence discipline's substrate.
- ladder rung: rung 1 + one rung-4 proof — structural defs; the removals
  size lemma is one structural induction; the loop's termination is the
  WF recursion the `smaller` field discharges.
- gate row: none — TestingKit is outside Gates.Packages' gated set;
  TestingKitTests self-tests the discipline.
-/

module

public import TestingKit.Lcg

@[expose] public section

namespace TestingKit

/-! ## The raw shape + the disciplined structure -/

/-- The raw shrinker shape: mechanics only — candidates per step.
    The discipline (totality, validity) lives in `ShrinkerV`, which is
    what the loop consumes; a bare `Shrinker` rides nothing. -/
abbrev Shrinker (α : Type) := α → List α

/-- The disciplined shrinker for `α` refined by `P`: the candidate list
    is finite per step (a function into `List`), every candidate is
    PROVABLY strictly smaller (the loop's termination discipline), and
    every candidate stays VALID (`P` — the refined type's invariant).
    The unrefined case instantiates `P := fun _ => True`. -/
structure ShrinkerV {α : Type} (P : α → Prop) where
  /-- The per-step candidate list (finite by construction). -/
  shrink : Shrinker α
  /-- The size measure the loop descends on. -/
  measure : α → Nat
  /-- Totality's proof obligation: every candidate is strictly smaller. -/
  smaller : ∀ (a c : α), c ∈ shrink a → measure c < measure a
  /-- Validity's proof obligation: every candidate satisfies `P` —
      the Packet.length/bytes lesson, in the type. -/
  valid : ∀ (a c : α), c ∈ shrink a → P c

/-! ## The greedy descent loop -/

/-- Walk `a`'s candidate list; the FIRST failing candidate triggers
    `descent`, which receives the candidate AND the proof it came from
    `keep` — the hook the measured loop uses to discharge its
    termination obligation (the skipped candidates are never revisited:
    greedy). Structural on the list — total. -/
def trailStep (fails : α → Bool) (a : α) (keep : List α) :
    (cs : List α) → (∀ c ∈ cs, c ∈ keep) → ((c : α) → c ∈ keep → List α) → List α
  | [], _, _ => [a]
  | c :: cs, hmem, descent =>
      if fails c then descent c (hmem c (List.Mem.head cs))
      else trailStep fails a keep cs (fun d hd => hmem d (List.Mem.tail c hd)) descent

/-- The greedy shrink trail: `a` followed by the trail of the first
    failing candidate. Total by well-founded recursion on `measure` —
    the descent's candidate is provably strictly smaller (`smaller`).
    The trail's LAST element is the minimal failing value found
    (globally minimal for monotone predicates — pinned in the tests;
    locally minimal otherwise, the honest choice stated in the header). -/
def shrinkTrail {α : Type} {P : α → Prop} (w : ShrinkerV P) (fails : α → Bool) : (a : α) → List α
  | a =>
    trailStep fails a (w.shrink a) (w.shrink a) (fun _ h => h)
      (fun c _hc => a :: shrinkTrail w fails c)
termination_by a => w.measure a
decreasing_by exact w.smaller a c (by assumption)

/-- The shrink loop: the minimal failing value found by greedy descent
    from `a` (the trail's last element; `a` itself if nothing smaller
    fails). -/
def shrinkLoop {α : Type} {P : α → Prop} (w : ShrinkerV P) (fails : α → Bool) (a : α) : α :=
  (shrinkTrail w fails a).getLast?.getD a

/-! ## The dependent-pair combinator (the coupling taken explicitly) -/

/-- The dependent pair's shrinker: candidates shrink the FIRST component
    via `wA` and RE-DERIVE the second by `bOf` — jointly, or not at all.
    There is deliberately no field-wise composition: shrinking the
    second component without re-deriving it against the first is the
    malformed-candidate anti-pattern (§11's Packet.length/bytes). The
    coupling `C` is carried explicitly and `hC` proves `bOf` maintains
    it, so `valid` discharges by construction. -/
def shrinkerDpair {α : Type} {β : α → Type} (C : (a : α) → β a → Prop)
    (wA : ShrinkerV (α := α) (fun _ => True)) (bOf : (a : α) → β a)
    (hC : ∀ a, C a (bOf a)) : ShrinkerV (α := Sigma β) (fun p => C p.1 p.2) where
  shrink p := (wA.shrink p.1).map (fun a' => Sigma.mk a' (bOf a'))
  measure p := wA.measure p.1
  smaller p q hq := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact wA.smaller p.1 a ha
  valid p q hq := by
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hq
    exact hC a

/-! ## The seed instances -/

/-- Removals: every list with one element struck out (in order).
    The list shrinker's candidate family. -/
def removals : List α → List (List α)
  | [] => []
  | x :: xs => xs :: (removals xs).map (fun r => x :: r)

/-- Removals strictly shorten: the list shrinker's `smaller` proof
    (one structural induction — rung 4). -/
theorem removals_lt : ∀ (xs : List α) (r : List α), r ∈ removals xs → r.length < xs.length
  | [], r, h => absurd h (by simp [removals])
  | x :: xs, r, h => by
      simp only [removals, List.mem_cons] at h
      rcases h with h1 | h'
      · subst h1
        exact Nat.lt_succ_self _
      · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp h'
        exact Nat.succ_lt_succ (removals_lt xs r' hr')

/-- The unrefined Nat shrinker: candidates `0..n-1` (the whole strictly
    smaller prefix — greedy over it finds the global minimum for
    monotone predicates), measure = id, validity trivial. -/
def shrinkNat : ShrinkerV (α := Nat) (fun _ => True) where
  shrink n := List.range n
  measure n := n
  smaller _ _c hc := List.mem_range.mp hc
  valid := fun _ _ _ => trivial

/-- The unrefined List shrinker: single-element removals, measure =
    length, validity trivial. -/
def shrinkList : ShrinkerV (α := List α) (fun _ => True) where
  shrink xs := removals xs
  measure xs := xs.length
  smaller _ _r hr := removals_lt _ _ hr
  valid := fun _ _ _ => trivial

/-- The worked refined-type example: a byte-like bound. The refined type
    `Bounded bound` carries the invariant IN the type, so the shrinker
    must re-prove it per candidate — `valid` is trivial exactly because
    the construction cannot produce an out-of-bound candidate without
    failing to elaborate. -/
abbrev Bounded (bound : Nat) := {n : Nat // n ≤ bound}

/-- The validity-preserving shrinker for `Bounded bound`: candidates
    shrink the witness downward; each candidate re-wraps with the proof
    `c < v.val ≤ bound`. -/
def shrinkBounded (bound : Nat) : ShrinkerV (α := Bounded bound) (fun _ => True) where
  shrink v :=
    (List.range v.val).attach.map
      (fun c => ⟨c.val, Nat.le_trans (Nat.le_of_lt (List.mem_range.mp c.property)) v.property⟩)
  measure v := v.val
  smaller _ q hq := by
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
    exact List.mem_range.mp c.property
  valid := fun _ _ _ => trivial

end TestingKit
