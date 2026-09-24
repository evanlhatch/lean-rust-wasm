/-
# ZSet.Graph — the graph-reading layer over the weighted relation

Owned by: the ZSet agent (the mandate tree, `zset/`).

The five questions (notes/v3/01-core.md):
- **Root**: Universe × Change crossing — the data plane's ONE relation
  semantics read as a DIRECTED GRAPH (02 §4 + 01 §1): a graph IS a
  weighted relation over `V × V`; reachability is the closure (the
  bounded path-folding of the relational composition); a DAG is the
  acyclicity predicate; a topological order is the strata.
- **Carrier grade**: none of its own — `Graph K V` is an ABBREV for
  `Weighted K (V × V)` (the READING, not a new type): every `Weighted`
  law and operator applies definitionally. No new rep, no new canon.
- **Spine reading**: none — the graph vocabulary is theorems-over-the-
  relation, consumed by the lanes' graph-shaped reads.
- **Ladder rung**: rung 6 hand theorems for the bridges
  (`Edge.succs_mem`/`succs_of_Edge`, the walk-soundness chain) + the
  decided checkers (`isEdge`, `cycle?`, `peel`) as the decidable
  shadows of the Prop statements (01 §4's statement shape).
- **Gate rows**: the axiom report (pinned in ZSetTests.Axioms) +
  ZSetTests' graph suite (the diamond's closure pinned, the
  acyclicity check's both faces, the mandatory negative controls).

## The known consumers (the shape's demand list — each a future citation)

- the ledger's demand graphs (dependency closure over obligations);
- the import/cone graph (LintKit.Cone's table + the transitivity
  follow-up is a graph read);
- the machines' transition graphs (01 §3's per-execution causal
  posets — the happens-before DAG);
- the schema reference graph (the schema lanes' reference closure).

The layer's shape serves all four: edges as nonzero-weight pairs, the
adjacency reading off the support, the closure as the bounded
path-folding, acyclicity with the cycle REFUSED AS DATA, the strata
peel.

## The cone call + the honest boundaries (named, not hidden)

- The Datalog closure (02 §9's LFP engine) is CONE-LEGAL here (ZSet
  and Datalog are both C1 in LintKit.Cone's table) — this layer keeps
  the local bounded path-folding instead, so the delta substrate stays
  self-contained; the Datalog-LFP bridge for `Reach` is the named
  follow-up.
- `reachFrom` is SOUND against `Reach` (`reachFrom_sound`); the
  CONVERSE (a `Reach` path needs no more than the |support| fuel — the
  simple-path shortcut) is the named follow-up, so `reachFrom`'s fuel
  is a completeness premise, never a claimed verdict.
- `cycle? g N = some c` PROVES a cycle, with `c` the closed walk as
  data (`cycle?_sound`); `none` means no closed walk within the fuel —
  for an `Acyclic` graph always `none` (`cycle?_eq_none_of_acyclic`),
  and budget exhaustion is never a verdict (01 §3).
- The strata: `Stratified` (the layer function strictly increasing
  along every edge) implies `Acyclic` (`Stratified.acyclic`, the cheap
  direction); the CONVERSE (a layering exists under `Acyclic` — the
  peel's correctness) is the deep construction, named follow-up; the
  `peel` checker lands as the decidable data face.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import ZSet.Relation

namespace ZSet

variable [wk : WKind K] [ck : CanonKey V] [DecidableEq V]

/-! ## The reading + the thin accessors -/

/-- **THE READING**: a directed graph IS a weighted relation over
    `V × V` (02 §4's one-relation-semantics; Bool = membership is the
    canonical instance, every `WKind` reads). An ABBREV — the READING,
    not a new type: every `Weighted` law applies definitionally. -/
abbrev Graph (K V : Type) [WKind K] [CanonKey V] [DecidableEq V] : Type :=
  Weighted K (V × V)

/-- The edge weight: the relation's value at `(x, y)` (thin —
    `weightW` at the pair). -/
def edgeWeight (g : Graph K V) (x y : V) : K := weightW g (x, y)

/-- The edge predicate, as data: a NONZERO weight at `(x, y)` (the
    finite-support discipline — zero weight = absent). -/
def isEdge (g : Graph K V) (x y : V) : Bool :=
  !wk.isZero (edgeWeight g x y)

/-- The Prop face of the edge reading — the theorems' vocabulary. -/
def Edge (g : Graph K V) (x y : V) : Prop := isEdge g x y = true

/-- The edge list as data: the support's triples `(x, y, w)` (thin). -/
def edges (g : Graph K V) : List (V × V × K) :=
  g.rep.map fun e => (e.1.1, e.1.2, e.2)

omit ck in
/-- The key-absent zero lemma: a pair missing from the rep weighs zero. -/
theorem weightOfW_pair_zero (l : List ((V × V) × K)) (v u : V)
    (h : ∀ p ∈ l, p.1 ≠ (v, u)) : weightOfW l (v, u) = wk.zero := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    have hne : ¬ (p.1 = (v, u)) := h p (by simp)
    simp only [weightOfW, if_neg hne]
    exact ih fun q hq => h q (by simp [hq])

/-! ## The ADJACENCY reading -/

/-- The ADJACENCY reading: `v`'s successors in the support (thin — the
    rep's out-entries of `v`). -/
def succs (g : Graph K V) (v : V) : List V :=
  g.rep.filterMap fun e => if e.1.1 = v then some e.1.2 else none

/-- The adjacency reading is SOUND: a successor is a real edge. -/
theorem Edge.succs_mem {g : Graph K V} {v u : V} (h : u ∈ succs g v) :
    Edge g v u := by
  obtain ⟨e, he, hsome⟩ := List.mem_filterMap.mp h
  obtain ⟨p, w⟩ := e
  obtain ⟨x, y⟩ := p
  by_cases hkey : x = v
  · rw [if_pos hkey] at hsome
    have hyu : y = u := Option.some.inj hsome
    subst hyu
    subst hkey
    unfold Edge isEdge edgeWeight weightW
    rw [weightOfW_entry g.rep g.sorted ((x, y), w) he,
      g.nonzero ((x, y), w) he]
    rfl
  · rw [if_neg hkey] at hsome
    simp at hsome

/-- ... and COMPLETE: every edge shows up in the adjacency reading. -/
theorem succs_of_Edge {g : Graph K V} {v u : V} (h : Edge g v u) :
    u ∈ succs g v := by
  by_cases hnin : u ∈ succs g v
  · exact hnin
  · exfalso
    have hmem : ∀ p ∈ g.rep, p.1 ≠ (v, u) := by
      intro p hp hkey
      have hf : (if p.1.1 = v then some p.1.2 else none) = some u := by
        rw [hkey]
        simp
      exact hnin (List.mem_filterMap.mpr ⟨p, hp, hf⟩)
    have h0 : weightW g (v, u) = wk.zero :=
      weightOfW_pair_zero g.rep v u hmem
    unfold Edge isEdge edgeWeight at h
    rw [h0, wk.isZero_zero] at h
    simp at h

/-! ## Reachability: the closure's Prop face -/

/-- REACHABILITY: the ≥1-edge path reading, inductively. A cycle is
    exactly `Reach g v v`. -/
inductive Reach (g : Graph K V) : V → V → Prop where
  | edge {x y : V} : Edge g x y → Reach g x y
  | step {x y z : V} : Reach g x y → Edge g y z → Reach g x z

/-- ACYCLICITY: no vertex reaches itself (`Reach` is the ≥1-edge
    reading, so `Reach g v v` IS a cycle — no non-trivial closed walk). -/
def Acyclic (g : Graph K V) : Prop := ∀ v, ¬ Reach g v v

/-! ## The support's vertices (the sweep's domain) -/

/-- Insert without duplication. -/
def vertIns (v : V) (l : List V) : List V :=
  if l.contains v then l else v :: l

omit ck in
theorem vertIns_mem (v w : V) (l : List V) :
    v ∈ vertIns w l ↔ v = w ∨ v ∈ l := by
  by_cases h : l.contains w = true
  · have hw : w ∈ l := List.contains_iff_mem.1 h
    simp only [vertIns, if_pos h]
    constructor
    · exact fun hv => Or.inr hv
    · rintro (hv | hv)
      · exact hv ▸ hw
      · exact hv
  · simp only [vertIns, if_neg h]
    exact List.mem_cons

omit wk in
/-- The support's vertices, deduplicated. -/
def vertsOf : List ((V × V) × K) → List V
  | [] => []
  | e :: r => vertIns e.1.1 (vertIns e.1.2 (vertsOf r))

/-- The graph's vertex support (thin over the rep). -/
def verts (g : Graph K V) : List V := vertsOf g.rep

omit wk ck in
theorem mem_vertsOf : ∀ (l : List ((V × V) × K)) (e : (V × V) × K), e ∈ l →
    e.1.1 ∈ vertsOf l ∧ e.1.2 ∈ vertsOf l := by
  intro l
  induction l with
  | nil => intro e h; cases h
  | cons e' r ih =>
    intro e h
    obtain rfl | h' := List.mem_cons.1 h
    · exact ⟨
        vertIns_mem _ _ _ |>.2 (Or.inl rfl),
        vertIns_mem _ _ _ |>.2 (Or.inr (vertIns_mem _ _ _ |>.2 (Or.inl rfl)))⟩
    · obtain ⟨h1, h2⟩ := ih e h'
      exact ⟨
        vertIns_mem _ _ _ |>.2 (Or.inr (vertIns_mem _ _ _ |>.2 (Or.inr h1))),
        vertIns_mem _ _ _ |>.2 (Or.inr (vertIns_mem _ _ _ |>.2 (Or.inr h2)))⟩

/-! ## The walk discipline -/

/-- The consecutive-pair discipline: a vertex list whose consecutive
    pairs are edges (the walk invariant — an INDUCTIVE, so the
    derivations induct). -/
inductive Links (g : Graph K V) : List V → Prop where
  | nil : Links g []
  | single (x : V) : Links g [x]
  | cons (x y : V) (rest : List V) :
      Edge g x y → Links g (y :: rest) → Links g (x :: y :: rest)

/-- The last element of a list (`none` for `[]` — never produced by
    the sweep's walks). -/
def lastOf? : List V → Option V
  | [] => none
  | [x] => some x
  | _ :: x :: r => lastOf? (x :: r)

omit wk in
omit ck [DecidableEq V] in
theorem lastOf?_nil : lastOf? ([] : List V) = none := rfl

omit wk in
omit ck [DecidableEq V] in
theorem lastOf?_single (x : V) : lastOf? [x] = some x := rfl

/-- Appending one edge-extensible vertex preserves the walk
    discipline. -/
theorem Links.append_edge {g : Graph K V} :
    ∀ (p : List V), Links g p → ∀ (l u : V), lastOf? p = some l →
      Edge g l u → Links g (p ++ [u]) := by
  intro p h
  induction h with
  | nil =>
    intro l u hl _
    rw [lastOf?_nil] at hl
    simp at hl
  | single x =>
    intro l u hl he
    rw [lastOf?_single] at hl
    have hx : x = l := Option.some.inj hl
    subst hx
    exact Links.cons x u [] he (Links.single u)
  | cons x y r he' _ ih =>
    intro l u hl he
    exact Links.cons x y (r ++ [u]) he' (ih l u hl he)

/-! ## The bounded path-folding (the closure's data face) -/

/-- The bounded path-folding: ALL walks from `v` of exactly `k` edges
    (the relational closure's iterated composition, as data — repeats
    kept; the sweep is honest, not memoized). -/
def walksFrom (g : Graph K V) : Nat → V → List (List V)
  | 0, v => [[v]]
  | k + 1, v =>
      (walksFrom g k v).flatMap fun p =>
        match lastOf? p with
        | none => []
        | some l => (succs g l).map fun u => p ++ [u]

/-- Every walk of at most `N` edges from any support vertex. -/
def walks (g : Graph K V) (N : Nat) : List (List V) :=
  (verts g).flatMap fun v =>
    (List.range (N + 1)).flatMap fun k => walksFrom g k v

theorem mem_walks {g : Graph K V} {N : Nat} {c : List V} (h : c ∈ walks g N) :
    ∃ (v : V) (k : Nat), c ∈ walksFrom g k v := by
  simp only [walks, List.mem_flatMap] at h
  obtain ⟨v, _, hk⟩ := h
  obtain ⟨k, _, hc⟩ := hk
  exact ⟨v, k, hc⟩

/-- The sweep's walks honor the walk discipline. -/
theorem walksFrom_links (g : Graph K V) (k : Nat) (v : V) :
    ∀ p ∈ walksFrom g k v, Links g p := by
  induction k with
  | zero =>
    intro p hp
    rcases List.mem_singleton.1 hp with rfl
    exact Links.single v
  | succ k ih =>
    intro p hp
    simp only [walksFrom, List.mem_flatMap] at hp
    obtain ⟨p', hp'mem, hp'ext⟩ := hp
    cases hlast : lastOf? p' with
    | none => rw [hlast] at hp'ext; simp at hp'ext
    | some l =>
      rw [hlast] at hp'ext
      simp only at hp'ext
      obtain ⟨u, hu, hp⟩ := List.mem_map.mp hp'ext
      subst hp
      exact Links.append_edge p' (ih p' hp'mem) l u hlast (Edge.succs_mem hu)

/-- The closed-walk test: the last→head edge exists (the self-loop
    `[v]` included — a 1-cycle IS a cycle). -/
def isClosedWalk (g : Graph K V) : List V → Bool
  | [] => false
  | x :: rest =>
      match lastOf? (x :: rest) with
      | some l => isEdge g l x
      | none => false

/-- Reach TRANSITIVITY: the closure's composition law (the
    path-folding's algebra). -/
theorem Reach.trans {g : Graph K V} :
    ∀ {b c : V}, Reach g b c → ∀ {a : V}, Reach g a b → Reach g a c := by
  intro b c h2
  induction h2 with
  | edge he => intro a h1; exact Reach.step h1 he
  | step _ he ih =>
    intro a h1
    exact Reach.step (ih h1) he

/-- The walk-to-reach lemma: a nontrivial walk's ends are connected. -/
theorem Reach.of_links {g : Graph K V} {y : V} :
    ∀ (p : List V), lastOf? p = some y → ∀ (x : V) (rest : List V),
      Links g p → p = x :: rest → rest ≠ [] → Reach g x y := by
  intro p
  induction p with
  | nil =>
    intro hl
    rw [lastOf?_nil] at hl
    simp at hl
  | cons x' r ih =>
    intro hl x rest hlinks heq hne
    cases heq
    cases hlinks with
    | single _ => exact absurd rfl hne
    | cons _ y'' r'' he' ht =>
      cases r'' with
      | nil =>
        simp only [lastOf?] at hl
        have hy : y'' = y := Option.some.inj hl
        subst hy
        exact Reach.edge he'
      | cons z rz =>
        exact Reach.trans (ih hl y'' (z :: rz) ht rfl (by simp))
          (Reach.edge he')

/-- A closed swept walk is a genuine cycle: some vertex reaches
    itself. -/
theorem Reach.cycle_of_closed {g : Graph K V} {c : List V}
    (hlinks : Links g c) (hc : isClosedWalk g c = true) :
    ∃ v, Reach g v v := by
  cases c with
  | nil => simp only [isClosedWalk] at hc; simp at hc
  | cons x rest =>
    simp only [isClosedWalk] at hc
    cases hl : lastOf? (x :: rest) with
    | none => rw [hl] at hc; simp at hc
    | some l =>
      rw [hl] at hc
      have hed : Edge g l x := hc
      cases rest with
      | nil =>
        rw [lastOf?_single] at hl
        have hxl : x = l := Option.some.inj hl
        subst hxl
        exact ⟨x, Reach.edge hed⟩
      | cons z rz =>
        exact ⟨x, Reach.step
          (Reach.of_links (x :: z :: rz) hl x (z :: rz) hlinks rfl (by simp))
          hed⟩

/-! ## The acyclicity check (the cycle refused AS DATA) -/

/-- The first closed walk in a sweep list (the check's scan). -/
def firstClosed (g : Graph K V) : List (List V) → Option (List V)
  | [] => none
  | c :: rest => if isClosedWalk g c then some c else firstClosed g rest

theorem firstClosed_sound (g : Graph K V) :
    ∀ (l : List (List V)) (c : List V), firstClosed g l = some c →
      c ∈ l ∧ isClosedWalk g c = true := by
  intro l
  induction l with
  | nil => intro c h; cases h
  | cons a rest ih =>
    intro c h
    unfold firstClosed at h
    by_cases hca : isClosedWalk g a = true
    · rw [if_pos hca] at h
      have hac : a = c := Option.some.inj h
      subst hac
      exact ⟨List.mem_cons_self .., hca⟩
    · rw [if_neg hca] at h
      obtain ⟨hmem, hclosed⟩ := ih c h
      exact ⟨List.mem_cons_of_mem _ hmem, hclosed⟩

/-- **THE ACYCLICITY CHECK**: sweep every walk of ≤ `N` edges from
    every support vertex; a closed one is returned AS DATA (the cycle).
    The honest trichotomy in one option: `some c` = PROVED cycle
    (`cycle?_sound`); `none` = no closed walk within the fuel — for an
    `Acyclic` graph always `none` (`cycle?_eq_none_of_acyclic`); a
    cyclic graph can exhaust a small fuel, and budget exhaustion is
    never a verdict (01 §3). -/
def cycle? (g : Graph K V) (N : Nat) : Option (List V) :=
  firstClosed g (walks g N)

theorem cycle?_sound {g : Graph K V} {N : Nat} {c : List V}
    (h : cycle? g N = some c) : ∃ v, Reach g v v := by
  obtain ⟨hmem, hc⟩ := firstClosed_sound g (walks g N) c h
  obtain ⟨v, k, hfrom⟩ := mem_walks hmem
  exact Reach.cycle_of_closed (walksFrom_links g k v c hfrom) hc

theorem cycle?_eq_none_of_acyclic {g : Graph K V} (N : Nat) (h : Acyclic g) :
    cycle? g N = none := by
  cases hfind : cycle? g N with
  | none => rfl
  | some c =>
    exfalso
    obtain ⟨v, hr⟩ := cycle?_sound hfind
    exact h v hr

/-- The fuel-honest check at the support-size bound. -/
def findCycle (g : Graph K V) : Option (List V) :=
  cycle? g (verts g).length

/-! ## The reachability sweep (the closure's data face) -/

/-- Insert every element of `l` into `acc` without duplication. -/
def addAll : List V → List V → List V
  | [], acc => acc
  | v :: rest, acc => addAll rest (vertIns v acc)

/-- One frontier step: the set, plus everything one edge away. -/
def expand (g : Graph K V) (frontier : List V) : List V :=
  addAll (frontier.flatMap (succs g)) frontier

omit ck in
theorem mem_addAll : ∀ (l acc : List V) (x : V),
    x ∈ addAll l acc → x ∈ l ∨ x ∈ acc := by
  intro l
  induction l with
  | nil =>
    intro acc x h
    simp only [addAll] at h
    exact Or.inr h
  | cons v rest ih =>
    intro acc x h
    simp only [addAll] at h
    rcases ih (vertIns v acc) x h with h1 | h1
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · rcases (vertIns_mem x v acc).mp h1 with h2 | h2
      · exact Or.inl (by simp [h2])
      · exact Or.inr h2

theorem mem_expand {g : Graph K V} {frontier : List V} {x : V}
    (h : x ∈ expand g frontier) :
    x ∈ frontier ∨ ∃ u, u ∈ frontier ∧ Edge g u x := by
  unfold expand at h
  rcases mem_addAll _ _ x h with h1 | h1
  · simp only [List.mem_flatMap] at h1
    obtain ⟨u, hu, hx⟩ := h1
    exact Or.inr ⟨u, hu, Edge.succs_mem hx⟩
  · exact Or.inl h1

/-- The bounded reachability sweep: `v` plus everything reachable by
    a walk of ≤ `N` edges (the frontier fold — the finite closure's
    data face). -/
def reachFrom (g : Graph K V) : Nat → V → List V
  | 0, v => [v]
  | N + 1, v => expand g (reachFrom g N v)

/-- The sweep is SOUND against the Prop reading (`v` itself rides the
    0-edge base). The converse — a `Reach` path needs no more than the
    |support| fuel (the simple-path shortcut) — is the named
    follow-up, so the fuel here is a premise, never a verdict. -/
theorem reachFrom_sound (g : Graph K V) (N : Nat) :
    ∀ (v x : V), x ∈ reachFrom g N v → x = v ∨ Reach g v x := by
  induction N with
  | zero =>
    intro v x h
    rcases List.mem_singleton.1 h with rfl
    exact Or.inl rfl
  | succ N ih =>
    intro v x h
    rcases mem_expand h with h' | ⟨u, hu, hx⟩
    · exact ih v x h'
    · rcases ih v u hu with rfl | hru
      · exact Or.inr (Reach.edge hx)
      · exact Or.inr (Reach.step hru hx)

/-! ## The topological discipline (the strata) -/

/-- A STRATIFICATION: a layer function strictly increasing along every
    edge — a DAG's strata as data (the topological order reading). -/
def Stratified (g : Graph K V) (layer : V → Nat) : Prop :=
  ∀ x y, Edge g x y → layer x < layer y

theorem Reach.layer_lt {g : Graph K V} {layer : V → Nat}
    (h : Stratified g layer) {x y : V} (hr : Reach g x y) :
    layer x < layer y := by
  induction hr with
  | edge he => exact h _ _ he
  | step _ he ih => exact Nat.lt_trans ih (h _ _ he)

/-- The cheap direction of the topological discipline: a stratified
    graph is acyclic (a cycle would give `layer v < layer v`). The
    converse — a layering exists under `Acyclic` — is the deep
    construction, the named follow-up; the `peel` checker below is its
    decidable data face. -/
theorem Stratified.acyclic {g : Graph K V} {layer : V → Nat}
    (h : Stratified g layer) : Acyclic g := fun _ hr =>
  Nat.lt_irrefl _ (Reach.layer_lt h hr)

/-- The sources of a vertex set: those with no in-edge from within the
    set (self-loops included — a self-loop is a cycle, correctly
    refused a source). -/
def sources (g : Graph K V) (vs : List V) : List V :=
  vs.filter fun v => !(vs.any fun u => isEdge g u v)

/-- The STRATA CHECKER: repeatedly peel the sources. `some layers` =
    the layering as data (layer `i` = `layers[i]`); `none` = the peel
    stuck with every remaining vertex in-edge — the residual is a
    cycle's vertex set. -/
def peel (g : Graph K V) : Nat → List V → Option (List (List V))
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, vs =>
      match sources g vs with
      | [] => none
      | ss =>
          (peel g fuel (vs.filter fun v => !(ss.contains v))).map
            fun layers => ss :: layers

end ZSet
