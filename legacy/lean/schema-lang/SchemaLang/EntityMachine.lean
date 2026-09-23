/-
# SchemaLang.EntityMachine — the entity-machine preset (W8.4)

The canon row: **an entity lifecycle = a machine ON a record: enum state
column + transitions; transitions are deltas on the state column;
legality relation, typestate Rust, journal antijoin check,
replay/rewind — all derived.** A workflow status = this preset.

The preset is COMPOSITION + the proofs that the composition preserves
the laws — it re-implements nothing. The pieces it assembles:

- `Machines.Core`/`Machines.Dsl` — the machine and the `machine!`
  `states:` entourage (state space, transition table, table lookup,
  the agreement theorem, the `DecidablePred` instance). The command
  half (`SchemaLang.Meta.EntityMachine`) emits the `machine!`
  invocation, so every generated machine carries the generated
  `tr`/`step?` agreement (`Machine.tr_iff_step?`, proved once in
  Core) and the generated `TableStep?_eq_step?` tie.
- `SchemaLang.Update2` — the per-transition keyed update: one
  transition = ONE keyed update on the state column (guard
  `status = from`, set `status := to`; codes = declaration order).
- The legality relation — the canon's regular-language row:
  `Machine.legalFrom` = membership (the run accepts); the JOURNAL is
  the delta log (`JournalEntry`), its check is the ANTIJOIN against
  the machine's edge table (`journalAntijoin`/`legalJournal`), and
  `replay` folds the journal through `step?`.
- The typestate hook — `Emit.Typestate`'s projection shape,
  generalized: non-rewind edges as methods on per-state newtypes, with
  the legality/reachability pins proved from the table's honesty
  (`trans_honest`) + the generated tie.
- The obligation view — each transition's guard/postcondition as
  obligations at `decidableNow` (`fires`/`moves`), discharged by the
  kernel's `decide` over the pinned from-row (the default-row
  discipline: the ONE row the lane materializes from the declaration).

The command half owns: record/state-column resolution, ctor gates,
code assignment, and emitting the generated defs. This module owns the
DATA and the generic theorems. One proof per law — every generated
machine instantiates them.

Ownership: the W8.4 entity-machine lane (this module +
`SchemaLang.Meta.EntityMachine`). Deliberate exclusions: NO emitter
registration (the hook's Rust text is a def, not a `GenCtx` job — the
byte-tie holds by construction, the `Meta.Keys` pattern); no
registration into `update2ItemExt` (the update lane owns that
registry's elaborator route; the preset emits the update DATA — wiring
the preset's rows in is a follow-up); no separate `Inv` surface (the
closed enum IS the invariant — `Inv := True`; a stray-state machine
like the hand-built `OrderMachine` keeps its hand-written `Inv`); no
effectful transition payloads (Machines v1, the OrderMachine
exclusion); the journal carries deltas, not full rows (the event
lane's `@[event_sourced]` journal is the wire record, a different
projection).
-/

module

public import SchemaLang.Validate
public import SchemaLang.Update2
public import Machines.Core
public import CodegenCore

@[expose] public section

namespace SchemaLang.EntityMachine

/-! ## The declaration data -/

/-- One declared transition: its event name and the edge (from-state →
    to-state), as NAMES (the codes ride the declaration's state order). -/
structure EntityTransition where
  name : String
  src : String
  dst : String
deriving Repr, BEq, DecidableEq, Inhabited

/-- The preset's declaration row: the generated machine's name, the
    record + the u64 state column it rides, the states (CODE ORDER —
    code = index), and the transitions. -/
structure EntityMachineDecl where
  machine : String
  record : String
  stateCol : String
  states : List String
  transitions : List EntityTransition
deriving Repr, BEq, DecidableEq, Inhabited

/-- The state CODE: the declared state's index in the states list (the
    u64 the transition deltas write). `none` = not a declared state
    (the command gates this — unreachable for command-generated data). -/
def EntityMachineDecl.stateCode (d : EntityMachineDecl) (s : String) :
    Option Nat :=
  (d.states.zip (List.range d.states.length)).find? (fun p => p.1 == s)
    |>.map (·.2)

/-! ## The legality relation (the canon: DFA membership) -/

/-- THE LEGALITY RELATION, executable: an event sequence is legal from
    `init` iff the machine's run ACCEPTS it — membership in the
    machine's language (the regular-language row; the DFA check needs
    no automata toolkit at this granularity). -/
def legalFrom (m : Machines.Machine) (init : m.State)
    (seq : List m.Label) : Bool :=
  (m.run init seq).isSome

/-! ## The journal: the event log as deltas — the antijoin check, replay -/

/-- One journal entry: a transition's DELTA on the state column —
    (event, from-state, to-state). The journal is the event log; its
    entries are the state-column deltas the transitions emit. -/
abbrev JournalEntry (L S : Type) := L × S × S

/-- THE JOURNAL ANTIJOIN CHECK: the journal's entries with NO matching
    row in the machine's edge table — the illegal deltas, isolated
    (the antijoin; legality check = membership). -/
def journalAntijoin [BEq L] [BEq S] (edges journal : List (JournalEntry L S)) :
    List (JournalEntry L S) :=
  journal.filter (fun j => !edges.any (fun e => e == j))

/-- Journal legality: the antijoin is EMPTY — every delta is a machine
    edge (the canon's membership reading of the regular language). -/
def legalJournal [BEq L] [BEq S] (edges journal : List (JournalEntry L S)) :
    Bool :=
  (journalAntijoin edges journal).isEmpty

theorem legalJournal_iff [BEq L] [BEq S] [LawfulBEq L] [LawfulBEq S]
    (edges journal : List (JournalEntry L S)) :
    legalJournal edges journal = true ↔ ∀ j ∈ journal, j ∈ edges := by
  unfold legalJournal journalAntijoin
  rw [List.isEmpty_iff, List.filter_eq_nil_iff]
  constructor
  · intro h j hj
    have h' := h j hj
    have hany : edges.any (fun e => e == j) = true := by
      cases hb : edges.any (fun e => e == j) with
      | true => rfl
      | false => rw [hb] at h'; simp at h'
    obtain ⟨e, he, heq⟩ := List.any_eq_true.mp hany
    have hej : e = j := beq_iff_eq.mp heq
    subst hej
    exact he
  · intro h j hj
    have hany : edges.any (fun e => e == j) = true :=
      List.any_eq_true.mpr ⟨j, h j hj, beq_self_eq_true _⟩
    simp [hany]

/-- Replay: fold the journal through the machine's step function —
    each entry must fire from the CURRENT state and land on its
    recorded delta. `none` = a broken journal (a stale delta, an
    illegal edge — replay is the audit, the antijoin is the gate). -/
def replay [BEq L] [BEq S] (step : S → L → Option S) (init : S) :
    List (JournalEntry L S) → Option S
  | [] => some init
  | (l, _, s₁) :: rest =>
      match step init l with
      | some s => if s == s₁ then replay step s rest else none
      | none => none

/-- The journal CHAINS from `init`: each entry's from-state is the
    previous entry's to-state (the deltas connect). -/
def ChainsFrom {L S : Type} (init : S) : List (JournalEntry L S) → Prop
  | [] => True
  | (_, s₀, s₁) :: rest => init = s₀ ∧ ChainsFrom s₁ rest

/-- THE REPLAY LAW: a journal that passes the antijoin check AND chains
    from `init` replays to a final state — legality + chaining means
    the log is executable. (Rewind is the machine! rank clause's
    `rank_advances` pair — the same discipline on the reversed edge.) -/
theorem replay_of_legalJournal [BEq L] [BEq S] [LawfulBEq L] [LawfulBEq S]
    (step : S → L → Option S) (edges : List (JournalEntry L S))
    (honest : ∀ e ∈ edges, step e.2.1 e.1 = some e.2.2)
    (journal : List (JournalEntry L S)) :
    legalJournal edges journal = true → ∀ init, ChainsFrom init journal →
      ∃ fin, replay step init journal = some fin := by
  induction journal with
  | nil => intro _ init _; exact ⟨init, rfl⟩
  | cons j rest ih =>
      intro hlegal init hchain
      obtain ⟨h₀, hrest⟩ := hchain
      subst h₀
      have hmem : j ∈ edges :=
        (legalJournal_iff edges (j :: rest)).mp hlegal j List.mem_cons_self
      have hstep : step j.2.1 j.1 = some j.2.2 := honest j hmem
      have hlegal' : legalJournal edges rest = true :=
        (legalJournal_iff edges rest).mpr fun j' hj' =>
          (legalJournal_iff edges (j :: rest)).mp hlegal j'
            (List.mem_cons_of_mem _ hj')
      simp only [replay, hstep, beq_self_eq_true]
      obtain ⟨fin, hfin⟩ := ih hlegal' j.2.2 hrest
      exact ⟨fin, hfin⟩

/-- THE GENERATED TABLE IS HONEST: every row of the machine!-generated
    transition table (the `states:` entourage's `List.flatMap`/
    `List.filterMap` fold) is a real step of the machine. One proof for
    every generated machine — the command cites it with `rfl` against
    the table's defining fold. -/
theorem trans_honest (m : Machines.Machine)
    (labels : List m.Label) (states : List m.State)
    (trans : List (JournalEntry m.Label m.State))
    (hdef : trans = _root_.List.flatMap
      (fun l => _root_.List.filterMap
        (fun s => _root_.Option.map (fun s' => (l, s, s')) (m.step? s l))
        states) labels) :
    ∀ e ∈ trans, m.step? e.2.1 e.1 = some e.2.2 := by
  intro e he
  rw [hdef, List.mem_flatMap] at he
  obtain ⟨l, hl, hfm⟩ := he
  rw [List.mem_filterMap] at hfm
  obtain ⟨s, hst, hmap⟩ := hfm
  cases hstep : m.step? s l with
  | none => rw [hstep] at hmap; simp at hmap
  | some s' =>
      rw [hstep] at hmap
      have he' : (l, s, s') = e := Option.some.inj hmap
      subst he'
      show m.step? s l = some s'
      exact hstep

/-! ## The typestate hook (the Emit/Typestate projection, generalized) -/

/-- The typestate projection's DATA: the rewind edge (never emitted —
    a typestate value is consumed, never rewrapped), the folded edge
    table (the command supplies `hookEdges` over the generated
    `Trans`), and the two naming maps. The Rust builder is pure over
    this — same discipline as `Emit.Machine.orderMachineEmitter`. -/
structure TypestateHook (m : Machines.Machine) where
  rewind : Option m.Label
  edges : List (JournalEntry m.Label m.State)
  stateStruct : m.State → String
  eventMethod : m.Label → String

/-- The typestate's edges: every non-rewind row of the transition
    table (the `reset`-edge exclusion, generalized; no rewind = every
    row). TRANS first — the edge table's type fixes the universes (the
    instance-search anchor; the Option rewind as the first arg would
    unify L to `Option L`, the elaboration-order lesson). -/
def hookEdges [BEq L] (trans : List (JournalEntry L S)) (rewind : Option L) :
    List (JournalEntry L S) :=
  match rewind with
  | none => trans
  | some rw => trans.filter (fun j => !(j.1 == rw))

/-- LEGALITY PIN (per generated machine): every folded edge is a
    `some` step of the proved table — no emitted method can represent
    an illegal firing, which is why the methods return their target
    directly (no Option, no panic). -/
theorem hookEdges_legal (m : Machines.Machine) [BEq m.Label]
    (rewind : Option m.Label)
    (trans : List (JournalEntry m.Label m.State))
    (tableStep : m.Label → m.State → Option m.State)
    (tie : ∀ (e : m.Label) (s : m.State), tableStep e s = m.step? s e)
    (honest : ∀ e ∈ trans, m.step? e.2.1 e.1 = some e.2.2) :
    ((hookEdges trans rewind).map fun e => tableStep e.1 e.2.1).all
      Option.isSome = true := by
  unfold hookEdges
  cases rewind with
  | none =>
      rw [List.all_eq_true]
      intro x hx
      obtain ⟨j, hj, hxj⟩ := List.mem_map.mp hx
      have hstep := honest j hj
      rw [← hxj, tie j.1 j.2.1, hstep]
      simp
  | some rw =>
      rw [List.all_eq_true]
      intro x hx
      obtain ⟨j, hj, hxj⟩ := List.mem_map.mp hx
      obtain ⟨hj', -⟩ := List.mem_filter.mp hj
      have hstep := honest j hj'
      rw [← hxj, tie j.1 j.2.1, hstep]
      simp

/-- The emitted states: the initial state plus every folded edge
    target, table order, deduped. An unreachable state (target of no
    row) cannot appear — the `Inv` non-vacuity reading. -/
def hookStates [BEq S] (init : S) (edges : List (JournalEntry L S)) :
    List S :=
  (init :: edges.map (·.2.2)).eraseDups

/-- REACHABILITY PIN: every emitted struct's state is the initial
    state or a row target of the folded edges. -/
theorem hookStates_reachable [BEq S] [LawfulBEq S] (init : S)
    (edges : List (JournalEntry L S)) :
    (hookStates init edges).all
      (fun s => (s == init) || edges.any (fun e => e.2.2 == s)) = true := by
  rw [List.all_eq_true]
  intro s hs
  have hs' : s ∈ init :: edges.map (·.2.2) := List.mem_eraseDups.mp hs
  rcases List.mem_cons.mp hs' with rfl | hm
  · simp
  · obtain ⟨e, he, hEq⟩ := List.mem_map.mp hm
    have hany : edges.any (fun e => e.2.2 == s) = true :=
      List.any_eq_true.mpr ⟨e, he, by simp [hEq]⟩
    simp [hany]

/-! ### The Rust items (the hook's emission shape) -/

/-- One typestate struct: `pub struct New(pub u64);` — the payload is
    the row identity (the `Emit.Typestate` shape). -/
def hookStructItem {m : Machines.Machine} (hook : TypestateHook m)
    (s : m.State) : CodegenCore.Emit.Rust.Item :=
  .newtype (hook.stateStruct s) "u64" ["Clone", "Copy", "Debug", "PartialEq", "Eq"]

/-- The methods on one source state: one per folded edge FROM it, in
    table order — direct return, the row is legal by construction
    (`hookEdges_legal`). -/
def hookMethodItems {m : Machines.Machine} (hook : TypestateHook m)
    (ms : List (m.Label × m.State)) : List CodegenCore.Emit.Rust.Item :=
  ms.flatMap fun (e, t) =>
    [ .raw s!"    pub fn {hook.eventMethod e}(self) -> {hook.stateStruct t} \{"
    , .raw s!"        {hook.stateStruct t}(self.0)"
    , .raw "    }" ]

/-- The inherent impl for one source state — omitted ENTIRELY for
    terminal states (no folded edge leaves them): the illegal
    transition is unrepresentable, not `None`. -/
def hookImplItems {m : Machines.Machine} [BEq m.State]
    (hook : TypestateHook m) (s : m.State) : List CodegenCore.Emit.Rust.Item :=
  let ms := hook.edges.filter fun j => j.2.1 == s
  match ms with
  | [] => []
  | _ =>
      [ .raw s!"impl {hook.stateStruct s} \{" ]
        ++ hookMethodItems hook (ms.map fun j => (j.1, j.2.2))
        ++ [ .raw "}" ]

/-- The full module's items: the pinning comments, one struct per
    reachable state, one impl per state WITH outgoing edges.
    Deterministic (table-order folds only — byte-tie ready). -/
def hookItems {m : Machines.Machine} [BEq m.State] (hook : TypestateHook m)
    (initial : m.State) (specSource : String) : List CodegenCore.Emit.Rust.Item :=
  let ss := hookStates initial hook.edges
  [ .comment s!"GENERATED from {specSource} — the entity machine's TYPESTATE"
  , .comment "projection. Each struct = one REACHABLE state (payload = the row"
  , .comment "id, u64); each method = one non-rewind edge of the machine's"
  , .comment "transition table — the table the generated tie theorem pins to"
  , .comment "the machine. No Option, no panic: every folded row is a step of"
  , .comment "the proved table (hookEdges_legal). Do not edit — regenerate."
  , .raw "" ]
    ++ ss.map (hookStructItem hook)
    ++ ((ss.flatMap fun s => .raw "" :: hookImplItems hook s).drop 1)

/-- The hook's Rust text (a DEF, not a registered emitter — the
    byte-tie holds by construction; the registry wiring is the registry
    owner's line when a fixture goes live). -/
def hookRust {m : Machines.Machine} [BEq m.State] (hook : TypestateHook m)
    (initial : m.State) (specSource : String) : String :=
  CodegenCore.Emit.Rust.renderModule (hookItems hook initial specSource)

/-! ## The obligation view -/

/-- The entity-machine obligation's fact: a transition's keyed update
    FIRES on the from-state row (`fires` — the guard reads the pinned
    code), or MOVES the state column to the to-code (`moves` — the
    postcondition). -/
inductive EntityClaim where
  | fires (u : SomeUpdate2) (fromCode : UInt64)
  | moves (u : SomeUpdate2) (fromCode toCode : UInt64)
deriving Inhabited

/-- THE CLAIM, executable: over the record's all-default row with the
    state column written to the from-code (the ONE row the lane
    materializes from the declaration — the default-row discipline),
    the guard fires / the postcondition holds. The from-row's write
    rides the GUARD's own code-equality path (the preset's derivation
    emits the `.eq (.col …) (.lit …)` shape — a foreign-shaped update
    claims `false`, the backend refuses). A record without a
    literal-default row claims `false` too. -/
def EntityClaim.holds : EntityClaim → Bool
  | .fires u fc =>
      match u with
      | ⟨fs, item⟩ =>
          match defaultRow? fs with
          | some row =>
              match item.guard with
              | .eq (.col _ p) (.lit _) =>
                  validates item.guard (p.set row (.u64 fc))
              | _ => false
          | none => false
  | .moves u fc tc =>
      match u with
      | ⟨fs, item⟩ =>
          match defaultRow? fs with
          | some row =>
              match item.guard with
              | .eq (.col _ p) (.lit _) =>
                  match ColPath.get p
                    (applySets item.sets (p.set row (.u64 fc))) with
                  | .u64 v => v == tc
                  | _ => false
              | _ => false
          | none => false

/-- The claim as a Prop (the `decide` gate reads this). -/
def EntityClaim.claim (c : EntityClaim) : Prop := c.holds = true

/-- The claim IS decidable: `holds` computes over the registered data
    (the anonymous-instance auto-name would collide cross-module, the
    `keyClaimDecidable` lesson). -/
instance entityClaimDecidable (c : EntityClaim) : Decidable c.claim :=
  instDecidableEqBool c.holds true

/-- The schema-level entity obligation (the kit's shape at the
    transition row; `abbrev` — reducible, the kit discipline). -/
abbrev EntityObligation := CodegenCore.Obligation EntityClaim

/-- The computed tier: entity claims are decidable row-data predicates
    over the pinned from-row — the `decidableNow` rung. No citation
    lane (the guard/postcondition are the DERIVATION's content, not
    user theorems) and no generated-check lane yet (the byte-tie: no
    emitter reads the preset). -/
def EntityClaim.tierOf : EntityClaim → CodegenCore.Obligation.Tier :=
  fun _ => .decidableNow

/-- The obligation VIEW of one transition: the guard obligation + the
    postcondition obligation (each transition's guard/postcondition as
    obligations — the preset's fifth artifact). -/
def transitionObligations (machine tname : String) (u : SomeUpdate2)
    (fromCode toCode : UInt64) : List EntityObligation :=
  [ { label := s!"{machine}.{tname}-fires"
    , tier := EntityClaim.tierOf (.fires u fromCode)
    , payload := .fires u fromCode
    , provenance := machine.toName }
  , { label := s!"{machine}.{tname}-moves"
    , tier := EntityClaim.tierOf (.moves u fromCode toCode)
    , payload := .moves u fromCode toCode
    , provenance := machine.toName } ]

/-- THE DISCHARGE. Only the `decidableNow` rung is an entity-lane
    assignment (`EntityClaim.tierOf`); the kernel's `decide` over the
    claim is the evidence. `none` = the loud gap: a hand-set tier the
    lane cannot serve, or a FALSE decide verdict (a guard that refuses
    its own from-row, a postcondition that misses the to-code — the
    negative controls pin both). (The decidableNow backend is the
    KIT's — `decideDischarge`; this definition is the lane's named
    application of it, the claim riding the payload.) -/
def EntityObligation.discharge (o : EntityObligation) :
    Option CodegenCore.Obligation.Evidence :=
  CodegenCore.Obligation.decideDischarge (fun c => c.payload.claim) o

/-- SOUNDNESS of the entity lane's decidableNow backend: a
    `.decided true` verdict means the claim HOLDS (the kernel's
    `decide` validated the guard/postcondition on the pinned row —
    `of_decide_eq_true`; no new trust base). Routes through the kit's
    `decideDischarge_sound` — the proof object is shared. -/
theorem EntityObligation.discharge_sound (o : EntityObligation)
    (ht : o.tier = .decidableNow)
    (h : o.discharge = some (.decided true)) : o.payload.claim :=
  CodegenCore.Obligation.decideDischarge_sound _ _ ht h

/-- COMPLETENESS: a true claim discharges to the `.decided true`
    evidence — the backend FIRES on the claims it can decide. -/
theorem EntityObligation.discharge_of_claim (o : EntityObligation)
    (ht : o.tier = .decidableNow) (hc : o.payload.claim) :
    o.discharge = some (.decided true) :=
  CodegenCore.Obligation.decideDischarge_of_claim _ _ ht hc

/-! ## The transition delta -/

/-- THE PRESET'S DELTA: one transition = one keyed update on the state
    column — guard `status = from`, set `status := to` (transitions
    ARE deltas on the state column; the code discipline makes the
    delta a u64 write). The command supplies the elaboration-checked
    `ColPath` (the `HasCol` instance search — a state column off the
    record has no path and fails to elaborate). -/
def transitionUpdate (machine tname record : String) {fs : List Field}
    {n : String} (p : ColPath n .u64 fs) (fromCode toCode : UInt64) :
    Update2Item fs :=
  { name := s!"{machine}-{tname}"
  , record := record
  , guard := .eq (.col n p) (.lit fromCode)
  , sets := [{ field := { name := n, ty := .u64 }, path := p
             , value := .lit toCode }] }

end SchemaLang.EntityMachine
