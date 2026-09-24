/-
# SchemaCore.EntityMachine — the entity-machine preset (`schema_entity_machine`)

The canon row (notes/v3/08-capabilities.md #5): **an entity lifecycle =
a machine ON a record: enum state column + transitions; transitions
are keyed updates on the state column; legality = the journal
antijoin; the obligations + the conformance battery — all derived.**
A workflow status = this preset.

The preset is COMPOSITION + the proofs that the composition preserves
the laws — it re-implements nothing. The pieces it assembles (each
LANDED, cited by name at every use):

- `Machines.Dsl` — the `machine!` entourage (the state enum + the Label
  inductive + the EventSpec family + the transition table computed from
  `step?` + the `TableStep?_eq_step?` tie + the `DecidablePred`
  instance + the battery registration). The command half EMITS the
  `machine!` invocation, so every generated machine carries the
  generated tie — the tie-before-emission discipline.
- `SchemaCore.Update` — the per-transition keyed update: one
  transition = ONE keyed update on the state column (guard
  `status = from`, set `status := to`; the ColPath write spine makes a
  missing or mistyped state column unconstructible — the Option route
  is the closed-world refusal). Codes = declaration order (UInt64).
- `SchemaCore.Keys` — the declared-key resolution (`keyDeclFor`, ONE
  reading shared with the update lane's WF rung) for the preset's
  `key:` rung; `dupNames` for the name rung.
- `Machines.Testing` — the conformance battery, fed by the
  `machine!`-generated enumerations + the generated
  `labels_complete` (the battery's first-class consumer).

The generic laws are proved ONCE here and INSTANTIATED per generated
machine by citation (08's preset-as-composition principle):

- `trans_honest` — every row of a computed table is a real step;
- `legalJournal_iff` — the antijoin's membership reading;
- `edgesDet_honest` + `replay_of_legalJournal` — the replay law (a
  legal, chaining journal replays through the edge table's `step`);
- `firesOf_shape` / `movesOf_shape` (+ `ColPath.set_project?_self`,
  riding the record's fields-nodup obligation) — the keyed update
  FIRES on its from-row and MOVES the state column to its to-code.

The command half owns: the clause sweep (cardinalities, the
closed-world unknown-clause refusal with the ONE did-you-mean engine),
the state-column code assignment, and emitting the generated defs.
Deliberately absent (honest gaps, named): the REGISTRY-resolving route
(`for <registered record>` with the state TYPE checked as a nullary
inductive — the legacy gate) needs the record's fields at ELABORATION
time; the slice-sized preset takes the fields as the `fields:` clause
TERM and refuses a missing or non-u64 state column through the
Option/Diag route (`EM0001`), never silently; NO typestate/Rust
emission (no emitter consumer — lands with the first emitted surface,
the leftover rule); NO payload-carrying transitions (the `machine!`
exclusion).

The five questions (notes/v3/01-core.md): root = Universe (the
declaration data) riding the machine's TraceModel + the update lane's
Change face; carrier = the ColPath GADT index (a keyed update to a
missing/mistyped column is unconstructible) + the Prop-indexed
obligation rows (Kit.Obligation, the claim IS the index); spine
reading = registry → interpretation → artifact, with the `machine!`
emission as the artifact stage; ladder rung = the generic laws are
hand theorems proved once (rung 6), the per-machine obligations
discharge at `decidableNow` by decide; gate row = the axiom report +
SchemaTests' entityMachineSpec (the worked example + the mandatory
negative controls).

Core-only (imports SchemaCore.Update + Machines.Dsl — both C1, the
cone rule; no mathlib, no Batteries).
-/

import SchemaCore.Update
import Machines.Dsl

namespace SchemaCore

/-! ## The declaration data -/

/-- One declared transition: its event name and the edge
    (from-state → to-state), as NAMES (the codes ride the states
    list's order). -/
structure EntityTransition where
  /-- The event's name (the Label ctor + the journal's event face). -/
  name : String
  /-- The edge's source state (a declared state). -/
  src : String
  /-- The edge's target state (a declared state). -/
  dst : String
deriving Repr, BEq, DecidableEq, Inhabited

/-- The preset's declaration row: the generated machine's name, the
    record + the u64 state column it rides, the states (CODE ORDER —
    code = index), the transitions, and the record's declared key
    (the keys lane's resolution rung; `none` = unkeyed). -/
structure EntityMachineDecl where
  /-- The generated machine's name. -/
  machine : String
  /-- The record's registry name (the provenance + key-resolution face). -/
  record : String
  /-- The state column's name (must be a `u64` column — the CODE
      discipline: the wire carries the code, the enum is the
      host-side discipline). -/
  stateCol : String
  /-- The states, in code order. -/
  states : List String
  /-- The declared transitions. -/
  transitions : List EntityTransition
  /-- The record's declared key, if any. -/
  key? : Option String := none

/-- The state CODE: the declared state's index in the states list
    (the u64 the transition deltas write). `none` = not a declared
    state (the command gates this; the decl-level Diag route reports
    it — unreachable for command-generated data). -/
def EntityMachineDecl.stateCode (d : EntityMachineDecl) (s : String) :
    Option UInt64 :=
  ((d.states.zip (List.range d.states.length)).find? (fun p => p.1 == s)).map
    (fun p => UInt64.ofNat p.2)

/-- The DECLARED edge table: (event, from-code, to-code) per
    transition whose endpoints are declared — the journal's closed
    world (the antijoin's edge side). -/
def EntityMachineDecl.edges (d : EntityMachineDecl) :
    List (String × UInt64 × UInt64) :=
  d.transitions.filterMap fun t =>
    (d.stateCode t.src).bind fun f => (d.stateCode t.dst).map fun tt => (t.name, f, tt)

/-! ## The state column's path — the write spine's runtime face

The update lane's `ColPath` is the GADT write spine; a keyed update to
a column that does not exist, or exists at another type, is
unconstructible. The preset builds the path from DECLARED data —
`findColPath` is the ONE lookup, and its `none` is the refusal (never
a fabricated path). -/

/-- The path for the column named `n` over the field list `fs`:
    `some ⟨t, p⟩` when the column exists (first match wins — the
    registry's fields-nodup obligation is what makes the first match
    THE match), `none` = the refusal. -/
def findColPath (fs : List Field) (n : String) :
    Option ((t : Ty) × ColPath n t fs) := by
  cases fs with
  | nil => exact none
  | cons f rest =>
      cases f with
      | mk fn ft =>
          if h : fn = n then
            subst h
            exact some ⟨ft, ColPath.here (fs := rest)⟩
          else
            exact (findColPath rest n).map (fun q => ⟨q.1, ColPath.there q.2⟩)

/-- A column path's column IS named `n` — the lemma the write-read
    coherence needs (the path's existence places `n` in the field
    list). -/
theorem colPath_name_mem {n : String} {t : Ty} :
    ∀ {fs : List Field} (_p : ColPath n t fs), n ∈ (fs.map (·.name)) := by
  intro fs p
  induction p with
  | here => simp
  | @there f fs' p' ih => exact List.mem_cons_of_mem _ ih

/-- THE WRITE-READ COHERENCE: a write to the path's column READS BACK
    exactly the written value (the preset's moves-law substrate). The
    fields-nodup hypothesis is load-bearing: without it a second
    column named `n` would shadow the read (the projection is
    first-match). The record's registration carries the nodup
    obligation (`Item.fieldNodupObligation`) — the composition's
    premise, discharged at the instance. -/
theorem ColPath.set_project?_self {n : String} {t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (row : RowVals fs) (v : Value t),
      ((fs.map (·.name))).Nodup →
      RowVals.project? fs (p.set row v) n = some ⟨t, v⟩ := by
  intro fs p
  induction p with
  | here =>
      intro row v _
      cases row with
      | cons _ vs =>
          simp only [ColPath.set, RowVals.project?, beq_self_eq_true]
          rfl
  | @there f fs' p' ih =>
      intro row v hnd
      cases row with
      | cons v0 vs =>
          have hmem : n ∈ (fs'.map (·.name)) := colPath_name_mem p'
          have hnd2 : ((fs'.map (·.name))).Nodup := (List.nodup_cons.mp hnd).2
          have hhead : f.name ∉ (fs'.map (·.name)) := (List.nodup_cons.mp hnd).1
          have hne : (f.name == n) = false := by
            cases hbeq : (f.name == n) with
            | true => exact absurd ((beq_iff_eq.mp hbeq) ▸ hmem) hhead
            | false => rfl
          simp only [ColPath.set, RowVals.project?, hne]
          exact ih vs v hnd2

/-! ## The keyed transitions — the update lane's composition

One transition = ONE keyed update on the state column: guard
`status = from`, set `status := to` (transitions ARE deltas on the
state column; the code discipline makes the delta a u64 write). The
`SetClause`'s GADT index pins the write to the DECLARED column; the
`Option` is the closed-world refusal (a missing or mistyped state
column yields `none` — the Diag envelope reports it, never silence). -/

/-- The transition's keyed update: the delta on the state column.
    `none` = the refusal (the state column is missing, mistyped, or a
    transition endpoint is undeclared). -/
def transitionUpdate (d : EntityMachineDecl) (fs : List Field)
    (t : EntityTransition) : Option (UpdateItem fs) :=
  match findColPath fs d.stateCol with
  | some ⟨.u64, p⟩ =>
      match d.stateCode t.src, d.stateCode t.dst with
      | some fc, some tc =>
          some { record := d.record
                 name := t.name
                 guard := .u64EqLit d.stateCol fc
                 sets := [{ field := ⟨d.stateCol, .u64⟩, path := p
                            value := .u64 tc }] }
      | _, _ => none
  | _ => none

/-- THE BUILDER'S SHAPE: when the state column resolves (`findColPath`
    = `some` at `.u64`) and both endpoints are declared, the built
    keyed update IS the delta `guard status = from, set status := to`
    — the preset's one builder, pinned once. -/
theorem transitionUpdate_eq_some {d : EntityMachineDecl} {fs : List Field}
    {t : EntityTransition} {p : ColPath d.stateCol .u64 fs}
    {fc tc : UInt64}
    (hp : findColPath fs d.stateCol = some ⟨.u64, p⟩)
    (hc : d.stateCode t.src = some fc)
    (hd : d.stateCode t.dst = some tc) :
    transitionUpdate d fs t = some
      { record := d.record, name := t.name
        guard := .u64EqLit d.stateCol fc
        sets := [{ field := ⟨d.stateCol, .u64⟩, path := p, value := .u64 tc }] } := by
  simp only [transitionUpdate, hp, hc, hd]

/-- All of the decl's transitions as keyed updates: `none` = some
    transition refused (the whole batch refuses — the preset's
    all-or-nothing rule). -/
def declUpdates (d : EntityMachineDecl) (fs : List Field) :
    Option (List (UpdateItem fs)) :=
  d.transitions.foldr (fun t acc =>
      match transitionUpdate d fs t with
      | some u => acc.map (fun us => u :: us)
      | none => none) (some [])

/-! ## The legality discipline — the journal antijoin + replay

The legality relation: an event sequence is legal from `init` iff the
machine's run ACCEPTS it (membership in the machine's language — the
regular-language row; the DFA check needs no automata toolkit at this
granularity). The JOURNAL is the delta log; its check is the ANTIJOIN
against the edge table; `journalReplay` folds the journal through the step
function. -/

/-- The journal entry: a transition's DELTA on the state column —
    (event, from-state, to-state). -/
abbrev JournalEntry (L S : Type) := L × S × S

/-- THE LEGALITY RELATION, executable: the run accepts (DFA
    membership). -/
def legalFrom {S I : Type} (m : Machines.MachineWithInv S I) (init : S)
    (seq : List I) : Bool :=
  (m.toMachine.run init seq).isSome

/-- THE JOURNAL ANTIJOIN CHECK: the journal's entries with NO matching
    row in the edge table — the illegal deltas, isolated (the
    antijoin; legality check = membership). -/
def journalAntijoin [BEq L] [BEq S] (edges journal : List (JournalEntry L S)) :
    List (JournalEntry L S) :=
  journal.filter (fun j => !edges.any (fun e => e == j))

/-- Journal legality: the antijoin is EMPTY — every delta is a machine
    edge (the membership reading of the regular language). -/
def legalJournal [BEq L] [BEq S] (edges journal : List (JournalEntry L S)) :
    Bool :=
  (journalAntijoin edges journal).isEmpty

/-- THE ANTIJOIN LAW: the journal is legal iff every entry is an edge
    — both directions, proved once, cited by every generated machine. -/
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

/-- THE STEP FACE of the edge table: the table as a lookup — one
    target per (event, from-state), the FIRST match (the determinacy
    rung below is what makes the first match THE match). -/
def edgeStep (edges : List (String × UInt64 × UInt64)) :
    UInt64 → String → Option UInt64 :=
  fun fromSt ev =>
    (edges.find? (fun e => e.1 == ev && e.2.1 == fromSt)).map (·.2.2)

/-- THE DETERMINACY RUNG, as data: every edge is the one its lookup
    finds — no (event, from-state) pair points at two targets. (The
    transition names being unique already implies this — the edge's
    event IS the transition's name; the rung is checked, not
    assumed.) -/
def edgesDet (edges : List (String × UInt64 × UInt64)) : Bool :=
  edges.all fun e => edgeStep edges e.2.1 e.1 == some e.2.2

/-- THE DETERMINACY LAW: a determined edge table's lookup HONESTLY
    realizes every row — the premise the replay law consumes. -/
theorem edgesDet_honest (edges : List (String × UInt64 × UInt64))
    (h : edgesDet edges = true) :
    ∀ e ∈ edges, edgeStep edges e.2.1 e.1 = some e.2.2 := by
  rw [edgesDet, List.all_eq_true] at h
  intro e he
  exact beq_iff_eq.mp (h e he)

/-- Replay: fold the journal through the step function — each entry
    must fire from the CURRENT state and land on its recorded delta.
    `none` = a broken journal (a stale delta, an illegal edge — replay
    is the audit, the antijoin is the gate). -/
def journalReplay [BEq L] [BEq S] (step : S → L → Option S) (init : S) :
    List (JournalEntry L S) → Option S
  | [] => some init
  | (l, _, s₁) :: rest =>
      match step init l with
      | some s => if s == s₁ then journalReplay step s rest else none
      | none => none

/-- The journal CHAINS from `init`: each entry's from-state is the
    previous entry's to-state (the deltas connect). -/
def ChainsFrom {L S : Type} (init : S) : List (JournalEntry L S) → Prop
  | [] => True
  | (_, s₀, s₁) :: rest => init = s₀ ∧ ChainsFrom s₁ rest

/-- THE REPLAY LAW: a journal that passes the antijoin check AND
    chains from `init` replays to a final state — legality + chaining
    means the log is executable. Proved ONCE; every generated machine
    instantiates it with its own edge table. -/
theorem replay_of_legalJournal [BEq L] [BEq S] [LawfulBEq L] [LawfulBEq S]
    (step : S → L → Option S) (edges : List (JournalEntry L S))
    (honest : ∀ e ∈ edges, step e.2.1 e.1 = some e.2.2)
    (journal : List (JournalEntry L S))
    (hlegal : legalJournal edges journal = true) (init : S)
    (hchain : ChainsFrom init journal) :
    ∃ fin, journalReplay step init journal = some fin := by
  induction journal generalizing init with
  | nil => exact ⟨init, rfl⟩
  | cons j rest ih =>
      cases hchain with
      | intro h₀ hrest =>
          subst h₀
          have hmem : j ∈ edges :=
            (legalJournal_iff edges (j :: rest)).mp hlegal j List.mem_cons_self
          have hstep : step j.2.1 j.1 = some j.2.2 := honest j hmem
          have hlegal' : legalJournal edges rest = true :=
            (legalJournal_iff edges rest).mpr fun j' hj' =>
              (legalJournal_iff edges (j :: rest)).mp hlegal j'
                (List.mem_cons_of_mem _ hj')
          simp only [journalReplay, hstep, beq_self_eq_true]
          exact ih hlegal' j.2.2 hrest

/-- THE GENERATED TABLE IS HONEST: every row of the machine!-generated
    transition table (the `List.flatMap`/`List.filterMap` fold) is a
    real step of the machine. One proof for every generated machine —
    the command cites it with `rfl` against the table's defining
    fold. -/
theorem trans_honest {S I : Type} (m : Machines.MachineWithInv S I)
    (labels : List I) (states : List S) (trans : List (I × S × S))
    (hdef : trans = _root_.List.flatMap
      (fun l => _root_.List.filterMap
        (fun s => _root_.Option.map (fun s' => (l, s, s'))
          (_root_.Machines.MachineWithInv.step? m s l))
        states)
      labels) :
    ∀ e ∈ trans, _root_.Machines.MachineWithInv.step? m e.2.1 e.1 = some e.2.2 := by
  intro e he
  rw [hdef, List.mem_flatMap] at he
  obtain ⟨l, hl, hfm⟩ := he
  rw [List.mem_filterMap] at hfm
  obtain ⟨s, hst, hmap⟩ := hfm
  cases hstep : _root_.Machines.MachineWithInv.step? m s l with
  | none => rw [hstep] at hmap; simp at hmap
  | some s' =>
      rw [hstep] at hmap
      have he' : (l, s, s') = e := Option.some.inj hmap
      subst he'
      show _root_.Machines.MachineWithInv.step? m s l = some s'
      exact hstep

/-! ## The WF checker — the Diag envelope + the Prop side

The rung cascade, all closed-world (each refusal enumerates the valid
space + the ONE did-you-mean engine):

1. the COLUMN rung — the state column exists and is `u64` (EM0001);
2. the ENDPOINT rung — every transition's src/dst is a declared state
   (EM0002);
3. the NAME rung — the transition names are distinct (the Label's
   ctors are one per name — EM0003, via the Keys lane's `dupNames`);
4. the KEY rung — the declared key resolves in the keys lane's
   declaration set (EM0004, `keyDeclFor` — ONE reading shared with the
   update lane). -/

/-- The preset's E-codes (allocated from the PERSISTED registry: the
    EM family — never a bare string). -/
def eEM0001 : Kit.ECode := ⟨"EM0001"⟩
def eEM0002 : Kit.ECode := ⟨"EM0002"⟩
def eEM0003 : Kit.ECode := ⟨"EM0003"⟩
def eEM0004 : Kit.ECode := ⟨"EM0004"⟩

/-- The COLUMN rung's diagnostics: the state column must exist and be
    `u64` (the state CODE discipline). -/
def colDiags (d : EntityMachineDecl) (fs : List Field) : List Kit.Diag :=
  match findColPath fs d.stateCol with
  | some ⟨.u64, _⟩ => []
  | some ⟨_, _⟩ =>
      [Kit.Diag.closedWorld eEM0001
        s!"entity machine `{d.machine}`: the state column `{d.stateCol}` must be \
          `u64` — the state CODE discipline (transitions are u64 deltas on it; \
          the wire record carries the code, the enum is the host-side discipline)"
        .error d.stateCol ((fs.filter (fun g => g.ty == .u64)).map (·.name))]
  | none =>
      [Kit.Diag.closedWorld eEM0001
        s!"entity machine `{d.machine}`: `{d.stateCol}` is not a column of \
          `{d.record}` — the state column must exist"
        .error d.stateCol (fs.map (·.name))]

/-- The checker face of the COLUMN rung (the bridge's Bool side). -/
def entityColU64 (fs : List Field) (col : String) : Bool :=
  match findColPath fs col with
  | some ⟨.u64, _⟩ => true
  | _ => false

/-- One transition's ENDPOINT diagnostics. -/
def endpointsPart (d : EntityMachineDecl) (t : EntityTransition) :
    List Kit.Diag :=
  (if d.states.contains t.src then [] else
      [Kit.Diag.closedWorld eEM0002
        s!"entity machine `{d.machine}`: transition `{t.name}`: `{t.src}` is not \
          a declared state"
        .error t.src d.states])
    ++ (if d.states.contains t.dst then [] else
      [Kit.Diag.closedWorld eEM0002
        s!"entity machine `{d.machine}`: transition `{t.name}`: `{t.dst}` is not \
          a declared state"
        .error t.dst d.states])

/-- The checker face of the ENDPOINT rung. -/
def endpointsDeclared (d : EntityMachineDecl) : Bool :=
  d.transitions.all fun t => d.states.contains t.src && d.states.contains t.dst

/-- The checker face of the NAME rung (the Keys lane's `dupNames` —
    the ONE duplicate detector). -/
def EntityMachineDecl.namesNodup (d : EntityMachineDecl) : Bool :=
  (dupNames (d.transitions.map (·.name))).isEmpty

/-- The checker face of the KEY rung (`keyDeclFor` — the keys lane's
    resolution, ONE reading shared with the update lane's WF rung). -/
def entityKeyOk (d : EntityMachineDecl) (decls : List KeyDecl) : Bool :=
  match d.key? with
  | none => true
  | some k => (keyDeclFor decls d.record k).isSome

/-- The KEY rung's diagnostics. -/
def keyPart (d : EntityMachineDecl) (decls : List KeyDecl) : List Kit.Diag :=
  match d.key? with
  | none => []
  | some k =>
      match keyDeclFor decls d.record k with
      | some _ => []
      | none =>
          [Kit.Diag.closedWorld eEM0004
            s!"entity machine `{d.machine}`: keys on `{k}` — no declared key of \
              `{d.record}` matches"
            .error k ((decls.filter (fun kd => kd.record == d.record)).map (·.key))]

/-- The NAME rung's diagnostics. -/
def namesPart (d : EntityMachineDecl) : List Kit.Diag :=
  if d.namesNodup then [] else
    [Kit.Diag.closedWorld eEM0003
      s!"entity machine `{d.machine}`: duplicate transition name — the events \
        are the Label constructors (one ctor per name)"
      .error ((dupNames (d.transitions.map (·.name))).headD "")
      ((d.transitions.map (·.name)).eraseDups)]

/-- The decl's WF diagnostics (the rung cascade; empty = well formed). -/
def entityDiags (d : EntityMachineDecl) (fs : List Field)
    (decls : List KeyDecl) : List Kit.Diag :=
  colDiags d fs
    ++ (d.transitions.flatMap (endpointsPart d))
    ++ namesPart d
    ++ keyPart d decls

/-- The ENDPOINT rung's chunk law (one transition). -/
theorem endpointsPart_nil_iff (d : EntityMachineDecl) (t : EntityTransition) :
    endpointsPart d t = [] ↔
      (d.states.contains t.src && d.states.contains t.dst) = true := by
  unfold endpointsPart
  cases hs : d.states.contains t.src <;> cases hd : d.states.contains t.dst <;> simp

/-- The COLUMN rung's chunk law. -/
theorem colDiags_nil_iff (d : EntityMachineDecl) (fs : List Field) :
    colDiags d fs = [] ↔ entityColU64 fs d.stateCol = true := by
  unfold colDiags entityColU64
  cases hb : findColPath fs d.stateCol with
  | none => simp
  | some q =>
      cases q with
      | mk t p => cases t <;> simp

/-- THE NAME rung's chunk law. -/
theorem namesPart_nil_iff (d : EntityMachineDecl) :
    namesPart d = [] ↔ d.namesNodup = true := by
  unfold namesPart
  cases hb : d.namesNodup <;> simp

/-- THE KEY rung's chunk law. -/
theorem keyPart_nil_iff (d : EntityMachineDecl) (decls : List KeyDecl) :
    keyPart d decls = [] ↔ entityKeyOk d decls = true := by
  unfold keyPart entityKeyOk
  cases d.key? with
  | none => simp
  | some k =>
      cases hb : keyDeclFor decls d.record k with
      | none => simp [hb]
      | some kd => simp [hb]

/-- The WF relation (the Prop side of the cascade) — the table's WF
    obligation's content. -/
structure EntityWf (d : EntityMachineDecl) (fs : List Field)
    (decls : List KeyDecl) : Prop where
  /-- The state column exists and is `u64`. -/
  colU64 : entityColU64 fs d.stateCol = true
  /-- Every transition's endpoints are declared states. -/
  endpoints : endpointsDeclared d = true
  /-- The transition names are distinct. -/
  names : d.namesNodup = true
  /-- The declared key resolves (or there is none). -/
  keyOk : entityKeyOk d decls = true

/-- THE WF BRIDGE (pattern #1): the checker never lies in either
    direction — an empty Diag envelope IS the WF relation. -/
theorem entityDiags_eq_nil_iff (d : EntityMachineDecl) (fs : List Field)
    (decls : List KeyDecl) :
    entityDiags d fs decls = [] ↔ EntityWf d fs decls := by
  constructor
  · intro h
    obtain ⟨h3, h4⟩ := List.eq_nil_of_append_eq_nil h
    obtain ⟨h5, h6⟩ := List.eq_nil_of_append_eq_nil h3
    obtain ⟨h1, h2⟩ := List.eq_nil_of_append_eq_nil h5
    exact ⟨(colDiags_nil_iff d fs).mp h1,
      List.all_eq_true.mpr (fun t ht =>
        (endpointsPart_nil_iff d t).mp (List.flatMap_eq_nil_iff.mp h2 t ht)),
      (namesPart_nil_iff d).mp h6,
      (keyPart_nil_iff d decls).mp h4⟩
  · rintro ⟨hcol, htr, hnames, hkey⟩
    refine List.append_eq_nil_iff.mpr ⟨?_, (keyPart_nil_iff d decls).mpr hkey⟩
    refine List.append_eq_nil_iff.mpr ⟨?_, (namesPart_nil_iff d).mpr hnames⟩
    refine List.append_eq_nil_iff.mpr ⟨(colDiags_nil_iff d fs).mpr hcol, ?_⟩
    exact List.flatMap_eq_nil_iff.mpr (fun t ht =>
      (endpointsPart_nil_iff d t).mpr ((List.all_eq_true.mp htr) t ht))
/-! ## The claims + the obligation rows (the Prop-indexed view)

The entity-machine obligation's fact: a transition's keyed update
FIRES on the from-state row (`fires` — the guard reads the pinned
code), or MOVES the state column to the to-code (`moves` — the
postcondition); plus the TABLE's WF (`tableWf` — the Diag envelope is
empty). The claim IS the obligation's type index (Kit.Obligation) — a
discharge proves the ACTUAL property, never a claim-shaped name. -/

/-- The guard's self-read: a `u64EqLit` guard on a row whose column
    reads the literal passes (the fires-law's small step). -/
theorem validates_u64EqLit_of_read {fs : List Field} {row : RowVals fs}
    {n : String} {v : UInt64}
    (h : (RowVals.project? fs row n).bind FieldVal.u64? = some v) :
    validates (.u64EqLit n v) row = true := by
  simp only [validates, Pred.check]
  rw [h]
  exact beq_self_eq_true v

/-- The fires content: the guard's verdict on the from-pinned row
    (the default-row discipline — the ONE row the claim materializes;
    the state column written to the from-code). The pattern is the
    GADT's shape discipline: the SET clause's column must be `u64` —
    anything else refuses (`false`). -/
def firesOf {fs : List Field} (u : UpdateItem fs) (fc : UInt64) : Bool :=
  match u.sets with
  | [{ field := ⟨_, .u64⟩, path := p, value := _ }] =>
      match defaultRow? fs with
      | some row => validates u.guard (p.set row (.u64 fc))
      | none => false
  | _ => false

/-- The moves content: the state column's post-update read equals the
    to-code (the postcondition, on the same pinned row). -/
def movesOf {fs : List Field} (u : UpdateItem fs) (fc tc : UInt64) : Bool :=
  match u.sets with
  | [{ field := ⟨n, .u64⟩, path := p, value := _ }] =>
      match defaultRow? fs with
      | some row =>
          ((RowVals.project? fs (applySets u.sets (p.set row (.u64 fc))) n).bind
            FieldVal.u64?) == some tc
      | none => false
  | _ => false

/-- THE FIRES LAW (proved once): a keyed update whose single SET clause
    writes the guard's own u64 column FIRES on its from-row — the
    write-read coherence (`ColPath.set_project?_self`) + the guard's
    self-read. Every generated machine instantiates this. -/
theorem firesOf_shape {fs : List Field} {u : UpdateItem fs} {fc : UInt64}
    {n : String} {p : ColPath n .u64 fs} {tc : UInt64}
    (hsets : u.sets = [{ field := ⟨n, .u64⟩, path := p, value := .u64 tc }])
    (hg : u.guard = .u64EqLit n fc)
    (hnd : ((fs.map (·.name))).Nodup)
    (hrow : defaultRow? fs ≠ none) :
    firesOf u fc = true := by
  simp only [firesOf, hsets]
  cases hd : defaultRow? fs with
  | none => exact absurd hd hrow
  | some row =>
      have hread : (RowVals.project? fs (p.set row (.u64 fc)) n).bind
          FieldVal.u64? = some fc := by
        rw [ColPath.set_project?_self p row (.u64 fc) hnd]
        rfl
      rw [hg]
      exact validates_u64EqLit_of_read hread

/-- THE MOVES LAW (proved once): the same update MOVES the state
    column to the to-code — the write, then the read-back. Every
    generated machine instantiates this. -/
theorem movesOf_shape {fs : List Field} {u : UpdateItem fs} {fc tc : UInt64}
    {n : String} {p : ColPath n .u64 fs}
    (hsets : u.sets = [{ field := ⟨n, .u64⟩, path := p, value := .u64 tc }])
    (hnd : ((fs.map (·.name))).Nodup)
    (hrow : defaultRow? fs ≠ none) :
    movesOf u fc tc = true := by
  simp only [movesOf, hsets]
  cases hd : defaultRow? fs with
  | none => exact absurd hd hrow
  | some row =>
      have hread := ColPath.set_project?_self p
        (p.set row (.u64 fc)) (.u64 tc) hnd
      show ((RowVals.project? fs
        (p.set (p.set row (.u64 fc)) (.u64 tc)) n).bind
        FieldVal.u64?) == some tc
      rw [hread]
      exact beq_self_eq_true (some tc)

/-- The entity-machine claim: fires / moves (the transition's keyed
    update, resolved from the declaration) / the table's WF. -/
inductive EntityClaim where
  /-- The transition's update fires on the from-pinned row. -/
  | fires (d : EntityMachineDecl) (fs : List Field) (t : EntityTransition)
      (fromCode : UInt64)
  /-- The transition's update moves the state column from-code → to-code. -/
  | moves (d : EntityMachineDecl) (fs : List Field) (t : EntityTransition)
      (fromCode toCode : UInt64)
  /-- The declared table is well formed (the Diag envelope is empty). -/
  | tableWf (d : EntityMachineDecl) (fs : List Field) (decls : List KeyDecl)

/-- The claim's content, executable: the transition's keyed update is
    resolved from the declaration (`transitionUpdate`) and the fires/
    moves content read off it; the WF claim is the Diag envelope's
    emptiness. -/
def EntityClaim.holds : EntityClaim → Bool
  | .fires d fs t fc =>
      match transitionUpdate d fs t with
      | some u => firesOf u fc
      | none => false
  | .moves d fs t fc tc =>
      match transitionUpdate d fs t with
      | some u => movesOf u fc tc
      | none => false
  | .tableWf d fs decls => (entityDiags d fs decls).isEmpty

/-- The claims decide over concrete declarations (the decidableNow
    rung's instance). -/
instance entityClaimDecidable (c : EntityClaim) : Decidable (c.holds = true) :=
  instDecidableEqBool c.holds true

/-- THE FIRES LAW, at the claim (proved once, instantiated per
    transition): when the state column resolves and the endpoints are
    declared, the transition FIRES on its from-row. -/
theorem fires_of_transition {d : EntityMachineDecl} {fs : List Field}
    {t : EntityTransition} {p : ColPath d.stateCol .u64 fs}
    {fc tc : UInt64}
    (hp : findColPath fs d.stateCol = some ⟨.u64, p⟩)
    (hc : d.stateCode t.src = some fc)
    (hd : d.stateCode t.dst = some tc)
    (hnd : ((fs.map (·.name))).Nodup)
    (hrow : defaultRow? fs ≠ none) :
    (EntityClaim.fires d fs t fc).holds = true := by
  simp only [EntityClaim.holds, transitionUpdate, hp, hc, hd]
  exact firesOf_shape rfl rfl hnd hrow

/-- THE MOVES LAW, at the claim: the transition MOVES the state column
    to the to-code. -/
theorem moves_of_transition {d : EntityMachineDecl} {fs : List Field}
    {t : EntityTransition} {p : ColPath d.stateCol .u64 fs}
    {fc tc : UInt64}
    (hp : findColPath fs d.stateCol = some ⟨.u64, p⟩)
    (hc : d.stateCode t.src = some fc)
    (hd : d.stateCode t.dst = some tc)
    (hnd : ((fs.map (·.name))).Nodup)
    (hrow : defaultRow? fs ≠ none) :
    (EntityClaim.moves d fs t fc tc).holds = true := by
  simp only [EntityClaim.holds, transitionUpdate, hp, hc, hd]
  exact movesOf_shape rfl hnd hrow

/-- The entity-machine obligation ROW: the claim-as-data paired with
    the Prop-indexed obligation AT that claim (the row's discharge
    proves the paired claim, never a name). -/
abbrev EntityOblRow := (c : EntityClaim) × Kit.Obligation EntityClaim (c.holds = true)

/-- The row's constructor: the decidableNow tier (entity claims are
    decidable row-data predicates over the pinned from-row). -/
def entityRow (label : String) (c : EntityClaim) : EntityOblRow :=
  ⟨c, { label := label, tier := .decidableNow, payload := c,
        provenance := `SchemaCore }⟩

/-- THE DISCHARGE — the kit's decidableNow backend at the row; `none`
    is the loud gap (a false claim — the backend refuses, it does not
    fabricate evidence). -/
def EntityOblRow.discharge (r : EntityOblRow) : Option Kit.Evidence :=
  r.2.decideDischarge

/-- The discharge's SOUNDNESS — the kit backend's theorem, cited (at
    the row CONSTRUCTOR, where the tier is the literal `.decidableNow`
    and reduces). -/
theorem entityRow_discharge_sound (label : String) (c : EntityClaim)
    (h : (entityRow label c).discharge = some (.decided true)) : c.holds = true :=
  Kit.Obligation.decideDischarge_sound (entityRow label c).2 rfl h

/-- The discharge's COMPLETENESS — a true claim fires the backend. -/
theorem entityRow_discharge_of_claim (label : String) (c : EntityClaim)
    (hc : c.holds = true) :
    (entityRow label c).discharge = some (.decided true) :=
  Kit.Obligation.decideDischarge_of_claim (entityRow label c).2 rfl hc

/-- One transition's obligation view: the fires row + the moves row
    (the guard + the postcondition, each at `decidableNow`). -/
def transitionObligations (d : EntityMachineDecl) (fs : List Field)
    (t : EntityTransition) (fc tc : UInt64) : List EntityOblRow :=
  [ entityRow s!"{d.machine}.{t.name}-fires" (.fires d fs t fc)
  , entityRow s!"{d.machine}.{t.name}-moves" (.moves d fs t fc tc) ]


end SchemaCore

/-! ## The command — `schema_entity_machine` (the meta mount)

    schema_entity_machine orderMachine for Order where
      states: [draft, placed, shipped, delivered, void]
      fields: [{ name := "id", ty := .u64 }, { name := "status", ty := .u64 }]
      column: status
      key: id
      Inv: fun s => s ≠ .void
      initial: draft
      transition: place (draft → placed)
      …

One declaration, the generated surface (names under `<m>`):

1. the `machine!` invocation with the FULL entourage (the state enum +
   the Label inductive + the EventSpec family + the table + the
   `TableStep?_eq_step?` tie + the `DecidablePred` + the battery
   registration); `Inv:` defaults to `True` (the closed enum IS the
   invariant — an author-supplied `Inv:` overrides; the battery's
   non-vacuity row reports a vacuous default honestly);
2. `<m>Fields`/`<m>Keys` — the record's fields + the keys lane's
   declaration set;
3. `<m>Decl` — the declaration row (the provenance data);
4. `<m>Updates` — the per-transition keyed updates (the deltas on the
   state column);
5. `<m>Edges` + `<m>EdgesDet` — the declared edge table (codes) + the
   determinacy rung, decided;
6. `<m>Diags` — the WF Diag envelope;
7. `<m>Trans_honest` — the generated table's honesty (cites
   `trans_honest` with `rfl`);
8. `<m>LegalFrom`/`<m>Antijoin`/`<m>LegalJournal`/`<m>Replay` +
   `<m>Replay_ok` — the legality discipline (the replay law cites the
   generic theorem with the decided determinacy premise);
9. `<m>StateCode`/`<m>EventName` + `<m>Edges_generated` — the code
   bridge + THE CODE TIE: the declared edge table IS the generated
   machine's table, under the code bridge;
10. `<m>Obligations` + `<m>Obligations_fire` — the decidableNow rows
    (fires/moves per transition + the table's WF), discharging under
    the record's declared premises (the conditional is the honesty:
    a refused decl's rows do NOT discharge — the loud gap);
11. `<m>Preserves`/`<m>PreservesRow` — the invariant-preservation
    obligation: the Prop-indexed row at the `.provedAtElab` tier,
    discharged by CITING `MachineWithInv.step?_preserves` (proved
    once, in Machines.Events).

Word-token discipline: the clauses are colon-suffixed (the `machine!`
lesson — the global token table is untouched, and the keyword tokens
are what stop the term-led clauses' juxtaposition); the edge separator
is the `→` punctuation (never a common word). -/

open Lean Lean.Elab.Command in
/-- `.ctor` — the dotted constructor reference (term AND pattern). -/
private def SchemaCore.dotRef (id : TSyntax `ident) : Lean.Term :=
  ⟨Syntax.node .none ``Lean.Parser.Term.dotIdent #[mkAtom ".", id.raw]⟩

open Lean in
/-- A Lean term holding a string literal (the splice helper). -/
private def SchemaCore.strT (s : String) : Lean.Term := quote s

open Lean in
/-- A Lean term holding a UInt64-sized natural literal (the code splice
    helper — the arm's expected type fixes the UInt64). -/
private def SchemaCore.natT (n : Nat) : Lean.Term := quote n

namespace SchemaCore.Meta

/-- The clause category (the Machines.Dsl clause-kit discipline — one
    named rule per clause, the low-priority unknown-clause catch-all
    rejecting typos with a did-you-mean at ELABORATION). -/
declare_syntax_cat entityMachineClause

/-- The state enumeration, in code order. -/
syntax (name := emStatesClause) "states:" "[" ident,* "]" : entityMachineClause

/-- The record's fields (a `List Field` term). -/
syntax (name := emFieldsClause) "fields:" term : entityMachineClause

/-- The state column (a `u64` column of the record). -/
syntax (name := emColumnClause) "column:" ident : entityMachineClause

/-- The record's declared key (the keys lane's resolution rung). -/
syntax (name := emKeyClause) "key:" ident : entityMachineClause

/-- The machine's invariant (optional — defaults to `True`, the closed
    enum IS the invariant; the battery's non-vacuity row reports a
    vacuous default honestly). -/
syntax (name := emInvClause) "Inv:" term : entityMachineClause

/-- The lifecycle's start state (exactly one). -/
syntax (name := emInitialClause) "initial:" ident : entityMachineClause

/-- One transition clause: `transition: <name> (<src> → <dst>)` — bare
    state names (the command emits the dotted refs). -/
syntax (name := emTransitionClause) "transition:" ident " (" ident " → " ident ")"
  : entityMachineClause

/-- The unknown-clause catch-all (the clause-kit discipline): low
    priority, so the named clauses win; anything else well-formed is
    rejected at ELABORATION with the legal-clause enumeration + the
    did-you-mean. -/
syntax (name := emUnknownClause) (priority := low) ident " : " term : entityMachineClause

/-- THE AUTHORING SURFACE (see the section header). The body is a
    uniform CLAUSE LIST (the Machines.Dsl clause-kit discipline). -/
syntax (name := schemaEntityMachineCmd) "schema_entity_machine " ident
  " for " ident " where " entityMachineClause* : command

/-- The legal-clause list (the unknown-clause refusal's closed world). -/
def emLegalClauses : List String :=
  ["states", "fields", "column", "key", "Inv", "initial", "transition"]

open Lean Lean.Elab.Command in
/-- The elaborator: sweep + gate + emit (the generated surface is the
    section header's list). -/
@[command_elab SchemaCore.Meta.schemaEntityMachineCmd]
def elabSchemaEntityMachine : Lean.Elab.Command.CommandElab := fun stx => do
  -- stx = [cmd, name, " for ", recId, " where ", clausesNode] — the clauses
  -- arrive in SOURCE ORDER; the sweep dispatches on the clause KIND.
  let base : TSyntax `ident := ⟨stx[1]!⟩
  let baseName := stx[1]!.getId.toString
  let recName := stx[3]!.getId.toString
  let mut states? : Option (Array Syntax) := none
  let mut fields? : Option Syntax := none
  let mut col? : Option Syntax := none
  let mut key? : Option Syntax := none
  let mut inv? : Option Syntax := none
  let mut init? : Option Syntax := none
  let mut trs : Array Syntax := #[]
  for c in stx[5]!.getArgs do
    match c.getKind with
    | ``emStatesClause =>
        if states?.isSome then
          throwErrorAt c s!"schema_entity_machine `{baseName}`: duplicate \
            `states:` clause — at most one"
        states? := some c[2]!.getSepArgs
    | ``emFieldsClause =>
        if fields?.isSome then
          throwErrorAt c s!"schema_entity_machine `{baseName}`: duplicate \
            `fields:` clause — at most one"
        fields? := some c[1]!
    | ``emColumnClause =>
        if col?.isSome then
          throwErrorAt c s!"schema_entity_machine `{baseName}`: duplicate \
            `column:` clause — at most one"
        col? := some c[1]!
    | ``emKeyClause =>
        if key?.isSome then
          throwErrorAt c s!"schema_entity_machine `{baseName}`: duplicate \
            `key:` clause — at most one"
        key? := some c[1]!
    | ``emInvClause =>
        if inv?.isSome then
          throwErrorAt c s!"schema_entity_machine `{baseName}`: duplicate \
            `Inv:` clause — at most one"
        inv? := some c[1]!
    | ``emInitialClause =>
        if init?.isSome then
          throwErrorAt c s!"schema_entity_machine `{baseName}`: duplicate \
            `initial:` clause — exactly one"
        init? := some c[1]!
    | ``emTransitionClause => trs := trs.push c
    | ``emUnknownClause =>
        throwErrorAt c s!"schema_entity_machine `{baseName}`: unknown clause \
          `{c[0]!.getId.toString}:` — legal clauses: \
          {String.intercalate ", " (emLegalClauses.map (fun l => s!"`{l}:`"))}\
          {TextKit.suggestSuffix c[0]!.getId.toString emLegalClauses}"
    | _ => Lean.Elab.throwUnsupportedSyntax
  let some stateArr := states?
    | throwError s!"schema_entity_machine `{baseName}`: missing `states:` \
        clause — the state enumeration, in code order"
  if stateArr.isEmpty then
    throwError s!"schema_entity_machine `{baseName}`: `states:` needs at \
      least one state"
  let some fieldsStx := fields?
    | throwError s!"schema_entity_machine `{baseName}`: missing `fields:` \
        clause — the record's fields (a `List Field` term)"
  let some colStx := col?
    | throwError s!"schema_entity_machine `{baseName}`: missing `column:` \
        clause — the state column's name"
  let initState : String ←
    match init? with
    | some i => pure i.getId.toString
    | none =>
        throwError s!"schema_entity_machine `{baseName}`: missing \
          `initial:` clause — the lifecycle's start state"
  let stateNames : Array String := stateArr.map (·.getId.toString)
  -- the closed-world gates: states distinct, endpoints + initial declared,
  -- transition names unique (did-you-mean over the valid space, ONE engine).
  if !(stateNames.toList.Nodup) then
    throwError s!"schema_entity_machine `{baseName}`: duplicate state name — \
      the states are the code order (one code per name)"
  let stateList := stateNames.toList
  unless stateList.contains initState do
    throwError s!"schema_entity_machine `{baseName}`: initial `{initState}` is \
      not a declared state{TextKit.suggestSuffix initState stateList}"
  let mut seen : List String := []
  let mut trData : Array (String × String × String) := #[]
  for tr in trs do
    let tName := tr[1]!.getId.toString
    if seen.contains tName then
      throwError s!"schema_entity_machine `{baseName}`: duplicate transition \
        name `{tName}` — the events are the Label constructors (one ctor per \
        name)"
    seen := seen ++ [tName]
    let src := tr[3]!.getId.toString
    let dst := tr[5]!.getId.toString
    unless stateList.contains src do
      throwError s!"schema_entity_machine `{baseName}`: transition `{tName}`: \
        `{src}` is not a declared state{TextKit.suggestSuffix src stateList}"
    unless stateList.contains dst do
      throwError s!"schema_entity_machine `{baseName}`: transition `{tName}`: \
        `{dst}` is not a declared state{TextKit.suggestSuffix dst stateList}"
    trData := trData.push (tName, src, dst)
  if trData.isEmpty then
    throwError s!"schema_entity_machine `{baseName}`: no transitions — an \
      entity machine needs at least one `transition:` clause"
  let colName := colStx.getId.toString

  -- Artifact 1 — the machine! declaration (+ the entourage)
  let stateIdents : Array (TSyntax `ident) :=
    stateNames.map (fun s => mkIdentFrom stx s.toName)
  let machineEvents : Array (TSyntax `machineClause) ←
    trData.mapM fun (tName, src, dst) => do
      `(machineClause|
          event: $(mkIdentFrom stx tName.toName):ident
            guard: (fun s => s = $(SchemaCore.dotRef (mkIdentFrom stx src.toName)))
            action: (fun _ _ => $(SchemaCore.dotRef (mkIdentFrom stx dst.toName))))
  let invT : Lean.Term ← match inv? with
    | some t => pure ⟨t⟩
    | none => `(fun _ => True)
  elabCommand (← `(command|
    machine! $base:ident where
      states: [$stateIdents,*]
      Inv: $invT
      $[$machineEvents:machineClause]*))

  -- Artifacts 2/3 — the fields + the keys lane's declaration set
  let fieldsT : Lean.Term := ⟨fieldsStx⟩
  elabCommand (← `(command|
    /-- The record's fields (the preset's `fields:` clause; the Item
        model's registration face — the fields-nodup obligation is this
        list's, discharged at the instance). -/
    def $(mkIdentFrom stx (baseName ++ "Fields").toName) : List Field := $fieldsT))
  let fieldsRef : Lean.Term := ⟨mkIdentFrom stx (baseName ++ "Fields").toName⟩
  let keysRhs : Lean.Term ← match key? with
    | some kId =>
        let kName := kId.getId.toString
        `(term| [ (⟨$(strT recName), $fieldsRef, $(strT kName), []⟩ : KeyDecl) ])
    | none => `(term| [])
  elabCommand (← `(command|
    /-- The keys lane's declaration set for the record (the preset's
        `key:` clause; `entityKeyOk` resolves against THIS — the ONE
        `keyDeclFor` reading, shared with the update lane's WF rung). -/
    def $(mkIdentFrom stx (baseName ++ "Keys").toName) : List KeyDecl := $keysRhs))
  let keysRef : Lean.Term := ⟨mkIdentFrom stx (baseName ++ "Keys").toName⟩

  -- Artifact 3b — the declaration row (the provenance data)
  let trTerms : Array Lean.Term ← trData.mapM fun (tName, src, dst) =>
    `(term| (⟨$(strT tName), $(strT src), $(strT dst)⟩ : EntityTransition))
  let stateStrs : Array Lean.Term := stateNames.map strT
  let keyRhs : Lean.Term ← match key? with
    | some kId => `(term| some $(strT kId.getId.toString))
    | none => `(term| none)
  elabCommand (← `(command|
    /-- The preset's declaration row (the provenance data — the codes
        ride the states list's order). -/
    def $(mkIdentFrom stx (baseName ++ "Decl").toName) : EntityMachineDecl :=
      (⟨$(strT baseName), $(strT recName),
        $(strT colName), [$stateStrs,*], [$trTerms,*], $keyRhs⟩ :
        EntityMachineDecl)))
  let declRef : Lean.Term := ⟨mkIdentFrom stx (baseName ++ "Decl").toName⟩

  -- Artifact 4 — the per-transition keyed updates
  elabCommand (← `(command|
    /-- The per-transition keyed updates — the deltas on the state
        column (`transitionUpdate`); `none` = the closed-world refusal
        (the state column is missing or mistyped — the Diag envelope
        reports it, never silence). -/
    def $(mkIdentFrom stx (baseName ++ "Updates").toName) :
        Option (List (UpdateItem $fieldsRef)) :=
      declUpdates $declRef $fieldsRef))

  -- Artifact 5 — the declared edge table + the determinacy rung
  elabCommand (← `(command|
    /-- The declared edge table (event, from-code, to-code) — the
        journal's closed world (the antijoin's edge side). -/
    def $(mkIdentFrom stx (baseName ++ "Edges").toName) :
        List (String × UInt64 × UInt64) := EntityMachineDecl.edges $declRef))
  let edgesRef : Lean.Term := ⟨mkIdentFrom stx (baseName ++ "Edges").toName⟩
  elabCommand (← `(command|
    /-- The determinacy rung, DECIDED: no (event, from-state) pair
        points at two targets — the replay law's premise. -/
    theorem $(mkIdentFrom stx (baseName ++ "EdgesDet").toName) :
        edgesDet $edgesRef = true := by decide))
  let edgesDetRef : Lean.Term :=
    ⟨mkIdentFrom stx (baseName ++ "EdgesDet").toName⟩

  -- Artifact 6 — the WF Diag envelope
  elabCommand (← `(command|
    /-- The WF diagnostics (the rung cascade: the column, the
        endpoints, the names, the key) — empty = well formed, and the
        bridge (`entityDiags_eq_nil_iff`) says so in both directions. -/
    def $(mkIdentFrom stx (baseName ++ "Diags").toName) : List Kit.Diag :=
      entityDiags $declRef $fieldsRef $keysRef))

  -- Artifact 7 — the generated table's honesty (the tie-before-emission
  -- discipline: the table is cited against `step?` by the generic law)
  let labelsRef : Lean.Term := ⟨mkIdentFrom stx s!"{baseName}.labels".toName⟩
  let statesRef : Lean.Term := ⟨mkIdentFrom stx (baseName ++ "States").toName⟩
  let transRef : Lean.Term := ⟨mkIdentFrom stx (baseName ++ "Trans").toName⟩
  elabCommand (← `(command|
    /-- THE GENERATED TABLE IS HONEST (`trans_honest`, cited with
        `rfl` against the table's defining fold): every row is a real
        step of the generated machine. -/
    theorem $(mkIdentFrom stx (baseName ++ "Trans_honest").toName) :
        ∀ e ∈ $transRef, Machines.MachineWithInv.step? $base e.2.1 e.1
          = some e.2.2 :=
      trans_honest $base $labelsRef $statesRef $transRef rfl))

  -- Artifact 8 — the legality discipline
  let stTy : Lean.Term := ⟨mkIdentFrom stx s!"{baseName}.State".toName⟩
  let lbTy : Lean.Term := ⟨mkIdentFrom stx s!"{baseName}.Label".toName⟩
  elabCommand (← `(command|
    /-- The legality relation (DFA membership — the run accepts). -/
    def $(mkIdentFrom stx (baseName ++ "LegalFrom").toName)
        (init : $stTy) (seq : List $lbTy) : Bool :=
      legalFrom $base init seq))
  elabCommand (← `(command|
    /-- The journal antijoin (the illegal deltas, isolated as data —
        the closed-world refusal's payload). -/
    def $(mkIdentFrom stx (baseName ++ "Antijoin").toName)
        (journal : List (String × UInt64 × UInt64)) :
        List (String × UInt64 × UInt64) :=
      journalAntijoin $edgesRef journal))
  elabCommand (← `(command|
    /-- Journal legality: the antijoin is empty. -/
    def $(mkIdentFrom stx (baseName ++ "LegalJournal").toName)
        (journal : List (String × UInt64 × UInt64)) : Bool :=
      legalJournal $edgesRef journal))
  elabCommand (← `(command|
    /-- Replay: fold the journal through the edge table's step (the
        audit — replay is the law, the antijoin is the gate). -/
    def $(mkIdentFrom stx (baseName ++ "Replay").toName) (init : UInt64) :
        List (String × UInt64 × UInt64) → Option UInt64 :=
      journalReplay (edgeStep $edgesRef) init))
  elabCommand (← `(command|
    /-- THE REPLAY LAW (`replay_of_legalJournal`, cited): a legal,
        chaining journal replays to a final state. -/
    theorem $(mkIdentFrom stx (baseName ++ "Replay_ok").toName)
        (init : UInt64) (journal : List (String × UInt64 × UInt64))
        (hlegal : legalJournal $edgesRef journal = true)
        (hchain : ChainsFrom init journal) :
        ∃ fin, $(mkIdentFrom stx (baseName ++ "Replay").toName) init journal
          = some fin :=
      replay_of_legalJournal (edgeStep $edgesRef) $edgesRef
        (edgesDet_honest $edgesRef $edgesDetRef) journal hlegal init hchain))

  -- Artifact 9 — the code bridge + THE CODE TIE
  let stateAlts : Array (TSyntax `Lean.Parser.Term.matchAlt) ←
    stateNames.zipIdx.mapM fun (s, i) =>
      `(Lean.Parser.Term.matchAltExpr| | $(SchemaCore.dotRef (mkIdentFrom stx s.toName)) =>
          $(natT i))
  elabCommand (← `(command|
    /-- The state's CODE (declaration order) — the record's u64 state
        column carries it; the enum is the host-side discipline. -/
    def $(mkIdentFrom stx (baseName ++ "StateCode").toName) : $stTy → UInt64
      $[$stateAlts:matchAlt]*))
  let stateCodeRef : Lean.Term :=
    ⟨mkIdentFrom stx (baseName ++ "StateCode").toName⟩
  let eventAlts : Array (TSyntax `Lean.Parser.Term.matchAlt) ←
    trData.mapM fun (tName, _, _) =>
      `(Lean.Parser.Term.matchAltExpr| | $(SchemaCore.dotRef (mkIdentFrom stx tName.toName)) =>
          $(strT tName))
  elabCommand (← `(command|
    /-- The event's name (the journal's event face — the edge table's
        first component). -/
    def $(mkIdentFrom stx (baseName ++ "EventName").toName) : $lbTy → String
      $[$eventAlts:matchAlt]*))
  let eventNameRef : Lean.Term :=
    ⟨mkIdentFrom stx (baseName ++ "EventName").toName⟩
  elabCommand (← `(command|
    /-- THE CODE TIE: the declared edge table IS the generated
        machine's transition table, under the code bridge — the
        journal face and the machine face are the SAME table (the
        generated `Trans` computes from `step?`, the generated tie
        pins it; this theorem pins the code reading). -/
    theorem $(mkIdentFrom stx (baseName ++ "Edges_generated").toName) :
        $edgesRef = $(transRef).map
          (fun e => ($eventNameRef e.1, $stateCodeRef e.2.1,
            $stateCodeRef e.2.2)) := by rfl))

  -- Artifact 10 — the obligations (the decidableNow rows)
  let wfLabel : Lean.Term := strT s!"{baseName}/table-wf"
  let mut rowTerms : Array Lean.Term :=
    #[← `(term| entityRow $wfLabel
          (EntityClaim.tableWf $declRef $fieldsRef $keysRef))]
  for (tName, src, dst) in trData do
    let fc := stateNames.idxOf src
    let tc := stateNames.idxOf dst
    rowTerms := rowTerms.push (← `(term|
      entityRow $(strT s!"{baseName}.{tName}-fires")
        (EntityClaim.fires $declRef $fieldsRef
          (⟨$(strT tName), $(strT src), $(strT dst)⟩ : EntityTransition)
          ($(natT fc) : UInt64))))
    rowTerms := rowTerms.push (← `(term|
      entityRow $(strT s!"{baseName}.{tName}-moves")
        (EntityClaim.moves $declRef $fieldsRef
          (⟨$(strT tName), $(strT src), $(strT dst)⟩ : EntityTransition)
          ($(natT fc) : UInt64) ($(natT tc) : UInt64))))
  elabCommand (← `(command|
    /-- The obligation rows (the decidableNow tier): the table's WF +
        per-transition fires/moves — each row's discharge proves ITS
        claim (the Prop-indexed view; `EntityOblRow.discharge_sound`). -/
    def $(mkIdentFrom stx (baseName ++ "Obligations").toName) :
        List EntityOblRow :=
      [$rowTerms,*]))
  elabCommand (← `(command|
    /-- Every obligation row DISCHARGES under the record's declared
        premises (the decidableNow backend — decided, not assumed; the
        generic fires/moves laws guarantee the verdicts). The
        ANTECEDENT is the honesty: a refused decl (the Diag envelope
        nonempty, or a default-less / duplicate-named field list) does
        NOT discharge — the loud gap, never a laundered pass. -/
    theorem $(mkIdentFrom stx (baseName ++ "Obligations_fire").toName) :
        (entityDiags $declRef $fieldsRef $keysRef = []
            ∧ defaultRow? $fieldsRef ≠ none
            ∧ (($(fieldsRef).map (·.name))).Nodup) →
        $(mkIdentFrom stx (baseName ++ "Obligations").toName).all
          (fun r => r.discharge = some (Kit.Evidence.decided true)) = true :=
      by decide))

  -- Artifact 11 — the invariant-preservation obligation (the
  -- .provedAtElab row, discharged by CITING the generic theorem)
  let claimT : Lean.Term ← `(term|
    ∀ (s : $stTy) (i : $lbTy) (s' : $stTy),
      Machines.MachineWithInv.step? $base s i = some s' →
      ($base).inv s → ($base).inv s')
  elabCommand (← `(command|
    /-- The invariant's preservation, realized by CITATION
        (`MachineWithInv.step?_preserves` — proved once, in
        Machines.Events; the generated machine instantiates it). -/
    theorem $(mkIdentFrom stx (baseName ++ "Preserves").toName) : $claimT :=
      fun s i s' h hi => Machines.MachineWithInv.step?_preserves $base h hi))
  elabCommand (← `(command|
    /-- The preservation obligation's Prop-indexed row, discharged by
        the citation (the `.provedAtElab` tier — the evidence is the
        cited kernel-checked theorem). -/
    def $(mkIdentFrom stx (baseName ++ "PreservesRow").toName) :
        Kit.Discharged Unit $claimT :=
      { obligation :=
          { label := $(strT s!"{baseName}/preserves-inv")
            tier := .provedAtElab, payload := (), provenance := `SchemaCore }
        evidence := Kit.Evidence.citedProof
          `Machines.MachineWithInv.step?_preserves }))

end SchemaCore.Meta
