/- # SchemaCore.DeltaLog — the delta log's crash-recovery model (A5)

Owner: the persistence lane (the mandate tree, `schemacore/`; the delta
discipline's honest home).
Driving decisions: notes/design-wave-30.md A5 (the Crash discipline →
the persistence model: the log as ONE transition family — append; the
crash as the Crash discipline's crash step; the torn-tail recovery's
correctness as theorems) + `Machines.Crash` (the crash/recovery
refinement: the persistent/volatile separation, the model face) +
`crates/mandate-delta/src/log.rs` (the RUNTIME face: the torn-tail
honesty — truncate-at-last-good-frame AND REPORT the cut, never silent;
a corrupt COMPLETE frame is a typed refusal).

THE MODEL (what lands, honestly): the log's file wire is a stream of
self-delimiting frames (`encDelta`'s shape — the landed codec's own
bytes). A crash DURING an append leaves a strict PREFIX of the journal:
every frame that fit is complete, the last partial frame is the TORN
TAIL — a byte shape no completed write can produce, so the recovery may
cut it (the prefix argument). The recovery discipline:

- the recovered journal is the LONGEST VALID PREFIX of the written one
  (the refinement's honest relation: recovered = the longest prefix);
- the cut is REPORTED (`RecoveryReport`: the offset + the surviving
  frame count) — never silent, never a phantom report;
- the cut lands at the torn frame's start (= the good prefix's byte
  length), strictly inside it, never past the crash point;
- the recovered state is the recovered journal's replay (`replay`, the
  I operator) — the log's invariant restored, the log stays appendable.

The snapshot's crash discipline rides the same honesty: a TORN or
CORRUPT snapshot never loads — the FULL log replay takes over and the
fallback is REPORTED (`SnapOutcome`; the byte-level alignment rules are
the Rust codec's, mirrored by its runtime matrix). The Rust recovery
implements this model and the duel (`tests/crash_duel.rs`) checks the
implementation at the LCG-seeded scenarios (the shared generator: seed
+ recurrence are the tree's one LCG, `TestingKit.lcg`).

The five questions (notes/v3/01-core.md):
- root: TraceModel (01 §3) crossed Change (01 §2) — the recovery IS the
  prefix's replay (the I operator over the longest valid prefix), the
  append IS the one transition family.
- carrier grade: `Machines.Crash.CrashMachine` instantiated at the
  keyed-table face (`Machines.Crash.Log`, the bridge module) — the
  machine face is THERE; this module is the byte-level walk + the
  recovery outcome algebra.
- spine reading: none — a substrate over Event.lean's codec laws.
- ladder rung: rung 6 hand theorems over the walk's recursion (the
  prefix/longest/report laws, one induction each) + rung-3 value pins
  in SchemaTests (the LCG scenarios, `decide`).
- gate row: SchemaTests' deltaLog suite + the axiom report.

Core-only (imports SchemaCore.Event — the cone rule; the generic encR/
encK parameters instantiate at the duel emitter's ONE fixture copy,
`SchemaCore.Emit.Journal` — the scenario pins consume that).
-/

import SchemaCore.Event

namespace SchemaCore.DeltaLog

/-! ## The journal wire (the log file's face: frames, NO count prefix) -/

/-- THE LOG WIRE: the frames back to back — the log file is NEVER
    rewritten, so it carries no journal-level count prefix (the duel
    journal's `encJournal` wire is the whole-log TRANSPORT face; the
    log's durable artifact is the bare frame stream). -/
def logWire {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (log : List (RowDelta fs)) : List UInt8 :=
  (log.map (encDelta encR encK)).flatten

theorem logWire_nil {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) : logWire encR encK [] = [] := rfl

theorem logWire_cons {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (d : RowDelta fs) (log : List (RowDelta fs)) :
    logWire encR encK (d :: log)
      = encDelta encR encK d ++ logWire encR encK log := rfl

/-- A frame is never empty: the tag byte alone is a byte (the walk's
    positivity — every surviving frame made progress). -/
theorem encDelta_pos {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (d : RowDelta fs) :
    (encDelta encR encK d).length > 0 := by
  cases d <;> simp [encDelta]

/-! ## The walk (the recovery's classifier) -/

/-- THE WALK, model face (`walk_journal`'s shape): from the front,
    keep every frame that FITS entirely before the cut; a frame
    straddling the cut is the TORN TAIL — reported at its start; a cut
    that lands on a frame's boundary (or past the end) ends the walk
    cleanly. The recursion is over the frame list with the running
    start offset — the byte positions are the frames' own. -/
def walkAux {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut : Nat) :
    Nat → List (RowDelta fs) → List (RowDelta fs) × Option Nat
  | _, [] => ([], none)
  | start, d :: rest =>
      if cut ≤ start then ([], none)             -- the journal ends here: clean
      else if start + (encDelta encR encK d).length ≤ cut then
        (d :: (walkAux encR encK cut (start + (encDelta encR encK d).length) rest).1,
         (walkAux encR encK cut (start + (encDelta encR encK d).length) rest).2)
      else ([], some start)                      -- TORN: straddles the cut

/-- The walk's outcome at the crash point. -/
def walk {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut : Nat) (log : List (RowDelta fs)) :=
  walkAux encR encK cut 0 log

/-! ### The walk's three branches, as equation lemmas (the induction's
     interface — each `simp only`-derived from the definition) -/

/-- The journal-ends-here branch: a cut at or before the running
    offset stops the walk cleanly. -/
theorem walkAux_stop {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut start : Nat) (d : RowDelta fs)
    (rest : List (RowDelta fs)) (h : cut ≤ start) :
    walkAux encR encK cut start (d :: rest) = ([], none) := by
  simp [walkAux, h]

/-- The frame-fits branch: the frame survives, the walk recurses past
    it. -/
theorem walkAux_fits {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut start : Nat) (d : RowDelta fs)
    (rest : List (RowDelta fs)) (h1 : ¬ (cut ≤ start))
    (h2 : start + (encDelta encR encK d).length ≤ cut) :
    walkAux encR encK cut start (d :: rest)
      = (d :: (walkAux encR encK cut (start + (encDelta encR encK d).length) rest).1,
         (walkAux encR encK cut (start + (encDelta encR encK d).length) rest).2) := by
  simp [walkAux, h1, h2]

/-- THE TORN BRANCH: the frame straddles the cut — reported at its
    start. -/
theorem walkAux_torn {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut start : Nat) (d : RowDelta fs)
    (rest : List (RowDelta fs)) (h1 : ¬ (cut ≤ start))
    (h2 : ¬ (start + (encDelta encR encK d).length ≤ cut)) :
    walkAux encR encK cut start (d :: rest) = ([], some start) := by
  simp [walkAux, h1, h2]

/-! ### The walk's laws (the recovery's correctness, one induction each) -/

/-- THE PREFIX LAW: every frame the walk kept is a PREFIX of the
    written journal — the recovery never invents, never reorders. -/
theorem walkAux_prefix {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut : Nat) :
    ∀ (start : Nat) (log : List (RowDelta fs)),
      ∃ rest, log = (walkAux encR encK cut start log).1 ++ rest := by
  intro start log
  induction log generalizing start with
  | nil => exact ⟨[], rfl⟩
  | cons d rest ih =>
      by_cases h1 : cut ≤ start
      · rw [walkAux_stop encR encK cut start d rest h1]
        exact ⟨d :: rest, rfl⟩
      · by_cases h2 : start + (encDelta encR encK d).length ≤ cut
        · rw [walkAux_fits encR encK cut start d rest h1 h2]
          obtain ⟨rest', hrest⟩ := ih (start + (encDelta encR encK d).length)
          exact ⟨rest', by rw [List.cons_append, ← hrest]⟩
        · rw [walkAux_torn encR encK cut start d rest h1 h2]
          exact ⟨d :: rest, rfl⟩

/-- THE LONGEST-PREFIX LAW (the refinement's honest relation): the
    frame the walk DROPPED is torn BY THE CUT — the reported offset is
    exactly the good prefix's byte length (the torn frame's start), the
    cut point is strictly inside the torn frame, so no longer prefix is
    valid: the kept prefix is the LONGEST valid one. -/
theorem walkAux_torn_longest {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut : Nat) :
    ∀ (start : Nat) (log : List (RowDelta fs)) (kept : List (RowDelta fs))
      (off : Nat),
      walkAux encR encK cut start log = (kept, some off) →
      ∃ d rest, log = kept ++ d :: rest
        ∧ off = start + (logWire encR encK kept).length
        ∧ off < cut
        ∧ cut < off + (encDelta encR encK d).length := by
  intro start log
  induction log generalizing start with
  | nil => intro kept off h; simp [walkAux] at h
  | cons d rest ih =>
      intro kept off h
      by_cases h1 : cut ≤ start
      · rw [walkAux_stop encR encK cut start d rest h1] at h
        simp at h
      · by_cases h2 : start + (encDelta encR encK d).length ≤ cut
        · cases hw : walkAux encR encK cut
              (start + (encDelta encR encK d).length) rest with
          | mk w1 w2opt =>
              cases w2opt with
              | none =>
                  rw [walkAux_fits encR encK cut start d rest h1 h2, hw] at h
                  simp at h
              | some off =>
                  rw [walkAux_fits encR encK cut start d rest h1 h2, hw] at h
                  simp at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨d', rest', hlog, hoff', hlt, hcut⟩ :=
                    ih (start + (encDelta encR encK d).length) w1 off hw
                  refine ⟨d', rest', ?_, ?_, hlt, hcut⟩
                  · rw [List.cons_append, hlog]
                  · rw [logWire_cons, List.length_append]; omega
        · rw [walkAux_torn encR encK cut start d rest h1 h2] at h
          simp at h
          obtain ⟨rfl, hoff⟩ := h
          cases hoff
          refine ⟨d, rest, rfl, ?_, by omega, by omega⟩
          rw [logWire_nil, List.length_nil]; omega

/-- THE REPORT-HONESTY LAW, the never-past face: a torn walk's cut
    point is at the torn frame's START — at or before the crash point
    (the torn frame itself never survives). -/
theorem walkAux_torn_offset_le {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut : Nat) :
    ∀ (start : Nat) (log : List (RowDelta fs)) (off : Nat),
      (walkAux encR encK cut start log).2 = some off → off ≤ cut := by
  intro start log
  induction log generalizing start with
  | nil => intro off h; simp [walkAux] at h
  | cons d rest ih =>
      intro off h
      by_cases h1 : cut ≤ start
      · rw [walkAux_stop encR encK cut start d rest h1] at h; simp at h
      · by_cases h2 : start + (encDelta encR encK d).length ≤ cut
        · rw [walkAux_fits encR encK cut start d rest h1 h2] at h
          simp only at h
          exact ih (start + (encDelta encR encK d).length) off h
        · rw [walkAux_torn encR encK cut start d rest h1 h2] at h
          simp at h; omega

/-- THE CLEAN FACE: a cut that tears NO frame reports nothing, and the
    cut point is at or past the kept prefix's end — a valid boundary
    (a boundary cut is a clean shorter journal; the empty file is the
    fresh-journal shape). Together with the torn law (the cut strictly
    inside the dropped frame), the report fires EXACTLY when a frame
    straddles the cut — never silent, never phantom. -/
theorem walkAux_clean {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut : Nat) :
    ∀ (start : Nat) (log : List (RowDelta fs)), start ≤ cut →
      (walkAux encR encK cut start log).2 = none →
      start + (logWire encR encK (walkAux encR encK cut start log).1).length
        ≤ cut := by
  intro start log
  induction log generalizing start with
  | nil =>
      intro hstart _
      simp only [walkAux, logWire_nil, List.length_nil]
      omega
  | cons d rest ih =>
      intro hstart h
      by_cases h1 : cut ≤ start
      · rw [walkAux_stop encR encK cut start d rest h1] at h ⊢
        simp only [logWire_nil, List.length_nil]
        omega
      · by_cases h2 : start + (encDelta encR encK d).length ≤ cut
        · rw [walkAux_fits encR encK cut start d rest h1 h2] at h ⊢
          simp only at h
          have h1' := ih (start + (encDelta encR encK d).length) (by omega) h
          show start
            + (logWire encR encK
                (d :: (walkAux encR encK cut
                  (start + (encDelta encR encK d).length) rest).1)).length ≤ cut
          rw [logWire_cons, List.length_append]
          omega
        · rw [walkAux_torn encR encK cut start d rest h1 h2] at h
          simp at h

/-! ## The recovery outcome (the open's algebra) -/

/-- THE REPORTED CUT (the `Recovery` report's model face): where the
    good prefix ends + how many frames survived — every recovery names
    both, never silent. -/
structure RecoveryReport where
  /-- Byte offset where the torn tail began (the good prefix's length). -/
  offset : Nat
  /-- The number of frames the good prefix carries. -/
  frames : Nat

/-- THE OPEN OUTCOME over a crash-cut journal: the clean shape (no
    report — nothing tore) or the recovery (the longest valid prefix +
    the REPORTED cut). -/
inductive OpenOutcome (fs : List Field) where
  /-- No frame tore: the journal loaded end to end (possibly a clean
      shorter prefix — a cut ON a frame boundary is a shorter journal,
      not a torn write). -/
  | clean (entries : List (RowDelta fs))
  /-- The torn tail: recover to the longest valid prefix AND report. -/
  | torn (entries : List (RowDelta fs)) (report : RecoveryReport)

/-- THE RECOVERING OPEN (the `TailPolicy::Recover` model face): walk
    the frames; a torn tail recovers to the longest valid prefix and
    REPORTS the cut. -/
def openAt {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut : Nat) (log : List (RowDelta fs)) :
    OpenOutcome fs :=
  match walk encR encK cut log with
  | (kept, none) => .clean kept
  | (kept, some off) => .torn kept ⟨off, kept.length⟩

/-- THE RECOVERED ENTRIES ARE THE PREFIX AT THE REPORT: the recovery's
    frame count names exactly the prefix it kept (the report and the
    state agree — never a silent drift between them). -/
theorem openAt_torn_take {fs : List Field} (encR : RowVals fs → List UInt8)
    (encK : FieldVal → List UInt8) (cut : Nat) (log : List (RowDelta fs))
    (entries : List (RowDelta fs)) (report : RecoveryReport)
    (h : openAt encR encK cut log = .torn entries report) :
    entries = log.take report.frames := by
  cases hw : walk encR encK cut log with
  | mk kept torn =>
      simp only [openAt, hw] at h
      cases torn with
      | none => simp at h
      | some off =>
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          show kept = log.take kept.length
          obtain ⟨rest, hprefix⟩ := walkAux_prefix encR encK cut 0 log
          rw [show walkAux encR encK cut 0 log = (kept, some off) from hw] at hprefix
          have hp2 : log = kept ++ rest := hprefix
          rw [hp2, List.take_left]

/-- THE RECOVERED STATE IS THE REPLAY (the log's invariant restored):
    the recovering open's state — the recovered journal's replay over
    the empty table — is exactly the prefix replay (`runStates`
    at the crash point's frame count). The recovered log is honest and
    appendable. -/
theorem openAt_torn_state {fs : List Field} (key : String)
    (encR : RowVals fs → List UInt8) (encK : FieldVal → List UInt8)
    (cut : Nat) (log : List (RowDelta fs))
    (entries : List (RowDelta fs)) (report : RecoveryReport)
    (h : openAt encR encK cut log = .torn entries report) :
    replay key entries [] = runStates key [] log report.frames := by
  rw [openAt_torn_take encR encK cut log entries report h]
  rfl

/-! ## The snapshot's crash discipline (the open outcome, model level) -/

/-- The snapshot-open's fallback reasons (the REPORTED ones — the
    byte-level alignment rules that decide them are the Rust codec's,
    mirrored by its runtime matrix; the model carries the discipline). -/
inductive SnapFallback where
  /-- A torn snapshot file (a strict prefix — the torn-write shape). -/
  | torn (offset : Nat)
  /-- A corrupt snapshot (bad magic, out-of-policy atom, hash
      mismatch) or one that does not ALIGN against the log (neither
      rule A nor rule B holds). -/
  | refused (offset : Nat)

/-- THE SNAPSHOT-OPEN OUTCOME: applied (the alignment was VERIFIED) or
    a REPORTED fallback. -/
inductive SnapOutcome (fs : List Field) where
  /-- The snapshot was applied: its state + the verified tail. -/
  | applied (skip : Nat)
  /-- Any anomaly: the FULL log replay takes over, the reason REPORTED
      (never silent, never a wrong state). -/
  | fellBack (reason : SnapFallback)

/-- THE SNAPSHOT RECOVERY (the model face): the state an open lands at.
    An applied snapshot replays the verified tail ON its state; a
    fallback IGNORES the snapshot state entirely — the full replay. -/
def snapRecover {fs : List Field} (key : String)
    (log : List (RowDelta fs)) (snapState : List (RowVals fs)) (skip : Nat) :
    SnapOutcome fs → List (RowVals fs)
  | .applied _ => replay key (log.drop skip) snapState
  | .fellBack _ => replay key log []

/-- THE SNAPSHOT FALLBACK LAW: a fallback open's state is the LOG's
    FULL replay — the snapshot's state is never trusted through a
    fallback, and the reason is carried as data (the never-silent
    discipline: the report IS the outcome's shape). -/
theorem snapRecover_fallback {fs : List Field} (key : String)
    (log : List (RowDelta fs)) (snapState : List (RowVals fs)) (skip : Nat)
    (reason : SnapFallback) :
    snapRecover key log snapState skip (.fellBack reason)
      = replay key log [] := rfl

/-- THE APPLIED FACE: an applied snapshot's state rides the tail
    replay on the snapshot's state (the subsumed prefix is retired
    because it was VERIFIED — rule A's byte-tie at the model level). -/
theorem snapRecover_applied {fs : List Field} (key : String)
    (log : List (RowDelta fs)) (snapState : List (RowVals fs)) (skip : Nat) :
    snapRecover key log snapState skip (.applied skip)
      = replay key (log.drop skip) snapState := rfl

end SchemaCore.DeltaLog
