/-
# Kit.CodeRegistry — the persisted E-code registry (notes/v3/05-codegen.md §4)

The E-code universe: ONE code space for all diagnostics (elaboration,
gates, Rust spans, wasm faults) — allocated from the PERSISTED registry,
with STABLE allocation: codes never derive from enumeration position or
import order, and a reordered registry changes no code. This module is
the named successor of the `ECode` wrapper's promise (Kit.Diag): the
registry allocates the codes; `ECode` wraps their spellings.

The pure model is the PAIRS face `List (String × Nat)` (name ↦ code) —
but the persisted value carries one more bit per row: the RETIRED
tombstone. Deletion keeps the row, flagged; without the flag a bare
pair list cannot say "this code is spent" without lying through
`lookup`. The tombstone is what makes the doctrine's sentence — a
deleted name's code stays retired — CHECKABLE (the gate's replay +
`checkStable`'s tombstone clause), and `allocate` (next free = max + 1)
never revisits a spent code, so a rename is a NEW name with a NEW code.

Invariants IN THE TYPE where honest: at runtime the registry is parsed
data, so `by decide` proof fields are unavailable — the kit's pattern
for that grade is `CheckedProp` (Kit.CheckedProp): `wfProp` is the
Prop (names distinct across ALL rows; codes strictly increasing by
adjacency — distinct codes ride the strict order, an equality would
force an adjacent failure), `codeRegistryWf.check` its decidable
shadow, soundness proved, completeness proved (the checker computes
exactly the Prop). Concrete literals that need the invariants as ELABO-
RATION gates use `DataRegistry`/`CodedRegistry` (Kit.Registry); this
module is the persisted-runtime sibling.

The file format (`notes/code-registry.txt`): one row per line,
`name<TAB>code`, an optional leading `-` marking the tombstone, rows
sorted by code, LF line endings, no blank lines, no comments. Parse and
print are TOTAL (TextKit.Basic's scanners; the typed grammar layer of
05 §1 is a later order — there the round-trip law widens to the typed
grammar). THE ROUND TRIP IS A THEOREM here: `parse_print` — a
well-formed (`wfProp`) registry with `rowNameOk` names prints to its
canonical bytes and parses back EXACTLY (`parse (print r) = .ok r`);
the gate re-derives the bytes and the KitTests pin rides the theorem.

Core-only (no mathlib/Batteries). Five questions (notes/v3/01-core.md):
- root: DATA — Universe content (closed codes + total denotation); the
  allocation discipline is the Change ladder's irreversible rung
  (allocate never reassigns: the delta retains old information).
- carrier grade: first-order over String/Nat/List — guest-thinkable
  (the guest's ids ride the same codes).
- spine reading: as-data (the gate replays it; nothing prints but the
  total `print`).
- ladder rung: rung 2-3 — `sortedCodes_iff` + the CheckedProp proofs
  are small inductions; no proof family.
- gate row: `gates code-registry-check` (Gates.CodeRegistryCheck) + the
  KitTests pins + the axiom pins in KitTests.Axioms.
-/

import Kit.CheckedProp
import TextKit.Basic
namespace Kit

/-! ## the row -/

/-- One persisted allocation: `name` holds `code`; `retired` marks the
    tombstone a deletion leaves behind (the code stays spent forever). -/
structure CodeRow where
  /-- The diagnostic's name (the registry's key; spent for tombstones). -/
  name : String
  /-- The allocated code (a bare natural; the E-code spelling renders
      at the consumer — Kit.Diag wraps, this allocates). -/
  code : Nat
  /-- The tombstone: a deleted name's row stays, flagged. -/
  retired : Bool := false
deriving BEq, DecidableEq, Repr, Inhabited

/-- The pure model — the tasked pairs face is `pairs` below; the
    persisted value rides the tombstones. (`abbrev`: the List carrier's
    instances — Membership, foldl, map — reach through.) -/
abbrev CodeRegistry : Type := List CodeRow

/-- The live pairs — `List (String × Nat)`, the face the consumers
    read (Diag sites, the faults lane). -/
def CodeRegistry.pairs (r : CodeRegistry) : List (String × Nat) :=
  (r.filter (fun row => !row.retired)).map (fun row => (row.name, row.code))

namespace CodeRegistry

/-! ## sortedness — the adjacency discipline -/

/-- Strictly increasing by adjacency (the executable sortedness; rows
    are stored sorted by code). -/
def sortedCodes : List Nat → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => (x < y) && sortedCodes (y :: rest)

/-- The Prop twin of `sortedCodes` (strictly increasing, as an
    inductive — the checker's soundness target). -/
inductive SortedLt : List Nat → Prop where
  | nil : SortedLt []
  | one (x : Nat) : SortedLt [x]
  | cons {x y : Nat} {rest : List Nat}
      (hlt : x < y) (hrec : SortedLt (y :: rest)) : SortedLt (x :: y :: rest)

/-- The checker decides its Prop — both directions proved (rung 2-3:
    small inductions, no classical machinery). -/
theorem sortedCodes_iff : ∀ l : List Nat, sortedCodes l = true ↔ SortedLt l
  | [] => ⟨fun _ => .nil, fun _ => rfl⟩
  | [_x] => ⟨fun _ => .one _x, fun _ => rfl⟩
  | x :: y :: rest => by
      constructor
      · intro h
        have h2 := Bool.and_eq_true_iff.mp
          (show ((x < y) && sortedCodes (y :: rest)) = true from h)
        exact SortedLt.cons (of_decide_eq_true h2.1)
          ((sortedCodes_iff (y :: rest)).mp h2.2)
      · intro h
        match h with
        | .cons hlt hrec =>
          exact Bool.and_eq_true_iff.mpr
            ⟨by simp [hlt], (sortedCodes_iff (y :: rest)).mpr hrec⟩

/-! ## the invariants — CheckedProp over the parsed data -/

/-- The invariants as a Prop: names distinct across ALL rows (a
    tombstone's name is spent too — a rename is a NEW name), codes
    strictly increasing by adjacency (distinct codes ride the strict
    order: an equality would force an adjacent failure). -/
def wfProp (r : CodeRegistry) : Prop :=
  (r.map (·.name)).Nodup ∧ SortedLt (r.map (·.code))

/-- The executable checker — `wfProp`'s decidable shadow. -/
def check (r : CodeRegistry) : Bool :=
  decide ((r.map (·.name)).Nodup) && sortedCodes (r.map (·.code))

end CodeRegistry

/-- The registry's well-formedness as a CheckedProp: soundness PROVED
    (a `true` verdict is the invariants), completeness PROVED (the
    checker computes exactly the Prop — both rungs up, no `.missing`). -/
def codeRegistryWf : CheckedProp CodeRegistry where
  P := CodeRegistry.wfProp
  check := CodeRegistry.check
  sound := by
    intro r h
    rw [CodeRegistry.wfProp]
    have h2 := Bool.and_eq_true_iff.mp
      (show ((decide (r.map (·.name) |>.Nodup)) && CodeRegistry.sortedCodes (r.map (·.code))) = true
        from h)
    exact ⟨decide_eq_true_iff.mp h2.1, (CodeRegistry.sortedCodes_iff _).mp h2.2⟩
  complete? := .proved (by
    intro r h
    show CodeRegistry.check r = true
    exact Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true_iff.mpr h.1, (CodeRegistry.sortedCodes_iff _).mpr h.2⟩)

namespace CodeRegistry

/-! ## lookup — the live face -/

/-- The live code of `name`: `none` for a miss AND for a tombstone (a
    retired name has no code — the lookup must never resurrect one). -/
def lookup (r : CodeRegistry) (name : String) : Option Nat :=
  match r.find? (fun row => row.name == name && !row.retired) with
  | some row => some row.code
  | none => none

/-! ## allocation — next free, never reassigned -/

/-- The highest code in the registry (0 when empty). -/
def maxCode (r : CodeRegistry) : Nat :=
  match r with
  | [] => 0
  | row :: rest => max row.code (maxCode rest)

/-- The next free code: max + 1. NEVER reassigns — every spent code
    (live or tombstoned) sits at or below `maxCode`, so the successor
    is fresh; a deleted name's code stays retired for free. -/
def nextCode (r : CodeRegistry) : Nat := r.maxCode + 1

/-- `maxCode` dominates every member's code. -/
theorem maxCode_ge : ∀ (r : CodeRegistry) (row : CodeRow), row ∈ r →
    row.code ≤ r.maxCode
  | [], _row, h => absurd h (by simp)
  | row0 :: rest, row, h => by
      rcases List.mem_cons.mp h with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (maxCode_ge rest row hmem) (Nat.le_max_right _ _)

/-- The next free code is strictly above every member's code. -/
theorem nextCode_gt (r : CodeRegistry) (row : CodeRow) (h : row ∈ r) :
    row.code < r.nextCode :=
  Nat.lt_succ_of_le (maxCode_ge r row h)

/-- Insert by code order (the rows stay sorted). -/
def insertRow : CodeRegistry → CodeRow → CodeRegistry
  | [], row => [row]
  | row :: rows, new =>
      if new.code < row.code then new :: row :: rows
      else row :: insertRow rows new

/-- Allocate: `name` must be fresh over ALL rows (a tombstone blocks
    its name too — a rename is a NEW name with a NEW code: retire the
    old row, allocate fresh); assigns `nextCode`, keeps the sort. -/
def allocate (r : CodeRegistry) (name : String) : Except String CodeRegistry :=
  if r.any (fun row => row.name == name) then
    .error s!"code-registry: `{name}` already holds a row — a rename is a \
NEW name with a NEW code (retire the old row, allocate fresh); codes are \
never reassigned"
  else
    .ok (insertRow r ⟨name, r.nextCode, false⟩)

/-- Mark the live row `name` retired (the tombstone): `none` when no
    live row carries the name (already retired, or never allocated). -/
def retireAux (name : String) : CodeRegistry → Option CodeRegistry
  | [] => none
  | row :: rows =>
      if row.name == name && !row.retired then
        some ({ row with retired := true } :: rows)
      else
        (retireAux name rows).map (fun rows' => row :: rows')

/-- Retire: the deletion op. The row STAYS (flagged) — its code is
    spent forever; nothing is removed from the allocation history. -/
def retire (r : CodeRegistry) (name : String) : Except String CodeRegistry :=
  match retireAux name r with
  | some r' => .ok r'
  | none => .error s!"code-registry: no live row `{name}` to retire"

/-! ## the stability verdict -/

/-- The stability verdict (05 §4): every old LIVE pair survives in
    `new` UNCHANGED (`new.lookup name = some code` — a re-allocated
    name or a retired pair fails), and every old tombstone's code
    STAYS RETIRED in `new` (still present, still flagged — a deleted
    tombstone row would let a future allocation reuse the code). -/
def checkStable (old new : CodeRegistry) : Bool :=
  old.all (fun o =>
    if o.retired then new.any (fun n => n.code == o.code && n.retired)
    else new.lookup o.name == some o.code)

/-- The semantic stability claim `checkStable` decides (pattern #1: the
    relation is the spec, the checker its executable shadow): every old
    LIVE pair survives in `new` UNCHANGED (the lookup still lands on the
    same code), and every old tombstone's code STAYS RETIRED in `new`
    (present, still flagged — a dropped tombstone would let a future
    allocation reuse a spent code). -/
def stableSem (old new : CodeRegistry) : Prop :=
  (∀ row : CodeRow, row ∈ old → !row.retired = true →
      new.lookup row.name = some row.code) ∧
  (∀ row : CodeRow, row ∈ old → row.retired = true →
      ∃ n : CodeRow, n ∈ new ∧ n.code = row.code ∧ n.retired = true)

/-- THE STABILITY BRIDGE: `checkStable old new = true ↔ stableSem old
    new` — the checker's verdict IS the semantic claim, both directions
    small list walks over `all` (the gate replays the checker; the
    theorem carries the meaning). -/
theorem checkStable_ok (old new : CodeRegistry) :
    checkStable old new = true ↔ stableSem old new := by
  constructor
  · intro h
    rw [checkStable, List.all_eq_true] at h
    refine ⟨?_, ?_⟩
    · intro row hrow hret
      have hf : row.retired = false := by
        cases hb : row.retired with
        | false => rfl
        | true => rw [hb] at hret; simp at hret
      have hr := h row hrow
      rw [if_neg (by rw [hf]; simp)] at hr
      exact beq_iff_eq.mp hr
    · intro row hrow hret
      have hr := h row hrow
      rw [if_pos hret] at hr
      obtain ⟨n, hn, hq⟩ := List.any_eq_true.mp hr
      have h2 := Bool.and_eq_true_iff.mp hq
      exact ⟨n, hn, beq_iff_eq.mp h2.1, h2.2⟩
  · intro ⟨hlive, htomb⟩
    rw [checkStable, List.all_eq_true]
    intro row hrow
    cases hret : row.retired with
    | false =>
        rw [if_neg (by simp [])]
        exact beq_iff_eq.mpr (hlive row hrow (by simp [hret]))
    | true =>
        rw [if_pos rfl]
        obtain ⟨n, hn, hcode, hret2⟩ := htomb row hrow hret
        exact List.any_eq_true.mpr ⟨n, hn, Bool.and_eq_true_iff.mpr
          ⟨beq_iff_eq.mpr hcode, hret2⟩⟩

/-! ## the allocation replay -/

/-- Replay the allocation discipline over the rows in code order: each
    row must be EXACTLY what `allocate` produces at that point (its
    code = the then-next free code). A hand-edited code falls off the
    discipline's sequence — the gate's tooth. Tombstones replay as
    allocate-then-retire. -/
def replay (r : CodeRegistry) : Except String CodeRegistry :=
  r.foldl (fun (acc : Except String CodeRegistry) (row : CodeRow) =>
      match acc with
      | .error e => .error e
      | .ok reg =>
          match reg.allocate row.name with
          | .error e => .error s!"code-registry replay: {e}"
          | .ok reg' =>
              let fresh := reg'.getLast?
              if !((fresh.map (fun a => a.name == row.name && a.code == row.code)).getD false) then
                .error s!"code-registry replay: `{row.name}`'s code {row.code} is not \
the allocation the discipline produces (next free: {reg.nextCode}) — a hand-edited code?"
              else if row.retired then .ok ((retireAux row.name reg').getD reg')
              else .ok reg')
    (.ok [])

/-! ## the file format — print/parse, both total -/

/-- Render one row: `[-]name<TAB>code`. -/
def renderRow (row : CodeRow) : String :=
  (if row.retired then "-" else "") ++ row.name ++ "\t" ++ toString row.code

/-- Print the registry: one row per line, LF-terminated (the committed
    file's canonical bytes). -/
def print (r : CodeRegistry) : String :=
  r.foldl (fun acc row => acc ++ renderRow row ++ "\n") ""

/-- A row name's charset: anything but the separators (a LEADING `-`
    is the tombstone marker — names starting with `-` are reserved). -/
def rowNameChar (c : Char) : Bool := c != '\t' && c != '\n' && c != '\r'

/-- Parse one row's body (`name<TAB>code`, the flag already stripped):
    TextKit's `scanNat` for the code; the line must be fully consumed.
    Total; `none` = malformed. -/
def parseRowBody (cs : List Char) (retired : Bool) : Option CodeRow :=
  let name := String.ofList (cs.takeWhile rowNameChar)
  if name = "" then none
  else
    match cs.dropWhile rowNameChar with
    | '\t' :: rest1 =>
        match TextKit.scanNat rest1 with
        | some (code, rest2) => if rest2 = [] then some ⟨name, code, retired⟩ else none
        | none => none
    | _ => none

/-- Parse one line: `[-]name<TAB>code`. Total; `none` = malformed.
    (The dispatch is the beq-face of the `-` marker — same behavior as
    the pattern-match spelling, at the grade the proofs consume.) -/
def parseRow (line : String) : Option CodeRow :=
  let cs := line.toList
  if cs.head? == some '-' then parseRowBody (cs.drop 1) true
  else if cs = [] then none
  else parseRowBody cs false

/-- The fold step of the line loop: propagate the error, else push the
    parsed row (the reversal is undone at the tail). -/
def parseStep (acc : Except String (List CodeRow)) (line : String) :
    Except String (List CodeRow) :=
  match acc with
  | .error e => .error e
  | .ok rows =>
      match parseRow line with
      | some row => .ok (row :: rows)
      | none => .error "code-registry: malformed row — expected \
`[-]name<TAB>code` (the `-` marks a retired tombstone); no blank lines"

/-- The line loop's tail: reverse the accumulated rows, then the
    well-formedness gate — an ill-formed (unsorted, duplicate-named)
    file is a REFUSAL, never a silent accept. -/
def parseLines (ls : List String) : Except String CodeRegistry :=
  match ls.foldl parseStep (.ok []) with
  | .error e => .error e
  | .ok revRows =>
      let r := revRows.reverse
      if codeRegistryWf.check r then .ok r
      else .error "code-registry: ill-formed registry — names must be unique \
and rows sorted by code (distinct codes ride the strict order)"

/-- The trailing-newline discipline: a final empty line is the file's,
    not a row's (dropped). -/
def dropLastEmpty (ls : List String) : List String :=
  if ls.getLast? == some "" then ls.take (ls.length - 1) else ls

/-- Parse the file: one `[-]name<TAB>code` row per line, LF endings,
    no blank lines; the final newline's empty tail is the file's, not a
    row's. The result must satisfy `codeRegistryWf.check` — an
    ill-formed (unsorted, duplicate-named) file is a REFUSAL, never a
    silent accept. Total over String. (The line split rides the
    List-level `splitOnP` — the same discipline as a single-char
    `String.splitOn`, at the grade its lemma library lives at.) -/
def parse (s : String) : Except String CodeRegistry :=
  parseLines (dropLastEmpty ((s.toList.splitOnP (· == '\n')).map String.ofList))

/-! ## the round trip — the file format's law -/

/-- A row name's round-trip discipline: nonempty, separator-free, and
    NOT `-`-led (a leading `-` is the reserved tombstone marker — the
    format's metacharacter honesty). -/
def rowNameOk (s : String) : Bool :=
  !s.isEmpty && s.toList.all rowNameChar
    && !(s.toList.head?.getD '-' == '-')

/-! ### the code token — `toString n` scans back through `scanNat` -/

private theorem takeWhile_all {p : Char → Bool} : ∀ l : List Char,
    (∀ c ∈ l, p c = true) → l.takeWhile p = l := by
  intro l h
  have h2 := List.takeWhile_append_of_pos h (l₂ := [])
  rw [← List.append_nil l, h2]
  simp

private theorem dropWhile_all {p : Char → Bool} : ∀ l : List Char,
    (∀ c ∈ l, p c = true) → l.dropWhile p = [] := by
  intro l h
  have h2 := List.dropWhile_append_of_pos h (l₂ := [])
  rw [← List.append_nil l, h2]
  rfl

private theorem toString_decDigits (n : Nat) :
    (toString n).toList = Nat.toDigits 10 n := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]

/-- THE CODE TOKEN'S LAW: a code's decimal spelling scans back to the
    code exactly (`TextKit.scanNat` over `toString`'s `toDigits` spec —
    the row format's digit token round-trips; the digit theory is core
    Nat.ToString's: `isDigit_of_mem_toDigits`, `toDigits_ne_nil`,
    `ofDigitChars_ten_toDigits`). -/
theorem scanNat_toString (n : Nat) :
    TextKit.scanNat (toString n).toList = some (n, []) := by
  have hall : ∀ c ∈ Nat.toDigits 10 n, Char.isDigit c = true :=
    fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  rw [toString_decDigits, TextKit.scanNat, takeWhile_all _ hall,
    dropWhile_all _ hall]
  have hne : String.ofList (Nat.toDigits 10 n) ≠ "" := by
    intro hcon
    have h2 := congrArg String.toList hcon
    rw [String.toList_ofList] at h2
    exact Nat.toDigits_ne_nil h2
  have hf : (fun (a : Nat) (d : Char) => a * 10 + (d.toNat - '0'.toNat))
      = (fun (a : Nat) (d : Char) => 10 * a + (d.toNat - '0'.toNat)) := by
    funext a d; simp [Nat.mul_comm]
  rw [if_neg hne, String.toList_ofList, hf, ← Nat.ofDigitChars_eq_foldl,
    Nat.ofDigitChars_ten_toDigits]

/-! ### the row law — renderRow parses back through parseRow -/

private theorem beq_false_of_isDigit {c : Char} (h : c.isDigit = true) :
    (c == '\n') = false := by
  cases hc : (c == '\n') with
  | false => rfl
  | true =>
      have he := beq_iff_eq.mp hc
      rw [he] at h
      simp [Char.isDigit] at h

private theorem ne_of_rowNameChar {c : Char} (h : rowNameChar c = true) :
    (c == '\n') = false := by
  have h2 := Bool.and_eq_true_iff.mp h
  have h3 := Bool.and_eq_true_iff.mp h2.1
  simpa using h3.2

private theorem renderRow_toList_flat (row : CodeRow) (hret : row.retired = false) :
    (renderRow row).toList
      = row.name.toList ++ '\t' :: (toString row.code).toList := by
  rw [renderRow, if_neg (by simp [hret]), String.toList_append,
    String.toList_append, String.toList_append, String.toList_empty,
    List.nil_append, List.append_assoc]
  rfl

private theorem renderRow_toList_tomb (row : CodeRow) (hret : row.retired = true) :
    (renderRow row).toList
      = '-' :: (row.name.toList ++ '\t' :: (toString row.code).toList) := by
  rw [renderRow, if_pos hret, String.toList_append,
    String.toList_append, String.toList_append, List.append_assoc]
  rfl

private theorem renderRow_ne_newline (row : CodeRow)
    (h : ∀ c ∈ row.name.toList, rowNameChar c = true) :
    ∀ c ∈ (renderRow row).toList, (c == '\n') = false := by
  have hdigit : ∀ c ∈ (toString row.code).toList, (c == '\n') = false := by
    intro c hc
    rw [toString_decDigits] at hc
    exact beq_false_of_isDigit (Nat.isDigit_of_mem_toDigits (by decide)
      (by decide) hc)
  cases hret : row.retired with
  | false =>
      intro c hc
      rw [renderRow_toList_flat row hret, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ne_of_rowNameChar (h c hc)
      · rcases List.mem_cons.mp hc with hc | hc
        · rw [hc]; simp
        · exact hdigit c hc
  | true =>
      intro c hc
      rw [renderRow_toList_tomb row hret, List.mem_cons, List.mem_append] at hc
      rcases hc with hc | hc
      · rw [hc]; simp
      · rcases hc with hc | hc
        · exact ne_of_rowNameChar (h c hc)
        · rcases List.mem_cons.mp hc with hc | hc
          · rw [hc]; simp
          · exact hdigit c hc

private theorem parseRowBody_render (cs : List Char) (code : Nat) (retired : Bool)
    (hall : ∀ c ∈ cs, rowNameChar c = true) (hne : String.ofList cs ≠ "") :
    parseRowBody (cs ++ '\t' :: (toString code).toList) retired
      = some ⟨String.ofList cs, code, retired⟩ := by
  have hfail : rowNameChar '\t' = false := rfl
  rw [parseRowBody, List.takeWhile_append_of_pos hall,
    List.dropWhile_append_of_pos hall]
  rw [List.takeWhile_cons_of_neg (by simp [hfail]),
    List.dropWhile_cons_of_neg (by simp [hfail])]
  simp only [List.append_nil, if_neg hne]
  rw [scanNat_toString]
  simp

private theorem parseRow_dash (rest : List Char) :
    parseRow (String.ofList ('-' :: rest)) = parseRowBody rest true := by
  rw [parseRow, String.toList_ofList]
  rfl

theorem parseRow_renderRow (row : CodeRow) (h : rowNameOk row.name) :
    parseRow (renderRow row) = some row := by
  obtain ⟨rname, rcode, rret⟩ := row
  have h12 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h12.1
  have hne : rname ≠ "" := by
    intro hcon
    rw [hcon] at h2
    simp at h2
  have hall : ∀ c ∈ rname.toList, rowNameChar c = true :=
    List.all_eq_true.mp h2.2
  have hhd := h12.2
  have hneL : String.ofList rname.toList ≠ "" := by
    rw [String.ofList_toList]
    exact hne
  cases rret with
  | false =>
      cases hcd : rname.toList with
      | nil =>
          exact absurd (show rname = "" from by
            rw [show rname = String.ofList rname.toList from
              String.ofList_toList.symm, hcd]) hne
      | cons c cs =>
          have hhd2 : rname.toList.head?.getD '-' = c := by simp [hcd]
          rw [hhd2] at hhd
          have hbeq'' : (c == '-') = false := by
            cases hb : (c == '-') with
            | false => rfl
            | true => rw [hb] at hhd; simp at hhd
          have hhd' : c ≠ '-' := by
            intro hcon
            rw [hcon] at hbeq''
            simp at hbeq''
          have hbeqS : (some c == some '-') = false := by simp [hbeq'']
          have hall' : ∀ x ∈ c :: cs, rowNameChar x = true := by
            intro x hx
            rw [← hcd] at hx
            exact hall x hx
          have hne' : String.ofList (c :: cs) ≠ "" := by
            rw [← hcd, String.ofList_toList]
            exact hne
          have hname' : String.ofList (c :: cs) = rname := by
            rw [← hcd, String.ofList_toList]
          rw [show renderRow ⟨rname, rcode, false⟩
              = String.ofList (renderRow ⟨rname, rcode, false⟩).toList from
            String.ofList_toList.symm, renderRow_toList_flat _ rfl,
            parseRow, String.toList_ofList, hcd, List.cons_append,
            List.head?_cons,
            if_neg (show ¬((some c == some '-') = true) from by simp [hbeqS]),
            if_neg (by simp), ← List.cons_append,
            parseRowBody_render (c :: cs) rcode false hall' hne', hname']
  | true =>
      have hnameL : String.ofList rname.toList = rname :=
        String.ofList_toList
      rw [show renderRow ⟨rname, rcode, true⟩
          = String.ofList (renderRow ⟨rname, rcode, true⟩).toList from
        String.ofList_toList.symm, renderRow_toList_tomb _ rfl,
        parseRow, String.toList_ofList,
        show (('-' :: (rname.toList ++ '\t' :: (toString rcode).toList)).head?
            == some '-') = true from rfl,
        if_pos rfl,
        show ('-' :: (rname.toList ++ '\t' :: (toString rcode).toList)).drop 1
          = rname.toList ++ '\t' :: (toString rcode).toList from rfl,
        parseRowBody_render rname.toList rcode true hall hneL, hnameL]

/-! ### the line structure — print's fold, splitOnP, the tail -/

private theorem print_foldl : ∀ (rest : CodeRegistry) (init : String),
    rest.foldl (fun acc row => acc ++ renderRow row ++ "\n") init
      = init ++ print rest
  | [], _ => by simp [print]
  | row :: rest, init => by
      rw [List.foldl_cons, print_foldl rest (init ++ renderRow row ++ "\n"),
        show print (row :: rest)
          = (row :: rest).foldl (fun acc x => acc ++ renderRow x ++ "\n") ""
          from rfl,
        List.foldl_cons,
        print_foldl rest ("" ++ renderRow row ++ "\n")]
      simp [String.append_assoc]

private theorem print_cons (row : CodeRow) (rest : CodeRegistry) :
    print (row :: rest) = renderRow row ++ "\n" ++ print rest := by
  show (row :: rest).foldl (fun acc x => acc ++ renderRow x ++ "\n") ""
    = renderRow row ++ "\n" ++ print rest
  rw [List.foldl_cons, print_foldl rest ("" ++ renderRow row ++ "\n")]
  simp

private theorem nl_list : "\n".toList = ['\n'] := rfl

private theorem splitOnP_print (r : CodeRegistry)
    (h : ∀ row ∈ r, ∀ c ∈ row.name.toList, rowNameChar c = true) :
    (print r).toList.splitOnP (· == '\n')
      = r.map (fun row => (renderRow row).toList) ++ [[]] := by
  induction r with
  | nil => simp [print, List.splitOnP_nil]
  | cons row rest ih =>
      rw [print_cons, String.toList_append, String.toList_append,
        nl_list, List.append_assoc, List.cons_append, List.nil_append]
      rw [List.splitOnP_append_cons (renderRow row).toList
        (print rest).toList (sep := '\n') rfl]
      rw [List.splitOnP_eq_singleton
        (renderRow_ne_newline row (h row (List.mem_cons_self)))]
      rw [ih (fun g hg => h g (List.mem_cons_of_mem _ hg))]
      simp [List.map_cons]

private theorem getLast?_append_singleton (xs : List String) (a : String) :
    (xs ++ [a]).getLast? = some a := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.getLast?_cons, ih]

private theorem dropLastEmpty_append (xs : List String) :
    dropLastEmpty (xs ++ [""]) = xs := by
  rw [dropLastEmpty, getLast?_append_singleton]
  rw [if_pos (by simp)]
  have hlen : (xs ++ [""]).length = xs.length + 1 := by simp
  rw [hlen, Nat.add_sub_cancel]
  induction xs with
  | nil => simp
  | cons x xs ih => simp

private theorem foldl_parseStep (r : CodeRegistry) : ∀ rows : List CodeRow,
    (∀ row ∈ r, parseRow (renderRow row) = some row) →
    (r.map renderRow).foldl parseStep (.ok rows) = .ok (r.reverse ++ rows) := by
  intro rows
  induction r generalizing rows with
  | nil => intro _h; rfl
  | cons row rest ih =>
      intro h
      simp only [List.map_cons, List.foldl_cons, parseStep,
        h row (List.mem_cons_self)]
      simp only [ih (row :: rows) (fun g hg => h g (List.mem_cons_of_mem _ hg)),
        List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]

private theorem map_ofList_map_toList (r : CodeRegistry) :
    List.map String.ofList (List.map (fun row => (renderRow row).toList) r)
      = r.map renderRow := by
  induction r with
  | nil => simp
  | cons row rest ih => simp

/-- THE FILE-FORMAT LAW: a well-formed registry prints to its canonical
    text and parses back to EXACTLY itself — the honest round trip over
    the canonical bytes. The name discipline `rowNameOk` is the
    format's metacharacter honesty (the reserved `-` head, the
    separators); the well-formedness gate accepts exactly what `wfProp`
    holds (the CheckedProp's completeness). -/
theorem parse_print (r : CodeRegistry) (hwf : CodeRegistry.wfProp r)
    (hnames : ∀ row ∈ r, rowNameOk row.name) :
    parse (print r) = .ok r := by
  have hchars : ∀ row ∈ r, ∀ c ∈ row.name.toList, rowNameChar c = true := by
    intro row hm c hc
    have h1 := Bool.and_eq_true_iff.mp (hnames row hm)
    exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp h1.1).2 c hc
  have hrow : ∀ row ∈ r, parseRow (renderRow row) = some row :=
    fun row hm => parseRow_renderRow row (hnames row hm)
  have hmap : List.map String.ofList
      (List.map (fun row => (renderRow row).toList) r ++ [[]])
      = r.map renderRow ++ [""] := by
    rw [List.map_append, List.map_singleton, map_ofList_map_toList]
  rw [parse, splitOnP_print r hchars, hmap, dropLastEmpty_append, parseLines,
    foldl_parseStep r [] hrow]
  simp only [List.append_nil, List.reverse_reverse]
  rw [if_pos (show codeRegistryWf.check r = true from
    Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true_iff.mpr hwf.1, (sortedCodes_iff _).mpr hwf.2⟩)]

/-! ## the coverage face — the tree's referenced codes vs the registry

05 §4's envelope discipline at the registry: every E-code the tree
writes is a HAND-STRUNG spelling that must name a LIVE row of the
persisted registry (the gate replays the file; this face is the tooth
that fails a hand-strung code outside it). The scan is over the (path,
literal) occurrences a file walk collects — the IO walk lives at the
gate (Gates.CodeRegistryCheck); the MATCHING + the verdict are pure
data here, so the teeth tests construct occurrences directly.
-/

/-- The declared E-code families: the shape table the coverage scan
    reads (a family's prefix + a 4-digit number). A new family lands
    HERE and in `notes/code-registry.txt` in the same change. -/
def codeFamilies : List String :=
  ["KB", "KD", "KL", "TK", "SC", "SD", "SCF", "SN", "SE", "WV", "SU", "GC",
    "EM"]

/-- The RAW code shape: uppercase letters (the family prefix's
    spelling) followed by exactly 4 digits — the family clause
    DROPPED. This is the scan's matcher: ANY literal of this shape is
    an E-code spelling, declared family or not. -/
def rawShape (s : String) : Bool :=
  let cs := s.toList
  let letters := cs.takeWhile Char.isUpper
  let digits := cs.drop letters.length
  cs.length = letters.length + digits.length
    && digits.length == 4
    && digits.all Char.isDigit

/-- The family prefix of a raw-shaped literal (its leading uppercase
    run). Only meaningful when `rawShape` holds. -/
def familyOf (s : String) : String :=
  String.ofList (s.toList.takeWhile Char.isUpper)

/-- The E-code shape: a declared family's prefix (uppercase letters,
    the family's spelling) followed by exactly 4 digits. -/
def codeShape (s : String) : Bool :=
  rawShape s && codeFamilies.contains (familyOf s)

/-- THE COVERAGE TOOTH, two teeth: (1) every RAW code-shaped literal
    (uppercase prefix + 4 digits) whose family prefix is UNDECLARED is
    a finding — a fresh prefix cannot bypass the registry by simply
    not being in the shape table; (2) every DECLARED-family code-shaped
    occurrence `(path, literal)` must name a LIVE registry row (a miss
    AND a tombstone fail — a spent code is not a live spelling). The
    offenders come back rendered, one line per occurrence. -/
def coverageOffenders (r : CodeRegistry)
    (hits : List (String × String)) : List String :=
  hits.filterMap fun (path, lit) =>
    if rawShape lit then
      if !codeFamilies.contains (familyOf lit) then
        some s!"{path}: `{lit}` is a code-shaped literal with an UNDECLARED \
family prefix `{familyOf lit}` — the E-code space has one registry: \
register the family in `codeFamilies` (Kit/Kit/CodeRegistry.lean) and \
allocate its rows in notes/code-registry.txt (the replay discipline), \
then spell it"
      else if r.lookup lit = none then
        some s!"{path}: `{lit}` is a hand-strung code — not a live row of \
the persisted registry (notes/code-registry.txt): allocate it there \
first, then spell it"
      else none
    else none


end CodeRegistry

end Kit
