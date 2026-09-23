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
05 §1 is a later order — there the round-trip laws upgrade from pins to
theorems; here `parse (print r)` is pinned in KitTests and the gate
re-derives the bytes).

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

/-- Parse one line: `[-]name<TAB>code`. Total; `none` = malformed. -/
def parseRow (line : String) : Option CodeRow :=
  match line.toList with
  | [] => none
  | '-' :: rest => parseRowBody rest true
  | _ => parseRowBody line.toList false

/-- Parse the file: one `[-]name<TAB>code` row per line, LF endings,
    no blank lines; the final newline's empty tail is the file's, not a
    row's. The result must satisfy `codeRegistryWf.check` — an
    ill-formed (unsorted, duplicate-named) file is a REFUSAL, never a
    silent accept. Total over String. -/
def parse (s : String) : Except String CodeRegistry :=
  let ls := s.splitOn "\n"
  let ls := if ls.getLast? == some "" then ls.take (ls.length - 1) else ls
  match ls.foldl (fun (acc : Except String (List CodeRow)) (line : String) =>
      match acc with
      | .error e => .error e
      | .ok rows =>
          match parseRow line with
          | some row => .ok (row :: rows)
          | none => .error "code-registry: malformed row — expected \
`[-]name<TAB>code` (the `-` marks a retired tombstone); no blank lines")
      (.ok []) with
  | .error e => .error e
  | .ok revRows =>
      let r := revRows.reverse
      if codeRegistryWf.check r then .ok r
      else .error "code-registry: ill-formed registry — names must be unique \
and rows sorted by code (distinct codes ride the strict order)"

end CodeRegistry

end Kit
