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
RATION gates use `DataRegistry` (Kit.Registry); this module is the
persisted-runtime sibling.

The file format (`notes/code-registry.txt`): one row per line,
`name<TAB>code`, an optional leading `-` marking the tombstone, rows
sorted by code, LF line endings, no blank lines, no comments. The
format IS a `TextKit.Grammar` value (05 §1's typed grammar layer — the
flat rep-of-lines shape, `GrammarSlice`'s template): the derived
parser/printer replaced the old hand-rolled pair, and THE ROUND TRIP
IS THE GENERIC THEOREM'S INSTANCE: `parse_print` — a well-formed
(`wfProp`) registry with `rowNameOk` names prints to its canonical
bytes and parses back EXACTLY (`parse (print r) = .ok r`) —
`Grammar.run_print_fixFree` (+ the wrapper's newline discipline + the
wf gate); the exactness direction instantiates `Grammar.print_parse`.
The gate re-derives the bytes and the KitTests pin rides the theorem.

Core-only (no mathlib/Batteries). Five questions (notes/v3/01-core.md):
- root: DATA — Universe content (closed codes + total denotation); the
  allocation discipline is the Change ladder's irreversible rung
  (allocate never reassigns: the delta retains old information).
- carrier grade: first-order over String/Nat/List — guest-thinkable
  (the guest's ids ride the same codes).
- spine reading: as-data (the gate replays it; nothing prints but the
  total `print`).
- ladder rung: rung 2-3 — `sortedCodes_iff` + the CheckedProp proofs
  are small inductions; the format's round trip is the generic laws'
  INSTANCE (the lexeme fields + the wrapper discipline are the only
  format-local proofs).
- gate row: `gates code-registry-check` (Gates.CodeRegistryCheck) + the
  KitTests pins + the axiom pins in KitTests.Axioms.
-/

module

public import Kit.CheckedProp
public import TextKit.Basic
public import TextKit.Literals
public import TextKit.Grammar
public import TextKit.Grammar.Lexemes
public import TextKit.Grammar.Check
public import TextKit.Grammar.Laws

@[expose] public section
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

/-! ## the file format — a Grammar value (05 §1's typed grammar layer) -/

open TextKit

/-- A row name's charset: anything but the separators (a LEADING `-`
    is the tombstone marker — names starting with `-` are reserved). -/
def rowNameChar (c : Char) : Bool := c != '\t' && c != '\n' && c != '\r'

/-- A row name's round-trip discipline: nonempty, separator-free, and
    NOT `-`-led (a leading `-` is the reserved tombstone marker — the
    format's metacharacter honesty). This is the name lexeme's
    write-side gate (`pre`) — exactly the value discipline the
    round-trip law needs. (The emptiness is read at the toList —
    `List.isEmpty` — the same discipline, at the grade the proofs
    reduce.) -/
def rowNameOk (s : String) : Bool :=
  !s.toList.isEmpty && s.toList.all rowNameChar
    && !(s.toList.head?.getD '-' == '-')

/-! ### the lexemes (TextKit.Grammar.Lexemes' shared constructors —
     the 06 §7 generator: the per-format constructions were N
     near-identical ~300-line proofs; the obligations discharge ONCE
     at the generic shape, and these are the instantiations) -/

/-- The registry's single-char literal (the separators `-`, `\t`,
    `\n`): the shared const-char lexeme at the unit payload — the
    exact one-char scan whose `print_scan` holds over ANY suffix (the
    lit-scan's exactness), so it carries no munch. -/
def charLex (c : Char) : Lexeme Unit := TextKit.constCharLex c ()

/-- The format's three literal tokens: the tombstone marker, the
    name/code separator, the line terminator. -/
def dashAtom : Lexeme Unit := charLex '-'
def tabAtom : Lexeme Unit := charLex '\t'
def nlAtom : Lexeme Unit := charLex '\n'

/-- The row-name head class: a `rowNameChar` that is not the tombstone
    marker `-` (the dash-led run parses ONLY as a tombstone — the
    metacharacter honesty; the WF-SEQ-1 row at the opt-dash junction
    demands the disjointness from `lit "-"`). -/
def nameHeadChar (c : Char) : Bool := rowNameChar c && !(c == '-')

/-- The head class rides the run class (the ident-atom's chain
    premise). -/
theorem nameHeadChar_chain : ∀ c, nameHeadChar c = true → rowNameChar c = true :=
  fun _c hc => (Bool.and_eq_true_iff.mp hc).1

/-- `rowNameOk` IS the shared ident-atom's gate: the head-class form of
    the same discipline (the bridge to `TextKit.identOk` — pointwise
    equal; the getD form is the spell the format's gate reads at). -/
theorem rowNameOk_eq (s : String) :
    rowNameOk s = TextKit.identOk nameHeadChar rowNameChar s := by
  cases hs : s.toList with
  | nil => simp [rowNameOk, TextKit.identOk, hs]
  | cons c cs =>
      show ((!s.toList.isEmpty && s.toList.all rowNameChar) &&
          !(s.toList.head?.getD '-' == '-')) =
        ((!s.toList.isEmpty && s.toList.all rowNameChar) &&
          s.toList.head?.all nameHeadChar)
      rw [hs, List.isEmpty_cons, List.head?_cons]
      simp only [Bool.not_false, Option.getD_some, Option.all_some]
      cases hrc : rowNameChar c with
      | false => simp [hrc, nameHeadChar]
      | true =>
          cases hb : (c == '-') with
          | false => simp [hrc, hb, nameHeadChar]
          | true => simp [hrc, hb, nameHeadChar]

/-- The row-name lexeme: the shared ident-atom at the registry's char
    classes (`munch` is the charset itself — the separator `\t` breaks
    it, the maximal-munch boundary). -/
def nameAtom : Lexeme String :=
  TextKit.identAtom "<name>" nameHeadChar rowNameChar nameHeadChar_chain

/-- The code lexeme: the shared nat-atom (the canonical-scanNat
    discipline — a leading zero is a refusal). -/
def codeAtom : Lexeme Nat := TextKit.natAtom

/-! ### the row + the line -/

/-- The row's raw parse shape (the seq/opt tuple face; the units are
    the separator markers' payloads). -/
abbrev RowRaw := Option Unit × (String × (Unit × Nat))

open Grammar in
/-- One row: the optional tombstone dash, the name, the TAB, the code. -/
def rowRawGrammar : Grammar RowRaw :=
  .seq (.opt (.atom dashAtom))
    (.seq (.atom nameAtom) (.seq (.atom tabAtom) (.atom codeAtom)))

/-- One raw row → the row (the tombstone bit is the dash's presence;
    the separator units drop). -/
def rowDecode : RowRaw → Option CodeRow :=
  fun raw => some ⟨raw.2.1, raw.2.2.2, raw.1.isSome⟩

/-- A row → its raw spelling (encode). -/
def rowEncode : CodeRow → RowRaw :=
  fun row => ((if row.retired then Option.some () else Option.none),
    (row.name, ((), row.code)))

open Grammar in
/-- One line: the row + the LF terminator (one per line — the
    committed file's discipline; the parse wrapper handles a MISSING
    final newline). -/
def lineRawGrammar : Grammar (RowRaw × Unit) :=
  .seq rowRawGrammar (.atom nlAtom)

/-- The raw line list → the registry. -/
def rowsDecode : List (RowRaw × Unit) → Option CodeRegistry
  | [] => Option.some []
  | p :: rest =>
      match rowDecode p.1 with
      | .some row => (rowsDecode rest).map (fun r' => row :: r')
      | .none => .none

/-- THE registry codec: the raw IS the line list; decode unmaps the
    rows (the tombstone bit from the dash's presence). -/
def registryCodec : Kit.Codec (List (RowRaw × Unit)) CodeRegistry where
  encode := fun r => r.map (fun row => (rowEncode row, ()))
  decode := rowsDecode
  policy := fun _ => True
  decode_encode := by
    intro r
    induction r with
    | nil => rfl
    | cons row rest ih =>
        have hrow : rowDecode (rowEncode row) = some row := by
          cases row with
          | mk name code retired =>
              cases retired <;> simp [rowDecode, rowEncode]
        show rowsDecode ((rowEncode row, ()) :: (rest.map fun row => (rowEncode row, ())))
          = some (row :: rest)
        simp only [rowsDecode, hrow, ih, Option.map_some]
  decode_some_policy := fun _ _ _ => trivial

/-- The codec's left-inverse (the rel node's `exact` field): decode
    determines encode — the raw spelling is recovered. (Public: the
    graduation's exactness premise cites it.) -/
theorem rowEncode_of_decode (rv : RowRaw) (row : CodeRow)
    (h : rowDecode rv = .some row) : rowEncode row = rv := by
  obtain ⟨dash, nm, u, cd⟩ := rv
  cases u
  rw [rowDecode] at h
  have hrow : ⟨nm, cd, dash.isSome⟩ = row := Option.some.inj h
  cases dash <;> rw [← hrow] <;> simp [rowEncode]

theorem encode_of_rowsDecode : ∀ (raw : List (RowRaw × Unit)) (r : CodeRegistry),
    rowsDecode raw = .some r → r.map (fun row => (rowEncode row, ())) = raw := by
  intro raw
  induction raw with
  | nil =>
      intro r h
      simp only [rowsDecode] at h
      have hr : r = [] := (Option.some.inj h).symm
      rw [hr]; rfl
  | cons p rest ih =>
      intro r h
      simp only [rowsDecode] at h
      cases hrw : rowDecode p.1 with
      | none => rw [hrw] at h; simp at h
      | some row =>
          rw [hrw] at h
          cases hr2 : rowsDecode rest with
          | none => rw [hr2] at h; simp at h
          | some rs =>
              rw [hr2] at h
              simp only [Option.map_some, Option.some.injEq] at h
              have hr : r = row :: rs := h.symm
              show List.map (fun row => (rowEncode row, ())) r = p :: rest
              rw [hr, List.map_cons, rowEncode_of_decode p.1 row hrw]
              have hrest : rs.map (fun row => (rowEncode row, ())) = rest :=
                ih rs (by rw [hr2])
              rw [hrest]

/-- The decode's TOTALITY as data (the graduation's witness function):
    the raw line list never refuses — every row decodes (the row level
    is total: `rowDecode` is `some`-valued by construction) and the
    fold recurses. -/
def rowsDecodeTotal : ∀ (raw : List (RowRaw × Unit)),
    {r : CodeRegistry // rowsDecode raw = some r}
  | [] => ⟨[], rfl⟩
  | ((dash, (nm, ((), code))), ()) :: rest =>
      let t := rowsDecodeTotal rest
      ⟨⟨nm, code, dash.isSome⟩ :: t.1, by
        simp only [rowsDecode, rowDecode, t.2, Option.map_some]⟩

/-- THE GRADUATION (15-patterns #11 at the codec grade,
    `Kit.Codec.toIsoOfExact`): the total decode + the exactness law
    (`encode_of_rowsDecode`) assemble the TRUE `Iso` — the raw line
    list ≅ the registry, both round trips. -/
def registryIso : Kit.Iso (List (RowRaw × Unit)) CodeRegistry :=
  registryCodec.toIsoOfExact rowsDecodeTotal encode_of_rowsDecode

open Grammar in
/-- THE file format as a grammar value: the flat rep-of-lines (the
    slice's shape — no `fix`, no `self` anywhere), under the registry
    codec (the ONE `rel` node; the raw IS the line list). -/
def registryGrammar : Grammar CodeRegistry :=
  .rel registryCodec (fun _ => true) (fun _ _ _ => rfl)
    (fun _raw _r h => encode_of_rowsDecode _ _ h)
    "registry" [] (.rep lineRawGrammar)

/-! ### the certificate + the law premises' discharge -/

/-- THE certificate discharge (06 §7's build-time check): the format's
    WF rows hand-check green (WF-REP-1: the line is non-nullable;
    WF-REP-2: vacuous — the LF atom's munch is none; WF-SEQ-1: the
    dash/name heads vs the TAB/LF literals are prefix-free; WF-SEQ-2:
    the name's munch broken by the TAB literal, the code's munch broken
    by the LF literal). -/
theorem registryCert : Grammar.Predictive registryGrammar :=
  Grammar.wfCheck_sound registryGrammar (by decide)

/-- The fix-free fold (no `fix` node anywhere). -/
theorem registryFixFree : Grammar.FixFree registryGrammar := by
  repeat constructor

/-- Law 2's coherence premise: NO `alt` node anywhere — the fold's
    branches are all trivial. -/
theorem registryCoherent : Grammar.altCoherent registryGrammar := by
  repeat constructor

/-- The valueOk faces at the raw row (the folds' simp readings — the
    value discipline is the name lexeme's `pre` and nothing else). -/
private theorem valueOk_row_none (name : String) (code : Nat)
    (h : rowNameOk name = true) :
    Grammar.valueOk rowRawGrammar ((Option.none : Option Unit), (name, ((), code)))
      = true := by
  have hp : nameAtom.pre name = true := by
    show TextKit.identOk nameHeadChar rowNameChar name = true
    rw [← rowNameOk_eq]
    exact h
  simp [Grammar.valueOk, rowRawGrammar, charLex, tabAtom, codeAtom,
    dashAtom, constCharLex, natAtom, hp]

private theorem valueOk_row_some (name : String) (code : Nat)
    (h : rowNameOk name = true) :
    Grammar.valueOk rowRawGrammar ((Option.some () : Option Unit), (name, ((), code)))
      = true := by
  have hp : nameAtom.pre name = true := by
    show TextKit.identOk nameHeadChar rowNameChar name = true
    rw [← rowNameOk_eq]
    exact h
  simp [Grammar.valueOk, rowRawGrammar, charLex, tabAtom, codeAtom,
    dashAtom, constCharLex, natAtom, hp]

private theorem valueOk_nl : Grammar.valueOk (.atom nlAtom) () = true := rfl

/-- The grammar's value discipline IS the name discipline: `valueOk`
    holds exactly when every row's name is `rowNameOk` (the name
    lexeme's write-side gate; every other field is trivially owned). -/
theorem valueOk_names (r : CodeRegistry) (h : ∀ row ∈ r, rowNameOk row.name) :
    Grammar.valueOk registryGrammar r = true := by
  have hline : ∀ row : CodeRow, rowNameOk row.name = true →
      Grammar.valueOk lineRawGrammar (rowEncode row, ()) = true := by
    intro row hn
    cases row with
    | mk name code retired =>
        cases retired with
        | false =>
            show Grammar.valueOk lineRawGrammar
                (((Option.none : Option Unit), (name, ((), code))), ()) = true
            simp [lineRawGrammar, Grammar.valueOk, charLex, nlAtom,
              valueOk_row_none name code hn]
        | true =>
            show Grammar.valueOk lineRawGrammar
                (((Option.some () : Option Unit), (name, ((), code))), ()) = true
            simp [lineRawGrammar, Grammar.valueOk, charLex, nlAtom,
              valueOk_row_some name code hn]
  show (r.map (fun row => (rowEncode row, ()))).all
    (fun z => Grammar.valueOk lineRawGrammar z) = true
  rw [List.all_eq_true]
  intro z hz
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hz
  exact hline row (h row hr)

/-! ### the derived print/parse (the wrappers) -/

/-- The row's spelling (the derived printer at the raw row) — the old
    hand-rolled `renderRow`'s bytes, now the grammar's. -/
def rowPrint : RowRaw → String := Grammar.printG rowRawGrammar

/-- Print the registry: the grammar's derived printer — one
    `[-]name<TAB>code` row per line, LF-terminated (the committed
    file's canonical bytes; byte-identical to the old hand-rolled
    `print`, which died). -/
def print (r : CodeRegistry) : String := Grammar.print registryGrammar r

/-- Parse the file: the grammar's derived parser (the run entry) + the
    well-formedness gate — an ill-formed (unsorted, duplicate-named)
    file is a REFUSAL, never a silent accept. The trailing-newline
    discipline: a MISSING final newline canonicalizes (the wrapper
    appends the LF the line terminator needs; the empty file is the
    empty registry). -/
def parse (s : String) : Except String CodeRegistry :=
  let s' := if s == "" || s.toList.getLast? == some '\n' then s else s ++ "\n"
  match Grammar.run registryGrammar s' with
  | .error _ =>
      .error "code-registry: malformed row — expected `[-]name<TAB>code` \
(the `-` marks a retired tombstone); one row per line, LF endings, no \
blank lines"
  | .ok r =>
      if codeRegistryWf.check r then .ok r
      else .error "code-registry: ill-formed registry — names must be \
unique and rows sorted by code (distinct codes ride the strict order)"

private theorem print_nil : print [] = "" := rfl

private theorem print_cons (row : CodeRow) (rest : CodeRegistry) :
    print (row :: rest) = (rowPrint (rowEncode row) ++ "\n") ++ print rest := rfl

private theorem getLast?_append_nl (xs : List Char) :
    (xs ++ ['\n']).getLast? = some '\n' := by
  rw [List.getLast?_append]
  simp

private theorem getLast?_append_right (a b : List Char) (hb : b ≠ []) :
    (a ++ b).getLast? = b.getLast? := by
  rw [List.getLast?_append]
  cases hb2 : b.getLast? with
  | none => exact absurd hb2 (by simp [hb])
  | some l => simp

/-- The derived print is LF-terminated (the last byte of a nonempty
    registry's print — the parse wrapper's no-append branch on the
    canonical bytes). -/
private theorem print_last_newline : ∀ (r : CodeRegistry), r ≠ [] →
    (print r).toList.getLast? = some '\n' := by
  intro r
  induction r with
  | nil => intro h; exact absurd rfl h
  | cons row rest ih =>
      intro hne
      rw [print_cons, String.toList_append]
      cases rest with
      | nil =>
          show ((rowPrint (rowEncode row) ++ "\n").toList ++ ([] : List Char)).getLast?
            = Option.some '\n'
          rw [List.append_nil, String.toList_append, TextKit.lit_nl,
            getLast?_append_nl]
      | cons r2 rs =>
          have hrest : (r2 :: rs) ≠ [] := by simp
          have hne2 : (print (r2 :: rs)).toList ≠ [] := by
            have h3 := ih hrest
            intro h0; rw [h0] at h3; simp at h3
          rw [getLast?_append_right _ _ hne2]
          exact ih hrest

/-! ### the round trip — the file format's law, the generic instances -/

/-- THE FILE-FORMAT LAW (the grammar layer's instance): a well-formed
    registry prints to its canonical text and parses back to EXACTLY
    itself. The hand-proved family of the pre-grammar file (the digit
    token's law, the row law, the line-structure fold — ~250 lines)
    died here: the content is `Grammar.run_print_fixFree`'s; what
    remains is the wrapper's newline discipline + the wf gate. -/
theorem parse_print (r : CodeRegistry) (hwf : CodeRegistry.wfProp r)
    (hnames : ∀ row ∈ r, rowNameOk row.name) :
    parse (print r) = .ok r := by
  simp only [parse]
  have hcond : ((print r == "" || (print r).toList.getLast? == some '\n') = true) := by
    cases r with
    | nil => rw [print_nil]; simp
    | cons row rest => simp [print_last_newline (row :: rest) (by simp)]
  rw [if_pos hcond]
  have hrun : Grammar.run registryGrammar (print r) = .ok r :=
    Grammar.run_print_fixFree registryGrammar registryFixFree registryCert r
      (valueOk_names r hnames)
  simp only [hrun]
  rw [if_pos (show codeRegistryWf.check r = true from
    Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true_iff.mpr hwf.1, (sortedCodes_iff _).mpr hwf.2⟩)]

/-- Law 2 (the exactness direction) at the registry's grammar: a
    successful derived parse consumed EXACTLY the print of its result
    (+ the parsed value is value-owned — the name discipline). -/
theorem print_parse (fuel : Nat) (ys : CodeRegistry) (cur cur' : Cursor)
    (h : Grammar.parseG registryGrammar fuel cur = .ok (ys, cur')) :
    cur.cs = (print ys).toList ++ cur'.cs ∧
    cur'.off = cur.off + (print ys).length ∧
    Grammar.valueOk registryGrammar ys = true :=
  Grammar.print_parse registryGrammar fuel registryCoherent h
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
    "EM", "IN", "FT", "QL", "SS", "LK", "GT", "CX", "SR", "CF", "WD"]

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

end -- public section
