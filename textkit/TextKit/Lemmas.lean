/-
# TextKit.Lemmas — the inversion kit

The theorem content the proofs consume (notes/v3/15-patterns.md #12):
the prefix kit's inversions (`startsWith_self`/`expect_self`), the
head-predicate exclusions (a scanner's accept side has a matching head;
a mismatched head refuses), and the bare-name inversion
(`scanIdent_of_identifier`). Mined from
`legacy/lean/TextKit/TextKit/Basic.lean` (same statements, re-proved
against the FRESH direct definitions — no `where`-clause unfolding).

Ownership: this file owns the scanners' INVERSION statements; the
definitions live in `TextKit.Basic`. A scanner behavior change that
breaks an inversion here is the proof doing its job.

The five questions (notes/v3/01-core.md):
- root: Universe — the theorems over TextKit.Basic's scanners.
- carrier grade: none — inversion statements about pure functions.
- spine reading: none — the proof surface the consumers' reductions
ride.
- ladder rung: hand theorems of the small generic kind (01 §7's
"often the best foundation").
- gate row: none yet — TextKit is outside Gates.Packages' gated set;
TextKitTests.Axioms pins these lemmas' cones (core triple only).
-/

module

public import TextKit.Basic

@[expose] public section

namespace TextKit

/-! ## the prefix kit inversions -/

/-- A literal prefix is recognized after itself. -/
theorem startsWith_self (p : String) (rest : List Char) :
    startsWith (p.toList ++ rest) p = true := by
  unfold startsWith
  rw [List.isPrefixOf_iff_prefix]
  exact ⟨rest, rfl⟩

/-- A literal prefix is consumed by `expect`. -/
theorem expect_self (p : String) (rest : List Char) :
    expect p (p.toList ++ rest) = some rest := by
  unfold expect
  rw [if_pos (startsWith_self p rest)]
  have h : p.length = p.toList.length := rfl
  rw [h, List.drop_left]

/-- Head-predicate exclusion: a prefix whose head differs from the
    input's head is NOT a prefix of it (the head mismatch decides). -/
theorem startsWith_cons_ne (p0 : Char) (ps : List Char) (c : Char) (rest : List Char)
    (h : p0 ≠ c) :
    startsWith (c :: rest) (String.ofList (p0 :: ps)) = false := by
  have h1 : (p0 :: ps).isPrefixOf (c :: rest) = (p0 == c && ps.isPrefixOf rest) := rfl
  have hbeq : (p0 == c) = false := by simp [h]
  unfold startsWith
  rw [String.toList_ofList, h1, hbeq]
  rfl

/-- Head-predicate exclusion: `expect` refuses a mismatched head. -/
theorem expect_cons_ne (p0 : Char) (ps : List Char) (c : Char) (rest : List Char)
    (h : p0 ≠ c) :
    expect (String.ofList (p0 :: ps)) (c :: rest) = none := by
  unfold expect
  rw [startsWith_cons_ne p0 ps c rest h]
  rfl

/-! ## the scanner exclusions -/

/-- Head-predicate exclusion: `scanIdent` refuses a non-alpha head. -/
theorem scanIdent_none_of_not_alpha (c : Char) (rest : List Char)
    (h : c.isAlpha = false) :
    scanIdent (c :: rest) = none := by
  simp only [scanIdent, h, Bool.false_eq_true, if_false]

/-- Head-predicate exclusion: `scanNat` refuses a non-digit head. -/
theorem scanNat_none_of_not_digit (c : Char) (rest : List Char)
    (h : c.isDigit = false) :
    scanNat (c :: rest) = none := by
  have htake : (c :: rest).takeWhile Char.isDigit = [] :=
    List.takeWhile_cons_of_neg (by simp [h])
  unfold scanNat
  rw [htake]
  rfl

/-! ## the takeWhile scanner's inversion -/

/-- A list whose head fails `p` has an empty `takeWhile` and a full
    `dropWhile` (the maximal scan's break condition). -/
theorem takeDrop_head {p : Char → Bool} {r : List Char}
    (hr : r.head?.all (fun c => !p c)) :
    r.takeWhile p = [] ∧ r.dropWhile p = r := by
  cases r with
  | nil => simp
  | cons c cs =>
      have h1 : ¬ p c := by simpa using hr
      simp [h1]

/-- The token-scan round trip: the maximal `Parser.takeWhile` scan of
    `w ++ r` stops exactly at `w` (all of `w` passes `p`, `r`'s head
    fails it) — it returns the token `w` and hands back the rest `r`. -/
theorem takeWhile_stop {p : Char → Bool} {w r : List Char}
    (hw : w.all p) (hr : r.head?.all (fun c => !p c)) :
    Parser.takeWhile p (w ++ r) = (String.ofList w, r) := by
  show some (String.ofList ((w ++ r).takeWhile p), (w ++ r).dropWhile p) = _
  rw [List.takeWhile_append_of_pos (List.all_eq_true.mp hw),
      List.dropWhile_append_of_pos (List.all_eq_true.mp hw)]
  have hd := takeDrop_head (p := p) hr
  rw [hd.1, List.append_nil, hd.2]

/-! ## the bare-name inversion -/

/-- Bare-name inversion: an identifier scans back to itself, provided the
    following text starts with a non-identifier character (emitters
    always follow names with a delimiter). -/
theorem scanIdent_of_identifier (n : String) (h : isIdentifier n = true)
    (rest : List Char)
    (hsep : rest = [] ∨ ∃ c0 rest0, rest = c0 :: rest0 ∧ isIdentChar c0 = false) :
    scanIdent (n.toList ++ rest) = some (n, rest) := by
  unfold isIdentifier at h
  cases hn : n.toList with
  | nil => rw [hn] at h; simp at h
  | cons c tail =>
    rw [hn] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hc, htail⟩ := h
    have hall : ∀ a ∈ tail, isIdentChar a := List.all_eq_true.mp htail
    show scanIdent (c :: (tail ++ rest)) = _
    have hopen : scanIdent (c :: (tail ++ rest))
        = some (String.ofList ((c :: (tail ++ rest)).takeWhile isIdentChar),
                (c :: (tail ++ rest)).dropWhile isIdentChar) := by
      simp only [scanIdent, hc]
      rfl
    rw [hopen]
    have hic : isIdentChar c = true := by
      unfold isIdentChar
      rw [hc]
      rfl
    rw [List.takeWhile_cons_of_pos hic]
    rw [List.takeWhile_append_of_pos hall]
    rw [List.dropWhile_cons_of_pos hic]
    rw [List.dropWhile_append_of_pos hall]
    cases hsep with
    | inl hr =>
      subst hr
      rw [List.takeWhile_nil, List.dropWhile_nil, List.append_nil, ← hn,
        String.ofList_toList]
    | inr hr =>
      obtain ⟨c0, rest0, hr, h0⟩ := hr
      subst hr
      have h0' : ¬ (isIdentChar c0 = true) := by simp [h0]
      rw [List.takeWhile_cons_of_neg h0', List.dropWhile_cons_of_neg h0',
        List.append_nil, ← hn, String.ofList_toList]

end TextKit

end -- @[expose] public section
