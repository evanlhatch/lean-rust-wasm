/-
# TextKit.Grammar.Lexemes — the shared lexeme constructors

The lexeme-construction generator (06 §7: a family of N near-identical
constructions is a generator that hasn't been written; 05 §1: every
text format consumes the grammar value). A `Lexeme` carries ~9 proof
fields, and the per-format constructions were the grammar migration's
honest friction: the SAME shapes re-proved per format. This module is
the ONE home for the shared shapes — each constructor's obligations
discharged ONCE, at the generic shape:

- `constCharLex` — the single-char literal at a fixed payload (the
  separator/tombstone atoms; the slice's value-constant token). Its
  `pre` is value-selective (`w = v`) — that is exactly what
  `print_scan` needs, and at a unit payload it is `true`.
- `identAtom` — the ident-atom: a maximal `p`-run LED by an `h`-char
  (the chain premise `h → p` keeps the run nonempty — the `consumes`
  field's honesty), `pre` the run's round-trip gate, `head` the
  `.cls h`, `munch` the run class (the maximal-munch boundary).
- `natAtom` — the nat-atom: `TextKit.scanNat` guarded to the
  CANONICAL spelling (a leading zero is a refusal — the raw `01` is
  not the spelling of the value it scans to, and `scan_exact` demands
  the raw), `munch` the digit class.

Per-format LEXEMES (a format's own word/quoted-string lexemes with
their own escape discipline) stay with their format; only the shapes
every format re-derives land here. Consumers (the honest set):
Kit.CodeRegistry's `charLex`/`nameAtom`/`codeAtom`,
TextKitTests.GrammarSlice's `boolLex`, and Wit.Parse's keyword
literals (`constStrLex` — the shape SchemaCore.Snapshot first derived
locally as `litLex`; two derivations = the generator rule, 06 §7).

Core-only (no mathlib/Batteries). The five questions
(notes/v3/01-core.md):
- root: Universe — pure data over `List Char`/`String`/`Nat`.
- carrier grade: none of its own — the constructors BUILD `Lexeme`
  values; the Lexeme interface's laws are the obligation surface.
- spine reading: none — the leaf layer the grammar values compose.
- ladder rung: rung 2-3 — small list inductions (the takeWhile kit),
  the obligations discharged once at the parameterized shape.
- gate row: none — TextKit is outside Gates.Packages' gated set;
  TextKitTests pins the constructors' teeth + the negative controls.

MODULE FORM: a NON-`module` file (rides `TextKit.Grammar`'s form —
the Lexeme interface lives there; consumers `import
TextKit.Grammar.Lexemes` directly).
-/

import TextKit.Grammar

namespace TextKit

/-! ## the takeWhile kit (the maximal-munch boundary's lemmas) -/

/-- A takeWhile member passes the predicate. PUBLIC: the consumers
    outside this module (SchemaCore.Snapshot's ty-atom `print_scan`). -/
theorem mem_takeWhile {p : Char → Bool} : ∀ (cs : List Char) (c : Char),
    c ∈ cs.takeWhile p → p c = true := by
  intro cs
  induction cs with
  | nil => intro c h; simp at h
  | cons a l ih =>
      intro c h
      simp only [List.takeWhile_cons] at h
      split at h
      · next ha =>
          rcases List.mem_cons.mp h with rfl | hmem
          · exact ha
          · exact ih c hmem
      · simp at h

/-- Its dropWhile twin: a suffix whose head fails `p` is all `p`-failure
    — the dropWhile keeps it whole. -/
private theorem dropWhile_self_of_head_fail {p : Char → Bool} : ∀ sfx : List Char,
    sfx.head?.all (fun c => !p c) = true → sfx.dropWhile p = sfx := by
  intro sfx h
  cases sfx with
  | nil => rfl
  | cons c rest =>
      have hc : p c = false := by
        have h2 := h
        simp only [List.head?_cons, Option.all_some] at h2
        simpa using h2
      simp [hc]

/-- The maximal-munch boundary: a suffix whose head fails `p` has the
    empty `p`-run. -/
private theorem takeWhile_nil_of_head_fail {p : Char → Bool} : ∀ sfx : List Char,
    sfx.head?.all (fun c => !p c) = true → sfx.takeWhile p = [] := by
  intro sfx h
  cases sfx with
  | nil => rfl
  | cons c rest =>
      have hc : p c = false := by
        have h2 := h
        simp only [List.head?_cons, Option.all_some] at h2
        simpa using h2
      simp [hc]

/-- The takeWhile of an all-pass run ++ a head-failing suffix is the run
    (the maximal-munch boundary, the takeWhile face). PUBLIC: the
    consumers outside this module (SchemaCore.Snapshot's ty-atom
    `print_scan`). -/
theorem takeWhile_append_stop {p : Char → Bool} : ∀ (l sfx : List Char),
    (∀ c ∈ l, p c = true) → sfx.head?.all (fun c => !p c) = true →
    (l ++ sfx).takeWhile p = l := by
  intro l
  induction l with
  | nil => intro sfx _ hm; exact takeWhile_nil_of_head_fail sfx hm
  | cons a l ih =>
      intro sfx hall hm
      have ha := hall a (List.Mem.head _)
      rw [List.cons_append, List.takeWhile_cons_of_pos ha,
        ih sfx (fun g hg => hall g (List.Mem.tail a hg)) hm]

/-- Its dropWhile twin: the run is consumed, the suffix stays. PUBLIC:
    the consumers outside this module (SchemaCore.Snapshot's ty-atom
    `print_scan`). -/
theorem dropWhile_append_stop {p : Char → Bool} : ∀ (l sfx : List Char),
    (∀ c ∈ l, p c = true) → sfx.head?.all (fun c => !p c) = true →
    (l ++ sfx).dropWhile p = sfx := by
  intro l
  induction l with
  | nil => intro sfx _ hm; exact dropWhile_self_of_head_fail sfx hm
  | cons a l ih =>
      intro sfx hall hm
      have ha := hall a (List.Mem.head _)
      rw [List.cons_append, List.dropWhile_cons_of_pos ha,
        ih sfx (fun g hg => hall g (List.Mem.tail a hg)) hm]

/-! ## the canonical field kit (the lexeme fields' shared extraction)

The generator rule (06 §7): the constructors' obligation set is ONE
shape — the OK-SHAPE (a success splits the input exactly at the
printed spelling: exactness, offset, gate, print-nonemptiness) plus
the MUNCH/HEAD SPEC (`head_ok`: a gate-passing print's continuation
always matches the head). The derived fields (`scan_head`,
`head_fail`, `consumes`) are extracted here ONCE; a constructor's
remaining rows are its ok-shape, the head spec, `print_scan`, and
`head_ne`. (The full-wrapper form — one `Lexeme.canonical` the four
become applications of — is walled by Wit.Parse's bridges, which
`unfold` the constructors and reduce the projections by `simp only`
iota, impossible through a wrapper def; the kit keeps each constructor
a direct structure literal and derives the PROOF fields.) -/

/-- `scan_head` from the ok-shape + the head spec. -/
theorem canonScan_head {R : Type} {scan : GParser R} {printF : R → String}
    {preF : R → Bool} {head : HeadSpec}
    (hok : ∀ r sfx, preF r = true → head.matches ((printF r).toList ++ sfx) = true)
    (ok : ∀ cur r cur', scan cur = .ok (r, cur') →
      cur.cs = (printF r).toList ++ cur'.cs ∧
        cur'.off = cur.off + (printF r).length ∧ preF r = true ∧
        (printF r).toList ≠ [])
    (cur : Cursor) (r : R) (cur' : Cursor) (h : scan cur = .ok (r, cur')) :
    head.matches cur.cs = true := by
  rw [(ok cur r cur' h).1]
  exact hok r cur'.cs (ok cur r cur' h).2.2.1

/-- `head_fail` from the same pair (the ok-shape's contradiction — no
    error-witness plumbing). -/
theorem canonScan_head_fail {R : Type} {scan : GParser R} {printF : R → String}
    {preF : R → Bool} {head : HeadSpec}
    (hok : ∀ r sfx, preF r = true → head.matches ((printF r).toList ++ sfx) = true)
    (ok : ∀ cur r cur', scan cur = .ok (r, cur') →
      cur.cs = (printF r).toList ++ cur'.cs ∧
        cur'.off = cur.off + (printF r).length ∧ preF r = true ∧
        (printF r).toList ≠ [])
    (cur : Cursor) (h : head.matches cur.cs = false) :
    ∃ e, scan cur = .error e := by
  cases hs : scan cur with
  | error e => exact ⟨e, rfl⟩
  | ok w =>
      have hw := ok cur w.1 w.2 hs
      rw [hw.1] at h
      exact absurd (hok w.1 w.2.cs hw.2.2.1)
        (fun hcon => by rw [hcon] at h; exact Bool.noConfusion h)

/-- `consumes` from the ok-shape (the print's nonemptiness is the
    progress honesty). -/
theorem canonScan_consumes {R : Type} {scan : GParser R} {printF : R → String}
    {preF : R → Bool}
    (ok : ∀ cur r cur', scan cur = .ok (r, cur') →
      cur.cs = (printF r).toList ++ cur'.cs ∧
        cur'.off = cur.off + (printF r).length ∧ preF r = true ∧
        (printF r).toList ≠ [])
    (cur : Cursor) (r : R) (cur' : Cursor) (h : scan cur = .ok (r, cur')) :
    cur'.cs.length < cur.cs.length := by
  rw [(ok cur r cur' h).1, List.length_append]
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ ((ok cur r cur' h).2.2.2)
  have hpos : 0 < (printF r).toList.length := List.length_pos_of_mem hx
  omega

/-! ## the char-literal lexeme (the const-payload single char) -/

/-- The const-value single-char scan: on the char `c` it yields the
    FIXED value `v` (the value-constant discipline — the scanner
    decides the value from the TEXT, so `pre` can discriminate). -/
def constCharScan (c : Char) (v : α) : GParser α := fun cur =>
  match cur.cs with
  | c' :: rest => if c = c' then .ok (v, ⟨cur.off + 1, rest⟩)
                  else .error (ParseError.base cur.off [s!"'{c}'"])
  | [] => .error (ParseError.base cur.off [s!"'{c}'"])

/-- The scan's success shape (the kit's canonical ok-shape: the
    exactness split, the offset, the value-constant gate, and the
    printed char's nonemptiness). -/
theorem constCharScan_ok {c : Char} {v : α} [DecidableEq α] {cur : Cursor} {r : α}
    {cur' : Cursor} (h : constCharScan c v cur = .ok (r, cur')) :
    cur.cs = (String.ofList [c]).toList ++ cur'.cs ∧
      cur'.off = cur.off + (String.ofList [c]).length ∧ (decide (r = v)) = true ∧
      (String.ofList [c]).toList ≠ [] := by
  simp only [constCharScan] at h
  revert h
  cases cur.cs with
  | nil => intro h; simp at h
  | cons c' rest =>
      intro h
      simp only at h
      by_cases hif : c = c'
      · rw [if_pos hif] at h
        obtain ⟨hr, hcc⟩ := Prod.mk.inj (Except.ok.inj h)
        have h1 := Cursor.mk.inj hcc
        refine ⟨?_, ?_, ?_, by simp⟩
        · rw [← hif, h1.2, String.toList_ofList, List.cons_append,
            List.nil_append]
        · rw [← h1.1]; simp
        · rw [← hr]; simp
      · rw [if_neg hif] at h
        simp at h

/-- The head's canonical round trip: the printed char's continuation
    always matches the literal head. -/
private theorem constCharHead_ok (c : Char) (sfx : List Char) :
    (HeadSpec.lit (String.ofList [c])).matches ((String.ofList [c]).toList ++ sfx) = true :=
  List.isPrefixOf_iff_prefix.mpr ⟨sfx, rfl⟩

/-- THE char-literal lexeme: prints the char, scans exactly it
    yielding the fixed value `v`, and its write-side gate is
    value-selective (`pre w ↔ w = v` — the scan never yields anything
    but `v`, so `scan_post` holds). At a unit payload the gate is
    `true` (the separator-atom face). -/ 
def constCharLex (c : Char) [DecidableEq α] (v : α) : Lexeme α where
  scan := constCharScan c v
  print := fun _ => String.ofList [c]
  pre := fun w => decide (w = v)
  head := .lit (String.ofList [c])
  munch := Option.none
  scan_post := fun _ _ _ h => (constCharScan_ok h).2.2.1
  scan_exact := fun _ _ _ h => (constCharScan_ok h).1
  scan_off := fun _ _ _ h => (constCharScan_ok h).2.1
  scan_head := canonScan_head (preF := fun w => decide (w = v))
    (fun _ sfx _ => constCharHead_ok c sfx)
    (fun cur r cur' h => constCharScan_ok h)
  head_fail := canonScan_head_fail (preF := fun w => decide (w = v))
    (fun _ sfx _ => constCharHead_ok c sfx)
    (fun cur r cur' h => constCharScan_ok h)
  print_scan := by
    intro k r sfx hpre _
    have hrv : r = v := of_decide_eq_true hpre
    show constCharScan c v ⟨k, (String.ofList [c]).toList ++ sfx⟩
      = .ok (r, ⟨k + (String.ofList [c]).length, sfx⟩)
    simp only [constCharScan, String.toList_ofList, hrv]
    simp
  consumes := canonScan_consumes (printF := fun _ => String.ofList [c])
    (fun cur r cur' h => constCharScan_ok h)
  head_ne := by
    show (String.ofList [c]).toList.isPrefixOf [] = false
    simp

/-- The gate at the owned value: the scan never yields anything but `v`
    (the simp face `print_scan`'s premise reduces at). -/
@[simp] theorem constCharLex_pre_self (c : Char) (v : α) [DecidableEq α] :
    (constCharLex c v).pre v = true := by
  show decide (v = v) = true
  exact decide_eq_true rfl

/-! ## the ident-atom (the maximal run led by a head class) -/

/-- The ident-atom's write-side gate: the run's round-trip discipline —
    nonempty, all-run-class, and its head passes the head class. -/
def identOk (h p : Char → Bool) (s : String) : Bool :=
  (!s.toList.isEmpty && s.toList.all p) && s.toList.head?.all h

/-- The ident-atom's scan: the maximal `p`-run, guarded to REQUIRE an
    `h`-led input (failing with `fail` otherwise). The chain premise
    (`h c → p c`) keeps every success's run nonempty — the `consumes`
    field's honesty. -/
def identScan (fail : String) (h p : Char → Bool) : GParser String := fun cur =>
  match cur.cs with
  | c :: _ =>
      if h c then
        .ok (String.ofList (cur.cs.takeWhile p),
             ⟨cur.off + (cur.cs.takeWhile p).length, cur.cs.dropWhile p⟩)
      else .error (ParseError.base cur.off [fail])
  | [] => .error (ParseError.base cur.off [fail])

/-- The scan's success shape (the kit's canonical ok-shape): the run
    splits the input exactly, the value passes the gate, and the run's
    spelling is nonempty (the progress honesty). -/
theorem identScan_ok (fail : String) (h p : Char → Bool)
    (hchain : ∀ c, h c = true → p c = true) {cur : Cursor} {s : String} {cur' : Cursor}
    (hres : identScan fail h p cur = .ok (s, cur')) :
    cur.cs = s.toList ++ cur'.cs ∧ cur'.off = cur.off + s.length ∧
      identOk h p s = true ∧ s.toList ≠ [] := by
  simp only [identScan] at hres
  revert hres
  cases cur.cs with
  | nil => intro hres; simp at hres
  | cons c rest =>
      intro hres
      simp only at hres
      have hg : h c = true := by
        cases hb : h c with
        | true => rfl
        | false => rw [hb] at hres; simp at hres
      have hpc : p c = true := hchain c hg
      rw [if_pos hg] at hres
      obtain ⟨hcc1, hcc2⟩ := Prod.mk.inj (Except.ok.inj hres)
      have h1 := Cursor.mk.inj hcc2
      have hds : (c :: rest).takeWhile p = c :: rest.takeWhile p :=
        List.takeWhile_cons_of_pos hpc
      have hs : s.toList = (c :: rest).takeWhile p := by
        rw [← hcc1, String.toList_ofList, hds]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hs, ← h1.2, List.takeWhile_append_dropWhile]
      · rw [← String.length_toList, hs]
        exact h1.1.symm
      · simp only [identOk]
        have hall : (c :: rest.takeWhile p).all p = true := by
          rw [List.all_eq_true]
          intro g hg'
          rcases List.mem_cons.mp hg' with rfl | hg''
          · exact hpc
          · apply mem_takeWhile (c :: rest) g
            rw [List.takeWhile_cons_of_pos hpc]
            exact List.Mem.tail _ hg''
        rw [hs, hds]
        simp [hall, hg]
      · rw [hs, hds]
        simp

/-- The head's canonical round trip: a gate-passing run's continuation
    always matches the head class (the gate's head conjunct, at the
    print ++ suffix shape the kit consumes). -/
private theorem identAtomHead_ok (h p : Char → Bool) : ∀ (r : String) (sfx : List Char),
    identOk h p r = true →
    (HeadSpec.cls h).matches (r.toList ++ sfx) = true := by
  intro r sfx hpre
  show (r.toList ++ sfx).head?.any h = true
  have h5 := Bool.and_eq_true_iff.mp hpre
  have h6 := Bool.and_eq_true_iff.mp h5.1
  cases hsL : r.toList with
  | nil => rw [hsL] at h6; simp at h6
  | cons c0 cs0 =>
      have hh : h c0 = true := by
        have h52 := h5.2
        rw [hsL] at h52
        simpa using h52
      exact hh

/-- THE ident-atom: a maximal `p`-run led by an `h`-char — `head` is
    the `.cls h` (the FIRST-set entry), `munch` the run class `p` (the
    maximal-munch boundary: any char failing `p` breaks the run), and
    `pre` the run's round-trip gate. The chain premise (`h → p`) is
    the constructor's honesty payment: without it an `h`-led input
    with a `p`-failing head char would scan to the EMPTY run (a
    zero-progress success — the `consumes` field's refusal). -/
def identAtom (fail : String) (h p : Char → Bool)
    (hchain : ∀ c, h c = true → p c = true) : Lexeme String where
  scan := identScan fail h p
  print := fun s => s
  pre := identOk h p
  head := .cls h
  munch := Option.some p
  scan_post := fun _ _ _ hres => (identScan_ok fail h p hchain hres).2.2.1
  scan_exact := fun _ _ _ hres => (identScan_ok fail h p hchain hres).1
  scan_off := fun _ _ _ hres => (identScan_ok fail h p hchain hres).2.1
  scan_head := canonScan_head (identAtomHead_ok h p)
    (fun cur s cur' hres => identScan_ok fail h p hchain hres)
  head_fail := by
    intro cur hmatch
    refine ⟨ParseError.base cur.off [fail], ?_⟩
    show identScan fail h p cur = Except.error (ParseError.base cur.off [fail])
    simp only [identScan]
    revert hmatch
    cases cur.cs with
    | nil => intro _; rfl
    | cons c rest =>
        intro hmatch
        have hc : h c = false := by
          have h2 := hmatch
          simp only [HeadSpec.matches, List.head?_cons, Option.any_some] at h2
          exact h2
        show (if h c
            then (Except.ok
              (String.ofList ((c :: rest).takeWhile p),
                (⟨cur.off + ((c :: rest).takeWhile p).length,
                  (c :: rest).dropWhile p⟩ : Cursor)) :
              Except ParseError (String × Cursor))
            else Except.error (ParseError.base cur.off [fail]))
          = Except.error (ParseError.base cur.off [fail])
        simp [hc]
  print_scan := by
    intro k s sfx hpre hmunch
    have hpre' : ((!s.toList.isEmpty && s.toList.all p) && s.toList.head?.all h) = true :=
      hpre
    have h5 := Bool.and_eq_true_iff.mp hpre'
    have h6 := Bool.and_eq_true_iff.mp h5.1
    show identScan fail h p ⟨k, s.toList ++ sfx⟩ = .ok (s, ⟨k + s.length, sfx⟩)
    cases hs : s.toList with
    | nil =>
        have h61 := h6.1
        rw [hs] at h61
        simp at h61
    | cons c rest =>
        have hh : h c = true := by
          have h52 := h5.2
          rw [hs] at h52
          simpa using h52
        have h62 := h6.2
        rw [hs] at h62
        have htw : List.takeWhile p (c :: rest ++ sfx) = c :: rest :=
          takeWhile_append_stop (c :: rest) sfx (List.all_eq_true.mp h62) hmunch
        have hdw : List.dropWhile p (c :: rest ++ sfx) = sfx :=
          dropWhile_append_stop (c :: rest) sfx (List.all_eq_true.mp h62) hmunch
        show (if h c
            then (Except.ok
              (String.ofList (List.takeWhile p (c :: rest ++ sfx)),
                ⟨k + List.length (List.takeWhile p (c :: rest ++ sfx)),
                  List.dropWhile p (c :: rest ++ sfx)⟩) :
              Except ParseError (String × Cursor))
            else Except.error (ParseError.base k [fail]))
          = Except.ok (s, ⟨k + s.length, sfx⟩)
        rw [if_pos hh, htw, hdw, ← hs, String.ofList_toList,
          ← String.length_toList]
  consumes := canonScan_consumes
    (fun cur s cur' hres => identScan_ok fail h p hchain hres)
  head_ne := rfl

/-! ## the nat-atom (the canonical-scanNat discipline) -/

/-- The nat token's `toString` spec (the digit theory is core
    `Nat.ToString`'s). -/
private theorem toString_decDigits (n : Nat) :
    (toString n).toList = Nat.toDigits 10 n := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]

/-- The nat token's law, append form: a nat's decimal spelling scans
    back to the value exactly, leaving any non-digit suffix (the
    munch's boundary). -/
private theorem scanNat_canonical (n : Nat) (sfx : List Char)
    (hm : sfx.head?.all (fun c => !c.isDigit) = true) :
    scanNat ((toString n).toList ++ sfx) = .some (n, sfx) := by
  have hall : ∀ c ∈ Nat.toDigits 10 n, Char.isDigit c = true :=
    fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  have hne : String.ofList (Nat.toDigits 10 n) ≠ "" := by
    intro hcon
    have h2 := congrArg String.toList hcon
    rw [String.toList_ofList] at h2
    exact Nat.toDigits_ne_nil h2
  have hf : (fun (a : Nat) (d : Char) => a * 10 + (d.toNat - '0'.toNat))
      = (fun (a : Nat) (d : Char) => 10 * a + (d.toNat - '0'.toNat)) := by
    funext a d; simp [Nat.mul_comm]
  rw [toString_decDigits, scanNat,
    List.takeWhile_append_of_pos hall, takeWhile_nil_of_head_fail _ hm,
    List.append_nil,
    List.dropWhile_append_of_pos hall, dropWhile_self_of_head_fail _ hm,
    if_neg hne, String.toList_ofList, hf, ← Nat.ofDigitChars_eq_foldl,
    Nat.ofDigitChars_ten_toDigits]

/-- `print_scan`'s boundary twin: the takeWhile over the canonical
    spelling ++ suffix is the spelling. -/
private theorem scanNat_canonical_tw (n : Nat) (sfx : List Char)
    (hm : sfx.head?.all (fun c => !c.isDigit) = true) :
    ((toString n).toList ++ sfx).takeWhile Char.isDigit = (toString n).toList := by
  have hall : ∀ c ∈ Nat.toDigits 10 n, Char.isDigit c = true :=
    fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  rw [toString_decDigits, List.takeWhile_append_of_pos hall,
    takeWhile_nil_of_head_fail _ hm, List.append_nil]

/-- The nat lexeme's scan: `TextKit.scanNat` (one or more digits —
    NONE on zero digits), guarded to the CANONICAL spelling (the
    scanned digit run must be exactly the value's `toString` — a
    leading zero is a refusal; the raw `01` is not the spelling of the
    value it scans to, and `scan_exact` demands the raw). -/
def natScan : GParser Nat := fun cur =>
  match scanNat cur.cs with
  | .none => .error (ParseError.base cur.off ["<nat>"])
  | .some (n, rest) =>
      if (toString n).toList = cur.cs.takeWhile Char.isDigit then
        .ok (n, ⟨cur.off + (toString n).length, rest⟩)
      else .error (ParseError.base cur.off ["<nat>"])

/-- The scan's success shape (the kit's canonical ok-shape). -/
theorem natScan_ok {cur : Cursor} {n : Nat} {cur' : Cursor}
    (h : natScan cur = .ok (n, cur')) :
    cur.cs = (toString n).toList ++ cur'.cs ∧
      cur'.off = cur.off + (toString n).length ∧ (fun _ => true) n = true ∧
      (toString n).toList ≠ [] := by
  simp only [natScan, scanNat] at h
  revert h
  cases hds : (cur.cs.takeWhile Char.isDigit) with
  | nil =>
      intro h
      simp [String.ofList_nil] at h
  | cons d ds =>
      intro h
      have hne : String.ofList (d :: ds) ≠ "" := by
        intro hcon
        have h2 := congrArg String.toList hcon
        rw [String.toList_ofList] at h2
        have h3 : ("" : String).toList = [] := rfl
        rw [h3] at h2
        simp at h2
      rw [if_neg hne] at h
      have h2 : (if (toString (List.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0
              (String.ofList (d :: ds)).toList)).toList = d :: ds
          then Except.ok ((List.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0
              (String.ofList (d :: ds)).toList),
            (⟨cur.off + (toString (List.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0
                (String.ofList (d :: ds)).toList)).length,
              List.dropWhile Char.isDigit cur.cs⟩ : Cursor))
          else Except.error (ParseError.base cur.off ["<nat>"]))
        = Except.ok (n, cur') := h
      by_cases hgd : (toString (List.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0
          (String.ofList (d :: ds)).toList)).toList = d :: ds
      · rw [if_pos hgd] at h2
        obtain ⟨hcc1, hcc2⟩ := Prod.mk.inj (Except.ok.inj h2)
        have h1c := Cursor.mk.inj hcc2
        have h11 := h1c.1
        rw [hcc1] at hgd h11
        refine ⟨?_, h11.symm, rfl, ?_⟩
        · rw [← h1c.2, hgd, ← hds, List.takeWhile_append_dropWhile]
        · rw [hgd]; simp
      · rw [if_neg hgd] at h2; simp at h2

/-- The head's canonical round trip: the decimal spelling is never
    empty and its head char is a digit (the munch's boundary face). -/
private theorem natAtomHead_ok : ∀ (n : Nat) (sfx : List Char),
    (HeadSpec.cls Char.isDigit).matches ((toString n).toList ++ sfx) = true := by
  intro n sfx
  show ((toString n).toList ++ sfx).head?.any Char.isDigit = true
  rw [toString_decDigits]
  cases hn : Nat.toDigits 10 n with
  | nil => exact absurd hn (Nat.toDigits_ne_nil)
  | cons d ds =>
      have hmem : d ∈ Nat.toDigits 10 n := by
        rw [hn]; exact List.Mem.head _
      show Char.isDigit d = true
      exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hmem

/-- THE nat-atom: the canonical-scanNat discipline as a leaf — `print`
    is `toString`, the scan refuses zero digits AND non-canonical
    spellings (a leading zero), `head`/`munch` the digit class (the
    munch's boundary is any non-digit). -/
def natAtom : Lexeme Nat where
  scan := natScan
  print := toString
  pre := fun _ => true
  head := .cls Char.isDigit
  munch := Option.some Char.isDigit
  scan_post := fun _ _ _ _ => rfl
  scan_exact := fun _ _ _ h => (natScan_ok h).1
  scan_off := fun _ _ _ h => (natScan_ok h).2.1
  scan_head := canonScan_head (preF := fun _ => true)
    (fun n sfx _ => natAtomHead_ok n sfx) (fun cur n cur' h => natScan_ok h)
  head_fail := canonScan_head_fail (preF := fun _ => true)
    (fun n sfx _ => natAtomHead_ok n sfx) (fun cur n cur' h => natScan_ok h)
  print_scan := by
    intro k n sfx _ hmunch
    show (match scanNat ((toString n).toList ++ sfx) with
      | .none => (Except.error (ParseError.base k ["<nat>"]) : Except _ (Nat × Cursor))
      | .some (n', rest) =>
          if (toString n').toList = ((toString n).toList ++ sfx).takeWhile Char.isDigit then
            .ok (n', ⟨k + (toString n').length, rest⟩)
          else .error (ParseError.base k ["<nat>"]))
      = .ok (n, ⟨k + (toString n).length, sfx⟩)
    rw [scanNat_canonical n sfx hmunch]
    show (if (toString n).toList = List.takeWhile Char.isDigit ((toString n).toList ++ sfx) then
      (Except.ok (n, ⟨k + (toString n).length, sfx⟩) : Except ParseError (Nat × Cursor))
    else Except.error (ParseError.base k ["<nat>"]))
    = .ok (n, ⟨k + (toString n).length, sfx⟩)
    rw [if_pos (scanNat_canonical_tw n sfx hmunch).symm]
  consumes := canonScan_consumes
    (fun cur n cur' h => natScan_ok h)
  head_ne := rfl

/-! ## the const-string literal (the multi-char keyword face) -/

/-- The multi-char literal's scan: the exact-prefix consumption + the
    loud refusal (the direct `if` form — the proofs stay at the
    `isPrefixOf` level, no expect-unfolding). -/
def constStrScan (s : String) : GParser Unit := fun cur =>
  if (s.toList.isPrefixOf cur.cs) = true then
    .ok ((), ⟨cur.off + s.length, cur.cs.drop s.length⟩)
  else .error (ParseError.base cur.off [s])

/-- The scan's success shape (the kit's canonical ok-shape; the
    literal's nonemptiness is the constructor's `hs` premise). -/
theorem constStrScan_ok (s : String) (hs : s.toList ≠ []) {cur : Cursor} {u : Unit}
    {cur' : Cursor} (h : constStrScan s cur = .ok (u, cur')) :
    cur.cs = s.toList ++ cur'.cs ∧ cur'.off = cur.off + s.length ∧
      (fun _ => true) u = true ∧ s.toList ≠ [] := by
  simp only [constStrScan] at h
  by_cases hsp : (s.toList.isPrefixOf cur.cs) = true
  · rw [if_pos hsp] at h
    obtain ⟨hcc1, hcc2⟩ := Prod.mk.inj (Except.ok.inj h)
    have h1 := Cursor.mk.inj hcc2
    obtain ⟨t, e⟩ := List.isPrefixOf_iff_prefix.mp hsp
    have hdrop : (s.toList ++ t).drop s.length = t := by
      rw [String.length_toList.symm]
      exact List.drop_left
    have ht : t = cur'.cs := by
      rw [← h1.2, ← e, hdrop]
    refine ⟨?_, h1.1.symm, rfl, hs⟩
    rw [← e, ht]
  · rw [if_neg hsp] at h
    simp at h

/-- The head's canonical round trip: the printed literal's continuation
    always matches the literal head. -/
private theorem constStrHead_ok (s : String) (sfx : List Char) :
    (HeadSpec.lit s).matches (s.toList ++ sfx) = true :=
  List.isPrefixOf_iff_prefix.mpr ⟨sfx, rfl⟩

/-- THE const-string literal lexeme (the keyword face; the single-char
    `constCharLex`'s multi-char twin): prints the literal, scans exactly
    it at the unit payload, no munch (a hard delimiter carries no
    maximal-munch boundary — the boundary IS the delimiter's last
    char). Requires a nonempty literal (the `consumes` honesty). -/
def constStrLex (s : String) (hs : s.toList ≠ []) : Lexeme Unit where
  scan := constStrScan s
  print := fun _ => s
  pre := fun _ => true
  head := .lit s
  munch := Option.none
  scan_post := fun _ _ _ _ => rfl
  scan_exact := fun _ _ _ h => (constStrScan_ok s hs h).1
  scan_off := fun _ _ _ h => (constStrScan_ok s hs h).2.1
  scan_head := canonScan_head (preF := fun _ => true)
    (fun _ sfx _ => constStrHead_ok s sfx)
    (fun cur u cur' h => constStrScan_ok s hs h)
  head_fail := canonScan_head_fail (preF := fun _ => true)
    (fun _ sfx _ => constStrHead_ok s sfx)
    (fun cur u cur' h => constStrScan_ok s hs h)
  print_scan := by
    intro k u sfx _ _
    show constStrScan s ⟨k, s.toList ++ sfx⟩ = .ok ((), ⟨k + s.length, sfx⟩)
    simp only [constStrScan]
    rw [if_pos (List.isPrefixOf_iff_prefix.mpr ⟨sfx, rfl⟩),
      String.length_toList.symm, List.drop_left]
  consumes := canonScan_consumes
    (fun cur u cur' h => constStrScan_ok s hs h)
  head_ne := by
    show s.toList.isPrefixOf [] = false
    cases hsl : s.toList with
    | nil => exact absurd hsl hs
    | cons c cs => simp

end TextKit
