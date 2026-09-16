/-
# Substrait.Decode.Types — parseType, the fuel lemmas, and the type inversion ladder

W5.3 phase 1: split of the monolithic Decode.lean along its section
structure (pure code-motion; statements unchanged).
-/
import Substrait.Decode.Basic
import Substrait.Grammar

namespace Substrait.Decode

-- ── types ──────────────────────────────────────────────────────────────────

/-- The nullability-suffix consumer, top-level so equation lemmas exist
    (inversion proofs reduce it via `withNull.eq_1`/`withNull.eq_2`). -/
def withNull (mk : Proto.Nullability → Proto.PType) (rest : List Char) :
    Option (Proto.PType × List Char) :=
  match rest with
  | '?' :: rest' => some (mk .nullable, rest')
  | _ => some (mk .required, rest)

/-- The suffix lemma: no leading `?` → required. -/
theorem withNull_required (mk : Proto.Nullability → Proto.PType) (rest : List Char)
    (h : rest.head? ≠ some '?') :
    withNull mk rest = some (mk .required, rest) := by
  rw [withNull.eq_2]
  intro rest' hr
  subst hr
  exact h rfl

/-- The suffix lemma: leading `?` → nullable. -/
theorem withNull_nullable (mk : Proto.Nullability → Proto.PType) (rest : List Char) :
    withNull mk ('?' :: rest) = some (mk .nullable, rest) := withNull.eq_1 mk rest

/-- **Head lexing**: fold the closed `TCtor` table for the prefix match.
    The match is UNIQUE by `TCtor.prefix_unique`, so the fold order is
    irrelevant — this replaces the ordered 14-branch if-chain. Structural
    `go` (not `findSome?`) for the same whnf reason as `parseScalarType`.
    Fuel-free: lexing never recurses, which is what makes the new
    `parseType_mono` a per-ctor case split with no `by_cases` chains. -/
def lexCtorGo : List Substrait.Grammar.TCtor → List Char → Option Substrait.Grammar.TCtor
  | [], _ => none
  | t :: ts, cs => if startsWith cs t.prefix then some t else lexCtorGo ts cs

def lexCtor (cs : List Char) : Option Substrait.Grammar.TCtor :=
  lexCtorGo Substrait.Grammar.TCtor.all cs

/-- The fold finds the matching row; uniqueness (`prefix_unique`) forces
    the found row to BE `t` whenever `t`'s prefix matches. -/
theorem lexCtorGo_eq_of_startsWith (ts : List Substrait.Grammar.TCtor) (cs : List Char)
    (t : Substrait.Grammar.TCtor) (hmem : t ∈ ts) (hsw : startsWith cs t.prefix = true) :
    lexCtorGo ts cs = some t := by
  induction ts with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [lexCtorGo]
    by_cases hx : startsWith cs x.prefix = true
    · rw [if_pos hx]
      have hxeq : x = t := Substrait.Grammar.TCtor.prefix_unique x t cs
        (List.isPrefixOf_iff_prefix.mp hx) (List.isPrefixOf_iff_prefix.mp hsw)
      rw [hxeq]
    · rw [if_neg hx]
      rcases List.mem_cons.mp hmem with htx | hin
      · subst htx; exact absurd hsw hx
      · exact ih hin

/-- Lexing succeeds on exactly the ctors whose prefix matches. -/
theorem lexCtor_eq_some (t : Substrait.Grammar.TCtor) (cs : List Char)
    (hsw : startsWith cs t.prefix = true) : lexCtor cs = some t :=
  lexCtorGo_eq_of_startsWith _ _ _ (Substrait.Grammar.TCtor.all_complete t) hsw

/-- Self-lexing: a ctor's own text lexes to it. ONE lemma for all 13 ctors —
    the round-trip proofs' per-branch prefix skips collapse into this. -/
theorem lexCtor_self (t : Substrait.Grammar.TCtor) (rest : List Char) :
    lexCtor (t.prefix.toList ++ rest) = some t :=
  lexCtor_eq_some _ _ (startsWith_self _ _)

mutual

/-- `", "`-separated type list (struct fields); structural on `lfuel`. -/
def parseTypeList : Nat → Nat → List Char → Option (List Proto.PType × List Char)
  | 0, _, _ => none
  | lfuel + 1, tfuel, cs =>
    match parseType tfuel cs with
    | none => none
    | some (t, r1) =>
      match expect ", " r1 with
      | some r2 => match parseTypeList lfuel tfuel r2 with
        | some (ts, r3) => some (t :: ts, r3)
        | none => none
      | none => some ([t], r1)

/-- Parse a type: lex the head ctor (`lexCtor`, unique by
    `TCtor.prefix_unique`), then dispatch on the CONSTRUCTOR — no prefix
    if-chain. `fuel` bounds nesting depth (list/map/struct). -/
def parseType : Nat → List Char → Option (Proto.PType × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    match lexCtor cs with
    | none => none
    | some (.scalar c) =>
      withNull (Substrait.Grammar.ScalarCtor.toPType c)
        (cs.drop (Substrait.Grammar.ScalarCtor.prefix c).length)
    | some .decimal =>
      match scanNat (cs.drop 8) with
      | some (p, r1) =>
        match expect "," r1 with
        | some r2 => match scanNat r2 with
          | some (s, r3) => match expect ">" r3 with
            | some r4 => withNull (.decimal p s) r4
            | none => none
          | none => none
        | none => none
      | none => none
    | some .list =>
      match parseType fuel (cs.drop 5) with
      | some (e, r1) => match expect ">" r1 with
        | some r2 => withNull (.list e) r2
        | none => none
      | none => none
    | some .map =>
      match parseType fuel (cs.drop 4) with
      | some (k, r1) => match expect ", " r1 with
        | some r2 => match parseType fuel r2 with
          | some (v, r3) => match expect ">" r3 with
            | some r4 => withNull (.map k v) r4
            | none => none
          | none => none
        | none => none
      | none => none
    | some .struct =>
      -- the emitter prints `struct<>` for the empty field list; parseTypeList
      -- needs ≥1 element, so the empty case is peeled off here
      match expect ">" (cs.drop 7) with
      | some r2 => withNull (.struct []) r2
      | none =>
        match parseTypeList (cs.length + 1) fuel (cs.drop 7) with
        | some (fs, r1) => match expect ">" r1 with
          | some r2 => withNull (.struct fs) r2
          | none => none
        | none => none

end

/-- Type nesting depth — the fuel a parse of `t`'s text needs. The fuel is
    a technicality of the termination proof; every successful parse at fuel
    f also succeeds at any larger fuel (`parseType_mono`). -/
def typeDepth : Proto.PType → Nat
  | .bool _ | .i8 _ | .i16 _ | .i32 _ | .i64 _ | .fp32 _ | .fp64 _
  | .string _ | .binary _ | .decimal _ _ _ | .userDefined _ _ _ => 1
  | .list e _ => typeDepth e + 1
  | .map k v _ => typeDepth k + typeDepth v + 1
  | .struct fs _ => fs.foldl (fun m t => max m (typeDepth t)) 0 + 1

/-- **Fuel monotonicity (+1)**: one more unit of fuel never breaks a
    successful parse. The proof peels the 14-branch if-chain (conditions
    depend on cs only, so both sides agree); the list/map recursive branches
    discharge by the fuel-`f` IH; the struct branch uses the nested
    `hlist_mono` (an lfuel-induction with the fuel-`f` IH available — the
    mutual knot dissolved by nesting, not by a `mutual` block). -/
theorem parseType_mono (fuel : Nat) (cs : List Char) (r : Proto.PType × List Char) :
    parseType fuel cs = some r → parseType (fuel + 1) cs = some r := by
  induction fuel generalizing cs r with
  | zero => simp [parseType]
  | succ f ih =>
    have hlist_mono : ∀ (lf : Nat) (cs' : List Char) (r' : List Proto.PType × List Char),
        parseTypeList lf f cs' = some r' → parseTypeList lf (f + 1) cs' = some r' := by
      intro lf
      induction lf with
      | zero => intro cs' r' h; simp [parseTypeList] at h
      | succ lf ihl =>
        intro cs' r' h
        rw [parseTypeList] at h ⊢
        cases hx : parseType f cs' with
        | none => simp_all
        | some p =>
          have hpt := ih _ _ hx
          cases h2 : expect ", " p.2 with
          | none => simp_all
          | some r2 =>
            cases hy : parseTypeList lf f r2 with
            | none => simp_all
            | some q =>
              have hlist := ihl _ _ hy
              simp_all
    intro h
    unfold parseType at h ⊢
    -- lexing is fuel-free: both sides dispatch on the same ctor. The old
    -- four `by_cases` prefix chains are now ONE case split on the lexed
    -- head — per ctor, only the recursion sites need the IH.
    cases hlex : lexCtor cs with
    | none => simp_all
    | some t =>
      simp only [hlex] at h ⊢
      cases t with
      | scalar c => exact h
      | decimal => exact h
      | list =>
        cases he : parseType f (cs.drop 5) with
        | none => simp_all
        | some x =>
          cases hgt : expect ">" x.2 with
          | none => simp_all
          | some r2 =>
            have hih := ih _ _ he
            simp_all
      | map =>
        cases hk : parseType f (cs.drop 4) with
        | none => simp_all
        | some x =>
          cases hsep : expect ", " x.2 with
          | none => simp_all
          | some r2 =>
            cases hv : parseType f r2 with
            | none => simp_all
            | some y =>
              have ihk := ih _ _ hk
              have ihv := ih _ _ hv
              simp_all
      | struct =>
        cases he0 : expect ">" (cs.drop 7) with
        | some r2 =>
          cases r2 with
          | nil => simp_all
          | cons c cs' => simp_all
        | none =>
          cases hlist : parseTypeList (cs.length + 1) f (cs.drop 7) with
          | none => simp_all
          | some x =>
            cases hgt : expect ">" x.2 with
            | none => simp_all
            | some r2 =>
              have hlm := hlist_mono (cs.length + 1) _ _ hlist
              simp_all

/-- **Fuel monotonicity (k steps)**: any extra fuel preserves a successful
    parse. The form inversion proofs consume. -/
theorem parseType_mono_of_le (f k : Nat) (cs : List Char) (r : Proto.PType × List Char) :
    parseType f cs = some r → parseType (f + k) cs = some r := by
  intro h
  induction k with
  | zero => exact h
  | succ k ihk => rw [Nat.add_succ]; exact parseType_mono _ _ _ ihk

/-- The depth-bounded form: a parse at fuel `typeDepth t` succeeds at any
    larger fuel. -/
theorem parseType_at_depth (t : Proto.PType) (cs : List Char) (r : Proto.PType × List Char)
    (h : parseType (typeDepth t) cs = some r) : ∀ k, parseType (typeDepth t + k) cs = some r :=
  fun _k => parseType_mono_of_le _ _ _ _ h

-- ── types: the inversion theorems ─────────────────────────────────────────

/-- The parseType form: a scalar's text parses at fuel 1. -/
theorem parseType_scalar (c : Substrait.Grammar.ScalarCtor) (rest : List Char)
    (hrest : rest.head? ≠ some '?') :
    parseType 1 ((Substrait.Grammar.ScalarCtor.prefix c).toList ++ rest) =
      some (Substrait.Grammar.ScalarCtor.toPType c .required, rest) := by
  rw [show (Substrait.Grammar.ScalarCtor.prefix c) =
      Substrait.Grammar.TCtor.prefix (.scalar c) from rfl]
  unfold parseType
  rw [lexCtor_self]
  -- the match on `some (.scalar c)` is constructor-headed: reduce it, then
  -- the drop peels the prefix
  show withNull (Substrait.Grammar.ScalarCtor.toPType c)
      (((Substrait.Grammar.TCtor.prefix (.scalar c)).toList ++ rest).drop
        (Substrait.Grammar.ScalarCtor.prefix c).length) =
    some (Substrait.Grammar.ScalarCtor.toPType c .required, rest)
  rw [show (Substrait.Grammar.ScalarCtor.prefix c).length =
      (Substrait.Grammar.TCtor.prefix (.scalar c)).toList.length from rfl,
    List.drop_left]
  exact withNull_required _ rest hrest

/-- The `(p ++ "?")` text as a char list: the prefix, then the `?`. -/
private theorem toList_append_question (p : String) (rest : List Char) :
    (p ++ "?").toList ++ rest = p.toList ++ ('?' :: rest) := by
  rw [String.toList_append, show ("?".toList) = ['?'] from by decide]
  simp [List.append_assoc]

/-- The nullable-suffix form of `parseType_scalar`: `<prefix>?` parses at
    `.nullable`. ONE lemma for all nine scalar ctors — the nine nullable
    round-trip sites collapse onto it. -/
theorem parseType_scalar_nullable (c : Substrait.Grammar.ScalarCtor) (rest : List Char) :
    parseType 1 ((Substrait.Grammar.ScalarCtor.prefix c).toList ++ '?' :: rest) =
      some (Substrait.Grammar.ScalarCtor.toPType c .nullable, rest) := by
  rw [show (Substrait.Grammar.ScalarCtor.prefix c) =
      Substrait.Grammar.TCtor.prefix (.scalar c) from rfl]
  unfold parseType
  rw [lexCtor_self]
  show withNull (Substrait.Grammar.ScalarCtor.toPType c)
      (((Substrait.Grammar.TCtor.prefix (.scalar c)).toList ++ '?' :: rest).drop
        (Substrait.Grammar.ScalarCtor.prefix c).length) =
    some (Substrait.Grammar.ScalarCtor.toPType c .nullable, rest)
  rw [show (Substrait.Grammar.ScalarCtor.prefix c).length =
      (Substrait.Grammar.TCtor.prefix (.scalar c)).toList.length from rfl,
    List.drop_left]
  exact withNull_nullable _ rest



/-- `expect ">"` on a literal `>` head. -/
private theorem expect_gt_cons (rest : List Char) : expect ">" ('>' :: rest) = some rest := by
  unfold expect startsWith
  have hpre : ">".toList.isPrefixOf ('>' :: rest) = true := by rfl
  rw [if_pos hpre]
  rfl

/-- `expect ", "` on a literal `, ` head. -/
private theorem expect_comma_sp (rest : List Char) : expect ", " (',' :: ' ' :: rest) = some rest := by
  unfold expect startsWith
  have hpre : ", ".toList.isPrefixOf (',' :: ' ' :: rest) = true := by rfl
  rw [if_pos hpre]
  rfl

/-- `(p ++ s).toList ++ tail = p.toList ++ (s.toList ++ tail)` — the prefix
    split the if-chain rewrites consume. -/
private theorem toList_head_eq (p s : String) (tail : List Char) :
    (p ++ s).toList ++ tail = p.toList ++ (s.toList ++ tail) := by
  rw [String.toList_append]
  rw [List.append_assoc]

/-- `(a ++ b ++ c).toList` split fully. -/
theorem toList_append3 (a b c : String) :
    (a ++ b ++ c).toList = a.toList ++ b.toList ++ c.toList := by
  rw [String.toList_append, String.toList_append]

-- the `Except`-monad reductions the emitter `do` blocks need (the emitter's
-- hard-error paths never produce a value; these make `simp` see it)

@[simp]
private theorem error_map_reduce {ε α β : Type} (e : ε) (f : α → β) :
    f <$> (Except.error e : Except ε α) = (Except.error e : Except ε β) := by rfl

@[simp]
private theorem ok_map_reduce {ε α β : Type} (a : α) (f : α → β) :
    f <$> (Except.ok a : Except ε α) = (Except.ok (f a) : Except ε β) := by rfl

@[simp]
private theorem error_bind_reduce {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = Except.error e := by rfl

@[simp]
private theorem ok_bind_reduce {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := by rfl

@[simp]
private theorem pure_ok_reduce {ε α : Type} (a : α) :
    (pure a : Except ε α) = Except.ok a := by rfl

@[simp]
private theorem throw_reduce {ε α : Type} (e : ε) :
    (throw e : Except ε α) = Except.error e := by rfl

/-- The scanNat stopping condition: empty, or a first char that isn't a digit. -/
def notDigitHead (rest : List Char) : Prop :=
  rest.head? = none ∨ ∃ c cs0, rest = c :: cs0 ∧ c.isDigit = false

private theorem scanNat_takeWhile_nil (rest : List Char) (hstop : notDigitHead rest) :
    rest.takeWhile Char.isDigit = [] := by
  cases rest with
  | nil => rfl
  | cons c cs0 =>
    rcases hstop with hnone | ⟨c0, cs1, hr, hnd⟩
    · simp at hnone
    · cases hr
      exact List.takeWhile_cons_of_neg (by simp [hnd])

private theorem scanNat_dropWhile_self (rest : List Char) (hstop : notDigitHead rest) :
    rest.dropWhile Char.isDigit = rest := by
  cases rest with
  | nil => rfl
  | cons c cs0 =>
    rcases hstop with hnone | ⟨c0, cs1, hr, hnd⟩
    · simp at hnone
    · cases hr
      exact List.dropWhile_cons_of_neg (by simp [hnd])

/-- `,` vs `",".toList` — the expect's literal head. -/
private theorem comma_prepend (rest : List Char) : ',' :: rest = ",".toList ++ rest := by
  rw [show ",".toList = [','] by decide]
  rfl

/-- `>` vs `">".toList` — the expect's literal head. -/
private theorem gt_prepend (rest : List Char) : '>' :: rest = ">".toList ++ rest := by
  rw [show ">".toList = ['>'] by decide]
  rfl

/-- `(toString n).toList` is never empty. -/
theorem toString_toList_ne_nil (n : Nat) : (toString n).toList ≠ [] := by
  have hdig : (toString n).toList = Nat.toDigits 10 n := by simp
  rw [hdig]
  exact Nat.toDigits_ne_nil

/-- The head char of a Nat's decimal text is a digit. -/
theorem toString_head_isDigit (n : Nat) (c : Char) (cs : List Char)
    (hn : (toString n).toList = c :: cs) : c.isDigit = true := by
  have hm : c ∈ Nat.toDigits 10 n := by
    have hdig : (toString n).toList = Nat.toDigits 10 n := by simp
    rw [← hdig, hn]
    simp
  exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) hm

/-- **The decimal-scan inversion**: a `ToString` number reads back to itself,
    provided the following text stops at a non-digit. -/
theorem scanNat_of_toString (n : Nat) (rest : List Char) (hstop : notDigitHead rest) :
    scanNat ((toString n).toList ++ rest) = some (n, rest) := by
  let f : Nat → Char → Nat := fun a d => a * 10 + (d.toNat - '0'.toNat)
  have hdig : (toString n).toList = Nat.toDigits 10 n := by simp
  rw [hdig]
  have hne : Nat.toDigits 10 n ≠ [] := Nat.toDigits_ne_nil
  cases hd : Nat.toDigits 10 n with
  | nil => exact (hne hd).elim
  | cons c cs =>
    change scanNat (c :: (cs ++ rest)) = some (n, rest)
    have hc : c.isDigit = true := by
      have hmc : c ∈ Nat.toDigits 10 n := by rw [hd]; simp
      exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) hmc
    have hcs : ∀ a ∈ cs, a.isDigit = true := by
      intro a ha
      exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide)
        (by rw [hd]; simp [ha])
    simp [scanNat, scanNat.scanNatGo, Parser.bind_apply, Parser.bind, Parser.takeWhile]
    rw [List.takeWhile_cons_of_pos hc]
    rw [List.takeWhile_append_of_pos hcs]
    rw [scanNat_takeWhile_nil rest hstop]
    rw [List.dropWhile_cons_of_pos hc]
    rw [List.dropWhile_append_of_pos hcs]
    rw [scanNat_dropWhile_self rest hstop]
    have hfold : List.foldl f (c.toNat - '0'.toNat) cs = n := by
      have hf0 : f 0 c = c.toNat - '0'.toNat := by simp [f]
      rw [← hf0]
      rw [← List.foldl_cons]
      rw [← hd]
      simpa [f, Nat.ofDigitChars_eq_foldl, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Nat.ofDigitChars_ten_toDigits : Nat.ofDigitChars 10 (Nat.toDigits 10 n) 0 = n)
    by_cases hz : c :: (cs ++ rest) = []
    · exact False.elim (by simp at hz)
    · simp [hz]
      change List.foldl f (c.toNat - '0'.toNat) cs = n
      exact hfold

-- ── the per-constructor helpers (full type text: base + `?`) ──────────────

/-- **The scalar inversion, ctor-generic**: the emitter's text for a
    scalar type parses back to it. The nine scalar cases are ONE proof via
    the grammar table. The ctor match must come first: `ScalarCtor.toPType`
    is ctor-indexed, so the emitter equation lemmas only reduce at a concrete
    ctor. -/
theorem scalarT (c : Substrait.Grammar.ScalarCtor) (n : Proto.Nullability) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hemit : Emit.Text.typeText (Substrait.Grammar.ScalarCtor.toPType c n) = .ok b) :
    parseType 1 (b.toList ++ rest) = some (Substrait.Grammar.ScalarCtor.toPType c n, rest) := by
  cases n with
  | required =>
      cases c <;> (
        rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
        simp [Emit.Text.nullSuffix, Substrait.Grammar.ScalarCtor.toPType,
          Proto.PType.nullability] at hemit
        rw [show b = Substrait.Grammar.ScalarCtor.prefix _ from hemit.symm]
        exact parseType_scalar _ rest hrest)
  | nullable =>
      -- ctor-generic: the base IS the table's prefix (`typeTextBase_scalar`),
      -- the nullability is `.nullable`, so `b = prefix c ++ "?"`
      have hn : Proto.PType.nullability (Substrait.Grammar.ScalarCtor.toPType c .nullable) =
          .nullable := by
        cases c <;> rfl
      rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase_scalar, hn] at hemit
      have hb : b = Substrait.Grammar.ScalarCtor.prefix c ++ "?" :=
        Except.ok.inj (hemit.symm : Except.ok b =
          Except.ok (Substrait.Grammar.ScalarCtor.prefix c ++ "?"))
      rw [hb, toList_append_question]
      exact parseType_scalar_nullable c rest
  | unspecified =>
      cases c <;> (
        rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
        simp [Emit.Text.nullSuffix, Substrait.Grammar.ScalarCtor.toPType,
          Proto.PType.nullability] at hemit)

/-- The decimal inversion: `decimal<P,S>` scans back (both nullabilities). -/
private theorem decimalT (p s : Nat) (n : Proto.Nullability) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hemit : Emit.Text.typeText (.decimal p s n) = .ok b) :
    parseType (typeDepth (.decimal p s n)) (b.toList ++ rest) = some (.decimal p s n, rest) := by
  simp [typeDepth]
  cases n with
  | required =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    have hb : b = "decimal<" ++ toString p ++ "," ++ toString s ++ ">" := hemit.symm
    rw [hb]
    unfold parseType
    simp
    have hA : notDigitHead (',' :: (Nat.toDigits 10 s ++ '>' :: rest)) := by
      right
      exact ⟨',', Nat.toDigits 10 s ++ '>' :: rest, rfl, by decide⟩
    have hp : scanNat (Nat.toDigits 10 p ++ ',' :: (Nat.toDigits 10 s ++ '>' :: rest)) =
        some (p, ',' :: (Nat.toDigits 10 s ++ '>' :: rest)) := by
      simpa using (scanNat_of_toString p (',' :: (Nat.toDigits 10 s ++ '>' :: rest)) hA)
    rw [hp]
    simp
    rw [comma_prepend (Nat.toDigits 10 s ++ '>' :: rest)]
    rw [expect_self "," (Nat.toDigits 10 s ++ '>' :: rest)]
    simp
    have hB : notDigitHead ('>' :: rest) := by
      right
      exact ⟨'>', rest, rfl, by decide⟩
    have hs : scanNat (Nat.toDigits 10 s ++ '>' :: rest) = some (s, '>' :: rest) := by
      simpa using (scanNat_of_toString s ('>' :: rest) hB)
    rw [hs]
    simp
    rw [gt_prepend rest]
    rw [expect_self ">" rest]
    exact withNull_required (.decimal p s) rest hrest
  | nullable =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    have hb : b = "decimal<" ++ toString p ++ "," ++ toString s ++ ">" ++ "?" := hemit.symm
    rw [hb]
    unfold parseType
    simp
    have hA : notDigitHead (',' :: (Nat.toDigits 10 s ++ '>' :: '?' :: rest)) := by
      right
      exact ⟨',', Nat.toDigits 10 s ++ '>' :: '?' :: rest, rfl, by decide⟩
    have hp : scanNat (Nat.toDigits 10 p ++ ',' :: (Nat.toDigits 10 s ++ '>' :: '?' :: rest)) =
        some (p, ',' :: (Nat.toDigits 10 s ++ '>' :: '?' :: rest)) := by
      simpa using (scanNat_of_toString p (',' :: (Nat.toDigits 10 s ++ '>' :: '?' :: rest)) hA)
    rw [hp]
    simp
    rw [comma_prepend (Nat.toDigits 10 s ++ '>' :: '?' :: rest)]
    rw [expect_self "," (Nat.toDigits 10 s ++ '>' :: '?' :: rest)]
    simp
    have hB : notDigitHead ('>' :: '?' :: rest) := by
      right
      exact ⟨'>', '?' :: rest, rfl, by decide⟩
    have hs : scanNat (Nat.toDigits 10 s ++ '>' :: '?' :: rest) = some (s, '>' :: '?' :: rest) := by
      simpa using (scanNat_of_toString s ('>' :: '?' :: rest) hB)
    rw [hs]
    simp
    rw [gt_prepend ('?' :: rest)]
    rw [expect_self ">" ('?' :: rest)]
    simp
    exact withNull_nullable (.decimal p s) rest
  | unspecified =>
    simp [Emit.Text.typeText, Emit.Text.typeTextBase, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit

/-- The list inversion: `list<T>` scans back. The element hypothesis
    `hie` is the master theorem restricted to `e` (depth-bounded). -/
private theorem listT (e : Proto.PType) (n : Proto.Nullability) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hie : ∀ (b' : String) (rest' : List Char), rest'.head? ≠ some '?' →
      Emit.Text.typeText e = .ok b' → parseType (typeDepth e) (b'.toList ++ rest') = some (e, rest'))
    (hemit : Emit.Text.typeText (.list e n) = .ok b) :
    parseType (typeDepth (.list e n)) (b.toList ++ rest) = some (.list e n, rest) := by
  simp [typeDepth]
  cases n with
  | required =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : Emit.Text.typeText e with
    | error em => simp [he] at hemit
    | ok es =>
      simp [he] at hemit
      have hb : b = "list<" ++ es ++ ">" := hemit.symm
      rw [hb]
      unfold parseType
      -- the lexer folds the closed ctor table; `list<…` self-lexes
      have hcv : (("list<" ++ es ++ ">").toList ++ rest) =
          (Substrait.Grammar.TCtor.prefix .list).toList ++ ((es ++ ">").toList ++ rest) := by
        simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
      rw [hcv, lexCtor_self]
      have hdrop : List.drop 5
          ((Substrait.Grammar.TCtor.prefix .list).toList ++ ((es ++ ">").toList ++ rest)) =
          (es ++ ">").toList ++ rest := by
        simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
      rw [hdrop]
      have hcomb : parseType (typeDepth e) ((es ++ ">").toList ++ rest) =
          some (e, '>' :: rest) := by
        have h0 := hie es ('>' :: rest) (by simp) he
        rw [String.toList_append]
        simp [List.append_assoc]
        exact h0
      rw [hcomb]
      dsimp
      rw [expect_gt_cons rest]
      dsimp
      exact withNull_required (.list e) rest hrest
  | nullable =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : Emit.Text.typeText e with
    | error em => simp [he] at hemit
    | ok es =>
      simp [he] at hemit
      have hb : b = "list<" ++ es ++ ">" ++ "?" := hemit.symm
      rw [hb]
      unfold parseType
      -- the scalar table-fold skips `list<…` (conversion to the literal char
      -- form + the param-prefix complement lemma), then the only preceding
      -- parameterized check (`decimal<`) is skipped by prefix mismatch
      have hcv : (("list<" ++ es ++ ">" ++ "?").toList ++ rest) =
          (Substrait.Grammar.TCtor.prefix .list).toList ++ ((es ++ ">" ++ "?").toList ++ rest) := by
        simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
      rw [hcv, lexCtor_self]
      have hdrop : List.drop 5
          ((Substrait.Grammar.TCtor.prefix .list).toList ++ ((es ++ ">" ++ "?").toList ++ rest)) =
          (es ++ ">" ++ "?").toList ++ rest := by
        simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
      rw [hdrop]
      have hcomb : parseType (typeDepth e) ((es ++ ">" ++ "?").toList ++ rest) =
          some (e, '>' :: '?' :: rest) := by
        have h0 := hie es ('>' :: '?' :: rest) (by simp) he
        rw [String.toList_append, String.toList_append]
        simp [List.append_assoc]
        exact h0
      rw [hcomb]
      dsimp
      rw [expect_gt_cons ('?' :: rest)]
      dsimp
      exact withNull_nullable (.list e) rest
  | unspecified =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    cases he : Emit.Text.typeText e with
    | error em => simp [he] at hemit
    | ok es =>
      simp [he, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit

/-- The map inversion: `map<K, V>` scans back (both nullabilities). -/
private theorem mapT (k v : Proto.PType) (n : Proto.Nullability) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hik : ∀ (b' : String) (rest' : List Char), rest'.head? ≠ some '?' →
      Emit.Text.typeText k = .ok b' → parseType (typeDepth k) (b'.toList ++ rest') = some (k, rest'))
    (hiv : ∀ (b' : String) (rest' : List Char), rest'.head? ≠ some '?' →
      Emit.Text.typeText v = .ok b' → parseType (typeDepth v) (b'.toList ++ rest') = some (v, rest'))
    (hemit : Emit.Text.typeText (.map k v n) = .ok b) :
    parseType (typeDepth (.map k v n)) (b.toList ++ rest) = some (.map k v n, rest) := by
  simp [typeDepth]
  cases n with
  | required =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : Emit.Text.typeText k with
    | error em => simp [he] at hemit
    | ok ks =>
      cases he2 : Emit.Text.typeText v with
      | error em => simp [he, he2] at hemit
      | ok vs =>
        simp [he, he2] at hemit
        have hb : b = "map<" ++ ks ++ ", " ++ vs ++ ">" := hemit.symm
        rw [hb]
        unfold parseType
        have hcv : (("map<" ++ ks ++ ", " ++ vs ++ ">").toList ++ rest) =
            (Substrait.Grammar.TCtor.prefix .map).toList ++ ((ks ++ ", " ++ vs ++ ">").toList ++ rest) := by
          simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
        rw [hcv, lexCtor_self]
        have hdrop : List.drop 4
            ((Substrait.Grammar.TCtor.prefix .map).toList ++ ((ks ++ ", " ++ vs ++ ">").toList ++ rest)) =
            (ks ++ ", " ++ vs ++ ">").toList ++ rest := by
          simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
        rw [hdrop]
        have hkey : parseType (typeDepth k) ((ks ++ ", " ++ vs ++ ">").toList ++ rest) =
            some (k, ',' :: ' ' :: (vs.toList ++ ('>' :: rest))) := by
          have h0 := hik ks (',' :: ' ' :: (vs.toList ++ ('>' :: rest))) (by simp) he
          rw [String.toList_append, String.toList_append, String.toList_append]
          simp [List.append_assoc]
          exact h0
        have hkeyF : parseType (typeDepth k + typeDepth v) ((ks ++ ", " ++ vs ++ ">").toList ++ rest) =
            some (k, ',' :: ' ' :: (vs.toList ++ ('>' :: rest))) := by
          exact parseType_mono_of_le (typeDepth k) (typeDepth v) _ _ hkey
        rw [hkeyF]
        dsimp
        rw [expect_comma_sp (vs.toList ++ '>' :: rest)]
        dsimp
        have hval : parseType (typeDepth v) (vs.toList ++ ('>' :: rest)) =
            some (v, '>' :: rest) := by
          exact hiv vs ('>' :: rest) (by simp) he2
        have hvalF : parseType (typeDepth k + typeDepth v) (vs.toList ++ ('>' :: rest)) =
            some (v, '>' :: rest) := by
          simpa [Nat.add_comm] using (parseType_mono_of_le (typeDepth v) (typeDepth k) _ _ hval)
        rw [hvalF]
        dsimp
        rw [expect_gt_cons rest]
        dsimp
        exact withNull_required (.map k v) rest hrest
  | nullable =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : Emit.Text.typeText k with
    | error em => simp [he] at hemit
    | ok ks =>
      cases he2 : Emit.Text.typeText v with
      | error em => simp [he, he2] at hemit
      | ok vs =>
        simp [he, he2] at hemit
        have hb : b = "map<" ++ ks ++ ", " ++ vs ++ ">" ++ "?" := hemit.symm
        rw [hb]
        unfold parseType
        have hcv : (("map<" ++ ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest) =
            (Substrait.Grammar.TCtor.prefix .map).toList ++ ((ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest) := by
          simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
        rw [hcv, lexCtor_self]
        have hdrop : List.drop 4
            ((Substrait.Grammar.TCtor.prefix .map).toList ++ ((ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest)) =
            (ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest := by
          simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
        rw [hdrop]
        have hkey : parseType (typeDepth k) ((ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest) =
            some (k, ',' :: ' ' :: (vs.toList ++ ('>' :: '?' :: rest))) := by
          have h0 := hik ks (',' :: ' ' :: (vs.toList ++ ('>' :: '?' :: rest))) (by simp) he
          rw [String.toList_append, String.toList_append, String.toList_append]
          simp [List.append_assoc]
          exact h0
        have hkeyF : parseType (typeDepth k + typeDepth v) ((ks ++ ", " ++ vs ++ ">" ++ "?").toList ++ rest) =
            some (k, ',' :: ' ' :: (vs.toList ++ ('>' :: '?' :: rest))) := by
          exact parseType_mono_of_le (typeDepth k) (typeDepth v) _ _ hkey
        rw [hkeyF]
        dsimp
        rw [expect_comma_sp (vs.toList ++ '>' :: '?' :: rest)]
        dsimp
        have hval : parseType (typeDepth v) (vs.toList ++ ('>' :: '?' :: rest)) =
            some (v, '>' :: '?' :: rest) := by
          exact hiv vs ('>' :: '?' :: rest) (by simp) he2
        have hvalF : parseType (typeDepth k + typeDepth v) (vs.toList ++ ('>' :: '?' :: rest)) =
            some (v, '>' :: '?' :: rest) := by
          simpa [Nat.add_comm] using (parseType_mono_of_le (typeDepth v) (typeDepth k) _ _ hval)
        rw [hvalF]
        dsimp
        rw [expect_gt_cons ('?' :: rest)]
        dsimp
        exact withNull_nullable (.map k v) rest
  | unspecified =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    cases he : Emit.Text.typeText k with
    | error em => simp [he] at hemit
    | ok ks =>
      cases he2 : Emit.Text.typeText v with
      | error em => simp [he, he2] at hemit
      | ok vs =>
        simp [he, he2, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit

-- ── the struct-field machinery (parseTypeList inversion) ────────────────

private theorem foldl_max_init_le (l : List Proto.PType) (init : Nat) :
    init ≤ l.foldl (fun m x => max m (typeDepth x)) init := by
  induction l generalizing init with
  | nil => simp
  | cons a rest ih =>
    simp [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left init (typeDepth a))
      (ih (max init (typeDepth a)))

private theorem foldl_max_mono_l (l : List Proto.PType) (i j : Nat) (hij : i ≤ j) :
    l.foldl (fun m x => max m (typeDepth x)) i ≤
      l.foldl (fun m x => max m (typeDepth x)) j := by
  induction l generalizing i j with
  | nil => simpa using hij
  | cons a rest ih =>
    simp [List.foldl_cons]
    exact ih (max i (typeDepth a)) (max j (typeDepth a))
      (Nat.max_le.mpr ⟨Nat.le_trans hij (Nat.le_max_left j (typeDepth a)),
        Nat.le_max_right j (typeDepth a)⟩)

private theorem typeDepth_le_foldl_max {l : List Proto.PType} {t : Proto.PType} (h : t ∈ l) :
    typeDepth t ≤ l.foldl (fun m x => max m (typeDepth x)) 0 := by
  induction l with
  | nil => cases h
  | cons a rest ih =>
    simp [List.foldl_cons]
    by_cases hca : t = a
    · subst t
      exact foldl_max_init_le rest (typeDepth a)
    · exact Nat.le_trans (ih (by simp [hca] at h; exact h))
        (foldl_max_mono_l rest 0 (typeDepth a) (Nat.zero_le _))

theorem mapM_length {α β ε : Type} (l : List α) (f : α → Except ε β) (ts : List β)
    (h : l.mapM f = Except.ok ts) : ts.length = l.length := by
  induction l generalizing ts with
  | nil =>
    have hpm : [].mapM f = Except.ok ([] : List β) := by simp [List.mapM_nil]
    have hts : ts = [] := (Except.ok.inj (h.symm.trans hpm))
    rw [hts]
    simp
  | cons a rest ih =>
    cases hf : f a with
    | error e => simp [hf] at h
    | ok b =>
      cases hr : rest.mapM f with
      | error e => simp [hf, hr] at h
      | ok bs =>
        simp [hf, hr] at h
        have hts : ts = b :: bs := h.symm
        rw [hts]
        simp [ih bs hr]

theorem mapM_cons_ok {α β ε : Type} (a : α) (rest : List α)
    (f : α → Except ε β) (ts : List β)
    (h : (a :: rest).mapM f = Except.ok ts) :
    ∃ tb tsr, f a = Except.ok tb ∧ rest.mapM f = Except.ok tsr ∧ ts = tb :: tsr := by
  cases hf : f a with
  | error e => simp [hf] at h
  | ok tb =>
    cases hr : rest.mapM f with
    | error e => simp [hf, hr] at h
    | ok tsr =>
      simp [hf, hr] at h
      exact ⟨tb, tsr, rfl, rfl, h.symm⟩

private theorem app_ne_prefix (pre tail : String) (hp : pre.toList ≠ []) :
    pre ++ tail ≠ "" := by
  intro hz
  have h' : (pre ++ tail).toList = [] := by simp [hz]
  have htl : pre.toList ++ tail.toList = [] := by simpa [String.toList_append] using h'
  exact hp ((List.append_eq_nil_iff.mp htl).1)

private theorem typeTextBase_nonempty (t : Proto.PType) (b0 : String)
    (h : Emit.Text.typeTextBase t = .ok b0) : b0 ≠ "" := by
  cases t with
  | userDefined a ps n =>
    rw [Emit.Text.typeTextBase.eq_def] at h
    simp at h
  | bool n =>
    simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h
    intro hz
    exact (by decide : "boolean".toList ≠ []) (by simpa [h] using hz)
  | i8 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i16 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i32 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i64 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | fp32 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | fp64 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | string n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | binary n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | decimal p s n =>
    simp [Emit.Text.typeTextBase] at h
    rw [h.symm]
    exact app_ne_prefix "decimal<" (toString p ++ "," ++ toString s ++ ">") (by decide)
  | list e n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : Emit.Text.typeText e with
    | error em => simp [he] at h
    | ok es =>
      simp [he] at h
      rw [h.symm]
      exact app_ne_prefix "list<" (es ++ ">") (by decide)
  | map k v n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : Emit.Text.typeText k with
    | error em => simp [he] at h
    | ok es =>
      cases he2 : Emit.Text.typeText v with
      | error em => simp [he, he2] at h
      | ok es2 =>
        simp [he, he2] at h
        rw [h.symm]
        exact app_ne_prefix "map<" (es ++ ", " ++ es2 ++ ">") (by decide)
  | struct fs n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : fs.mapM Emit.Text.typeText with
    | error em => simp [he] at h
    | ok es =>
      simp [he] at h
      rw [h.symm]
      exact app_ne_prefix "struct<" (Emit.Text.sep ", " es ++ ">") (by decide)

theorem typeText_nonempty (t : Proto.PType) (s : String) (h : Emit.Text.typeText t = .ok s) : s ≠ "" := by
  rw [Emit.Text.typeText.eq_def] at h
  cases hb : Emit.Text.typeTextBase t with
  | error em => simp [hb] at h
  | ok b0 =>
    simp [hb] at h
    cases hn : Emit.Text.nullSuffix (Proto.PType.nullability t) with
    | error em => simp [hn] at h
    | ok ns =>
      simp [hn] at h
      intro hz
      have hne0 : b0 ≠ "" := typeTextBase_nonempty t b0 hb
      exact hne0 (by
        have hbs : b0 ++ ns = "" := h.trans hz
        have h' : (b0 ++ ns).toList = [] := by simp [hbs]
        have htl : b0.toList ++ ns.toList = [] := by simpa [String.toList_append] using h'
        have hpl : b0.toList = [] := (List.append_eq_nil_iff.mp htl).1
        exact String.toList_inj.mp (by simpa using hpl))

private theorem mapM_ok_mem (l : List Proto.PType) (ts : List String)
    (h : l.mapM Emit.Text.typeText = .ok ts) (s : String) (hs : s ∈ ts) : s ≠ "" := by
  induction l generalizing ts with
  | nil =>
    have hts : ts = [] := (Except.ok.inj
      (h.symm.trans (by simp [List.mapM_nil])))
    rw [hts] at hs
    simp at hs
  | cons x rest ih =>
    cases hx : Emit.Text.typeText x with
    | error e => simp [hx] at h
    | ok tx =>
      cases hr : rest.mapM Emit.Text.typeText with
      | error e => simp [hx, hr] at h
      | ok tsr =>
        simp [hx, hr] at h
        -- h : ts = tx :: tsr after the simp; hs : s ∈ ts. Rewrite hs.
        have hts : ts = tx :: tsr := h.symm
        rw [hts] at hs
        rcases List.mem_cons.mp hs with htx | ht
        · exact htx ▸ typeText_nonempty x tx hx
        · exact ih tsr hr ht

theorem sep_cons {l : List String} (d s : String) (hl : l ≠ []) :
    Emit.Text.sep d (s :: l) = s ++ d ++ Emit.Text.sep d l :=
  String.intercalate_cons_of_ne_nil hl

private theorem sep_len_ge (l : List String) (hl : l ≠ [])
    (he : ∀ s ∈ l, s ≠ "") : l.length ≤ (Emit.Text.sep ", " l).toList.length := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons s rest ih =>
    cases rest with
    | nil =>
      have hs' : 1 ≤ s.toList.length := by
        have : 0 < s.toList.length := List.length_pos_iff.mpr (by
          intro hz
          exact he s (by simp) (String.toList_inj.mp hz))
        omega
      simp [Emit.Text.sep]
      exact hs'
    | cons s2 rest2 =>
      have hssep : Emit.Text.sep ", " (s :: s2 :: rest2) =
          s ++ ", " ++ Emit.Text.sep ", " (s2 :: rest2) := by
        simp [Emit.Text.sep]
      have ih' : (s2 :: rest2).length ≤ (Emit.Text.sep ", " (s2 :: rest2)).toList.length :=
        ih (by simp) (by intro x hx; exact he x (by simp [hx]))
      calc
        (s :: s2 :: rest2).length = (s2 :: rest2).length + 1 := by simp
        _ ≤ (Emit.Text.sep ", " (s2 :: rest2)).toList.length + 1 := by
          have h1 : (s2 :: rest2).length ≤ (Emit.Text.sep ", " (s2 :: rest2)).toList.length := ih'
          omega
        _ ≤ s.toList.length + 2 + (Emit.Text.sep ", " (s2 :: rest2)).toList.length := by
          have h1 : 1 ≤ s.toList.length := by
            have : 0 < s.toList.length := List.length_pos_iff.mpr (by
              intro hz
              exact he s (by simp) (String.toList_inj.mp hz))
            omega
          omega
        _ = (Emit.Text.sep ", " (s :: s2 :: rest2)).toList.length := by
          rw [hssep]
          rw [String.toList_append, String.toList_append]
          simp [List.length_append, List.length_cons]
          omega

theorem expect_fail (p : String) (rest : List Char) (hp : p ≠ "")
    (hh : rest.head? ≠ p.toList.head?) : expect p rest = none := by
  unfold expect
  have hs : startsWith rest p = false := by
    unfold startsWith
    cases hp' : p.toList with
    | nil => exact (hp (String.toList_inj.mp hp')).elim
    | cons c cs =>
      cases hr : rest with
      | nil => simp [List.isPrefixOf]
      | cons c0 rest0 =>
        have hh0 : some c0 ≠ some c := by
          intro hc
          exact hh (by simp [hp', hr, hc])
        have hc0 : c0 ≠ c := by
          intro hcc
          exact hh0 (by rw [hcc])
        simp [List.isPrefixOf, hc0.symm]
  simp [hs]

private theorem expect_comma_fail (rest : List Char) (hh : rest.head? ≠ some ',') :
    expect ", " rest = none := by
  have hh' : rest.head? ≠ ", ".toList.head? := by simpa using hh
  exact expect_fail ", " rest (by decide) hh'

/-- The separator text starts with its first element (char-wise). -/
private theorem sep_toList_head (s : String) (l : List String) (hs : s.toList ≠ []) :
    (Emit.Text.sep ", " (s :: l)).toList.head? = s.toList.head? := by
  cases l with
  | nil => simp [Emit.Text.sep]
  | cons x xs =>
    have hsep : Emit.Text.sep ", " (s :: x :: xs) =
        s ++ ", " ++ Emit.Text.sep ", " (x :: xs) := by
      simp [Emit.Text.sep]
    rw [hsep]
    rw [String.toList_append]
    rw [String.toList_append]
    cases hs' : s.toList with
    | nil => exact (hs hs').elim
    | cons c cs => rfl

/-- The head of a nonempty append is the head of the prefix. -/
private theorem head_append_ne (l l' : List Char) (hl : l ≠ []) :
    (l ++ l').head? = l.head? := by
  cases hl' : l with
  | nil => exact (hl hl').elim
  | cons c cs => rfl

/-- The separator text is nonempty and does not start with `>`. -/
private theorem sep_toList_ne_gt (s : String) (l : List String)
    (hs : s.toList ≠ [] ∧ s.toList.head? ≠ some '>') :
    (Emit.Text.sep ", " (s :: l)).toList ≠ [] ∧ (Emit.Text.sep ", " (s :: l)).toList.head? ≠ some '>' := by
  constructor
  · intro hz
    have h0 := sep_toList_head s l hs.1
    cases hmt : s.toList with
    | nil => exact (hs.1 hmt).elim
    | cons c cs =>
      have hh : (Emit.Text.sep ", " (s :: l)).toList.head? = some c :=
        h0.trans (by rw [hmt]; rfl)
      rw [hz] at hh
      simp at hh
  · have h0 := sep_toList_head s l hs.1
    intro hz
    exact hs.2 (h0.symm.trans hz)

private theorem expect_gt_fail_char (c : Char) (rest : List Char) (hc : c ≠ '>') :
    expect ">" (c :: rest) = none := by
  unfold expect
  cases hc0 : c == '>' with
  | true =>
    have hce : c = '>' := beq_iff_eq.mp hc0
    exact (hc hce).elim
  | false =>
    have hpre : startsWith (c :: rest) ">" = false := by
      unfold startsWith
      have hl : (">" : String).toList = ['>'] := by decide
      rw [hl]
      simp [List.isPrefixOf]
      exact fun hz : '>' = c => hc hz.symm
    rw [if_neg (by intro hz; rw [hpre] at hz; simp at hz)]

private theorem expect_gt_fail_head (cs : List Char) (hh : cs ≠ [] ∧ cs.head? ≠ some '>') :
    expect ">" cs = none := by
  cases cs with
  | nil => exact (hh.1 rfl).elim
  | cons c cs0 =>
    have hc : c ≠ '>' := by
      intro hcc
      exact hh.2 (by simp [hcc])
    exact expect_gt_fail_char c cs0 hc

private theorem parseTypeList_invert (l : List Proto.PType) (fuel0 : Nat) (after : List Char)
    (hafter : after.head? ≠ some '?' ∧ after.head? ≠ some ',')
    (hall : ∀ f ∈ l, typeDepth f ≤ fuel0)
    (hfield : ∀ (f : Proto.PType), f ∈ l →
        ∀ (tf : String), Emit.Text.typeText f = .ok tf →
        ∀ (rf : List Char), rf.head? ≠ some '?' →
        parseType (typeDepth f) (tf.toList ++ rf) = some (f, rf)) :
    ∀ (ts : List String), l.mapM Emit.Text.typeText = .ok ts → l ≠ [] →
    ∀ lf, lf ≥ l.length →
    parseTypeList (lf + 1) fuel0 ((Emit.Text.sep ", " ts).toList ++ after) = some (l, after)
  := by
  induction l generalizing fuel0 after with
  | nil => intro ts hmap hne; exact (hne rfl).elim
  | cons f fs' ih =>
    intro ts hmap hne lf hlf
    rcases (mapM_cons_ok f fs' Emit.Text.typeText ts hmap) with ⟨tf, ts'', hf, hr, hts⟩
    subst ts
    cases fs' with
    | nil =>
      have ht0 : ts'' = [] := by
        have hpm : [].mapM Emit.Text.typeText = Except.ok ([] : List String) := by
          simp [List.mapM_nil]
        exact (Except.ok.inj (hr.symm.trans hpm))
      subst ts''
      have hsep1 : Emit.Text.sep ", " [tf] = tf := by simp [Emit.Text.sep]
      rw [hsep1]
      rw [parseTypeList.eq_2]
      have hfld := hfield f (by simp) tf hf after hafter.1
      have hb := hall f (by simp)
      have hm : parseType (fuel0 - typeDepth f + typeDepth f) (tf.toList ++ after) = some (f, after) := by
        have hm0 : parseType (typeDepth f + (fuel0 - typeDepth f)) (tf.toList ++ after) = some (f, after) := by
          exact parseType_mono_of_le (typeDepth f) (fuel0 - typeDepth f) _ _ hfld
        simpa [Nat.add_comm] using hm0
      rw [← Nat.sub_add_cancel hb]
      rw [hm]
      simp
      rw [expect_comma_fail after hafter.2]
    | cons f2 fs2 =>
      rcases (mapM_cons_ok f2 fs2 Emit.Text.typeText ts'' hr) with ⟨tf2, ts2, hf2, hr2, hts2⟩
      subst ts''
      let cont : List Char := ", ".toList ++ (Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after
      have hinput : ((Emit.Text.sep ", " (tf :: tf2 :: ts2)).toList ++ after) = tf.toList ++ cont := by
        have hc := sep_cons (l := (tf2 :: ts2)) ", " tf (by simp)
        have hsept : Emit.Text.sep ", " (tf :: tf2 :: ts2) = tf ++ ", " ++ Emit.Text.sep ", " (tf2 :: ts2) := by
          simp [Emit.Text.sep]
        rw [hsept, toList_append3]
        simp [cont, List.append_assoc]
      rw [hinput]
      rw [parseTypeList.eq_2]
      have hcontQ : cont.head? ≠ some '?' := by
        simp [cont]
      have hfld := hfield f (by simp) tf hf cont hcontQ
      have hb := hall f (by simp)
      have hm : parseType (fuel0 - typeDepth f + typeDepth f) (tf.toList ++ cont) = some (f, cont) := by
        have hm0 : parseType (typeDepth f + (fuel0 - typeDepth f)) (tf.toList ++ cont) = some (f, cont) := by
          exact parseType_mono_of_le (typeDepth f) (fuel0 - typeDepth f) _ _ hfld
        simpa [Nat.add_comm] using hm0
      rw [← Nat.sub_add_cancel hb]
      rw [hm]
      simp
      rw [show expect ", " cont = some ((Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after) by
        have hlist : ", ".toList ++ ((Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after) = cont := by
          simp [cont, List.append_assoc]
        rw [← hlist]
        exact expect_self ", " ((Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after)]
      have hlen' : (f :: f2 :: fs2).length = (f2 :: fs2).length + 1 := by simp
      have hlf1 : 1 ≤ lf := by
        have hlen2 : 2 ≤ (f :: f2 :: fs2).length := by simp
        have : (f :: f2 :: fs2).length ≤ lf := hlf
        omega
      have hfield' : ∀ (x : Proto.PType), x ∈ f2 :: fs2 →
          ∀ (tx : String), Emit.Text.typeText x = .ok tx →
          ∀ (rx : List Char), rx.head? ≠ some '?' →
          parseType (typeDepth x) (tx.toList ++ rx) = some (x, rx) := by
        intro x hx tx htx rx hrx
        exact hfield x (by simp [hx]) tx htx rx hrx
      have hall' : ∀ x ∈ f2 :: fs2, typeDepth x ≤ fuel0 := by
        intro x hx
        exact hall x (by simp [hx])
      have hlf' : lf - 1 ≥ (f2 :: fs2).length := by
        have : (f2 :: fs2).length + 1 ≤ lf := by simpa [hlen'] using hlf
        omega
      have hfuel : fuel0 - typeDepth f + typeDepth f = fuel0 := Nat.sub_add_cancel hb
      rw [hfuel]
      have hrec : parseTypeList lf fuel0 ((Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after) =
          some (f2 :: fs2, after) := by
        simpa [Nat.sub_add_cancel hlf1] using
          (ih fuel0 after hafter hall' hfield' (tf2 :: ts2) hr (by simp) (lf - 1) hlf')
      show (match parseTypeList lf fuel0 ((Emit.Text.sep ", " (tf2 :: ts2)).toList ++ after) with
        | some (ts, r3) => some (f :: ts, r3) | none => none) = some (f :: f2 :: fs2, after)
      rw [hrec]

private theorem cons_head_append (c : Char) (cs tail : List Char) :
    (c :: cs ++ tail).head? = some c := rfl

private theorem prefix_head (pre : String) (c : Char) (pre_rest : List Char) (tail : String)
    (hc : c ≠ '>') (hp : pre.toList = c :: pre_rest) :
    (pre ++ tail).toList ≠ [] ∧ (pre ++ tail).toList.head? ≠ some '>' := by
  rw [String.toList_append, hp]
  constructor
  · simp
  · rw [cons_head_append]
    intro hz
    exact hc (Option.some.inj hz)

private theorem typeText_base_head (t : Proto.PType) (b0 : String)
    (h : Emit.Text.typeTextBase t = .ok b0) : b0.toList ≠ [] ∧ b0.toList.head? ≠ some '>' := by
  cases t with
  | userDefined a ps n =>
    rw [Emit.Text.typeTextBase.eq_def] at h
    simp at h
  | bool n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i8 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i16 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i32 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | i64 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | fp32 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | fp64 n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | string n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | binary n => simp [Emit.Text.typeTextBase, Substrait.Grammar.ScalarCtor.prefix] at h; rw [h.symm]; decide
  | decimal p s n =>
    simp [Emit.Text.typeTextBase] at h
    rw [h.symm]
    exact prefix_head "decimal<" 'd' "ecimal<".toList (toString p ++ "," ++ toString s ++ ">") (by decide)
      (by decide : "decimal<".toList = 'd' :: "ecimal<".toList)
  | list e n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : Emit.Text.typeText e with
    | error em => simp [he] at h
    | ok es =>
      simp [he] at h
      rw [h.symm]
      exact prefix_head "list<" 'l' "ist<".toList (es ++ ">") (by decide)
        (by decide : "list<".toList = 'l' :: "ist<".toList)
  | map k v n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : Emit.Text.typeText k with
    | error em => simp [he] at h
    | ok es =>
      cases he2 : Emit.Text.typeText v with
      | error em => simp [he, he2] at h
      | ok es2 =>
        simp [he, he2] at h
        rw [h.symm]
        exact prefix_head "map<" 'm' "ap<".toList (es ++ ", " ++ es2 ++ ">") (by decide)
          (by decide : "map<".toList = 'm' :: "ap<".toList)
  | struct fs n =>
    simp [Emit.Text.typeTextBase] at h
    cases he : fs.mapM Emit.Text.typeText with
    | error em => simp [he] at h
    | ok es =>
      simp [he] at h
      rw [h.symm]
      exact prefix_head "struct<" 's' "truct<".toList (Emit.Text.sep ", " es ++ ">") (by decide)
        (by decide : "struct<".toList = 's' :: "truct<".toList)

private theorem typeText_head (t : Proto.PType) (s : String) (h : Emit.Text.typeText t = .ok s) :
    s.toList ≠ [] ∧ s.toList.head? ≠ some '>' := by
  rw [Emit.Text.typeText.eq_def] at h
  cases hb : Emit.Text.typeTextBase t with
  | error em => simp [hb] at h
  | ok b0 =>
    simp [hb] at h
    cases hn : Emit.Text.nullSuffix (Proto.PType.nullability t) with
    | error em => simp [hn] at h
    | ok ns =>
      simp [hn] at h
      have hsp : s = b0 ++ ns := h.symm
      rw [hsp]
      rw [String.toList_append]
      have hk := typeText_base_head t b0 hb
      constructor
      · exact fun hz => hk.1 ((List.append_eq_nil_iff.mp hz).1)
      · intro hz
        cases hb' : b0.toList with
        | nil => exact (hk.1 hb').elim
        | cons c cs =>
          have hhh : (b0.toList ++ ns.toList).head? = some c := by
            rw [hb', cons_head_append]
          have hc : some c = some '>' := hhh.symm.trans hz
          have hcd : c = '>' := Option.some.inj hc
          have hb0h : b0.toList.head? = some c := by rw [hb']; rfl
          have hb0gt : b0.toList.head? = some '>' := by rw [hb0h, hcd]
          exact hk.2 hb0gt

/-- The struct inversion: `struct<T,…>` (and the empty `struct<>`) scans back. -/
private theorem structT (fs : List Proto.PType) (n : Proto.Nullability) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hif : ∀ (f : Proto.PType), f ∈ fs → ∀ (b' : String) (rest' : List Char), rest'.head? ≠ some '?' →
      Emit.Text.typeText f = .ok b' → parseType (typeDepth f) (b'.toList ++ rest') = some (f, rest'))
    (hemit : Emit.Text.typeText (.struct fs n) = .ok b) :
    parseType (typeDepth (.struct fs n)) (b.toList ++ rest) = some (.struct fs n, rest) := by
  simp [typeDepth]
  cases n with
  | required =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : fs.mapM Emit.Text.typeText with
    | error em => simp [he] at hemit
    | ok ts =>
      simp [he] at hemit
      have hb : b = "struct<" ++ Emit.Text.sep ", " ts ++ ">" := hemit.symm
      rw [hb]
      unfold parseType
      have hcv : (("struct<" ++ Emit.Text.sep ", " ts ++ ">").toList ++ rest) =
          (Substrait.Grammar.TCtor.prefix .struct).toList ++ ((Emit.Text.sep ", " ts ++ ">").toList ++ rest) := by
        simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
      rw [hcv, lexCtor_self]
      have hdrop : List.drop 7
          ((Substrait.Grammar.TCtor.prefix .struct).toList ++ ((Emit.Text.sep ", " ts ++ ">").toList ++ rest)) =
          (Emit.Text.sep ", " ts ++ ">").toList ++ rest := by
        simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
      rw [hdrop]
      -- the parseTypeList lfuel counts the input length; restore the
      -- string-append form the downstream lemmas are stated against
      rw [show ((Substrait.Grammar.TCtor.prefix .struct).toList ++
              ((Emit.Text.sep ", " ts ++ ">").toList ++ rest)).length =
            (("struct<" ++ Emit.Text.sep ", " ts ++ ">").toList ++ rest).length from by
          simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]]
      cases ts with
      | nil =>
        have hfs : fs = [] := by
          have hl := mapM_length fs Emit.Text.typeText [] he
          cases fs with
          | nil => rfl
          | cons x xs => simp at hl
        subst fs
        simp [Emit.Text.sep]
        rw [gt_prepend rest]
        rw [expect_self ">" rest]
        simp
        exact withNull_required (.struct []) rest hrest
      | cons t ts' =>
        cases fs with
        | nil => simp at he
        | cons f fs0 =>
          rcases (mapM_cons_ok f fs0 Emit.Text.typeText (t :: ts') he) with ⟨tb, tsr, hft, hfr, hts⟩
          have ht : t = tb := (List.cons.inj hts).1
          have htsr : ts' = tsr := (List.cons.inj hts).2
          rw [ht, htsr] at he
          rw [ht, htsr]
          have hth := typeText_head f tb hft
          have hsn := sep_toList_ne_gt tb tsr hth
          have hargne : ((Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest) ≠ [] := by
            intro hz
            -- hz : (sep ++ ">").toList ++ rest = [] → both components are []
            have h2 := (List.append_eq_nil_iff.mp hz).1
            -- h2 : (sep ++ ">").toList = [] → sep's toList = []
            rw [String.toList_append] at h2
            have h3 := (List.append_eq_nil_iff.mp h2).1
            exact hsn.1 h3
          have harghead : ((Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest).head? ≠ some '>' := by
            -- the combined text starts with sep's head (sep is nonempty), which ≠ '>'
            have hne : (Emit.Text.sep ", " (tb :: tsr)).toList ≠ [] := hsn.1
            have hhd : (Emit.Text.sep ", " (tb :: tsr)).toList.head? ≠ some '>' := hsn.2
            have hx : (Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest =
                (Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ rest) := by
              rw [String.toList_append, List.append_assoc]
            rw [hx]
            cases hsep : (Emit.Text.sep ", " (tb :: tsr)).toList with
            | nil => exact absurd hsep hne
            | cons c cs => simp_all
          have htgt : expect ">" ((Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest) = none := by
            exact expect_gt_fail_head ((Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest) ⟨hargne, harghead⟩
          rw [htgt]
          dsimp
          -- parseTypeList inversion: sep text + ">" + rest
          have hinput : ((Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest) =
              (Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ rest) := by
            rw [String.toList_append]
            rw [List.append_assoc]
          rw [hinput]
          have hinpLen : (f :: fs0).length ≤ (( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest).length := by
            have hm : (f :: fs0).length = (tb :: tsr).length := by
              simpa using (mapM_length (f :: fs0) Emit.Text.typeText (tb :: tsr) he).symm
            have hsepl := sep_len_ge (tb :: tsr) (by simp) (fun s hs => mapM_ok_mem (f :: fs0) (tb :: tsr) he s hs)
            calc
              (f :: fs0).length = (tb :: tsr).length := hm
              _ ≤ (Emit.Text.sep ", " (tb :: tsr)).toList.length := hsepl
              _ ≤ (( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest).length := by
                rw [String.toList_append, String.toList_append]
                simp only [List.length_append]
                have hc8 : (("struct<".toList).length) ≥ 7 := by decide
                omega
          have hall : ∀ x ∈ f :: fs0, typeDepth x ≤ (f :: fs0).foldl (fun m x => max m (typeDepth x)) 0 := by
            intro x hx
            exact typeDepth_le_foldl_max hx
          have hafterRest : (">".toList ++ rest).head? ≠ some '?' ∧ (">".toList ++ rest).head? ≠ some ',' := by
            simp
          -- the parser's tfuel for the struct branch is the OUTER fuel =
          -- foldl over (f :: fs0) from 0 = foldl over fs0 from (max 0 (typeDepth f))
          have hfold : (f :: fs0).foldl (fun m x => max m (typeDepth x)) 0 =
              fs0.foldl (fun m x => max m (typeDepth x)) (max 0 (typeDepth f)) := rfl
          have hplt : parseTypeList ((( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest).length + 1)
                (fs0.foldl (fun m x => max m (typeDepth x)) (max 0 (typeDepth f)))
                ((Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ rest)) =
              some (f :: fs0, ">".toList ++ rest) := by
            have h := parseTypeList_invert (f :: fs0)
              ((f :: fs0).foldl (fun m x => max m (typeDepth x)) 0)
              (">".toList ++ rest)
              hafterRest hall
              (fun x hx tx htx rx hrx => hif x hx tx rx hrx htx)
              (tb :: tsr) he (by simp)
              (("struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">").toList ++ rest).length
              hinpLen
            rw [hfold] at h
            exact h
          rw [hplt]
          dsimp
          rw [gt_prepend rest]
          rw [expect_self ">" rest]
          dsimp
          exact withNull_required (.struct (f :: fs0)) rest hrest
  | nullable =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    simp [Emit.Text.nullSuffix, Proto.PType.nullability] at hemit
    cases he : fs.mapM Emit.Text.typeText with
    | error em => simp [he] at hemit
    | ok ts =>
      simp [he] at hemit
      have hb : b = "struct<" ++ Emit.Text.sep ", " ts ++ ">" ++ "?" := hemit.symm
      rw [hb]
      unfold parseType
      have hcv : (("struct<" ++ Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest) =
          (Substrait.Grammar.TCtor.prefix .struct).toList ++ ((Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest) := by
        simp [String.toList_append, List.append_assoc, Substrait.Grammar.TCtor.prefix]
      rw [hcv, lexCtor_self]
      have hdrop : List.drop 7
          ((Substrait.Grammar.TCtor.prefix .struct).toList ++ ((Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest)) =
          (Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest := by
        simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]
      rw [hdrop]
      rw [show ((Substrait.Grammar.TCtor.prefix .struct).toList ++
              ((Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest)).length =
            (("struct<" ++ Emit.Text.sep ", " ts ++ ">" ++ "?").toList ++ rest).length from by
          simp [Substrait.Grammar.TCtor.prefix, String.toList_append, List.append_assoc]]
      cases ts with
      | nil =>
        have hfs : fs = [] := by
          have hl := mapM_length fs Emit.Text.typeText [] he
          cases fs with
          | nil => rfl
          | cons x xs => simp at hl
        subst fs
        simp [Emit.Text.sep]
        rw [gt_prepend ('?' :: rest)]
        rw [expect_self ">" ('?' :: rest)]
        simp
        exact withNull_nullable (.struct []) rest
      | cons t ts' =>
        cases fs with
        | nil => simp at he
        | cons f fs0 =>
          rcases (mapM_cons_ok f fs0 Emit.Text.typeText (t :: ts') he) with ⟨tb, tsr, hft, hfr, hts⟩
          have ht : t = tb := (List.cons.inj hts).1
          have htsr : ts' = tsr := (List.cons.inj hts).2
          rw [ht, htsr] at he
          rw [ht, htsr]
          have hth := typeText_head f tb hft
          have hsn := sep_toList_ne_gt tb tsr hth
          have hargne : ((Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest) ≠ [] := by
            intro hz
            have h2 := (List.append_eq_nil_iff.mp hz).1
            rw [String.toList_append] at h2
            have h3 := (List.append_eq_nil_iff.mp h2).1
            rw [String.toList_append] at h3
            have h4 := (List.append_eq_nil_iff.mp h3).1
            exact hsn.1 h4
          have harghead : ((Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).head? ≠ some '>' := by
            have hne : (Emit.Text.sep ", " (tb :: tsr)).toList ≠ [] := hsn.1
            have hhd : (Emit.Text.sep ", " (tb :: tsr)).toList.head? ≠ some '>' := hsn.2
            have hx : (Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest =
                (Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ "?".toList ++ rest) := by
              rw [String.toList_append, String.toList_append]
              simp [List.append_assoc]
            rw [hx]
            cases hsep : (Emit.Text.sep ", " (tb :: tsr)).toList with
            | nil => exact absurd hsep hne
            | cons c cs => simp_all
          have htgt : expect ">" ((Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest) = none := by
            exact expect_gt_fail_head ((Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest) ⟨hargne, harghead⟩
          rw [htgt]
          dsimp
          have hinput : ((Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest) =
              (Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ "?".toList ++ rest) := by
            rw [String.toList_append, String.toList_append]
            simp [List.append_assoc]
          rw [hinput]
          have hinpLen : (f :: fs0).length ≤ (( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).length := by
            have hm : (f :: fs0).length = (tb :: tsr).length := by
              simpa using (mapM_length (f :: fs0) Emit.Text.typeText (tb :: tsr) he).symm
            have hsepl := sep_len_ge (tb :: tsr) (by simp) (fun s hs => mapM_ok_mem (f :: fs0) (tb :: tsr) he s hs)
            calc
              (f :: fs0).length = (tb :: tsr).length := hm
              _ ≤ (Emit.Text.sep ", " (tb :: tsr)).toList.length := hsepl
              _ ≤ (( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).length := by
                have h1 : (("struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).length =
                    "struct<".toList.length + (Emit.Text.sep ", " (tb :: tsr)).toList.length +
                    ">".toList.length + "?".toList.length + rest.length := by
                  rw [String.toList_append, String.toList_append, String.toList_append]
                  simp [List.length_append]
                  omega
                have hc8 : "struct<".toList.length ≥ 7 := by decide
                omega
          have hall : ∀ x ∈ f :: fs0, typeDepth x ≤ (f :: fs0).foldl (fun m x => max m (typeDepth x)) 0 := by
            intro x hx
            exact typeDepth_le_foldl_max hx
          have hafterRest : (">".toList ++ "?".toList ++ rest).head? ≠ some '?' ∧
              (">".toList ++ "?".toList ++ rest).head? ≠ some ',' := by
            simp
          have hfold : (f :: fs0).foldl (fun m x => max m (typeDepth x)) 0 =
              fs0.foldl (fun m x => max m (typeDepth x)) (max 0 (typeDepth f)) := rfl
          have hplt : parseTypeList ((( "struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).length + 1)
                (fs0.foldl (fun m x => max m (typeDepth x)) (max 0 (typeDepth f)))
                ((Emit.Text.sep ", " (tb :: tsr)).toList ++ (">".toList ++ "?".toList ++ rest)) =
              some (f :: fs0, ">".toList ++ "?".toList ++ rest) := by
            have h := parseTypeList_invert (f :: fs0)
              ((f :: fs0).foldl (fun m x => max m (typeDepth x)) 0)
              (">".toList ++ "?".toList ++ rest)
              hafterRest hall
              (fun x hx tx htx rx hrx => hif x hx tx rx hrx htx)
              (tb :: tsr) he (by simp)
              (("struct<" ++ Emit.Text.sep ", " (tb :: tsr) ++ ">" ++ "?").toList ++ rest).length
              hinpLen
            rw [hfold] at h
            exact h
          rw [hplt]
          dsimp
          rw [gt_prepend ('?' :: rest)]
          rw [expect_self ">" ('?' :: rest)]
          exact withNull_nullable (.struct (f :: fs0)) rest
  | unspecified =>
    rw [Emit.Text.typeText.eq_def, Emit.Text.typeTextBase.eq_def] at hemit
    cases he : fs.mapM Emit.Text.typeText with
    | error em => simp [he] at hemit
    | ok ts =>
      simp [he, Emit.Text.nullSuffix, Proto.PType.nullability] at hemit

/-- The mutual `Proto.PType` recursor driven on a `PType → Prop` motive:
    the `PParam` minors are trivial (`True`), the `List PType` minor is the
    membership induction.  The shared skeleton of `parseType_typeText` and
    `typeDepth_le_len` (`induction` refuses `Proto.PType` — it lives in a
    mutual block with `PParam` — so the recursor is driven directly). -/
theorem ptypeRec (motive : Proto.PType → Prop)
    (hbool : ∀ n, motive (.bool n)) (hi8 : ∀ n, motive (.i8 n))
    (hi16 : ∀ n, motive (.i16 n)) (hi32 : ∀ n, motive (.i32 n))
    (hi64 : ∀ n, motive (.i64 n)) (hfp32 : ∀ n, motive (.fp32 n))
    (hfp64 : ∀ n, motive (.fp64 n)) (hstring : ∀ n, motive (.string n))
    (hbinary : ∀ n, motive (.binary n))
    (hdecimal : ∀ p s n, motive (.decimal p s n))
    (hlist : ∀ e n, motive e → motive (.list e n))
    (hmap : ∀ k v n, motive k → motive v → motive (.map k v n))
    (hstruct : ∀ fs n, (∀ f, f ∈ fs → motive f) → motive (.struct fs n))
    (huser : ∀ a ps n, True → motive (.userDefined a ps n))
    (t : Proto.PType) : motive t := by
  have hnil : ∀ f, f ∈ ([] : List Proto.PType) → motive f := by
    intro f hf
    simp at hf
  have hcons : ∀ (hd : Proto.PType) (tl : List Proto.PType),
      motive hd → (∀ f, f ∈ tl → motive f) → ∀ f, f ∈ hd :: tl → motive f := by
    intro hd tl ihd iht f hf
    rw [List.mem_cons] at hf
    rcases hf with hfe | hft
    · subst hfe; exact ihd
    · exact iht f hft
  refine @Proto.PType.rec motive (fun _ => True)
    (fun (l : List Proto.PType) => ∀ f, f ∈ l → motive f) (fun _ => True)
    hbool hi8 hi16 hi32 hi64 hfp32 hfp64 hstring hbinary hdecimal
    hlist hmap hstruct huser
    (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial)
    hnil hcons trivial (fun _ _ _ _ => trivial) t

/-- ***Master type-inversion theorem***: `parseType` at fuel `typeDepth t`
    inverts `Emit.Text.typeText` on the whole emit-able fragment (all
    constructors except `userDefined`, which the emitter hard-errors on and
    the `hemit` hypothesis rules out).  The induction is a thin unwrapping:
    every per-constructor helper (`boolT`…`binaryT`, `decimalT`, `listT`,
    `mapT`, `structT`) is stated *exactly* at this theorem's shape, so each
    recursive case preinstantiates the induction hypothesis on its subterms.
    The nullable suffix is inside the helpers (withNull_required /
    withNull_nullable), so no case re-derives the `?` scan.
    `Proto.PType` lives in a mutual block with `PParam`, so the `induction`
    tactic refuses it; the mutual recursor is driven directly, with the
    `PParam` motives `True` (the emitter hard-errors before `PParam` values
    can matter here) and the `List PType` motive the struct membership
    induction. -/
theorem parseType_typeText (t : Proto.PType) (b : String) (rest : List Char)
    (hrest : rest.head? ≠ some '?')
    (hemit : Emit.Text.typeText t = .ok b) :
    parseType (typeDepth t) (b.toList ++ rest) = some (t, rest) := by
  let motive : Proto.PType → Prop :=
    fun t => ∀ (b : String) (rest : List Char), rest.head? ≠ some '?' →
      Emit.Text.typeText t = .ok b → parseType (typeDepth t) (b.toList ++ rest) = some (t, rest)
  have hscalar : ∀ (c : Substrait.Grammar.ScalarCtor) n,
      motive (Substrait.Grammar.ScalarCtor.toPType c n) := by
    intro c n b rest hrest hemit
    rw [show typeDepth (Substrait.Grammar.ScalarCtor.toPType c n) = 1 from by
      cases c <;> simp [typeDepth, Substrait.Grammar.ScalarCtor.toPType]]
    exact scalarT c n rest hrest hemit
  have hbool   : ∀ n, motive (.bool n)   := hscalar .bool
  have hi8     : ∀ n, motive (.i8 n)     := hscalar .i8
  have hi16    : ∀ n, motive (.i16 n)    := hscalar .i16
  have hi32    : ∀ n, motive (.i32 n)    := hscalar .i32
  have hi64    : ∀ n, motive (.i64 n)    := hscalar .i64
  have hfp32   : ∀ n, motive (.fp32 n)   := hscalar .fp32
  have hfp64   : ∀ n, motive (.fp64 n)   := hscalar .fp64
  have hstring : ∀ n, motive (.string n) := hscalar .string
  have hbinary : ∀ n, motive (.binary n) := hscalar .binary
  have hdecimal : ∀ p s n, motive (.decimal p s n) :=
    fun p s n b rest hrest hemit => decimalT p s n rest hrest hemit
  have hlist : ∀ e n, motive e → motive (.list e n) := by
    intro e n ih b rest hrest hemit
    exact listT e n rest hrest (fun b' rest' hr' he' => ih b' rest' hr' he') hemit
  have hmap : ∀ k v n, motive k → motive v → motive (.map k v n) := by
    intro k v n ihk ihv b rest hrest hemit
    exact mapT k v n rest hrest
      (fun b' rest' hr' he' => ihk b' rest' hr' he')
      (fun b' rest' hr' he' => ihv b' rest' hr' he') hemit
  have hstruct : ∀ fs n, (∀ f, f ∈ fs → motive f) → motive (.struct fs n) := by
    intro fs n ih b rest hrest hemit
    exact structT fs n rest hrest
      (fun f hf b' rest' hr' he' => ih f hf b' rest' hr' he') hemit
  have huser : ∀ a ps n, True → motive (.userDefined a ps n) := by
    intro a ps n _ b rest hrest hemit
    simp [Emit.Text.typeText, Emit.Text.typeTextBase] at hemit
  exact ptypeRec motive hbool hi8 hi16 hi32 hi64 hfp32 hfp64 hstring hbinary
    hdecimal hlist hmap hstruct huser t b rest hrest hemit

/-- The nullability marker. Delegates to `Proto.PType.nullability` (one
    accessor, not two — the parallel fold was dead duplication). -/
abbrev nullabilityOf (t : Proto.PType) : Proto.Nullability := t.nullability


end Substrait.Decode
