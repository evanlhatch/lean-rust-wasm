/-
# Vortex.Compute — COMPUTE-ON-COMPRESSED (evaluation OVER the encoded form)

Owner: the Vortex agent (the mandate tree, `vortex/`).
Driving decisions: notes/design-vortex-encodings.md (the encodings are
physical layouts FOR a logical dtype — compute rides the LAYOUT, never
a materialized decode) + notes/v3/02-data-plane.md (the relational
center: selection restricts — the predicate op's semantics) + 15-patterns
#2/#18 (the law shapes: per (encoding, op) the retention discipline —
`evalEncoded op enc ≡ decode enc |> eval op`) + #5 (the mandatory
negative controls: the off-fragment refusal + the corrupted-carrier
refusal, both pinned).

## THE POINT

Vortex's whole reason: evaluation OVER ENCODED ARRAYS without decoding.
Per encoding, the operations that work DIRECTLY on the encoded form,
each with its law against the decode baseline:

- `identity` (`.rawVals`) — the values as-is: the predicate filters
  pointwise (nothing compressed — the tie row of the matrix).
- `constant` (`.constData`) — ANY op is the op on the SINGLE value:
  one probe + a replicate (the landslide case). The probe account is 1
  regardless of the row count — the win the teeth pin.
- `dict` (`.dictData`) — the classic dict trick: the predicate
  evaluates on the VALUES table ONCE (`mapCount` over `vals`), then the
  codes' selection vector re-indexes it. Probes = distinct values,
  independent of the row count. A corrupted carrier (a code out of the
  values table's range) REFUSES — never a fabricated row.
- `foR` (`.forData`) — the pushdown: the predicate on the value
  `base + off` projects onto the OFFSET domain through `shiftFoR` —
  equality evaluates pointwise (`off == t - base`), the thresholds are
  exact under the shift (`off < t - base`), and the fragment is CLOSED
  under complement (`notP` maps through). THE NAMED FRAGMENT: boolean
  combinations of equality and thresholds. An OPAQUE predicate
  (`.raw f`) REFUSES: it has no projection onto the narrow offset
  domain without widening — `f (base + off)` is decode in disguise.
- `bitPacked` (`.bitPackData`) — the fused peel: the selection walks
  the w-bit stream (`s % 2^w` per peel), never materializing the
  decoded list — selection without the full decode.

THE NAMED GAPS (each lands with its first consumer — the leftover
rule): `sequence`'s closed-form pushdown (a threshold on the row
INDEX's interval — no carrier yet), `sparse`'s dict-trick nesting
(p on the default once + the patches pointwise — no carrier yet).
`carrierOf?` refuses both specs loudly; the tests pin the refusals.

## The probe account (the fusion teeth's instrument)

`mapCount` is the ONE instrument: a mapped list + the count of `f`
applications. The decoded baseline's account is `mapCount` over the
DECODED column (`decodeProbes`); the encoded paths' accounts are their
syntactic p-application counts (`encodedProbes` — `evalDict` probes
through `mapCount` on `vals`; `evalConst` probes once by match; the
pointwise paths probe once per element by `filter`'s own face). The
teeth: three pointwise TIES (the honest rows) + two WINS (dict and
constant — the account is independent of the row count). Same
instrument both sides — apples to apples.

The five questions (notes/v3/01-core.md): root = the encoding
vocabulary's compute face (no new universe — the carriers are the
retention exemplars' own data types); carrier grade = `Encoded` (the
semantic encoded carrier, sum over the landed rows); spine reading =
none — the op layer UNDER the plan (Emit emits layouts, Compute
evaluates over them); ladder rung = the per-(encoding, op) laws are
small structural inductions citing the codecs' lemmas, never re-proofs;
gate row = VortexTests' compute suite (agreement sweeps + the
refusals + the account teeth) + the axiom report.

Core-only (imports Vortex.Codecs — the cone rule).
-/

import Vortex.Codecs

namespace Vortex

/-! ## The predicate fragment (the op side of the matrix) -/

/-- The row predicate as DATA — the named fragment: boolean
    combinations of equality and thresholds (closed under complement).
    `.raw` is the off-fragment escape hatch: an opaque computable
    predicate, admissible ONLY on the pointwise rows (identity,
    constant, dict — the value-domain carriers), refused by the foR
    pushdown (no projection onto the offset domain without widening). -/
inductive VPred where
  /-- The row equals `t`. -/
  | eqVal (t : Nat)
  /-- The row is below `t` (a threshold). -/
  | ltVal (t : Nat)
  /-- The row is above `t` (a threshold). -/
  | gtVal (t : Nat)
  /-- The complement (in-fragment: `¬<` and `¬>` are thresholds,
      `¬¬` cancels; `¬=` stays pointwise). -/
  | notP (p : VPred)
  /-- An OPAQUE predicate — off the named fragment (the refusal face). -/
  | raw (f : Nat → Bool)

/-- The fragment's semantics: one application per probe. -/
def VPred.holds : VPred → Nat → Bool
  | .eqVal t, x => decide (x = t)
  | .ltVal t, x => decide (x < t)
  | .gtVal t, x => decide (x > t)
  | .notP p, x => !p.holds x
  | .raw f, x => f x

/-- The fragment's membership: raw is the off-fragment row. -/
def VPred.inFragment : VPred → Bool
  | .raw _ => false
  | .notP p => p.inFragment
  | _ => true

/-! ## The foR shift (the pushdown's content) -/

/-- The predicate's projection onto the OFFSET domain: `p (base + off)`
    as a predicate ON the offsets — in the SAME named vocabulary (the
    narrow-domain face). Equality shifts pointwise; the thresholds
    shift exactly; `notP` maps through; `.raw` has NO projection (the
    fragment's boundary — `none`). The degenerate bounds: below the
    base, `eq`/`lt` become the always-false `.ltVal 0`, `gt` the
    always-true `.notP .ltVal 0`. -/
def shiftFoR : VPred → Nat → Option VPred
  | .eqVal t, base => some (if t < base then .ltVal 0 else .eqVal (t - base))
  | .ltVal t, base => some (if t ≤ base then .ltVal 0 else .ltVal (t - base))
  | .gtVal t, base => some (if t < base then .notP (.ltVal 0) else .gtVal (t - base))
  | .notP p, base => (shiftFoR p base).map .notP
  | .raw _, _ => none

/-- THE SHIFT LAW: the projected predicate decides `p` on the decoded
    value WITHOUT decoding — `q off = p (base + off)`, pointwise. -/
theorem shiftFoR_holds : ∀ (p : VPred) (base x : Nat) (q : VPred),
    shiftFoR p base = some q → q.holds x = p.holds (base + x) := by
  intro p
  induction p with
  | eqVal t =>
      intro base x q hq
      simp only [shiftFoR] at hq
      by_cases hb : t < base
      · rw [if_pos hb] at hq; cases hq
        simp only [VPred.holds, decide_eq_decide]
        omega
      · rw [if_neg hb] at hq; cases hq
        simp only [VPred.holds, decide_eq_decide]
        omega
  | ltVal t =>
      intro base x q hq
      simp only [shiftFoR] at hq
      by_cases hb : t ≤ base
      · rw [if_pos hb] at hq; cases hq
        simp only [VPred.holds, decide_eq_decide]
        omega
      · rw [if_neg hb] at hq; cases hq
        simp only [VPred.holds, decide_eq_decide]
        omega
  | gtVal t =>
      intro base x q hq
      simp only [shiftFoR] at hq
      by_cases hb : t < base
      · rw [if_pos hb] at hq; cases hq
        -- q = .notP (.ltVal 0): both sides are TRUE (below the base,
        -- every value clears the bound)
        have hv1 : (VPred.notP (VPred.ltVal 0)).holds x = true := by
          simp only [VPred.holds]; simp
        have hv2 : (VPred.gtVal t).holds (base + x) = true := by
          simp only [VPred.holds]; exact decide_eq_true (by omega)
        rw [hv1, hv2]
      · rw [if_neg hb] at hq; cases hq
        simp only [VPred.holds, decide_eq_decide]
        omega
  | notP p ih =>
      intro base x q hq
      simp only [shiftFoR] at hq
      cases h0 : shiftFoR p base with
      | none => rw [h0] at hq; simp at hq
      | some q' =>
          rw [h0] at hq
          simp only [Option.map_some] at hq
          cases hq
          simp only [VPred.holds]
          exact congrArg not (ih base x q' h0)
  | raw f =>
      intro base x q hq
      simp only [shiftFoR] at hq
      simp at hq

/-- The fragment's shift totality: every in-fragment predicate projects
    (the raw row is the only refusal — the boundary's content). -/
theorem inFragment_shift (p : VPred) (base : Nat) (h : p.inFragment = true) :
    (shiftFoR p base).isSome = true := by
  induction p with
  | raw f => simp [VPred.inFragment] at h
  | eqVal t => simp [shiftFoR]
  | ltVal t => simp [shiftFoR]
  | gtVal t => simp [shiftFoR]
  | notP q ih =>
      simp only [shiftFoR, Option.isSome_map]
      exact ih (by simpa [VPred.inFragment] using h)

/-! ## The probe account (the ONE instrument) -/

/-- The instrument: the mapped list + the count of `f` applications.
    Both faces are the account — a value face for the agreement, a
    count face for the fusion teeth. -/
def mapCount (f : Nat → Bool) : List Nat → List Bool × Nat
  | [] => ([], 0)
  | x :: xs => (f x :: (mapCount f xs).1, (mapCount f xs).2 + 1)

/-- The instrument's law: both faces are the plain map/length. -/
theorem mapCount_ok (f : Nat → Bool) (xs : List Nat) :
    (mapCount f xs).1 = xs.map f ∧ (mapCount f xs).2 = xs.length := by
  induction xs with
  | nil => simp [mapCount]
  | cons u us ih => simp [mapCount, ih]

/-! ## The generic list index (the carriers' lookup face) -/

/-- The index lookup: `none` past the end (the refusal face). -/
def atIdx? : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => atIdx? xs i

theorem atIdx?_map (f : α → β) :
    ∀ (xs : List α) (i : Nat), atIdx? (xs.map f) i = (atIdx? xs i).map f := by
  intro xs
  induction xs with
  | nil => intro i; cases i <;> rfl
  | cons u us ih =>
      intro i
      cases i with
      | zero => rfl
      | succ i' => simp [atIdx?, ih i']

theorem atIdx?_exists_of_lt :
    ∀ (xs : List α) (i : Nat), i < xs.length → ∃ v, atIdx? xs i = some v := by
  intro xs
  induction xs with
  | nil => intro i h; exact absurd h (by simp)
  | cons u us ih =>
      intro i h
      cases i with
      | zero => exact ⟨u, rfl⟩
      | succ i' => exact ih i' (by simp at h; omega)

theorem atIdx?_ge_none :
    ∀ (xs : List α) (i : Nat), xs.length ≤ i → atIdx? xs i = none := by
  intro xs
  induction xs with
  | nil => intro i _; rfl
  | cons u us ih =>
      intro i h
      cases i with
      | zero => exact absurd h (by simp)
      | succ i' => simp [atIdx?, ih i' (by simp at h; omega)]

/-- `atIdx?` is `valueAt?`'s argument-order twin (the Codecs lookup). -/
theorem atIdx?_valueAt? : ∀ (xs : List Nat) (i : Nat), atIdx? xs i = valueAt? i xs := by
  intro xs
  induction xs with
  | nil => intro i; cases i <;> rfl
  | cons u us ih =>
      intro i
      cases i with
      | zero => rfl
      | succ i' => simp [atIdx?, valueAt?, ih i']

/-! ## The per-encoding direct evaluators (the matrix's rows) -/

/-- The filter's shift through `+base`: select on the OFFSET domain,
    then project — the same rows as filtering the decoded values.
    The foR law's engine. -/
theorem filter_shift_map (p q : VPred) (base : Nat)
    (h : ∀ x, q.holds x = p.holds (base + x)) (xs : List Nat) :
    (xs.filter q.holds).map (fun o => o + base)
      = (xs.map (fun o => o + base)).filter p.holds := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
      simp only [List.filter_cons, List.map_cons]
      rw [h u, Nat.add_comm base u]
      cases hp : p.holds (u + base) <;> simp [ih]

/-- THE CONSTANT ROW: one probe on the shared value, the result is the
    replicate or the empty list — the landslide case (the op NEVER
    walks the rows; the account is 1 regardless of `count`). -/
def evalConst (p : VPred) (c : ConstantData Nat) : List Nat × Nat :=
  match c.value with
  | some v => if p.holds v then (List.replicate c.count v, 1) else ([], 1)
  | none => ([], 0)

theorem filter_replicate (p : Nat → Bool) (v : Nat) (n : Nat) :
    (List.replicate n v).filter p = if p v then List.replicate n v else [] := by
  induction n with
  | zero => cases hp : p v <;> simp
  | succ k ih =>
      simp only [List.filter_cons, List.replicate_succ]
      cases hp : p v <;> simp [ih, hp]

/-- THE CONSTANT LAW: the encoded evaluation IS the decoded evaluation
    (`constRead`-then-filter), with the ONE-probe account. -/
theorem evalConst_ok (p : VPred) (c : ConstantData Nat) :
    evalConst p c
      = ((constRead c).filter p.holds, if c.value.isSome then 1 else 0) := by
  cases c with
  | mk n val =>
      cases val with
      | none => simp [evalConst, constRead]
      | some v =>
          simp only [evalConst, constRead, Option.isSome_some]
          cases hp : p.holds v <;> simp [hp]

/-- THE FoR COMPUTE CARRIER: the BYTE codec's own semantic form — the
    base (`colMin`, exactly `encFoR`'s) plus the Nat offsets. NOT a
    parallel table: the retention exemplar `FoRData` is the ℤ-faced
    law's carrier (lossless over ℤ); the compute carriers are uniform
    over the u64 column domain (the byte codec's domain — the same
    uniformity `Encoded`'s sum demands), and the decode face below is
    `map_add_colMin`'s own law. -/
structure FoRCompute where
  base : Nat
  offsets : List Nat

/-- The column's foR carrier: base = the column's min (the byte
    codec's own base), offsets from it. -/
def forComputeOf (xs : List Nat) : FoRCompute :=
  { base := colMin xs, offsets := xs.map (fun v => v - colMin xs) }

/-- The foR carrier's decoded face. -/
def forComputeRead (d : FoRCompute) : List Nat :=
  d.offsets.map (fun o => o + d.base)

/-- THE FoR ROW: the predicate projects onto the offsets (`shiftFoR`),
    the selection filters the offsets, the projection re-adds the base —
    the decoded value list is NEVER materialized (the offsets are the
    carrier's own content). The account: one probe per offset. -/
def evalFor? (p : VPred) (d : FoRCompute) : Option (List Nat × Nat) :=
  (shiftFoR p d.base).map fun q =>
    ((d.offsets.filter q.holds).map (fun o => o + d.base), d.offsets.length)

/-- THE FoR LAW: on the fragment (a shift exists), the encoded
    evaluation IS the decoded evaluation. The `.raw` row refuses
    (the `none` case — the fragment's boundary). -/
theorem evalFor?_ok (p : VPred) (d : FoRCompute)
    (h : (shiftFoR p d.base).isSome = true) :
    evalFor? p d = some ((forComputeRead d).filter p.holds, d.offsets.length) := by
  obtain ⟨q, hq⟩ : ∃ q, shiftFoR p d.base = some q := by
    cases hq0 : shiftFoR p d.base with
    | none => rw [hq0] at h; exact absurd h (by simp)
    | some q => exact ⟨q, rfl⟩
  simp only [evalFor?, hq, Option.map_some, forComputeRead]
  rw [filter_shift_map p q d.base (fun x => shiftFoR_holds p d.base x q hq) d.offsets]

/-- THE BITPACKED ROW — the fused peel: the selection walks the w-bit
    stream directly (`s % 2^w` per peel), keeping only the passing
    values — selection WITHOUT materializing the full decode. The
    account: one probe per peel (the stream position count). -/
def evalBitPack (p : VPred) (w : Nat) : (n : Nat) → Nat → List Nat × Nat
  | 0, _ => ([], 0)
  | n + 1, s =>
      if p.holds (s % 2 ^ w) then
        (s % 2 ^ w :: (evalBitPack p w n (s / 2 ^ w)).1, n + 1)
      else ((evalBitPack p w n (s / 2 ^ w)).1, n + 1)

theorem unpackStream_length (w : Nat) :
    ∀ (n s : Nat), (unpackStream w n s).length = n := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ k ih => intro s; simp [unpackStream, ih (s / 2 ^ w)]

/-- THE BITPACKED LAW — UNCONDITIONAL: the fused peel IS the decoded
    filter (`unpackStream`-then-filter), never materializing it. -/
theorem evalBitPack_ok (p : VPred) (w : Nat) : ∀ (n s : Nat),
    evalBitPack p w n s = ((unpackStream w n s).filter p.holds, n) := by
  intro n
  induction n with
  | zero => intro s; simp [evalBitPack, unpackStream]
  | succ k ih =>
      intro s
      simp only [evalBitPack, unpackStream]
      cases hp : p.holds (s % 2 ^ w) <;> simp [ih, hp]

/-- One dict row's compute: the code's value + its PRE-PROBED selection
    bit (the bit comes from the values table's single pass — no probe
    here). An out-of-range code refuses: corruption is loud. -/
def dictRow? (sel : List Bool) (vals : List Nat) (c : Nat) : Option (Option Nat) :=
  match atIdx? vals c with
  | none => none
  | some v =>
      match atIdx? sel c with
      | some b => some (if b then some v else none)
      | none => none

/-- The dict rows' streaming walk: the codes peel one at a time against
    the pre-probed selection vector; the first out-of-range code
    refuses the whole evaluation. -/
def evalDictRows (sel : List Bool) (vals : List Nat) :
    List Nat → Option (List Nat)
  | [] => some []
  | c :: cs =>
      match dictRow? sel vals c with
      | some (some v) => (evalDictRows sel vals cs).map (v :: ·)
      | some none => evalDictRows sel vals cs
      | none => none

/-- THE DICT ROW — the classic trick: the predicate probes the VALUES
    table ONCE (`mapCount` over `vals`), then the codes' selection
    vector re-indexes it. The account: the DISTINCT-VALUE count,
    independent of the row count. -/
def evalDict (p : VPred) (d : DictData) : Option (List Nat × Nat) :=
  (evalDictRows (mapCount p.holds d.vals).1 d.vals d.codes).map
    fun rows => (rows, (mapCount p.holds d.vals).2)

/-- The dict rows' law: with the values table's own selection vector,
    the walk IS the decoded filter. -/
theorem evalDictRows_ok (p : VPred) (vals : List Nat) (sel : List Bool)
    (hsel : sel = vals.map p.holds) :
    ∀ (codes : List Nat), codes.all (fun c => c < vals.length) = true →
      evalDictRows sel vals codes
        = some ((codes.map (fun c => (valueAt? c vals).getD 0)).filter p.holds) := by
  intro codes
  induction codes with
  | nil => intro _; rfl
  | cons c cs ih =>
      intro hall
      have hsplit := hall
      simp only [List.all_cons, Bool.and_eq_true] at hsplit
      have hc : c < vals.length := of_decide_eq_true hsplit.1
      have hcs : cs.all (fun x => x < vals.length) = true := hsplit.2
      obtain ⟨v, hv⟩ := atIdx?_exists_of_lt vals c hc
      have hvat : valueAt? c vals = some v :=
        (atIdx?_valueAt? vals c).symm.trans hv
      have hrow : dictRow? sel vals c
          = some (if p.holds v then some v else none) := by
        simp only [dictRow?, hv, Option.map_some, hsel, atIdx?_map]
      simp only [evalDictRows, hrow]
      cases hp : p.holds v <;> simp [ih hcs, hp, hvat]

/-- THE DICT LAW: on the uncorrupted carrier (every code in the values
    table's range), the encoded evaluation IS the decoded evaluation,
    with the distinct-value account. -/
theorem evalDict_ok (p : VPred) (d : DictData)
    (hok : d.codes.all (fun c => c < d.vals.length) = true) :
    evalDict p d = some ((dictDecode d).filter p.holds, d.vals.length) := by
  obtain ⟨vals, codes⟩ := d
  obtain ⟨msel, mlen⟩ := mapCount_ok p.holds vals
  simp only [evalDict, msel, mlen]
  rw [evalDictRows_ok p vals (vals.map p.holds) rfl codes hok]
  rfl

/-- The corrupted carrier REFUSES: one out-of-range code and the whole
    evaluation is `none` — never a fabricated row. -/
theorem evalDictRows_none (vals : List Nat) (sel : List Bool) :
    ∀ (codes : List Nat) (c : Nat), c ∈ codes → vals.length ≤ c →
      evalDictRows sel vals codes = none := by
  intro codes
  induction codes with
  | nil => intro c hm _; cases hm
  | cons u us ih =>
      intro c hm hge
      rcases List.mem_cons.mp hm with rfl | hin
      · simp only [evalDictRows, dictRow?, atIdx?_ge_none vals _ hge]
      · rw [evalDictRows]
        cases hd : dictRow? sel vals u with
        | none => simp
        | some r =>
            cases r with
            | none => simp [ih c hin hge]
            | some v => simp [ih c hin hge]

theorem evalDict_corrupt (p : VPred) (vals : List Nat) :
    ∀ (codes : List Nat) (c : Nat), c ∈ codes → vals.length ≤ c →
      evalDict p ⟨vals, codes⟩ = none := by
  intro codes c hc hge
  simp only [evalDict]
  rw [evalDictRows_none vals _ codes c hc hge]
  simp

/-! ## The carrier, the gate, the account — and THE LAWS -/

/-- The semantic encoded carrier (the compute grade's sum over the
    landed rows — the retention exemplars' own data types). -/
inductive Encoded where
  | rawVals (xs : List Nat)
  | bitPackData (w : Nat) (n : Nat) (stream : Nat)
  | forData (d : FoRCompute)
  | dictData (d : DictData)
  | constData (c : ConstantData Nat)

/-- The decoded face of each carrier (the law's right side). -/
def decodeOf : Encoded → List Nat
  | .rawVals xs => xs
  | .bitPackData w n s => unpackStream w n s
  | .forData d => forComputeRead d
  | .dictData d => dictDecode d
  | .constData c => constRead c

/-- THE COMPUTE GATE: the admissibility of (op, carrier) as data —
    the fragment's boundary on foR (a shift must exist: `.raw`
    refuses), the integrity gate on dict (every code in range:
    corruption refuses). The pointwise rows are unconditional. -/
def computeOk (p : VPred) : Encoded → Bool
  | .rawVals _ => true
  | .bitPackData _ _ _ => true
  | .forData d => (shiftFoR p d.base).isSome
  | .dictData d => d.codes.all (fun c => c < d.vals.length)
  | .constData _ => true

/-- The encoded path's probe account (the syntactic p-application
    count — see the header: each evaluator's structure makes it a
    definitional face). -/
def encodedProbes : Encoded → Nat
  | .rawVals xs => xs.length
  | .bitPackData _ n _ => n
  | .forData d => d.offsets.length
  | .dictData d => d.vals.length
  | .constData c => if c.value.isSome then 1 else 0

/-- The decoded baseline's probe account: the SAME instrument over the
    DECODED column — what decode-then-eval spends. -/
def decodeProbes (p : VPred) (e : Encoded) : Nat :=
  (mapCount p.holds (decodeOf e)).2

/-- The baseline account is the decoded column's length (the
    instrument's law — apples to apples with `encodedProbes`). -/
theorem decodeProbes_eq (p : VPred) (e : Encoded) :
    decodeProbes p e = (decodeOf e).length :=
  (mapCount_ok p.holds (decodeOf e)).2

/-- THE DIRECT EVALUATOR: per carrier, the encoded-form evaluation.
    `none` = refused (off-fragment or corrupted — the gate says which). -/
def evalEncoded (p : VPred) (e : Encoded) : Option (List Nat × Nat) :=
  match e with
  | .rawVals xs => some (xs.filter p.holds, xs.length)
  | .bitPackData w n s => some (evalBitPack p w n s)
  | .forData d => evalFor? p d
  | .dictData d => evalDict p d
  | .constData c => some (evalConst p c)

/-- THE COMPUTE LAW (the retention discipline, per (encoding, op)):
    `evalEncoded op enc ≡ decode enc |> eval op` — the encoded
    evaluation's result IS the decoded column's filter, with the
    encoded account. The gate premise names the admissible domain. -/
theorem evalEncoded_law (p : VPred) (e : Encoded) (hok : computeOk p e = true) :
    evalEncoded p e = some ((decodeOf e).filter p.holds, encodedProbes e) := by
  cases e with
  | rawVals xs => simp [evalEncoded, decodeOf, encodedProbes]
  | bitPackData w n s =>
      simp only [evalEncoded, decodeOf, encodedProbes]
      rw [evalBitPack_ok]
  | forData d =>
      simp only [computeOk] at hok
      simp only [evalEncoded, decodeOf, encodedProbes]
      exact evalFor?_ok p d hok
  | dictData d =>
      simp only [computeOk] at hok
      simp only [evalEncoded, decodeOf, encodedProbes]
      exact evalDict_ok p d hok
  | constData c =>
      simp only [evalEncoded, decodeOf, encodedProbes]
      rw [evalConst_ok p c]

/-! ## The fusion teeth (the account wins and ties) -/

/-- THE DICT WIN: the account is the DISTINCT-VALUE count — the row
    count never enters. On low-card data the encoded evaluation probes
    the values table once where decode-then-eval probes every row. -/
theorem dict_probes_win (p : VPred) (d : DictData)
    (h : d.vals.length < d.codes.length) :
    encodedProbes (.dictData d) < decodeProbes p (.dictData d) := by
  rw [decodeProbes_eq]
  have hl : (decodeOf (.dictData d)).length = d.codes.length := by
    simp [decodeOf, dictDecode]
  rw [hl]; exact h

/-- THE CONSTANT WIN: the account is ONE — the row count never enters
    (the landslide case: a million constant rows, one probe). -/
theorem const_probes_win (p : VPred) (v : Nat) (k : Nat) (hk : 1 < k) :
    encodedProbes (.constData { count := k, value := some v })
      < decodeProbes p (.constData { count := k, value := some v }) := by
  rw [decodeProbes_eq, decodeOf]
  simp only [constRead, List.length_replicate]
  exact hk

/-- The honest TIES — the pointwise rows: the account IS the row count,
    on both sides (the encoded path wins nothing there; the law is the
    only claim). -/
theorem account_tie_raw (p : VPred) (xs : List Nat) :
    encodedProbes (.rawVals xs) = decodeProbes p (.rawVals xs) := by
  rw [decodeProbes_eq]; rfl

theorem account_tie_bitPack (p : VPred) (w n s : Nat) :
    encodedProbes (.bitPackData w n s) = decodeProbes p (.bitPackData w n s) := by
  rw [decodeProbes_eq]
  simp [decodeOf, encodedProbes, unpackStream_length w n s]

theorem account_tie_for (p : VPred) (d : FoRCompute) :
    encodedProbes (.forData d) = decodeProbes p (.forData d) := by
  rw [decodeProbes_eq]
  simp [decodeOf, encodedProbes, forComputeRead]

/-! ## The column tie (the spec → carrier face) -/

/-- The carrier a spec + column build (the compute entry point).
    `sequence`/`sparse` refuse — THE NAMED GAPS (the header): the
    closed-form index-interval pushdown and the dict-trick nesting land
    with their first consumers. -/
def carrierOf? : EncodingSpec → List Nat → Option Encoded
  | .identity, xs => some (.rawVals xs)
  | .bitPacked w, xs => some (.bitPackData w xs.length (packStream w xs))
  | .foR _, xs => some (.forData (forComputeOf xs))
  | .dict, xs => some (.dictData (dictEncode xs))
  | .constant, xs => some (.constData (constEncode xs))
  | .sequence, _ => none
  | .sparse _, _ => none

/-- The dict carrier's codes are in range — `dictEncode`'s own codes
    are first-occurrence indices (the corruption gate holds by
    construction on the encode path). -/
theorem dictCodes_bound (xs : List Nat) :
    (dictCodes xs).all (fun c => c < (dedupVals xs).length) = true := by
  refine List.all_eq_true.mpr fun c hc => ?_
  obtain ⟨x, hx, hcx⟩ := List.mem_map.mp hc
  obtain ⟨i, hi, hvat⟩ := codeOf?_find (dedupVals xs) x (mem_dedupVals xs x hx)
  rw [hi] at hcx
  have hlt := valueAt?_bound (dedupVals xs) i (by simp [hvat])
  simp at hcx
  rw [show c = i from hcx.symm]
  exact decide_eq_true hlt

/-- The carrier's decoded face IS the column, on the in-domain data —
    the byte-tie at the compute grade (one case per encoding, each
    citing the codec's own law). -/
theorem decodeOf_carrier (e : EncodingSpec) (xs : List Nat)
    (hdom : inDomain e xs = true) (c : Encoded) (hc : carrierOf? e xs = some c) :
    decodeOf c = xs := by
  cases e with
  | identity =>
      simp only [carrierOf?, Option.some.injEq] at hc
      cases hc; rfl
  | bitPacked w =>
      simp only [carrierOf?, Option.some.injEq] at hc
      cases hc
      simp only [decodeOf]
      exact unpackStream_packStream w xs
        (fun v hv => of_decide_eq_true (List.all_eq_true.mp hdom v hv))
  | foR _ =>
      simp only [carrierOf?, Option.some.injEq] at hc
      cases hc
      show forComputeRead (forComputeOf xs) = xs
      exact map_add_colMin xs
  | dict =>
      simp only [carrierOf?, Option.some.injEq] at hc
      cases hc
      exact dictRetention xs
  | constant =>
      simp only [carrierOf?, Option.some.injEq] at hc
      cases hc
      cases xs with
      | nil => rfl
      | cons v vs =>
          have hall : vs.all (fun w => w == v) = true := by
            have h := List.all_eq_true.mp hdom
            refine List.all_eq_true.mpr fun w hw => ?_
            have hx := h w (by simp [hw])
            simp only [Bool.and_eq_true] at hx
            simpa using hx.2
          rw [show decodeOf (.constData (constEncode (v :: vs)))
              = constRead (constEncode (v :: vs)) from rfl]
          rw [constRead_constEncode v vs hall]
  | sequence => cases hc
  | sparse _ => cases hc

/-- THE COLUMN LAW: over a real in-domain column, the encoded
    evaluation (through the spec's carrier) IS the column's filter —
    `evalEncoded op enc ≡ decode enc |> eval op` at the column face. -/
theorem evalEncoded_column (p : VPred) (e : EncodingSpec) (xs : List Nat)
    (hdom : inDomain e xs = true) (c : Encoded) (hc : carrierOf? e xs = some c)
    (hok : computeOk p c = true) :
    evalEncoded p c = some (xs.filter p.holds, encodedProbes c) := by
  rw [evalEncoded_law p c hok, decodeOf_carrier e xs hdom c hc]

/-! ## THE AFFINE KERNEL GENERALIZATION (the flatland absorbables —
    arithmetic pushed INTO the encoding, E3)

`shiftFoR` above is the FoR ref-bump SPECIAL CASE. The general shape:
push ARITHMETIC into the encoding instead of decode-then-compute — per
(encoding × op), the absorb dispatches on the CARRIER:

- **constant** — the scalar rewrite with CHECKED overflow: the op
  applies to the single shared value (one probe); an inexact result
  REFUSES.
- **foR** — `absorbFor`: `addC` is THE REF-BUMP (the factor==1 face —
  the base takes the constant, the offsets are untouched, zero row
  work); `mulC` is the REBASE+BUMP (base·k, offsets·k) when the
  arithmetic is exact, else refuse.
- **dict** — the values-map: the op applies to the VALUES table once
  (O(|dict|)), the codes untouched.
- **primitive** (identity / bitPacked) — the wrapping row loop (the
  honest fallback; mod 2^64, never a refusal).

The LAW (the retention discipline at the arithmetic grade, the
landed `evalEncoded_law` as the precedent):
`evalArith op enc ≡ decode enc |> map op`, gated by `arithOk` — the
op's exactness class per carrier (exact-on-range / wrapping). -/

/-- The affine op as data: `x ↦ x + c` / `x ↦ x · k` (the study's
    add-const / mul-const kernels). Floats are rejected by policy (the
    hazard law note below) — the op's domain is the u64 column's. -/
inductive AOp where
  | addC (c : Nat)
  | mulC (k : Nat)

/-- The op's WRAPPING semantics (mod 2^64 — the u64 column domain):
    the primitive arms' exact face (the honest wrapping row loop). -/
def AOp.eval : AOp → Nat → Nat
  | .addC c, x => (x + c) % 2 ^ 64
  | .mulC k, x => (x * k) % 2 ^ 64

/-- The op's EXACT result (the pre-mod arithmetic — the rewrite
    arms' face). -/
def AOp.exactEval : AOp → Nat → Nat
  | .addC c, x => x + c
  | .mulC k, x => x * k

/-- The op's EXACTNESS CLASS on a value: exact-on-range when the
    result stays in the u64 domain. The pushdown arms REFUSE off-range
    (the checked-overflow class); the primitive arms wrap. -/
def AOp.exactOn : AOp → Nat → Bool
  | .addC c, x => decide (x + c < 2 ^ 64)
  | .mulC k, x => decide (x * k < 2 ^ 64)

/-- The classes meet: an exact result's wrap IS the exact arithmetic. -/
theorem AOp.eval_eq_exact (op : AOp) (x : Nat) (h : op.exactOn x = true) :
    op.eval x = op.exactEval x := by
  cases op with
  | addC c =>
      simp only [exactOn, decide_eq_true_eq] at h
      simp [eval, exactEval, Nat.mod_eq_of_lt h]
  | mulC k =>
      simp only [exactOn, decide_eq_true_eq] at h
      simp [eval, exactEval, Nat.mod_eq_of_lt h]

/-- The arithmetic instrument (mapCount's transform twin): the mapped
    list + the count of `f` applications — the op-application account. -/
def transCount (f : Nat → Nat) : List Nat → List Nat × Nat
  | [] => ([], 0)
  | x :: xs => (f x :: (transCount f xs).1, (transCount f xs).2 + 1)

/-- The instrument's law: both faces are the plain map/length. -/
theorem transCount_ok (f : Nat → Nat) (xs : List Nat) :
    (transCount f xs).1 = xs.map f ∧ (transCount f xs).2 = xs.length := by
  induction xs with
  | nil => simp [transCount]
  | cons u us ih => simp [transCount, ih]

/-- `valueAt?` survives a pointwise map (the dict values-map's fusion
    face): the code indexes the SAME row of the mapped table. -/
theorem valueAt?_map (f : Nat → Nat) :
    ∀ (xs : List Nat) (i : Nat), valueAt? i (xs.map f) = (valueAt? i xs).map f := by
  intro xs
  induction xs with
  | nil => intro i; cases i <;> rfl
  | cons u us ih =>
      intro i
      cases i with
      | zero => rfl
      | succ i' => simp [valueAt?, ih i']

/-- A hit is a member (the values-map's exactness gate lifts to the
    probed value). -/
theorem valueAt?_mem : ∀ (xs : List Nat) (i : Nat) (v : Nat),
    valueAt? i xs = some v → v ∈ xs := by
  intro xs
  induction xs with
  | nil => intro i v h; simp [valueAt?] at h
  | cons u us ih =>
      intro i v h
      cases i with
      | zero => simp [valueAt?] at h; rw [h]; simp
      | succ i' =>
          simp only [valueAt?] at h
          exact List.mem_cons_of_mem _ (ih i' v h)

/-! ### The arms (per carrier; each self-checked) -/

/-- THE CONSTANT ARM — the scalar rewrite, CHECKED overflow (the
    study's arm (a)): the op applies to the single shared value — ONE
    application; an inexact result refuses the absorb (never a silent
    wrap through the rewrite). -/
def absorbConst (op : AOp) (c : ConstantData Nat) : Option (Encoded × Nat) :=
  match c.value with
  | some v =>
      if op.exactOn v then
        some (.constData ⟨c.count, some (op.exactEval v)⟩, 1)
      else none
  | none => some (.constData c, 0)

/-- THE FoR ARMS — the absorbable pushdowns (the study's arm (b)):
    `addC c` is THE REF-BUMP (the affine's factor==1 face): the base
    takes the constant, the offsets are UNTOUCHED — zero row work.
    `mulC k` is the REBASE+BUMP: base·k, offsets·k (row work: the
    offsets' map). Both CHECKED: an offset whose arithmetic leaves the
    u64 domain refuses (the exact-on-range class — never a silent
    wrap). -/
def absorbFor (op : AOp) (d : FoRCompute) : Option (Encoded × Nat) :=
  match op with
  | .addC c =>
      if d.offsets.all (fun o => (AOp.addC c).exactOn (d.base + o)) then
        some (.forData ⟨d.base + c, d.offsets⟩, 0)
      else none
  | .mulC k =>
      if d.offsets.all (fun o => (AOp.mulC k).exactOn (d.base + o)) then
        some (.forData ⟨d.base * k, d.offsets.map (fun o => o * k)⟩,
          d.offsets.length)
      else none

/-- THE DICT ARM — the values-map (the study's arm (c), O(|dict|)):
    the op applies to the VALUES table once; the codes are UNTOUCHED.
    Checked: an inexact table value refuses (the table stays in the
    u64 domain). The CODE-RANGE integrity gate (a corrupted carrier
    refuses — never a fabricated row) rides the SPINE (`arithOk`'s
    dict arm, `computeOk`'s mirror). The account: the TABLE's length —
    the teeth pin it. -/
def absorbDict (op : AOp) (d : DictData) : Option (Encoded × Nat) :=
  if d.vals.all (AOp.exactOn op) then
    some (.dictData ⟨d.vals.map (AOp.exactEval op), d.codes⟩, d.vals.length)
  else none

/-- THE ABSORB DISPATCH — per (encoding, op), the pushdown or the
    fallback. The result carries its OWN account (the syntactic
    op-application count — no drift possible). The primitive rows are
    the honest fallback (the study's arm (d)): the wrapping row loop —
    the op rides the row domain, mod 2^64, never a refusal; the
    bitPacked face fuses peel+op in one walk (the terminal's row
    loop), the absorbable spent, the carrier lands raw. -/
def absorbAOp? (op : AOp) (e : Encoded) : Option (Encoded × Nat) :=
  match e with
  | .rawVals xs => some (.rawVals (xs.map (AOp.eval op)), xs.length)
  | .bitPackData w n s =>
      some (.rawVals ((unpackStream w n s).map (AOp.eval op)), n)
  | .constData c => absorbConst op c
  | .forData d => absorbFor op d
  | .dictData d => absorbDict op d

/-- THE ARITHMETIC GATE (the inDomain face, per (op, carrier) — the
    op's exactness class): the pushdown arms are the CHECKED class
    (constant / FoR / dict refuse inexact arithmetic), the primitive
    arms the WRAPPING class (never refuse). -/
def arithOk (op : AOp) : Encoded → Bool
  | .rawVals _ => true
  | .bitPackData _ _ _ => true
  | .constData c =>
      match c.value with
      | some v => op.exactOn v
      | none => true
  | .forData d => d.offsets.all (fun o => op.exactOn (d.base + o))
  | .dictData d =>
      -- the integrity gate (the corrupted carrier refuses) + the
      -- values-table's exactness (the checked class)
      d.codes.all (fun c => c < d.vals.length) && d.vals.all (AOp.exactOn op)

/-- The arithmetic account (the syntactic op-application count — the
    absorb's second component, restated): the pushdown wins are the
    teeth's content below. -/
def arithProbes (op : AOp) : Encoded → Nat
  | .rawVals xs => xs.length
  | .bitPackData _ n _ => n
  | .forData d =>
      match op with
      | .addC _ => 0
      | .mulC _ => d.offsets.length
  | .dictData d => d.vals.length
  | .constData c => if c.value.isSome then 1 else 0

/-- The decoded baseline's arithmetic account: the row count (the map
    over every row — the same apples-to-apples face as `decodeProbes`). -/
def arithDecodeProbes (_op : AOp) (e : Encoded) : Nat := (decodeOf e).length

/-! ### The spine, THE LAW, and the teeth -/

/-- THE ARITHMETIC EVALUATOR: the op pushed into the encoding — the
    absorb runs, the result reads back through the carrier's own
    decode. `none` = refused (the checked-overflow class fired). -/
def evalArith (op : AOp) (e : Encoded) : Option (List Nat × Nat) :=
  if arithOk op e then
    (absorbAOp? op e).map fun (e', probes) => (decodeOf e', probes)
  else none

/-- THE ARITHMETIC LAW (the retention discipline at the arithmetic
    grade, per (encoding, op)): `evalArith op enc ≡ decode enc |>
    map op` — the absorbed carrier's decode IS the decoded column's
    map, with the absorb's own account. The gate premise names the
    admissible domain (the checked class). -/
theorem evalArith_law (op : AOp) (e : Encoded) (hok : arithOk op e = true) :
    evalArith op e
      = some ((decodeOf e).map (AOp.eval op), arithProbes op e) := by
  rw [evalArith, if_pos hok]
  cases e with
  | rawVals xs => simp [absorbAOp?, decodeOf, arithProbes]
  | bitPackData w n s => simp [absorbAOp?, decodeOf, arithProbes]
  | constData c =>
      cases c with
      | mk n val =>
          cases val with
          | none =>
              simp [absorbAOp?, absorbConst, decodeOf, constRead, arithProbes]
          | some v =>
              have hx : op.exactOn v = true := by simpa [arithOk] using hok
              simp only [absorbAOp?, absorbConst, if_pos hx, Option.map_some,
                Option.some.injEq, decodeOf, constRead]
              show (List.replicate n (AOp.exactEval op v), 1)
                  = (List.map (AOp.eval op) (List.replicate n v), 1)
              rw [List.map_replicate, AOp.eval_eq_exact op v hx]
  | forData d =>
      cases op with
      | addC c =>
          have hg : d.offsets.all (fun o => (AOp.addC c).exactOn (d.base + o))
              = true := by simpa [arithOk] using hok
          have key : ∀ o ∈ d.offsets,
              o + (d.base + c) = (AOp.addC c).eval (o + d.base) := by
            intro o ho
            have hx : d.base + o + c < 2 ^ 64 := by
              simpa [AOp.exactOn, decide_eq_true_eq]
                using List.all_eq_true.mp hg o ho
            simp only [AOp.eval]
            have := Nat.mod_eq_of_lt (by omega)
            omega
          simp only [absorbAOp?, absorbFor, if_pos hg, Option.map_some,
            Option.some.injEq, decodeOf, forComputeRead, arithProbes,
            List.map_map, Prod.mk.injEq]
          exact ⟨List.map_congr_left key, by simp⟩
      | mulC k =>
          have hg : d.offsets.all (fun o => (AOp.mulC k).exactOn (d.base + o))
              = true := by simpa [arithOk] using hok
          have key : ∀ o ∈ d.offsets,
              o * k + d.base * k = (AOp.mulC k).eval (o + d.base) := by
            intro o ho
            have hx0 : (d.base + o) * k < 2 ^ 64 := by
              simpa [AOp.exactOn, decide_eq_true_eq]
                using List.all_eq_true.mp hg o ho
            have hx : (o + d.base) * k < 2 ^ 64 := by
              rw [Nat.add_comm o d.base]; exact hx0
            show o * k + d.base * k = ((o + d.base) * k) % 2 ^ 64
            rw [Nat.mod_eq_of_lt hx, Nat.add_mul]
          simp only [absorbAOp?, absorbFor]
          rw [if_pos hg]
          simp only [Option.map_some, Option.some.injEq, decodeOf,
            forComputeRead, arithProbes, List.map_map, Prod.mk.injEq]
          exact ⟨List.map_congr_left key, by simp⟩
  | dictData d =>
      obtain ⟨hgr, hg⟩ : d.codes.all (fun c => c < d.vals.length) = true
          ∧ d.vals.all (AOp.exactOn op) = true := by
        simpa [arithOk] using hok
      have key : ∀ c ∈ d.codes,
          (valueAt? c (d.vals.map (AOp.exactEval op))).getD 0
            = AOp.eval op ((valueAt? c d.vals).getD 0) := by
        intro c hc
        have hcr : c < d.vals.length :=
          of_decide_eq_true (List.all_eq_true.mp hgr c hc)
        obtain ⟨v, hv⟩ := atIdx?_exists_of_lt d.vals c hcr
        have hvat : valueAt? c d.vals = some v :=
          (atIdx?_valueAt? d.vals c).symm.trans hv
        rw [valueAt?_map, hvat]
        have hx : op.exactOn v = true :=
          List.all_eq_true.mp hg v (valueAt?_mem d.vals c v hvat)
        simp [Option.map_some, Option.getD_some, AOp.eval_eq_exact op v hx]
      simp only [absorbAOp?, absorbDict, if_pos hg, Option.map_some,
        Option.some.injEq, decodeOf, dictDecode, arithProbes, List.map_map,
        Prod.mk.injEq]
      exact ⟨List.map_congr_left key, by simp⟩

/-! ### The fusion teeth (the arithmetic account's wins and ties) -/

/-- THE FoR REF-BUMP WIN (the study's "zero row work", measured): the
    add absorb's account is ZERO — the row count never enters. -/
theorem for_add_probes_zero (c : Nat) (d : FoRCompute) :
    arithProbes (AOp.addC c) (.forData d) = 0 := rfl

/-- THE FoR ADD WIN: zero row work against the decoded baseline's
    row-length account (on any nonempty column). -/
theorem for_add_win (c : Nat) (d : FoRCompute) (h : 0 < d.offsets.length) :
    arithProbes (AOp.addC c) (.forData d)
      < arithDecodeProbes (AOp.addC c) (.forData d) := by
  simp [arithDecodeProbes, decodeOf, forComputeRead]
  exact h

/-- THE CONSTANT WIN: the rewrite is ONE application — the row count
    never enters (the landslide case). -/
theorem const_arith_win (op : AOp) (v : Nat) (k : Nat) (hk : 1 < k) :
    arithProbes op (.constData { count := k, value := some v })
      < arithDecodeProbes op (.constData { count := k, value := some v }) := by
  simp [arithDecodeProbes, decodeOf, constRead, List.length_replicate]
  exact hk

/-- THE DICT WIN: the account is the TABLE's length — the row (code)
    count never enters (the O(|dict|) discipline's teeth). -/
theorem dict_arith_win (op : AOp) (d : DictData)
    (h : d.vals.length < d.codes.length) :
    arithProbes op (.dictData d)
      < arithDecodeProbes op (.dictData d) := by
  simp [arithDecodeProbes, decodeOf, dictDecode]
  exact h

/-- The honest TIE — the primitive rows: the wrapping loop's account
    IS the row count, both sides. -/
theorem raw_arith_tie (op : AOp) (xs : List Nat) :
    arithProbes op (.rawVals xs) = arithDecodeProbes op (.rawVals xs) := rfl

/-! ### THE f64-EXACTNESS HAZARD LAW NOTE (vortex-fork.md:299-303) -/

/-- The exactness horizon: above 2^53 an f64 cast loses u64 integers
    (the fused-kernel hazard the flatland study measured —
    `apply_msg_op`'s pointwise-f64-hop). -/
def f53 : Nat := 9007199254740992

/-- THE DISCIPLINE — the named refusal: NO f64-cast kernel exists in
    the arithmetic selection. u64/i64 arithmetic rides the exact Nat
    lanes (the wrapping mod-2^64 face, `AOp.eval`) or REFUSES (the
    checked gates); an inexact pushdown is a REFUSAL, never a float
    round-trip. -/
theorem hazard_refused_not_rounded (op : AOp) (v : Nat)
    (h : op.exactOn v = false) :
    evalArith op (.constData { count := 1, value := some v }) = none := by
  simp [evalArith, arithOk, h]

/-- The integer lane's face: the wrapping kernel NEVER leaves the u64
    domain — the f53 cliff is unreachable because no kernel ever
    leaves the integer domain (the exactness does not degrade with
    magnitude; there is no float in the path). -/
theorem hazard_no_f53_cliff (op : AOp) (x : Nat) : AOp.eval op x < 2 ^ 64 := by
  cases op <;> exact Nat.mod_lt _ (by omega)

/-- The study's concrete hazard face: a u64 value ABOVE the f53
    horizon rides the integer lane EXACTLY (`addC 0` is the identity
    mod 2^64) — where the f64 hop would round silently. -/
theorem hazard_above_f53_exact (v : Nat) (_hv : f53 ≤ v) (hv64 : v < 2 ^ 64) :
    AOp.eval (AOp.addC 0) v = v :=
  Nat.mod_eq_of_lt hv64

end Vortex
