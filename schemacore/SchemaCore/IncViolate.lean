/-
# SchemaCore.IncViolate — the incremental violation maintenance (03 §8's ΔV face)

Owner: the bidirectional-slice agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/03-bidirectional.md §8 (THE STRONGEST SINGLE
COMPOSITION: constraints compiled to maintained violation queries; the
commit gate is the empty-result verdict; the foundation proves the
incremental result equals full recomputation — ONCE) + §9 (the
derivative discipline: `ΔQ = Q(B + ΔB) − Q(B)`; the join's delta
carries the cross term — NEVER infer linearity) + notes/v3/
02-data-plane.md §4 (the weighted relations — the violation relation is
a ℤ/weighted query).

THE DERIVATIVE DISCIPLINE, AT THE SLICE'S SIZE. The landed
`Commit.checkDelta` checks the POST-STATE — full recomputation, the
honest first cut its header names. This module lands the
change-proportional face the header deferred: the delta's effect on the
violation relation, computed from the DELTA + the old state, with the
agreement theorem — the maintained relation is the recomputed relation
(`incViolations_perm`), hence the same empty-result verdict
(`incViolations_clean_iff`, the commit gate's law).

Per query (Violate's table), the honest rung:

- `negativeAccounts` — POINTWISE: the face is a row filter, so the
  delta evaluation is row-local. The update step (`negUpd`) maintains
  the face from the delta + the old state — including the REVIVED block
  (a previously-clean row whose update goes negative: the naive
  violations-only maintenance misses it — the tooth is pinned in
  SchemaTests.Inc). The step's list order is blocked where the
  recompute's is positional, so the update face's agreement is a
  `List.Perm` — the violation relation is a SET of diagnostics (02 §1),
  its executable image's order is not the spec.
- `danglingSrc` / `danglingDst` — JOIN-shaped: a transfer's dangling
  verdict is membership in the account ids. Under account UPDATES the
  id list is stable (`accIds_stable_update` — proved, general), so the
  faces are maintained EXACTLY through transfer INSERT/REMOVE deltas
  (`dangStep1?`, one step function parameterized by the endpoint
  getter — Violate's `dangling_eq_nil_iff` shape).
- `dupIds` — count-based: OUTSIDE the linear fragment (03 §9: counts
  carry maintained state; a list face carries none). The FALLBACK — the
  face is recomputed over the MAINTAINED id list, named here.

THE HONESTY BOUNDARY (03 §8: "a constraint outside the efficient
incremental fragment gets the fallback checker — named, never silent").
`accStep?` returns `none` for account INSERT/REMOVE (the id list moves:
the join faces' ΔA — the semijoin's other side must be re-scanned, and
the join's delta must carry the cross term ΔA⋈ΔB) and `dangStep1?`
returns `none` for transfer UPDATE (a rewrite can dangle a resolved row
at any endpoint). A `none` — or a whole-delta fold hitting one — routes
`incViolations` to the fallback checker: the full post-state
recomputation. The routing is the OPTION, mechanically enforced — a
delta outside the fragment CANNOT take the maintained path.

THE CROSS TERM IS LOAD-BEARING, AND THE BOUNDARY IS ITS GUARD: for the
cross delta (an account insert + a transfer insert referencing it), the
naive delta evaluation — the transfer insert judged against the OLD ids
— dangles the transfer (a false refusal); the checker (the maintained
path refusing the fragment, the fallback carrying the join fresh)
accepts. Pinned in SchemaTests.Inc, both sides.

THE COMMIT INTEGRATION: `checkDeltaInc` is the delta-driven check path
alongside `Commit.checkDelta`'s post-state path; `checkDeltaInc_perm`
is the faces' agreement and `checkVerdictInc_agree` the verdicts' — the
two faces agree BY PROOF, and SchemaTests.Inc exercises both on the
slice's fixture (the duel's proposals, verdict-for-verdict,
payload-for-payload).

The five questions (notes/v3/01-core.md): root = the constraint face's
maintained relation (03 §8's ΔV at the slice's substrate); carrier =
the maintained face lists + the Option fragment dispatch (a `none` IS
the named boundary — data, not prose); spine reading = none — the
module rides Violate's queries + Update's `applyRowDelta`, re-proving
nothing the lanes own; ladder rung = the agreement theorems are the
small hand kind (list filter/Perm algebra over the pointwise and
membership bridges Violate proved); gate row = SchemaTests.Inc's
incSpec + the axiom report.

Core-only (imports SchemaCore.Commit — the cone rule; the commit lane's
`Deltas`/`applyDeltas`/`postDb` are the delta substrate, consumed, not
re-invented).
-/

import SchemaCore.Commit
import Kit.Change
import Kit.ListExtras

-- The filters' commutation is Kit.ListExtras' (the DRY sweep's ONE
-- copy — core ships `filter_filter`, never the commuted form).
open Kit.ListExtras (filter_filter_comm)

namespace SchemaCore

/-! ## The key images (the projection is total by the GADT index) -/

/-- The account row's key image (the declared key `id`). -/
def accKey (r : RowVals accountFields) : FieldVal := ⟨.u64, .u64 (accId r)⟩

/-- The transfer row's key image (the declared key `tid`). -/
def trKey (t : RowVals transferFields) : FieldVal := ⟨.u64, .u64 (trId t)⟩

theorem accKey_proj : ∀ (r : RowVals accountFields),
    RowVals.project? accountFields r "id" = some (accKey r)
  | .cons (.u64 _) (.cons (.string _) (.cons (.i64 _) .nil)) => rfl

theorem trKey_proj : ∀ (t : RowVals transferFields),
    RowVals.project? transferFields t "tid" = some (trKey t)
  | .cons (.u64 _) (.cons (.u64 _) (.cons (.u64 _) (.cons (.u64 _) .nil))) => rfl

/-- The key images' beq IS the ids' beq (the `.u64` ctor is injective). -/
theorem accKey_beq (a b : RowVals accountFields) :
    FieldVal.beq (accKey a) (accKey b) = (accId a == accId b) := rfl

theorem trKey_beq (a b : RowVals transferFields) :
    FieldVal.beq (trKey a) (trKey b) = (trId a == trId b) := rfl

/-! ## The keyed application's update arm, at the account key -/

/-- The update arm's step function (the keyed applicator's map, at the
    account's declared key — the projection is total by the index). -/
def accUpd (r old : RowVals accountFields) : RowVals accountFields :=
  if FieldVal.beq (accKey old) (accKey r) then r else old

theorem accUpd_eq (r a : RowVals accountFields) :
    (match RowVals.project? accountFields a "id" with
      | some x =>
          match RowVals.project? accountFields r "id" with
          | some b => if FieldVal.beq x b then r else a
          | none => a
      | none => a)
    = accUpd r a := by
  unfold accUpd
  rw [accKey_proj a, accKey_proj r]

/-- THE KEYED APPLICATION'S UPDATE ARM IS A MAP (at the account key) —
    the shape every maintained account face reads. -/
theorem applyRowDelta_update_acc (r : RowVals accountFields)
    (rows : List (RowVals accountFields)) :
    applyRowDelta "id" (RowDelta.update r) rows = rows.map (accUpd r) := by
  rw [applyRowDelta]
  exact List.map_congr_left (fun a _ => accUpd_eq r a)

theorem accUpd_id (r a : RowVals accountFields) : accId (accUpd r a) = accId a := by
  unfold accUpd
  by_cases hm : FieldVal.beq (accKey a) (accKey r) = true
  · rw [if_pos hm]
    have hke : accKey a = accKey r := beq_iff_eq.mp hm
    have : accId a = accId r := by simpa [accKey] using hke
    rw [this]
  · rw [if_neg hm]

/-- THE ID LIST IS STABLE under an account update: the keyed applicator
    replaces a row only with one carrying the SAME key image, so the
    key-id projection is pointwise fixed (the join faces' lease on
    life — the account-delta face of the join is EMPTY under updates). -/
theorem accIds_stable_update (r : RowVals accountFields)
    (rows : List (RowVals accountFields)) :
    accIds (applyRowDelta "id" (RowDelta.update r) rows) = accIds rows := by
  rw [applyRowDelta_update_acc]
  show List.map accId (List.map (accUpd r) rows) = List.map accId rows
  induction rows with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, accUpd_id]
      exact congrArg _ ih

/-! ## The negative face's maintained step (the pointwise face) -/

/-- The maintained negative face under an account UPDATE: the old
    violations not matching the updated key, plus the matching rows' new
    image — kept iff the new balance is negative. THE REVIVED BLOCK: the
    second summand reads the ROW TABLE (the maintained state carries it
    — the keyed application is the substrate's own primitive), because a
    previously-clean matching row's update can go negative. A
    violations-only maintenance misses exactly that revival — the
    naive-delta tooth pinned in SchemaTests.Inc. -/
def negUpd (A negs : List (RowVals accountFields)) (r : RowVals accountFields) :
    List (RowVals accountFields) :=
  negs.filter (fun o => !FieldVal.beq (accKey o) (accKey r))
    ++ (if decide (accBal r < 0) then
          List.map (fun _ => r)
            (List.filter (fun o => FieldVal.beq (accKey o) (accKey r)) A)
        else [])

theorem negRow_accUpd (r a : RowVals accountFields) :
    decide (accBal (accUpd r a) < 0)
      = if FieldVal.beq (accKey a) (accKey r) then decide (accBal r < 0)
        else decide (accBal a < 0) := by
  unfold accUpd
  by_cases hm : FieldVal.beq (accKey a) (accKey r) = true
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm]

/-- THE NEGATIVE FACE'S UPDATE AGREEMENT (the pointwise face's delta
    evaluation — 03 §9's ΔQ at the row granularity): the maintained face
    is the recomputed face, up to the executable image's order (the
    violation relation is a SET of diagnostics — 02 §1; the verdict
    consumes only its emptiness). -/
theorem negUpd_agree (A negs : List (RowVals accountFields))
    (r : RowVals accountFields) (h : List.Perm negs (negativeAccounts A)) :
    List.Perm (negUpd A negs r)
      (negativeAccounts (applyRowDelta "id" (RowDelta.update r) A)) := by
  rw [applyRowDelta_update_acc, negativeAccounts, List.filter_map,
    List.filter_congr (p := (fun r => decide (accBal r < 0)) ∘ accUpd r)
      fun o _ => negRow_accUpd r o]
  -- the recomputed filter's partition: matching rows (whose image is r)
  -- vs non-matching rows (whose image is themselves)
  have part := List.filter_append_perm
    (fun o => FieldVal.beq (accKey o) (accKey r))
    (List.filter (fun o =>
      if FieldVal.beq (accKey o) (accKey r) then decide (accBal r < 0)
      else decide (accBal o < 0)) A)
  -- the matching block's map: copies of r, kept iff the new balance is negative
  have mmap : List.map (accUpd r)
        (List.filter (fun o => FieldVal.beq (accKey o) (accKey r))
          (List.filter (fun o =>
            if FieldVal.beq (accKey o) (accKey r) then decide (accBal r < 0)
            else decide (accBal o < 0)) A))
      = List.map (fun _ => r)
          (List.filter (fun o => FieldVal.beq (accKey o) (accKey r)
            && decide (accBal r < 0)) A) := by
    rw [List.filter_filter, List.filter_congr
      (q := fun o => FieldVal.beq (accKey o) (accKey r) && decide (accBal r < 0))
      (fun o (_ : o ∈ A) => by
        cases hb : FieldVal.beq (accKey o) (accKey r) <;> simp [])]
    exact List.map_congr_left (f := accUpd r) (g := fun _ => r)
      (l := List.filter (fun o => FieldVal.beq (accKey o) (accKey r)
        && decide (accBal r < 0)) A)
      fun a ha => by
      have h2 := (List.mem_filter.mp ha).2
      simp only [Bool.and_eq_true] at h2
      cases hbb : FieldVal.beq (accKey a) (accKey r) with
      | false => simp [hbb] at h2
      | true => simp only [accUpd, if_pos hbb]
  -- the non-matching block's map: the rows themselves (their own verdicts)
  have nmap : List.map (accUpd r)
        (List.filter (fun o => !FieldVal.beq (accKey o) (accKey r))
          (List.filter (fun o =>
            if FieldVal.beq (accKey o) (accKey r) then decide (accBal r < 0)
            else decide (accBal o < 0)) A))
      = List.filter (fun o => !FieldVal.beq (accKey o) (accKey r)
        && decide (accBal o < 0)) A := by
    rw [List.filter_filter, List.filter_congr
      (q := fun o => !FieldVal.beq (accKey o) (accKey r)
        && decide (accBal o < 0))
      (fun o (_ : o ∈ A) => by
        cases hb : FieldVal.beq (accKey o) (accKey r) <;> simp [])]
    have hcongr : List.map (accUpd r)
        (List.filter (fun o => !FieldVal.beq (accKey o) (accKey r)
          && decide (accBal o < 0)) A)
      = List.map (fun o => o)
          (List.filter (fun o => !FieldVal.beq (accKey o) (accKey r)
            && decide (accBal o < 0)) A) :=
      List.map_congr_left (f := accUpd r) (g := fun o => o)
        (l := List.filter (fun o => !FieldVal.beq (accKey o) (accKey r)
          && decide (accBal o < 0)) A)
        (fun a ha => by
          have h2 := (List.mem_filter.mp ha).2
          simp only [Bool.and_eq_true] at h2
          cases hbb : FieldVal.beq (accKey a) (accKey r) with
          | false =>
              have hneg : ¬(FieldVal.beq (accKey a) (accKey r) = true) := by
                simp [hbb]
              simp only [accUpd, if_neg hneg]
          | true => simp [hbb] at h2)
    rw [hcongr, List.map_id']
  -- the non-matching survivors ARE the old violations' survivors
  have nsurv : List.Perm
      (List.filter (fun o => !FieldVal.beq (accKey o) (accKey r)
        && decide (accBal o < 0)) A)
      (List.filter (fun o => !FieldVal.beq (accKey o) (accKey r)) negs) := by
    rw [← List.filter_filter, ← negativeAccounts]
    exact (List.Perm.filter _ h).symm
  -- the matching block is the r-copies iff the new balance is negative
  have mif : (if decide (accBal r < 0) then
          List.map (fun _ => r)
            (List.filter (fun o => FieldVal.beq (accKey o) (accKey r)) A)
        else [])
      = List.map (fun _ => r)
          (List.filter (fun o => FieldVal.beq (accKey o) (accKey r)
            && decide (accBal r < 0)) A) := by
    cases hr : decide (accBal r < 0) with
    | false => simp [List.filter_eq_nil_iff]
    | true => simp []
  -- the recomputed face's partition, mapped (the blocked form)
  have partmap : List.Perm
      (List.map (accUpd r)
        (List.filter (fun o =>
          if FieldVal.beq (accKey o) (accKey r) then decide (accBal r < 0)
          else decide (accBal o < 0)) A))
      (List.map (accUpd r)
          (List.filter (fun o => FieldVal.beq (accKey o) (accKey r))
            (List.filter (fun o =>
              if FieldVal.beq (accKey o) (accKey r) then decide (accBal r < 0)
              else decide (accBal o < 0)) A))
        ++ List.map (accUpd r)
            (List.filter (fun o => !FieldVal.beq (accKey o) (accKey r))
              (List.filter (fun o =>
                if FieldVal.beq (accKey o) (accKey r) then decide (accBal r < 0)
                else decide (accBal o < 0)) A))) := by
    refine List.Perm.trans (List.Perm.map _ part.symm) ?_
    rw [List.map_append]
  refine List.Perm.trans ?_ (List.Perm.symm partmap)
  rw [negUpd, mif, mmap.symm]
  exact (List.perm_append_comm).trans
    (List.Perm.append (List.Perm.refl _)
      (nsurv.symm.trans (List.Perm.of_eq nmap.symm)))

/-! ## The account fold (the maintained state threads table + face) -/

/-- THE MAINTAINED ACCOUNT STATE: the table (the keyed application's own
    image — the substrate primitive, not a re-invention) + the negative
    face, threaded together. The table is what the revived block reads. -/
structure AccState where
  /-- The table's image under the deltas applied so far. -/
  table : List (RowVals accountFields)
  /-- The maintained negative face of that table. -/
  negs : List (RowVals accountFields)

/-- THE MAINTAINED ACCOUNT STEP. The update arm maintains the negative
    face from the delta + the old state (`negUpd`). THE HONESTY
    BOUNDARY: insert/remove return `none` — an account set-change moves
    the id list, and the JOIN faces' ΔA (the semijoin's other side +
    the cross term ΔA⋈ΔB) is outside the fragment. The `none` routes
    `incViolations` to the fallback checker — named, never silent. -/
def accStep? (d : RowDelta accountFields) (st : AccState) : Option AccState :=
  match d with
  | .update r =>
      some { table := applyRowDelta "id" (RowDelta.update r) st.table
           , negs := negUpd st.table st.negs r }
  | _ => none

/-- The account fold — Kit.Change's ONE poison-fold (`optionFoldl`)
    at the maintained account step (the DRY sweep: the first `none`
    poisons it, the fold's shape is the ladder's own operation). -/
def accFold? (ds : List (RowDelta accountFields)) (st : AccState) : Option AccState :=
  Kit.optionFoldl (fun st d => accStep? d st) ds st

/-- THE ACCOUNT FOLD'S AGREEMENT (the once-proof for every account-delta
    list in the fragment): the folded table IS the keyed application's
    table, and the maintained face is the recomputed face (up to the
    executable image's order). The induction is Kit.Change's
    `optionFoldl_agree` — the lanes instantiate `R` (the table identity
    + the maintained face), never re-roll it. -/
def accStepAgreeR (st : AccState) (t : List (RowVals accountFields)) : Prop :=
  st.table = t ∧ List.Perm st.negs (negativeAccounts t)

theorem accFold_agree (ds : List (RowDelta accountFields)) :
    ∀ (st : AccState), List.Perm st.negs (negativeAccounts st.table) →
      ∀ st' : AccState, accFold? ds st = some st' →
        st'.table = List.foldl (fun t d => applyRowDelta "id" d t) st.table ds
          ∧ List.Perm st'.negs (negativeAccounts st'.table) := by
  intro st hp
  have h : ∀ st' : AccState, accFold? ds st = some st' →
      accStepAgreeR st'
        (List.foldl (fun t d => applyRowDelta "id" d t) st.table ds) :=
    Kit.optionFoldl_agree
      (f := fun (st : AccState) (d : RowDelta accountFields) => accStep? d st)
      (plain := fun (t : List (RowVals accountFields))
          (d : RowDelta accountFields) => applyRowDelta "id" d t)
      (R := accStepAgreeR)
      (hstep := fun d st t st' hs hR => by
        cases d with
        | insert => simp [accStep?] at hs
        | remove => simp [accStep?] at hs
        | update r =>
            have h₁ : st' = { table := applyRowDelta "id" (RowDelta.update r)
                                st.table
                            , negs := negUpd st.table st.negs r } := by
              simpa [accStep?] using hs.symm
            subst h₁
            have hp' : List.Perm st.negs (negativeAccounts st.table) := by
              rw [hR.1]
              exact hR.2
            refine ⟨?_, ?_⟩
            · rw [hR.1]
            · rw [← hR.1]
              exact negUpd_agree st.table st.negs r hp')
      ds st st.table ⟨rfl, hp⟩
  intro st' hacc
  obtain ⟨ht, hp'⟩ := h st' hacc
  refine ⟨ht, ?_⟩
  rw [ht]
  exact hp'

/-! ## The dangling faces' maintained step (the join face, in-fragment) -/

/-- THE MAINTAINED JOIN FACE, per transfer delta, at ONE endpoint (the
    getter parameterization is Violate's `dangling_eq_nil_iff` shape —
    ONE step function, two faces). THE HONESTY BOUNDARY: the update arm
    returns `none` — a transfer rewrite can dangle a resolved row or
    resolve a dangling one at ANY endpoint (the fallback checker's
    face). Insert appends the row iff its endpoint misses the ids;
    remove drops the key-image's dangles. -/
def dangStep1? (ids : List UInt64) (get : RowVals transferFields → UInt64)
    (d : RowDelta transferFields)
    (dangs : List (RowVals transferFields)) :
    Option (List (RowVals transferFields)) :=
  match d with
  | .insert t => some (dangs ++ (if decide (get t ∈ ids) then [] else [t]))
  | .remove k => some (dangs.filter (fun o => !FieldVal.beq (trKey o) k))
  | .update _ => none

/-- The keyed application's remove arm, at the transfer key (a filter). -/
theorem applyRowDelta_remove_tid (k : FieldVal)
    (T : List (RowVals transferFields)) :
    applyRowDelta "tid" (RowDelta.remove k) T
      = List.filter (fun o => !FieldVal.beq (trKey o) k) T := by
  rw [applyRowDelta]
  exact List.filter_congr fun o _ => by rw [trKey_proj o]

/-- The join face's fold — Kit.Change's ONE poison-fold (`optionFoldl`)
    at the maintained join step (the DRY sweep; the first `none`
    poisons it). -/
def dangFold1? (ids : List UInt64) (get : RowVals transferFields → UInt64)
    (ds : List (RowDelta transferFields))
    (dangs : List (RowVals transferFields)) :
    Option (List (RowVals transferFields)) :=
  Kit.optionFoldl (fun dangs d => dangStep1? ids get d dangs) ds dangs

/-- THE JOIN FACE'S STEP AGREEMENT, insert arm (exact — the filter's
    append law: the new row is judged against the CURRENT ids). -/
theorem dangStep1_insert (ids : List UInt64)
    (get : RowVals transferFields → UInt64)
    (T dangs : List (RowVals transferFields)) (t : RowVals transferFields)
    (h : dangs = List.filter (fun u => !decide (get u ∈ ids)) T) :
    dangStep1? ids get (RowDelta.insert t) dangs
      = some (List.filter (fun u => !decide (get u ∈ ids)) (T ++ [t])) := by
  rw [dangStep1?, h, List.filter_append]
  cases hd : decide (get t ∈ ids) with
  | true => simp [hd]
  | false => simp [hd]

/-- THE JOIN FACE'S STEP AGREEMENT, remove arm (exact — the filters'
    commutation: dropping the removed key image's rows drops exactly its
    dangles). -/theorem dangStep1_remove (ids : List UInt64)
    (get : RowVals transferFields → UInt64)
    (T dangs : List (RowVals transferFields)) (k : FieldVal)
    (h : dangs = List.filter (fun u => !decide (get u ∈ ids)) T) :
    dangStep1? ids get (RowDelta.remove k) dangs
      = some (List.filter (fun u => !decide (get u ∈ ids))
          (List.filter (fun o => !FieldVal.beq (trKey o) k) T)) := by
  rw [dangStep1?, h, filter_filter_comm]

/-- THE FOLD'S ID STABILITY: a fold that returned `some` never left the
    fragment (every step was an update), so the id list is stable — the
    join faces' lease, fold-level. -/
theorem accFold_ids : ∀ (ds : List (RowDelta accountFields)) (st : AccState),
    ∀ st' : AccState, accFold? ds st = some st' →
      accIds st'.table = accIds st.table := by
  intro ds
  induction ds with
  | nil =>
      intro st st' hacc
      simp only [accFold?, Kit.optionFoldl, Option.some.injEq] at hacc
      subst hacc
      rfl
  | cons d rest ih =>
      intro st st' hacc
      simp only [accFold?, Kit.optionFoldl_cons] at hacc
      cases hd : accStep? d st with
      | none => simp [hd] at hacc
      | some st₁ =>
          simp only [hd] at hacc
          have hupd : accIds st₁.table = accIds st.table := by
            cases d with
            | insert => simp [accStep?] at hd
            | remove => simp [accStep?] at hd
            | update r =>
                have h₁ : st₁ = { table := applyRowDelta "id" (RowDelta.update r)
                                    st.table
                                , negs := negUpd st.table st.negs r } := by
                  simpa [accStep?] using hd.symm
                rw [h₁]
                exact accIds_stable_update r st.table
          exact (ih st₁ st' hacc).trans hupd

/-- THE JOIN FOLD'S AGREEMENT (the once-proof for every transfer-delta
    list in the fragment): the maintained face IS the recomputed face —
    exact, both are the endpoint's filter over the applied table. The
    induction is Kit.Change's `optionFoldl_agree` — `R` is the dangle
    filter's equality; the per-arm step agreements discharge `hstep`. -/
theorem dangFold1_agree (ids : List UInt64)
    (get : RowVals transferFields → UInt64) :
    ∀ (ds : List (RowDelta transferFields))
        (T dangs : List (RowVals transferFields)),
      dangs = List.filter (fun u => !decide (get u ∈ ids)) T →
      ∀ dangs' : List (RowVals transferFields),
        dangFold1? ids get ds dangs = some dangs' →
          dangs' = List.filter (fun u => !decide (get u ∈ ids))
              (List.foldl (fun t d => applyRowDelta "tid" d t) T ds) := by
  have hstep : ∀ (d : RowDelta transferFields)
      (dangs T dangs' : List (RowVals transferFields)),
      dangStep1? ids get d dangs = some dangs' →
      dangs = List.filter (fun u => !decide (get u ∈ ids)) T →
      dangs' = List.filter (fun u => !decide (get u ∈ ids))
        (applyRowDelta "tid" d T) := by
    intro d dangs T dangs' hs hR
    cases d with
    | insert t =>
        rw [dangStep1_insert ids get T dangs t hR] at hs
        rw [applyRowDelta_insert]
        exact Option.some.inj hs.symm
    | remove k =>
        rw [dangStep1_remove ids get T dangs k hR] at hs
        rw [applyRowDelta_remove_tid]
        exact Option.some.inj hs.symm
    | update t => simp [dangStep1?] at hs
  intro ds T dangs hR
  have h := Kit.optionFoldl_agree
    (f := fun (dangs : List (RowVals transferFields))
        (d : RowDelta transferFields) => dangStep1? ids get d dangs)
    (plain := fun (t : List (RowVals transferFields))
        (d : RowDelta transferFields) => applyRowDelta "tid" d t)
    (R := fun (dangs T : List (RowVals transferFields)) =>
      dangs = List.filter (fun u => !decide (get u ∈ ids)) T)
    hstep ds dangs T hR
  intro dangs' hf
  exact h dangs' hf

/-! ## THE INCREMENTAL VIOLATION CHECK -/

/-- The maintained path's assembly (the faces over the maintained
    state; the dup face — count-based, outside the linear fragment — is
    recomputed over the MAINTAINED id list: the named fallback face). -/
def incAssembly (db : Db) (d : Deltas) (ast : AccState) : List Violation :=
  match dangFold1? (accIds ast.table) trSrc d.transfers
      (danglingSrc db.transfers (accIds db.accounts)) with
  | none => violations (applyDeltas db d)
  | some dsF =>
      match dangFold1? (accIds ast.table) trDst d.transfers
          (danglingDst db.transfers (accIds db.accounts)) with
      | none => violations (applyDeltas db d)
      | some ddF =>
          (dupIds (accIds ast.table)).map Violation.dupId
            ++ ast.negs.map Violation.negative
            ++ dsF.map Violation.danglingSrc
            ++ ddF.map Violation.danglingDst

/-- THE INCREMENTAL VIOLATION CHECK (03 §8's maintained relation, at the
    slice's substrate): the faces fold the deltas from the delta + the
    old state; any `none` en route routes the WHOLE check to the
    fallback checker — the full post-state recomputation. Named, never
    silent. -/
def incViolations (db : Db) (d : Deltas) : List Violation :=
  match accFold? d.accounts ⟨db.accounts, negativeAccounts db.accounts⟩ with
  | none => violations (applyDeltas db d)
  | some ast => incAssembly db d ast

/-- THE AGREEMENT THEOREM (03 §8's "the foundation proves the
    incremental result equals full recomputation — ONCE", at the slice's
    size): the maintained relation IS the recomputed relation. The
    violation relation is a SET of diagnostics (02 §1) — the executable
    images agree up to `List.Perm`, and the verdict consumes only the
    emptiness (`incViolations_clean_iff`). -/
theorem incViolations_perm (db : Db) (d : Deltas) :
    List.Perm (incViolations db d) (violations (applyDeltas db d)) := by
  unfold incViolations
  split
  next => exact List.Perm.refl _
  next ast hacc =>
    unfold incAssembly
    split
    next => exact List.Perm.refl _
    next dsF hs =>
      split
      next => exact List.Perm.refl _
      next ddF hd =>
        obtain ⟨htab, hperm⟩ := accFold_agree d.accounts ⟨db.accounts,
          negativeAccounts db.accounts⟩ (List.Perm.refl _) ast hacc
        have hids : accIds ast.table = accIds db.accounts :=
          accFold_ids d.accounts ⟨db.accounts, negativeAccounts db.accounts⟩
            ast hacc
        have hsrc' : dsF = danglingSrc (d.transfers.foldl
              (fun acc x => applyRowDelta "tid" x acc) db.transfers)
            (accIds ast.table) := by
          rw [hids] at hs ⊢
          exact dangFold1_agree (accIds db.accounts) trSrc d.transfers db.transfers
            (danglingSrc db.transfers (accIds db.accounts)) rfl dsF hs
        have hdst' : ddF = danglingDst (d.transfers.foldl
              (fun acc x => applyRowDelta "tid" x acc) db.transfers)
            (accIds ast.table) := by
          rw [hids] at hd ⊢
          exact dangFold1_agree (accIds db.accounts) trDst d.transfers db.transfers
            (danglingDst db.transfers (accIds db.accounts)) rfl ddF hd
        have hrec : violations (applyDeltas db d)
            = (dupIds (accIds ast.table)).map Violation.dupId
              ++ (negativeAccounts ast.table).map Violation.negative
              ++ dsF.map Violation.danglingSrc
              ++ ddF.map Violation.danglingDst := by
          simp only [violations, applyDeltas, ← htab, ← hsrc', ← hdst']
        rw [hrec]
        exact List.Perm.append
          (List.Perm.append (List.Perm.append (List.Perm.refl _)
            (List.Perm.map _ hperm)) (List.Perm.refl _))
          (List.Perm.refl _)

/-- THE COMMIT GATE'S LAW (the sharp corollary): the incremental check's
    empty-result verdict IS the post-state check's. -/
theorem incViolations_clean_iff (db : Db) (d : Deltas) :
    incViolations db d = [] ↔ violations (applyDeltas db d) = [] := by
  constructor
  · intro h
    have hl := (incViolations_perm db d).length_eq
    rw [h, List.length_nil] at hl
    exact List.eq_nil_of_length_eq_zero hl.symm
  · intro h
    have hl := (incViolations_perm db d).length_eq
    rw [h, List.length_nil] at hl
    exact List.eq_nil_of_length_eq_zero hl

/-! ## The commit integration (the delta-driven check path) -/

/-- THE INCREMENTAL CHECK PATH: the delta-driven face of
    `Commit.checkDelta` (the post-state path) — the proposal's deltas
    are evaluated against the maintained faces, not by recomputing the
    post-state's relation from scratch. -/
def checkDeltaInc (db : Db) (p : Proposal) : List Violation :=
  incViolations db (p.deltas db)

/-- THE INCREMENTAL VERDICT (the same empty-result discipline). -/
def checkVerdictInc (db : Db) (p : Proposal) : Verdict :=
  match checkDeltaInc db p with
  | [] => .accept
  | vs => .refuse vs

/-- The incremental verdict's law (the verdict is the query's decision). -/
theorem checkVerdictInc_accept_iff (db : Db) (p : Proposal) :
    checkVerdictInc db p = .accept ↔ checkDeltaInc db p = [] := by
  unfold checkVerdictInc
  cases hq : checkDeltaInc db p with
  | nil => simp
  | cons v vs => simp

/-- THE TWO FACES AGREE (the relation): the delta-driven check's
    maintained relation IS the post-state check's recomputed relation. -/
theorem checkDeltaInc_perm (db : Db) (p : Proposal) :
    List.Perm (checkDeltaInc db p) (checkDelta db p) :=
  incViolations_perm db (p.deltas db)

/-- THE TWO FACES AGREE (the verdict): the incremental path accepts iff
    the post-state path accepts — the two faces' verdicts coincide BY
    PROOF; the tests exercise both. -/
theorem checkVerdictInc_agree (db : Db) (p : Proposal) :
    checkVerdictInc db p = .accept ↔ checkVerdict db p = .accept := by
  rw [checkVerdictInc_accept_iff, checkVerdict_accept_iff]
  exact incViolations_clean_iff db (p.deltas db)

end SchemaCore
