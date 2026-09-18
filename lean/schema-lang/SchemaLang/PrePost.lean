/-
# SchemaLang.PrePost — pre/postconditions as first-class obligations (W8.9)

The order (the dispatch board's W8.9 = pre/postconditions; the runbook's
Wave-8 lane text "Pre/post on `@[schema_fn]` — VExpr over params+result
as obligations"): a pre-condition is an obligation at the CALLER's tier
(the boundary check refuses calls whose inputs fail it); a
post-condition is an obligation at the FUNCTION's tier (discharged by
proof/generation/oracle per the ladder).

NO new concept — the module composes the existing pieces:

- the Validate predicate layer (`VExpr`/`validates`) — both sides are
  schema-indexed predicates, GADT-typed at the record's field list;
- the Invariant tier machinery (`Invariant.Tier`'s ladder +
  `tierOf`'s computed rungs) — the post's tier is COMPUTED from the
  citation, never hand-set;
- the obligation view (W7.1's `CodegenCore.Obligation` at the
  `Update2Obligation`/`SchemaObligation` shape) — the tier is a
  BACKEND ASSIGNMENT, `discharge`'s `none` is the loud gap;
- the Error lane (W6.11's check-eliminates-error discipline) — the
  caller's boundary check is EXACT (proved both directions) and the
  refusal is TYPED and LOUD (the verdict names the failed contract).

## The tier story, per side

- PRE → `.generatedCheck` (the caller's boundary rung): the caller runs
  `validates contract.pre` BEFORE the call; failure = `.refusedPre`
  carrying the contract's name — a typed refusal in the Error lane's
  shape, never a silent misfire. Exactness (the iff) is proved and the
  check packs as a `CodegenCore.CheckedProp` with `.proved`
  completeness. Discharge evidence names the caller-boundary route.
- POST → the function's tier, computed by the ladder: a cited
  correctness theorem (`postProof?`) → `.provedAtElab`, discharged to
  `.citedProof`; uncited → `.decidableNow`, discharged by the kernel's
  `decide` over the pinned all-default-row verdict (the default-row
  discipline — the ONE row the lane materializes from the declaration
  alone; a false verdict is `none`, the loud gap). The `oracleSwept`/
  `guestVerified` rungs have no pre/post-lane source (closed ctors) —
  their discharge is `none` until a backend lands.

The POST's correctness story: a body that writes NONE of the post's
columns PRESERVES the post on every kept result row
(`ContractOp.post_preserved_of_neutral` — Update2's `evalB_applySets`
neutrality law does the work). The fixture's contract (pre = post =
`age > 0`, an email-only write) is the preservation instance.

Ownership: the W8.9 pre/post lane (this module; the Meta/ command half
— attaching contracts to `@[schema_fn]` signatures at registration —
is the follow-up, the `checkCitation?` resolver rides it).
Deliberate exclusions: NO emitter registration (the caller-boundary
check's Rust text is a def route, not a `GenCtx` job — the byte-tie
holds by construction, the `Meta.Keys`/EntityMachine hook pattern); no
two-row posts (a post reading BOTH the pre-row and the result-row needs
a name-disjoint concat surface — the current post reads the result row,
and pre-row facts reach it through the update's own neutrality laws);
no contract REGISTRY (the enumeration is per-op data; the registry
lane lands with the Meta/ half).
-/

module

public import SchemaLang.Validate
public import SchemaLang.Update2
public import CodegenCore

@[expose] public section

namespace SchemaLang

/-! ## The contract -/

/-- A named pre/post contract on operations over the record `fs`.
    `pre` reads the CALL's input row (the params); `post` reads the
    RESULT row. `postProof?` is the proved-tier citation — `some`
    exactly on `.provedAtElab` rows (the `InvariantItem.proofName`
    shape; the Meta/ half resolves the name at registration). -/
structure FnContract (fs : List Field) where
  name : String
  pre : VExpr fs .bool
  post : VExpr fs .bool
  postProof? : Option Lean.Name := none

/-! ## The caller's boundary — the typed refusal -/

/-- The call's verdict. `refusedPre` is the TYPED refusal: the caller's
    boundary check failed, and the verdict NAMES the contract whose
    pre was violated (loud — never a silent misfire). -/
inductive CallVerdict (fs : List Field) where
  | accepted (rows : List (RowVals fs))
  | refusedPre (label : String)

/-- Accepted? -/
def CallVerdict.isAccepted : CallVerdict fs → Bool
  | .accepted _ => true
  | .refusedPre _ => false

/-- The refusal's loud half: the failed contract's name (`none` =
    accepted). -/
def CallVerdict.refusal? : CallVerdict fs → Option String
  | .accepted _ => none
  | .refusedPre l => some l

/-- The accepted result rows (`none` = refused). -/
def CallVerdict.rows? : CallVerdict fs → Option (List (RowVals fs))
  | .accepted rows => some rows
  | .refusedPre _ => none

/-- A pre/post contract ATTACHED to a body: the operation the contract
    governs. The body is a keyed v2 update (W8.3) — the function's
    implementation; the contract's pre/post are the obligations riding
    it. -/
structure ContractOp (fs : List Field) where
  contract : FnContract fs
  body : Update2Item fs

/-- THE CALL: the caller's boundary check runs FIRST — a pre-satisfying
    input row proceeds to the body (applied to the singleton table);
    a failing row is REFUSED with the contract's name. The body's own
    guard is independent (rows it refuses pass through unchanged —
    the update's batch law). -/
def ContractOp.run (op : ContractOp fs) (r : RowVals fs) : CallVerdict fs :=
  if validates op.contract.pre r = true then
    .accepted (op.body.apply [r])
  else .refusedPre op.contract.name

/-- The accepted direction: a pre-satisfying row is accepted, with the
    body's table effect as the result. -/
theorem ContractOp.run_accepted_of_pre (op : ContractOp fs) (r : RowVals fs)
    (h : validates op.contract.pre r = true) :
    op.run r = .accepted (op.body.apply [r]) := by
  unfold ContractOp.run
  rw [if_pos h]

/-- The refusal direction: a pre-failing row is refused LOUDLY — the
    verdict carries the contract's own name. -/
theorem ContractOp.run_refused_of_pre_false (op : ContractOp fs) (r : RowVals fs)
    (h : validates op.contract.pre r = false) :
    op.run r = .refusedPre op.contract.name := by
  unfold ContractOp.run
  rw [if_neg (by simp [h])]

/-- EXACTNESS (the W6.11 discipline, both directions): the boundary
    check refuses IFF the pre fails — no silent misfire in either
    direction. -/
theorem ContractOp.refuses_iff_pre_fails (op : ContractOp fs) (r : RowVals fs) :
    ((op.run r).refusal?).isSome = true ↔ validates op.contract.pre r = false := by
  unfold ContractOp.run
  split
  · simp_all [CallVerdict.refusal?]
  · simp_all [CallVerdict.refusal?]

/-- The refusal is LOUD: a refused call's verdict names the contract. -/
theorem ContractOp.refusal_names_contract (op : ContractOp fs) (r : RowVals fs)
    (h : ((op.run r).refusal?).isSome = true) :
    (op.run r).refusal? = some op.contract.name := by
  cases hp : validates op.contract.pre r with
  | false =>
      rw [ContractOp.run_refused_of_pre_false op r hp]
      rfl
  | true =>
      rw [ContractOp.run_accepted_of_pre op r hp, CallVerdict.refusal?] at h
      simp [Option.isSome] at h

/-- The boundary check, packed (the canon's CheckedProp row): P =
    "the call is accepted", check = the pre's verdict, completeness
    PROVED (the exactness above — a two-directional gate, declared). -/
def ContractOp.admission (op : ContractOp fs) :
    CodegenCore.CheckedProp (RowVals fs) :=
  CodegenCore.CheckedProp.ofComplete
    (fun r => (op.run r).isAccepted = true)
    (fun r => validates op.contract.pre r)
    (fun r h => by
      rw [ContractOp.run_accepted_of_pre op r h]
      rfl)
    (fun r h => by
      cases hp : validates op.contract.pre r with
      | true => rfl
      | false =>
          rw [ContractOp.run_refused_of_pre_false op r hp] at h
          simp [CallVerdict.isAccepted] at h)

/-! ## The post = the contract the correctness story cites -/

/-- THE CORRECTNESS STORY: the post is the fact the op's correctness
    proof cites. The general law — a body that writes NONE of the
    post's columns PRESERVES the post on every kept result row (the
    refused pass-through keeps the original row; a delete removes it —
    nothing left to satisfy). Update2's `evalB_applySets` neutrality
    law does the work. -/
theorem ContractOp.post_preserved_of_neutral (op : ContractOp fs)
    (hne : ∀ c ∈ op.body.sets, c.field.name ∉ op.contract.post.reads)
    (r : RowVals fs) (h : validates op.contract.post r = true)
    (new : RowVals fs) (hk : op.body.keepRow r = some new) :
    validates op.contract.post new = true := by
  unfold Update2Item.keepRow at hk
  split at hk
  · -- the body's guard fires
    split at hk
    · simp at hk -- a delete removes the row: nothing to satisfy
    · -- not a delete: the result is the write fold — the post's
      -- columns are untouched, the verdict carries
      have hval : validates op.contract.post (applySets op.body.sets r)
          = validates op.contract.post r := by
        show (evalB op.contract.post (applySets op.body.sets r) == 1)
          = (evalB op.contract.post r == 1)
        rw [evalB_applySets op.contract.post hne r]
      rw [← Option.some.inj hk, hval]
      exact h
  · -- the guard refuses: the row passes through untouched
    rw [← Option.some.inj hk]
    exact h

/-! ## The obligation view (W7.1's substrate, the keys-lane shape) -/

/-- The fact a contract records: the pre at the CALLER's tier, the
    post at the FUNCTION's tier. Both ride the op (the post's verdict
    is about the body's result). -/
inductive PrePostClaim where
  | pre (fs : List Field) (op : ContractOp fs)
  | post (fs : List Field) (op : ContractOp fs)

/-- The pre/post lane's obligation (`abbrev` — reducible, the kit
    discipline). -/
abbrev PrePostObligation := CodegenCore.Obligation PrePostClaim

/-- The claim's label (the enumeration's handle). -/
def PrePostClaim.claimName : PrePostClaim → String
  | .pre _ op => op.contract.name
  | .post _ op => op.contract.name

/-- THE TIER COMPUTATION (the `Invariant.tierOf` discipline — computed,
    never hand-set):
    - pre → `.generatedCheck`: the CALLER's boundary rung — the check
      the caller runs refuses calls whose inputs fail it;
    - post with a citation → `.provedAtElab` (the cited correctness
      theorem);
    - uncited post → `.decidableNow` (the pinned default-row verdict). -/
def PrePostClaim.tierOf : PrePostClaim → CodegenCore.Obligation.Tier
  | .pre _ _ => .generatedCheck
  | .post _ op =>
      match op.contract.postProof? with
      | some _ => .provedAtElab
      | none => .decidableNow

/-- The proved tier's citation (the discharge reads it). -/
def PrePostClaim.citedProof? : PrePostClaim → Option Lean.Name
  | .pre _ _ => none
  | .post _ op => op.contract.postProof?

/-- The caller-boundary route the pre's discharge names (the
    EntityMachine hook pattern: the check's Rust text is a def route,
    not a `GenCtx` job — the byte-tie holds by construction; the
    emitter wiring is the Meta-half follow-up). -/
def callerBoundaryArtifact : String := "caller-boundary"

/-- The label is side-tagged: `-pre` for the caller's row, `-post` for
    the function's (the enumeration distinguishes the two). -/
def PrePostClaim.label (c : PrePostClaim) : String :=
  match c with
  | .pre _ _ => s!"{c.claimName}-pre"
  | .post _ _ => s!"{c.claimName}-post"

/-- The obligation VIEW of one claim (the `Update2Item.obligations`
    shape: additive — nothing the emitters read changes). -/
def PrePostClaim.mkObligation (c : PrePostClaim) : PrePostObligation :=
  { label := c.label
  , tier := c.tierOf
  , payload := c
  , provenance := c.claimName.toName }

/-- THE ENUMERATION: a contract op carries exactly TWO obligations —
    the pre (the caller's boundary row) and the post (the function's
    row). -/
def ContractOp.obligations (op : ContractOp fs) : List PrePostObligation :=
  [PrePostClaim.pre fs op |>.mkObligation, PrePostClaim.post fs op |>.mkObligation]

/-! ### The decidableNow backend (the uncited post's rung) -/

/-- The decidableNow CLAIM at the pre/post lane: on the pinned
    all-default row (the default-row discipline — the ONE row the lane
    materializes from the declaration alone), IF the pre admits the
    call THEN the kept result row satisfies the post. A pre-refused or
    removed default row is vacuous (the `Update2Obligation` discipline
    — the antecedent keeps vacuous contracts honest while still
    exercising the wiring); a record with no default row has NO row to
    pin — the claim is `False`, the backend refuses (loud). -/
def PrePostObligation.decidableClaim (o : PrePostObligation) : Prop :=
  match o.payload with
  | .pre _ _ => True
  | .post fs op =>
      match SchemaLang.defaultRow? fs with
      | some row =>
          (if validates op.contract.pre row then
              match op.body.keepRow row with
              | some new => validates op.contract.post new
              | none => true
            else true) = true
      | none => False

/-- The claim IS decidable: the pinned row reduces it to Bool
    equations over computed rows (named explicitly — the
    `update2ClaimDecidable` precedent: anonymous-instance auto-names
    collide cross-module). -/
instance prePostClaimDecidable (o : PrePostObligation) :
    Decidable o.decidableClaim := by
  unfold PrePostObligation.decidableClaim
  cases hp : o.payload with
  | pre fs op => exact inferInstanceAs (Decidable True)
  | post fs op =>
      show Decidable (match SchemaLang.defaultRow? fs with
        | some row =>
            (if validates op.contract.pre row then
                match op.body.keepRow row with
                | some new => validates op.contract.post new
                | none => true
              else true) = true
        | none => False)
      cases hd : SchemaLang.defaultRow? fs <;> infer_instance

/-- THE DISCHARGE (the tier is a backend assignment; the match reads
    the tier — the `SchemaObligation` shape):
    - `.generatedCheck` (the pre's caller-boundary rung): the evidence
      is the boundary check itself, at the lane's declared route;
    - `.provedAtElab`: the cited correctness theorem (resolved at
      registration by the Meta/ half — a citation-less proved row
      refuses, the loud gap);
    - `.decidableNow`: the kernel's `decide` over `decidableClaim` —
      `.decided true` on a true claim, `none` on a false one (the loud
      gap: the backend refuses, it does not fabricate evidence);
    - `.oracleSwept`/`.guestVerified`: no pre/post-lane source (closed
      ctors) — `none` until a backend lands. -/
def PrePostObligation.discharge (o : PrePostObligation) :
    Option CodegenCore.Obligation.Evidence :=
  match o.tier with
  | .generatedCheck =>
      some (.generatedCheck callerBoundaryArtifact o.payload.claimName)
  | .provedAtElab => o.payload.citedProof?.map .citedProof
  | .decidableNow =>
      match decide o.decidableClaim with
      | true => some (.decided true)
      | false => none
  | .oracleSwept | .guestVerified => none

/-- SOUNDNESS of the decidableNow backend: a `.decided true` verdict
    means the claim HOLDS (the kernel's `decide` validated the pinned
    default-row fact — `of_decide_eq_true`; no new trust base). The
    evidence ctor's own tier is `.decidableNow` — the shape match
    already forces the rung (no mis-wiring by construction); the
    hypothesis keeps the ladder discipline explicit. -/
theorem PrePostObligation.discharge_decidableNow_sound (o : PrePostObligation)
    (ht : o.tier = .decidableNow)
    (h : o.discharge = some (.decided true)) : o.decidableClaim := by
  unfold PrePostObligation.discharge at h
  rw [ht] at h
  cases hd : decide o.decidableClaim with
  | true => exact of_decide_eq_true hd
  | false =>
      rw [hd] at h
      simp at h

/-- COMPLETENESS: a true claim discharges to the `.decided true`
    evidence — the backend FIRES on the claims it can decide. -/
theorem PrePostObligation.discharge_decidableNow_of_claim (o : PrePostObligation)
    (ht : o.tier = .decidableNow) (h : o.decidableClaim) :
    o.discharge = some (.decided true) := by
  unfold PrePostObligation.discharge
  rw [ht, decide_eq_true h]

/-- The pre's obligation ALWAYS discharges (the caller-boundary rung's
    evidence is the check itself — the tier's `isSome` is not vacuous). -/
theorem PrePostObligation.discharge_pre_isSome (fs : List Field) (op : ContractOp fs) :
    ((PrePostClaim.pre fs op).mkObligation.discharge).isSome = true := rfl

/-- The cited post's discharge IS the citation (the proved rung's
    evidence). -/
theorem PrePostObligation.discharge_post_proved (fs : List Field)
    (op : ContractOp fs) (pn : Lean.Name)
    (hc : op.contract.postProof? = some pn) :
    (PrePostClaim.post fs op).mkObligation.discharge = some (.citedProof pn) := by
  have ht : (PrePostClaim.post fs op).tierOf = .provedAtElab := by
    simp [PrePostClaim.tierOf, hc]
  simp [PrePostClaim.mkObligation, PrePostObligation.discharge, ht,
    PrePostClaim.citedProof?, hc]

end SchemaLang
