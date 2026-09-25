/-
# Guest.Effects — the effects lane's integration (the compiled functions carry effect rows)

The guest compiler's effect-row integration (notes/v3/08-capabilities.md
§8, the LANDED effects lane's first GUEST consumer): the compiler
DERIVES each function's effect row from the function's content — the
honest first cut — and the boundary check refuses an over-claimed
purity (the discipline: a function declared pure that touches memory
fails the check).

The honest level (judged): the LCNF `Code .impure` — the SAME data
`Guest.Lower` folds, BEFORE the lowering (a row derived from the
emitted wasm would need to read the instructions back; the LCNF's
constructs ARE the registry items, and the derivation is a fold over
them — 08 §8's discipline: rows derive from registry items, never
hand-written).

The construct → effect mapping (the honest first cut, keyed to
`Guest.Lower`'s fragment):

- the PURE arithmetic (the scalar literals, the copies, the `binop?`
  faps, the boxed-Nat compares, the scalar-face ctor value, the Bool/
  UInt8/scalar-enum cases riding the VALUE branch) → the EMPTY row (a
  pure scalar function is the empty row — the pin);
- the MEMORY-touching constructs → `read` + `write`: the bump-arena
  ALLOCATORS (the Nat boxes, the Nat arith's fresh boxes, the object
  ctors, the pap closures, the scalar `box`) read the bump pointer
  cell and write it + the object's cells; the RC ops (`inc`/`dec`)
  read and write the rc cell; the field/payload READS (`sproj`,
  `oproj`, `unbox`) and the object tag dispatch's tag read carry
  `read`;
- the UNMODELED constructs (the refused forms — `oset`/`uset`/`sset`/
  `setTag`/`del`/`proj`/`uproj`/reset-reuse, the local `fun` values,
  the string/usize literals) and every CALLEE OUTSIDE THE LOCAL FOLD
  (a cross-decl call, a closure application, a `const` — the callee's
  row is not derivable from one decl's code; the multi-decl fixpoint
  is the named follow-up) carry the honest OVER-APPROXIMATION: the
  top row (every atom — the construct COULD do anything, so the
  derivation claims everything). The derivation is thus TOTAL — it
  never throws (a refusal is the lowering's job; an over-approximation
  is the derivation's).

The boundary check (`verdictOf`/`enforce`): a function's DECLARED row
vs the derived row — `derived ≤ declared` is the discipline (the
sub-effect order, `Effects.Row.le`). An over-claim (declared purer
than derived) REFUSES with the named diagnostic (`EffectError.
overClaim`, the GC-family E-code GC2023 — a NEW closed vocabulary,
not `LowerError`'s: `Lower.lean`'s existing content is not this
slice's). An under-claim (declared strictly more permissive) is
HONEST but REPORTED — the verdict carries the slack.

The obligation rows: per function, the Prop-indexed claim that the
declared allowance covers the derived row (`Obligation` — discharged
by `decide`; a false obligation is unprovable, the over-claim's face
at rung 1), and the computed manifest (`obligationRows` — one row per
function: derived + declared + verdict, never hand-written).

The footprint discipline's first consumer (`fpOf`): the functions'
FOOTPRINTS — which state (which memory-layout regions) the function
touches — computed over the SAME fold, keyed as `Effects.Fp` keys
(the layout-region keys: the bump pointer cell, the rc cells, the tag
cells, the payload slots, the field slots), joined by the SAME
`Effects.Fp.join` set-union discipline. The keys are LAYOUT REGIONS,
not addresses (addresses are dynamic under the bump arena — the
model's honest note); the `Effects.Footprint.Cmd` LAW face
(reads_depend/writes_depend/the frame rule over these keys) lands
with the memory-model semantics (the named follow-up).

Doctrine slots (notes/v3/01-core.md, the five questions):

- **Root**: none — a derivation is a FOLD over the LCNF registry
  items (the rows derive; nothing is hand-written).
- **Carrier grade**: none new — the verdicts/refusals ride closed
  inductives + `Kit.Diag` (the ONE envelope).
- **Spine reading**: the LCNF `Code` is the spine this module folds
  (ONE traversal — `deriveCode` — producing the row AND the footprint:
  the ONE-walk discipline, `Guest.Lower`'s pattern).
- **Ladder rung**: rung 1 (the obligation is unprovable when false —
  the over-claim's face) + rung 6 (the boundary check's law: the
  refused verdict is EXACTLY the over-claim, soundness AND
  completeness).
- **Gate row**: `gates kernel-check` (the module is gated source) +
  the axiom report's Guest section (the derivation's pure faces are
  pinned in GuestTests.Axioms).

Host-side (imports Lean via Guest.Lower); the guest lane is C2/host —
Effects (C1-adjacent) is a legal import direction (cone-high may ride
cone-low).
-/

import Guest.Lower
import Effects
import Kit.Diag
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

open Effects Lean Compiler.LCNF

namespace Guest.Effects

/-! ## The rows' faces (the honest first cut's constants) -/

/-- THE over-approximation row: every atom. An unmodeled construct or
    a callee outside the local fold COULD do anything — the derivation
    claims everything (the honest over-approximation; 08 §8). -/
def rowTop : Effects.Row :=
  [Effect.read, Effect.write, Effect.guestCap, Effect.fail,
   Effect.consume, Effect.clock, Effect.hostIO, Effect.observe]

/-- The row's one-line render (the diagnostic's got face; `Effect`'s
    derived Repr, never a hand-parsed spelling). -/
def renderRow (r : Effects.Row) : String := toString (repr r)

/-! ## The footprint keys (the layout regions — the honest model) -/

/-- THE layout-region keys (the footprint's honest model): the guest
    module's linear memory is touched through exactly five layout
    FACES — the bump pointer cell, the rc cells, the tag cells, the
    payload slots, the field slots. A key is a REGION, not an address
    (addresses are dynamic under the bump arena — the model's honest
    note; per-address footprints are the named follow-up). -/
def fpBump : Effects.Key := 0
@[nolint linter.guestlang.dupDefBodies "the rc cell's key is its own layout-region row — a shared numeric value with unrelated constants is coincidence, not duplication"]
def fpRc : Effects.Key := 1
@[nolint linter.guestlang.dupDefBodies "the tag cell's key is its own layout-region row — a shared numeric value with unrelated constants is coincidence, not duplication"]
def fpTag : Effects.Key := 2
@[nolint linter.guestlang.dupDefBodies "the payload slot's key is its own layout-region row — a shared numeric value with unrelated constants is coincidence, not duplication"]
def fpPayload : Effects.Key := 3
@[nolint linter.guestlang.dupDefBodies "the field slot's key is its own layout-region row — a shared numeric value with unrelated constants is coincidence, not duplication"]
def fpField : Effects.Key := 4

/-- The footprint's over-approximation (every region) — the top
    construct's footprint face. -/
def fpTop : Effects.Fp := [fpBump, fpRc, fpTag, fpPayload, fpField]

/-! ## The per-construct derivation (the row AND the footprint) -/

/-- One construct's derivation: the effect row + the footprint keys —
    ONE pair, the same dispatch the lowering makes. -/
structure Deriv where
  /-- The effect row. -/
  row : Effects.Row
  /-- The footprint keys (the layout regions touched). -/
  fp : Effects.Fp

/-- The join: both faces join (the set-union discipline — one
    mechanism, `Effects.unionMem`, two instances). -/
def Deriv.join (a b : Deriv) : Deriv :=
  ⟨Effects.Row.join a.row b.row, Effects.Fp.join a.fp b.fp⟩

/-- The pure face: the empty row, the empty footprint. -/
def derivPure : Deriv := ⟨[], []⟩

/-- The allocation face: the bump-arena allocator READS the bump
    pointer cell and WRITES it + the object's cells (rc, tag, body).
    `fpBody` = the object's body region key (a payload slot for a box,
    a field slot for a ctor/closure object). -/
def derivAlloc (fpBody : Effects.Key) : Deriv :=
  ⟨[Effect.read, Effect.write], [fpBump, fpRc, fpTag, fpBody]⟩

/-- The RC-op face (`inc`/`dec`): the rc cell's read + write. -/
def derivRc : Deriv := ⟨[Effect.read, Effect.write], [fpRc]⟩

/-- The read faces: the field/payload loads + the object tag
    dispatch's tag read. -/
def derivReadField : Deriv := ⟨[Effect.read], [fpField]⟩
@[nolint linter.guestlang.dupDefBodies "the payload-read face is its own derivation row (a payload slot is not a field slot — the layout regions are distinct keys) — the shared row VALUE is the honest read effect, not duplication"]
def derivReadPayload : Deriv := ⟨[Effect.read], [fpPayload]⟩
@[nolint linter.guestlang.dupDefBodies "the tag-read face is its own derivation row (the dispatch's tag cell is not a field slot) — the shared row VALUE is the honest read effect, not duplication"]
def derivTagRead : Deriv := ⟨[Effect.read], [fpTag]⟩

/-- The top face: the honest over-approximation, both faces. -/
def derivTop : Deriv := ⟨rowTop, fpTop⟩

/-! ## The fold's context (the scrutinee-class lookup) -/

/-- The fold's type context: the fvar → the LEAN type's const name
    (`none` for a non-const type) — the `cases` dispatch's key (the
    SAME lookup the lowering's type map makes: a Bool/UInt8/scalar-
    enum scrutinee branches on the VALUE — no memory; an object-
    typed scrutinee reads the tag cell). -/
abbrev TyCtx := Std.HashMap Lean.FVarId (Option Lean.Name)

/-! ## The let-value forms (the SAME dispatch order as `emitLet`) -/

/-- The `let` value form's derivation: the fragment's constructs map
    to their effects (the honest first cut — see the module header). -/
def deriveLet (decl : LetDecl .impure) : Deriv :=
  match decl.value with
  | .lit (.uint64 _) | .lit (.uint32 _) | .lit (.uint8 _) => derivPure
  | .lit (.nat _) => derivAlloc fpPayload      -- the bump-arena box
  | .lit _ => derivTop                          -- str/usize lits: unmodeled
  | .erased => derivPure
  | .fvar _ args =>                             -- the copy / the closure application
      if args.isEmpty then derivPure else derivTop
  | .fap fn _ =>
      match natFap? fn with
      | some .decEq | some .beq | some .decLt | some .decLe => derivPure
      | some .add | some .sub | some .mul => derivAlloc fpPayload
      | none =>
          if (binop? fn).isSome then derivPure
          else derivTop     -- the call lane: the callee's row is not locally derivable
  | .ctor _ _ =>
      if objectRowName ((tyName? decl.type).getD `anon) then
        derivAlloc fpField   -- the object face: the {rc, tag, fields} allocation
      else
        derivPure            -- the tag face: a scalar-row ctor's value IS the tag
  | .pap _ _ => derivAlloc fpField          -- the closure object's allocation
  | .sproj .. => derivReadField
  | .oproj .. => derivReadField
  | .proj .. | .uproj .. => derivTop        -- the non-scalar payload shapes: refused
  | .box ty .. =>
      if objectRowName ((tyName? ty).getD `anon) then
        derivPure            -- the object-row box: the IDENTITY copy (the value IS the box)
      else
        derivAlloc fpPayload -- the boxed scalar's allocation
  | .unbox .. => derivReadPayload
  | .reset .. | .reuse .. | .isShared .. => derivTop
  | .const .. => derivTop                   -- the callee's row is not locally derivable

/-! ## The ONE walk (the row AND the footprint, one traversal) -/

/-! The ONE derivation walk over the LCNF `Code` (the same spine
`Guest.Lower` folds; well-founded over the SAME measures
`Guest.codeSize`/`Guest.altSizes` — cited, never re-proven). The type
context threads the let/jp bindings so the `cases` dispatch sees each
scrutinee's class: a SCALAR-repr scrutinee (Bool/UInt8/the prescan's
enums) branches on the VALUE — no memory; an object-typed scrutinee
(or an untracked one — the honest over-approximation) reads the tag
cell. The walk is TOTAL — the unmodeled constructs over-approximate,
they never throw. This is the module's spine: ONE traversal produces
the row AND the footprint. -/
mutual
def deriveCode (enums : Std.HashMap Lean.Name Unit) (tys : TyCtx)
    (code : Code .impure) : Deriv :=
  match code with
  | .let decl k =>
      (deriveLet decl).join
        (deriveCode enums (tys.insert decl.fvarId (tyName? decl.type)) k)
  | .jp fd k =>
      let tysP := fd.params.foldl
        (fun m p => m.insert p.fvarId (tyName? p.type)) tys
      (deriveCode enums tysP fd.value).join (deriveCode enums tys k)
  | .cases c =>
      let head : Deriv :=
        match tys[c.discr]? with
        | some (some n) =>
            if n == `Bool || n == `UInt8 || enums.contains n then derivPure
            else derivTagRead
        | _ => derivTagRead
      head.join (deriveAlts enums tys c.alts 0)
  | .return _ | .jmp .. | .unreach _ => derivPure
  | .fun .. => derivTop
  | .oset .. | .uset .. | .sset .. | .setTag .. => derivTop
  | .inc _ _ _ _ k _ => derivRc.join (deriveCode enums tys k)
  | .dec _ _ _ _ objs? k =>
      (match objs? with
      | none => derivRc        -- the rc cell's read + write
      | some _ => derivTop)    -- the field-cascade dec: refused (unmodeled)
        |>.join (deriveCode enums tys k)
  | .del .. => derivTop
  termination_by codeSize code
  decreasing_by all_goals (simp only [codeSize]; omega)
def deriveAlts (enums : Std.HashMap Lean.Name Unit) (tys : TyCtx)
    (alts : Array (Alt .impure)) (i : Nat) : Deriv :=
  if h : i < alts.size then
    match hget : alts[i] with
    | .ctorAlt _ code => (deriveCode enums tys code).join (deriveAlts enums tys alts (i + 1))
    | .default code => (deriveCode enums tys code).join (deriveAlts enums tys alts (i + 1))
    | .alt _ _ _ hp => absurd hp (by simp)
  else
    derivPure
  termination_by altSizes alts i
  decreasing_by
    all_goals (first
      | exact altSizes_suffix alts i h
      | exact altSizes_gt_ctor alts i h _ _ hget
      | exact altSizes_gt_default alts i h _ hget
      | omega)
end

/-- THE derivation (08 §8's discipline: the row derives from the
    registry item — the LCNF decl IS the registry item, the walk the
    derivation): the decl's effect row + its footprint keys, computed,
    never hand-written. The prescan's enum registry rides the SAME
    call the lowering makes (`Guest.collectScalarEnums`); an `extern`
    decl (no body) is the honest top (unmodeled). -/
def derive (d : Decl .impure) : Deriv :=
  match d.value with
  | .code c => deriveCode (collectScalarEnums c) {} c
  | .extern .. => derivTop

/-- The decl's derived effect row. -/
def rowOf (d : Decl .impure) : Effects.Row := (derive d).row

/-- The decl's derived footprint (the layout regions the function
    touches — the footprint discipline's first consumer, 08 §8). -/
def fpOf (d : Decl .impure) : Effects.Fp := (derive d).fp

/-! ## The boundary check (the declared vs the derived) -/

/-- The row difference `a ∖ b` (membership-wise; the over-claim's
    evidence is `der ∖ declared`, the slack is `declared ∖ der`). -/
def rowDiff (a b : Effects.Row) : Effects.Row :=
  a.filter (fun e => !Effects.Row.memB e b)

@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `rowDiff_nil_iff_le` in this module (the boundary check's law face) + cited by GuestTests.Deriv (the derivation's pins)"]
theorem rowDiff_mem {e : Effect} {a b : Effects.Row} :
    e ∈ rowDiff a b ↔ e ∈ a ∧ e ∉ b := by
  simp only [rowDiff, List.mem_filter]
  constructor
  · rintro ⟨hm, hp⟩
    refine ⟨hm, fun hin => ?_⟩
    have hb : Effects.Row.memB e b = true := (Effects.Row.memB_iff e b).mpr hin
    rw [hb] at hp
    simp at hp
  · rintro ⟨hm, hn⟩
    refine ⟨hm, ?_⟩
    show (!Effects.Row.memB e b) = true
    cases hb : Effects.Row.memB e b with
    | false => rfl
    | true => exact absurd ((Effects.Row.memB_iff e b).mp hb) hn

/-- THE boundary check's law: the difference is empty exactly when the
    sub-effect discipline holds (`Effects.Row.le` — the order's
    membership reading, cited). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by the verdict laws (`verdict_over_refuses`/`verdict_not_le_refuses`/`verdict_le_of_not_refused`) in this module + cited by GuestTests.Deriv"]
theorem rowDiff_nil_iff_le (a b : Effects.Row) :
    rowDiff a b = [] ↔ Effects.Row.le a b := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h e he
    by_cases hb : e ∈ b
    · exact hb
    · exact absurd (rowDiff_mem.mpr ⟨he, hb⟩) (h e)
  · intro h e he
    have ⟨_, hn⟩ := rowDiff_mem.mp he
    exact hn (h e (rowDiff_mem.mp he).1)

/-- The boundary verdict: the check's closed vocabulary. `covered` —
    the derived row is below the declared, no slack; `coveredWithSlack`
    — the under-claim (honest, REPORTED: the slack names the unused
    allowance); `refused` — the over-claim (the leaked row names the
    effects the declaration HIDES). -/
inductive RowVerdict where
  | covered
  | coveredWithSlack (slack : Effects.Row)
  | refused (leaked : Effects.Row)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The verdict's computation: the over-claim refuses; the under-claim
    passes but reports the slack; the exact match covers. -/
def verdictOf (declared der : Effects.Row) : RowVerdict :=
  if rowDiff der declared = [] then
    if rowDiff declared der = [] then .covered
    else .coveredWithSlack (rowDiff declared der)
  else
    .refused (rowDiff der declared)

/-- THE obligation row: per function, the Prop-indexed claim that the
    declared allowance covers the derived row (the check's PROOF face
    — discharged by `decide` at the declaration site; a false
    obligation is unprovable, the over-claim's face at rung 1). -/
abbrev Obligation (declared : Effects.Row) (d : Decl .impure) : Prop :=
  Effects.Row.le (rowOf d) declared

/-- THE obligation rows: the per-function manifest, COMPUTED from the
    decls (never hand-written) — one row per function carrying the
    derived row, the declared allowance, and the verdict. -/
structure ObligationRow where
  fn : Lean.Name
  derived : Effects.Row
  declared : Effects.Row
  verdict : RowVerdict
  deriving Repr, BEq, Inhabited

/-- The manifest fold (the caller supplies the declared allowances —
    the registry's rows; the derivation supplies everything else). -/
def obligationRows (declaredOf : Lean.Name → Effects.Row)
    (ds : List (Decl .impure)) : List ObligationRow :=
  ds.map (fun d =>
    { fn := d.name
    , derived := rowOf d
    , declared := declaredOf d.name
    , verdict := verdictOf (declaredOf d.name) (rowOf d) })

/-! ## The refusal vocabulary (the envelope discipline, 05 §4) -/

/-- THE closed-world refusal vocabulary of the boundary check: the
    over-claim (a NEW closed vocabulary — `Lower.lean`'s existing
    `LowerError` is not this slice's; the E-code numbering continues
    the GC family's monotone allocation). -/
inductive EffectError where
  /-- The declared row hides effects the derivation derived (`leaked`
      = the derived row's members outside the declared allowance). -/
  | overClaim (fn : String) (leaked : Effects.Row)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The GC-family E-code: the boundary check's over-claim refusal
    (the numbering continues `LowerError`'s monotone allocation —
    GC2023). -/
def ecOverClaim : Kit.ECode := ⟨"GC2023"⟩

/-- THE diagnostic envelope: the over-claim renders into the ONE Diag
    (the GC-family E-code, the leaked row as the got, the discipline
    in the valid-space slot). -/
def EffectError.toDiag : EffectError → Kit.Diag
  | .overClaim fn leaked =>
      Kit.Diag.closedWorld ecOverClaim
        s!"effect-row over-claim on {fn}: the derivation derived \
           {renderRow leaked} from the function's content, and the \
           declared allowance does not carry it — a function declared \
           purer than its content fails the check (08 §8's discipline: \
           rows derive from registry items, never hand-written)"
        .error (renderRow leaked)
        ["a declared row that is a superset of the derived row"]

/-- The one-line rendering (the envelope's `.toString`). -/
def EffectError.render (e : EffectError) : String := Kit.Diag.toString e.toDiag

/-- THE boundary enforcement: the over-claim REFUSES (the named
    diagnostic); the under-claim and the exact match pass (the slack
    is the REPORTED face — the verdict's data, the caller's to read). -/
def enforce (fn : Lean.Name) (declared : Effects.Row) (d : Decl .impure) :
    Except EffectError Effects.Row :=
  match verdictOf declared (rowOf d) with
  | .refused leaked => .error (.overClaim fn.toString leaked)
  | .covered => .ok declared
  | .coveredWithSlack _ => .ok declared

/-! ## The verdict's law face (the teeth's theorems) -/

/-- THE refused verdict's law (the soundness face): a refused check is
    EXACTLY an over-claim — the derived row is not below the declared.
    (The obligation for the leaked row is the unprovable Prop.) -/
@[nolint linter.guestlang.zeroCitation "public API: the boundary check's law face (the teeth's soundness — cited by GuestTests.Deriv's pins)"]
theorem verdict_over_refuses (declared der : Effects.Row) (leaked : Effects.Row)
    (hv : verdictOf declared der = RowVerdict.refused leaked) :
    ¬ Effects.Row.le der declared := by
  intro hle
  exfalso
  have hd : rowDiff der declared = [] :=
    (rowDiff_nil_iff_le der declared).mpr hle
  simp only [verdictOf, hd, reduceIte] at hv
  split at hv
  · simp at hv
  · simp at hv

/-- THE refused verdict's law (the completeness face): an over-claim
    is ALWAYS refused — no leaked row slips through the check. -/
@[nolint linter.guestlang.zeroCitation "public API: the boundary check's law face (the teeth's completeness — cited by GuestTests.Deriv's pins)"]
theorem verdict_not_le_refuses (declared der : Effects.Row)
    (h : ¬ Effects.Row.le der declared) :
    ∃ leaked, verdictOf declared der = RowVerdict.refused leaked := by
  have hd : ¬ (rowDiff der declared = []) := by
    intro h0
    exact h ((rowDiff_nil_iff_le der declared).mp h0)
  refine ⟨rowDiff der declared, ?_⟩
  rw [verdictOf, if_neg hd]

/-- The under-claim's honest face: a non-refused verdict ALWAYS has
    the derived row below the declared (the under-claim passes —
    honestly, with the slack reported in the verdict). -/
@[nolint linter.guestlang.zeroCitation "public API: the boundary check's law face (the under-claim's honesty — cited by GuestTests.Deriv's pins)"]
theorem verdict_le_of_not_refused (declared der : Effects.Row) (v : RowVerdict)
    (hv : verdictOf declared der = v)
    (hr : ∀ leaked, v ≠ RowVerdict.refused leaked) :
    Effects.Row.le der declared := by
  have hd : rowDiff der declared = [] := by
    by_cases hne : rowDiff der declared = []
    · exact hne
    · exfalso
      have hvr : verdictOf declared der = RowVerdict.refused (rowDiff der declared) := by
        simp only [verdictOf]
        rw [if_neg hne]
      rw [hvr] at hv
      exact hr (rowDiff der declared) hv.symm
  exact (rowDiff_nil_iff_le der declared).mp hd

end Guest.Effects
