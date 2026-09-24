/-
# Inspector.Obligations — the obligation row as the inspector's data

Owner: the Inspector agent (the mandate tree, `inspector/`).
Driving decisions: notes/v3/03-bidirectional.md §5 (evidence binds to
EXACT implementation dependencies; the "why may this operation commit?"
command answers with the evidence chain — Lean's role stays visible and
honest); notes/v3/04-verification.md §2/§6/§8 (obligations as data; the
FOUR trust axes kept distinct — evidence strength / production method /
checker / assumptions; the acceptance shape of a correctness claim);
notes/v3/09-gates-ops.md §3-4 (the obligations are the gate's data — a
registered obligation with no discharge fails the gate; the demand-set
honesty — recording reads is insufficient, conservative invalidation).

The row is the UNIFORM view over the lanes' obligation items: the lane
replays its env extension (Kit.Lane's discipline) and projects each
item onto this carrier. The discharge state is a VALUE — an undischarged
obligation is the LOUD gap (`.openGap` with the reason), never a
comment; a row whose discharge evidence's tier mismatches the row's
tier is the data-level mis-wire (`tierMismatch` — the type-level
`Discharged` stays the lanes' construction face; the inspector INSPECTS
surfaces, so the check is data-level here).

The rendering is the honesty discipline: each tier's trust axes are
RENDERED PER AXIS (04 §6), and an `oracleSwept` row's evidence line
says TESTED AGREEMENT — it can never render as a universal proof (the
tests pin the negative).

Deliberately OUT (no consumer in this landing): the E-code applicability
rule (the first lane whose claims carry Diag codes in their obligation
payloads declares it — the leftover rule); the ledger's forward query
(the artifact ledger is the emit spine's file; the inspector reads it
when the first lane attests artifacts).

The five questions (notes/v3/01-core.md):
- root: none — the aggregation layer's uniform row over the lanes'
  obligation items (03 §5's evidence chain, as data).
- carrier grade: the closed `DischargeState` — an undischarged row is a
  value (the loud gap), a mis-wired discharge is detectable as data.
- spine reading: the lanes' replay output is this row's INPUT; the
  why-answer and the sweep report are its OUTPUT faces.
- ladder rung: n/a (the row CARRIES the tier; the rung vocabulary is
  Kit.Obligation's, defined once there).
- gate row: none yet — the gates' obligation sweep consumes
  `Inspector.report` (09 §3) in the next order; Inspector is outside
  Gates.Packages' gated set until then.
-/

import Kit.Obligation

namespace Inspector

/-! ## The discharge state (the loud gap is a value) -/

/-- A row's discharge state: either the LOUD gap (no discharge recorded,
    with the honest reason — never a silent pass) or a recorded
    discharge carrying the kit's closed evidence set. -/
inductive DischargeState where
  /-- No discharge recorded. The reason says WHY (e.g. the decidable-now
      backend fires per-table at check time; the replay carries no
      table) — an honest `none`, not a fabricated green. -/
  | openGap (reason : String)
  /-- A recorded discharge: the kit evidence (tier-consistent rows only
      pass `InspRow.tierMismatch`; the construction-side gate is
      `Kit.Discharged`'s proof field, in the lane). -/
  | discharged (ev : Kit.Evidence)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The row's short evidence tag (the sweep line's face; the why-answer
    renders the full kind line). -/
def DischargeState.tag : DischargeState → String
  | .openGap _ => "NONE RECORDED (GAP)"
  | .discharged ev =>
      match ev with
      | .citedProof thm => s!"cited `{thm}`"
      | .decided true => "decided true"
      | .decided false => "decided FALSE"
      | .generatedCheck _ _ => "generated check"
      | .oracleRow _ => "oracle row (TESTED AGREEMENT)"
      | .guestWitness _ _ => "guest witness"

/-! ## The uniform row -/

/-- The uniform obligation row: one lane's item projected onto the
    evidence-chain carrier. `payload` is the lane's own payload,
    rendered (the lanes keep their typed payloads; the inspector's
    uniform view is for the report). -/
structure InspRow where
  /-- The lane that replayed the item (e.g. `check`). -/
  lane : String
  /-- The obligation's label (the why-command's key). -/
  label : String
  /-- The obligation's computed tier (the lanes compute it at
      registration; the inspector reads, never re-derives). -/
  tier : Kit.Tier
  /-- The declaring declaration (the provenance). -/
  provenance : Lean.Name
  /-- The lane's payload, rendered. -/
  payload : String
  /-- The observer, where the claim's meaning depends on one (04 §4).
      Mandatory-in-effect for `oracleSwept`/`guestVerified` rows
      (`defects` flags its absence). -/
  observer : Option String
  /-- The row's E-code, where the lane's claim carries one (rendered
      when present; the applicability rule is named in the header). -/
  eCode : Option String
  /-- The discharge state (the loud gap is a value). -/
  discharge : DischargeState
deriving Repr, BEq, Inhabited

/-- The data-level mis-wire check: a discharged row whose evidence's
    tier differs from the obligation's tier (the construction-side gate
    is `Kit.Discharged`; the inspector INSPECTS, so this is checkable
    data — the loud, greppable flag). -/
def InspRow.tierMismatch (r : InspRow) : Bool :=
  match r.discharge with
  | .discharged ev => ev.tier != r.tier
  | .openGap _ => false

/-! ## The trust axes (04 §6 — four axes, kept distinct) -/

/-- Axis 1 — evidence strength: universal proof / bounded proof /
    sampled test. An `oracleSwept` row's strength is a SAMPLED TEST —
    the render can never say "proof". -/
def trustStrength : Kit.Tier → String
  | .provedAtElab => "universal proof (kernel-checked at elaboration)"
  | .decidableNow =>
      "bounded proof — the kernel decides the claim over the provided inputs"
  | .generatedCheck =>
      "bounded check — the generated artifact's runtime check"
  | .oracleSwept => "sampled test — tested agreement over the sweep's cases"
  | .guestVerified =>
      "bounded proof — the compiled verifier's verdict over the witness"

/-- Axis 2 — production method: handwritten / derived / solver-produced. -/
def trustProduction : Kit.Tier → String
  | .provedAtElab => "handwritten (the proof term), kernel-checked"
  | .decidableNow => "derived (the claim's decision procedure runs at check time)"
  | .generatedCheck =>
      "derived (emitted by the generator; the byte-tie binds the artifact)"
  | .oracleSwept => "derived (the sweep replays the lane's oracle fn)"
  | .guestVerified =>
      "solver-produced (the guest's untrusted producer + the small verified checker)"

/-- Axis 3 — the checker (the trusted base): the kernel / native
    evaluation / compiled verifier. -/
def trustChecker : Kit.Tier → String
  | .provedAtElab => "the kernel (elaboration)"
  | .decidableNow => "the kernel (decide)"
  | .generatedCheck => "the runtime consumer (the artifact's check fn)"
  | .oracleSwept => "the test harness (the oracle fn is the spec's shadow)"
  | .guestVerified => "the compiled verifier (identity must be pinned — 04 §7)"

/-- Axis 4 — the assumptions (environment fairness, hash assumptions,
    handler contracts — whatever the row's discharge leans on). -/
def trustAssumptions : Kit.Tier → String
  | .provedAtElab => "none disclosed"
  | .decidableNow => "none disclosed (the claim is closed at check time)"
  | .generatedCheck =>
      "the runtime environment the check runs in (toolchain, store adapter)"
  | .oracleSwept =>
      "the oracle fn is the spec's honest shadow; the generator reaches its cases"
  | .guestVerified =>
      "the checker's identity + the claim's semantics are pinned by the consumer"

/-! ## The evidence kind lines (the honesty discipline) -/

/-- The FULL evidence line: what the evidence actually guarantees, said
    out loud. The `oracleRow` line says TESTED AGREEMENT — never a
    universal theorem (04 §6); the `guestWitness` line says portability
    is tested agreement, the checker's identity is the consumer's pin. -/
def evidenceKindLine : Kit.Evidence → String
  | .citedProof thm =>
      s!"cited kernel theorem `{thm}` — universal proof, kernel-checked at elaboration"
  | .decided true =>
      "decided true — kernel-checked decision of the closed claim"
  | .decided false =>
      "decided FALSE — the claim fails (the loud gap; the backend refused, it did not fabricate)"
  | .generatedCheck artifact fn =>
      s!"generated check `{fn}` at {artifact} — the artifact's runtime check, \
        bound to its content by the byte-tie"
  | .oracleRow ref =>
      s!"oracle row `{ref}` — TESTED AGREEMENT (a regression sweep): NOT a proof, \
        never a universal theorem over unbounded inputs (04 §6)"
  | .guestWitness artifact ref =>
      s!"guest witness `{ref}` at {artifact} — a compiled verifier's verdict: \
        tested portability, and the checker's identity must be pinned (04 §7)"

/-! ## The acceptance-shape defects (04 §8) -/

/-- The row's acceptance-shape defects: the missing/lying pieces, each
    a LOUD marker (a claim without its evidence is the loudest row).
    The closed set: UNLABELED, UNATTRIBUTED, GAP, MISWIRED,
    FALSE-DECIDE, OBSERVER-MISSING. -/
def InspRow.defects (r : InspRow) : List String :=
  (if r.label.isEmpty then ["UNLABELED: an obligation row without its label"] else [])
  ++ (if r.provenance.isAnonymous then
        ["UNATTRIBUTED: no provenance — the declaring declaration must be named"]
      else [])
  ++ (match r.discharge with
      | .openGap reason =>
          [s!"GAP: undischarged — {reason} (no discharge recorded; \
            the loud gap, never a silent pass)"]
      | .discharged ev =>
          (if r.tierMismatch then
            [s!"MISWIRED: the evidence's tier `{ev.tier}` does not match \
              the obligation's tier `{r.tier}`"]
          else [])
          ++ (match ev with
              | .decided false =>
                  ["FALSE-DECIDE: the discharge's decide returned false — \
                    the claim fails"]
              | _ => []))
  ++ (if (r.tier == .oracleSwept || r.tier == .guestVerified) && r.observer.isNone then
        ["OBSERVER-MISSING: a sweep/witness claim without its observer — \
          `same behavior` is meaningless without naming what is observed (04 §4)"]
      else [])

/-- A row is clean iff its acceptance shape is complete and honest. -/
def InspRow.isClean (r : InspRow) : Bool := r.defects.isEmpty

/-- The row carries the loud gap (undischarged). -/
def InspRow.hasGap (r : InspRow) : Bool :=
  match r.discharge with
  | .openGap _ => true
  | .discharged _ => false

end Inspector
