/-
Gates.ObligationView — the gates' rows AS obligation values (B7, the
self-application: design-wave-30 item B7).

Each baseline-report gate row's invariant enters the Kit.Obligation
substrate as DATA: the label (`gate/<name>`), the COMPUTED tier (every
gate check is `.generatedCheck` — an IO-shaped host check: file reads,
child processes, env replays — never a decidable proposition, so never
`.decidableNow`), the payload (the row's own context), the provenance
(this module's minter), and the closed evidence: the committed baseline
file IS the generated check's artifact, the gate's check fn its name —
`.generatedCheck artifact fn`, the EXISTING closed ctor (no new
evidence kind: the set is closed and already carries this shape).

The three equations (the plan's B7 wording, made concrete):
- the gate's RUN = the DISCHARGE ATTEMPT: `Driver.diffBaseline`'s three
  faces map one-to-one onto the verdict — in sync = discharged, drift =
  a STALE CERTIFICATE, absent = no certificate.
- the BASELINE = the DISCHARGED CERTIFICATE: the committed
  `render ++ "\n"` file at the artifact path, carrying the
  `.generatedCheck` ref.
- DRIFT = a STALE CERTIFICATE, and the RE-BASELINE DISCIPLINE IS THE
  REPLAY DISCIPLINE: `--write --accept-drift` (Driver.reportGate's
  refusal without it) re-RUNS the discharge and re-mints the
  certificate — a deliberate, commit-visible replay, never a silent
  overwrite. Re-baselining without re-running is unrepresentable (the
  write only ever happens from a fresh render).

THE HONEST MISFIT (disclosed, not forced): the substrate's soundness
theorem lives at the `decidableNow` rung only (`decideDischarge_sound`);
there is NO Lean-side soundness at the `generatedCheck` rung — a gate
discharge's trust base is the host run itself (the VCS + the fresh
render), the same trust story every `.generatedCheck` evidence carries.
The claim index `GateClaim gate` is correspondingly opaque: no Lean
proof object exists for a gate row, and `certify` mints the
`Discharged` CERTIFICATE AS DATA from the run's verdict — the tier
mis-wire stays unconstructible (the `tierOK` field), the claim mis-wire
stays a type error, but the claim's truth is carried by the run, not by
elaboration. The teeth: an undischarged row (stale, absent, or
mis-wired evidence) is LOUD — `undischarged` + the GT0003/GT0002 Diag
face; a gate that swallowed a stale certificate would be the fiction.

The trichotomy on the gates' own state (the plan's N9, 03 §7): a gate
RUN is a COMMAND (requested intent — can fail, can no-op); a
RE-BASELINE is a DELTA (the accepted NET change to the certificate — it
erases the intermediate drift history, which is why it must be
deliberate); an AUDIT-LOG entry is an EVENT (the recorded occurrence —
the report lines: which gate, which verdict, when). Driver.reportGate's
three branches and Gates.runAll's START/verdict lines ARE these three,
named here once.

Additive layer: no gate's IO behavior changes — the existing gates keep
their exits; this is the vocabulary + the data face the rows ride (the
consumers: GatesTests' B7 sabotage battery, then the gates' tails as
they adopt it).

The five questions (notes/v3/01-core.md):
- root: none — a VIEW over Kit.Obligation (the substrate unchanged).
- carrier grade: none of its own — the mis-wire rules stay
  `Discharged`'s (tier unconstructible, claim a type error).
- spine reading: the artifact stage's check face, indexed.
- ladder rung: `.generatedCheck` (the gates' own rung — the only one
  the IO-shaped checks honestly occupy).
- gate row: this module is Kit-row'd via the Gates lib's per-library
  axiom sweep; the battery's B7 suite is the negative-control row.
-/

import Kit.Obligation
import Gates.Common

namespace Gates.ObligationView

/-! ## The claim index — opaque, per gate -/

/-- The gate row's claim, as the obligation's TYPE INDEX: opaque at
    elaboration (a gate's check is an IO-shaped host check — its truth
    is discharged by the RUN, not by a Lean decision). One claim per
    gate name: a certificate filed under a different gate's claim is a
    different TYPE — the claim mis-wire fails to elaborate. -/
class GateClaim (gate : String) : Prop

/-! ## The gate row as an obligation value -/

/-- The gate row's obligation value: label + computed tier
    (`.generatedCheck` — every gate check is IO-shaped) + payload +
    provenance, indexed by the gate's OWN claim. (The artifact + fn
    names live on the EVIDENCE — `certificate` — not on the row: the
    obligation claims, the discharge cites.) -/
def gateObligation (gate payload : String) :
    Kit.Obligation String (GateClaim gate) :=
  { label := s!"gate/{gate}"
  , tier := .generatedCheck
  , payload := payload
  , provenance := `Gates.ObligationView.gateObligation }

/-- The discharged certificate's EVIDENCE (the closed set's existing
    `.generatedCheck` ctor — the committed baseline file is the
    artifact, the gate's check fn the name). -/
def certificate (artifact fn : String) : Kit.Evidence :=
  .generatedCheck artifact fn

/-! ## The discharge attempt — the gate's run as a verdict -/

/-- The gate run's outcome as data (the discharge attempt's three
    faces). `discharged` carries the closed evidence; a stale or absent
    certificate is the LOUD undischarged face. -/
inductive Verdict where
  | discharged (e : Kit.Evidence)
  | staleCertificate
  | absentCertificate

/-- The gate's RUN = the discharge attempt: the baseline diff's three
    faces ARE the verdict's three (Driver.diffBaseline → Verdict,
    one-to-one). DRIFT = a stale certificate — the committed baseline no
    longer replays against the fresh render. -/
def attempt (b : Driver.Baseline) (e : Kit.Evidence) : Verdict :=
  match b with
  | .inSync => .discharged e
  | .drifted => .staleCertificate
  | .absent => .absentCertificate

/-- The tier-gated certificate mint (the substrate's `Discharged` at the
    `.generatedCheck` rung): only evidence whose tier MATCHES the row's
    computed tier mints a certificate — a mis-wired evidence kind (e.g.
    a `.decided` verdict filed on a gate row) is the LOUD `none` (the
    data-level mis-wire check, made a proof), and a stale/absent
    certificate discharges NOTHING. -/
def certify (o : Kit.Obligation String (GateClaim gate)) (v : Verdict) :
    Option (Kit.Discharged String (GateClaim gate)) :=
  match v with
  | .discharged e =>
      if h : e.tier = o.tier then
        some { obligation := o, evidence := e, tierOK := h }
      else none
  | .staleCertificate | .absentCertificate => none

/-! ## The teeth — the undischarged row fails LOUDLY -/

/-- THE TEETH: an undischarged obligation fails LOUDLY. `true` = the
    gate must fail (exit 1 + the Diag face); a stale certificate is a
    FINDING, never a silent pass. -/
def undischarged : Verdict → Bool
  | .discharged _ => false
  | .staleCertificate | .absentCertificate => true

/-- The verdict's Diag face (the ONE envelope, B1): the stale
    certificate is GT0003 (an artifact drifted its regen), the absent
    one GT0002 (a declared artifact is absent); a discharged row is
    quiet (no finding exists). -/
def verdictDiag (gate : String) : Verdict → Option Kit.Diag
  | .discharged _ => none
  | .staleCertificate =>
      some (GateDiag eGT0003
        s!"{gate}: the baseline is a STALE CERTIFICATE — the gate's \
          obligation is UNDISCHARGED; run `lake exe gates {gate} --write` \
          and commit (the replay discipline: re-mint deliberately)")
  | .absentCertificate =>
      some (GateDiag eGT0002
        s!"{gate}: no baseline certificate — run \
          `lake exe gates {gate} --write` and commit")

/-! ## The trichotomy on the gates' own state (N9, 03 §7) -/

/-- The gates' own state in the discipline's vocabulary: a RUN is a
    COMMAND (can fail, can no-op), a RE-BASELINE is a DELTA (the
    accepted net change), an AUDIT-LOG entry is an EVENT (the recorded
    occurrence). Driver.reportGate's branches (run / accept-drift write
    / report lines) and Gates.runAll's START/verdict lines are these
    three — named once, here. -/
inductive GateAction where
  | command
  | delta
  | event

def GateAction.render : GateAction → String
  | .command => "command (can fail, can no-op)"
  | .delta => "delta (the accepted net change)"
  | .event => "event (the recorded occurrence)"

end Gates.ObligationView
