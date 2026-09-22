/-
# Gates.ObligationCheck — the oracle-ref resolution gate (`gates obligation-check`)

The obligation ladder's LAST rung, armed AND fired: schema-lang's
`SchemaObligation.discharge` discharges an `oracleSwept` obligation on a
WELL-FORMED row reference (non-empty, naming the payload's record — the
lightest honest check available THERE: schema-lang cannot see the
oracle's row universe). The CROSS-PACKAGE resolution half lives HERE —
the gates exe loads both environments (Gates.Common's replayed
registries + wasm-backend's `Oracle.rowUniverse`, the same shapes
Gates.Coverage consumes):

  every `Evidence.oracleRow` ref claimed for a registered obligation
  RESOLVES to an actual oracle row.

An oracle row PROVES nothing by itself — it is evidence a property was
SWEPT. The gate's claim is exactly the ladder's semantics: an
obligation claiming oracle coverage names a row that EXISTS (a
claimed-but-dangling ref fails CI), and an obligation REGISTERED at
`oracleCovered` claims a row (discharge-side that is the loud `none`;
gate-side it is a failure — the armed-but-unfired gap cannot hide).

The claims table: (obligation label, oracle fn ref) pairs — the demo's
oracle-coverage claims. EMPTY today: the invariant lane's registration
(`schema_invariant`) computes only `boundaryCheck`/`proved` tiers, so
no oracleSwept obligation exists in the registry yet — the tier's
first consumer is a later order, and its registrations land here. The
gate is still NON-VACUOUS: the canary ref below must resolve on every
run (the demo's witness rows are committed spec data), so a broken
resolution surface fails loudly even with no claims.

Checks (each failure = exit 1):
1. CANARY — `canaryRef` resolves to an actual oracle row fn (the
   machinery is exercised every run; a vacuous gate cannot hide).
2. LABEL — a claimed label names a REGISTERED invariant (a claim for
   an unregistered obligation is drift).
3. TIER — the claimed obligation's tier IS `oracleCovered` (a claim of
   oracle-row evidence for a non-oracle obligation is the kit's
   mis-wire: `Evidence.tier` must equal the obligation's tier).
4. RESOLUTION — every claimed ref's fn is an actual oracle row fn
   (`rowUniverse`; the ref names the WIT export, the args ride the
   byte-frozen manifest).
5. COMPLETENESS — every registered `oracleCovered` invariant has a
   claim (the loud-none audit's positive form).

Teeth (verified for this order, then removed): a temporary dangling
entry `("id-positive", "no-such-fn")` failed check 4; a temporary
entry for an unregistered label failed check 2; a temporary
mis-wired claim (`("id-positive", "user-valid")` — `id-positive` is a
`generatedCheck` obligation) failed check 3; and pointing the canary
at a missing fn failed check 1. All four teeth FIRE; the committed
state (no claims, canary resolving) is green.

LEGACY (non-module) file: meta env-extension access via Gates.Common
(the module-migration constraint: such drivers stay legacy).
-/
import Gates.Common
import SchemaLang
import Oracle

namespace Gates.ObligationCheck

/-- The canary: a ref the oracle's row universe MUST resolve (the
    `verify-witness` rows are committed spec data — the witness
    fixtures). Non-vacuity control: if this ever fails, the resolution
    surface is broken and the gate says so LOUDLY, even with no
    claims to audit. -/
def canaryRef : String := "verify-witness"

/-- The oracle-coverage claims: (obligation label, oracle fn ref)
    pairs. EMPTY today — no registered obligation carries the
    `oracleCovered` tier yet (the registration command computes only
    the two executable/proved rungs); the first consumer's claims land
    here. See the header's teeth log for the verified negative shapes. -/
def oracleClaims : List (String × String) := []

/-- The oracle's fn surface, read from the ROW UNIVERSE itself (never
    a hand copy — wasm-backend's `Oracle.rowUniverse` is THE single
    source of the oracle's rows). -/
def oracleRowFns : List String :=
  (rowUniverse.map (·.1)).eraseDups

/-- Check 1: the canary resolves. -/
def canaryFindings : List String :=
  if oracleRowFns.contains canaryRef then []
  else [s!"canary: ref `{canaryRef}` does not resolve to any oracle row \
    — the resolution surface is broken (non-vacuity control FIRED)"]

/-- Checks 2+3+4: every claim names a registered oracleCovered
    invariant AND its ref resolves to an actual oracle row fn. -/
def claimFindings (invs : List SchemaLang.InvariantItem) : List String :=
  oracleClaims.flatMap fun (label, ref) =>
    match invs.find? (·.name == label) with
    | none =>
        [s!"claim `{label}`: no registered invariant of that name \
          (drift — the obligation it claims is gone)"]
    | some it =>
        (if it.tier == .oracleSwept then []
         else [s!"claim `{label}`: registered tier is `{it.tier}` — \
           oracle-row evidence is MIS-WIRED onto a non-oracle obligation \
           (the kit's Evidence.tier rule)"])
        ++
        (if oracleRowFns.contains ref then []
         else [s!"claim `{label}`: ref `{ref}` DANGLES — no oracle row \
           replays that fn (the armed-and-FIRED gate)"])

/-- Check 5: every registered `oracleCovered` invariant has a claim —
    the discharge-side loud `none` (the armed-but-unfired gap) as a
    gate failure. -/
def unclaimedFindings (invs : List SchemaLang.InvariantItem) : List String :=
  invs.filterMap fun it =>
    if it.tier == .oracleSwept && !(oracleClaims.any (·.1 == it.name)) then
      some s!"obligation `{it.name}` registers tier `oracle-covered` but \
        claims no oracle row — the armed-but-unfired gap"
    else none

/-- The gate. -/
unsafe def run : IO UInt32 := do
  let ctx ← Gates.loadGenCtx
  let findings := canaryFindings
    ++ claimFindings ctx.invariants
    ++ unclaimedFindings ctx.invariants
  IO.println s!"obligation-check: {oracleClaims.length} oracle-coverage \
    claim(s) over {ctx.invariants.length} registered invariant(s), \
    {oracleRowFns.length} oracle row fn(s)"
  if findings.isEmpty then
    IO.println "obligation-check: every claimed oracleRow ref RESOLVES; \
      every oracleCovered obligation is claimed"
    return 0
  findings.forM fun f => IO.println s!"obligation-check: {f}"
  return 1

end Gates.ObligationCheck
