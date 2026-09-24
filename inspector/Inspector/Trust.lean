/-
# Inspector.Trust — the trust report: the tree's trust surface, honestly rendered

Owner: the Inspector agent (the mandate tree, `inspector/`).
Driving decisions: notes/v3/04-verification.md §6 (the FOUR trust axes
kept distinct; a duel verdict / an oracle sweep is TESTED AGREEMENT —
never a theorem; the rendering's honesty discipline: the tests pin that
a fabricated `oracleSwept` row NEVER renders as a proof); §2 (the
obligation tiers as the evidence-strength profile); notes/v3/09-gates-ops.md
§3-4 (the kernel-check row is the lean4lean sweep's — this report NAMES
the replay surface, it does not re-run it; the duel rows land with the
first consumer's lane — the leftover rule).

Three sections over data the inspector already holds (the replayed rows
+ the replayed env's axiom cones, Gates.Axioms' machinery consumed via
LintKit — never re-encoded):

- the axiom surface: the replayed roots' distinct axiom cones, sorted,
  classified through `LintKit.isAllowedAxiom` (THE allowlist — the core
  triple + the disclosed native trust bases; a bare `axiom` outside it
  renders as the LOUD flag — report-only here, the axiom gate owns the
  ratchet's teeth);
- the obligation tiers' distribution: how many facts at each tier, each
  line rendered with the tier's HONEST strength (an `oracleSwept` line
  says TESTED AGREEMENT — the negative control pins the lie);
- the duel rows' status: the honest ZERO — no duel lane is registered
  today (Kit.Duel's harness seed has no consumer lane), and the report
  says "none registered", never "all duels agree".

The five questions (notes/v3/01-core.md):
- root: none — the trust surface's rendering face over the replay +
  the axiom cones (04 §6's axes, rendered per section).
- carrier grade: none — the classification is data (the closed
  `AxiomClass`); the strings are the human face.
- spine reading: the evidence stage's summary face (the replayed rows
  + cones → the profile).
- ladder rung: rung 1 — total folds; the honesty is a pinned render,
  not a proved law (the render lies are caught by the tests' negative
  controls, 15-patterns #5).
- gate row: none — the report-only face; the teeth are the gates' rows
  (axioms, native-policy, kernel-check), named in the render.
-/

import Inspector.Obligations
import LintKit
import Lean

namespace Inspector.Trust

open Lean

/-! ## The axiom surface -/

/-- The closed axiom classification (04 §6: the trust base named per
    class — never a bare "uses axioms"). -/
inductive AxiomClass where
  /-- The core triple: `propext`, `Classical.choice`, `Quot.sound`. -/
  | coreTriple
  /-- A DISCLOSED native trust base (`native_decide`/`bv_decide`'s
      certificate axioms — the native-policy gate's ratchet). -/
  | nativeTrustBase
  /-- OUTSIDE the allowlist — the loud flag (a sorry-shaped hole can
      never land; this class is how any OTHER axiom renders). -/
  | outside
deriving BEq, Repr

/-- The native trust base's shape (the same runner-checked certificate
    class LintKit.AxiomAllowlist matches — RENDERED here per class, the
    allowlist membership itself is LintKit's, consumed below). -/
def isNativeTrustBase (n : Name) : Bool :=
  ((toString n).splitOn "_native.native_decide.").length != 1 ||
  ((toString n).splitOn "_native.bv_decide.").length != 1

/-- Classify one axiom: the core triple by name, the native trust
    bases by their certificate shape, everything else OUTSIDE — via
    `LintKit.isAllowedAxiom` (consumed, never re-encoded). -/
def classifyAxiom (n : Name) : AxiomClass :=
  if n == `propext || n == `Classical.choice || n == `Quot.sound then .coreTriple
  else if isNativeTrustBase n then .nativeTrustBase
  else if LintKit.isAllowedAxiom n then .nativeTrustBase
  else .outside

/-- String-list dedup, order-preserving. -/
def dedup : List Name → List Name
  | [] => []
  | x :: xs => if xs.contains x then dedup xs else x :: dedup xs

/-- Sort + dedup the axiom set (deterministic rendering). -/
def sortedAxioms (axs : List Name) : List Name :=
  let sorted := (dedup axs).toArray.qsort (fun a b => a.toString < b.toString)
  sorted.toList

/-- The axiom surface's lines: per class, the members; an empty native
    class renders NONE DISCLOSED (the tree's state today — zero
    native_decide tree-wide, the native-policy gate's report). -/
def axiomSummary (axs : List Name) : String :=
  let sorted := sortedAxioms axs
  let core := sorted.filter (fun a => match classifyAxiom a with | .coreTriple => true | _ => false)
  let native := sorted.filter (fun a => match classifyAxiom a with | .nativeTrustBase => true | _ => false)
  let outside := sorted.filter (fun a => match classifyAxiom a with | .outside => true | _ => false)
  let coreLine :=
    if core.isEmpty then "(none)" else String.intercalate ", " (core.map toString)
  let nativeLine :=
    if native.isEmpty then
      "NONE DISCLOSED (zero native_decide tree-wide — the native-policy gate's report)"
    else String.intercalate ", " (native.map toString)
  let outsideBlock :=
    if outside.isEmpty then "  outside the allowlist: none\n"
    else "  outside the allowlist: FLAGGED (report-only here — the axiom \
            gate owns the ratchet's teeth):\n" ++
          String.intercalate "\n" (outside.map (fun a => s!"    AXIOM-OUTSIDE {a}")) ++ "\n"
  s!"axiom surface — {sorted.length} distinct axiom(s) over the replayed \
    roots' declarations (the kernel's CollectAxioms; the allowlist is \
    LintKit's, consumed):\n" ++
  s!"  core triple: {coreLine}\n" ++
  s!"  native trust bases: {nativeLine}\n" ++
  outsideBlock

/-! ## The obligation tiers' distribution (the evidence-strength profile) -/

/-- One tier's distribution line: the count + the tier's HONEST
    strength (04 §6's axis 1 — an `oracleSwept` line says TESTED
    AGREEMENT and can never render as a universal proof; the tests pin
    the negative). -/
def tierLine (t : Kit.Tier) (n : Nat) : String :=
  let strength := Inspector.trustStrength t
  s!"  {t}: {n} row(s) — {strength}" ++
  (match t with
  | .oracleSwept => "; TESTED AGREEMENT (NOT a proof; 04 §6)"
  | .guestVerified => "; the verifier's identity must be pinned (04 §7)"
  | _ => "")

/-- The tiers' distribution over the replayed rows, in the closed
    tier order (the evidence-strength profile). -/
def tierDistribution (rows : List Inspector.InspRow) : String :=
  "obligation tiers (the evidence-strength profile over the replayed rows):\n" ++
  String.intercalate "\n"
    ([Kit.Tier.provedAtElab, .decidableNow, .generatedCheck, .oracleSwept,
      .guestVerified].map fun t =>
        tierLine t (rows.filter (fun r => r.tier == t) |>.length))

/-! ## The duel rows' status (the honest zero) -/

/-- The duel rows' status: the tree registers NO duel lane yet —
    Kit.Duel's harness seed has no consumer lane (the leftover rule:
    the rows land with the first consumer). A zero here is the honest
    absence, NEVER a green "all duels agree" (04 §6: a duel verdict is
    tested agreement; an unregistered duel is no verdict at all). -/
def duelStatus : String :=
  "duel rows: NONE REGISTERED — no duel lane exists yet (Kit.Duel's \
    harness seed has no consumer lane); a zero here is honest absence, \
    never \"all duels agree\""

/-! ## THE TRUST REPORT -/

/-- THE TRUST REPORT: the kernel-check coverage (which modules replay —
    the demand-set honesty: the replay names its roots; the loaded
    closure's size is split into the tree's own modules vs the total —
    the census's project-roots discipline made visible; the lean4lean
    double-check is the kernel-check gate's row, never re-run here),
    the axiom surface, the tiers' distribution, the duel status. -/
def trustReport (replayed : String) (projMods totalMods : Nat)
    (axs : List Name) (rows : List Inspector.InspRow) : String :=
  s!"trust report — replayed roots: {replayed}\n" ++
  s!"kernel-check coverage: {totalMods} module(s) in the loaded closure, " ++
  s!"{projMods} of them the tree's own (the project-roots discipline's " ++
  "face) — the replay's roots name the checked surface exactly; the \
    lean4lean pure-kernel sweep is the kernel-check gate's row (never \
    re-run here)\n" ++
  axiomSummary axs ++
  tierDistribution rows ++ "\n" ++
  duelStatus ++ "\n" ++
  "honesty discipline (04 §6): an oracle-swept row renders TESTED \
    AGREEMENT — the tests pin that it can never render as a proof"

/-! ## the host face (the axiom cones over a replayed env) -/

/-- The replayed roots' distinct axiom cone: every decl whose module is
    rooted at one of the roots (LintKit.packageDecls, consumed) gets
    its kernel `collectAxioms` cone; the union is the surface the
    report classifies. Host-side (the env machinery). -/
unsafe def axiomCones (env : Lean.Environment) (roots : Array Name) :
    CoreM (List Name) := do
  let decls ← LintKit.packageDecls env roots
  let mut set : NameSet := {}
  for d in decls do
    for a in ← collectAxioms d do
      set := set.insert a
  pure set.toList

end Inspector.Trust
