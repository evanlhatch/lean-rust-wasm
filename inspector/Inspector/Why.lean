/-
# Inspector.Why — the why-answer + the sweep report (pure rendering)

Owner: the Inspector agent (the mandate tree, `inspector/`).
Driving decisions: notes/v3/03-bidirectional.md §5 (the "why may this
operation commit?" command answers with the evidence chain); notes/v3/
04-verification.md §6/§8 (the trust axes rendered honestly per evidence
kind; the acceptance shape enforced per row); notes/v3/09-gates-ops.md
§3-4 (the sweep the gates consume — a registered obligation with no
discharge fails the gate; the demand-set honesty: the report names the
replayed roots, because a lane outside them is INVISIBLE here and
silence would lie).

Pure over `Inspector.InspRow` — no IO, so the tests pin the rendering
without an environment. The exe (InspectorMain) and the test driver own
the replay.

The five questions (notes/v3/01-core.md):
- root: none — the rendering face over the uniform obligation row.
- carrier grade: none — strings are the human face; the row is the data.
- spine reading: the lanes' replay output rendered per row (why) and as
  the sweep (report).
- ladder rung: n/a.
- gate row: the report IS the future gate row's body (the gates'
  obligation sweep consumes it next; 09 §3).
-/

import Inspector.Obligations

namespace Inspector

/-! ## The why-answer (one row's evidence chain) -/

/-- One row's why-answer: the label → its tier, its evidence (the cited
    theorem / the decide result / the artifact ref), its provenance, the
    FOUR trust axes, and the honest gaps. An undischarged obligation
    renders as the LOUD GAP, never omitted; the defects ride the tail
    as FLAG lines. -/
def InspRow.renderWhy (r : InspRow) : String :=
  let observerLine :=
    match r.observer with
    | some o => s!"  observer: {o}\n"
    | none => ""
  let eCodeLine :=
    match r.eCode with
    | some c => s!"  e-code: {c}\n"
    | none => ""
  let evBlock : String :=
    match r.discharge with
    | .openGap reason =>
        s!"    GAP: undischarged at replay — {reason}\n" ++
        "    No discharge is recorded for this row; no universal claim is made."
    | .discharged ev => s!"    {evidenceKindLine ev}"
  let flagLines :=
    (String.intercalate "\n" (r.defects.map (fun d => s!"  FLAG: {d}")))
  s!"why `{r.label}`\n" ++
  s!"  lane: {r.lane}\n" ++
  s!"  provenance: {r.provenance}\n" ++
  s!"  tier: {r.tier}\n" ++
  s!"  payload: {r.payload}\n" ++
  observerLine ++ eCodeLine ++
  "  trust axes:\n" ++
  s!"    evidence strength: {trustStrength r.tier}\n" ++
  s!"    production method: {trustProduction r.tier}\n" ++
  s!"    checker: {trustChecker r.tier}\n" ++
  s!"    assumptions: {trustAssumptions r.tier}\n" ++
  "  evidence:\n" ++ evBlock ++
  (if r.defects.isEmpty then "" else "\n" ++ flagLines)

/-- The unknown-label answer: the LOUD miss — the available labels are
    listed (the one engine's did-you-mean discipline at report scale). -/
def whyUnknown (rows : List InspRow) (label : String) : String :=
  "inspector: NO obligation labeled `" ++ label ++ "` in the replayed rows\n" ++
  "  available labels:\n" ++
  (String.intercalate "\n" (rows.map (fun r => s!"    - {r.label}"))) ++ "\n" ++
  "  (the full sweep: lake exe inspector report)"

/-- The why command over the collected rows: an exact label match
    renders the row's evidence chain; no match renders the loud miss. -/
def why (rows : List InspRow) (label : String) : String :=
  match rows.filter (fun r => r.label == label) with
  | [] => whyUnknown rows label
  | ms => (String.intercalate "\n" (ms.map (·.renderWhy)))

/-- Whether the label resolves (the exe's exit-code face: an unknown
    label is a loud miss, exit 1). -/
def whyKnown (rows : List InspRow) (label : String) : Bool :=
  rows.any (fun r => r.label == label)

/-! ## The sweep report (the gates' future input) -/

/-- One row's sweep line + its defect lines. -/
def InspRow.renderSweep (r : InspRow) : String :=
  let observerTag := match r.observer with | some o => o | none => "—"
  let eCodeTag := match r.eCode with | some c => c | none => "—"
  let head :=
    s!"  [{r.lane}] {r.label} — tier={r.tier} evidence={r.discharge.tag} \
      observer={observerTag} e-code={eCodeTag}"
  if r.defects.isEmpty then head
  else head ++ "\n" ++ (String.intercalate "\n" (r.defects.map (fun d => s!"    FLAG: {d}")))

/-- THE SWEEP: every replayed row, its acceptance shape, the loud gaps,
    and the summary counts. `replayed` names the replayed roots — the
    demand-set honesty: coverage is EXACTLY the loaded roots; a lane
    registered outside them is invisible here (09 §4: conservative
    invalidation governs the gates' consumption). -/
def report (replayed : String) (rows : List InspRow) : String :=
  let gaps := rows.filter (·.hasGap)
  let flagged := rows.filter (fun r => !r.isClean)
  "obligation sweep — replayed roots: " ++ replayed ++ "\n" ++
  s!"{rows.length} obligation row(s):\n" ++
  (String.intercalate "\n" (rows.map (·.renderSweep))) ++ "\n" ++
  s!"summary: {rows.length} row(s), {gaps.length} gap(s), \
    {flagged.length} row(s) flagged\n" ++
  "coverage = the replayed roots ONLY — a lane outside them is invisible \
    here (09 §4: the demand set names its reads; conservative invalidation \
    governs the gates' consumption)\n" ++
  "the gates' obligation sweep consumes this report (09 §3: a registered \
    obligation with no discharge, or evidence resolving to nothing, fails \
    the gate)"

end Inspector
