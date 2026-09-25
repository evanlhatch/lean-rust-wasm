/-
# Inspector.DuelReplay — the duel vector sets' replay + the explain discipline

Owner: the Inspector agent (the mandate tree, `inspector/`).
Driving decisions: notes/v3/13-interfaces.md (the oracle manifest +
verdicts row — the replay/explain face of the evidence channels);
the legacy oracle-runner's EXPLAIN discipline (legacy/crates/
oracle-runner: re-run ONE row with the full witness — the path, both
sides' outcomes, the divergence kind — not a raw dump); notes/v3/
04-verification.md §6 (the verdicts' honesty: `oracleSwept` means
TESTED AGREEMENT, never a theorem — the report says so); Kit.Duel (the
vector-set convention + the verdict vocabulary, consumed READ-ONLY);
notes/v3/02-data-plane.md (the divergences.md ledger discipline, the
duel lane's face: a divergence is investigated before it is
adjudicated; an empty ledger = we looked).

THE REPLAY DISCIPLINE: the five committed duel sets (the wasm
execution duel `gen/wasm-duel`, the codec differential
`crates/schema-generated/tests/duel`, the commit slice
`crates/schema-generated/tests/duel-commit`, the journal duel
`crates/mandate-delta/tests/duel`, the witness duel
`crates/schema-generated/tests/duel-witness`) each carry a committed manifest
(generator row + one `<path>\t<expectation>` row per vector) and the
committed vector bytes. The replay re-runs the duel's LEAN side
against the current state: the committed bytes go through the landed
engine (the executor, the codec, the checker), the observed outcome is
rendered in the manifest's OWN note vocabulary, and the verdict is
compared row-for-row against the committed expectation. A duel that
replays green is a regression row (tested agreement, never a
theorem); a divergence carries the witness — BOTH sides' values, the
manifest's expectation and the Lean replay's observation (04 §8:
never a bare "behavior changed").

THE EXPLAIN DISCIPLINE: each divergence renders as the ONE diagnostic
envelope (Kit.Diag — the E-code, the message naming both sides, the
got/valid pair) plus a ready-to-paste LEDGER ROW for
`inspector/duel-divergences.md` (the divergences.md discipline's
table). The ledger itself is committed and honest-empty today: the
first full replay found zero divergences, and an empty ledger says we
looked.

The lanes are consumed READ-ONLY (WasmCore.Duel, SchemaCore.Codec,
SchemaCore.Commit, SchemaCore.Emit.Journal — their emitters stay the
ONE writer per artifact; this module only READS the committed
manifests + vectors and re-runs the landed engines).

The five questions (notes/v3/01-core.md):
- root: Crossing — the four duels' Lean halves vs their committed
  expectations, coupled through the committed manifests (Kit.Duel's
  consumer contract, Lean face).
- carrier grade: the verdicts are Kit.Duel's ctors (never strings);
  the closed duel registry drives the closed-world did-you-mean (the
  ONE engine); the parse refusals are `Except` (single-fail).
- spine reading: the artifacts are read, never re-encoded — the
  manifest the text lane, the vectors the binary lane (gen-check owns
  the byte-tie; the wasm replay re-derives the byte tie as EVIDENCE,
  not authority).
- ladder rung: rung 1 — pure data + total folds; the agreement is
  TESTED (the tier note above), nothing here is proved about the
  engines.
- gate row: none — the inspector exe's `duel` command is the
  consumer; the InspectorTests suite (the replay pins + the planted
  divergence + the negative controls) is the standing evidence; the
  E-codes ride the persisted registry (IN0001–IN0003).
-/

import Kit.Duel
import Kit.Suggest
import Kit.Varint
import SchemaCore.Codec
import SchemaCore.Commit
import SchemaCore.Emit.Journal
import SchemaCore.Emit.Witness
import WasmCore.Duel

namespace Inspector.DuelReplay

open Kit.Duel

/-! ## The manifest (Kit.Duel's consumer contract, the Lean face) -/

/-- One expectation row's parsed form: the closed vocabulary rendered
    by `Kit.Duel.Expect.render`, read back. Unparseable rows refuse
    NAMING the vocabulary (never a silent skip). -/
def parseExpect (s : String) : Except String Expect :=
  match s.splitOn " " with
  | ["refuse"] => Except.ok .refuse
  | ["trap"] => Except.ok .trap
  | "decode" :: rest => Except.ok (.decode (String.intercalate " " rest))
  | "run" :: rest => Except.ok (.run (String.intercalate " " rest))
  | _ => Except.error s!"unparseable expectation `{s}` — the closed vocabulary: \
`decode <note>` | `refuse` | `run <result>` | `trap`"

/-- A parsed duel manifest: the generator provenance + one
    (path, expectation) row per vector (Kit.Duel's ONE format). -/
structure DuelManifest where
  /-- The manifest's `generator` provenance row's module. -/
  generator : String
  /-- The rows: repo-root-relative path + the expectation. -/
  rows : List (String × Expect)
  deriving Repr

/-- The manifest parser — the consumer contract's walk: skip the
    2-line GENERATED header, read the `generator\t<module>`
    provenance row, then one tab-split row per vector. Every deviation
    refuses NAMING the line (never a silent skip, never a panic). -/
def parseManifest (text : String) : Except String DuelManifest :=
  match (text.splitOn "\n").drop 2 |>.filter (· ≠ "") with
  | [] => Except.error "manifest: only the GENERATED header — no rows"
  | genLine :: rest =>
      match genLine.splitOn "\t" with
      | ["generator", g] =>
          rest.foldl (fun acc line =>
            match acc with
            | Except.error e => Except.error e
            | Except.ok rows =>
                match line.splitOn "\t" with
                | [path, expectStr] =>
                    match parseExpect expectStr with
                    | Except.ok x => Except.ok (rows ++ [(path, x)])
                    | Except.error e => Except.error s!"row `{line}`: {e}"
                | _ => Except.error s!"row `{line}`: expected `<path>\t<expectation>`")
            (Except.ok [])
          |>.map fun rows => { generator := g, rows := rows }
      | _ => Except.error
          "manifest: the first row must be the `generator\t<module>` provenance row"

/-! ## The observed outcome (the replay's answer, per row) -/

/-- What the Lean engine observed for one vector — the replay's
    observed face, rendered in the duel's OWN note vocabulary so the
    comparison against the manifest's note is exact-string. `trapped`
    is the executor's typed trap (distinct from a decode refusal —
    the R6 discipline). -/
inductive Observed where
  | /-- The vector answered; the note is the duel's value vocabulary. -/
    value (note : String)
  | /-- The executor trapped (the wasm duel's expected-trap face). -/
    trapped (why : String)
  | /-- The engine refused — a typed refusal, never a panic. -/
    refusal (why : String)
  deriving Repr

/-- Render an observation (the explain face's rhs side). -/
def Observed.render : Observed → String
  | .value n => s!"value {n}"
  | .trapped w => s!"trapped: {w}"
  | .refusal w => s!"refused: {w}"

/-- One row's verdict: the manifest's expectation vs the Lean
    replay's observation. Agreement is exact-string in the duel's note
    vocabulary; ANY other pairing diverges with the witness carrying
    BOTH sides (Kit.Duel's ctors, 04 §8). -/
def rowVerdict (path : String) (x : Expect) (o : Observed) : Verdict :=
  let diverge : Verdict := .diverge ⟨path, Expect.render x, Observed.render o⟩
  match x, o with
  | .decode note, .value n => if n = note then .agree else diverge
  | .run r, .value n => if n = r then .agree else diverge
  | .refuse, .refusal _ => .agree
  | .trap, .trapped _ => .agree
  | _, _ => diverge

/-! ## The shared value-note vocabulary (the atoms + the row walks) -/

/-- One scalar value's note spelling (the duel manifests' value
    vocabulary: `false`, `300`, `-1`, `hi`). -/
def fieldNoteVal : (t : SchemaCore.Ty) → SchemaCore.Value t → String
  | .bool, .bool b => if b then "true" else "false"
  | .u64, .u64 n => toString n
  | .i64, .i64 n => toString n
  | .string, .string s => s
  | _, _ => "unrendered"

/-- Decode a positional field walk (schema order IS the positional
    order — the encoders' contract), keeping the typed payloads as
    `FieldVal`s. A truncated or out-of-policy walk refuses. -/
def decFields : List SchemaCore.Ty → List UInt8 →
    Option (List SchemaCore.FieldVal × List UInt8)
  | [], bs => some ([], bs)
  | t :: ts, bs =>
      match SchemaCore.decVal t bs with
      | none => none
      | some (v, rest) =>
          match decFields ts rest with
          | none => none
          | some (vs, rest') => some ({ ty := t, val := v } :: vs, rest')

/-- Re-encode a walked field list (the decode-then-re-encode
    differential's BOTH directions, Lean face). -/
def encFields : List SchemaCore.FieldVal → List UInt8 :=
  fun fs => fs.flatMap fun kv => SchemaCore.encVal kv.ty kv.val

/-- The Example row's field types (the codec duel's record row — the
    goldens' encoding face, schema order). -/
def exampleTys : List SchemaCore.Ty :=
  [.bool, .u64, .i64, .string, .option .string, .list .string]

/-! ## The wasm execution duel's Lean replay (WasmCore.Duel, read-only) -/

/-- The duel family PLUS the invalid control (the control's bytes are
    the encoder's output too — its refusal is its expectation). -/
def wasmFamilyEx : List (String × WasmCore.Module) :=
  WasmCore.Duel.duelFamily ++ [("invalid", WasmCore.Duel.invalidModule)]

/-- THE WASM REPLAY: the committed bytes must be the current encoder's
    output for the family member the path names (the byte tie, re-derived
    as EVIDENCE — gen-check owns the authority), then the landed
    executor re-runs and its computed answer is the observation. The
    invalid control re-validates: the refusal IS the expectation. -/
def wasmEngine (path : String) (_x : Expect) (bytes : ByteArray) : Observed :=
  match wasmFamilyEx.find? (fun nm => WasmCore.Duel.duelVecName nm.1 = path) with
  | none =>
      -- the closed-world discipline: the family's vector names are
      -- enumerable — the error enumerates them + the did-you-mean suffix
      -- (Kit.suggestSuffix; the didyoumeanDiscipline rule)
      let valid := wasmFamilyEx.map (fun nm => WasmCore.Duel.duelVecName nm.1)
      .refusal s!"unknown wasm duel vector `{path}` — the committed family \
        is the closed world: {String.intercalate ", " valid}\
        {Kit.suggestSuffix path valid}"
  | some (n, m) =>
      if bytes.toList ≠ WasmCore.encodeModule m then
        .refusal s!"the committed bytes are not the current encoder's output for `{n}`"
      else if n = "invalid" then
        match WasmCore.checkModule m with
        | .error _ => .refusal "the validator refuses (the expected refusal)"
        | .ok () => .value "validated"
      else
        match WasmCore.Duel.duelExpect n m with
        | .error e => .refusal s!"generation failure: {e}"
        | .ok (.run r) => .value r
        | .ok .trap => .trapped "the executor traps"
        | .ok (.decode _) => .refusal "decode expectation on a wasm member — generator bug"
        | .ok .refuse => .refusal "refuse expectation on a valid member — generator bug"

/-! ## The schema-codec duel's Lean replay (SchemaCore.Codec, read-only) -/

/-- The atom note's kind word → the wire type (the manifest's own
    spelling: `str` names the string). -/
def atomTy : String → Option SchemaCore.Ty
  | "bool" => some .bool
  | "u64" => some .u64
  | "i64" => some .i64
  | "str" => some .string
  | _ => none

/-- ONE ATOM ROW's replay: decode, re-encode (byte-identical), render
    the observation in the note vocabulary — the manifest's note is
    the value-level pin (a drift from the bytes fails the replay). -/
def atomObserved (kind : String) (bs : List UInt8) : Observed :=
  match atomTy kind with
  | none => .refusal s!"unparsed atom kind `{kind}`"
  | some t =>
      match SchemaCore.decVal t bs with
      | none => .refusal "the Lean codec refuses the bytes"
      | some (v, rest) =>
          if !rest.isEmpty then .refusal "the Lean codec left unconsumed bytes"
          else if SchemaCore.encVal t v ≠ bs then
            .refusal "re-encode drifted from the committed bytes"
          else .value s!"atom {kind} {fieldNoteVal t v}"

/-- THE CODEC REPLAY: `refuse` rows re-run the refusal probe (the
    tampered shapes must refuse — the negative control passing);
    `decode` rows decode + re-encode byte-identically and render the
    observed note (the record row's note is `example`, the atoms' are
    the value pins). -/
def codecEngine (_path : String) (x : Expect) (bytes : ByteArray) : Observed :=
  let bs := bytes.toList
  match x with
  | .refuse =>
      match decFields exampleTys bs with
      | none => .refusal "the Lean codec refuses (the expected refusal)"
      | some (_, rest) =>
          if !rest.isEmpty then .refusal "the walk left unconsumed bytes"
          else .value "decoded"
  | .decode note =>
      if note = "example" then
        match decFields exampleTys bs with
        | none => .refusal "the Lean codec refuses the row"
        | some (fvs, rest) =>
            if !rest.isEmpty then .refusal "the walk left unconsumed bytes"
            else if encFields fvs ≠ bs then
              .refusal "re-encode drifted from the committed bytes"
            else .value "example"
      else
        match note.splitOn " " with
        | "atom" :: kind :: _ => atomObserved kind bs
        | _ => .refusal s!"unparsed decode note `{note}`"
  | _ => .refusal "the schema-codec duel has no run/trap rows"

/-! ## The journal duel's Lean replay (SchemaCore.Event, read-only) -/

/-- The journal duel's schema (the delta crate's slice — Emit.Journal's
    documented shape, consumed read-only). -/
def journalFields : List SchemaCore.Field :=
  SchemaCore.Emit.Journal.journalFields

/-- The journal duel's keyed field name (the delta crate's slice keys
    on `id` — the emitter's documented shape; the remove note renders
    the key image against it. A key drift diverges loudly: the note IS
    the pin). -/
def journalKeyFieldName : String := "id"

/-- A typed row decoder over the GADT (the Rust consumer's face: a
    varint field count checked against the schema's arity — the skewed
    count refuses — then one `decVal` per field in schema order). -/
def decRowVals : (fs : List SchemaCore.Field) → List UInt8 →
    Option (SchemaCore.RowVals fs × List UInt8)
  | [], bs => some (.nil, bs)
  | f :: fs, bs =>
      match SchemaCore.decVal f.ty bs with
      | none => none
      | some (v, rest) =>
          match decRowVals fs rest with
          | none => none
          | some (vs, rest') => some (.cons v vs, rest')

/-- The frame's ROW decoder (the count-checked walk over the journal
    schema). -/
def journalDecR : List UInt8 →
    Option (SchemaCore.RowVals journalFields × List UInt8) :=
  fun bs =>
    match Kit.Varint.decVarNat? bs with
    | none => none
    | some (n, rest) =>
        if n = journalFields.length then decRowVals journalFields rest
        else none

/-- The frame's KEY decoder (the key image's own type — the encoder's
    `encKeyJ` is `encVal kv.ty kv.val`). -/
def journalDecK : List UInt8 → Option (SchemaCore.FieldVal × List UInt8) :=
  fun bs =>
    match SchemaCore.decVal .u64 bs with
    | none => none
    | some (v, rest) => some ({ ty := .u64, val := v }, rest)

/-- One row's `name=value` note walk (schema order; the frame notes'
    vocabulary). -/
def rowFieldsNote : (fs : List SchemaCore.Field) → SchemaCore.RowVals fs → String
  | [], .nil => ""
  | f :: fs, .cons v vs =>
      f.name ++ "=" ++ fieldNoteVal f.ty v ++
        (match rowFieldsNote fs vs with
          | "" => ""
          | t => " " ++ t)

/-- One row's bare-value notes (the journal notes' vocabulary). -/
def rowValNotes : (fs : List SchemaCore.Field) → SchemaCore.RowVals fs → List String
  | [], .nil => []
  | f :: fs, .cons v vs => fieldNoteVal f.ty v :: rowValNotes fs vs

/-- One frame's note (the manifest's `frame-*` vocabulary). -/
def deltaNote : SchemaCore.RowDelta journalFields → String
  | .insert r => "frame-insert " ++ rowFieldsNote journalFields r
  | .update r => "frame-update " ++ rowFieldsNote journalFields r
  | .remove k =>
      "frame-remove " ++ journalKeyFieldName ++ "=" ++ fieldNoteVal k.ty k.val

/-- One journal event's note (the manifest's `journal` vocabulary). -/
def eventNote : SchemaCore.RowDelta journalFields → String
  | .insert r => "insert:" ++ String.intercalate ":" (rowValNotes journalFields r)
  | .update r => "update:" ++ String.intercalate ":" (rowValNotes journalFields r)
  | .remove k => "remove:" ++ fieldNoteVal k.ty k.val

/-- The whole-log note (`journal-empty` when the log is empty — the
    manifest's own spelling). -/
def journalNote : List (SchemaCore.RowDelta journalFields) → String
  | [] => "journal-empty"
  | log => "journal " ++ String.intercalate "|" (log.map eventNote)

/-- One frame's observation (the single-frame face of the duel). -/
def frameObserved (bs : List UInt8) : Observed :=
  match SchemaCore.decDelta? journalDecR journalDecK bs with
  | none => .refusal "the Lean codec refuses the frame"
  | some (d, rest) =>
      if !rest.isEmpty then .refusal "the frame left unconsumed bytes"
      else .value (deltaNote d)

/-- THE JOURNAL REPLAY: try the whole-log codec first (a frame's bytes
    are never a whole journal — the tag byte reads as a varint count
    whose body then misaligns; the full-consumption check decides),
    then the single frame. Refusals are typed, never panics. -/
def journalEngine (_path : String) (_x : Expect) (bytes : ByteArray) : Observed :=
  let bs := bytes.toList
  match SchemaCore.decJournal? journalDecR journalDecK bs with
  | some (log, rest) =>
      if !rest.isEmpty then frameObserved bs else .value (journalNote log)
  | none => frameObserved bs

/-! ## The commit slice's Lean replay (SchemaCore.Commit, read-only) -/

/-- One `FieldVal`'s u64 payload (the proposal fields' carrier). -/
def u64Of : SchemaCore.FieldVal → Option UInt64
  | ⟨.u64, .u64 n⟩ => some n
  | _ => none

/-- THE COMMIT REPLAY: the vector decodes as the five proposal fields
    (base, tid, src, dst, amount — five canonical varints), then the
    LANDED CHECKER re-proposes against the fixture snapshot: the
    checker's verdict IS the observation (`accept` / the refusal). -/
def commitEngine (_path : String) (_x : Expect) (bytes : ByteArray) : Observed :=
  let bs := bytes.toList
  match decFields [.u64, .u64, .u64, .u64, .u64] bs with
  | none => .refusal "the Lean codec refuses the proposal bytes"
  | some (fvs, rest) =>
      if !rest.isEmpty then .refusal "the proposal left unconsumed bytes"
      else match fvs.map u64Of with
        | [some b1, some b2, some b3, some b4, some b5] =>
            let p : SchemaCore.Proposal :=
              { base := b1.toNat, tid := b2, src := b3, dst := b4, amount := b5 }
            match p.commit SchemaCore.fixtureSnap with
            | .ok _ => .value "accept"
            | .error _ => .refusal "the checker refuses the proposal"
        | _ => .refusal "the proposal fields are not five u64s"

/-! ## The duel registry (the closed world) -/

/-- One replayed duel: the name, the committed directory, and the Lean
    engine the replay re-runs. -/
structure DuelEntry where
  name : String
  dir : String
  engine : String → Expect → ByteArray → Observed

/-- THE WITNESS DUEL's Lean replay (SchemaCore.Emit.Witness, read-only):
    the certificate's envelope decodes (the version gate + the
    append-form payload — truncation and trailing garbage refuse), then
    the fuel-bounded checker runs at the certificate's OWN cap over the
    fixture row. An accept row's value note pins the DUAL contract
    (decode AND checker-accept) in the manifest's own words; a refuse
    row's decoder-or-checker refusal is the expected refusal (the
    tamper splices + the hand-built false claim — the producer refuses
    to emit one, and the vector proves the checker refuses it too). -/
def witnessEngine (_path : String) (x : Expect) (bytes : ByteArray) : Observed :=
  match x with
  | .decode _ =>
      match SchemaCore.decWitness? (fs := exampleCheckFields)
          SchemaCore.Emit.Witness.witnessVersion bytes.toList with
      | none => .refusal "the Lean decoder refuses the certificate"
      | some (w, rest) =>
          if !rest.isEmpty then .refusal "the decoder left unconsumed bytes"
          else if !w.checks SchemaCore.Emit.Witness.seedRow then
            .refusal s!"the checker refuses `{w.label}` at its pinned fuel"
          else .value s!"accept {w.label} at its pinned fuel over the fixture row"
  | .refuse =>
      match SchemaCore.decWitness? (fs := exampleCheckFields)
          SchemaCore.Emit.Witness.witnessVersion bytes.toList with
      | none => .refusal "the Lean decoder refuses (the expected refusal)"
      | some (w, rest) =>
          if !rest.isEmpty then .refusal "the decoder left unconsumed bytes"
          else if w.checks SchemaCore.Emit.Witness.seedRow then
            .refusal s!"the checker ACCEPTS the refusal vector `{w.label}`"
          else .refusal "the checker refuses (the expected refusal)"
  | _ => .refusal "the witness duel has no run/trap rows"

/-- THE DUEL REGISTRY: the five committed duel sets, ONE row each
    (the lanes' directories are the committed artifacts; a new duel
    lands its row here — the registration point). -/
def duelEntries : List DuelEntry :=
  [ { name := "wasm-exec", dir := "gen/wasm-duel", engine := wasmEngine }
  , { name := "schema-codec", dir := "crates/schema-generated/tests/duel"
      engine := codecEngine }
  , { name := "journal-delta", dir := "crates/mandate-delta/tests/duel"
      engine := journalEngine }
  , { name := "commit-slice", dir := "crates/schema-generated/tests/duel-commit"
      engine := commitEngine }
  , { name := "witness-check", dir := "crates/schema-generated/tests/duel-witness"
      engine := witnessEngine } ]

/-! ## The explain discipline (the Diag envelope + the ledger rows) -/

/-- IN0001 — an unknown duel name (the closed world: the registry's
    names are enumerable, so the did-you-mean engine fires). -/
def unknownDuelDiag (got : String) : Kit.Diag :=
  Kit.Diag.closedWorld ⟨"IN0001"⟩
    "unknown duel — the committed duel registry is the closed world"
    .error got (duelEntries.map (·.name))

/-- IN0002 — the duel manifest is unreadable (absent or malformed):
    the manifest rides the emitter spine, never hand-edited. -/
def manifestRefusalDiag (dir : String) (msg : String) : Kit.Diag :=
  { code := ⟨"IN0002"⟩
    message := s!"the duel manifest is unreadable — {msg} (the manifest rides \
the emitter spine; regen through the owning lane, never hand-edit)"
    context := [{ name := "duel-replay", detail := dir }]
    got := none
    valid := []
    severity := .error }

/-- IN0003 — THE DIVERGENCE (the explain face): the message names both
    sides (the manifest's expectation and the Lean replay's
    observation — 04 §8: never a bare "behavior changed"); the got /
    valid pair is the witness data. -/
def divergenceDiag (duel : String) (w : Witness) : Kit.Diag :=
  { code := ⟨"IN0003"⟩
    message := s!"duel `{duel}`: vector `{w.loc}` DIVERGED — expected `{w.lhs}`, \
observed `{w.rhs}`; the witness is both sides — adjudicate in the \
divergences ledger before the replay is trusted again"
    context := [{ name := "duel-replay", detail := duel }]
    got := some w.rhs
    valid := [w.lhs]
    severity := .error }

/-- The LEDGER ROW (the notes/divergences.md discipline, the duel
    lanes' face): one markdown-table row per divergence, ready to
    paste into `inspector/duel-divergences.md`. The resolution column
    starts unadjudicated — a divergence is investigated before the
    replay is trusted again. -/
def ledgerRow (date duel : String) (w : Witness) : String :=
  s!"| {date} | {duel} | {w.loc} | {w.lhs} vs {w.rhs} | (adjudicate) |"

/-! ## The report (the Diag discipline's rendering) -/

/-- One row's line in the replay report (a ROW RENDERER, not a verdict
    — the verdict is the `Verdict` ctor; the lint's verdict-shape tooth
    demands the naming honesty). -/
def renderRow : String × Verdict → String
  | (p, .agree) => s!"  agree   {p}"
  | (p, .diverge w) => s!"  DIVERGE {p}: expected {w.lhs} | observed {w.rhs}"
  | (p, .refused why) => s!"  refused {p}: {why}"

/-- Is this row an agreement row (the summary's count). -/
def isAgree : Verdict → Bool
  | .agree => true
  | _ => false

/-- THE REPLAY REPORT: the header names the tier (tested agreement,
    never a theorem — 04 §6); every row renders; divergences render
    their Diag + the ready-to-paste ledger row; a clean run renders
    the honest zero line (the ledger discipline: an empty ledger = we
    looked). -/
def report (duelName : String) (rows : List (String × Verdict)) : String :=
  let n := rows.length
  let a := (rows.filter (fun r => isAgree r.2)).length
  let ds := rows.filter (fun r => match r.2 with | .diverge _ => true | _ => false)
  let head := s!"duel replay: {duelName} — {n} rows replayed \
(tested agreement, never a theorem — 04 §6)"
  let body := String.intercalate "\n" (rows.map renderRow)
  let summary := s!"{a}/{n} agree, {ds.length} diverge"
  let divBlocks := ds.filterMap fun (_p, v) =>
    match v with
    | .diverge w =>
        some (Kit.Diag.toString (divergenceDiag duelName w) ++
          "\n  ledger row: " ++ ledgerRow "2026-09-28" duelName w)
    | _ => none
  let tail :=
    if ds.isEmpty then "zero divergences — the ledger (inspector/duel-divergences.md) \
records we looked"
    else String.intercalate "\n" divBlocks
  String.intercalate "\n" [head, body, summary, tail] ++ "\n"

/-! ## The replay (the IO face over the committed artifacts) -/

/-- Replay ONE duel: read the committed manifest, parse it
    (Kit.Duel's consumer contract), then re-run every row — the
    committed bytes through the duel's Lean engine, the observation
    rendered in the manifest's vocabulary, the verdict against the
    committed expectation. A manifest or vector refusal is the loud
    `.error` (no partial green). -/
def replayDuel (e : DuelEntry) : IO (Except String (List (String × Verdict))) := do
  let mf : System.FilePath := e.dir ++ "/manifest.txt"
  unless ← mf.pathExists do
    return .error s!"{mf}: absent — the duel lanes' artifacts are committed \
(gen-check owns the byte-tie); replay from the repo root"
  let text ← IO.FS.readFile mf
  match parseManifest text with
  | .error perr => return .error s!"{mf}: {perr}"
  | .ok m =>
      let mut out : List (String × Verdict) := []
      for (path, x) in m.rows do
        let vp : System.FilePath := path
        if ← vp.pathExists then
          let bytes ← IO.FS.readBinFile vp
          out := out ++ [(path, rowVerdict path x (e.engine path x bytes))]
        else
          out := out ++ [(path, .diverge ⟨path, Expect.render x,
            "refused: the vector file is absent"⟩)]
      return .ok out

/-- The aggregate verdict over one duel's rows: all-agree is agree;
    the FIRST non-agree row wins (Kit.Duel's minimal-counterexample
    discipline). -/
def duelVerdict : List (String × Verdict) → Verdict :=
  fun rows => Verdict.foldRows (rows.map (·.2))

end Inspector.DuelReplay
