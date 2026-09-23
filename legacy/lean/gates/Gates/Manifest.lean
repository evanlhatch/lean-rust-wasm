/-
# Gates.Manifest — the manifest-drift gate (`gates manifest-check`)

Closes the review-flagged "manifest drift" robustness gap:
every `lean/*/lake-manifest.json` must agree with its lakefile.

MECHANISM (documented per the work order — Lake has no `update
--dry-run`, and a real `lake update` re-resolves branch/tag inputRevs
against the network, so "what `lake update` would produce" is not a
pure function of the tree — e.g. LeanSearchClient rides `inputRev:
"main"`, where `lake update` would ALWAYS move the rev). What this gate
checks instead is the DRIFT CLASS the review named — lakefile edited,
manifest stale — deterministically and offline:

1. every `[[require]]` in lakefile.toml has exactly one NON-inherited
   entry in lake-manifest.json (same `name`);
2. git requires: the manifest's `inputRev` equals the lakefile's `rev`
   string verbatim, and when the pin is a full 40-hex sha the resolved
   `rev` must equal it (for a tag/branch pin the resolved rev is
   checked against the actual checkout instead — next rule);
3. checkout consistency: when `.lake/packages/<name>/.git` exists, the
   checkout's HEAD must equal the manifest's `rev` (catches a manifest
   edited past its materialized deps — the reverse direction of 2);
4. path requires: the manifest entry is `"type": "path"` with the same
   `dir`;
5. reverse coverage: every non-inherited manifest entry names a
   lakefile require (a dropped require must not leave a zombie entry).

The lakefile parser is deliberately NOT a TOML parser: it reads only
the `[[require]]` block shapes this repo writes. The SHAPES are one
`TextKit.Grammar` value each (the T1 lane — `Shape.header`, the four
`key = "…"` key lines, the generic any-key line), recognized over the
`TextKit.Parser` monad by `Grammar.pOfLift`; an in-block line matching
NO shape fails the parse loudly via the Diag lane (the T2 lane:
`labels`-tagged expectations + `farthestFailure` + `renderDiag`),
never silently skipped (see the parser section's shape contract). The
parser stays the cheapest module to rebuild: TextKit is import-free
below `TextKit.Basic`, so new imports cost nothing beyond it.

Pure stdlib + Lean core (Lean.Json) + TestKit.Baseline + the TextKit
lanes (T1 Grammar, T2 Diag) — the machine-driven routing (F3) lives in
the coverage gate's lane, not here.

F2: the gate is ONE Baseline record (the doctrine). The audited artifact
is the root `lake-manifest.json`; `regenerate` runs the structural audit
and renders its finding text; `compare` judges the finding text (empty =
the agreement holds) — the COMPUTED-gate pattern in TestKit.Baseline's
header. There is deliberately NO re-baseline lane: the agreement is
computed from the tree every run, nothing is committed to write over
(`write` refuses).
-/
import Lean
import TestKit.Baseline
import TextKit.Grammar
import TextKit.Diag

open TextKit

namespace Gates.Manifest

/-- One parsed `[[require]]` block. -/
structure Require where
  name : String
  git : Option String := none
  rev : Option String := none
  path : Option String := none
  deriving Inhabited

/-! ## the require-block line grammar (the `Grammar`-lane conversion)

The lakefile's `[[require]]` blocks are the rigid line shapes this repo
writes — ONE Grammar value per shape, recognized over the `TextKit.Parser`
monad by `Grammar.pOfLift` (the T1 lane):

- `Shape.header`   — `[[require]]` (the block opener, byte-exact);
- `Shape.keyLine k`— `k = "v"` for the four known keys (the fixed
  skeleton `k = "` + closing `"` are TOKENS; the VALUE is the `scanTo
  '"'` gap — consumed, never emitted — so the consumer reads it from
  the input between the tokens, the `scanTo` consumer-side reading the
  Grammar module documents);
- `Shape.anyLine`  — the generic `key = "v"` shape (the unknown-key
  lane the old parser silently ignored). Consumed directly (never
  GWF-checked: `scanTo` sits in a `seq` position — the documented
  exclusion; the shape is applied, not gated).

The OUTER loop stays the line split (`splitOn "\n"`): a line is the
format's physical unit — the scanner fact, not a Grammar construct. The
Grammar owns each line's SHAPE; the loop owns the block bookkeeping.

Diagnostics ride the Diag lane: a line matching no shape is the loud
error (the old text, preserved verbatim) PLUS the farthest-failure
render (`Diag.labels`-tagged expectations + `farthestFailure` +
`renderDiag`) — the expected shape the line almost satisfied.

Shape contract (documented divergence from the old split-`" = "`-plus-
`unquote` parser): the shapes require the literal `key = "v"` spelling
— the ONLY spelling this repo's lakefiles write (every value quoted,
none containing a quote). A value containing `" = "` — which the old
split ERRORS on (>2 parts) — now PARSES (the value runs to the closing
quote; the TOML truth). The silent-ignore surface (blank, `#`,
non-require `[…]` sections, unknown-key `key = "v"` lines) is
unchanged. -/

namespace Shape

/-- The require-block header line, byte-exact. -/
def header : Grammar.Grammar := Grammar.Grammar.tok "[[require]]"

/-- The opening token of a keyed value line (`key = "`). -/
def keyOpen (key : String) : String := s!"{key} = \""

/-- One keyed value line: `key = "v"` — the fixed skeleton as tokens,
    the value as the `scanTo` gap. -/
def keyLine (key : String) : Grammar.Grammar :=
  Grammar.Grammar.seq
    [ Grammar.Grammar.tok (keyOpen key)
    , Grammar.Grammar.scanTo '"'
    , Grammar.Grammar.tok "\"" ]

/-- The GENERIC `key = "v"` line (any key) — the unknown-key lane.
    (`scanTo` in `seq` position: consumer-side only, see the section
    header.) -/
def anyLine : Grammar.Grammar :=
  Grammar.Grammar.seq
    [ Grammar.Grammar.scanTo ' '
    , Grammar.Grammar.tok " = \""
    , Grammar.Grammar.scanTo '"'
    , Grammar.Grammar.tok "\"" ]

end Shape

/-- The value a `key = "v"` recognition consumed: the chars between the
    opening token and the closing quote, read from the input between
    the tokens (`scanTo` records no payload — the consumer reads the
    gap; the Grammar module's documented consumer lane). -/
def gapOf (openTok : List Char) (cs rest : List Char) : String :=
  String.ofList (cs.drop openTok.length |>.take ((cs.length - rest.length) - openTok.length - 1))

/-- The length of the common prefix of `cs` with the shape token `tok`:
    how far the recognition got before failing (the failure point's
    depth — the farthest-failure lane's position source). -/
def prefixDepth (tok : List Char) (cs : List Char) : Nat :=
  (cs.zip tok).takeWhile (fun (a, b) => a == b) |>.length

/-- Recognize one known key line over the Grammar lane: the value when
    the shape matched. -/
def lineValue (key : String) (line : String) : Option String :=
  match Grammar.pOfLift (Shape.keyLine key) line.toList with
  | none => none
  | some (_, rest) => some (gapOf (Shape.keyOpen key).toList line.toList rest)

/-- One key shape on the Diag lane, LABELED: a failure records ITS OWN
    (deepest) point — the remaining length at the `key = "` common-
    prefix depth — and `DParser.labels` re-tags the deepest failure's
    expected set with the shape spelling. -/
def keyD (key : String) : Diag.DParser (String × String) :=
  Diag.DParser.labels s!"expected '{key} = \"…\"'"
    (fun cs => match Grammar.pOfLift (Shape.keyLine key) cs with
      | some (_, rest) => (some ((key, gapOf (Shape.keyOpen key).toList cs rest), rest), [])
      | none => (none, [(cs.length - prefixDepth (Shape.keyOpen key).toList cs, [])]))

/-- The generic shape on the Diag lane, LABELED (the unknown-key
    lane's expectation). -/
def anyD : Diag.DParser (String × String) :=
  Diag.DParser.labels "expected 'KEY = \"…\"'"
    (fun cs =>
      let run := cs.takeWhile (fun c => c != ' ')
      match Grammar.pOfLift Shape.anyLine cs with
      | some (_, rest) => (some (("", String.ofList run), rest), [])
      | none =>
          let depth := run.length + prefixDepth (" = \"").toList (cs.drop run.length)
          (none, [(cs.length - depth, [])]))

/-- The full line recognizer on the Diag lane: the four key shapes plus
    the generic shape, every failure's record MERGED (the farthest-
    failure union). Success = the first shape that matched (dispatch
    order: the old if-chain's). The instrumented lane is the module's
    `labels`/`farthestFailure`/`renderDiag` consumer — the error path's
    diag source (real lakefiles never reach it). -/
def shapeD : Diag.DParser (String × String) := fun cs =>
  let rec go : List (Diag.DParser (String × String)) →
        List (Nat × List String) →
        Option ((String × String) × List Char) × List (Nat × List String)
    | [], acc => (none, acc)
    | p :: ps, acc =>
        let (r, d) := p cs
        match r with
        | some _ => (r, d)
        | none => go ps (Diag.merge acc d)
  go [keyD "name", keyD "git", keyD "rev", keyD "path", anyD] []

/-- An in-block line matching NO shape: the loud error — the old text
    verbatim, plus the farthest labeled expectation the line almost
    satisfied (the Diagnostic's render, position = the furthest the
    shapes got into the line). -/
def parseError (lineNo : Nat) (l : String) : String :=
  s!"line {lineNo}: unparseable line inside [[require]]: '{l}' "
    ++ "(" ++ Diag.renderDiag lineNo (Diag.farthestFailure shapeD l.toList) ++ ")"

/-- Parse the `[[require]]` blocks of a lakefile.toml (the repo's rigid
    shape only — Grammar lane per line, Diag lane for the loud error;
    see the section header). `.error` = a line inside a require block
    no shape matches. -/
def parseRequires (lakefile : String) : Except String (List Require) := Id.run do
  let mut reqs : List Require := []
  let mut cur : Option Require := none
  let mut lineNo : Nat := 0
  for line in lakefile.splitOn "\n" do
    lineNo := lineNo + 1
    let l := line.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    if l.startsWith "[" then
      if let some r := cur then reqs := r :: reqs
      -- the require opener exactly, byte-exact via the Grammar; any
      -- other `[…]` section closes the block without opening
      cur := match Grammar.pOfLift Shape.header l.toList with
        | some (_, []) => some { name := "" }
        | _ => none
      continue
    if let some r := cur then
      match lineValue "name" l with
      | some v => cur := some { r with name := v }
      | none => match lineValue "git" l with
        | some v => cur := some { r with git := some v }
        | none => match lineValue "rev" l with
          | some v => cur := some { r with rev := some v }
          | none => match lineValue "path" l with
            | some v => cur := some { r with path := some v }
            | none => match Grammar.pOfLift Shape.anyLine l.toList with
              | some _ => continue   -- unknown key: the old silent-ignore lane
              | none => return .error (parseError lineNo l)
  if let some r := cur then reqs := r :: reqs
  return .ok reqs.reverse

/-- One manifest package entry (the fields this gate reads). -/
structure Entry where
  name : String
  type : String
  rev : Option String
  inputRev : Option String
  dir : Option String
  inherited : Bool

def parseManifest (text : String) : Except String (List Entry) := do
  let j ← Lean.Json.parse text
  let pkgs ← j.getObjVal? "packages"
  let arr ← match pkgs with | .arr a => .ok a | _ => .error "packages is not an array"
  arr.toList.mapM fun p => do
    let get? (k : String) : Except String (Option String) :=
      match p.getObjVal? k with
      | .ok (.str s) => .ok (some s)
      | .ok .null => .ok none
      | .error _ => .ok none
      | _ => .error s!"entry: field '{k}' is not a string"
    let inh ← match p.getObjVal? "inherited" with
      | .ok (.bool b) => .ok b
      | _ => .error "entry: missing 'inherited'"
    return { name := ← p.getObjVal? "name" >>= (·.getStr?)
           , type := (← get? "type").getD "git"
           , rev := ← get? "rev"
           , inputRev := ← get? "inputRev"
           , dir := ← get? "dir"
           , inherited := inh }

def isSha (s : String) : Bool :=
  s.length == 40 && s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- The checkout's HEAD, when the dep is materialized (`none` when not —
    an unmaterialized dep is not drift; the first `lake build` fetches
    it, pinned by the manifest rev). -/
def checkoutHead (pkgDir : System.FilePath) (name : String) : IO (Option String) := do
  let depDir := pkgDir / ".lake" / "packages" / name
  unless ← (depDir / ".git").pathExists do return none
  let out ← IO.Process.output
    { cmd := "git", args := #["-C", depDir.toString, "rev-parse", "HEAD"] }
  if out.exitCode == 0 then return some out.stdout.trimAscii.toString
  return none

structure Finding where
  pkg : String
  msg : String

/-- Check one package dir (a `lean/<pkg>` with a lakefile.toml). -/
def checkPkg (dir : System.FilePath) (pkg : String) : IO (Array Finding) := do
  let mut findings : Array Finding := #[]
  let lakefileText ← IO.FS.readFile (dir / "lakefile.toml")
  let reqs ← match parseRequires lakefileText with
    | .ok rs => pure rs
    | .error e =>
      return #[⟨pkg, s!"lakefile.toml: {e}"⟩]
  let manifestText ← IO.FS.readFile (dir / "lake-manifest.json")
  let entries ← match parseManifest manifestText with
    | .ok es => pure es
    | .error e => return #[⟨pkg, s!"lake-manifest.json: {e}"⟩]
  let own := entries.filter (!·.inherited)
  -- rules 1, 2, 4 (require → manifest)
  for r in reqs do
    match own.filter (·.name == r.name) with
    | [] => findings := findings.push ⟨pkg, s!"require '{r.name}' has no manifest entry — run `lake update`"⟩
    | [e] =>
      match r.git, r.path with
      | some _, none =>
        if e.type != "git" then
          findings := findings.push ⟨pkg, s!"require '{r.name}': lakefile says git, manifest says {e.type}"⟩
        if let some rev := r.rev then
          if e.inputRev != some rev then
            findings := findings.push ⟨pkg, s!"require '{r.name}': lakefile rev '{rev}' ≠ manifest inputRev '{e.inputRev.getD "∅"}' — stale manifest"⟩
          if isSha rev && e.rev != some rev then
            findings := findings.push ⟨pkg, s!"require '{r.name}': lakefile pinned sha {rev} but manifest resolved '{e.rev.getD "∅"}'"⟩
        -- rule 3 (checkout consistency)
        if let some head ← checkoutHead dir r.name then
          if let some mrev := e.rev then
            if head != mrev then
              findings := findings.push ⟨pkg, s!"require '{r.name}': checkout HEAD {head.take 12}… ≠ manifest rev {mrev.take 12}…"⟩
      | none, some p =>
        if e.type != "path" || e.dir != some p then
          findings := findings.push ⟨pkg, s!"require '{r.name}': lakefile path '{p}' ≠ manifest (type {e.type}, dir '{e.dir.getD "∅"}')"⟩
      | _, _ =>
        findings := findings.push ⟨pkg, s!"require '{r.name}': neither/extra of git= and path= set"⟩
    | _ :: _ :: _ =>
      findings := findings.push ⟨pkg, s!"require '{r.name}': multiple manifest entries"⟩
  -- rule 5 (manifest → require)
  for e in own do
    unless reqs.any (·.name == e.name) do
      findings := findings.push ⟨pkg, s!"manifest entry '{e.name}' has no lakefile require — zombie, run `lake update`"⟩
  return findings

/-- The full audit (single-lake): ONE root lakefile.toml ↔
    lake-manifest.json, plus NO stray per-package lakefiles/manifests
    under lean/ (a stray = an un-absorbed package — the inventory rule's
    successor). Run from lean/gates (`../..` = the repo root). -/
def checkAll : IO (Array Finding) := do
  let root : System.FilePath := "../.."
  let mut findings ← checkPkg root "LeanRoot"
  for entry in ← (root / "lean").readDir do
    unless ← entry.path.isDir do continue
    if ← (entry.path / "lakefile.toml").pathExists then
      findings := findings.push ⟨entry.fileName,
        "stray lakefile.toml — the package was never absorbed (single-lake: the root owns all targets)"⟩
    if ← (entry.path / "lake-manifest.json").pathExists then
      findings := findings.push ⟨entry.fileName,
        "stray lake-manifest.json — dead pre-monolith artifact (delete it)"⟩
  return findings

/-- The manifest gate as ONE Baseline record (see the module header). -/
def manifestBaseline : IO TestKit.Baseline := do
  let findings ← checkAll
  let report := String.intercalate "\n"
    (findings.toList.map fun f => s!"{f.pkg}: {f.msg}")
  pure { path := "../../lake-manifest.json"
       , regenerate := pure report
       , compare := fun _ fresh => fresh == ""
       , write := fun _ =>
           throw (IO.userError "manifest-check is structural + offline — the \
             agreement is computed from the tree every run, never re-baselined")
       , evidence := "lakefile require ↔ manifest entry/rev/checkout agreement \
           (structural, offline)"
       , name := "manifest-check" }

/-- The gate: the findings print first (the gate's log), then the shared
    verdict loop over the one baseline (C5: run → verdict → count). -/
unsafe def run : IO UInt32 := do
  let base ← manifestBaseline
  let report ← base.regenerate
  if !report.isEmpty then IO.println report
  TestKit.runBaselines "manifest-check" TestKit.computedVerdict [base]

end Gates.Manifest
