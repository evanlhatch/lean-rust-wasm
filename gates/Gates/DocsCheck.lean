/-
Gates.DocsCheck — the notes excerpt-drift gate (`gates docs-check`;
mined from legacy/lean/gates/Gates/DocsCheck.lean). Our `notes/` carry
Lean code fences that can silently rot — a fence naming a decl that no
longer exists (or never did) fails here. MINIMAL and true, by design:

(a) Every ```lean fence in `notes/*.md` (and one level of
    subdirectories — the doctrine sets live there) must have its
    DECLARED top-level names (theorem/def/abbrev/instance/structure/
    class/inductive/opaque, after the usual modifiers) RESOLVE in the
    gated tree's environment — resolved by the constant's LAST component
    (notes habitually write short names).
(b) `path:line` citations and inline `Name.path` references are
    deliberately NOT checked (the honest subset is (a); adding (b)
    without a real citation convention would be a false-positive
    machine).
(c) THE GATE-ROW HONESTY SCAN (the D33 durable fix): every module
    header may state a five-questions gate row (01-core's fifth
    question); the claims that say a library is OUTSIDE the gated set
    are checked against `Gates.Packages` — a claim of the form
    `<Lib> is outside …` / `<Lib> is not [yet] in … (gated) set`
    naming a library that HAS a gated row is a finding (the
    header-corrections wave's class: 20+ headers claimed their
    package was ungated after `gates packages-check` gated them).
    The covered forms are the observed ones, exactly: subject token
    before `is outside` / `is not in` / `is not yet in` (backstepping
    over `itself`), the subject being the claimed-outside library's
    name. Prose about fragments/tables ("the field type is outside
    the supported fragment") does not match — the subject must BE a
    gated library's name for the class to fire. EXCLUSION (named):
    `textkit` — the grammar-laws agent owns those headers' rot-fix
    (the Laws.lean citation landing); the exclusion lifts when that
    lands, and the same scan then covers textkit's headers.

THE MARKER CONVENTION: a fence of PROPOSED code (a statement shape, a
template, a migration sketch) tags itself on the open line:

    ```lean sketch

The fence — not a side list — is the truth about what is a sketch; an
unmarked fence CLAIMS to be real code, so its decl names must resolve.
Fences that declare no top-level names (a `#guard` probe, an anonymous
literal) trivially pass.

Requires `lake build` (the resolution imports the gated packages'
oleans — this gate never builds). Not a load-time gate: a package env
that fails to load is a FAILURE (an unloadable tree verifies nothing).

THE MEMORY SHAPE (revised — the deliberate in-process exclusion did not
survive measurement): resolution runs ONE CHILD PROCESS per gated
package (the Axioms shard discipline, `Gates.shardDispatch`), each
loading its package env in a fresh process and printing the pending
names that resolve there. The in-process shape this file first landed
with ("each env imported one at a time and dropped; RSS stays flat")
was wrong: libgc's conservative stack scan RETAINS every dropped env
(the legacy lesson, arrived again) — measured at a 27GB peak + an
earlyoom SIGTERM (exit 143) once the gated set grew past a handful of
packages. The child discipline bounds the peak at the heaviest single
env (~2GB); the pool rides the RSS admission like every other env
lane.

The five questions (notes/v3/01-core.md):
- root: none — the notes-drift gate + the headers' gate-row honesty
scan (both are text checks over the gated tree).
- carrier grade: none — name resolution over fences, not a crossing;
the gate-row scan is a token-level claim check against the Packages
table (Universe data), also no crossing.
- spine reading: the interpretation stage (notes fences → decl names →
resolution in the gated envs; header gate-row claims → the subject
library → membership in Gates.Packages).
- ladder rung: n/a (the honesty rule: an unmarked fence CLAIMS to be
real code — the marker convention is the declaration).
- gate row: the docs-check row itself (`gates docs-check`).
-/
import Lean
import Gates.Packages
import Gates.Common

open Lean

namespace Gates.DocsCheck

open Gates (PkgSpec gatedPackages loadPkgEnv)

/-! ## Fence scanning -/

/-- Whitespace trim (fence lines are short — the list round-trip is
    free). -/
def trimWs (s : String) : String :=
  String.ofList (s.toList.dropWhile Char.isWhitespace
    |>.reverse.dropWhile Char.isWhitespace
    |>.reverse)

/-- The top-level declaration keywords a fence's names are read from. -/
def declKeywords : Array String :=
  #["theorem", "def", "abbrev", "instance", "structure", "class",
    "inductive", "opaque"]

/-- Modifiers that may precede a declaration keyword (skipped when
    reading the decl line). -/
def declModifiers : Array String :=
  #["private", "protected", "noncomputable", "partial", "unsafe",
    "public", "recursive", "local", "meta", "sealed"]

def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '\''

/-- The identifier prefix of a token: `foo:` → `foo`, `(x` → "" —
    anonymous/invalid decl positions yield the empty string. -/
def identPrefix (tok : String) : String :=
  String.ofList (tok.toList.takeWhile isIdentChar)

/-- The declared name on one fence line, if any: strip the modifiers,
    expect a decl keyword, take the next token's identifier prefix.
    Anonymous positions (`instance : …`, `theorem {p : …}`) yield none. -/
def declName? (line : String) : Option String :=
  let toks := (trimWs line |>.splitOn " ").filter (· != "")
  let rec stripMods : List String → List String
    | t :: rest => if declModifiers.contains t then stripMods rest else t :: rest
    | [] => []
  match stripMods toks with
  | kw :: rest =>
    if declKeywords.contains kw then
      match rest with
      | n :: _ =>
        let name := identPrefix n
        match name.toList with
        | c :: _ => if c.isAlpha || c.isDigit || c == '_' then some name else none
        | [] => none
      | [] => none
    else none
  | [] => none

/-- One scanned lean fence. -/
structure Fence where
  /-- Notes-relative file name (as reported). -/
  file : String
  /-- 1-indexed open line of the fence. -/
  openLine : Nat
  /-- The fence tagged itself `sketch` (exempt from resolution). -/
  sketch : Bool
  /-- Fence body lines with their 1-indexed source line numbers. -/
  body : Array (Nat × String)
  /-- An open lean fence never closed is scanned but reported. -/
  unclosed : Bool := false

/-- Scan one markdown file's fences. Only fences tagged `lean` (optionally
    `lean sketch`) are kept; every other language's fences are ignored. -/
def scanFile (file : String) (path : System.FilePath) : IO (Array Fence) := do
  let text ← IO.FS.readFile path
  let mut out : Array Fence := #[]
  let mut cur : Option Fence := none
  for (line, i) in (text.splitOn "\n").zipIdx do
    let trimmed := trimWs line
    if trimmed.startsWith "```" then
      match cur with
      | some f =>
        -- closing fence (nested fences are not markdown)
        out := out.push { f with unclosed := false }
        cur := none
      | none =>
        -- open fence: the info string after the backtick run
        let stripped := String.ofList (trimmed.toList.dropWhile (· == '`'))
        let info := (trimWs stripped |>.splitOn " ").filter (· != "")
        if info.headD "" == "lean" then
          cur := some { file, openLine := i + 1, sketch := info.contains "sketch", body := #[] }
    else match cur with
      | some f => cur := some { f with body := f.body.push (i + 1, line) }
      | none => pure ()
  -- EOF inside a lean fence: keep it, flagged
  if let some f := cur then
    out := out.push { f with unclosed := true }
  return out

/-! ## Resolution -/

/-- A name's last component (`WasmBackend.Correct.tpl_add_ret_ok` →
    `tpl_add_ret_ok`) — notes write short names. -/
def lastComponent (n : Name) : Name :=
  match n with
  | .str _ s => .str .anonymous s
  | n => n

/-- The set of every constant's last component in one environment
    (a name resolves in this env iff its last component is here). -/
def envLeafNames (env : Environment) : NameSet :=
  env.constants.fold (fun acc n _ => acc.insert (lastComponent n)) {}

/-! ## The gate-row honesty scan (the D33 durable fix) -/

/-- One scanned token: its 1-indexed source line + the text. The
    gate-row claims SPAN LINES (the subject may sit on the line
    before `is not in … gated set`), so tokens carry their line. -/
structure Tok where
  /-- 1-indexed source line. -/
  line : Nat
  /-- The token text. -/
  tok : String
  deriving Inhabited

/-- Whole-text tokenization with line attribution (whitespace-split;
    the claims are comment prose — tabs do not occur). -/
def toksOf (text : String) : Array Tok :=
  ((text.splitOn "\n").zipIdx.flatMap fun (ln, i) =>
      ((ln.splitOn " ").filter (· != "")).map
        (fun t => Tok.mk (i + 1) t)).toArray

/-- Strip non-ident noise from a subject token: `` `Kit` `` → `Kit`.
    (The claims write the library bare — the stripping only makes the
    quoted/parenthesized forms harmless to accept.) -/
def cleanSubject (t : String) : String :=
  String.ofList
    ((t.toList.dropWhile fun c => !(c.isAlpha || c.isDigit || c == '_'))
      |>.takeWhile isIdentChar)

/-- The token at index `i`, as text (`none` past the end). -/
def tokAt? (toks : Array Tok) (i : Nat) : Option String :=
  match toks[i]? with
  | some t => some t.tok
  | none => none

/-- The gate-row claims in one file's text: `(line, lib)` pairs where
    the text claims `lib` is OUTSIDE the gated set (`is outside …` /
    `is not in …` / `is not yet in …`, subject = the token before
    `is`, backstepping over `itself`). Only claims whose subject IS a
    gated library's name fire upstream — the caller supplies the
    gated-name set. Pure + deterministic: the pins in GatesTests
    plant a false claim and demand exactly this output. -/
def gateRowClaims (gatedDirs : Array String) (text : String) :
    Array (Nat × String) := Id.run do
  let toks := toksOf text
  let mut out : Array (Nat × String) := #[]
  for i in [0:toks.size] do
    let t := toks[i]!
    let n1 := tokAt? toks (i + 1)
    let n2 := tokAt? toks (i + 2)
    let n3 := tokAt? toks (i + 3)
    let isClaim :=
      if t.tok != "is" then none
      else if n1 == some "outside" then some ()
      else if n1 == some "not" &&
          (n2 == some "in" || (n2 == some "yet" && n3 == some "in")) then
        some ()
      else none
    if isClaim.isNone then continue
    let prev : String := if i == 0 then "" else (tokAt? toks (i - 1)).getD ""
    let subRaw : String :=
      if prev == "itself" then
        (if i ≥ 2 then (tokAt? toks (i - 2)).getD "" else "")
      else prev
    let sub := cleanSubject subRaw
    if gatedDirs.contains sub then
      out := out.push (t.line, sub)
  return out

/-- The gate-row scan's SKIPPED directory names (named exclusions, per
    Packages.lean's convention): `.lake`/`.git`/`.jj` are build + VCS
    state (the `.`-srcDir rows must not walk the dependency cache);
    `legacy` is the read-only mining source (out of the gated scope by
    the mandate); `textkit` is the grammar-laws agent's zone (its
    headers' rot-fix — the Laws.lean citation — lands there; the
    exclusion lifts when that lands). Checked by BASE NAME, so the
    `.`-srcDir rows' walk honors them too. -/
def skippedDirNames : Array String :=
  #[".lake", ".git", ".jj", "legacy", "textkit"]

/-- Fuel-bounded recursive walk (the noNewPartial lint's discipline:
    no `partial` — the fuel bounds the depth, structurally; exhaustion
    is REPORTED upstream, never a silent truncation). Returns the
    .lean files + whether the fuel ran out. -/
def leanFilesUnder : Nat → System.FilePath →
    IO (Array System.FilePath × Bool)
  | 0, _ => return (#[], true)
  | fuel + 1, dir => do
    if !(← dir.pathExists) then return (#[], false)
    let mut files : Array System.FilePath := #[]
    let mut subdirs : Array System.FilePath := #[]
    for e in ← dir.readDir do
      if ← e.path.isDir then
        -- the skip is by BASE NAME (readDir entries under a `.`-srcDir
        -- carry the `./` prefix — a toString compare would miss them)
        if skippedDirNames.contains (e.path.fileName.getD "") then continue
        subdirs := subdirs.push e.path
      else if e.path.extension == some "lean" then
        files := files.push e.path
    let mut exhausted := false
    for d in subdirs do
      let (fs, ex) ← leanFilesUnder fuel d
      files := files ++ fs
      exhausted := exhausted || ex
    return (files, exhausted)

/-! ## The 08-status discipline made mechanical (B5) -/

/-- One parsed status row of the capability catalog's table
(`notes/v3/08-capabilities.md`): the section number, its status word,
the LANDED/PARTIAL citations (each MUST resolve — the landed scope
names a real declaration), and the SPEC/PARTIAL `pending` citations
each MUST NOT resolve (a resolution = the section landed and the row
is stale — the promotion is owed). A LANDED/PARTIAL row with no
citation is a finding (the row does not name its decl). -/
structure StatusRow where
  sec : Nat
  status : String
  landed : List String
  pending : List String
  deriving Inhabited

/-- The status table's file (the capability catalog). -/
def statusTablePath : System.FilePath := "notes/v3/08-capabilities.md"

/-- The backticked spans of one table cell (the citation form).
Non-identifier debris between the backticks is dropped. -/
def cellCitations (cell : String) : List String :=
  (cell.splitOn "`").zipIdx.filterMap fun (seg, i) =>
    if i % 2 == 1 && !seg.isEmpty &&
        (seg.toList.all isIdentChar || seg.toList.all (· == '.')) then
      some seg
    else none

/-- Parse the status table: the `| §N | STATUS | … |` rows. Pure so the
GatesTests pins can plant rows. -/
def parseStatusRows (text : String) : List StatusRow :=
  (text.splitOn "\n").filterMap fun line =>
    let cells := (line.splitOn "|").map trimWs
    match cells[1]? with
    | some secTok =>
        let secNum : String :=
          if secTok.startsWith "§" then (secTok.drop 1).toString else secTok
        if !(secNum.isEmpty) && (secNum.toList.all Char.isDigit) then
          match cells[2]? with
          | some status =>
              if status == "LANDED" || status == "PARTIAL" ||
                  status == "SPEC" || status == "WATCH" then
                some { sec := secNum.toNat?.getD 0
                       status
                       landed := match cells[3]? with
                         | some c => cellCitations c
                         | none => []
                       pending := match cells[4]? with
                         | some c => cellCitations c
                         | none => [] }
              else none
          | none => none
        else none
    | none => none

/-! ## The gate -/

/-- Display name for a scanned file: report `notes/<file>.md` (the
    repo-relative shape the notes cite). -/
def dispName (f : String) : String :=
  match f.dropPrefix? "notes/" with
  | some r => "notes/" ++ r
  | none => f

/-- The notes scan: the sorted .md file list + every scanned fence +
an ABSENT-notes error message (a total return, never a throw — the
child's face rides the same scan; the driver's face reports the error
as a finding). The driver's face AND the shard child's — the scan is
cheap, the notes tree is small, so the child RECOMPUTES its pending
set instead of plumbing it through argv. -/
def scanNotes : IO (Array System.FilePath × Array Fence × Option String) := do
  let notesDir : System.FilePath := "notes"
  if !(← notesDir.pathExists) then
    return (#[], #[], some s!"{notesDir} not found (run the exe from the repo root)")
  -- 1. scan (deterministic file order); ONE level of subdirectories
  --    (notes/v2/, notes/v3/ — the doctrine sets live there; a deeper
  --    tree is not expected)
  let mut files : Array System.FilePath := #[]
  let mut dirs : Array System.FilePath := #[notesDir]
  for e in ← notesDir.readDir do
    -- nested `if`s, NOT `&&` over monadic operands (the do-notation
    -- hoists every `←` out of `&&` eagerly)
    if ← e.path.isDir then dirs := dirs.push e.path
  for d in dirs do
    for e in ← d.readDir do
      if ← e.path.isDir then continue
      if e.path.extension == some "md" then
        files := files.push e.path
  files := files.qsort (fun a b => a.toString < b.toString)
  let mut fences : Array Fence := #[]
  for f in files do
    fences := fences ++ (← scanFile f.toString f)
  return (files, fences, none)

/-- The pending resolution set: (location, name) per non-sketch fence. -/
def pendingOfFences (fences : Array Fence) : Array (String × String) :=
  (fences.filter (fun f => !f.sketch)).flatMap fun f =>
    f.body.filterMap fun (ln, line) =>
      if (trimWs line).startsWith "--" then none
      else (declName? line).map fun n => (s!"{dispName f.file}:{ln}", n)

/-- ONE package's shard (the per-package process — the memory
discipline): the pending set recomputed from the same notes scan, THIS
package's env loaded in this fresh process, the pending names that
resolve printed one per line (the parent's machine face — the human
report stays the parent's). A load failure is the loud stderr line +
exit 1 (the parent collects the row); an empty pending set exits
clean without loading (the env is the only cost). -/
unsafe def runPkg (pkg : PkgSpec) : IO UInt32 := do
  let (_, fences, _) ← scanNotes
  -- the pending set = the fences' names + the 08-status table's
  -- citations (B5: the child recomputes BOTH — the same deterministic
  -- scan, nothing plumbed through argv)
  let statusRows : List StatusRow ← do
    if ← statusTablePath.pathExists then
      pure (parseStatusRows (← IO.FS.readFile statusTablePath))
    else pure []
  let statusNames : List String :=
    statusRows.flatMap fun r => r.landed ++ r.pending
  let pending :=
    pendingOfFences fences ++
      statusNames.map (fun n => (s!"08-status (child)", n))
  if pending.isEmpty then return 0
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  match ← loadPkgEnv base pkg with
  | .error e => do
    IO.eprintln s!"docs-check: LOAD FAILED — {pkg.dir}: {e} (run `just build` first)"
    return 1
  | .ok env =>
    let leaves := envLeafNames env
    for (_, n) in pending do
      if leaves.contains (lastComponent (String.toName n)) then
        IO.println n
    return 0

/-- Run the gate: scan the notes, resolve the pending decl names against
    the gated packages' environments — ONE CHILD PROCESS per package
    (the shard dispatch's pooled lanes; the memory shape in the header). -/
unsafe def run (package : Option String) : IO UInt32 := do
  let (files, fences, scanError) ← scanNotes
  -- 2. the pending resolution set: (location, name) per non-sketch fence
  let pending := pendingOfFences fences
  -- 3. resolve: ONE CHILD PROCESS per gated package (the shard
  --    dispatch — the memory discipline; the header's shape). Each
  --    child loads its env in a fresh process and prints the pending
  --    names that resolve there; the parent folds the resolved sets. A
  --    load failure is a gate failure — an unloadable tree verifies
  --    nothing — a collected loadError row with the `just build` hint
  --    (the honest-partiality rule: not `Gates.withPkgEnv`'s
  --    first-failure exit, not the combinator's shape).
  -- 4. THE 08-STATUS DISCIPLINE (B5): the capability catalog's status
  --    table — every LANDED/PARTIAL row's citations resolve (the landed
  --    scope names a real decl, resolved against the SAME gated envs as
  --    the fences); every SPEC/PARTIAL `pending` citation must NOT
  --    resolve (a resolution = the section landed; the promotion is
  --    owed). The citations join the pending set (the same shard
  --    machinery, one env walk).
  let statusRows : List StatusRow ← do
    if ← statusTablePath.pathExists then
      pure (parseStatusRows (← IO.FS.readFile statusTablePath))
    else pure []
  -- the parent's `pending` stays the FENCES' names (the unresolved-fence
  -- report's face); the status citations resolve in the children only
  -- (runPkg recomputes both) and are judged against `resolvedAll` below
  Gates.shardDispatch "docs-check" package runPkg fun outs => do
    let mut loadErrors : Array String := #[]
    let mut resolvedAll : Array String := #[]
    -- `outs` is in the input order (the gatedPackages order)
    for (pkg, (code, text)) in gatedPackages.zip outs do
      if code != 0 then
        loadErrors := loadErrors.push
          s!"{pkg.dir}: the shard's env load failed (its loud LOAD FAILED \
            line is on stderr; run `just build` first)"
      resolvedAll := resolvedAll ++
        (text.splitOn "\n").filter (· != "")
    let pending := pending.filter fun (_, n) => !resolvedAll.contains n
    -- the status rows' verdicts (the gate reads the RESOLVED set —
    -- a citation that resolved is gone from `pending`)
    let mut statusFindings : List String := []
    for r in statusRows do
      match r.status with
      | "LANDED" | "PARTIAL" =>
          if r.landed.isEmpty then
            statusFindings := statusFindings ++
              [toString (GateDiag eGT0009
                s!"docs-check: 08-status §{r.sec}: the {r.status} row names \
                  NO declaration — a landed scope cites its decl (the \
                  status discipline is mechanical: the row's citation is \
                  the gate's resolution target)")]
          for n in r.landed do
            unless resolvedAll.contains n do
              statusFindings := statusFindings ++
                [toString (GateDiag eGT0009
                  s!"docs-check: 08-status §{r.sec}: the {r.status} row \
                    cites '{n}' — no such declaration in the tree's env \
                  (the landed scope's citation must resolve; repair the \
                  row or the lane)")]
      | "SPEC" =>
          for n in r.pending do
            if resolvedAll.contains n then
              statusFindings := statusFindings ++
                [toString (GateDiag eGT0010
                  s!"docs-check: 08-status §{r.sec}: the SPEC row's \
                    pending decl '{n}' RESOLVES — the section landed; \
                  promote the row (a SPEC entry that lands moves to \
                  LANDED in the same commit)")]
      | _ => pure ()  -- WATCH: one line + its trigger; no decl to check
    -- 5. the gate-row honesty scan (D33): every gated srcDir's .lean
    --    files' "outside the gated set" claims, checked against the
    --    table (textkit's exclusion is the named one above).
    let gatedDirs := gatedPackages.map (·.dir)
    -- ONE deduped file set (rows share srcDirs; the `.`-srcDir rows
    -- overlap every tree dir — each file is scanned once, in sorted
    -- order for a deterministic report). Walk fuel 16: far beyond any
    -- real srcDir's depth; exhaustion is a REPORTED finding, never a
    -- silent truncation.
    let walkFuel := 16
    let mut walkExhausted := false
    let mut gateRowFiles : Array String := #[]
    for pkg in gatedPackages do
      if skippedDirNames.contains pkg.srcDir then continue
      let (fs, ex) ← leanFilesUnder walkFuel pkg.srcDir
      walkExhausted := walkExhausted || ex
      for f in fs do
        unless gateRowFiles.contains f.toString do
          gateRowFiles := gateRowFiles.push f.toString
    gateRowFiles := gateRowFiles.qsort (fun a b => a < b)
    let mut gateRowScanned := 0
    let mut gateRowFindings : Array String := #[]
    for f in gateRowFiles do
      let text ← IO.FS.readFile f
      gateRowScanned := gateRowScanned + 1
      for (ln, lib) in gateRowClaims gatedDirs text do
        gateRowFindings := gateRowFindings.push <| toString (GateDiag eGT0010
          s!"docs-check: {f}:{ln}: \
          gate-row claim — '{lib} is outside/not in the gated set' — but \
          {lib} IS in Gates.Packages' gated set; correct the header's \
          gate row")
    -- 6. report (the ONE envelope — every finding a gate Diag, its GT
    -- row a live registry spelling; 05 §4's discipline at the gates')
    let mut findings : List String := []
    for f in fences do
      if f.unclosed then
        findings := findings ++ [toString (GateDiag eGT0008
          s!"docs-check: {dispName f.file}:{f.openLine}: UNCLOSED lean fence")]
    for (loc, n) in pending do
      findings := findings ++ [toString (GateDiag eGT0009
        s!"docs-check: {loc}: fence names '{n}' — no such declaration in \
        the tree's env (is the fence a sketch? tag it ```lean sketch)")]
    for g in gateRowFindings do
      findings := findings ++ [g]
    for g in statusFindings do
      findings := findings ++ [g]
    for e in loadErrors do
      findings := findings ++ [toString (GateDiag eGT0011
        s!"docs-check: LOAD FAILED — {e}")]
    if walkExhausted then
      findings := findings ++
        [toString (GateDiag eGT0012
          "docs-check: WALK FUEL EXHAUSTED — a srcDir is deeper than the \
          gate-row scan's bound; raise the fuel or flatten the tree")]
    if let some e := scanError then
      findings := findings ++ [toString (GateDiag eGT0012 s!"docs-check: {e}")]
    let exempt := fences.filter (·.sketch) |>.size
    for l in findings do IO.println l
    if loadErrors.isEmpty then
      IO.println s!"docs-check: {files.size} notes file(s), {fences.size} lean fence(s) \
        ({exempt} sketch-exempt), {pending.size} unresolved name(s); \
        gate-row scan: {gateRowScanned} file(s), {gateRowFindings.size} false claim(s); \
        08-status: {statusRows.length} row(s), {statusFindings.length} stale row(s)"
    if !findings.isEmpty then return 1
    IO.println "docs-check: clean — every non-sketch lean fence's decl names resolve in the tree's env"
    return 0

end Gates.DocsCheck
