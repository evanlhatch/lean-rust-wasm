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

Deliberate exclusion vs the legacy module: the SHARDED child-process
resolution (the legacy memory shape — libgc retained every dropped env).
Here each package env is imported in this process, one at a time, and
dropped; two core-only libraries stay flat in RSS. The sharding arrives
with the first gated package heavy enough to need it.

The five questions (notes/v3/01-core.md):
- root: none — the notes-drift gate.
- carrier grade: none — name resolution over fences, not a crossing.
- spine reading: the interpretation stage (notes fences → decl names →
resolution in the gated envs).
- ladder rung: n/a (the honesty rule: an unmarked fence CLAIMS to be
real code — the marker convention is the declaration).
- gate row: the docs-check row itself (`gates docs-check`).
-/
import Lean
import Gates.Packages

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

/-- The names from `pending` that `env` resolves (by last component). -/
def resolvedIn (env : Environment) (pending : Array (String × String)) :
    Array String :=
  let leaves := envLeafNames env
  pending.filterMap fun (_, n) =>
    if leaves.contains (lastComponent (String.toName n)) then some n else none

/-! ## The gate -/

/-- Display name for a scanned file: report `notes/<file>.md` (the
    repo-relative shape the notes cite). -/
def dispName (f : String) : String :=
  match f.dropPrefix? "notes/" with
  | some r => "notes/" ++ r
  | none => f

/-- Run the gate: scan the notes, resolve the pending decl names against
    the gated packages' environments (one at a time in this process). -/
unsafe def run : IO UInt32 := do
  let notesDir : System.FilePath := "notes"
  unless ← notesDir.pathExists do
    IO.eprintln s!"docs-check: {notesDir} not found (run the exe from the repo root)"
    return 1
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
  -- 2. the pending resolution set: (location, name) per non-sketch fence
  let mut pending : Array (String × String) := #[]
  for f in fences do
    if f.sketch then continue
    for (ln, line) in f.body do
      if (trimWs line).startsWith "--" then continue
      if let some n := declName? line then
        pending := pending.push (s!"{dispName f.file}:{ln}", n)
  -- 3. resolve: one package env at a time in this process (the memory
  --    shape in the header); a load failure is a gate failure — an
  --    unloadable tree verifies nothing. Not `Gates.withPkgEnv`: this
  --    gate folds ALL gated packages, a load failure is a collected
  --    loadError row with the `just build` hint, not a first-failure
  --    gate exit (the combinator's shape).
  let mut loadErrors : Array String := #[]
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  for pkg in gatedPackages do
    if pending.isEmpty then break
    match ← loadPkgEnv base pkg with
    | .error e => loadErrors := loadErrors.push s!"{pkg.dir}: {e} (run `just build` first)"
    | .ok env => pending := pending.filter fun (_, n) =>
        !(resolvedIn env pending).contains n
  -- 4. report
  let mut findings : List String := []
  for f in fences do
    if f.unclosed then
      findings := findings ++ [s!"docs-check: {dispName f.file}:{f.openLine}: UNCLOSED lean fence"]
  for (loc, n) in pending do
    findings := findings ++ [s!"docs-check: {loc}: fence names '{n}' — no such declaration in \
      the tree's env (is the fence a sketch? tag it ```lean sketch)"]
  for e in loadErrors do
    findings := findings ++ [s!"docs-check: LOAD FAILED — {e}"]
  let exempt := fences.filter (·.sketch) |>.size
  for l in findings do IO.println l
  if loadErrors.isEmpty then
    IO.println s!"docs-check: {files.size} notes file(s), {fences.size} lean fence(s) \
      ({exempt} sketch-exempt), {pending.size} unresolved name(s)"
  if !findings.isEmpty then return 1
  IO.println "docs-check: clean — every non-sketch lean fence's decl names resolve in the tree's env"
  return 0

end Gates.DocsCheck
