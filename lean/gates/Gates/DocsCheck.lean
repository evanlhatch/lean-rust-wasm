/-
# Gates.DocsCheck — the notes excerpt-drift gate (`gates docs-check`)

PolyFun's `check-docs-integrity.py` pattern (polyfun-study.md borrow item
1, their check 4): our `notes/` carry Lean code fences that can silently
rot — a gate naming a decl that no longer exists (or never did) fails
here. MINIMAL and true, by design (the study's "keep it minimal and
true"):

(a) Every ```lean fence in `notes/*.md` must have its DECLARED
    top-level names (theorem/def/abbrev/instance/structure/class/
    inductive/opaque, after the usual modifiers) RESOLVE in the gated
    tree's environment — resolved by the constant's LAST component
    (notes habitually write short names; `Correct.tpl_add_ret_ok` is
    written `tpl_add_ret_ok`).
(b) `path:line` citations and inline `Name.path` references are
    deliberately NOT checked (the honest subset is (a); adding (b)
    without a real citation convention would be a false-positive
    machine).

THE MARKER CONVENTION: a fence of PROPOSED code (a statement shape, a
template, a migration sketch) tags itself on the open line:

    ```lean sketch

The fence — not a side list — is the truth about what is a sketch; an
unmarked fence CLAIMS to be real code, so its decl names must resolve.
Fences that declare no top-level names (an anonymous structure literal,
a `#guard` probe) trivially pass.

Requires `just lean-build` (the resolution imports the gated packages'
oleans — this gate never builds). Not a load-time gate: a package env
that fails to load is a FAILURE (an unloadable tree verifies nothing).

MEMORY SHAPE (the axioms-gate lesson, learned twice): importing the
gated packages' environments into ONE process accumulates RSS — libgc's
conservative stack scan retains each dropped env, and the walk reached
~15GB before earlyoom's SIGTERM. So the resolution is SHARDED like
`gates axioms`' `--package` mode: the outer process scans the notes and
then spawns ONE short-lived child per gated package
(`docs-check --package X --resolve n1,n2,…`) — one environment per
process, the child prints the names its env resolves and dies; the
parent collects the lines and stops early once nothing is pending. The
parent itself never imports an env, so its RSS stays flat.

Pure Lean core + Gates.Packages (+ Gates.Common's shared loader).
-/
import Lean
import Gates.Packages
import Gates.Common

open Lean

namespace Gates.DocsCheck

open Gates (PkgSpec gatedPackages loadPkgEnv)

/-! ## Fence scanning -/

/-- Whitespace trim without the deprecated `String.trim` (fence lines
    are short — the list round-trip is free). -/
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

/-! ## Child mode: one package env per process -/

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

/-- One package's env, imported in THIS process (the sharded mode —
    the parent never imports an env, see the header). Prints one
    `RESOLVED <name>` line per pending name this env resolves. -/
unsafe def runChild (pkg : PkgSpec) (names : Array String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  match ← loadPkgEnv base pkg with
  | .error e =>
    IO.eprintln s!"docs-check: LOAD FAILED ({pkg.dir}) — {e} (run `just lean-build` first)"
    return 1
  | .ok env =>
    let leaves := envLeafNames env
    for n in names do
      if leaves.contains (lastComponent (String.toName n)) then
        IO.println s!"RESOLVED {n}"
    return 0

/-- Spawn the child for one package and return the names it resolved. -/
def spawnChild (pkg : PkgSpec) (names : Array String) :
    IO (Except String (Array String)) := do
  let out ← IO.Process.output
    { cmd := "lake"
    , args := #["--dir", "../..", "exe", "gates", "docs-check",
                "--package", pkg.dir, "--resolve",
                String.intercalate "," names.toList]
    , cwd := some ("." : System.FilePath) }
  if out.exitCode != 0 then
    -- a child load failure is a gate failure (an unloadable tree
    -- verifies nothing), not a skip
    let tail := String.intercalate "\n" (((out.stderr.splitOn "\n").reverse.take 6).reverse)
    return .error s!"{pkg.dir}: child exited {out.exitCode} — {tail}"
  return .ok ((((out.stdout.splitOn "\n").filter (·.startsWith "RESOLVED ")).map
    (fun l => trimWs (String.ofList (l.toList.drop 9)))).toArray)

/-! ## The gate -/

/-- The notes dir, relative to the exe's cwd (`lean/gates`). -/
def notesDir : System.FilePath := "../../notes"

/-- Display name for a scanned file: strip the dir prefix, report
    `notes/<file>.md` (the repo-relative shape the notes cite). -/
def dispName (f : String) : String :=
  match f.dropPrefix? (notesDir.toString ++ "/") with
  | some r => "notes/" ++ r
  | none => f

/-- Parent mode: scan the notes, then resolve the pending decl names
    against the gated packages' environments — one short-lived child
    process per package (`--package X --resolve …`), so this process
    never imports an env (the memory shape in the header). -/
unsafe def runParent : IO UInt32 := do
  unless ← notesDir.pathExists do
    IO.eprintln s!"docs-check: {notesDir} not found (run the exe from lean/gates)"
    return 1
  -- 1. scan (deterministic file order)
  let mut files : Array System.FilePath := #[]
  for e in ← notesDir.readDir do
    -- nested `if`s, NOT `&&` over monadic operands (the KernelCheck
    -- lesson: do-notation hoists every `←` out of `&&` eagerly)
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
  -- 3. resolve: one child process per gated package (one env per
  --    process — the sharded memory discipline); stop when none pending
  let mut loadErrors : Array String := #[]
  for pkg in gatedPackages do
    if pending.isEmpty then break
    let names := (pending.map (·.2)).foldl (fun acc n =>
      if acc.contains n then acc else acc.push n) #[]
    match ← spawnChild pkg names with
    | .error e => loadErrors := loadErrors.push e
    | .ok resolved =>
      pending := pending.filter fun (_, n) => !resolved.contains n
  -- 4. report
  let mut failed := false
  for f in fences do
    if f.unclosed then
      failed := true
      IO.println s!"docs-check: {dispName f.file}:{f.openLine}: UNCLOSED lean fence"
  for (loc, n) in pending do
    failed := true
    IO.println s!"docs-check: {loc}: fence names '{n}' — no such declaration in \
      the tree's env (is the fence a sketch? tag it ```lean sketch)"
  for e in loadErrors do
    failed := true
    IO.println s!"docs-check: LOAD FAILED — {e} (run `just lean-build` first)"
  let exempt := fences.filter (·.sketch) |>.size
  IO.println s!"docs-check: {files.size} notes file(s), {fences.size} lean fence(s) \
    ({exempt} sketch-exempt), {pending.size} unresolved name(s)"
  if failed then return 1
  IO.println "docs-check: clean — every non-sketch lean fence's decl names resolve in the tree's env"
  return 0

/-- Dispatch: no flags = the parent (scan + shard); `--package X
    --resolve n1,n2,…` = the child (ONE env in this process). -/
unsafe def run (pkgName resolve : Option String) : IO UInt32 := do
  match pkgName, resolve with
  | some pkg, some csv =>
    let some pkg ← Driver.selectPackages "docs-check" (some pkg) | return 1
    match pkg with
    | #[p] => runChild p ((csv.splitOn "," |>.map trimWs |>.filter (· != "")).toArray)
    | _ =>
      IO.eprintln "docs-check: child mode takes exactly one --package"
      return 1
  | none, none => runParent
  | _, _ =>
    IO.eprintln "docs-check: --package and --resolve are given together (child mode)"
    return 1

end Gates.DocsCheck
