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
    written `tpl_add_ret_ok`). Resolution walks the gated packages'
    environments one at a time via the shared `loadPkgEnv` preamble
    (the sharded memory discipline — each env is dropped after use).
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
  (s.toList.dropWhile Char.isWhitespace
    |>.reverse.dropWhile Char.isWhitespace
    |>.reverse).asString

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
  c.isAlphanumeric || c == '_' || c == '\''

/-- The identifier prefix of a token: `foo:` → `foo`, `(x` → "" —
    anonymous/invalid decl positions yield the empty string. -/
def identPrefix (tok : String) : String :=
  (tok.toList.takeWhile isIdentChar).asString

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
        match name.get? 0 with
        | some c => if c.isAlphanumeric || c == '_' then some name else none
        | none => none
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
        let stripped := ((trimmed.toList.dropWhile (· == '`')).asString)
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

/-- Drop the pending names this environment resolves. -/
def filterResolved (env : Environment) (pending : Array (String × String)) :
    Array (String × String) :=
  let leaves := envLeafNames env
  pending.filter fun (_, n) =>
    !leaves.contains (lastComponent (String.toName n))

/-! ## The gate -/

/-- The notes dir, relative to the exe's cwd (`lean/gates`). -/
def notesDir : System.FilePath := "../../notes"

unsafe def run : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  unless ← notesDir.pathExists do
    IO.eprintln s!"docs-check: {notesDir} not found (run the exe from lean/gates)"
    return 1
  -- 1. scan (deterministic file order)
  let mut files : Array System.FilePath := #[]
  for e in ← notesDir.readDir do
    if !← e.path.isDir && e.path.extension == some "md" then
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
        pending := pending.push (s!"notes/{f.file}:{ln}", n)
  -- 3. resolve: one gated package env at a time (dropped after use —
  --    the sharded memory discipline); stop when nothing is pending
  let mut loadErrors : Array String := #[]
  for pkg in gatedPackages do
    if pending.isEmpty then break
    match ← loadPkgEnv base pkg with
    | .error e => loadErrors := loadErrors.push s!"{pkg.dir}: {e}"
    | .ok env => pending := filterResolved env pending
  -- 4. report
  let mut failed := false
  for f in fences do
    if f.unclosed then
      failed := true
      IO.println s!"docs-check: notes/{f.file}:{f.openLine}: UNCLOSED lean fence"
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

end Gates.DocsCheck
