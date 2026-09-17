/-
# Gates.Manifest — the manifest-drift gate (`gates manifest-check`)

Closes the "manifest drift" robustness gap (notes/review-2026-09-16):
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
the `[[require]]` block shapes this repo writes (`name`/`git`/`rev`/
`path` as bare `key = "value"` lines). A fancier lakefile feature
(scope, subDir, version) appearing in a require block fails the parse
loudly (listed as an error), never silently skips.

Pure stdlib + Lean core (Lean.Json); no package imports — this module
stays the cheapest to rebuild in the package.
-/
import Lean

namespace Gates.Manifest

/-- One parsed `[[require]]` block. -/
structure Require where
  name : String
  git : Option String := none
  rev : Option String := none
  path : Option String := none
  deriving Inhabited

/-- Strip one layer of double quotes (TOML basic strings in this repo's
    lakefiles never escape). -/
def unquote (v : String) : String :=
  let v := v.trimAscii.toString
  let v := match v.dropPrefix? "\"" with | some r => r.toString | none => v
  match v.dropSuffix? "\"" with | some r => r.toString | none => v

/-- Parse the `[[require]]` blocks of a lakefile.toml (the repo's rigid
    shape only — see the module header). `.error` = a line inside a
    require block this parser doesn't know (loud, not skipped). -/
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
      cur := if l == "[[require]]" then some { name := "" } else none
      continue
    if let some r := cur then
      match l.splitOn " = " with
      | [k, v] =>
        let v := unquote v
        match k.trimAscii.toString with
        | "name" => cur := some { r with name := v }
        | "git"  => cur := some { r with git := some v }
        | "rev"  => cur := some { r with rev := some v }
        | "path" => cur := some { r with path := some v }
        | _ => continue   -- known-extra keys (e.g. none today) are ignored
      | _ => return .error s!"line {lineNo}: unparseable line inside [[require]]: '{l}'"
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

/-- The gate: every lean/*/ with a lakefile.toml. Run from lean/gates
    (`..` = lean/). -/
unsafe def run : IO UInt32 := do
  let leanDir : System.FilePath := ".."
  let mut findings : Array Finding := #[]
  let mut checked : Nat := 0
  for entry in ← leanDir.readDir do
    unless ← entry.path.isDir do continue
    unless ← (entry.path / "lakefile.toml").pathExists do continue
    checked := checked + 1
    findings := findings ++ (← checkPkg entry.path entry.fileName)
  for f in findings do
    IO.println s!"{f.pkg}: {f.msg}"
  if findings.isEmpty then
    IO.println s!"manifest-check: {checked} package manifests agree with their lakefiles"
    return 0
  IO.println s!"manifest-check: {findings.size} finding(s) across {checked} packages"
  return 1

end Gates.Manifest
