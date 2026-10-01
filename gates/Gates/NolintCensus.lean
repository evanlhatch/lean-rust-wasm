/-
Gates.NolintCensus — the nolint census gate (`gates nolint-census
[--write] [--accept-drift]`): a baselined count-per-linter census over
the gated sources' `@[nolint …]` rows (the enforcement wave's gap 3 —
the opt-outs are the lints' honest escape hatch, and EXACTLY BECAUSE of
that they are drift-watched: a new nolint row must land as a deliberate
baseline diff, never silently).

The scan: every `.lean` file under the gated packages' srcDirs (the
text-lint mounts' own surface), the CODE channel only
(`LintKit.splitCodeComments` — comments and string literals can't fake a
row), each `@[nolint` site's linter names extracted between the
attribute opener and the reason string/close bracket, counted per
(linter, file). The baseline is the TSV (the honest name):
`notes/nolint-census.tsv`, one `linter<TAB>file<TAB>count` line, sorted.

Adjudication discipline (the audit's demand): every counted row is
either load-bearing — its named reason stays — or fixed. The
enforcement wave's sweep found all counted rows reasoned (the
nolintReason lint makes a bare opt-out unlandable); the counts
themselves live in the baseline's first-write.

The teeth: the drift check (a new/unlanded-silenced site fails the row)
+ the scan's own unit teeth in GatesTests (a planted row the scan MUST
count — the negative control is the row-free file). The five questions
(notes/v3/01-core.md): none of its own — a census row (data + drift).
-/
import Lean
import LintKit
import Gates.Baselines
import Gates.Packages
import Gates.Common

namespace Gates.NolintCensus

open Gates (PkgSpec gatedPackages)
open Lean

/-- The committed baseline. -/
def baselinePath : System.FilePath := "notes/nolint-census.tsv"

/-- The `@[nolint` sites' linter names in one file's CODE channel:
the tokens between the attribute opener and the reason string or the
close bracket that start with `linter.`. Heuristic, deliberately (the
text lints' own stance: a scanner, not a parser). -/
def fileNolints (content : String) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (_, code, _) in LintKit.splitCodeComments content do
    let toks := code.trimAscii.toString.splitOn.filter (!·.isEmpty)
    let mut inNolint := false
    for t in toks do
      if t == "@[nolint" then
        inNolint := true
      else if inNolint then
        if t == "]" || t.startsWith "\"" then
          inNolint := false
        else if (t.splitOn ".").head?.getD "" == "linter" then
          out := out.push t.toName
  return out

/-- One file's census lines: `(linter, file, count)`, counts > 0. -/
def fileRows (file : String) (content : String) :
    Array (Name × String × Nat) := Id.run do
  let mut counts : Array (Name × Nat) := #[]
  for n in fileNolints content do
    match counts.findIdx? fun (m, _) => m == n with
    | some i => counts := counts.modify i fun (_, k) => (n, k + 1)
    | none => counts := counts.push (n, 1)
  return counts.filterMap fun (n, k) =>
    if k > 0 then some (n, file, k) else none

/-- A srcDir-relative `.lean` file's module name (`Foo/Bar.lean` →
`Pkg.Foo.Bar` shape — the dotted join; the caller's prefix filter does
the rest). -/
def fileModule? (root : System.FilePath) (f : System.FilePath) : Option Name :=
  let rel? := f.toString.dropPrefix? (root.toString ++ "/")
  rel?.map fun rel =>
    ((rel.toString.splitOn ".lean").head?.getD rel.toString |>.splitOn "/")
      |>.foldl (fun acc c => Name.mkStr acc c) Name.anonymous

/-- The gated surface's files: THE TEXT LINTS' OWN SURFACE — every
module under a gated package's root prefixes (`runTextLintsOnModules`'s
`roots.any (·.isPrefixOf m)` rule, computed over the FILES; the census
is their drift twin, never a wider walk). Dot-directories (`.lake`)
are skipped; the app rows' `srcDir := "."` stays safe because the
prefix filter rejects everything outside the roots. Deduplicated by
path. -/
def gatedLeanFiles : IO (Array System.FilePath) := do
  let mut seen : Array System.FilePath := #[]
  for pkg in gatedPackages do
    let dir : System.FilePath := pkg.srcDir
    let mut stack := #[dir]
    while stack.size > 0 do
      let d := stack[stack.size - 1]!
      stack := stack.pop
      match ← d.readDir |>.toBaseIO with
      | .error _ => continue
      | .ok entries =>
        for e in entries do
          let p := e.path
          if ← p.isDir then
            unless p.fileName.getD "" == ".lake" || (p.toString.take 1 == ".") do
              stack := stack.push p
          else if (p.toString.splitOn ".").getLast?.getD "" == "lean" then
            match fileModule? dir p with
            | some m =>
                if pkg.roots.any (·.isPrefixOf m) then
                  unless seen.contains p do
                    seen := seen.push p
            | none => pure ()
  return seen

/-- The fresh render: THE GRAMMAR'S DERIVED PRINTER over the sorted
    rows (the linter's SPELLING is the grammar value's face; the hand
    byte-assembly died — the bytes are unchanged, the gate's green run
    without a re-baseline is the proof). -/
def render (rows : Array (Name × String × Nat)) : String :=
  let sorted := rows.qsort fun a b =>
    let n1 := toString a.1
    let n2 := toString b.1
    n1 < n2 || (n1 == n2 && a.2.1 < b.2.1)
  Gates.Baselines.printCensus
    (sorted.toList.map fun (l, f, k) => (toString l, f, k))

/-- `nolint-census [--write] [--accept-drift]` — the gate row. -/
unsafe def run (write acceptDrift : Bool) : IO UInt32 := do
  let mut rows : Array (Name × String × Nat) := #[]
  let files ← gatedLeanFiles
  for f in files do
    match ← IO.FS.readFile f |>.toBaseIO with
    | .error e => IO.eprintln s!"nolint-census: unreadable {f}: {e}"; return 1
    | .ok content => rows := rows ++ fileRows f.toString content
  let text := render rows
  Driver.reportGate "nolint-census" baselinePath text write acceptDrift false
    "nolint-census: clean — the opt-out rows' census in sync"
    (Driver.diffCheck "nolint-census" "census" "the nolint rows changed"
      baselinePath text)

end Gates.NolintCensus
