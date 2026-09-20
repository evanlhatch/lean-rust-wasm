/-
# Gates.Audit — the static census (`gates audit`)

The audit-to-gate loop: the CHEAP STATIC censuses as a standing gate,
computed as data-driven checks over the loaded environments. This gate
REPORTS (exit 0 with the report) — it is the census channel; failures
belong to the specific lints it feeds. Exit 1 only when a package
environment fails to load (a build problem, not a finding).

Sections:

(a) **Zero-consumer candidates** — per gated package, its own declarations
    (`LintKit.packageDecls`) with ZERO references anywhere in the loaded
    environments (the constant-usage analysis: every our-tree constant's
    type + value's used-constant set, accumulated over every gated
    package's env, self-references erased). Honest false-positive classes
    — consumers invisible to constant-reference analysis:
      * exe entry points (`main`-named decls — ALLOWLISTED),
      * instances (`instInfo` — ALLOWLISTED; instance resolution never
        names the constant),
      * attribute-registered decls (`register_*_attribute` runners,
        `initialize` blocks) and meta-registry consumers (the emitters
        replay the registries WITHOUT naming the constants — NOT
        statically detectable here; v4.33 exposes no
        decls-carrying-attributes query).
    So the section is a REVIEW QUEUE, not a verdict — stated in the
    report itself. NOT a failure, ever.

(b) **Comment ratio** — per module, comment characters / total characters
    (a single-pass scanner: `--` lines, nested `/- -/` blocks, `"` strings
    with escapes; char literals and raw strings are approximated as plain
    text — a ratio census, not a parser). REPORT-ONLY, no threshold —
    calibration data for the docstring doctrine, not a lint.

(c) **Hand-roll patterns** — CITED, not duplicated: the upstream-duplicate
    class (a def alpha-equivalent to a core/Batteries decl) is OWNED by
    LintKit.UpstreamDup (`linter.guestlang.upstreamDup`, alpha-equivalence
    with binder + level names stripped, `>= 20` Expr nodes, enforcement
    via `just lean-lint`). The report reads that linter's own calibration
    constants (`upstreamRoots`, `upstreamDupMinNodes`) so the citation
    cannot rot silently. Explicitly NO module-size lint here (owner
    rejected it).

LEGACY (non-module) file: meta env-extension access
(LintKit.packageDecls over `importModules`'d envs — constraint 12,
notes/w5-4-module-migration.md).
-/
import Lean
import LintKit
import Gates.Packages

open Lean
open Gates (PkgSpec gatedPackages)

namespace Gates.Audit

/-! ## (a) the zero-consumer scan -/

/-- The our-tree module roots a consumer must live in: every gated
    package's root names (`TestKitTests.Main` → `TestKitTests`). A
    consumer of our decl is always in some gated package's module tree
    (core/mathlib never imports us), so scanning these roots over every
    gated package's loaded env is a COMPLETE consumer universe. -/
def ourRoots : Array Name :=
  (gatedPackages.flatMap fun p => p.roots.map (·.getRoot)).toList.eraseDups.toArray

/-- The our-tree constants' used-constant union over one loaded env
    (type + value, self-references erased — a recursive decl consumes
    nothing but itself). Only our-tree modules are scanned: nothing else
    can reference our decls. -/
def scanUsedConsts (env : Environment) : NameSet := Id.run do
  let mut used : NameSet := {}
  for (decl, info) in env.constants.map₁.toList do
    match env.const2ModIdx[decl]? with
    | none => pure ()
    | some idx =>
      let m := env.header.moduleNames[idx]!
      if ourRoots.any (·.isPrefixOf m) then
        for c in info.getUsedConstantsAsSet.toList do
          if c != decl then used := used.insert c
  return used

/-- The always-consumed decls: instances (resolution never names the
    constant) and exe entry points (`main`, `Foo.main`). -/
def allowlisted (d : Name) (isInst : Bool) : Bool :=
  isInst || d == `main || d.componentsRev.getLast? == some `main

structure PkgScan where
  dir : String
  /-- The package's own decls, tagged with instance-hood (an
      allowlist input; the used-set pass runs later, over all envs). -/
  decls : Array (Name × Bool) := #[]
  loadError : Option String := none

/-- Load one package's env (the Axioms preamble: its olean dir prepended,
    initializers executed), collect its own decls, and merge the env's
    our-tree used-constant set into `usedRef`. The env is dropped after
    the scan — one environment in memory at a time. -/
unsafe def scanPkg (base : SearchPath) (pkg : PkgSpec) (usedRef : IO.Ref NameSet) :
    IO PkgScan := do
  Lean.searchPathRef.set (pkg.oleanDirOf :: base)
  try
    Lean.enableInitializersExecution
    let env ← importModules (pkg.roots.map ({ module := · })) {}
      (trustLevel := 1024) (loadExts := true)
    let ctx : Core.Context := { fileName := "<gates-audit>", fileMap := default }
    let (decls, _) ← (LintKit.packageDecls env (pkg.roots.map (·.getRoot))).toIO ctx { env := env }
    let rows := decls.toList.map fun d =>
      -- instance-hood via the instance extension (v4.33 has no instInfo ctor:
      -- instances are defnInfo + the attribute — resolution never names them)
      (d, Lean.Meta.isInstanceCore env d)
    usedRef.modify (scanUsedConsts env ++ ·)
    return { dir := pkg.dir, decls := rows.toArray }
  catch e =>
    return { dir := pkg.dir, loadError := some (toString e) }

/-- Render the zero-consumer section: per package, the decls no loaded
    env references, minus the allowlist. Sorted by name (deterministic). -/
def renderZeroConsumer (scans : Array PkgScan) (used : NameSet) : String :=
  let lines : List String := Id.run do
    let mut lines : List String :=
      [ "## zero-consumer candidates (per gated package; report-only)"
      , ""
      , "Constant-reference analysis over every gated package's loaded env. Invisible"
      , "consumers exist (exe entry points and instances are allowlisted below;"
      , "attribute-registered decls, `initialize` blocks and meta-registry replays are"
      , "not statically detectable) — candidates are a REVIEW QUEUE, not a verdict."
      , "" ]
    for s in scans do
      if s.loadError.isSome then continue
      let cands := s.decls.filterMap fun (d, isInst) =>
        if allowlisted d isInst || used.contains d then none else some d
      let sorted := cands.qsort Name.quickLt
      lines := lines ++
        [ s!"{s.dir}: {sorted.size} candidate(s) / {s.decls.size} decls"
          ++ (if sorted.isEmpty then "" else ":")]
          ++ sorted.toList.map (fun d => s!"  - {d}")
    return lines
  String.intercalate "\n" lines

/-! ## (b) the comment-ratio report -/

/-- One module row: display path (`<pkg-dir>/<rel>`), comment chars,
    total chars. -/
structure RatioRow where
  path : String
  comment : Nat
  total : Nat

/-- One pass over the source: comment characters (chars inside `--` line
    comments or nested `/- -/` block comments, markers included). `"`
    strings with `\` escapes are excluded; char literals and raw strings
    are approximated as plain text (documented — a ratio, not a parser). -/
-- partial: a two-char-lookahead scanner (structural recursion over the
-- nested `rest` matches defeats the termination checker; this is IO census
-- code, never proof-reduced).
partial def scanCommentChars (chars : List Char) : Nat :=
  go chars false 0 false false 0
where
  /-- chars, inLine, block depth, inString, escaped, count -/
  go : List Char → Bool → Nat → Bool → Bool → Nat → Nat
    | [], _, _, _, _, n => n
    | c :: rest, inLine, depth, inStr, esc, n =>
      if inLine then
        if c == '\n' then go rest false depth inStr esc n
        else go rest inLine depth inStr esc (n + 1)
      else if depth > 0 then
        -- inside a block comment: only `-` `/` transitions matter
        if c == '-' then
          match rest with
          | '/' :: rest2 => go rest2 false (depth - 1) inStr esc (n + 2)
          | _ => go rest true depth inStr esc (n + 1)
        else if c == '/' then
          match rest with
          | '-' :: rest2 => go rest2 false (depth + 1) inStr esc (n + 2)
          | _ => go rest true depth inStr esc (n + 1)
        else go rest true depth inStr esc (n + 1)
      else if inStr then
        if esc then go rest inLine depth true false n
        else match c with
          | '\\' => go rest inLine depth inStr true n
          | '"' => go rest inLine depth false esc n
          | _ => go rest inLine depth inStr esc n
      else
        -- normal source
        match c with
        | '-' =>
          match rest with
          | '-' :: rest2 => go rest2 true depth inStr esc (n + 2)
          | _ => go rest inLine depth inStr esc n
        | '/' =>
          match rest with
          | '-' :: rest2 => go rest2 false (depth + 1) inStr esc (n + 2)
          | _ => go rest inLine depth inStr esc n
        | '"' => go rest inLine depth true esc n
        | _ => go rest inLine depth inStr esc n

/-- All `.lean` files under `dir` (recursive). -/
partial def walkDir (dir : System.FilePath) (acc : Array System.FilePath) :
    IO (Array System.FilePath) := do
  let mut acc : Array System.FilePath := acc
  for e in ← dir.readDir do
    let p := System.FilePath.mk (dir.toString ++ "/" ++ e.fileName)
    if ← p.isDir then
      acc ← walkDir p acc
    else if p.toString.endsWith ".lean" then
      acc := acc.push p
  return acc

/-- The comment-ratio rows for one package's sources. -/
def ratioRows (pkg : PkgSpec) : IO (Array RatioRow) := do
  let src := pkg.srcDirOf
  if ← src.pathExists then
    let mut rows : Array RatioRow := #[]
    for f in ← walkDir src #[] do
      let rel := ((f.toString.splitOn (src.toString ++ "/")).getD 1 f.toString)
      let srcText ← IO.FS.readFile f
      rows := rows.push { path := s!"{pkg.dir}/{rel}"
                        , comment := scanCommentChars srcText.toList
                        , total := srcText.length }
    return rows
  else
    return #[]

/-- Render the comment-ratio section (sorted by path; percentages,
    integer-rounded). -/
def renderRatios (rows : Array RatioRow) : List String :=
  let sorted := rows.qsort (fun a b => a.path < b.path)
  let pct (r : RatioRow) :=
    if r.total == 0 then 0 else r.comment * 100 / r.total
  [ "## comment ratio (per module; comment chars / total chars — report-only)"
  , "" ]
  ++ sorted.toList.map fun r =>
       s!"{r.path}: {pct r}% ({r.comment}/{r.total})"

/-! ## (c) the hand-roll citation -/

/-- The hand-roll section: CITES LintKit.UpstreamDup (which landed the
    enforcement) rather than duplicating its analysis — the constants are
    READ from the linter so the citation cannot rot silently. -/
def renderHandroll : List String :=
  [ "## hand-rolled upstream decls (citation — LintKit.UpstreamDup owns enforcement)"
  , ""
  , s!"The class (a def body alpha-equivalent — binder + level-param names \
    stripped — to a constant under upstream roots \
    [{String.intercalate ", " (LintKit.upstreamRoots.map toString)}]) is \
    flagged by `linter.guestlang.upstreamDup` (>= \
    {LintKit.upstreamDupMinNodes} Expr nodes: the non-triviality filter) \
    via `just lean-lint`. This census cites the linter; it does not \
    duplicate the analysis."
  , "" ]

/-- The census: load every gated package's env one at a time (used-sets
    merged, envs dropped — one env in memory), then the three sections.
    Exit 0 on all findings; exit 1 only on a load failure. -/
unsafe def run : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  let usedRef ← IO.mkRef ({} : NameSet)
  let mut scans : Array PkgScan := #[]
  let mut ratios : Array RatioRow := #[]
  let mut failed := false
  for pkg in gatedPackages do
    let s ← scanPkg base pkg usedRef
    if s.loadError.isSome then
      IO.println s!"{s.dir}: LOAD FAILED — {s.loadError.get!}"
      failed := true
    scans := scans.push s
    for r in ← ratioRows pkg do
      ratios := ratios.push r
  IO.println "gates audit: the static census (report-only — findings are a \
    review queue; exit 1 only on a load failure)"
  IO.println ""
  IO.println (renderZeroConsumer scans (← usedRef.get))
  IO.println ""
  IO.println (String.intercalate "\n" (renderRatios ratios))
  IO.println ""
  IO.println (String.intercalate "\n" renderHandroll)
  let scanned := scans.filter (·.loadError.isNone)
  IO.println s!"gates audit: census complete — {scanned.size}/{gatedPackages.size} \
    package env(s) loaded"
  if failed then return 1
  return 0

end Gates.Audit
