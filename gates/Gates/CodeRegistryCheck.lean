/-
Gates.CodeRegistryCheck — the persisted E-code registry gate
(`gates code-registry-check [--write]`; notes/v3/05-codegen.md §4 + 09 §3).

The registry `notes/code-registry.txt` is the SPEC OF RECORD for the
one E-code space (elaboration, gates, Rust spans, wasm faults): STABLE
allocation — codes never derive from enumeration position or import
order, a deleted name's code stays retired, a rename is a new code.
The gate loads the committed file and checks, in order, each with its
refusal:

1. PARSE — the file is `[-]name<TAB>code` rows, LF, no blank lines
   (Kit.CodeRegistry.parse; a malformed file is a refusal).
2. WELL-FORMEDNESS — `Kit.codeRegistryWf.check` (names unique over ALL
   rows; codes strictly increasing — distinct codes ride the order).
3. THE ALLOCATION REPLAY — every row is exactly the allocation the
   discipline produces at that point (`Kit.CodeRegistry.replay`):
   replaying `allocate` over the rows in code order must reproduce each
   row's code. A hand-edited code falls off the sequence — THE tooth.
4. SELF-STABILITY — `checkStable r r` (the machinery's live pin; the
   real old→new verdicts arrive with the registration-site consumers —
   the faults lane).
5. CANONICAL BYTES — `print (parse file)` ties the committed bytes.
6. THE COVERAGE TOOTH — every code-shaped string literal in the
   tree's Lean sources (the declared families' prefix + 4 digits;
   `Kit.CodeRegistry.codeShape`) must name a LIVE row of the registry
   (`Kit.CodeRegistry.coverageOffenders`): a hand-strung code outside
   the persisted registry is a gate refusal — the envelope discipline
   (05 §4) lands at the source, not in a convention. ALLOWANCE, named:
   the tooth scans string LITERALS, so a code assembled by
   concatenation (the digits computed, never spelled) is invisible to
   it — the honest blind spot (the ComponentTests control's spelling
   discipline is the countermeasure: codes are spelled, so the tooth
   sees them).

`--write` is the deliberate allocation/normalization step: it
bootstraps an absent file (the empty allocation history) and
canonicalizes formatting — but ONLY after parse + well-formedness +
replay pass, so it can never launder an ill-formed or hand-edited
registry. (The canonical-bytes tail is `Driver.byteTieGate`'s core —
not `reportGate`'s accept-drift tail, deliberately: here the committed
file IS the data, not a rendered baseline — there is no
fresh-vs-committed duality to re-baseline; the content checks above
run identically in both modes.)

The registration-site consumers (recomputing the allocation from the
Diag/fault call sites against this file) arrive with the faults lane.

The five questions (notes/v3/01-core.md):
- root: Universe — the committed registry file as the spec of record
(finite data, checked well-formedness).
- carrier grade: the CheckedProp grade (well-formedness as a decidable
shadow over a Prop) + the replay equality per row.
- spine reading: the interpretation stage (file → parse → wf → replay
→ canonical bytes).
- ladder rung: rung 1/decide — every check decided; the tombstone is
the honesty bit.
- gate row: the code-registry-check row itself.
-/
import Kit.CodeRegistry
import Gates.Common

namespace Gates.CodeRegistryCheck

/-- The committed registry (the exe runs from the repo root). -/
def registryPath : System.FilePath := "notes/code-registry.txt"

/-- The directories the coverage walk skips: the VCS/build internals
    and the LEGACY tree (read-only pre-v3 reference with its own
    pre-registry spellings — never this gate's jurisdiction). -/
def skipDirs : List String := [".git", ".lake", "legacy", "node_modules"]

/-- The string-literal spans of a Lean text (a conservative scan:
    double-quoted runs, `\`-escapes respected; no raw-string or comment
    awareness — an over-approximation is safe, the tooth only fires on
    code-SHAPED spans). -/
private def stringLiterals : List Char → Option (List Char) → List String → List String
  | [], some acc, out => String.ofList acc.reverse :: out
  | [], none, out => out
  | '\\' :: c :: rest, some acc, out => stringLiterals rest (some (c :: acc)) out
  | '"' :: rest, some acc, out => stringLiterals rest none (String.ofList acc.reverse :: out)
  | '"' :: rest, none, out => stringLiterals rest (some []) out
  | c :: rest, some acc, out => stringLiterals rest (some (c :: acc)) out
  | _c :: rest, none, out => stringLiterals rest none out

/-- The coverage walk: the `.lean` sources under `root`, their string
    literals as `(path, literal)` hits (the IO half of the coverage
    tooth; the verdict is `Kit.CodeRegistry.coverageOffenders`). The
    worklist loop is the walk — the skip list guards the non-source
    dirs (the LEGACY tree is read-only reference, never this gate's
    jurisdiction). -/
def collectHits (root : System.FilePath) :
    IO (List (String × String)) := do
  let mut hits : List (String × String) := []
  let mut queue : List System.FilePath := [root]
  while !queue.isEmpty do
    let dir := queue.head!
    queue := queue.tail!
    for e in ← dir.readDir do
      let p := dir / e.fileName
      if ← p.isDir then
        unless skipDirs.contains e.fileName do
          queue := p :: queue
      else if e.fileName.endsWith ".lean" then
        hits := (stringLiterals (← IO.FS.readFile p).toList none []).map
          (fun lit => (p.toString, lit)) ++ hits
  return hits

/-- `gates code-registry-check [--write]` — exit 1 on any refusal. -/
def run (write : Bool) : IO UInt32 := do
  unless ← registryPath.pathExists do
    if write then
      IO.FS.writeFile registryPath ""
      IO.println s!"wrote {registryPath} (bootstrap — the empty allocation history)"
      IO.println "code-registry-check: clean — the registry is well-formed and stable"
      return 0
    IO.println s!"code-registry-check: {registryPath} absent — run \
`lake exe gates code-registry-check --write` and commit"
    return 1
  let bytes ← IO.FS.readFile registryPath
  match Kit.CodeRegistry.parse bytes with
  | .error e =>
      IO.println s!"code-registry-check: REFUSED — {e}"
      return 1
  | .ok r =>
      if !(Kit.codeRegistryWf.check r) then
        IO.println "code-registry-check: REFUSED — the registry is ill-formed \
(names must be unique over all rows, tombstones included; rows sorted by code)"
        return 1
      match Kit.CodeRegistry.replay r with
      | .error e =>
          IO.println s!"code-registry-check: REFUSED — {e}"
          return 1
      | .ok _ =>
          -- stability against itself (the consumers' old→new verdicts arrive
          -- with the registration sites; the machinery's live pin here)
          if !(Kit.CodeRegistry.checkStable r r) then
            IO.println "code-registry-check: REFUSED — the registry is unstable \
against itself"
            return 1
          -- 6. THE COVERAGE TOOTH: every code-shaped string literal in
          -- the tree's Lean sources names a LIVE row (a tombstone's
          -- spelling refuses too — a spent code is not a live code).
          let offenders := Kit.CodeRegistry.coverageOffenders r
            (← collectHits ".")
          unless offenders.isEmpty do
            for o in offenders.take 20 do
              IO.println s!"code-registry-check: REFUSED — {o}"
            if offenders.length > 20 then
              IO.println s!"code-registry-check: ... and \
{offenders.length - 20} more"
            return 1
          let canonical := Kit.CodeRegistry.print r
          -- the canonical-bytes tail (the Driver.byteTieGate core; the
          -- parse/wf/replay/stability refusals above run first in both
          -- modes, so a write can never launder an ill-formed registry)
          Driver.byteTieGate bytes canonical write
            (IO.FS.writeFile registryPath)
            (inSyncWrite := some s!"wrote {registryPath} (in sync)")
            (driftWriteMsg := s!"wrote {registryPath} (canonicalized)")
            (cleanAfterWrite := true)
            (cleanMsg :=
              "code-registry-check: clean — well-formed, the allocation \
replays, stable, canonical bytes")
            (driftMsg :=
              s!"code-registry-check: {registryPath} is not canonical — \
run `lake exe gates code-registry-check --write` and commit")

end Gates.CodeRegistryCheck
