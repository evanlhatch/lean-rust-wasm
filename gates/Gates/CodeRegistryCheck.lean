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

`--write` is the deliberate allocation/normalization step: it
bootstraps an absent file (the empty allocation history) and
canonicalizes formatting — but ONLY after parse + well-formedness +
replay pass, so it can never launder an ill-formed or hand-edited
registry. (Divergence from `Driver.reportGate`'s accept-drift tail,
deliberate: here the committed file IS the data, not a rendered
baseline — there is no fresh-vs-committed duality to re-baseline; the
content checks above run identically in both modes.)

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

namespace Gates.CodeRegistryCheck

/-- The committed registry (the exe runs from the repo root). -/
def registryPath : System.FilePath := "notes/code-registry.txt"

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
          let canonical := Kit.CodeRegistry.print r
          if canonical != bytes then
            if write then
              IO.FS.writeFile registryPath canonical
              IO.println s!"wrote {registryPath} (canonicalized)"
            else
              IO.println s!"code-registry-check: {registryPath} is not canonical — \
run `lake exe gates code-registry-check --write` and commit"
              return 1
          else if write then
            IO.println s!"wrote {registryPath} (in sync)"
          IO.println "code-registry-check: clean — well-formed, the allocation \
replays, stable, canonical bytes"
          return 0

end Gates.CodeRegistryCheck
