/-
# Kit.Derive.Common — the elab drivers' shared boilerplate

The `Kit.Derive` generators (Fold's `declare_fold`, Bridge's
`declare_bridge`, Cascade's `declare_cascade*`) share their driver
skeleton — the DRY sweep's finding: the PROOF GATE was duplicated
verbatim (Bridge's local `gateCmd`, Cascade's private one), the refusal
logger and the resolve-try/catch twice each, and the V1 scope-check
quadruple (indices / parameters / empty / mutual) restated per driver
with only the E-codes + the message spellings differing. This module is
the ONE copy.

THE E-CODE DISCIPLINE (the code-registry gate's coverage scan): this
module allocates NO E-codes — the refusals carry the CALLER's family
constants (`eKD…`/`eKB…`), whose named-constant spellings stay at the
drivers (each site's allocated row is the scan's tie). The shared
checks take the codes as data (`ScopeRefusal`); no code is invented
here, none moves.

Core-only (imports Lean + Kit.Diag — the cone rule). META module: the
generated decls are ordinary core-level decls; the drivers' refusals
are the curated Diags (Kit.Diag).

Five questions (notes/v3/01-core.md):
- root: META — the generator skeleton's shared face (the drivers cite
  this; the generated surfaces do not change).
- carrier grade: none of its own — elaboration-time machinery over
  syntax + the Diag envelope.
- spine reading: the SHARED driver stage — one skeleton, three
  generators.
- ladder rung: none (no proofs; the generated surfaces' proofs stay at
  the drivers).
- gate row: KitTests' derive suites (the refusal teeth are byte-pinned,
  so the shared skeleton's messages are the callers' own texts — the
  pins cannot drift).
-/

module

public meta import Lean
public meta import Kit.Diag

public meta section

namespace Kit.Derive.Common

open Lean Elab Command Meta

/-! ## The curated Diag face -/

/-- Throw the refusal (the Diag rendered verbatim, the Lane discipline):
    the unsupported shape named — the code row + the message + the error
    severity. The code slot is an `ECode` of the caller's allocated
    family — a bare string cannot reach the throw. -/
def throwDiag {m : Type → Type} [Monad m] [MonadError m]
    (code : Kit.ECode) (message : String) : m α :=
  throwError m!"{({ code := code, message := message, severity := .error } : Kit.Diag)}"

/-- The refusal, named at the command's own level (a refusal logged
    inside the gate's closure never reaches the caller's message log —
    the #guard_msgs teeth would miss it). -/
def logRefusal (code : Kit.ECode) (refuseMsg : String) :
    CommandElabM Unit :=
  logError m!"{({ code := code, message := refuseMsg, severity := .error } : Kit.Diag)}"

/-! ## The proof gate -/

/-- THE PROOF GATE (the generated-theorem discipline, one copy): a
    generated command whose elaboration LOGGED an error must not commit —
    the gate rolls the state back and returns true (the caller refuses);
    the refusal is LOGGED, not thrown (a thrown exception never reaches
    the caller's message log — the #guard_msgs teeth would miss it).
    Wrongness does not elaborate; sorry never lands (zero-sorry is
    non-negotiable even in the test fixtures; the axiom sweep's `bt5`
    lesson — the guard captured the errors, the env kept the sorries). -/
def gateCmd (cmdStx : Syntax) : CommandElabM Bool := do
  let snap ← get
  elabCommand cmdStx
  -- the FULL message log: the state's log + the snapshot tasks'
  -- diagnostics (with incrementality on, the generated theorem's
  -- elaboration errors land in the snapshot tasks, not the log —
  -- counting the log alone misses every refusal)
  let allMsgs : MessageLog := (← get).messages ++
    ((← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl
      (· ++ ·.diagnostics.msgLog) .empty) .empty)
  let errCount (log : MessageLog) : Nat :=
    (log.reportedPlusUnreported.toArray.filter
      (·.severity matches .error)).size
  unless errCount allMsgs == errCount snap.messages do
    set { snap with messages := allMsgs, snapshotTasks := #[] }
    return true
  return false

/-! ## The resolve-try/catch -/

/-- The resolve-try/catch (one copy): resolve the ident to a constant,
    `none` on failure — the caller's curated refusal names the miss
    (the got + the valid space + the ONE engine's suggestion). -/
def resolveConst? (ident : TSyntax `ident) : CommandElabM (Option Name) := do
  try
    some <$> Lean.resolveGlobalConstNoOverload ident
  catch _ =>
    pure none

/-! ## The scope-check quadruple -/

/-- One scope-refusal slot: the caller's E-code + the caller's message
    spelling (the per-generator hint text differs — "the DEPENDENT fold
    (the motive riding the index, 06 §2)" vs the bridge's wording — so
    the texts stay at the drivers, byte-identical to the #guard_msgs
    pins; the CHECK is the one here). -/
structure ScopeRefusal where
  code : Kit.ECode
  message : String

/-- THE SCOPE-CHECK QUADRUPLE (the V1 closed-fragment gate, one copy):
    the resolved inductive must be simple, closed, non-empty, and
    non-mutual. Each refusal carries the caller's `ScopeRefusal` (the
    driver's family codes + its message spellings). -/
def checkScope (ii : InductiveVal)
    (rIdx rParam rEmpty rMutual : ScopeRefusal) : CommandElabM Unit := do
  let _indName := ii.name
  if ii.numIndices != 0 then
    throwDiag rIdx.code rIdx.message
  if ii.numParams != 0 then
    throwDiag rParam.code rParam.message
  if ii.ctors.isEmpty then
    throwDiag rEmpty.code rEmpty.message
  if ii.all.length > 1 then
    throwDiag rMutual.code rMutual.message

end Kit.Derive.Common

end -- public meta section