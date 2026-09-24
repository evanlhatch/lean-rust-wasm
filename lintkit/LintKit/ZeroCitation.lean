/-
LintKit.ZeroCitation — the proof-level leftover rule: a theorem with
zero citations is the proof layer's dead code.

The finding: a `theorem` whose name is referenced NOWHERE outside its
own module — no other declaration's type or value mentions it, and no
test file pins it.

Detection (honest about the limits — the census exists because they are
real):

* The environment's constant dependencies: every constant's type + value
  `getUsedConstants` (LintKit.Citations' cached graph). A theorem cited
  only by its OWN module's decls still fires — the leftover rule counts
  the tree, not the file.
* The test pins: `#print axioms Foo` leaves NO constant in the
  environment, so pin targets would read as uncited — the detection sees
  them via a full-dotted-name scan of the test modules' SOURCES
  (LintKit.Citations' corpus; a pin spelled without the full dotted name
  is missed — census mode catches the false positive).
* Exemptions: theorems in `Tests` modules (test scaffolding, the
  verdictCtors precedent), skipDecl shapes, and `@[nolint
  linter.guestlang.zeroCitation "public API"]` for the library
  theorems that ship for downstream consumers.

REPORT-ONLY census (default OFF) by design: the public-API surface (the
kit's library theorems consumed downstream) is legitimately
zero-in-tree-cited today; promote to a gate after the false-positive
review of the real numbers.

  lake exe lintkit --enable=linter.guestlang.zeroCitation <roots>

The five questions (notes/v3/01-core.md):
- root: none — the proof-level leftover census.
- carrier grade: none — host machinery.
- spine reading: interpretation (env → citation graph → findings).
- ladder rung: n/a.
- gate row: census only (default OFF).
-/
module

public import LintKit.Basic
public import LintKit.Citations

public meta section

open Lean Meta Linter EnvLinter

namespace LintKit

meta def zeroCitationTest (decl : Name) : MetaM (Option MessageData) := do
  if ← skipDecl decl then return none
  let env ← getEnv
  let some (.thmInfo _) := env.find? decl | return none
  let some idx := env.getModuleIdxFor? decl | return none
  let mod := env.header.moduleNames[idx]!
  if isTestModule mod then return none
  let census ← citationCensus env
  if citedOutsideModule? env census decl then return none
  -- the test pins count as citations (#print axioms in a Tests module)
  if ← citedInTestSources? env decl then return none
  return some m!"zero citations: `{decl}` is referenced nowhere outside \
    its own module — the proof layer's dead code (the leftover rule, at \
    proof level): consume it in the tree, or opt out with `@[nolint \
    linter.guestlang.zeroCitation \"public API\"]` if it ships for \
    downstream"

meta def zeroCitationLinter : EnvLinter where
  test := zeroCitationTest
  noErrorsFound := "every theorem is cited outside its own module or pinned by a test"
  errorsFound := "theorems with zero citations outside their own module"

end LintKit

-- the census linter: registered default-OFF via the `default_false` token
-- (LintKit.Basic — the one-liner registration).
register_guestlang_linter linter.guestlang.zeroCitation
  LintKit.zeroCitationLinter default_false
  "flag theorems referenced nowhere outside their own module (the \
    proof-level leftover rule — census: default OFF, promote to gate \
    after the false-positive review)"
