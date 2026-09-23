/-
# CodegenCore.GenKit — the `declare_*` generation runtime

The `declare_*` sibling of `register_check_attribute` (AttrKit): the glue
EVERY generating command re-implemented, landed once with its first clients.
Consumers read (`Machines/Dsl.lean` didYouMeanError, `Templates.lean`'s
duplicate gates, `Faults/Registry.lean` registerFaultItem,
`SchemaLang/EnumWire.lean` elabGenerated + fresh-name checks — the honest
shared idioms, extracted verbatim):

* the closed-world unknown-name rejection — the error ENUMERATES the legal
  space (names, clauses, slots) and appends the did-you-mean over
  `CodegenCore.didYouMean` (nearest first, empty = nothing close);
* the fresh-name gate — a duplicate registration is an ELABORATION error,
  carrying the same did-you-mean (the registry rejects; no overwrite path);
* the generated-decl stamp — `@[derived]` (LintKit.Basic) marks what a
  command EMITS so env-linters exempt it structurally; `stampDerived` rides
  the `addDecl` route where no source syntax exists for the attribute.

Placement: codegen-core (every error path downstream reaches it core-only),
with the stamp's registration in LintKit — the import DAG's first package;
codegen-core imports LintKit, never the reverse (the importBan rows).

Deliberate exclusions (anti-museum — the runtime earns each piece WITH its
clients): no emit-buffer abstraction, no diagnostic inductive, no message
framework. What a `declare_*` command needs beyond this kit is command-
specific by nature (cardinality tables, item shapes) and stays local.
-/

module

public import Lean
public import CodegenCore.DidYouMean
public meta import LintKit.Basic

@[expose] public section

open Lean

namespace CodegenCore

/-- The did-you-mean suffix every DSL error path appends (the one tree-wide
    format; was `Machines.Dsl.didYouMeanHint`, extracted). `didYouMean`
    returns the candidates nearest first; empty candidates = empty suffix. -/
def didYouMeanSuffix (got : String) (cands : List String) : String :=
  let c := didYouMean got cands
  if c.isEmpty then "" else s!" — did you mean: {String.intercalate ", " c}?"

/-- The unknown-name rejection MESSAGE (pure core; `unknownNameError` throws
    it): the error names the context, the rejected `got`, WHAT it is, and
    ENUMERATES the legal space — the closed-world discipline (errors list
    the valid moves, they don't guess). -/
def unknownNameMessage (ctx got what : String) (legal : List String) : String :=
  s!"{ctx}: unknown {what} `{got}` — legal {what}s: " ++
    String.intercalate ", " (legal.map (fun l => s!"`{l}`")) ++
    didYouMeanSuffix got legal

/-- The unknown-name rejection: the enumerated-legal-space + did-you-mean
    error, one shape (was `Machines.Dsl.didYouMeanError`'s clause rejection;
    the Templates/faults slot-and-name rejections share the format). -/
def unknownNameError [Monad m] [MonadError m]
    (ctx got what : String) (legal : List String) : m Unit :=
  throwError (unknownNameMessage ctx got what legal)

/-- The fresh-name VERDICT (pure core; `freshNameCheck` throws it):
    `none` = fresh, `some msg` = the duplicate-decl rejection with the
    did-you-mean over the taken space. -/
def freshNameVerdict (ctx proposed what : String) (taken : List String) :
    Option String :=
  if taken.contains proposed then
    some (s!"{ctx}: `{proposed}` is already a registered {what} — "
      ++ "names must be fresh" ++ didYouMeanSuffix proposed taken)
  else none

/-- The fresh-name gate: a duplicate-decl rejection at elaboration (the
    `derive_*` discipline — the registry rejects, there is no overwrite
    path). -/
def freshNameCheck [Monad m] [MonadError m]
    (ctx proposed what : String) (taken : List String) : m Unit :=
  match freshNameVerdict ctx proposed what taken with
  | none => pure ()
  | some msg => throwError msg

end CodegenCore

public meta section

open Lean.Elab.Command

namespace CodegenCore

/-- Elaborate ONE generated declaration (source text → parsed command →
    elabCommand). Parse errors are internal (the generator wrote them).
    PROVENANCE: extracted verbatim from `SchemaLang.EnumWire.elabGenerated`
    — the one copy for every `declare_*` command's emit loop. -/
meta def elabGenerated (src : String) : CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← getEnv) `command src with
  | .ok stx => elabCommand stx
  | .error e =>
      throwError "generation runtime: internal: generated code failed to parse\n{e}"

/-- The `addDecl`-route `@[derived]` stamp: a command that assembles the
    `Declaration` itself (e.g. `schema_update`'s emitted instances) has no
    source syntax for the attribute to ride — it stamps here instead. The
    elabCommand route writes `@[derived]` in the generated source directly.
    (The registration lives in LintKit.Basic; see its header.) -/
meta def stampDerived (decl : Name) : CommandElabM Unit :=
  LintKit.stampDerived decl

end CodegenCore
