/-
# CodegenCore.Registry — the one-source-of-truth pattern

Lifted from flatland's `Codegen.Registry` (flatland's notes/lean/lean-v3.md Part 7.1),
generalized: one `SimplePersistentEnvExtension` per item kind; registration
is attribute-first (the attribute layer lands with the emitters); emitters
run post-elaboration over the compiled environment, folding these
extensions.

The machinery is generic over the item type. Domain items (schema records,
export signatures, failure modes, WIT resources) live in the packages above
this one — they supply the item structure and call `mkRegistryExt`.

Staging note (flatland's own discipline, kept): v1 of any registry keeps
the items a plain `def : List Item` for deterministic order; attribute
registration moves over when the authoring DSL lands. The emitter reads
the list either way.

The `RegistrySpec`/`mkRegistryExt` split is so the semantics (append on
add, concatenate on import — boring on purpose, the bus-factor rule) can
be tested purely, without an environment.
-/

import Lean

open Lean
open Lean.Elab.Command
open Lean.Parser.Term

namespace CodegenCore

/-! ## The registry semantics (pure, testable) -/

/-- The two operations every registry shares: append on add, concatenate
    all imported arrays on import. Extracted so tests exercise the
    semantics without an environment. -/
structure RegistrySpec (α : Type) where
  /-- Append one item (registry is append-only; order = registration order). -/
  addEntryFn : List α → α → List α
  /-- Merge imported environments: keep order, concatenate. -/
  addImportedFn : Array (Array α) → List α

/-- The semantics, as data. -/
def registrySpec : RegistrySpec α where
  addEntryFn := fun xs x => xs ++ [x]
  addImportedFn := fun ess => ess.foldl (fun acc arr => acc ++ arr.toList) []

/-! ## The extension factory -/

/-- One `SimplePersistentEnvExtension` per item kind. Call from
    `initialize`:

    ```
    initialize myItemExt : SimplePersistentEnvExtension MyItem (List MyItem) ←
      mkRegistryExt `myMyItemExt
    ```
-/
def mkRegistryExt {α : Type} [Inhabited α] (name : Name) :
    IO (SimplePersistentEnvExtension α (List α)) :=
  registerSimplePersistentEnvExtension {
    name := name
    addEntryFn := registrySpec.addEntryFn
    addImportedFn := registrySpec.addImportedFn
  }

/-- Read the registered items of the current environment (the emitter
    entry point). -/
def Registry.all {α : Type} (ext : SimplePersistentEnvExtension α (List α)) :
    CoreM (List α) :=
  return ext.getState (← getEnv)

/-! ## The driver preamble (runtime registry loading)

Driver exes (GenMain, test harnesses) replay the registry from compiled
oleans at RUNTIME: `initSearchPath` (+ any package-local build dirs),
`enableInitializersExecution`, `importModules` with `loadExts := true` —
without the replay the extension comes back EMPTY. One copy here; every
driver calls it. -/

/-- Import `modules` with their persistent env extensions replayed,
    returning the elaborated environment. `extraPaths` are appended to
    the search path (a direct binary run lacks LEAN_PATH; tests pass
    their package build dir). Unsafe: executes imported initializers. -/
unsafe def importModulesReplayed (modules : Array Name)
    (extraPaths : List System.FilePath := []) : IO Environment := do
  initSearchPath (← findSysroot)
  searchPathRef.modify fun sp => sp ++ extraPaths
  enableInitializersExecution
  importModules (modules.map ({ module := · })) (opts := {}) (loadExts := true)

/-- Load the items registered into `ext` by `modules` (the whole
    importModules+loadExts preamble). -/
unsafe def loadRegisteredItems {α : Type}
    (ext : SimplePersistentEnvExtension α (List α)) (modules : Array Name)
    (extraPaths : List System.FilePath := []) : IO (List α) := do
  let env ← importModulesReplayed modules extraPaths
  pure (ext.getState env)

/-! ## Code allocation

Codes are derived from registry position — stable because the registry is
append-only and CI-regen-diffed. Codes are NEVER hand-set: collision-free
by construction, and they mean the same thing in DSL elaboration errors and
fast-observe runtime reports. -/

/-- Allocate `"E{100+i}"`-style identifiers from list position. -/
def allocateCodes {α : Type} (pre : String) (start : Nat) (items : List α) :
    List (α × String) :=
  items.zipIdx.map (fun (item, i) => (item, s!"{pre}{start + i}"))

/-- Code allocation preserves count — one code per failure mode, always. -/
theorem allocateCodes_length {α : Type} (pre : String) (start : Nat)
    (items : List α) :
    (allocateCodes pre start items).length = items.length := by
  simp [allocateCodes]

/-! ## Ctor-kind derivation (the diag-kind pattern, W7.4)

A registry of diagnostic kinds keyed by an inductive's constructors was
historically TWO hand mirrors: the constructor-name list (the allocation
key order) and the kind function (a hand `match`). Both are derived here
from `getConstInfoInduct` at elaboration: the kind list is the
constructor list, and the kind function is a match over ALL constructors
— exhaustiveness is compiler-enforced at every build, so the mirror
cannot drift. First consumer: faults' E-code block for
`SchemaLang.SchemaDiag`. -/

/-- The constructor's short name (last component — schema-lang
    `ctorNameOf`'s trick, robust to namespaced ctors). -/
def ctorShortName (ctor : Name) : String :=
  (String.splitOn ctor.toString ".").getLast!

/-- `derive_ctor_kinds kindsName fnName from InductiveName` — define

    1. `def kindsName : List String` — the constructor short names, in
       declaration order (the allocation/lookup key order).
    2. `def fnName : InductiveName → String` — the kind function, a
       generated match over every constructor.

    Parameterized or indexed inductives are rejected (the generated
    match binds no type arguments). An unknown or non-inductive name is
    an elaboration error — the derivation cannot silently go stale. -/
syntax (name := deriveCtorKinds)
  "derive_ctor_kinds " ident ident " from " ident : command

@[command_elab deriveCtorKinds]
def deriveCtorKindsImpl : CommandElab := fun stx => do
  let kindsName := stx[1].getId
  let fnName := stx[2].getId
  let indName := stx[4].getId
  let indVal ← getConstInfoInduct indName
  if indVal.numParams != 0 || indVal.numIndices != 0 then
    throwError "derive_ctor_kinds: `{indName}` has parameters or indices — \
      the generated match binds no type arguments"
  let kinds := indVal.ctors.map ctorShortName
  let kindsTerm : Term := quote kinds
  elabCommand (← `(def $(mkIdent kindsName) : List String := $kindsTerm))
  let alts : Array (TSyntax ``matchAlt) ← indVal.ctors.toArray.mapM fun ctor => do
    let cinfo ← getConstInfoCtor ctor
    let holes : Array Term :=
      (List.replicate (cinfo.numParams + cinfo.numFields) (← `(_))).toArray
    let pat : Term ← `(@$(mkIdent ctor):ident $holes:term*)
    `(matchAltExpr| | $pat:term => $(quote (ctorShortName ctor)))
  let d := mkIdent `d
  elabCommand (← `(def $(mkIdent fnName) : $(mkIdent indName) → String
    := fun $d => match $d:ident with $alts:matchAlt*))

end CodegenCore
