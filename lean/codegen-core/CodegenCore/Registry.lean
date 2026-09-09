/-
# CodegenCore.Registry — the one-source-of-truth pattern

Lifted from flatland's `Codegen.Registry` (notes/lean/lean-v3.md Part 7.1),
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

end CodegenCore
