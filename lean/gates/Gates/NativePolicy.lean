/-
# Gates.NativePolicy — the native_decide grandfathering gate (`gates native-policy`)

W9.7, implementing notes/design-guest-verified.md §6.3 + the
notes/lean-doctrine.md §3 rule it added: lean4lean does NOT support
`reduceBool` (the kernel extension `native_decide` reduces through), so
any declaration on the `_native` trust base is OUTSIDE the independent
kernel's checking. Rule: decls in the lean4lean-checked set must not
depend on the native_decide trust base. The 3 disclosed uses are
grandfathered as permanent checked-set exiles (design §7 decision 3:
re-proving them buys zero artifact-correctness — edgepython emits no
shipped artifact; the gate's job is preventing NEW uses).

How the trust base MANIFESTS (probe-verified 2026-09-17, v4.33.0):
`native_decide` mints a per-declaration axiom named
`<decl>._native.native_decide.ax_<N>_<M>` inside the cone —
`EdgePython.Parity.parity_double_21._native.native_decide.ax_1_1`
(legacy module) and, in module-mode files, the `_private.` mangled
shape `_private.SchemaLang.Emit.Circuit.0.SchemaLang.Emit.Circuit.
orderTotalCkt_denote_tick3._native.native_decide.ax_1_1`. Substring
match on `_native.native_decide.` (LintKit.AxiomAllowlist's rule, kept
identical in meaning) survives both shapes. The `_native.bv_decide.`
sibling (proofkit's disclosed `u64add_assoc`) is OUT OF SCOPE here:
bv_decide is the verified-LRAT certificate class (the doctrine's
discharge ladder), governed by the axiom allowlist's disclosure
discipline — this gate owns native_decide only.

Mechanics: Gates.Axioms' replay pattern, minus the LintKit runner —
per gated package, importModules the roots, `LintKit.packageDecls` for
the package's own decls, the kernel's `collectAxioms` per decl, flag
any cone containing a `_native.native_decide.` axiom UNLESS the decl's
module (via `const2ModIdx` — the same mechanism packageDecls uses) is
in `grandfatheredNative` below. Grandfathering granularity is
(package dir, MODULE), mirroring `KernelCheck.knownReduceBoolGaps`:
the grandfathered modules are wholly-disclosed trust-basis modules
(their headers + Tests/Axioms.lean carry the disclosure), and per-decl
granularity would fight the `_private.` name mangling. Discovery of a
NEW use INSIDE a grandfathered module stays with `gates axioms`'s
committed-report diff — this gate is the boundary around the modules.

Fail-closed both ways: a `_native` dep outside the allowlist fails; a
STALE allowlist entry (module with zero native_decide deps — the exile
was re-proved) also fails. The allowlist is additive only with a
disclosed justification landing in the same commit (the doctrine rule).

LEGACY (non-module) file: importModules replay + the meta axiom
extension (the Gates.Axioms precedent; constraint 12,
notes/w5-4-module-migration.md).
-/
import Lean
import LintKit
import Gates.Packages
import Gates.Common

open Lean

namespace Gates.NativePolicy

open Gates (PkgSpec gatedPackages)

/-- The grandfathered checked-set exiles (W9.7; design-guest-verified.md
    §6.3 + §7 decision 3; notes/lean-doctrine.md §3). The 3 disclosed
    `native_decide` uses, at (package dir, module) granularity:
    edgepython/EdgePython/Parity.lean (its header: "DISCLOSED trust
    basis"; edgepython/Tests/Axioms.lean) and
    schema-lang/SchemaLang/Emit/Circuit.lean's two theorems
    (`orderTotalCkt_denote_tick3`, `orderTotalIncr_denote_tick3`;
    schema-lang/Tests/Axioms.lean's header). Additive ONLY with a
    disclosed justification in the same commit; an entry whose module
    goes `_native`-free fails as STALE (remove it). -/
def grandfatheredNative : Array (String × Name) := #[
  ("edgepython", `EdgePython.Parity),
  ("schema-lang", `SchemaLang.Emit.Circuit)
]

/-- LintKit.AxiomAllowlist's native_decide rule, kept identical in
    meaning: an axiom name containing `_native.native_decide.`
    (survives both the plain and the `_private.`-mangled shapes). -/
def isNativeDecideAxiom (n : Name) : Bool :=
  ((toString n).splitOn "_native.native_decide.").length != 1

/-- Per-package result: decls checked + every decl whose cone touches
    the native_decide trust base, paired with its defining module. -/
structure PkgReport where
  dir : String
  decls : Nat := 0
  /-- (defining module, decl) for every decl on the trust base. -/
  native : Array (Name × Name) := #[]
  loadError : Option String := none

/-- The package's decls on the native_decide trust base. `none` from
    `const2ModIdx` maps to the anonymous module — it cannot match the
    allowlist, so an unresolvable module is a violation (fail-closed). -/
def analyzeEnv (roots : Array Name) : CoreM (Array Name × Array (Name × Name)) := do
  let env ← getEnv
  let decls ← LintKit.packageDecls env roots
  let mut native : Array (Name × Name) := #[]
  for d in decls do
    if (← collectAxioms d).any isNativeDecideAxiom then
      let m := match env.const2ModIdx[d]? with
        | some idx => env.header.moduleNames[idx]!
        | none => Name.anonymous
      native := native.push (m, d)
  return (decls, native)

/-- Import one package's roots (its olean dir prepended — the
    Axioms.lean search-path lesson) and analyze. -/
unsafe def analyzePkg (base : SearchPath) (pkg : PkgSpec) : IO PkgReport := do
  Lean.searchPathRef.set (pkg.oleanDirOf :: base)
  try
    Lean.enableInitializersExecution
    let env ← importModules (pkg.roots.map ({ module := · })) {}
      (trustLevel := 1024) (loadExts := true)
    let modRoots := pkg.roots.map (·.getRoot)
    let ctx : Core.Context := { fileName := "<gates-native-policy>", fileMap := default }
    let ((decls, native), _) ← (analyzeEnv modRoots).toIO ctx { env := env }
    return { dir := pkg.dir, decls := decls.size, native := native }
  catch e =>
    return { dir := pkg.dir, loadError := some (toString e) }

/-- The `--package` filter lives in Gates.Driver.selectPackages (the
    sharded mode: one env per PROCESS — the full sweep in one process
    accumulates every package's environment and OOMs (the axiom gate's
    lesson); the justfile loops). The stale-entry check is scoped to
    the selected packages. -/
unsafe def run (pkgName : Option String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  let some pkgs ← Driver.selectPackages "native-policy" pkgName | return 1
  let mut violations : Array (String × Name × Name) := #[]
  let mut stale : Array (String × Name) :=
    grandfatheredNative.filter (fun (d, _) => pkgs.any (fun p : PkgSpec => p.dir == d))
  let mut failed := false
  for pkg in pkgs do
    let r ← analyzePkg base pkg
    match r.loadError with
    | some e =>
      IO.println s!"{pkg.dir}: LOAD FAILED — {e}"
      failed := true
    | none =>
      let mut exiled : Nat := 0
      for (m, d) in r.native do
        if grandfatheredNative.contains (pkg.dir, m) then
          stale := stale.erase (pkg.dir, m)
          exiled := exiled + 1
          IO.println s!"{pkg.dir}: {d} — on the native_decide trust base, \
            GRANDFATHERED ({m} is a checked-set exile, §6.3)"
        else
          violations := violations.push (pkg.dir, m, d)
          IO.println s!"{pkg.dir}: VIOLATION — {d} (module {m}) depends on \
            the native_decide trust base outside the grandfathered set"
      IO.println s!"{pkg.dir}: {r.decls} decls checked, {r.native.size} on \
        the trust base ({exiled} grandfathered)"
  unless stale.isEmpty do
    failed := true
    IO.println "native-policy: STALE grandfather entries — these modules no \
      longer depend on native_decide; remove the entries (the exile was re-proved):"
    for (d, m) in stale do IO.println s!"  {d}/{m}"
  if failed || !violations.isEmpty then
    unless violations.isEmpty do
      IO.println s!"native-policy: {violations.size} violation(s) — new \
        native_decide uses need a disclosed justification AND a \
        grandfatheredNative entry in the same commit (notes/lean-doctrine.md §3)"
    return 1
  IO.println "native-policy: clean — the grandfathered three are the only \
    native_decide deps tree-wide"
  return 0

end Gates.NativePolicy
