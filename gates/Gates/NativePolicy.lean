/-
Gates.NativePolicy — the native_decide grandfathering gate
(`gates native-policy`; mined from legacy/lean/gates/Gates/NativePolicy.lean,
ported fresh at the fresh tree's scale — no sharding, no Baseline lane).

The rule: lean4lean does NOT support `reduceBool` (the kernel extension
`native_decide` reduces through), so a declaration on the
native_decide trust base is OUTSIDE the independent kernel's checking.
Allowed uses are a COMMITTED ALLOWLIST SET (`allowlistedNative` —
(package dir, module) granularity, additive ONLY with a disclosed
justification in the same commit). The ratchet discipline, fail-closed
both ways:

- a `_native.native_decide.` dependency OUTSIDE the allowlist FAILS;
- a STALE allowlist entry — a listed module whose cone has zero
  native_decide dependencies (the exile was re-proved) — FAILS too
  (remove the entry).

How the trust base manifests (probe-verified in the legacy tree,
v4.33.0): `native_decide` mints a per-declaration axiom named
`<decl>._native.native_decide.ax_<N>_<M>` inside the cone (with the
`_private.` mangling in module-mode files); substring match on
`_native.native_decide.` survives both shapes.

THE FRESH TREE'S STATE: the allowlist is the EMPTY SET and the sweep
reports zero native_decide dependencies tree-wide — the gate is
teeth-ready with the empty set (a new use fails; a stale entry fails).

The five questions (notes/v3/01-core.md):
- root: none — the trust-basis boundary over the gated set.
- carrier grade: none — kernel-collected axiom cones, not a crossing.
- spine reading: the enforcement face of 01 §7's ladder (the allowlist
  accepts the core triple + the DISCLOSED native_decide bases only).
- ladder rung: the ladder's enforcement, not a rung.
- gate row: the native-policy row itself (`gates native-policy`).
-/
import Lean
import LintKit
import Gates.Packages

open Lean

namespace Gates.NativePolicy

open Gates (PkgSpec gatedPackages)

/-- The committed allowlist: the disclosed native_decide trust bases,
    at (package dir, defining module) granularity. ADDITIVE ONLY, with
    a disclosed justification landing in the same commit (the module's
    header + its Tests/Axioms.lean carry the disclosure). An entry
    whose module goes `_native`-free FAILS as stale (remove it).

    The fresh tree: EMPTY — there are zero native_decide uses. This
    array is the gate's teeth-ready ratchet. -/
def allowlistedNative : Array (String × Name) := #[]

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

/-- Import one package's roots via the shared loadPkgEnv preamble and
    analyze. -/
unsafe def analyzePkg (base : SearchPath) (pkg : PkgSpec) : IO PkgReport := do
  match ← Gates.loadPkgEnv base pkg with
  | .error e =>
    return { dir := pkg.dir, loadError := some e }
  | .ok env =>
    let modRoots := pkg.roots.map (·.getRoot)
    let ctx : Core.Context := { fileName := "<gates-native-policy>", fileMap := default }
    let ((decls, native), _) ← (analyzeEnv modRoots).toIO ctx { env := env }
    return { dir := pkg.dir, decls := decls.size, native := native }

/-- The gate, ONE package per process (the shard): flag every decl on
    the native_decide trust base outside the allowlist (fail-closed),
    and check this package's allowlist entries for staleness
    (fail-closed the other way — a done exile must be removed). Exit 0
    iff clean. The SHARD exists for the same reason as the lint
    driver's: libgc's conservative stack scan retains each dropped env
    — folding all 37 gated packages' envs in one process peaked past
    the OOM line (observed, SIGTERM) once the table completed. -/
unsafe def runPackage (pkg : PkgSpec) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.searchPathRef.get
  let r ← analyzePkg base pkg
  match r.loadError with
  | some e =>
      IO.println s!"{pkg.dir}: LOAD FAILED — {e}"
      return 1
  | none =>
    let mut failed := false
    let mut totalNative := 0
    -- this package's allowlist slice: an entry no scan matches
    -- survives here and fails the shard
    let mut stale : Array (String × Name) :=
      allowlistedNative.filter fun (d, _) => d == pkg.dir
    for (m, d) in r.native do
      totalNative := totalNative + 1
      if allowlistedNative.contains (pkg.dir, m) then
        stale := stale.erase (pkg.dir, m)
        IO.println s!"{pkg.dir}: {d} — on the native_decide trust base, \
          DISCLOSED ({m} is an allowlisted exile)"
      else
        IO.eprintln s!"{pkg.dir}: VIOLATION — {d} (module {m}) depends on \
          the native_decide trust base outside the allowlist"
        failed := true
    unless stale.isEmpty do
      failed := true
      IO.eprintln "native-policy: STALE allowlist entries — these modules no \
        longer depend on native_decide; remove the entries (the exile was re-proved):"
      for (d, m) in stale do
        IO.eprintln s!"  {d}/{m}"
    unless failed do
      IO.println s!"native-policy: {pkg.dir} — {r.decls} decls checked, \
        {totalNative} native_decide dependency(ies), allowlist clean"
    return if failed then 1 else 0

/-- The gate: per gated package, one CHILD process (the shard above;
    the same shape `Gates.runAll` uses for the gate rows), stdio
    inherited so the findings stream live; first failure fails the
    fold. Exit 0 iff every shard is clean. -/
unsafe def run (package : Option String) : IO UInt32 := do
  match package with
  | some dir =>
      match gatedPackages.toList.find? fun p => p.dir == dir with
      | none =>
          IO.eprintln s!"native-policy: --package={dir} names no \
            Gates.Packages row"
          return 1
      | some pkg => runPackage pkg
  | none =>
      let mut failed := false
      for pkg in gatedPackages do
        let child ← IO.Process.spawn
          { cmd := "lake"
          , args := #["exe", "gates", "native-policy",
                      s!"--package={pkg.dir}"]
          , stdout := .inherit, stderr := .inherit }
        let code ← child.wait
        if code != 0 then failed := true
      if failed then return 1
      IO.println s!"native-policy: clean — every gated package's decls \
        inside the allowlist ({gatedPackages.size} shard(s); the ratchet \
        is live)"
      return 0

end Gates.NativePolicy
