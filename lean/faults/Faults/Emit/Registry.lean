/-
# Faults.Emit.Registry — the emitter registry (the buf plugin model)

Mirrors `SchemaLang.Emit.Registry`: one `Emitter` record per artifact,
declared output paths (the one-writer audit surface), pure `run`. The
driver (`GenMain`) iterates `jobs`, prepends the GENERATED header from
each emitter's `style` + `specSource`, and writes — emitters never
prepend headers themselves (the `CodegenCore.Emit.Core` contract).

faults has TWO spec sources (guest `Spec.apiFaults`, host
`Spec.hostFaults`), so unlike schema-lang (one spec, many emitters) the
registry pairs each emitter with the spec it consumes (`jobs`). The
audit surface — declared `outputs`, `pathsUnique`, header-via-driver,
pure `run` — is identical.
-/
import CodegenCore
import Faults.Registry
import Faults.Emit.Rust
import Faults.Spec.Demo
import Faults.Spec.Host

namespace Faults.Emit

open CodegenCore.Emit

/-- The spec a faults emitter consumes: a coded failure-mode registry
    (name uniqueness + code collision-freedom in the type, W7.4). -/
abbrev FaultsSpec := CodegenCore.CodedRegistry FailureModeItem

/-- The empty registry (the forge-jobs emitter consumes no fault
    registry — it emits the driver manifest). -/
def noFaults : FaultsSpec :=
  { items := [], nameOf := (·.name), codePrefix := "E", start := 100 }

/-- The guest emitter: `OrderError` + `init_guest`, from `Spec.apiFaults`. -/
def guestEmitter : Emitter FaultsSpec where
  name := "faults-guest"
  style := .doubleSlash
  specSource := "Faults/Spec/Demo.lean"
  outputs := ["../../src/faults_generated.rs"]
  run items :=
    [ { path := "../../src/faults_generated.rs"
      , contents := Rust.renderModule (Rust.faultModule "OrderError" items.codes) } ]

/-- The host emitter: `HostFault` + `init_host`, from `Spec.hostFaults`. -/
def hostEmitter : Emitter FaultsSpec where
  name := "faults-host"
  style := .doubleSlash
  specSource := "Faults/Spec/Host.lean"
  outputs := ["../../src/host_faults_generated.rs"]
  run items :=
    [ { path := "../../src/host_faults_generated.rs"
      , contents := Rust.renderModule (Rust.faultModule "HostFault" items.codes (guest? := false)) } ]

/-- The emitters (order = write order). -/
def emitters : List (Emitter FaultsSpec) := [guestEmitter, hostEmitter]

/-- Audit: no two emitters claim the same output path. -/
def pathsUnique : Bool := (emitters.flatMap (·.outputs)).Nodup

/-! ## The forge-driver manifest row

Same pattern as `SchemaLang.Emit`: the job row is a LITERAL copy of the
registry's outputs under the driver exe (the copy breaks the
cycle rows → registry → manifest emitter → rows), and
`jobsCoverEmitters` makes the copy's drift a TEST FAILURE. forge unions
the per-package manifest files and byte-ties every listed output.
-/

def forgeJobs : List (String × List String) :=
  [("faults-gen",
    [ "../../src/faults_generated.rs"
    , "../../src/host_faults_generated.rs"
    ])]

def jobsCoverEmitters : Bool :=
  (emitters.flatMap (·.outputs)) == forgeJobs.flatMap (·.2)

/-- The manifest rows for this package (forge unions rows across
    packages; brackets + header come from the writer). Paths are
    REPO-ROOT-relative (forge joins from the root). -/
def forgeJobsLines : List String :=
  -- RAW outputs: `jobJson` roots paths itself (`CodegenCore.Emit.rootRel`) —
  -- mapping here too would root twice.
  forgeJobs.map fun (exe, outputs) =>
    SchemaLang.Emit.jobJson "faults" exe [] outputs

def forgeJobsEmitter : Emitter FaultsSpec where
  name := "forge-jobs"
  style := .hash
  specSource := "Faults.Emit.Registry (forgeJobs)"
  outputs := ["../../crates/forge/src/faults_jobs_generated.json"]
  run _ :=
    [{ path := "../../crates/forge/src/faults_jobs_generated.json"
       contents := "[\n" ++ String.intercalate ",\n" forgeJobsLines ++ "\n]\n" }]

/-- Pair each emitter with the spec it consumes (faults has two spec
    sources, so the driver runs each with its own registry). The
    forge-jobs emitter consumes no fault registry — it emits the driver
    manifest — so it pairs with the empty registry. -/
def jobs : List (Emitter FaultsSpec × FaultsSpec) :=
  [(guestEmitter, Spec.apiFaults), (hostEmitter, Spec.hostFaults)
   , (forgeJobsEmitter, noFaults)]

/-! ## The schema-elaboration block (the ONE E-code universe, completed)

`SchemaLang.SchemaDiag` — the elaboration-level diagnostics — previously
had NO codes: a DISJOINT second universe (elaboration errors unnumbered,
fault codes E100+). They join the SAME space here, where both fault
registries and schema-lang are visible (faults sits downstream of
schema-lang — the payloads are `Ty`-typed — so the schedule cannot live
on the other side of the import edge). The block starts AFTER the guest
and host fault registries (DERIVED — `100 + guest + host`, never
hand-set), allocated by the SAME `CodegenCore.allocateCodes` over the
diag-kind names. Append-only registry ⇒ stable codes, CI byte-tie
enforces. -/

-- The `SchemaDiag` kinds + kind function, DERIVED at elaboration from
-- the inductive's actual constructor list (`CodegenCore.Registry`'s
-- `derive_ctor_kinds` — the hand mirror is deleted; a `SchemaDiag` edit
-- re-derives both, and the generated match stays total by compiler-
-- enforced exhaustiveness). The derived constructor DECLARATION ORDER
-- is the allocation/lookup key order — the byte-tie and the Tests'
-- E108/E109 pins are the regression controls on its stability.
derive_ctor_kinds schemaDiagKinds schemaDiagKind from SchemaLang.SchemaDiag

/-- The schema-diag E-codes: same allocator, same space, after the
    fault registries. -/
def schemaDiagCodes : List (String × String) :=
  CodegenCore.allocateCodes "E"
    (100 + Spec.apiFaults.items.length + Spec.hostFaults.items.length) schemaDiagKinds

/-- The coded render: the diag + its E-code — the cross-ref is ONE
    lookup into `schemaDiagCodes` (no second allocation to drift). -/
def renderDiagCoded (d : SchemaLang.SchemaDiag) : String :=
  match schemaDiagCodes.lookup (schemaDiagKind d) with
  | some c => s!"[{c}] {SchemaLang.SchemaDiag.render d}"
  | none => SchemaLang.SchemaDiag.render d


end Faults.Emit
