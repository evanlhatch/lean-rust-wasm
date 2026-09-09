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

/-- The spec a faults emitter consumes: a failure-mode registry. -/
abbrev FaultsSpec := List FailureModeItem

/-- The guest emitter: `OrderError` + `init_guest`, from `Spec.apiFaults`. -/
def guestEmitter : Emitter FaultsSpec where
  name := "faults-guest"
  style := .doubleSlash
  specSource := "Faults/Spec/Demo.lean"
  outputs := ["../../src/faults_generated.rs"]
  run items :=
    [ { path := "../../src/faults_generated.rs"
      , contents := Rust.renderModule (Rust.faultModule "OrderError" (allocate items)) } ]

/-- The host emitter: `HostFault` + `init_host`, from `Spec.hostFaults`. -/
def hostEmitter : Emitter FaultsSpec where
  name := "faults-host"
  style := .doubleSlash
  specSource := "Faults/Spec/Host.lean"
  outputs := ["../../src/host_faults_generated.rs"]
  run items :=
    [ { path := "../../src/host_faults_generated.rs"
      , contents := Rust.renderModule (Rust.faultModule "HostFault" (allocateHost items) (guest? := false)) } ]

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
  let rootRel := fun (p : String) =>
    match p.dropPrefix? "../../" with | some rest => rest.toString | none => p
  forgeJobs.map fun (exe, outputs) =>
    SchemaLang.Emit.jobJson "faults" exe (outputs.map rootRel)

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
    manifest — so it pairs with the empty list. -/
def jobs : List (Emitter FaultsSpec × FaultsSpec) :=
  [(guestEmitter, Spec.apiFaults), (hostEmitter, Spec.hostFaults)
   , (forgeJobsEmitter, [])]


end Faults.Emit
