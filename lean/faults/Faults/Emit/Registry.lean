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

/-- Pair each emitter with the spec it consumes (faults has two spec
    sources, so the driver runs each with its own registry). -/
def jobs : List (Emitter FaultsSpec × FaultsSpec) :=
  [(guestEmitter, Spec.apiFaults), (hostEmitter, Spec.hostFaults)]

/-- Audit: no two emitters claim the same output path. -/
def pathsUnique : Bool := (emitters.flatMap (·.outputs)).Nodup

end Faults.Emit
