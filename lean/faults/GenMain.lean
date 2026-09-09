/-
# Faults.GenMain — the artifact writer (one-writer-per-artifact)

Regenerates the committed fast-observe error module from the failure
registry. Byte-tie CI: `forge gen --check` re-runs this in memory and
diffs — never edit the artifact, regenerate.
-/
import Faults

def faultsOut : System.FilePath := "../../src/faults_generated.rs"

def hostFaultsOut : System.FilePath := "../../src/host_faults_generated.rs"

def main : IO Unit := do
  let hdr := CodegenCore.Emit.header .doubleSlash "faults" "Faults/Spec/Demo.lean"
  let body := Faults.Emit.Rust.faultModule "OrderError"
    (Faults.allocate Faults.Spec.apiFaults)
  IO.FS.writeFile faultsOut (hdr ++ CodegenCore.Emit.Rust.renderModule body)
  IO.println s!"wrote {faultsOut}"

  let hostHdr := CodegenCore.Emit.header .doubleSlash "faults" "Faults/Spec/Host.lean"
  let hostBody := Faults.Emit.Rust.faultModule "HostFault"
    (Faults.allocateHost Faults.Spec.hostFaults) (guest? := false)
  IO.FS.writeFile hostFaultsOut (hostHdr ++ CodegenCore.Emit.Rust.renderModule hostBody)
  IO.println s!"wrote {hostFaultsOut}"
