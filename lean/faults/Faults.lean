/- Faults — the failure-mode registry + fast-observe emission.

   GenMain (the artifact writer) is a separate exe root: it imports the
   lib, never the reverse (one-writer discipline). -/
import Faults.Category
import Faults.Registry
import Faults.Emit.Rust
import Faults.Spec.Demo
