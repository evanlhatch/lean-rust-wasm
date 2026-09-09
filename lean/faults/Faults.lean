/- Faults — the failure-mode registry + fast-observe emission.

   GenMain (the artifact writer) is a separate exe root: it imports the
   lib, never the reverse (one-writer discipline).

   The demo specs (`Faults.Spec.Demo`/`Host`) and the spec-paired emitter
   registry (`Faults.Emit.Registry`) live in the SEPARATE `FaultsSpec`
   lean_lib (mirroring schema-lang's `Demo` split): downstream
   `import Faults` gets the registry machinery without pulling the
   order-shop demo. -/
import Faults.Category
import Faults.Registry
import Faults.Emit.Rust
