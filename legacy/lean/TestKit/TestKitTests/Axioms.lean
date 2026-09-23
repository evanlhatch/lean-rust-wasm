/- Axioms gate: TestKit is a harness package — it ships no theorems. This
   file exists so `just lean-axioms` covers it uniformly; it checks the kit's
   core definitions stay axiom-free. -/
import TestKit
#print axioms TestKit.PropSpec.runIO
#print axioms TestKit.Golden.checkAgainstGolden
#print axioms TestKit.suiteOf
