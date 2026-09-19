/- Axiom gate — the QLang surface must print only the core triple
   (+ disclosed native_decide). The compile fold's resolution proof is a
   term-level `rfl`-chain: no axioms, no sorryAx. -/
import QLang

-- the dynamic-surface compiler (instance-as-data reification)
#print axioms QLang.compile
#print axioms QLang.compileCol
#print axioms QLang.compileSpine
#print axioms QLang.HasCol.ofIndex

-- the query log (fusion canon + error accumulation)
#print axioms QLang.Query.filter
#print axioms QLang.Query.project
#print axioms QLang.Query.sort
#print axioms QLang.Query.fetch
#print axioms QLang.Query.checked
#print axioms QLang.Query.fromRegistry

-- the error system (the suggestion engine is CodegenCore's — gated there)
#print axioms QLang.QLangError.unknownColumnMsg
#print axioms QLang.Registry.find
