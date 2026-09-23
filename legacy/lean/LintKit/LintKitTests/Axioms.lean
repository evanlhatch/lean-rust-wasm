/- Axiom gate (uniform with the `just lean-axioms` loop over lean_pkgs):
   LintKit's pure helpers must not smuggle axioms. LintKit ships no
   theorems of its own — its linters are the theorems' enforcement layer —
   so this pins the helpers the census paths exercise. -/
import LintKit

#print axioms LintKit.isAllowedAxiom
#print axioms LintKit.stripBinderNames
#print axioms LintKit.runTextLints
#print axioms LintKit.packagePrefixes
