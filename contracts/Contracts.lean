/-
# Contracts — requires/ensures with wp-composition (the contract lanes' composition engine)

notes/v3/08-capabilities.md §36: `wp (p >>= k) Q = wp p (fun x => wp
(k x) Q)` — scoped to the contracted lanes; total pure functions keep
direct proofs. The review's §5 is the content discipline: for each
primitive — the execution semantics + the precondition transformer + the
soundness theorem; the compound obligations derive STRUCTURALLY; the
developer writes the program + the postcondition; the toolkit computes
the obligations, discharges the routine fragments, shows the remaining
domain-specific goals. The feasibility discipline is 04 §5.

Modules:
- `Contracts.Wp`         — the fragment + the transformer + the rules
- `Contracts.Contract`   — the surface + the obligation + the feasibility
- `Contracts.WpMachine`  — the wp↔machine bridge (wave 30's A4): the
  fragment's exec + the while carrier as `Machines.Machine` instances,
  `wp_sound` as the simulation (`wp_machine_safe`: the wp's soundness
  implies the machine-level safety), and the four VCs at the machine's
  reachable-states discipline (the invariant reaches, the variant
  bounds the machine's own runs, the exit lands in Q).

The five questions (notes/v3/01-core.md): root/carrier/spine/ladder/
gate answers live in the modules (this umbrella aggregates the imports).
-/

import Contracts.Wp
import Contracts.WpMachine
import Contracts.Contract
