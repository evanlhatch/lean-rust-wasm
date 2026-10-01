/-
# Repr — the representation-independence lane

The reviews' §2 (the meaning↔representation split) as a lane: a domain
concept should not equal its current encoding. The discipline
(`Repr.Basic`): the abstract spec + the efficient implementation + the
representation relation `Represents` (the operations' preservation
fields ARE the construction gate) + the composition + THE generic
client theorem — a client of the abstract interface works over ANY
representation.

The worked example (`Repr.FinMap`): the finitely-supported map at TWO
honestly different representations — the sorted assoc list (the
canonical-rep discipline: insort canonicalizes, canonicity theorem =
the retraction-grade face) and the unsorted-with-duplicates write log
(the Abstraction grade: `raw_not_injective` — no inverse exists; the
Iso is claimed nowhere).

Relation to the landed substrate: the zset lane's canonical-rep
discipline (the weight function vs the canonical rep) is THE instance
this lane generalizes; the grades ride `Kit.Correspondence`, the
relation machinery rides `Kit.Relation`.

The five questions (notes/v3/01-core.md):
- root: Universe (the carriers) × Change (the token programs).
- carrier grade: the honest grade per representation — Abstraction at
  minimum; canonicity where earned; NEVER the Iso by default.
- spine reading: none — the lanes' state carriers are the consumers.
- ladder rung: hand theorems of the small generic kind (01 §7).
- gate row: Repr's row in Gates.Packages' gated set; ReprTests.Axioms
  pins the laws' cones (core triple only).

Core-only: no mathlib, no Batteries (the cone rule).
-/
module

public import Repr.Basic
public import Repr.FinMap
@[expose] public section

end -- public section
