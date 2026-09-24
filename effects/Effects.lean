/-
# Effects — the umbrella module

One import point for the library. Submodules:

- `Effects.Basic` — the closed effect lattice (the eight atoms) + the
  rows as finite sets with the lattice laws + the effect-annotated
  computation (the row as INDEX; the join computed at the type level;
  the check boundary's sub-effect proof — an over-permissive
  composition fails to elaborate).
- `Effects.Resource` — the resources split SEPARATE (D7: effects are
  upper bounds, resources are usage accounting with context splitting;
  the double-spend's unrepresentability is the point) + the counted
  monus tie (01 §2).
- `Effects.Footprint` — the footprint laws over the minimal state
  model: reads depend only on the declared footprint; writes preserve
  everything outside it; the frame rule composes (the full
  wp-composition is the contracts wave's — 08 §36, named exclusion).

Named exclusions live in each submodule's header (the handlers, the
wp-composition, row polymorphism, the registry-derived rows — each
lands with its first consumer, the leftover rule).
-/

import Effects.Basic
import Effects.Resource
import Effects.Footprint
