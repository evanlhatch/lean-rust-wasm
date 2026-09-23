/- TestKit — the shared test harness (fresh, core-only: no LSpec, no
   Plausible, no mathlib). The root module names the surface: Lcg (the
   seeded generator), Spec (the ONE spec structure + the verdict),
   Harness (the check runner + the driver), Golden (the byte-tie
   compare). Module headers state ownership + exclusions per module.

   The five questions (notes/v3/01-core.md): answered per submodule;
   the umbrella answers none — import point. Gate row: none — TestKit
   is not in Gates.Packages' gated set; TestKitTests is its evidence. -/

module

public import TestKit.Lcg
public import TestKit.Spec
public import TestKit.Harness
public import TestKit.Golden

@[expose] public section
