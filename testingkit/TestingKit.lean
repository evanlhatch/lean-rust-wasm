/- TestingKit — the shared test harness (fresh, core-only: no LSpec, no
   Plausible, no mathlib). The root module names the surface: Lcg (the
   seeded generator), Shrink (the shrinking discipline), Spec (the ONE
   spec structure + the verdict),
   Harness (the check runner + the driver), Golden (the byte-tie
   compare). Module headers state ownership + exclusions per module.

   The five questions (notes/v3/01-core.md): answered per submodule;
   the umbrella answers none — import point. Gate row: none — TestingKit
   is not in Gates.Packages' gated set; TestingKitTests is its evidence. -/

module

public import TestingKit.Lcg
public import TestingKit.Shrink
public import TestingKit.Spec
public import TestingKit.Harness
public import TestingKit.Golden

@[expose] public section
