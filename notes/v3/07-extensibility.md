# 07 — The extensibility cookbook

"To add an X, fill N rows and instances." Every capability kind has a
recipe with a checklist. A feature that can't be expressed this way is a
design failure: stop, revisit 01, and only then extend the catalog.

## The growth metric

The number that matters is the MARGINAL COST of the next thing:
(new LOC)/capability, reviewed at each phase gate. Rows + instances =
the architecture is healthy; new modules/universes/proof families per
capability = revisit 01.

## R1. Add a target language (data target)

1. A lowering instance over the closed `Ty` (leaves + wrappers; never a
   new universe).
2. A typed target AST where the target supports it — misrendering
   unconstructible.
3. A correspondence row: text targets → the 05 grammar value (inversion
   generated); value targets → the graded carrier's strongest honest law.
4. An Emitter row (outputs nodup in the type; the law or the header
   note) + the byte-tie golden + the self-audit row.
5. The duel/regression hook for semantics-bearing targets (04 §4 names
   the observer).

Checklist: cone ✓ · closed matches only ✓ · curated errors ✓ ·
elab-shallow ✓ · this recipe's entry updated ✓.

## R2. Add a record capability

1. A `deriving`-staged handler per 05 §3: read the record's description
   → derive via generic definitions + generic theorems (thin wrappers) →
   `@[derived]` → curated failures.
2. Register the rows in the Universe + snapshot case.
3. Extend the capability list in 08.
Checklist: diagnostics land with the FIRST capability ✓ · end-to-end
slice (record → derive → artifact → byte-tie → duel) ✓ · no hand mirror
(the description layer) ✓ · derivation is lazy (requested capabilities
only) ✓.

## R3. Add a lane (invariants, updates, keys, witnesses, migrations)

1. A Universe field + a Statement/registry member (declare_registry_member).
2. A snapshot case + a breaking-gate diff row.
3. Emitter rows folding the lane (recordGroupedModule/family! reuse).
4. The obligation rows (tiers computed, evidence closed, kit discharge).
Checklist: no new registry machinery ✓ · no new obligation trio ✓ ·
no new parser/emitter module class ✓.

## R4. Add a DSL (authoring surface)

1. A grammar spec (05 §1) with labels + payload correspondences.
2. `dsl!` → elaborator + unexpanders + printer.
3. Curated instance-gate failures (never a synthesis wall).
4. The valid-space rows + did-you-mean data per construct.
Checklist: no hand-written syntax-category + elaborator + unexpander
trio ✓ (the third+ DSL MUST use dsl!; the first two migrate).

## R5. Add a legality (a new judgment)

1. A Statement instance (checker + sound; completeness `.missing` unless
   proved) + its mounts (gate/lint/test/obligation/monitor).
2. A closed evidence kind + the tier mapping.
3. The curated failure enumerating the valid space.
Checklist: no new check-shaped infrastructure ✓ · the E-code row from
the persisted registry ✓ · the feasibility note where vacuity is
possible (04 §5) ✓.

## R6. Add an op / semantic primitive

1. A row in the ONE op table (name, arity, semantics, spellings,
   renderings, contracts) — expression eval, raw/compiled readings,
   emission, oracle, proof are all folds of it.
2. The typed-AST/spelling instance per target.
3. The property battery (positive + negative rows) generated.
Checklist: no new per-op hand places (no parallel semantics tables,
eval arms, or spellings) ✓.

## The reuse contract

Before ANY mechanism: name the table it folds (Registry/Interpretation/
Correspondence/Statement), the kit it mounts, the recipe it implements.
None fits → the catalog is incomplete — extend it WITH the first
consumer, never before. The leftover rule: every new module/capability
sits in this file's recipe table with its consumer; unreachable rows are
wired or deleted at phase boundaries (P8).
