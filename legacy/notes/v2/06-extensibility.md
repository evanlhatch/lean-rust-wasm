# 06 — Extensibility: the cookbook

"To add an X, fill N rows and instances." Every capability kind has a recipe
with a checklist. A feature that cannot be expressed this way is a design
failure: stop, revisit 02, and (only then) extend the catalog in 05.

## Recipes

### R1. Add a target language (data target)
1. A `tyLower`/`ShapeLang` instance over the closed `Ty` (leaves + wrappers;
   never a new universe).
2. A typed target AST (`RustItem : Ty → Type`, `WitTy`, …) — misrendering
   unconstructible.
3. A grammar row if text/invertible (03) — for text targets, `declare_inversion`
   gives the inverse/wire-roundtrip; for value targets, a `PartialIso`/`Iso`
   with the law in the type.
4. An `Emitter` row (outputs + law + header), the byte-tie golden, and the
   self-audit row.
5. A duel/regression hook (08) — the differential oracle row for semantics-
   bearing targets.
Checklist: cone ✓ · closed matches only ✓ · curated errors (04) ✓ · elab-shallow
(01 §2 addendum) ✓ · `06` recipe entry written ✓.

### R2. Add a record capability
1. A `deriving`-staged handler (05 §2) following the WireCodec precedent:
   read record → emit surface + laws + rows via the ONE reifier → `@[derived]`
   stamp → curated failures.
2. Register its rows in the One Universe + the snapshot case.
3. Extend the capability list in 05 §2.
Checklist: diagnostics land with the FIRST capability ✓ · end-to-end slice
(record → derive → artifact → byte-tie → duel) ✓ · no hand mirror (reifier) ✓.

### R3. Add a lane (invariants, updates, keys, witnesses, migrations)
1. A `Universe` field + a Statement/registry member (`declare_registry_member`).
2. A snapshot case; a breaking-gate diff row.
3. Emitter rows that fold the lane (reuse `recordGroupedModule`/`family!`).
4. The obligation rows (tiers computed, evidence closed, discharge from the
   kit — 05 §1).
Checklist: no new registry machinery (MemberKit) ✓ · no new obligation trio ✓ ·
no new parser/emitter module class ✓.

### R4. Add a DSL (authoring surface)
1. A grammar spec (03) with labels + correspondence payloads.
2. `dsl!` → elaborator + unexpanders + printer (03 §7).
3. Curated instance-gate failures (04 §3) — the surface never shows a
   synthesis wall.
4. Rows: the valid space per construct; did-you-mean data.
Checklist: no hand-written syntax category + elaborator + unexpander trio ✓.
(Rule: the third+ DSL in the tree is REQUIRED to use `dsl!`; the first two are
migrations.)

### R5. Add a legality (new judgment)
1. A `Statement` instance (checker + sound; completeness `.missing` unless
   proved) + mounts (gate/lint/test).
2. A closed evidence kind and a Tier mapping (05 §1).
3. Curated failure (04) enumeration of the valid space.
Checklist: no new check-shaped infrastructure ✓ · E-code row ✓.

### R6. Add an op / semantic primitive
1. A row in the op table (name, arity, semantics, spellings, renderings,
   contracts) — across the ONE table: expression eval, raw/compiled readings,
   emission, oracle, proof (01 §4 "one table many consumers").
2. The typed-AST/spelling instance per target.
3. The property battery (positive + negative rows) generated (08).
Checklist: no new per-op hand places (no parallel binop tables, no parallel
eval arms, no parallel spellings) ✓.

## The reuse contract

- Before ANY mechanism: name the table it folds (Registry/Interpretation/
  Correspondence/Emitter/Statement), the kit it mounts, and the recipe (R1–R6)
  it implements. If none fits, the catalog (05) is incomplete — extend it WITH
  the first consumer, never before.
- The leftover rule: every new module/capability sits in the 06 recipe table
  with its consumer; unreachable rows are deleted at phase boundaries.
- The growth test: the marginal cost of the NEXT capability ≈ rows + instances;
  measured as (new LOC)/capability and reviewed at each phase gate.
