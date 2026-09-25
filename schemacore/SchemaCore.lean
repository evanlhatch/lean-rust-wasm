/-
# SchemaCore — the umbrella module

One import point for the library (root-module imports are NOT
re-exported — this module re-exports by importing):

- `SchemaCore.Ty` — the closed boundary universe (now with the `KeyTy`
  scalar sub-universe for map/set keys and the `bounded` cap-in-type
  lane base).
- `SchemaCore.Value` — the typed value universe + the evaluator (the
  total denotation).
- `SchemaCore.Item` — the item model + the registry + the obligation view.
- `SchemaCore.RowVals` — the positional row layer + the name↔index iso.
- `SchemaCore.Register` — `@[schema]` + the env extension.
- `SchemaCore.Describe` — the typed description universe (D19's ONE
  meta-universe) + the generic rendering derivation + the reflector.
- `SchemaCore.Codec` — the binary value lane (the wire grade over
  `Value`) + the append-form master law.
- `SchemaCore.Derive` — the GENERIC derivation layer over the
  description: the record codec as ALGEBRA values over the ONE walk
  (`foldDescr` — 16-surface §4.4's functorial deepening), the
  correctness claims as claim algebras discharged by the ONE generic
  theorem `law_of_rows` (the append-form law `deriveCodec_correct` +
  the exact-image `deriveDec_eq` are instances), the wire grade
  `deriveCodec`, and the row bridge (`toRowF`/`ofRowF` +
  `rowBridgeIso`) — each law proved ONCE over the
  description structure.
- `SchemaCore.DeriveMeta` — the deriving-handler mounts
  (`deriving WireCodec`, `deriving row_bridge`): the per-record thin
  wrappers, the curated refusals (the Diag envelope), lazily per
  capability.
- `SchemaCore.Emit` — the slice's emitter + the shared regen core.
- `SchemaCore.Emit.Journal` — the journal duel's emitter: the Event
  lane's golden bytes for the `mandate-delta` crate (the delta/journal
  wire's differential vectors, Kit.Duel's convention).
- `SchemaCore.Snapshot` — the universe snapshot (the registry-state
  serialization: the canonical sorted one-line-per-item format, the
  total print/parse pair, the PROVED round trip `parse_print`, the
  emitter row + the gate's ONE reading).
- `SchemaCore.Diff` — the snapshot-pair diff (the NET change over the
  name key) + the compatibility relation + the three-way verdict
  (clean/remedied/unremedied) + the remedy seed (`FieldMigration`, the
  bounded-cap widening exemplar with its soundness obligation).
- `SchemaCore.Delta` — the event-sourcing lane's shared delta variant:
  the keyed semantics, the witnessed delta, the Change-ladder rungs
  (Applicable → WithIdentity → Reversible — the climbs PROVED lawful
  or walled).
- `SchemaCore.Event` — the journal: the event log (the trichotomy's
  event face), the replay (the I fold), the fusion (replay = run), the
  journal codec (append-form), the migration seed (the refusal
  discipline).
- `SchemaCore.Migrate` — the migration lane: the upcaster DERIVED from
  the diff's change set + the registered remedies (the plan GADT —
  removals/renames/reorders unconstructible, the LOUD refusals), the
  key-stability laws, THE ONE INDUCTION (replay preservation), the
  composition law (two hops ≡ the composed plan), and the event-lane
  seed integration (`MigrationSeed.ofPlan` — the gate still refuses an
  unwitnessed replay).
- `SchemaCore.Commit` — the propose→check→commit discipline (as DATA): the
  proposal's lowering to the shared delta carrier, the violation query over
  the post-state, the verdict, the transactional adapter, and the commit
  duel's vector set.
- `SchemaCore.IncViolate` — the incremental violation maintenance (03 §8's
  ΔV face): the maintained faces fold the deltas (the pointwise negative
  face + the join faces under the stable-ids fragment), the named fallback
  checker for deltas outside the fragment, and the agreement theorem — the
  maintained relation IS the recomputed relation.
- `SchemaCore.View` — the writable-views lane (02 §7's relational lenses):
  the view = selection + projection over the keyed table's rows (the
  writeback-TYPED column twin of `Query.Cols`), the reader laws over the
  write spine, the WRITABLE FRAGMENT derived from the key's determinacy
  (the fiber is at most one under the checked `uniqueOn`), the TOTAL
  classifier whose refusals carry the ambiguity as data, the lens
  (`ViewLens`/`keyedViewLens`) with both round-trip laws as fields
  (read-after-write; unchanged-view preservation), the complement frame
  (the unprojected columns survive), and the delta integration (the
  applied edit's verdict carries the shared `RowDelta` + the post-state
  through the keyed applicator).
- `SchemaCore.Profile` — the semantic-profiles lane (16-surface §4.5):
  the closed `Profile` enum + the erasing phantom wrapper + the
  deterministic-float model (`Fixed` — the fixed-point carrier, the
  `Money Cents` shape) with its promise/forfeit laws.
- `SchemaCore.Confluence` — the coordination classifier (02 §8's
  invariant confluence): the four-row verdict
  (`safeUnderMerge` / `safeUnderPartition` / `requiresCoordination`
  with the remedy named / `unknown` honestly), the proved sufficient
  condition (the pair commutes via the update lane's `UpdateCompat`
  pack AND the invariant is merge-closed — `MergeSafe.ofSufficient`
  earns the ∀-tables claim from the decidable faces), the overdraw
  witness at the balance carrier (the doctrine's own example: two
  individually-valid withdrawals jointly overdraw — the witness as
  data, the classifier refusing the safe call), the counterexample
  query returning the violating rows as data, and the Prop-indexed
  obligation rows (the provided-table claims at `decidableNow`; the
  ∀-tables claim at the loud `provedAtElab`-only open row).

The five questions (notes/v3/01-core.md): answered per submodule (the
list above); the umbrella itself answers none — it is the import
point. Gate row: SchemaCore IS a gated package — the axiom report +
docs-check + gen-check (the committed gen/schema-slice.wit byte-tie)
all sweep it.
-/

import SchemaCore.Ty
import SchemaCore.Fold
import SchemaCore.Value
import SchemaCore.Item
import SchemaCore.RowVals
import SchemaCore.Register
import SchemaCore.Emit
import SchemaCore.Emit.Journal
import SchemaCore.Snapshot
import SchemaCore.Diff
import SchemaCore.Describe
import SchemaCore.Codec
import SchemaCore.Derive
import SchemaCore.DeriveMeta
import SchemaCore.Update
import SchemaCore.Delta
import SchemaCore.Event
import SchemaCore.Migrate
import SchemaCore.Profile
import SchemaCore.EntityMachine
import SchemaCore.Violate
import SchemaCore.Commit
import SchemaCore.IncViolate
import SchemaCore.View
import SchemaCore.Confluence
