/-
# Kit — the umbrella module

One import point for the whole library. Submodules (import what you
name when you need only one — root-module imports are NOT re-exported
into scope, but this module re-exports by importing):

- `Kit.Correspondence` — the graded correspondence library
  (Iso / Retraction / Codec / Normalization / Simulation / Abstraction).
- `Kit.Obligation` — the obligation substrate (closed Tier + Evidence,
  the mis-wire rule, the decide backends).
- `Kit.Registry` — the value-level registries (DataRegistry, CodedRegistry).
- `Kit.CheckedProp` — relation + checker + bridge discipline.
- `Kit.Emit` — the emitter spine (pure run, outputs nodup in the type,
  the header/content-hash discipline, the driver fold).
- `Kit.Suggest` — the ONE did-you-mean engine (the bounded edit
  distance + the suffix rendering as data).
- `Kit.FreshName` — the fresh-name discipline (the verdict + the
  curated duplicate rejection, mined from legacy GenKit).
- `Kit.Diag` — the ONE diagnostic envelope (05 §4: ECode, Label, the
  closed five severities, the closedWorld constructor, the rendering).
- `Kit.Lane` — the lane substrate (`register_lane <Item>`: the env
  extension + the attribute mount as one kit call; 12 §2's steps 1–2).
- `Kit.CodeRegistry` — the persisted E-code registry (05 §4: stable
  allocation, the tombstones, the allocation replay, the file format).
- `Kit.Change` — the Change capability ladder (01-core §2: Applicable /
  Composable / WithIdentity / Reversible / Commuting / Additive, the
  two doctrine laws as structures, the worked instances + the proved
  non-instances).
- `Kit.Observer` — the observer parameter (04 §4: Observer, the
  equivalence + refinement vocabulary, the standard hierarchy's
  inclusion relations as data).
- `Kit.Varint` — the ONE LEB128 varint (the shared byte primitive: the
  encode/decode pair + the append-form law + the exact-image policy as
  a `Kit.Codec`; the C0 home both domain cores' codecs consume).

The five questions (notes/v3/01-core.md): this umbrella answers none
on its own — root, carrier, spine, and rung are each submodule's (the
list above is where the answers live). Gate row: none directly — Kit
itself is not yet in Gates.Packages' gated set (the per-library axiom
sweep covers LintKit/Gates/SchemaCore), so the KitTests axiom pins are
the standing evidence.
-/

import Kit.Correspondence
import Kit.Obligation
import Kit.Registry
import Kit.CheckedProp
import Kit.Emit
import Kit.Suggest
import Kit.FreshName
import Kit.Diag
import Kit.Lane
import Kit.CodeRegistry
import Kit.Change
import Kit.Observer
import Kit.Varint
