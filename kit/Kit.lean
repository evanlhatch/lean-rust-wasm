/-
# Kit — the umbrella module

One import point for the whole library. Submodules (import what you
name when you need only one — root-module imports are NOT re-exported
into scope, but this module re-exports by importing):

- `Kit.Correspondence` — the graded correspondence library
  (Iso / Retraction / Codec / Normalization / Simulation / Abstraction).
- `Kit.Relation` — the relational engine's substrate (01-core §6, D16:
  the relation family + composition + the identity/diagonal, the
  interpretation bundle, THE generic theorem — per-primitive
  preservation ⟹ whole-term preservation — + the composition rows
  (map lift / chain via `Rel.comp`) + the Kripke note (the named
  extension for the stateful lanes).
- `Kit.Hyper` — the hyperproperty substrate (16-surface §4.3: the
  power jump — `Rel2` over execution pairs + the pointwise lift
  discipline + THE flagship hyperproperty `Noninterfering` as a type
  over a two-run relation, the factor row, the observer composition
  (output-coarsening + the security row), the worked positive/negative
  instances with the counterexample pairs as data).
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
- `Kit.Text` — the rope text-builder (06 §7b: the emitters' STRUCTURE
  carrier — `Text` chunk tree, O(1) `app`/`cat`/`sepBy`, ONE render;
  the byte-tie's bridge laws).
- `Kit.Duel` — the duel/vector harness seed (03 §3: the evidence
  shape — the vector-set convention, the verdict ctors, the LCG-seeded
  generator; the manifest rides the emitter spine's binary lane).
- `Kit.Mangle` — the ONE name-mangling surface (words/camel/pascal/
  snake/kebab + `rustIdent`) + THE post-mangle uniqueness discipline
  (`collDiags` + the `collDiags_eq_nil_iff` bridge — the mined
  `mangleCollDiags_eq_nil_iff`).
- `Kit.Json` — the minimal JSON builders (`jsonStr` — the ONE escaping
  decision — + obj/objPad/arr; pre-rendered texts, no `Json` AST).
- `Kit.Validation` — the error-accumulating applicative (the
  anti-early-exit surface: `foldlM`/`traverse` collect ALL failures;
  NO `Monad` — bind cannot accumulate).

The five questions (notes/v3/01-core.md): this umbrella answers none
on its own — root, carrier, spine, and rung are each submodule's (the
list above is where the answers live). Gate row: none directly — Kit
itself is not yet in Gates.Packages' gated set (the per-library axiom
sweep covers LintKit/Gates/SchemaCore), so the KitTests axiom pins are
the standing evidence.
-/

import Kit.Correspondence
import Kit.Relation
import Kit.Hyper
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
import Kit.Text
import Kit.Duel
import Kit.Mangle
import Kit.Json
import Kit.Validation
