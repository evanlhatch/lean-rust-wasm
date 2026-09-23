# 17 — The foundation contract: declare once, inherit five

The foundation's core guarantee. Every declared entity (record, op, lane,
machine, boundary) ships FIVE derived products by construction via the
deriving protocol (05 §2). Correctness flows DOWN: downstream features are
consumers of the products — and their laws — never of per-feature code.
"Provability is downstream of the foundation" is implemented as: the products
carry their laws; citing a product cites its law.

## The five products (what every declaration generates)

For a declaration `D` (a `@[schema]` record, a `declare_*` op, a `machine!`,
a boundary), the deriving handers emit:

| # | Product | Type | Law it carries | Downstream consumers |
|---|---|---|---|---|
| 1 | **Canonical form** | `Canonical D` (class: `canon : D → C`, `toCanon`/`ofCanon` iso on the rep) | order-freedom/perm-invariance certificate (16 §2) | maps/sets order-free, wire canonicalization, diffs |
| 2 | **Change structure** | `Change D Δ` / `Difference` / `ChangeInversion` / `Noc` instances (dbsp.ChangeSpec) | patch valid/invert/diff-correct (proved at derivation) | event sourcing, migrations (13 §1), what-if (13 §2), incremental views (13 §6), journals |
| 3 | **Effect row** | `HasEffects D` (12 §1: the closed lattice) | composition join; boundary bounds | sessions, async, determinism, GuestBan — one axis |
| 4 | **Correspondence** | `Iso`/`PartialIso`/`Denotes+ReprOp` (codegen. Kit) | the law IN the type | wire/value/row/dtype crossings |
| 5 | **Statement + obligation** | `CheckedStatement` + `Obligation` where legality applies (05 §1) | sound (+complete choice), closed evidence | gates, lints, tests, tourist rows |

The five are generated, not hand-written; the generating handler is the
record protocol (05 §2) extended — same mechanism as RowBridge/WireCodec/Gen
today, generalized so ANY declaration ships all five products.

## The inheritance diagram (what runs on the products)

```
declaration D
  ├─ Canonical    → maps/sets, wire form, diffs
  ├─ Change       → EventSourced.replay, Migrations.upcast, Inspector.whatIf,
  │                 Incremental views (cite Δ + D/I), Replicas
  ├─ Effect       → boundaries/sessions/async/guest-ban (one axis)
  ├─ Correspondence → every crossing (codec, wire, dtype, row)
  └─ Statement    → every legality gate/obligation
```

Downstream lanes NEVER re-derive a product; they consume the instance. A lane
that re-declares a change structure, an effect row, or a correspondence where
the product exists is an R1/R9 violation (10).

## The re-founded theories (16 §1–§4, raised to foundation level)

- **ILC-lite = product #2 (Changeable-deriving).** The generic "compiler pass
  derives Δf for any pure function" stays PARKED; its derivable slice — a
  generated change structure with proved D/I laws per declared shape — is
  foundation. dbsp's ChangeSpec classes are the seed.
- **Effects = product #3.** The lattice is the single what-happens kernel:
  async-as-shift/reset (vocabulary), sessions, boundaries, determinism, guest
  ban are INSTANCES of one axis. The delimited-control runtime stays parked.
- **Order-freedom = product #1.** The quotient discipline at the right layer:
  canonical rep + perm certificate at the spec layer; the wire/guest/decide
  layers consume the rep, never the Quot.
- **Bisimulation up-to** → a Machines theory kit (16 §4) all machine
  conformance proofs inherit.

## Acceptance (the contract is real, mechanically)

1. A bare `@[schema] record` lands with all five products and their laws —
   no hand-written change structure / effect row / correspondence.
2. Two unrelated lanes (e.g. EventSourced + the WhatIf inspector) consume the
   SAME generated `Change` instance; their correctness cites the same laws
   (grep check: no second instance of `ChangeInversion` for the type).
3. A boundary's effect row bounds its sessions; the WIT capability set = the
   join of export rows (12 §1).
4. Order-freedom of maps/sets is inherited (Canonical), and no
   wire/guest/decide module carries a `Quot` (16 §2 discipline).

## Guard rules

- Products are generated ONCE at the declaration; the protocol is the only
  writer (one-writer).
- The five products are SPEC/logic-layer. The compute surfaces (wire, guest,
  decide, emitted code) consume the canonical reps and, never the raw
  quotient/effect-theory objects (09 §2, 16 §2).
- If a product's derivation cannot be generated for a declaration, the handler
  FAILS LOUD (curated, 04 §3) and the declaration re-scopes — never a silent
  fallback.
