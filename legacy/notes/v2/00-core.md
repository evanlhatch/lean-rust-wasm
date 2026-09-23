# 00 — The minimal core (the compression of the whole doctrine)

The generating set this toolkit actually needs, after folding every
duplicated shape into the shape it was always an instance of. Everything
in 01–21 is an instance of this. If a proposed addition does not name its
slot here, it is a design failure (01 §3).

## The roots (three, provably irreducible)

| Root | Question | Irreducibility (the wall) |
|---|---|---|
| **Universe** | what is | finite data, initial-algebra side |
| **Change** | what changes, reversibly | needs symmetry (group/DeltaSystem); states don't invert — NOT machine behavior |
| **TraceModel** | what behaves | events + causal order (a poset); degenerates to a list when sequential — NOT data |

Under one roof: the algebra/coalgebra duality. Universe = the initial-
algebra side (folds; data). TraceModel = the final-coalgebra side
(behavior; a machine's trace set is its coalgebraic semantics,
bisimulation its equality). Change = the symmetry layer between them
(group where it holds — dbsp is that instance; DeltaSystem where it
doesn't). A new shape is either data, behavior, or a crossing — and the
answer names its inheritance.

**Temporality is not a root.** Time = the TraceModel's order: logical
time IS the causal order (Lamport); a global clock is the degenerate
total-order case; rate/duration is metric DATA over the order (Universe
content: Tick/Rate values). A fourth root would double the TraceModel.

**Resources are not a root.** Fuel/budgets/size = monotone consumption —
a Change instance (the monus discipline).

**Provenance is not a root.** The artifact ledger is an event log; the
causal trail is the TraceModel OF THE BUILD. (15 rides 19.)

**The fourth-root trigger, named honestly:** probability (randomized
semantics). Only that earns a new root, and only when a product lane
needs it.

## The carrier (ONE)

**Correspondence** — `Iso` / `PartialIso` / `Denotes`, the law in the
type. Every crossing is declared as one. AND, the fusion v2 missed:

- **A Statement is a correspondence** — between the decidable shadow and
  the proposition: `{a // check a = true} ≅ {a // P a}` (completeness)
  or the honest PartialIso when completeness is `.missing`. The
  CheckedProp/Statement shape is the Bool↔Prop instance of the carrier.
- **An Obligation** = a Statement + the tier + evidence record — a
  structure OVER the carrier instance, not a separate kind. Tier stays
  closed (A1); evidence stays closed (A1); the loud `.missing`/
  no-evidence gap rule survives the fusion BECAUSE PartialIso's
  one-endedness already is that discipline.

## The spine (ONE)

**Registry → Interpretation → artifact** — accumulate (the compile-time
event log) then read. Two fusions v2 listed as separate primitives:

- **An Emitter is an Interpretation** — a reading of the universe into
  the target's grammar. Law field, byte-tie, checked-universe input:
  all the interpretation's correspondence, cited.
- **The generative engine is an Emitter into the Lean-syntax target.**
  `family!`/`deriving` handlers = `spec → List (named decl + law)` — the
  SAME shape. Declared as the iso, the meta level inherits the emitter
  discipline for free: generated decls carry law fields; the generated
  surface's stability is a byte-tie instance; `@[derived]` is the
  artifact header.

## The discipline layer (unchanged)

The ladder (unrepresentable > no-instance > defaulted decide > generated
> disclosed native > hand) + the gates machine over the obligations.
01/07/08/09/10 carry it; nothing in this file changes them.

## What this buys (the acceptance test)

Fewer concepts, same power: the doctrine's primitives go from
"3 roots + 2 carriers + 6 primitives" to **3 + 1 + 1 + discipline**, and
every v2 component lands as a named instance. A new capability asks five
questions only: which root (or the degenerate cases), which carrier
instance, which spine reading, which rung, which gate row. The cognitive
shield: a dev writes records and attributes; the five questions are
answered by the recipe (06) + this file's instance table.
