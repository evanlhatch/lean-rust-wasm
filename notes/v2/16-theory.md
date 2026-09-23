# 16 — Theory integration: what to build in, what to park (and how)

The six theory-level ideas evaluated against this tree, with the adoption
level (BUILD-IN / ADOPT / VOCABULARY / PARK), the discipline that keeps them
honest, and where they land.

## 1. The Incremental Lambda Calculus — PARK (the D/I row's endgame)

- What: for any pure f, derive Δf with `f (x ⊕ Δ) = f x ⊕ Δf Δ` — the
  generalization of which dbsp is one instance.
- What we already are: `D`/`I` inverse pair, `incremental2`/`timesIncremental`
  (the bilinear three-term join), `incrementalize_ok` (Ckt), `distinctIncremental`,
  and `LinearMachine.deltaChain` — the machine-level hand-incremental. We have
  ILC for the two shapes we need (streams for the query curve, machines for
  state).
- BUILD-IN prerequisite: the extractable fragment (the interpretation family,
  08 §2) — ILC is the interaction of that machinery with change types. Park a
  research track named THIS: "derive Δf via a compiler pass over the
  fragment." Do not hand-roll beyond the two instantiations.

## 2. Quotient types for order-freedom — ADOPT (one place, doctrine-grade)

- The law becomes a type: order-freedom as unrepresentable-wrong rather than
  proved-after. Lean's `Quot` makes "a function defined on the quotient
  cannot distinguish orders by construction."
- THE DISCIPLINE (hard): a quotient only where ALL hold —
  1. order is SEMANTICALLY irrelevant,
  2. a canonical representative exists (deterministic, total),
  3. NO wire/guest/decide/emitted layer carries the quotient
     (they stay on the canonical rep; Lean quots kill Derive/BEq/match and
     defeat the guest),
  4. the respect obligation is paid ONCE, at the encoder boundary.
- The one live candidate: **map/set payloads** — VMap's
  "insertion-order-is-data" stance (W8.2) becomes order-free at the spec
  level; the encoder canonicalizes (KeyTy scalars: total order); the wire
  stays canonical. This is the "law becomes a type" demonstration.
- Explicitly NOT quotienting: update batches, journals, codec paddings —
  there the order-freedom theorem is already proved once at the structure
  (Update2/Effects) and cited; a quotient would re-pay respect at every
  lift and break decide. The structure theorem is the Lean-correct form.

## 3. Delimited continuations — VOCABULARY (name the theory, keep the protocol)

- What: the component-model's [async-lift] + task-return dance (guest
  suspends, host answers, guest resumes) is hand-rolled shift/reset, host as
  handler.
- Adopt the STRUCTURE: name the suspension points, the host-as-handler, and
  session laws at those points (composes with Boundary sessions, 12 §7).
- Do NOT implement a delimited-control runtime in the guest: compiling
  continuations to wasm is a massive lift that clarifies a lane that already
  ships. The protocol-shaped compiled form is CORRECT; the theory names it.

## 4. Bisimulation up-to — ADOPT (perma-upgrade to conformance)

- Fusion's `bisim_iff_resp_streams` is the seed; up-to techniques (up to
  congruence/context) turn one monolithic machine-equivalence proof into
  small local proofs that compose.
- Land in the fusion lane (Phase 8's conformance work); a small coinduction
  theory + the up-to theorems; consumers cite, never re-derive.

## 5. Difference lists — BUILD-IN (as doctrine; mostly already true)

- Emitters' structure already rides `Std.Format` — a ROPE (append O(1),
  render one linear walk). The rule (add to 09): structure = Format; leaves
  = `String.join`/`intercalate`; NEVER a left-nested `++` loop over String
  (the `replicate` class — quadratic).
- Fixes this week: the known `replicate`-style left-appends → join; audit
  the leaf layers (manifests, WIT text, spawn strings) with the rule.

## 6. IC3/PDR — PARK (moonshot; CEGAR is the pragmatic step)

- Invariant-strengthening search is the real missing piece in invariant
  verification — for INFINITE state. Our invariants are mostly simple and
  finite: the model-checker (12 §3) exhausts finite strengthening;
  CEGAR (13 §4) names the culprit by refinement. PARK PDR as a research line
  triggered by an infinite-state invariant that needs it.

## The built-in framing ("we don't consciously think about it")

- Quotient/ILC-shaped laws become machinery, not decisions: the
  interpretation family + deriving (05 §2) is the mechanism that makes a new
  shape's incremental/order-free structure FALL OUT of declaring it, rather
  than being thought about per feature. When a new capability is declared:
  derive its change reading (ILC-lite), its canonical order (quotient-lite),
  its suspension points (session-lite) as generated instances — the
  "shift left, built in" that turns theory into rows.

## Indexed types — extend at five points

1. Stack-typed Sem (checker = derivation) — sequenced (Phase 6).
2. Typed target ASTs (`RustItem : Ty → Type`) — sequenced (Phase 6).
3. `Fin`-indexed codes/arities/tables — sequenced.
4. **Length-indexed journals** — event logs/W9 witness logs; fuel and
   partiality evaporate (the D2 discipline applied to the data plane).
5. **Kind-indexed registry** — the One Universe as a dependent aggregate over
   lane kinds; "new lane = one kind case" is typed by the kind; snapshot
   parse↔typed round-trip becomes type-directed.
Rule (09 §2): never index the wire/guest/decide layers; closed enums stay the
compute surface.
