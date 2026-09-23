# 05 — The primitive catalog + the deriving-staged protocol

The four mechanism kinds (02 §3) concretized, plus the record protocol.

## 1. Statement + Obligation (the legality primitive)

- One `Statement` shape: a proposition, an executable checker, soundness
  (mandatory), completeness (constructor choice `.missing | .proved` — never
  defaulted true), and **mounts** (gate / lint / test / obligation row / duel).
  One shape for universe WF, key legality, guest-compatibility, range checks,
  witness checks — the current four parallel carriers (CheckedProp/DeclCheck/
  BareChecker/Wf-relation-idiom) converge on it.
- One `Obligation` shape: label + computed `Tier` + payload + provenance +
  `Evidence`, with `Evidence` and `Tier` CLOSED (axiom A1) and the discharge
  contract: a row whose evidence's tier ≠ the obligation's tier is a
  mis-wire that fails construction.
- The discharge trio (claim, discharge, sound + completeness lemmas) exists ONCE
  in the kit; lanes instantiate, never reimplement.

## 2. The deriving-staged protocol (the record IS the spec)

The canonical way a record gains capabilities: `@[schema] … deriving Cap1, Cap2`
where each capability is a `deriving`-style handler emitting its decls + laws +
rows into the universe.

Protocol per capability handler:

1. Read the record from the elaborated env (fields, types, order — never a
   hand mirror; reifiers are the ONE quoter family).
2. Emit the capability's derived surface (abbrev, builder, bridge, codec+law,
   gen, machine battery, RoundTripSpec rows) — all via the family! engine and
   the shared reifier.
3. Bestow the `@[derived]` stamp so lint exemptions are structural.
4. Throw CURATED failures (04 §3): name the record, the capability, the
   unsupported fragment, the valid space, the fix.
5. Register in the One Universe (§02.5) and the snapshot.

Order of build: the diagnostics (step 4) land with the FIRST capability,
before any further handlers are added. Each new handler follows the WireCodec
precedent: one record, end-to-end, byte-tie green, then generalize.

Capabilities planned (in order): RowBridge (fields+row+iso), WireCodec
(codec+RoundTripSpec), Gen, MachineBattery, Validators/Update surface,
WitnessSpec rows, DTypeLowering. New capabilities are rows in this list.

## 3. Registry primitives

- `MemberKit` — the extension + reader + registration mount skeleton
  (declare_registry_member): fresh-name check + did-you-mean + provenance.
- `GenKit` — shared elaboration-side glue: `freshNameCheck`, the did-you-mean
  context, the reifier wiring, the `@[derived]` stamp.
- DataRegistry / CodedRegistry — value-level registries with nodup/codes in
  the type (already).
- Snapshot — the universe text as one committed baseline; per-lane cases
  extend it (One Universe).

## 4. Emitter primitives (the spine)

- `Emitter`: name, style, specSource, OUTPUTS (with `nodup` in the type),
  `run` (pure, total — 07 §1), optional `law`; `runCertified` when the law
  must discharge.
- `family!`: tables + name-patterns + decl-templates + proof/test templates —
  the generative engine every `declare_*` rides.
- Shared module skeletons: `recordGroupedModule` (per-record fn/test modules),
  `moduleRust` (machine → step fns) — the emitters consume these, never rebuild.
- The self-audit (AuditRule list: no TODO/unwrap/dbg/unsafe in generated
  artifacts) runs over EVERY emitter, not just schema-lang's.

## 5. Text primitives — TextKit (03 in full)

Grammar value → lexer/parser/printer/inversion; ParseError; Diag; dsl!.
This is the shared text machinery; every text artifact consumes it (no
per-package hand parsers; the per-package "text wire" modules migrate onto
Grammar values — acceptance gate 03 §9).

## 6. Test/Spec primitives (TestKit)

One `Spec` (positives + negatives + vacuity-louder-than-fail in the type),
one `Verdict` (differential: expected/observed/category/payloadDiffAt),
one golden/byte-tie (stripped), one self-audit. Every package's tests are
folds over lane data (08).

## 7. The kit's usage rule

A new lane/capability/tool READS the catalog and consumes; it never re-declares
a primitive. If a primitive is missing, add it to the catalog (this file) with
its handler/rows in the SAME change as the first consumer — never before
("no consumer, no primitive" — the leftover rule, 01 §4).
