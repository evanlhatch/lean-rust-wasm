# 15 — The pattern catalog (the shapes that earned their place, and why)

The construction handbook (12) is the mechanical how; this file is the
WHY: the patterns proven in the old tree, each with its canonical
instance, why it's right, and when NOT to use it. A new build uses these
by default; a deviation carries a written reason. These are the shapes
the re-bloat guard protects: they exist so the new tree starts lean and
stays lean — each pattern replaces a family of ad-hoc rewrites.

## The proof/correctness patterns

**1. Relation-as-spec + executable checker + proved bridge.** A spec is
an inductive relation (the honest semantics); the checker is the
decidable procedure; the bridge theorem connects them (sound; complete
only when honestly provable — the LOUD two-constructor completeness
choice, never a defaulted `true`). Canonical: `WellFormed` +
`universeCheck` + `universeWellFormed_iff`. Why right: the spec never
lies to fit the checker; a partial checker is honest data. When NOT:
when a type can carry the invariant directly (the ladder's rungs 1–3
beat this pattern where they apply).

**2. The append-form codec law.** Every binary codec's law:
`dec (enc a ++ rest) = some (a, rest)` — the appended rest is the
composition discipline: codecs compose under bind BECAUSE the law is
append-form. Canonical: Codec.lean's atoms + combinators. Why right:
the per-type laws compose for free. When not: never for a codec; a
codec without the append law doesn't compose.

**3. The certificate pattern (untrusted producer + small verified
checker).** A search/analysis/proposal produces a candidate + evidence;
a small checked validator accepts or refuses. Canonical: the witness
lane (host generates the witness; the guest's compiled checker
verifies). Why right: the trusted surface stays small and honest; the
producer stays free to be clever. When not: when the honest answer is
decide-in-kernel (rung 3) — don't build a checker where decide works.

**4. The obligation as data.** Every checkable fact: label + computed
tier + payload + provenance + closed evidence; discharge backends live
once in the kit; a row whose evidence's tier mismatches fails
construction; an undischarged obligation is a loud gap. Canonical:
Kit's Obligation + the lanes' views. Why right: armed-but-unfired
becomes unrepresentable. When not: single-use one-off checks (a plain
decide is fine — the substrate is for REGISTERED facts).

**5. The mandatory negative control.** A property sweep carries its
sabotaged sibling in the STRUCTURE (the PropSpec `control` field — a
suite without its control doesn't construct). Why right: a vacuous
suite fails loudly instead of passing forever. When not: never — this
is unconditional.

**6. The dual-reading tie.** Two semantics of one expression (boxed vs
raw, spec vs compiled) tied by ONE theorem at the structure, cited —
never re-proved per lane. Canonical: the ExprLang ties + the duel rows
as regression. Why right: agreement by construction, the duel as
regression not authority. When not: where the two readings are one
(the parameterization only pays at two+).

## The structure/generation patterns

**7. The env extension as the compile-time event log.** Registration =
append to a persistent extension; replay = the materialization;
snapshot = the integral. Canonical: the Meta/Register machinery. Why
right: one writer, deterministic replay, the import order irrelevant
to content. When not: for genuinely global mutable state — there is
none in the pure core.

**8. The deriving protocol (the record is the spec).** Reflect once
into the typed description; derive the capability surface via generic
definitions + generic theorems (thin wrappers); stamp `@[derived]`;
throw curated failures (name the record, the capability, the valid
space, the fix). Canonical: the WireCodec handler. Why right:
elaboration is the correctness gate; the record's type is the spec.
When not: for one-off declarations (the protocol pays at two+ records).

**9. The machine! entourage.** One declaration generates the state
enum + the transition table + the table↔step tie theorem + the
decidable predicate + the conformance battery. Canonical: Machines/Dsl.
Why right: the generated surface IS the law-carrying surface. When not:
payload-machines that don't fit the clause grammar — hand-build with
the note (the Sync precedent).

**10. The emitter spine.** Pure total `run : Spec → List GeneratedFile`
with declared outputs (nodup in the type) + the optional law + the
header; drivers own IO (`runEmitters`); the artifact's 2-line GENERATED
header carries the content hash; the byte-tie strips only the volatile
lines. Canonical: the schema-lang Emit lane. Why right: the byte-tie is
the emitter's correspondence law, CI-enforced. When not: never for an
emitter.

**11. The kit's correspondence values.** Crossings declared as
Iso/PartialIso/Denotes with the law in the type; the image-iso upgrade
(every PartialIso is a true Iso onto its canonical image). Canonical:
Kit.lean + the WireCodec instances. v3 EXTENDS this to the graded
library (01 §4) — the pattern's full form.

**12. The total parser + the inversion kit.** Total structural parsers
over `List Char` with the equation-lemma-friendly definitions + the
per-shape inversion lemmas (and per 05 §1: the typed bidirectional
grammar generating them). Canonical: TextKit. Why right: proofs reduce
by equation lemmas; a total parser has no silent divergence. When not:
host-side throwaway parsing may ride core's Parsec (no theorems to
protect).

**13. The guest-compat discipline.** Guest-compilable decls carry
`@[guest]`/`@[guest_std]`; the ban linter checks the closure at
elaboration; the boundary is the gate. Canonical: GuestlangStd. Why
right: guest-incompatibility is caught at elaboration, never at the
wasm emitter. When not: host-only code needs no mark (don't mark for
the ceremony).

**14. The LCG discipline.** Generated data is seeded + deterministic
(`TestingKit.lcg`); a failing case replays byte-identically from its seed;
shrinking walks toward the minimal case. Why right: "works on my seed"
is never a bug report. When not: never for a generated fixture.

**15. The closed-universe exhaustiveness discipline.** The boundary
universe (`Ty` and friends) is CLOSED; a new constructor breaks every
fold's exhaustiveness and the compiler drives the extension. Why right:
the compiler is the change-management system. When not: the instance
worlds stay open deliberately (01's A1: closed cores, open mounts).

**16. The closed-world error discipline.** Every failure over a closed
world enumerates the valid space + did-you-means (one engine, one
suffix); a bare error is an unfinished API. Canonical: the GenKit
helpers + the DSL clause rejections. Why right: the error IS the API's
teaching surface. When not: internal invariant panics (documented
impossible states keep their panics with comments).

## The meta-pattern (why this file exists)

Every pattern above replaced a FAMILY of hand-rolled variants. The
re-bloat guard for the new tree: before writing a new mechanism, name
the pattern it rides (this file) or the recipe it fills (07) — if
neither, it's a new primitive and it enters the catalog WITH its first
consumer, never before (the leftover rule). The marginal cost of the
next thing stays at rows + instances.
