# 05 — The generative layer: text, emitters, deriving, diagnostics

## 1. Text: one grammar value drives everything

Every text artifact (wire formats, manifests, snapshots, configs, DSL
surfaces) consumes TextKit's grammar value. A per-package hand parser is
a migration target, never a new option.

The grammar is TYPED and BIDIRECTIONAL — `Grammar α` where α is the
payload type; the parser produces α, the printer consumes α:

```lean
-- the supported fragment: certified predictive grammars
inductive Node (Tok : Type) (R : Type) where
  | tok    (l : Lex Tok) (payload : Tok → Option R)     -- parse-side prism
  | seq    … | alt …                                    -- product/sum payloads
  | rep    (body : Node Tok R) (progress : proof the body consumes)
  | opt    … | label (name : String) (body : Node Tok R)
  | rel    (m : PartialIso Raw R) (body : Node Tok Raw) -- the semantic mapping
```

The honest laws (the only two a text format gets):

```
parse (print x) = ok x                  -- everything we print parses back
print (parse text) = canonicalize text  -- accepted text normalizes
```

Rules: unambiguity is undecidable in general — the supported fragment is
predictive grammars with the decidable certificate (FIRST-prefix freedom
at alternation + FOLLOW interactions for optional/repeated + progress
for `rep`); other parsing strategies enter through the same semantic
contract, not through claims that one check handles all formats. Total
parsers only (structural recursion or a size measure); errors are
`ParseError` values (position + expected-set + label stack + did-you-
mean + the E-code), never `none`; the guest carrier is a thin
bytes+ids variant of the same error.

**The boundary that must not blur:** a parser/printer roundtrip proves
TEXTUAL agreement. It says nothing about the emitted artifact's
semantics — that is a separate theorem (the correspondence lane).

**declare_inversion** generates the per-node inversion lemmas + the
headline `parse_emit` from the grammar value. **dsl!** generates the
authoring surface (syntax category + elaborator + unexpanders) from the
same grammar. The third DSL in the tree must use dsl!; the first two
migrate.

## 2. Emitters (the spine's reading half)

An `Emitter` is: name, declared outputs (nodup IN THE TYPE), a pure
total `run : Spec → List GeneratedFile`, an optional `law`, and the
header (owner/exclusions/decision). Drivers own IO. `runCertified` when
the law must discharge for emission to proceed.

- Totality is the prerequisite for everything: a total emitter's golden
  equality is a theorem; the gate's regen-and-diff is the CI shadow of
  a proved fact. `partial` in the emission layer is a written-reason
  decision, ratcheting down only.
- Ownership is GLOBAL: outputs disjoint across ALL emitters, and the
  emitted paths must match the declared ones (the gates check both).
- The self-audit scans every artifact (no TODO/unwrap/dbg/unsafe in
  generated output).

## 3. The deriving protocol (the record is the spec)

`@[schema] … deriving Cap1, Cap2` — each capability a handler that:

1. reflects the record ONCE into its typed description (the description
   layer: a small typed universe of supported structure — primitive /
   product / sum / optional / sequence / reference / refinement /
   dependent field — interpreted into the Lean type; the ONE deliberate
   meta-universe, its instances are our types);
2. derives the capability's surface from the description via GENERIC
   definitions + GENERIC theorems (the thin-wrapper rule:
   `User.codec := deriveCodec User.description`,
   `User.codec_roundtrip := deriveCodec_correct User.description` —
   generic theorem first, specialization second);
3. stamps `@[derived]` (lint exemptions are structural);
4. throws CURATED failures (name the record, the capability, the
   unsupported fragment, the valid space, the fix);
5. registers its rows in the Universe + snapshot.

Elaboration is the untrusted producer of ordinary checked definitions:
resolve names, inspect declarations, construct the typed description,
synthesize the thin wrappers, present diagnostics. Ordinary Lean does
transformations, semantics, composition, validators, and the correctness
theorems. Instance search stays narrow: profile-indexed classes or
explicit bundles where one type legitimately has several codecs (JSON /
binary / canonical-hash / legacy — a global `Codec User` instance risks
accidental choice).

Derive lazily: a declaration gets exactly the capabilities its consumers
request; its remaining obligations appear at its declaration site. No
mandatory product bundle (that overclaim is decisions.md).

## 4. Diagnostics (one envelope, all channels)

```
Diag { code : ECode; message : String; context : List Label;
       got : Option String; valid : List String; suggest : Option String;
       severity : error | warning | gate | obligation | info }
```

Every channel speaks it: elaboration errors, parse failures
(ParseError = a Diag with position), lint findings, gate verdicts,
obligation rows, oracle divergences, Rust spans (emitted data), the
guest's thin diagnostics (ids only).

Rules: every failure over a closed world enumerates the valid space +
did-you-mean (one engine, one suffix — data, `suggestFor got valid`);
instance-search failures are CAUGHT and curated (never a raw synthesis
wall); no silent degradation (a missing discharge is a loud gap, corrupt
bytes are a refusal, an unsupported construct is a throw — never a
sentinel); `Validation` accumulates, `Except` single-fails, never
implicitly convert; every new failure path ships its Diag + its E-code
row + its curation in the SAME change as the feature.

**The E-code universe:** one code space for all diagnostics (Lean
elaboration, gates, Rust spans, wasm faults) — allocated from the
persisted registry (STABLE allocation: codes never derive from
enumeration position or import order; a reordered registry changes no
code). The E-code means the same thing in an elaboration error, a gate
log, a Rust span, and a guest refusal.

## 5. Acceptance gate for this layer

A new text format = a Grammar value + golden rows (no parser module, no
printer module, no proof family). A new emitter = an Emitter row (nodup
in the type, the law or the header note). A new capability = a deriving
handler following §3 with its curated failures landing first. A tour of
failure paths renders structured Diags with stable codes and valid-space
enumeration.
