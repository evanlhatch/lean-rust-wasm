# The user guide — the concepts, in the order a user meets them

The quickstart (`notes/quickstart.md`) ran the loop once; this guide
names what you were standing on. The order here is the USER's walk —
declare, consume, persist, query, observe, evolve, submit to the
gates — NOT the doctrine's. The WHY lives in `notes/v3/` (each
section names its file); the WHAT's owner is always the code cited
inline. The map of every library and gate row:
`notes/architecture.md`.

## 1. Schemas — the closed universe + the `table!` surface

A schema item is a plain Lean record mounted `@[schema]` into ONE
registry (the accumulated event log, 15 #7). You author it through
the `table!` clause macro (`SchemaCore.Surface`) — `key:`/`ref:`/
`rule:`/`deriving:` clauses — which DESUGARS to the same mounts the
attribute face uses; there is no second reflection path (D19). Field
types come from the CLOSED `Ty` universe (`SchemaCore.Ty`) — a type
outside the fragment refuses at the declaration (SR0007), because
every downstream guarantee (codecs, emitters, coverage) is proved per
constructor of that universe.
Why: `notes/v3/01-core.md` (three roots, one carrier), `02` §1 (the
shared authority of constraints), `16-surface.md` §1–2 (the two-idiom
frontend, the vocabulary).

## 2. The generated surfaces — one writer per artifact

The registry replays; the emitters fold it (`Kit.Emit`'s spine). One
declaration's faces: the WIT world (`Wit`'s renderer), the TS interop
module, the Rust crate (`crates/schema-generated`), the wasm slice,
the component lane — each path has exactly ONE writer exe, and every
committed artifact carries the 2-line GENERATED header whose content
hash is the byte-tie anchor. You never hand-edit any of it: regen is
mechanical (`just gen`/`wasmgen`/`componentgen`), drift is a gate
failure, and the honest lossiness is DECLARED (the TS face is the
JSON interop encoding, not a second wire spec).
Why: `notes/v3/05-codegen.md` (grammar-as-data, the emit spine),
`13-interfaces.md` (the wire specs + the byte-tie).

## 3. The data plane — propose / check / commit

State changes are DELTAS, not overwrites: the Z-set substrate
(`ZSet`) gives the canonical additive change; the trichotomy
command/delta/event is TYPES, not convention (02 §7 — upcasters work
on deltas). A change is PROPOSED, CHECKED against the schema's rules
(the check lane's rows — the violating rows are the payload, not a
boolean), then COMMITTED as an append to the journal. The host-side
log is `crates/mandate-delta` (byte-exact port of the Lean codec; it
invents no format); torn-tail recovery is modeled and proved in the
Crash discipline.
Why: `notes/v3/02-data-plane.md` (the relational center), `03
-bidirectional.md` (propose→check→commit, one owner per fact), `07`
(the persistence row).

## 4. Queries — qlang!, typed at elaboration

`qlang!{ from <schema> then select (…) then project […] then union … }`
elaborates to the typed `Q` (`Query.QLang`): columns resolve BY NAME
at elaboration (a miss is QL0002 + did-you-mean), the term is
self-typed (`Q fs gs` pins every stage), and the bridge theorem says
the elaborated query ≡ the hand-written relational form — both
evaluators agree. Result typing is FD-driven: a key is a determinacy
theorem, not a uniqueness hope (02 §3).
Why: `notes/v3/02-data-plane.md` §3, `08` (the query capability
spec).

## 5. Observability — the ONE Diag envelope, the E-codes, the fault face

Every curated refusal — elaboration-time or runtime — is the ONE
`Kit.Diag` envelope: a code, the message, the valid space, the
did-you-mean. Codes are ALLOCATED from the persisted registry
(`notes/code-registry.txt`; the code-registry gate replays the
allocation) — families you'll meet: SR (schema surface), QL (query),
SCF (scaffold), FT (faults). The Rust fault face is generated into
`crates/mandate-faults` in fast-observe's `error!` syntax (nightly —
the declared cost), so Lean's category/policy mapping holds on the
host by construction, not convention.
Why: `notes/v3/05-codegen.md` §4 (diagnostics), `08` (the faults
lane), `09` (the registry's teeth).

## 6. Evolution — diff → plan → upcaster, refused when unsound

Bump the version (`table! Account v2`); the registry diffs against
the prior row; the migration lane DERIVES the upcaster and its plan
(key stability is a checked property of the plan, not an assertion).
The refusal list is the soundness boundary: removals, unremedied
retypes, reorders/mid-inserts, key moves, defaultless additions —
all AT ELABORATION, before anything is emitted. The committed
universe snapshot (`notes/universe.snapshot`) is the baseline the
breaking gate judges drift against; re-baselining is a deliberate
loud act, never a quiet overwrite.
Why: `notes/v3/03-bidirectional.md` §7 (deltas + upcasters), `13`
(the snapshot/breaking rows), `09` (the re-baseline discipline).

## 7. The gates — the discipline that makes the above true

Nothing above survives on trust: 14 gates (`Gates.gateNames`, closed
order) read the tree after every change — the axiom sweep (zero
`sorry`/`axiom` outside the disclosed allowlist), gen-check (the
byte-tie), docs-check (every non-sketch ```lean fence in `notes/`
resolves — including this guide's), kernel-check (an independent
pure-kernel replay), coverage, ownership, breaking. You run
`just check` in the loop and `just gates` before you call it done;
a red gate names its finding. The baselines under `notes/` are the
gates' memory — `--write` re-baselines belong to the integrator,
loudly.
Why: `notes/v3/09-gates-ops.md` (the gates + the dev loop), `04
-verification.md` (the proof ladder behind the axiom gate).

## 8. The honest boundary (what is NOT here yet)

The `table!` vocabulary's `state`/`event` words are named next rows
(`SchemaCore.Surface`'s header), the qlang join has a named refusal
(QL0001 — the design question is open), and the C-phase faces
(bench/e2e templates, config, fuzz) land per `notes/design-wave-30.md`
' rows. The doctrine's own ledger of holes: `notes/v3/16-surface.md`
§5 (the strengthening program).
