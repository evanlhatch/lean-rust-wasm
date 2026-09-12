# Strategic Lean review — Lean as spec language for Rust+WASM

Scope: all 11 packages (~32K lines, .lake excluded). Method: three parallel
full-read cluster reviews (schema-lang/codegen-core/faults/std/ledger;
wasm-backend/dbsp; Machines/substrait/TestKit/LintKit) plus direct reads of
Ty/Item/Pipeline/Demo/Correct. Every headline claim below was spot-verified
in the tree.

## Verdict

The TYPE pipeline is genuinely strong: one `@[schema]` SSOT, reflection →
registry → pure emitters → byte-tie → wit-parser round-trip is a real,
CI-enforced discipline few projects have. The PROOF pipeline is honest but
narrower than the pitch: what is kernel-checked is type-safety and layout
non-overlap over a fragment the emitted code barely uses; end-to-end
"Lean semantics = wasm execution" is differential TESTING, not proof — and
the repo's own honesty ledgers (Correct.lean, full-remaining-work.md) say
so. The biggest structural problem: three packages are spec-only or
decorative (Machines emits nothing, dbsp's circuit theory certifies nothing
downstream, substrait's Decode is 3.7K lines proved only through scalars).

## 1. What's actually proved vs claimed

- PROVED, real: `Layout.go_pairwise` (flat-record non-overlap),
  `Sem.exec_typed` type safety, `Pipeline.rank_advances` +
  `tableStep?_eq_step?` (the emitted stage table IS the machine — the best
  theorem in the tree: it directly licenses generated Rust),
  `Replicas` convergence (abel-group one-liners, honest but shallow),
  DBSP fix/incrementalization port (substantive math over abstract
  operators), Codec varnat/envelope round-trips (scalar layer only).
- NOT PROVED, admitted: no compiler-correctness theorem (`lower ∘ emit`
  vs LCNF source semantics — Correct.lean covers straight-line + 2-alt
  branch + call-convention slices via `#guard`-pinned hand shapes, not
  kernel theorems); `Sem` lacks every op the backend emits (multi-byte
  loads, `memory.copy`, `call_indirect`, frames, globals, sub/mul/ltu);
  guest object layout (sproj index → byte offset) is convention;
  `runtime.wat` allocator/RC freelist unverified; `typeSafety` never
  applies to real branchy output (`checkFrame` rejects result-bearing
  `if`s — pinned in a guard).
- Oracle weakness: `resultOf` expecteds for stream fns are hardcoded
  strings (`"(42,43)"` for watch-counts) — the "Lean authority" is a
  constant there, not Lean's semantics. Manifest is 20 rows, fixed.

## 2. Spec-language gaps (what a user cannot model today)

- No generics (reflect rejects `numParams != 0`), no recursive types
  (acyclic v1, `refSem` fuel 8), no map/set, no variant case with record
  payload, no field defaults/docs/deprecation, no pre/postconditions on
  `@[schema_fn]` (FuncSig carries only nullSem/determinism/delivery —
  determinism is "armed but unfired"), no field invariants attached to
  items (VExpr is a separate hand-written layer emitters never see),
  register-before-reference ordering.
- VExpr covers only `gt/eq/and/strlen` over u64.

## 3. Hygiene: hand-mirrors that should be generated

The repo bans hand-written type lists in principle; four survive:
`Faults.Spec.knownTypes`, `Emit/Registry.forgeJobs` (patched at test time
by `jobsCoverEmitters` instead of derived), `GuestImpl.orderErrorCases`
(std), `Layout.userTys`-adjacent pins. Plus: `Validate.string_len` defined
twice; `target/oracle.lean` committed duplicate of `Oracle.lean`; asyncFns
comment rot on the riskiest protocol; WIT world name hardcoded
(`"demo:gateway"`); `Migration.remedies` is unchecked Bool logic; Diff has
no kind-change or param-rename story; Vortex `recordDTypes` silently skips
unlowerable records (no negative test).

## 4. Disconnected packages

- Machines: `Sim/Refine/Rewind/Convergent/Compose/Trace/Foundations` have
  ZERO downstream consumers (grep-verified). No emitter consumes `Machine`
  — machines produce no Rust/WIT artifact. No outputs/effects/error
  channel in `EventSpec`, no link to Faults.
- dbsp: circuit/fixpoint theory is a parallel universe; codegen consumes
  only `ChangeSpec`. Nothing emits circuits; `incrementalize_ok` certifies
  nothing downstream.
- substrait: load-bearing only at `Bridge.Ty.toSType?`; Decode proved
  through scalar types only.

## 5. How to use it better (workflow, no code changes)

1. State cross-function invariants as THEOREMS over the impl module (e.g.
   `getUser_spec : getUser id = ...`) — the axiom gate already enforces
   they're real proofs; today impl modules carry no properties at all.
2. Use Plausible (already a dep) for property-based differentials:
   `Arbitrary (Value t)` → randomized oracle manifests instead of the
   fixed 20 rows — closes the constant-expectation hole cheaply.
3. Use Machines.Session + the conformance battery for any multi-party
   spec; use the breaking gate (registered migrations) for every schema
   evolution — it exists and is tested but under-exercised.
4. Route ALL new artifacts through the registry+emitter pattern; forbid
   new hand-mirrors in review (the four above should be derived).

## 6. Ranked roadmap (leverage per unit of work)

1. **Prove the lowering relation**: a `Ty`-indexed "faithful lowering"
   relation with per-ctor lemmas that `tyRust`/`tyFmt`/`tyWit`/Vortex
   agree — catches the silent `list`→`stream<elem>` class at theorem
   level. Cheap, high value.
2. **Invariants as schema data**: attach VExpr to `@[schema]` items,
   emit validation Rust + WIT flags. Turns the spec language from
   "types only" into a real contract language.
3. **Generate the four hand-mirrors** (§3). Mechanical, kills a drift
   class the gates currently only detect late.
4. **Grow `Sem` to cover emitted ops** (loads, multi-byte stores, frames,
   `call_indirect`) OR restate `emitCode` totally and prove
   `lower ∘ emit` for a defined decl grammar. This is the seam between
   "tested" and "proved" — the single biggest honesty win.
5. **Emit machines**: registry fold over `machine!` models → Rust state
   types + guards + trace-replay conformance test. Makes Machines
   load-bearing or justifies deleting the dead half.
6. **Property-based oracle** (Plausible over `Value t`) — replaces the
   fixed manifest.
7. **Expressiveness**: lift single-payload variants + acyclic-types v1
   limits (recursive Tree is the first casualty of the current design).
8. **Finish or shrink substrait Decode** — 3.7K unproved lines past the
   scalar layer is either the next proof target or dead weight.
9. **Verify or gate `runtime.wat`** (allocator/RC freelist invariants) —
   it is the riskiest unverified code in the compiled path.
