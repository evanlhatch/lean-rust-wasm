# lean-rust-wasm — working agreements (agents and humans)

## The docs (read before designing; runbook before executing)

`notes/README.md` is the index. Reading order: `notes/vision.md`
(what this is + scope locks) → `notes/canon.md` (what everything IS —
binding: name your row, no row = a finding) → `notes/lean-doctrine.md`
(the rules + enforcement levels) → `notes/runbook-2026-09-15.md`
(the work plan: agent primer + prescriptive work orders). Evidence
behind decisions: `notes/studies/` (cedar-spec, verified-ledger).

## Version control: jj

- Working copy IS a commit. Small atomic changes, `jj describe` once known.
  Never `git checkout/reset/stash` — `jj undo`/`jj new`.
- `just push` to sync the GitHub remote (gh is authed).

## Verification (every change)

`devenv shell --profile wasm` then:
- `just lean-build && just lean-axioms` — full Lean matrix, axiom gate
- `just gates` — byte-tie, wit-parser, axioms
All green before declaring done. Never trust your own report — run the gate.

## Lean discipline

- **Zero `sorry`/`axiom`.** A missing theorem is information; a stub is a lie.
  `just lean-axioms` enforces (core triple + disclosed native_decide only).
- **Compile after every declaration.** Every multi-round repair came from
  writing 100+ lines before the first build.
- Tests live in `<Package>/Tests/`; negative controls are MANDATORY for
  property sweeps (a vacuous suite fails the gate — see TestKit.PropSpec).
- Module headers state ownership, deliberate exclusions, and the driving
  decision. Provenance for lifted code: source package + what was skipped.
- The `abbrev` rule: field/type lists used in instance search MUST be
  `abbrev` (reducible) — plain `def` defeats elaboration-time resolution.
- Equations match ALL binders including implicits when structural patterns
  are needed (the `Row.setN` lesson: `_` wildcards for `{sem}`/`{fs}`).
- Dot-notation argument order: `x.f args` requires `f`'s FIRST explicit
  arg to be x's type — check signatures before dot-chaining.

## Known traps (do not re-pay)

- wf-recursive (`termination_by`) defs are KERNEL-OPAQUE — `decide`/rfl
  over anything touching them can never reduce (module system or not).
  The pattern: prove a specialized reduction lemma for the concrete
  shape (e.g. `FieldVal.beq_u64_ne`) and route the check through it.
  (Found by the W8.3 landing repair, 2026-09-17.)
- `Option.noConfusion` across universe-mismatched Eq: use `nomatch h`.

- `SimplePersistentEnvExtension.addImportedFn` takes `Array (Array α)`.
- `prefix` is a reserved token. `{{` is not the f! brace escape — `\{` is.
- GADTs forbid nested `List (Value t)` — mutual sibling inductive.
- `Except` monads: `throw`, never `return .error`.
- `String.replace` is `(s pattern replacement)` — check `|>` arg order.
- `intercalate` as dot-syntax swaps sep/list.
- Root-module imports are NOT re-exported — import what you name.
- `String → Type` is `Type 1`.

## Architecture invariants

- The spec of record is the COMMITTED generated universe (byte-tie);
  never hand-edit GENERATED files.
- One writer per artifact path (audited in Tests).
- Emitters are pure `List Item → List GeneratedFile`; drivers write.
- The boundary universe (`Ty`) is CLOSED — new constructors must extend
  every emitter (compiler-enforced by exhaustiveness).
- Deltas at the boundary, inversion in the log (event-sourcing rule).
