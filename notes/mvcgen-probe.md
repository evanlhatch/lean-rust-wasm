# mvcgen deep probe — the WP typeclass vs the contracts lane's wp engine

Probe record (scratch in `/tmp/mvcprobe/`, run via `lake env lean` against
the built tree, toolchain v4.33.0). Nothing landed in `contracts/` — see
the verdicts. Zero `sorry` in anything quoted; every snippet below was
compiled.

## What the two sides are

**The tree's side** (`contracts/Contracts/Wp.lean`): `wp` is a closed
transformer over the first-order fragment `Prog` (assign / ret / bind /
cond), postcondition over result + exit state, with `wp_sound`,
`wp_bind` (`wp (p >>= k) Q = wp p (fun x => wp (k x) Q)`, `rfl`),
`wp_mono`, `wp_cons`, exactness (`wp_iff`), and the loop discipline
(`While` carrier + `LoopVCs` — init / preserve / descend / exit — with
`while_sound_fuel`).

**Lean's side** (`Std/Do/WP.lean`, `Std/Do/WP/Monad.lean`,
`Lean/Elab/Tactic/Do/VCGen/Basic.lean` in the toolchain src): the
`WP m ps` typeclass interpreting ANY monad into `PredTrans ps`, the
`WPMonad` discipline (wp preserves `pure`/`bind`), the `@[spec]`
schematic-postcondition mechanism, and the `mvcgen` symbolic-execution
tactic. Instances ship for `Id`, `StateT`, `ReaderT`, `ExceptT`,
`OptionT`, `EStateM`. `mvcgen` is flagged **experimental** by its own
toolchain ("Avoid using it in production projects").

---

## Q1 — the unification question: could `Prog` get a WP instance?

**Verdict: not directly — `Prog` is type-ineligible — but the unification
holds through the interpretation `interp`, and it is definitional.**

- `WP m ps` requires `m : Type u → Type v` with a `Monad m`. The tree's
  `Prog : Type` is a first-order AST (a deep embedding), not a type
  constructor; `bind : Prog → (Nat → Prog) → Prog` is not `Monad.bind`.
  No instance can be written on `Prog` itself. (Observed: the class
  signature, `Std/Do/WP/Basic.lean`.)
- But `Prog.exec : Prog → State → Nat × State` makes `Prog` a notation
  for `StateM State Nat`, and `WP (StateM σ)` **already exists** in Std
  (`StateT.instWP`, `StateT.instWPMonad` with `m := Id`). The bridge is
  `rfl` (probe1, `bridge`):

```lean sketch
def interp (p : Contracts.Prog) : StateM Contracts.State Nat := p.exec

theorem bridge (p : Contracts.Prog) (Q : Nat → Contracts.State → Prop)
    (s : Contracts.State) :
    (wp⟦interp p⟧ post⟨fun x s' => ⌜Q x s'⌝⟩ s).down
      = Q (p.exec s).1 (p.exec s).2 := rfl
```

  and the tree's `wp p Q s` reduces to `Q (p.exec s).1 (p.exec s).2` by
  its own defining arms — so **the tree's wp engine IS the typeclass
  WP's instance face at `interp`**, definitionally, with the tree's
  state model (`Effects.State`) and the tree's `Key`/`upd` lived-in.
- **mvcgen accepts it.** Two positive probes:
  - A do-notation program over the tree's own state model and `upd`
    (the fragment's increment) — `mvcgen [Contracts.upd]` closed the
    whole spec with **zero leftover goals** (probe2, `incr_spec`).
  - A **concrete `Prog` literal through `interp`** —
    `mvcgen [Contracts.Prog.exec]` also closed it outright (probe2,
    `ex2` example). mvcgen reads the fragment's own carriers.
- **Boundary (important):** mvcgen symbolically executes only via
  `@[spec]` theorems matching the program-head constant; a def-headed
  program with no spec falls back to `simp` (trace: "Failed to find
  spec for wp maybeSet. Trying simp. Candidates: []"). Straight-line
  bind/pure/get/set closes; **branching (if/match) only splits when the
  do-term is INLINE in the theorem** (probe12: two branch VCs
  `vc1.isTrue` / `vc2.isFalse` with hypotheses `s 0 = 0` /
  `¬s 0 = 0`); a def head with branches leaves the whole wp (probes
  9–11).
- **Negative control** (probe19, compiled): the wrong postcondition
  `r = s' k + 1` for the increment is **refutable by computation** —
  `simp [incr, Contracts.upd]` reduces the wrong-spec wp to `False` —
  matching the tree's exactness face (`wp_iff`). The toolkit refuses;
  it never fabricates.

**Adoption reading:** the unification is real and free (one `interp`
abbreviation + one `rfl` bridge theorem), and the tree's wp rules are
the same equations the `WPMonad` laws state (`wp_pure`/`wp_bind` vs the
tree's `rfl` arms). But since the tree's `wp` is *already* the
definitionally-equal instance face, adopting the typeclass changes no
semantics — it only changes WHICH PROVER FACE runs on top (`mvcgen` vs
the hand `wp_sound` route).

## Q2 — the effect-heavy zone: where would mvcgen verify the tree's own code?

**Verdict: nowhere that matters; the honest candidates are outside the
fragment, and the inside candidates are already proved better.**

- The gates' IO drivers (`gates/GatesMain.lean`: `runAxioms`,
  `runKernelCheck`, … all `IO UInt32`) and the goldens' teeth
  (`SchemaCore.Goldens.goldsTeeth : CommandElabM Unit`) run on `IO` /
  `CoreM`. **`IO` has no `WP` instance** (probe15: `inferInstanceAs
  (WP IO .pure)` fails to synthesize), and `CoreM`/`CommandElabM` are
  built on it — mvcgen's fragment ends where the toolchain's own
  monads begin. The drivers' error paths are `throwError` /
  `IO.eprintln` plumbing whose correctness content is delegated to the
  THEOREM channel, not the driver.
- The emitters are **total pure folds verified by kernel reduction**:
  `diff_artifact : Emit.Rust.renderDifferential = goldenDiff := rfl`
  and the TS tie in `SchemaCore.Goldens` are `rfl` theorems. mvcgen's
  symbolic evaluation would be a *weaker* proof face than the kernel
  `rfl` the tree already uses — and 08 §36's own scope note says it:
  "total pure functions keep direct proofs".
- The registry replays are `EStateM`-shaped in spirit (`Result.ok` /
  `.error` in `goldensTeeth`), and `EStateM` *does* have WP instances —
  but the replay's content is `getSchemas env` over the mutable
  environment, i.e., meta, opaque, outside the fragment.

**Verdict unchanged by probing:** the tree's own code is meta/IO-heavy
precisely where it is monadic, and pure-exactly-where-verifiable. There
is no effect-heavy zone where mvcgen adds verification the tree lacks.

## Q3 — the radical approach: rebuild the contracts lane ON the WP typeclass?

**Verdict: a regression. The named stay.**

- The tree's discipline is **type-level unconstructibility**: a wrong
  invariant cannot build `LoopVCs` (`vBody` is false and the structure
  refuses); `FeasibleVc` carries the admissibility witness in the type,
  so a vacuous contract cannot forge a discharge; `Kit.Obligation`'s
  claim is the type index. mvcgen's VCs are **tactic-level subgoals** —
  metavariables left for `grind`/`omega`, closed or not, with no
  unforgeability discipline. 01 §7's ladder ranks exactly this:
  unrepresentable > no-instance > … > hand theorem — "the ladder ranks
  the LOCATION of correctness, not the count of handwritten proofs".
  The tree sits at the top of that ladder; the mvcgen face sits below
  it.
- The probe showed the concrete costs of the mvcgen face for exactly
  the tree's shapes: def-headed branching programs don't split (Q1
  boundary); recursive/loop programs need user-written `@[spec]` step
  lemmas whose RHS must be an inline do-term — and the `rfl` proof of
  such a restatement **fails** (elaboration drift between the def body
  and the restated body; probes 13–14), forcing an induction per loop
  that the tree's `While` carrier avoids by making the invariant+variant
  DATA. mvcgen's `invariants?` suggested nothing for def-head loops
  ("There were no suggestions for missing invariants").
- What mvcgen would genuinely buy — free splitting of inline branches,
  `grind` discharge of arithmetic VCs — the tree's VCs don't need: the
  fragment's `cond` rule is a `rfl` arm, and the routine fragments
  discharge through the decidableNow backend (`Contract.pointDischarge`)
  with a soundness theorem behind it (`pointDischarge_sound`).
- The honest residual value of the probe: `interp` + the bridge is a
  legitimate **compatibility note** — if a future wave wants mvcgen's
  ergonomics for an INLINE do-term over `Effects.State` (a quick what-if
  spec, a script-style proof), it can have them over the tree's own
  state model with no new machinery (Q1 probes). That is an additive
  scratch-level convenience, not a rebuild.

## Q4 — the bidirectionality angle

**Verdict: mvcgen verifies the MODEL's Lean side only; 03's discipline
is untouched.**

- What the probe actually demonstrated (Q1): mvcgen can verify claims
  about programs over the tree's `Effects.State` model — i.e., the
  Lean side of a lane. That is the same side the tree's wp engine
  already covers, with exactness (`wp_iff`) that mvcgen's
  partial-correctness face does not exceed. (Note: v4.33's `while`
  desugars to `ite` on a Prop — partial correctness with pinning; there
  is **no variant/termination certificate** in mvcgen's box. The
  tree's `LoopVCs.vVar` — the descent VC — has no mvcgen counterpart.)
- The Rust side stays the duel: the byte-tie is the committed generated
  artifact vs the emitter output (`rfl` theorems + the goldens' teeth),
  and the emitters are pure folds — kernel-reduced, no monadic
  fragment, nothing for mvcgen to see. mvcgen adds no lever on the
  cross-language boundary; 03's discipline (the duel, the byte-tie,
  never hand-editing generated files) is orthogonal to wp entirely.

---

## The adoption design (what would land, if anything)

**Nothing lands in `contracts/`.** The probe's conclusion is the named
stay: the contracts lane keeps its own wp engine, which (a) is
definitionally the WP typeclass face at `interp` — the unification is
already true, adopting it changes nothing semantically; (b) sits higher
on 01 §7's ladder (type-driven unconstructibility over tactic-driven
subgoals); (c) covers the loop variant discipline mvcgen lacks; and (d)
targets the fragment where the tree's own code is either pure (kernel
`rfl`, stronger) or meta/IO (no WP instance, out of fragment).

If a future consumer appears, the landing shape is one file,
`contracts/Contracts/WpBridge.lean` (or a tests-side module first, per
the leftover rule):

```lean sketch
/-- The typeclass face of the tree's wp — the bridge is definitional. -/
def Prog.interp (p : Prog) : StateM State Nat := p.exec

theorem wp_eq_wpTC (p : Prog) (Q : Nat → State → Prop) (s : State) :
    (wp⟦p.interp⟧ post⟨fun x s' => ⌜Q x s'⌝⟩ s).down = wp p Q s := rfl
```

…with the four required rows if it were more than a bridge (lakefile
none needed — same lib; cone-table: Contracts stays C1-core, `Std.Do`
import check against the mathlib-free cone rule; gates: the per-library
axiom sweep already covers the module; tests: `wp_eq_wpTC`'s `rfl` pin +
the negative control). Until such a consumer exists, the leftover rule
says: don't.

## Probe ledger

| Probe | Claim | Result |
|---|---|---|
| probe1 `bridge` | tree wp = typeclass wp at `interp` | `rfl`, compiles, no `sorryAx` |
| probe2 `incr_spec` | mvcgen over tree state model + `upd` | closed by mvcgen alone |
| probe2 `ex2` | mvcgen through concrete `Prog` literal | closed by mvcgen alone |
| probe9–12 | branch splitting | inline do-terms split (`vc1.isTrue`/`vc2.isFalse`); def heads do not |
| probe13–14 | loop/@spec step lemma | restated-body `rfl` fails; `invariants?` silent for def heads |
| probe15 | `WP IO` | fails to synthesize (IO outside fragment) |
| probe19 `incr_neg` | wrong postcondition refutable | `simp [incr, Contracts.upd]` → `False` |
