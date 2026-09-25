# Design: the closed-universe case sweep (P1)

**Status:** design, unlanded. **Author:** senior designer. **Consumers:**
the wave that ports these proof refactors; `notes/v3/15-patterns.md`
gains entry 18 at the wave's commit.

**Doctrine slots named** (the mandate's contract): the graded carrier
(01 §4 — the exhaustion tables are data with laws in the type); the
ladder (01 §7, 04 §1 — every mechanism below is rung 1–4 data or rung
6 write-once-cite structure lemmas; the rejected alternative is
sub-ladder proof search, 06 §10); the pattern catalog (15 — this note
becomes entry 18); the placement lookup (mandate hard rules — every
kit lands INSIDE its consumer's existing library; no new lakefile row,
cone-table row, gates row, or test list entry is needed, and per the
leftover rule none may be added ahead of content).

**The claim, up front.** The ~1,500–2,000 LOC audit estimate counts
scaffolding the tree has ALREADY collapsed once (Guest's `RowP`,
Explore's `foldFrontier_*`). The honest remaining duplication is six
sites, four shapes, and the weakest mechanisms that cover them are all
rung ≤ 6: **exhaustion-as-data + one generic lemma** (2 sites),
**inversion lemmas over the mismatch grid** (2 sites), **a premise-pack
structure** (1 site), **the definition's own equation-lemma set, wired**
(2 sites). The `case_sweep` tactic macro is evaluated and REJECTED
(§B.1). Honest achievable total: **≈ −200 to −280 net LOC** plus the
larger win — every grid/triple/quadruple becomes a single-payment
obligation, so the NEXT theorem over these universes costs rows, not
arms.

---

## A. The taxonomy (every site, its shape, file:line)

Shape key: **T** = table + generic lemma (candidate 2); **G** =
verdict-grid / inversion kit (candidate 3); **P** = premise-pack
structure (candidate 4); **E** = equation-lemma set of the definition,
wired as a named attr (06 §5's endorsed discipline); **H** = stays
hand (real per-arm content).

### A.1 Witness.lean — the mismatch grid is **G**

- `checkWitness` (Witness.lean:143-155): a Bool checker whose catch-all
  arm `| _, _, _, _ => false` is SEMANTICS ("a proof term that does not
  fit the claim is not evidence" — the doc at 148-150). The grid is
  `WProof` (4 ctors, :118-133) × `Pred` (8 ctors).
- `checkWitness_sound` (169-213): `cases pr` (4 arms), three of which
  `cases p` (8 sub-arms each); the `neg` arm nests `cases inner`
  (4 sub-arms). Counted: 21 mismatch arms `| … => simp [checkWitness]
  at h`, 4 real arms (`and+conj` 186-189, `or+disj` 202-205,
  `not+neg+verdict false` 209-217, plus `verdict` 174-176 which needs
  no `cases p`).
- `checkWitness_mono` (230-308): the SAME grid walked again — 24
  mismatch arms, the real arms differing only in threading
  `Nat.succ_le_succ_iff.mp hle` into `ih`.
- Verdict: 45 mismatch arms across two theorems, all instances of ONE
  fact per proof-term ctor: *acceptance forces shape*. That is an
  **inversion lemma**, the pattern-12 inversion kit applied to a Bool
  checker. NOT a table site (nothing enumerates `Pred`; the content is
  the two-type shape match).

### A.2 Migrate.lean — fold-arm plumbing is **E**, with real content **H**

- `FieldPlan` is RECURSIVE (`carry/retype/fill` carry a tail plan) —
  these are structural inductions, not finite sweeps. Candidate 2
  (FinEnum-style enumeration) does NOT apply; an honest design must say
  so.
- `project_key_stable` (219-269): 3 inductive arms; each arm =
  destructure a `Bool.and` premise → `show` the goal equation →
  `simp only [RowVals.project?, …]` → `ih`. The `by_cases`/`if_pos`
  dance (239-243) repeats per arm.
- `stableKey_comp` (410-475): induction on `p23` × `cases p12` — 10
  arm-pairs, each the textual triple `have hx := … simpa [stableKey]`
  + `simp only [comp, stableKey, hx.1, ih …, Bool.and_true]`. REAL
  content lives here: the composed `retype` checks only `fN.name`, so
  `stableKey (comp p23 p12)` is NOT `stableKey p23 && stableKey p12`
  (the middle factor `!(fM'.name == key)` is dropped — verified against
  `comp` at Migrate.lean:400-405). The law is an implication, not a
  distributive equation — that is why this is rung 6 hand content, and
  why the collapse targets only the plumbing.
- `upcast_comp` (477-531): the same triple shape over
  `comp`/`upcast` equations, 10 arm-pairs, no extra premise content.
- Verdict: **E** — one `@[simp]`-wired equation set over
  `FieldPlan.comp`/`stableKey`/`upcast` (06 §5: a named attr where a
  hand `simp only` list repeats) collapses each arm to
  destructure + `simp_all`/`exact ih`. The premise-destructure and the
  middle-factor subtlety stay **H**.

### A.3 Update.lean `foldDeltas_go` — the carried-invariant kit is **P**

- The theorem (1015-1295, ~280 lines) is ONE induction over `rest`
  carrying FOUR premises (`hproj`, `hfresh`, `hnd`, `hI`, 1019-1026)
  that must be re-derived at every recursive call shape. The verbatim
  blocks:
  - shrunk kit `hfreshS/hndS/hIS` (1040-1048) — used at every leaf;
  - K-extended kit `hfreshK/hndK/hIK` (1053-1062) and its `applySets`
    twins `hfreshK'/hndK'/hIK'` (1205-1215, 1240-1250) — three copies
    differing only in `hk` vs `hk'`;
  - insert-extended `hI1` (1100-1118, 1159-1177, 1255-1273) — three
    byte-near-identical 19-line blocks.
- Verdict: **P**, the textbook premise-pack. A structure
  `KeyImgsInv K rest I` bundling the four premises + three constructor
  lemmas (`shrink`, `keep` (parameterized by the kept row's key-image
  equality — covers both `hk` and `hk'` uses), `insert`) each proved
  ONCE. The 12-leaf case tree itself (guard × delete × sets × insert?)
  is the semantics and stays — the pack removes premise re-derivation,
  not the case analysis. Note `KeyCoherent` (1298+) already packs the
  USER-level premises; the pack extends that discipline one level down
  into the induction.

### A.4 Substrait `parseScalarGo_typeChars` — exhaustion-as-data is **T**

- The theorem (314-360): `cases n`, then per nullability arm
  `cases c <;> simp [… chars_bool_cons, chars_i32_cons, chars_i64_cons,
  chars_string_cons]` — the four ctor branches differ ONLY in which
  per-ctor `rfl`-lemma (Text.lean:160-169 family) the simp set cites.
  The fuel-0 arm repeats the same four citations through
  `chars_*_length` (325-328).
- The per-ctor lemmas are the text-proof discipline's once-per-format
  `rfl` family (mandate: literal `"…".toList` reductions established
  ONCE) — but here they are cited per-ARM, four times, when the
  exhaustion itself is the data.
- Verdict: **T**. `ScalarCtor.chars` IS the table (a function out of a
  closed 4-ctor type); the NameTable bundle precedent sits in the SAME
  file (Text.lean:380-397, `sortDirTable` 403+). The generic lemmas the
  round trip actually needs are token-agnostic: `startsWith (t ++ r) t`
  (a List-generic fact), `t ≠ []`, and "`?` ∉ token heads" (the
  follow-set fact, one `decide` over the table). One generic proof over
  `c`, zero per-ctor branches. The `chars_*_cons/length` `rfl` family
  stays (they ARE the table's face) but is cited once, inside the
  generic lemma.

### A.5 WasmCore mem — half-built **T**; finish the row table

- `MemRow` (OpTable.lean:78-92) and `memRow : MemOp → MemRow`
  (OpTable.lean:119-136) already exist — name, opcode, align, sig, and
  a PROSE `sem` note. The execution content (width 1/4/8, load-vs-store,
  value type) is NOT in the row: `step`'s mem arm re-spells it across 7
  match arms (Exec.lean:410-459), and `step_mem_spec` re-proves the
  same 16-line `by_cases` bounds/trap/push block 7 times
  (Exec.lean:924-1049).
- Verdict: **T**, the largest single win. Extend `MemRow` with the
  execution row (`width : Nat`, `access : load ValType | store ValType`
  — names indicative); redefine the mem arm of `step` as ONE generic
  computation over `memRow op`; prove `step_mem_spec` ONCE over an
  abstract row + discharge the 7 ctors by `cases m <;> rfl/decide` at
  the row's field projections. `step_mem_preserves`/`step_mem_outcome`
  stay as projections (they already are, Exec.lean:1051+).
- Honest cost: this is the ONLY def change in the program. Consumers of
  `simp [step]` on mem instructions re-check (Exec.lean:782, 809 cite
  `memPop/memSig/memRow` through `step` already — the row projections
  keep their names, so the simp faces survive). Guest's fragment has no
  mem instructions (fnModuleW, Correct.lean:577-583 — "no memory"), so
  the guest lane is untouched. Blast radius: WasmCore + WasmTests pins.

### A.6 Guest/Correct.lean — mostly paid; the residue is **E**

- The audit's "hrow premise ×5" is NOT five proofs: `RowP` is one
  abbrev (300-310) with two instances (`row_opW` 313-316, `row_wBuggy`
  ~323-327, each already a one-line `cases op <;> simp`) consumed by
  `fap_steps` (341), `run_chain` (374), `run_chain_inv` (455),
  `run_fnBody` (542). This is 01 §6's per-primitive-preservation
  discipline ALREADY LANDED — the design must not "fix" it.
- The real residue: `run_chain_inv` (455-~533) pays the fuel-shape
  case-peel per node — nested `cases fuel/cases f/cases f'`… with an
  `execList_zero`-absurd per level (the `fap` arm: 4 nested peels,
  ~473-495). `run_chain` avoids it via the sufficiency arithmetic
  (`m + need e`, 374-388). The twin simp blocks (`compileChain,
  List.cons_append, execList, h1…`) are the missing **E**: ONE
  equation lemma `execList (f+1) s (i :: is) = …`-in-`step`-form, then
  each peel is a `rw`, and `split`/`simp` discharges the outcome match.
- The per-node tails (`funext n; by_cases hn : n < L; …; locals_else …`,
  e.g. 400-408 and its twin in `run_chain_inv`) carry REAL content
  (the env-update/ locals-update agreement per ctor) — **H**, cited via
  `locals_else` already; a further collapse is possible (a per-node
  "step face" structure pairing `*_steps` with its `realizes_*`), but
  the two twins differ in direction (equation vs. inversion), so the
  honest call is: leave the tails, take the fuel-peel kit.

### A.7 Machines/Explore.lean — mostly paid; the residue is **G**-lite

- `foldFrontier_run` (267-292) and `foldFrontier_coverage` (298-326)
  ARE the collapsed skeletons; `seen_handler` (368-378) is the shared
  some-face. The audit's "verdict-handler block ×4" is the four
  `cases hb : badEntry inv? a with | none => simp […] at hcon | some e
  => …` blocks inside `exploreAux_proved`'s `hbudget/hstable`
  (336-350) and `exploreAux_refuted`'s (393-408).
- Verdict: **G**-lite — the two observers (`refutedOf`, `stabilizedOf`)
  each want ONE equation/inversion lemma
  (`refutedOf inv? a = v ↔ (badEntry … , …)`-form); the four handler
  blocks become four one-line rewrites. ~10 lines of kit, ~20 removed.
  Anything more is theater — the skeletons already carry the induction.

### A.8 The E/G twin family (textkit/TextKit/Grammar/Laws.lean:~1020)

EXCLUDED — the transfer-discipline agent owns it. Composition rule
(§E): our kits shrink the per-side scripts; transport then moves less.

---

## B. The mechanisms, evaluated honestly

### B.1 Candidate 1 — the `case_sweep` tactic macro: REJECTED

- **Fit:** the sites it would serve are A.1's grid (better served by
  inversion lemmas — proof terms the kernel checks, citable by name,
  no elab) and nothing else. Every other site's collapse is data or
  structure, where a tactic contributes nothing.
- **Precedent:** the tree's four meta surfaces (`register_lane`
  Kit/Lane.lean:261, `declare_bridge` Kit/Derive/Bridge.lean:103,
  `declare_fold` Kit/Derive/Fold.lean:318, `declare_cascade`
  Kit/Derive/Cascade.lean:338, plus `schema_entity_machine`
  SchemaCore/EntityMachine.lean:879) are ALL declaration generators —
  `spec → List (decl + law)`, pattern 8/the spine (01 §5). A
  proof-SCRIPT compressor would be a new KIND of surface: no env
  extension to ride, no byte-tie story (proofs aren't artifacts), and
  per-command curated-failure obligations (05 §4) for zero new
  capability.
- **Cost:** 06 §10 — grown proof terms rot under drift; a macro over
  `cases <;> simp` is exactly the grind-shaped fragility the doctrine
  bans as a foundation. The elab-watch gate (justfile:199-200,
  `gates-elab-watch`, re-times every gated root against
  `notes/elab-baseline.tsv`) pays for every new elaboration path; the
  inversion-lemma route pays nothing (plain theorems).
- **What survives of the idea:** stock `<;>` at call sites (A.4's
  `cases c <;> simp` already does this) and the escape-hatch goal the
  sweep leaves behind — which is precisely the inversion-lemma
  interface. The macro adds a name over two tokens of stock tactic;
  rejected per weakest-sufficient.

### B.2 Candidate 2 — exhaustion-as-data (table + ONE generic lemma): ADOPTED for A.4, A.5

The exhaustion is the closed type's ctor table; the law is one generic
lemma over the table. Canonical precedent in-tree: `NameTable`
(Text.lean:380-397) with `nodup := by decide` + `complete` — rungs 3–4.
Two honest sub-cases:
- A.4 needs no new structure — `ScalarCtor.chars` is already the table;
  only the generic token lemmas are new.
- A.5 extends an existing table (`MemRow`) with the semantic fields the
  consumers currently re-spell — the doctrine's "one row per ctor,
  consumers are projections" (OpTable.lean:96-99 doc) completed.
NOT applicable where the universe is recursive (A.2's `FieldPlan`) or
where the content is a two-type shape match rather than an enumeration
(A.1) — naming that boundary is part of the pattern.

### B.3 Candidate 3 — the verdict grid as product + generic off-diagonal: ADOPTED as inversion lemmas for A.1 (and A.7-lite)

The 45 mismatch arms of A.1 are one fact per `WProof` ctor: acceptance
at that ctor forces the matching `Pred` shape and hands back the
sub-checks' truths:
```lean sketch
theorem checkWitness_conj_inv {fs} {f} {p : Pred fs} {pp pq row} :
    checkWitness (f+1) p (.conj pp pq) row = true →
    ∃ a b, p = .and a b ∧ checkWitness f a pp row = true
                         ∧ checkWitness f b pq row = true
```
(plus `disj_inv`, `neg_inv`). The grid is paid ONCE inside these three
lemmas (each: `cases p`, 7 mismatch cells by the checker's equations,
1 real cell); `checkWitness_sound`/`checkWitness_mono` then run 4 arms
each with the real content only. This is pattern 12's inversion kit
moved onto a Bool checker — NOT a product-type restructure: the
catch-all refusal is semantics (A.1), so the grid is load-bearing and
the honest collapse is the inversion face, not making mismatch
unrepresentable. (The rung-1 alternative — indexing `WProof` by the
claim — was considered and rejected: it moves the refusal out of the
checker's semantics into decoding, changing what the certificate
MEANS.)

### B.4 Candidate 4 — premise-pack structures: ADOPTED for A.3 only

The rule: an induction carrying ≥ 3 invariant premises that re-derive
at ≥ 2 call shapes gets a named structure + one constructor lemma per
call shape (`shrink`/`keep`/`insert` for A.3). This is the
`KeyCoherent` discipline (Update.lean:1298+) applied INSIDE the
induction, and `foldFrontier_*`'s `hbudget/hstable` parameterization
(Machines) is its already-landed sibling — the pattern exists in the
tree under two faces; entry 18 names them one. Honest boundary: packs
move plumbing only; the foldDeltas_go case tree stays.

### B.5 The mechanism the candidates missed: **E** (equation sets, wired)

A.2 and A.6 are neither grids, tables, nor packs — they are folds whose
arms repeat the definition's own equations through hand `simp only`
lists. 06 §5 already names the discipline ("simp only over hand lists
is a smell where a named attr or generated set exists"); the sites
pre-date it. One attr per definition family (`FieldPlan`'s
`comp/stableKey/upcast` set; `execList`'s step-form equation), wired at
the definition, cited at every arm.

---

## C. Landing sequence (per-step green: `just build` + `just test` + `just gates`)

Order: leaf-risk first, the one def change last. Every step is a
proof-only refactor EXCEPT step 6; steps 1–5 keep every theorem
statement byte-identical (the refactor's own regression check is that
the statements — the pinned API — do not move).

| # | Site | Mechanism | Files touched | LOC delta (est.) |
|---|------|-----------|---------------|------------------|
| 1 | A.3 `foldDeltas_go` | **P**: `KeyImgsInv` + 3 constructors, placed in Update.lean above 1015 (no new file — leftover rule) | schemacore/SchemaCore/Update.lean | +~65 kit / −~105 blocks → **−40** |
| 2 | A.4 scalar round trip | **T**: generic token lemmas + one proof over `chars`; `chars_*` family cited once | substrait/Substrait/Text.lean | +~18 / −~32 → **−14** |
| 3 | A.1 Witness grid | **G**: `conj_inv`/`disj_inv`/`neg_inv`, then sound+mono re-armed | schemacore/SchemaCore/Witness.lean | +~45 kit / −~45 arms → **≈0** (grid ×2 → ×1; the win is the obligation, not the lines) |
| 4 | A.2 Migrate folds | **E**: `@[simp]`-wired plan-equation attr; re-arm 3 theorems | schemacore/SchemaCore/Migrate.lean | **−50 to −60** |
| 5 | A.6 Guest fuel-peel + A.7 observer faces | **E** (`execList` step equation) + **G**-lite (2 observer inversion lemmas) | guest/Guest/Correct.lean, wasmcore/WasmCore/Exec.lean (lemma near `execList`), machines/Machines/Explore.lean | **−35 to −45** |
| 6 | A.5 mem row completion | **T**: `MemRow` + exec fields; `step` mem arm generic; `step_mem_spec` once over the row + `cases m` row discharge | wasmcore/WasmCore/OpTable.lean, wasmcore/WasmCore/Exec.lean, WasmTests pins re-check | +~55 / −~135 → **−80** |

**Honest total: ≈ −170 to −240 net LOC** (call it −200 ± 40), NOT the
audit's implied kiloline collapse. The defensible claim is obligation
dedup: 45 grid arms → 3 lemmas; 3 freshness triples → 3 constructor
applications; 7+7 mem arms → 1 row + 1 proof; 4 ctor branches → 1
generic proof; and every FUTURE theorem over these universes inherits
the kit. Per-step acceptance: gates green, statements unmoved (steps
1–5), the duel rows + WasmTests pins green (step 6), and each kit
lemma's negative control already exists in the suites that pin these
theorems' consumers.

---

## D. The pattern-catalog entry (for notes/v3/15-patterns.md, landing with step 1's wave)

> **18. The closed-universe sweep kit (exhaustion is data; the grid is
> paid once).** Proofs over a closed universe split into the CASE
> SCAFFOLD (which ctor am I in) and the ARM CONTENT (what this ctor
> means). The scaffold is never per-theorem: (a) where the theorem
> enumerates a closed type, the enumeration is DATA — the ctor table
> (`NameTable`, `memRow`); per-ctor facts are the table's projections,
> discharged by `decide`/`rfl` at the row, and the theorem is ONE
> generic lemma over the table; (b) where a Bool checker's catch-all
> refusal is semantics, the claim-shape × proof-shape mismatch grid is
> paid ONCE as per-proof-ctor INVERSION lemmas (acceptance forces
> shape), and every soundness/monotonicity theorem runs its real arms
> only; (c) where an induction carries ≥ 3 invariant premises that
> re-derive at ≥ 2 recursive-call shapes, the premises are a named
> STRUCTURE with one constructor lemma per call shape (the
> `KeyCoherent`/`foldFrontier` discipline moved inside the induction);
> (d) where fold arms repeat the definition's own equations, the
> equation set is a named attr wired at the definition — never a hand
> `simp only` list per arm. Canonical: SchemaCore.Witness's inversion
> kit, SchemaCore.Update's `KeyImgsInv`, Substrait's `NameTable`,
> WasmCore's completed `MemRow`. Why right: the scaffold is rung ≤ 4
> data or rung 6 write-once structure; the arm content stays hand where
> it IS the content; a `case_sweep` tactic macro was evaluated and
> rejected (proof-term rot per 06 §10, elab-watch cost, no byte-tie —
> the macro's only value is the escape hatch, and the inversion lemma
> IS the escape hatch as a kernel-checked term). When NOT: recursive
> universes whose arms carry real per-ctor content (the kit moves
> plumbing only — Migrate's `stableKey_comp` middle-factor stays hand);
> genuinely open worlds (pattern 15's boundary); a mismatch that is
> unrepresentable-by-construction (then there is no grid — take rung 1).

## E. The honest residue (what stays hand, and why)

- **A.1's four real arms** (`and+conj`, `or+disj`, `not+neg` refutation
  via `check_complete`'s contrapositive, Witness.lean:209-217) and
  mono's `hle`-threading: relational content, rung 6, cited.
- **A.2's premise content**: the `stableKey (comp …)` non-equation (the
  dropped middle factor) is a real semantic fact about `comp`
  (Migrate.lean:400-405); the kit removes the plumbing around it, never
  the fact.
- **A.3's 12-leaf case tree**: guard × delete × sets × insert? IS the
  update semantics; only the premise re-derivation packs.
- **A.6's per-node tails** (`funext`/`locals_else` agreement): real
  per-ctor content in two non-symmetric directions (equation vs.
  inversion); collapsing further would fake a symmetry that isn't
  there.
- **A.5's per-ctor row VALUES**: still `cases m`-discharged — that is
  the table's face, not duplication.
- **The E/G twins**: the transfer agent's. Composition rule: land the
  kits FIRST (steps 1–5 are statement-preserving, so they commute with
  transport work); the transfer discipline (01 §4/§6 correspondence
  transport) then carries SMALLER per-side scripts. No shared files, no
  ordering constraint beyond that preference.
- **What this design does NOT attempt**: re-baselining any gate
  (mandate: drift is reported, never re-baselined mid-order); new
  libraries, lakefile rows, or gate rows (placement lookup: every kit
  lands in its consumer's existing lib); any tactic elab.
