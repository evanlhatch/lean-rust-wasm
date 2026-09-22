# Design — one-AST: the wasm-backend's two instruction ASTs collapse into one

Status: SPEC (notes-only — no code change is authorized by this document).
Model: notes/design-guest-verified.md's shape (context → design → exact
deltas → migration → risks). Executable by an agent with zero context:
every decl/path below was grepped against the tree 2026-09-23; a
reference that fails to resolve is a spec bug — fix the spec, not the
tree, if you find one.

---

## 0. Context — the two ASTs, verified

Two instruction ASTs describe the same machine today:

1. `WasmBackend.Wat.Instr` (lean/wasm-backend/WasmBackend/Wat.lean) —
   the EMISSION AST. The emitter (`emitCode`/`emitCases` in
   WasmBackend.lean) produces it; `instrW` renders it to the goldens.
   Locals/labels/functions are STRINGS (`localget (n : String)`,
   `block (label : String)`); ops ride the 19-ctor `Wat.Op` and the
   6-ctor `Wat.MemOp`; `mem` carries structured `offset`/`align`
   fields. `deriving Inhabited` only.
2. `WasmBackend.Sem.Instr` (lean/wasm-backend/WasmBackend/Sem.lean) —
   the SEMANTICS AST. 16 ctors, locals as `Nat`. Mirrors the flat
   subset 1:1 (its own header documents the mapping); `Sem.State.locals
   : Nat → Val`, and `Sem.Err.branch n ls` carries the branch-point
   locals as `Nat → Val`.

Between them sits the translation layer in
lean/wasm-backend/WasmBackend/Correct.lean — the FULL list, every decl
dies in this work:

- `Correct.localIdx?` (String → Option Nat; parses the emitter's
  `l{n}` family)
- `Correct.lowerI` (one `Wat.Instr` → `Option (List Sem.Instr)`;
  `.ret` → `[]`, the return convention)
- `Correct.lowerGo` (bodies, recursing into `if_`)
- `Correct.lower` (strips the trailing fallthrough-seal `unreach`)

Plus every consumer that re-spells the op/instr content per AST:
`Sem.step`'s arms, `Sem.checkStack`'s arms, `Sem.exec_typed`'s per-ctor
cases (exec_typed spans ~655–1190 of Sem.lean's 2738 lines), Audit's
walk (`WasmBackend.Wat.Audit.go`, lean/wasm-backend/WasmBackend/
Audit.lean), `WasmBackend.binop?` (WasmBackend.lean:134 — the LCNF
Name → `Wat.Op` map, 5 rows), and — zero proofs, the M3 finding —
edgepython's SECOND frame machine: `EdgePython.WEval` in
lean/edgepython/EdgePython/Eval.lean (231 lines: `stepI`, `execInstrs`,
`execFn`, `callModule`, `Flow`/`FlatFlow`, `getLocal`/`setLocal`,
`labelDepth`, `popN`, `WVal`, `wrap64`, `u64Of`), whose parity theorems
(`EdgePython.Parity.parity_*`, `wasm_*`) pin it against the PYTHON
reference, never against `Sem`. Also orphaned:
`Proofkit.Binop.u64add_sub` / `Proofkit.u64add_assoc` (verified zero
consumers outside the axiom gate's `#print axioms`).

Consumer census of `WasmBackend.Sem.Instr` (grepped): Sem.lean,
Correct.lean, WasmBackendTests/Axioms.lean (via the Correct import).
Nothing else. This is why the collapse is tractable.

In-flight collision (verified in the working copy): wasm-backend has
heavy parallel lanes (the deletions-verdicts and emitter-pipeline
waves, notes/review-2026-09-16.md wave queue). Step 0 below makes the
rebase explicit.

## 1. The one-AST design

**Sem executes `Wat.Instr` directly. `Sem.Instr` is deleted.** The
name→index resolution (`localIdx?`'s `l{n}` parse) is not moved
elsewhere — it DISSOLVES: the executor's local map keys on the NAME
itself.

Exact state change (verified against Sem.lean's actual definitions):

- `Sem.State.locals : Nat → Val` → `locals : String → Val`.
  The map was already a total function; only the key type changes.
  The emitter's `l0, l1, …` family stays a NAMING CONVENTION, never
  parsed again.
- `Sem.Err.branch (n : Nat) (ls : Nat → Val)` → `ls : String → Val`
  (the branch-point locals payload; the `n` frame-depth counter is
  unchanged).
- `Sem.checkStack (locals : Nat → Ty)` /
  `Sem.checkFrame` → the locals context becomes `String → Ty`.
- `Sem.Calls.bindArgs`'s `fun n => args.getD n (s.locals n)` — key
  type follows `State.locals`; `Fn { params : Nat, body : List
  Instr }` is unchanged except `body`'s element type is now
  `Wat.Instr`.

Signatures that change TYPE but not shape (same names, same arities):

- `Sem.step : State → Instr → Except Err State` — `Instr` is now
  `Wat.Instr`.
- `Sem.execList`, `Sem.exec` — element type follows.
- `Sem.checkStack`, `Sem.checkFrame`, `Sem.exec_typed`,
  `Sem.typeSafetyList`, `Sem.typeSafety`, `Sem.storeInBounds` —
  element + locals-key types follow.
- The whole `Calls` layer (`callExecFuel`, `callExec`, `pushArgs`,
  `popParams`, `call_split` and friends) and the `Alloc` layer are
  retyped the same way; their theorems re-prove mechanically.

How `step` covers the LARGER `Wat.Instr` (the honest ledger, per the
doctrine — every unmodeled form EXPLICIT, never a silent catch-all):

- Modeled already, mapped arm-for-arm: `i32const`/`i64const`
  (Wat's `Nat` consts — `step` applies the same `UInt32.ofNat` /
  `UInt64.ofNat` cast `lowerI` applied today, Correct.lean's
  "the fragment's consts are small" note moves into the arm),
  `localget`/`localset` (String keys), `.op .i32add`, `.op .i64add`,
  `.op .i32eq`, `drop`, `br`/`brif` (the String label is IGNORED
  dynamically — the frame-depth discipline replaces it; Sem's
  `br n` counts frames exactly as before, and `execList`'s label
  handling does NOT change because Sem never resolved labels
  syntactically), `block`/`loop` (label dropped), `if_`
  (`res : Option String` dropped dynamically — see Risk R5),
  `unreach`, `.mem .i32store8 _ _`, `.mem .i32load8u off _`
  (the structured `offset` field replaces `Sem.i32load8u`'s arg —
  strictly better: the field is the thing `Layout` feeds).
- `Err` gains ONE ctor: `unmodeled` (distinct from `trap` and from
  `structural`, which survives — `step` still never sees the three
  structural forms; `execList` dispatches them).
- Every remaining flat form gets an EXPLICIT
  `.error .unmodeled` arm: `.op` ctors i64sub/i64mul/i64ltu/i64leu/
  i64eq/i32sub/i32mul/i32and/i32xor/i32shru/i64shru/i32eqz/i32ltu/
  i32gtu/i32wrapi64/i64extendi32u (16 of 19 — W-A3 fills them),
  `.mem`'s other five `MemOp` ctors, `localtee`, `globalget`,
  `globalset`, `call`, `returncall`, `callindirect`, `memcopy`,
  `select`, `ret`, `raw`. The `Op`/`MemOp` sub-matches are written
  EXHAUSTIVELY WITH EXPLICIT ARMS (no wildcard) — a new `Op` ctor
  then breaks the build until an arm exists, which is the
  fail-loud discipline, compiler-enforced (Risk R7).

`checkStack` mirrors the same two classes: modeled arms as today
(retyped), explicit `.error "unmodeled"` strings for the rest —
also wildcard-free.

`Audit.go` is already over `Wat.Instr` and STAYS UNTOUCHED in W-A1
(it was never the duplicate; its `.op` arm has two bespoke sub-arms —
`i32eqz`, `i32add` — plus a fallback; W-A3 retargets the fallback).

**What dies** (complete list):

- `WasmBackend.Sem.Instr` (the whole 16-ctor inductive) — replaced by
  `Wat.Instr`.
- `Correct.localIdx?`, `Correct.lowerI`, `Correct.lowerGo`,
  `Correct.lower` — the emitter's output IS the machine's input; no
  `Option` wrapper, no fragment gate at the translation seam.
- In W-A2: the entire `EdgePython.WEval` evaluator (the decl list in
  §5).

**What the correctness theorem BECOMES.** Today the chain is emitter
→ `Wat.Instr` → `lower` → `Sem.Instr` → `Sem.execList`, pinned by
`#guard`s of the shape `lower (runEmit (doubleShape k)) == some
(specDouble k)` (Correct.lean's extraction checks — note the Option
and the lowering in the middle). After the collapse the chain is
emitter → `Wat.Instr` → `Sem.execList` — the statements lose the
lowering hop and keep the W6.9 two-leg shape (convergence +
fuel-insensitive partial correctness, glued by
`Sem.execList_ok_unique`). Exact new statement shape (the straight-line
theorem, `Correct.tpl_add_ret_ok` retyped — String locals, `.op`
wrapper; the proof strategy is unchanged, `simp only` over the same
equation lemmas):

```lean sketch
theorem tpl_add_ret_ok (x y l : String) (a b : UInt64) (s : Sem.State)
    (hx : s.locals x = .i64 a) (hy : s.locals y = .i64 b) (hs : s.stack = [])
    (fuel : Nat) (s' : Sem.State)
    (h : Sem.execList fuel s
        [Wat.Instr.localget x, .localget y, .op .i64add,
         .localset l, .localget l]
      = .ok s') :
    s'.stack = [.i64 (a + b)]
```

and the extraction `#guard`s become definitional identity with no
Option:

```lean
#guard (match runEmit (doubleShape 21) with
        | .ok is => is == specDouble 21      -- was: lower is == some (specDouble 21)
        | .error _ => false) = true
```

The end-to-end pins (`Sem.exec` of the LOWERED backend output = 42)
become `Sem.exec` of the backend output directly — the `lower is`
match inside those `#guard`s deletes. The extraction gap (hand-built
LCNF decls, `partial runEmit`) is UNCHANGED by this work — the header
of Correct.lean owns it; do not claim more than the seam move.

The templates (`tplLit`, `tplAdd`, `tplRet`, `specDouble`, `specAdd`,
`specCasesFrom`, `specCases`, `specCasesLoad`, the call-prep/
prologue/trampoline templates and their negative controls) are
restated over `Wat.Instr` verbatim — indices become `"l{n}"` strings,
`i64add` becomes `.op .i64add`, `i32load8u off` becomes
`.mem .i32load8u off 0` (the align field; `none` also acceptable —
pick one, the negative controls pin it). `tplLitBuggy`'s off-by-one
becomes `localset (s!"l{l+1}")` — same bug class, same theorem shape
(`spec_double_buggy_zero`, `buggy_ne_spec` re-prove by the same
`rfl`/`decide` routes).

## 2. The op table — the follow-up, not the first move

The "grand prize" candidate: a `declare_instr` table — one row per op
carrying (a) the wasm text (the `opW` mapping, Wat.lean), (b) the
stack effect, (c) the Lean `step` arm, (d) the checker arm
(`checkStack`), (e) the audit arm (`Audit.go`'s `.op` behavior) —
generating arms 2–5 from the row, so a new op is ONE row instead of
four hand-spelled consumers (`Sem.step`, `Sem.checkStack`,
`Audit.go`, and `binop?`'s LCNF row).

**Verdict: land the one-AST collapse FIRST; the table is the second
move, ON TOP of the collapse.** Dependency reasoning:

- A row can generate only ONE target shape. Today a `declare_instr`
  row would need to emit both a `Sem.Instr` arm AND a `Wat.Instr`
  arm PLUS the `lower` clause — three consumers, one of them (lower)
  about to die. Landing the table first freezes the two-AST split
  into the generator, and the collapse then has to fight the
  generator. Collapse first: the table's row shape lands on ONE
  instruction type and four (→ three after W-A2) live consumers.
- The table needs the SEMANTICS of the unmodeled 16 `Op` ctors as
  its row content. Those semantics exist in exactly one place today:
  `EdgePython.WEval.stepI` (i64sub/i64mul/i64ltu/i64eq/i32eqz —
  Eval.lean's arms). Lifting them into `Sem.Val` arithmetic is W-A2's
  work (see §5); the table's rows then cite the lifted arms as the
  semantics column. Table-first would re-derive semantics that
  W-A2 is about to deliver.
- Honest scope of the prize: the table is NOT what kills the 2700-line
  tower (§7, R1). It is what makes the NEXT op cost one row with a
  proof obligation attached, and what retires `binop?`'s drift risk
  (an op `binop?` emits but no row covers = a build break, not a
  silent wrong-backend).

**Per-op law template** (the type-preservation shape instantiated per
row — this is the "law" column of the table, the per-op slice of
`exec_typed`'s case shape, made standalone):

```lean sketch
-- `row.op`'s preservation: IF the row's checker accepts the op on a
-- stack of shape `pop ++ ts`, THEN any completed execution of the
-- one-instruction program ends on `push ++ ts` (fuel-insensitive —
-- the W6.9 partial-correctness leg; a one-instruction convergence
-- leg is per-row `rfl`-only and cheap).
theorem row_ok (row : InstrRow) (ts : List Ty) (s s' : Sem.State)
    (fuel : Nat)
    (hc : Sem.checkStack (fun _ => .i64) (row.pop ++ ts) [row.toInstr] = .ok (row.push ++ ts))
    (h : Sem.execList fuel s [row.toInstr] = .ok s') :
    stackTys s'.stack = row.push ++ ts   -- + the locals clause, row-shaped
```

The rows where this does NOT template are §7/R1's subject — the
load/store rows (the bounds check couples `memSize`), the comparison
rows (the `1`/`0` result VALUE is fixed but the theorem's antecedent
must exclude nothing), and anything touching `Err.branch` (rows never
produce branches — the structural forms are not rows).

## 3. The migration sequence

Gates named are the justfile's live definitions (`just gates` =
lean-proof-roots lean-build gen-check artifact-headers wit-check
lean-axioms native-policy kernel-check manifest-check coverage
check-schema breaking wasm-diff-check splice-smoke rt-conformance
lean-lint budget-check). Every step runs inside
`devenv shell --profile wasm` with
`TC=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0/bin`.

- **Step 0 — base pin.** Verify the in-flight lanes (deletions
  verdicts, emitter pipeline — the wave queue in
  notes/review-2026-09-16.md) have LANDED: `just gates` green on the
  parent of your working copy. If not, STOP — the collapse must not
  race the emitter-pipeline consolidation (both touch
  WasmBackend.lean's emission surface). `jj new` with a bookmark.
- **Step 1 (W-A1) — the collapse, one commit.**
  a. Retype `Sem.lean` per §1 (State/Err/checkStack/step/execList/
     exec_typed/Calls/Alloc). Compile after every declaration.
  b. Delete `Correct.localIdx?/lowerI/lowerGo/lower`; restate the
     templates + theorems + `#guard`s per §1.
  c. Gate: `cd lean/wasm-backend && lake build` (Correct.lean's
     `#guard`s are build-failing extraction checks — they ARE the
     gate), `lake exe WasmBackendTests` (wait — the test exe target;
     run per lakefile: `lake build WasmBackendTests && lake exe
     WasmBackendTests`), then `just lean-axioms`, then
     `just wasm-diff-check` — the OBSERVATION-FREE claim: emission
     bytes unchanged, the byte-tie over the WAT + the oracle manifest
     (`target/diff.json`) proves the collapse changed NOTHING the
     module emits. This is the strongest gate of the whole migration;
     if it moves, the collapse leaked into the emitter and the change
     is WRONG until explained.
- **Step 2 (W-A2) — edgepython migrates (§5).** Gate:
  `cd lean/edgepython && lake build && lake exe EdgePythonTests`,
  `just lean-axioms` (both packages: wasm-backend, edgepython —
  Parity.lean is an exile module in the native-policy allowlist, it
  must stay one or the gate grows).
- **Step 3 (W-A3) — the op table (§2).** One commit per table slice
  (binops, then comparisons/converts, then mem-ops) so each slice's
  per-row laws land green. Gate: the W-A1 gate list + the oracle
  replay (`just wasm-compile`'s differential smoke is INSIDE
  wasm-diff-check; the manifest must be byte-stable across the
  table's landing — semantics of newly modeled ops only reach
  `diff.json` if some fixture exercises them, and none does until a
  row's op enters `binop?`'s surface, which is a SEPARATE decision
  with its own manifest re-baseline).
- **Step 4 — `just gates`, full stop.** Then `just push`.

Nothing in the sequence touches `Wat.lean` (the renderer), the goldens,
`Layout`, or the oracle. lakefile.toml's globs
(`WasmBackend`, `WasmBackend.Correct`, `WasmBackend.Audit`,
`WasmBackend.Sem`) are UNCHANGED — Sem.lean keeps its path, only its
contents retarget.

## 4. The new top-level correctness surface (what one AST buys)

After W-A1+W-A2 there is exactly ONE place a per-op semantic can
live: `Sem.step`'s arm (then W-A3's row). The statement the program
is aiming at, stated once here so no agent re-derives it:

- Backend correctness (the seam, per shape): `∀ fuel s',
  Sem.execList fuel init (emitted body) = .ok s' → s'.stack =
  [the source's value]` — template instances pinned by Correct.lean's
  extraction `#guard`s + the fuel-insensitive theorems.
- Frontend parity (edgepython, after W-A2): `Sem`-exec of the compiled
  module ≡ `Py.pyEval` per fixture, with the negative controls
  (`buggy_double_diverges`, `swapped_dec1_diverges`) still diverging.
- The frame/allocator layers (`Sem.Calls`, `Sem.Alloc`) keep their
  theorems statement-unchanged modulo the locals-key type.

## 5. The edgepython angle — exact deletion + parity migration

With one AST, `EdgePython.WEval` (Eval.lean) is strictly redundant:
it re-implements Sem's frame machine (its own header: "~250 lines of
unproved interpreter beside a proved one") with a DIFFERENT value type.
Deletion, exact:

- DIE: `WVal`, `wrap64`, `u64Of`, `getLocal`, `setLocal`, `findFn`
  (folds into the replacement driver), `labelDepth` (Sem's frames are
  structural — there is no label stack to walk),
  `popN`, `FlatFlow`, `Flow`, `stepI`, `execInstrs`, `execFn`,
  `callModule`. `modFns` survives (the `Item.func` fold — pure module
  plumbing) and moves into the driver section.
- The parity theorems (Parity.lean: `parity_double_21`, …,
  `parity_if_max_9_3`; the wasm pins `wasm_double_21`, …) are
  RE-STATED, not deleted: the engine side becomes
  `Sem.exec` over the compiled `Wat.Instr` bodies, denoted into the
  Python reference's `Int` world:

```lean
-- shape (one per fixture; the wasm_* pins keep their exact form with
-- `Sem` in place of `WEval` and a Val-denotation in place of WVal):
theorem parity_double_21 :
    denot (Sem.execFn' compiledFns "double" [21]) = Py.pyEval fixtures "double" [21]
```

  where `denot : Option Sem.Val → Option Int` (or the exec-side
  `Except Sem.Err` unwrapped) maps `.i64 v → some v.toNat`-style — the
  bridging function is PINNED on the fixtures (concrete values), not
  proven in general; the general `WEval ≡ Sem` per-op theorem the old
  header wanted is REPLACED by "the evaluator IS Sem" — there is no
  second evaluator left to relate. That is the parity-theorem
  migration: same nine parity theorems + five wasm pins, new engine,
  negative controls (`buggy_double_diverges`, `swapped_dec1_diverges`)
  re-instantiated at the Sem level with the same buggy-emission
  modules (they are `List Func` — retyped to `Sem.Calls.Fn`/`Module`
  and run through the Sem frame machine).
- RISK carried by the migration (R3): `WVal.w64 : Int` + `wrap64` vs
  `Sem.Val.i64 : UInt64` (native wrap). The fixtures' values are far
  from the wrap boundary except `loop_sum` (adds up to 10) — safe,
  but the parity theorems' PROOFS go from `decide`-able `Option Int`
  computations to Sem machine runs (`simp only [execList, step]`
  chains); budgets re-derived (R3 in §7).
- Sem needs a per-module entry point (find-fn-by-name + the frame
  machine): add a small `Sem.callModule`-shaped driver
  (`List Fn → String → List Val → Option Val`) over `Sem.Calls`'s
  machinery + `findFn`-equivalent — ~10 lines, in Sem.lean's Calls
  section, NOT a resurrection of the deleted evaluator.
- `EdgePython.Compiler` (emits `Wat.Instr`) is UNTOUCHED — with one
  AST its output runs on the proved machine directly, which is the
  IR-reuse claim finally being TRUE at the type level for proofs,
  not just types.

## 6. What is deliberately NOT in scope

- No new modeled ops beyond what `binop?` already emits and W-A2's
  lift covers (i64sub/i64mul/i64ltu/i64eq/i32eqz). i64leu, i32and/
  xor/shru etc. wait for the table's rows to be FILLED (explicit
  `.unmodeled` arms until then) — filling them is row work, not
  collapse work.
- No `checkFrame` result-type extension (the typing gap stays; R5).
- No call-frames in the model (Sem.Calls v1's scope decision stands).
- No `binop?` surface extension (no new LCNF rows — that changes
  emitted WAT and needs its own order + manifest re-baseline).

## 7. Risks — the honest ones

- **R1 — the proof tower does not shrink the way the prize implies.**
  `exec_typed` (~535 lines) splits into: per-op cases (i32add/i64add/
  i32eq/i32store8/i32load8u — same shape modulo the type, these DO
  template into the per-row law of §2, and the `err_tail` macro
  already compresses the error triples) and the STRUCTURAL frame
  cases (block/loop/if_ with the branch-signal plumbing — genuinely
  bespoke; ~400 lines of the lemma, no per-op structure to exploit).
  Reading Correct.lean confirms the bespoke class is real: the
  frame cases carry the `branch 0`/`branch (n+1)` bookkeeping and the
  `checkFrame_ok` threading — nothing a per-op row generates.
  HONEST ESTIMATE of the whole program's consolidation: `Sem.Instr`
  (~40 lines) + the `lower` layer (~50) + WEval (~250) die outright;
  exec_typed's per-op cases compress into row laws (~150–250 lines
  once W-A3 lands); the structural cases RE-PROVE at ~the same size.
  The 2738-line Sem.lean does not halve. The real yield is one
  per-op surface for every FUTURE op — measure the win in "next op =
  1 row + 1 law", not in deleted lines.
- **R2 — value representation at the parity seam** (§5): WVal's
  Int/wrap64 vs Val's native UInt64 wrap. Pin with concrete values;
  do NOT attempt a general `wrap64 x = (x : UInt64)` denotation
  theorem in this program.
- **R3 — fuel budgets re-derivation.** WEval ran `execFn 400`;
  Sem's `defaultFuel` = 1000 but the migrated parity theorems run the
  frame machine whose fuel accounting (every flat step AND every
  frame entry AND every loop restart) may differ per fixture from
  WEval's — `loop_sum`'s restarts are the sensitive one. Budgets are
  per-theorem constants; derive by running the machine, pin, move on.
- **R4 — in-flight collision.** The tree has parallel wasm-backend
  lanes; Step 0's base pin is mandatory. The collapse touches
  Sem.lean, Correct.lean, and (W-A2) edgepython/Eval+Parity — if
  another lane touches those files, re-queue.
- **R5 — the `if_` result field goes along for the ride.** One AST
  means `Wat.if_ (res : Option String)` sits in Sem's match with the
  field dynamically ignored — the documented typing gap (the checker
  rejects correct branch programs, Correct.lean's TYPING GAP notes)
  persists AND becomes less visible (no separate AST to point at).
  Keep the existing `#guard` that pins the rejection (it survives
  verbatim) and the header ledger; the checkFrame extension is the
  table's follow-up, not this program's.
- **R6 — `Err.unmodeled` conflation pressure.** The easy wrong move
  is folding unmodeled into `trap` (it "is" one). It must stay its
  own ctor: the audit's job is distinguishing an unmodeled SEM from a
  genuine wasm trap, and `storeInBounds`-class theorems quantify over
  errors.
- **R7 — the wildcard temptation.** With 16 unmodeled `Op` ctors the
  collapse wants a catch-all arm. Forbidden (§1): the explicit-arm
  exhaustiveness is the only compiler-enforced force that makes the
  table's coverage claim true later. Same for `checkStack` and the
  audit fallback.
- **R8 — `#guard` opacity.** The mutual `checkStack`/`checkFrame`
  block is well-founded-compiled (Correct.lean's note) — kernel-
  opaque, so its checks stay `#guard`/interpreter-evaluated. Retyping
  does not fix that; do not "upgrade" the checker `#guard`s to
  `decide` (they will not reduce).

## 8. Work orders

- **W-A1** — the collapse (§1, §3 step 1). One commit:
  `jj describe -m "W-A1: one-AST collapse — Sem executes Wat.Instr (lower layer deleted)"`.
  Sizes: Sem.lean retypes ~60% of its lines mechanically, Correct.lean
  loses the lowering seam. Do not start until Step 0 passes.
- **W-A2** — edgepython migration (§5). One commit after W-A1 green.
- **W-A3** — the op table (§2): rows for the 5 modeled ops first
  (proves the generator against known semantics), then the W-A2-lifted
  five (sub/mul/ltu/eq/eqz), then the mem-ops, each slice gated.
- **W-A4** (optional, separate decision) — extend `binop?` to consume
  the newly modeled ops; changes emitted WAT; requires the manifest
  re-baseline and is NOT part of this program.
