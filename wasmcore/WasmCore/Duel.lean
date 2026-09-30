/-
# WasmCore.Duel — the wasm execution duel (the Lean half)

THE EXECUTION DUEL (notes/v3/03-bidirectional.md §3's differential
level; notes/v3/04-verification.md §6's tier honesty): a vector set of
(module-input, expected-output) rows over the slice module + the op
table's generated rows + the scenario layer + the two standing
controls. The LEAN side computes each expected output by RUNNING the
landed executor (`WasmCore.Exec.runFunc`) — the expectations are NEVER
hand-spelled; the HOST side (crates/mandate-host, the duel runner)
executes the same bytes in the real wasmtime engine and answers
agree / diverge-with-witness per row.

THE FAMILY (notes/design-wave-30.md C6 — the op table's duel rows;
07-extensibility R6's full consumption: "a row in the ONE op table —
expression eval, raw/compiled readings, emission, oracle, proof are
all folds of it". The duel row is the ORACLE fold):

- THE GENERATED ROWS (a fold over the ONE op table — `allOps`/
  `allMems`, whose completeness is proved in WatParse): per PLAIN-OP
  row, `duelOpModule` — the row's sig pushed with BOUNDARY canonical
  operands (the type maxes: the mod-semantics ops exercise their
  overflow face, the shift ops the mod-2^k count, the comparisons the
  equality edge, the conversions the wrap/extend seams — the edges the
  row's own `sem` note names), the op applied, the result adapted to
  the i64 return. Per MEM row, TWO vectors: `duelMemModule` (the load
  face reads the canonical address; the store face stores the
  canonical value and reads it back through the width-matching load —
  `memBytes`'s fold) and `duelMemTrapModule` (the canonical address
  beyond the page — the "trap if out of bounds" face the row's sem
  note names). A NEW OP = one ctor + one table row (already
  compile-forced) + one `allOps`/`allMems` entry (compile-forced by
  the completeness proofs) → its duel vector(s) appear FREE. No per-op
  hand place anywhere (R6's checklist).
- THE SCENARIO LAYER (the hand-authored multi-instruction rows the
  generator cannot derive — the honest split: per-op coverage
  generated, scenarios hand):
  `wasmSliceModule` — the committed slice (the seed row:
  `i64.const 42`); `controlModule` — the loop-restart discipline
  (locals survive the restart, the frame-entry stack does not) + the
  `if_`/`else` selection; `memoryModule` — composed memory traffic
  (two stores, both loads back, the extend + add); `trapModule` —
  `unreachable`, the typed trap in BOTH engines. (The old
  `arithModule` DIED here: every op it exercised is a generated row
  now — R6's no-parallel-places rule.)
- THE CONTROLS: `invalidModule` — the NEGATIVE CONTROL: an
  operand-type mismatch the validator refuses at generation and
  wasmtime's compiler refuses at consumption; its refusal IS its
  expectation (`.refuse`).

THE TIER HONESTY (04 §6): the duel's verdict is TESTED AGREEMENT —
`oracleSwept`, a regression surface, never a theorem over unbounded
inputs; the report's rendering says so (the host's duel runner carries
the same sentence). The verdicts are ctors (Kit.Duel.Verdict), never
strings.

THE BYTE-TIE: the vectors (each member's encoded bytes) and the
manifest ride the Kit.Emit spine — the manifest the TEXT lane
(`Kit.Duel.manifestRows`, the ONE format), the vectors the BINARY lane
(each with its `.hdr` sidecar; the host re-derives the hash tie per
vector before the engine sees a byte — a tampered vector refuses).
`regen` below is the ONE copy shared by the `wasmgen` writer and
`gates gen-check` (Slice.regen's discipline, duel-shaped); the
VALIDATOR RUNS AT GENERATION over every valid family member — an
invalid member is a generation failure, never an artifact (the invalid
control is the one deliberate exception: its refusal is its
expectation). The vector bytes CHANGED in the C6 migration (the
generated rows joined the family) — the regeneration is deliberate;
the manifest's re-tie rides the spine, never a hand edit.

The five questions (notes/v3/01-core.md):
- root: Crossing — the executor's computed outputs vs the real
  engine's, coupled through committed vectors + the shared verdict
  vocabulary (Kit.Duel).
- carrier grade: none new — the expectations are computed data; the
  honesty is the TIER (tested agreement), stated here and in the host.
- spine reading: the artifact spine — the manifest's text lane + the
  vectors' binary lane through `Kit.Emit.runEmitters`/
  `runBinaryEmitters`; `gates gen-check` byte-ties both.
- ladder rung: rung 1 — pure data + total folds; nothing here is
  proved, everything is tested (the tier note above).
- gate row: `gates gen-check`'s duel rows + `gates ownership`'s
  `duelEmitter` declaration. WasmCoreTests' duel spec pins the family's
  known answers + the coverage audit + the negative controls.
-/

import Kit.Duel
import WasmCore.Encode
import WasmCore.Profile
import WasmCore.Exec
import WasmCore.Module
import WasmCore.Slice
import WasmCore.Validate
import WasmCore.WatParse

namespace WasmCore.Duel

open WasmCore.WatParse

/-! ## The duel directory + the vector path convention -/

/-- The duel's directory (repo-root-relative — ONE directory per
    duel, Kit.Duel's convention). -/
def duelDir : String := "gen/wasm-duel"

/-- One vector's path. -/
def duelVecName (n : String) : String := duelDir ++ "/" ++ n ++ ".wasm"

/-! ## The generated per-op rows (the op table's fold — the oracle facet) -/

/-- The canonical duel operand per value type: BOUNDARY-VALUED (the
    type's max) so the mod-semantics rows (add/sub/mul, the
    wrap/extend seams) exercise their overflow face and the shift rows
    the mod-2^k shift count — the edges the rows' `sem` notes name,
    with NO per-op hand data. A non-integer type pushes nothing: no
    row in the closed table pops one, and a future one would fail the
    validator AT GENERATION (fail-loud, never a fake operand). -/
def duelOperand : ValType → List Instr
  | .i32 => [.i32const 2147483647]
  | .i64 => [.i64const 9223372036854775807]
  | .f32 => []
  | .f64 => []
  | .funcref => []
  | .externref => []

/-- The i64-return adapter over a row's push list (the duel's
    convention: every module's ONE export returns `i64` — the host
    runner's `export_i64`): an i32-pushing row's result rides the
    `i64.extend_i32_u` seam. A row whose pushes are anything else
    (none in the closed table) leaves the adapter empty — the
    validator at generation then refuses the module loudly. -/
def retI64 (pushes : List ValType) : List Instr :=
  match pushes with
  | [.i32] => [.op .i64extendi32u]
  | [.i64] => []
  | _ => []

/-- The plain-op row's canonical vector: push the sig's operands
    (REVERSE pop order — head = top, so the first pop is pushed
    last), apply the op, adapt to the i64 return. THE FOLD: derived
    from the row's `sig` alone — a new op row gets this vector FREE. -/
def duelOpModule (o : Op) : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [],
    (opPop o).reverse.flatMap duelOperand ++ [.op o] ++ retI64 (opPush o)⟩]
  exports := [{ name := "answer", desc := .func 0 }]

/-- The width-matching load (the mem row's `width` field's fold): a
    store row's vector reads its store back through the SAME width
    (1 byte → `i32.load8_u`, 8 → `i64.load`, else the 32-bit form). -/
def loadOfWidth (w : Nat) : MemOp :=
  match w with
  | 8 => .i64load
  | 1 => .i32load8u
  | _ => .i32load

/-- The mem-op row's canonical vector: a LOAD row (nonempty pushes)
    reads the canonical address; a STORE row (empty pushes — the sig's
    head pop is the VALUE, popped first; the last pop the address)
    stores the canonical value at the canonical address 16 and reads
    it back through the width-matching load. THE FOLD: derived from
    the row's `sig` + `width` alone — a new mem row gets it FREE. -/
def duelMemModule (m : MemOp) : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [],
    match memPush m with
    | [] => -- the store face: value on top, address under it
        match memPop m with
        | [] => []  -- unreachable: the validator refuses at generation
        | v :: _ =>
            let ld := loadOfWidth (memBytes m)
            [.i32const 16] ++ duelOperand v ++ [.mem m 0 none]
              ++ [.i32const 16, .mem ld 0 none] ++ retI64 (memPush ld)
    | _ => -- the load face: the address operand, then the load
        [.i32const 16, .mem m 0 none] ++ retI64 (memPush m)⟩]
  exports := [{ name := "answer", desc := .func 0 }]
  memMin := 1

/-- The mem-op row's TRAP vector: the canonical address beyond the one
    page — the "trap if out of bounds" face the row's sem note names,
    exercised in BOTH engines (the executor's bounds check and
    wasmtime's). -/
def duelMemTrapModule (m : MemOp) : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [],
    [.i32const 4294967280]
      ++ (match memPush m with
          | [] => -- the store face: the value rides on the far address
              match memPop m with
              | [] => []  -- unreachable: the validator refuses at generation
              | v :: _ => duelOperand v
          | _ => []) -- the load face: the far address alone
      ++ [.mem m 0 none]
      ++ retI64 (memPush m)
      ++ (match memPush m with | [] => [.i64const 0] | _ => [])⟩]
  exports := [{ name := "answer", desc := .func 0 }]
  memMin := 1

/-- The generated rows' vector names (the op table's rows, named). -/
def opVecName (o : Op) : String := "op-" ++ opName o
def memVecName (m : MemOp) : String := "mem-" ++ memName m
def memTrapVecName (m : MemOp) : String := "trap-mem-" ++ memName m

/-- The generated PLAIN-OP family: one canonical vector per op row —
    the fold over `allOps`. -/
def duelOpFamily : List (String × Module) :=
  allOps.map fun o => (opVecName o, duelOpModule o)

/-- The generated MEM family: one normal + one trap vector per mem
    row — the fold over `allMems`. -/
def duelMemFamily : List (String × Module) :=
  (allMems.map fun m => (memVecName m, duelMemModule m))
    ++ (allMems.map fun m => (memTrapVecName m, duelMemTrapModule m))

/-! ## The scenario layer (the hand-authored multi-instruction rows) -/

/-- The control-flow scenario: a loop counts 5..1 into an accumulator
    (locals survive the restart; the frame-ENTRY stack does not), then
    the `if_`/`else` selects on `acc = 15` → 100. Frames are
    stack-balanced (the validator's frame discipline). Hand-authored:
    the loop/if composition is the generator's non-goal. -/
def controlModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [.i32, .i64, .i32],
    [ .i32const 5, .localset 0
    , .i64const 0, .localset 1
    , .loop [ .localget 1, .localget 0, .op .i64extendi32u, .op .i64add
            , .localset 1
            , .localget 0, .i32const 1, .op .i32sub, .localset 0
            , .localget 0, .op .i32eqz, .op .i32eqz, .brif 0 ]
    , .localget 1, .i64const 15, .op .i64eq, .localset 2
    , .localget 2, .if_ [ .i64const 100, .localset 1 ]
                        [ .i64const 200, .localset 1 ]
    , .localget 1 ]⟩]
  exports := [{ name := "answer", desc := .func 0 }]

/-- The memory scenario: an `i64` and a byte stored into page 0, loaded
    back, extended, added: 0x12345678 + 255 = 305420151. Hand-authored
    COMPOSED memory traffic (the per-row store/load reads are the
    generated rows' job; this exercises the memory ACROSS ops). -/
def memoryModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [],
    [ .i32const 16, .i64const 305419896, .mem .i64store 0 none
    , .i32const 24, .i32const 255, .mem .i32store8 0 none
    , .i32const 16, .mem .i64load 0 none
    , .i32const 24, .mem .i32load8u 0 none, .op .i64extendi32u
    , .op .i64add ]⟩]
  exports := [{ name := "answer", desc := .func 0 }]
  memMin := 1

/-- The trap scenario: `unreachable` after a dead value — the typed
    trap in BOTH engines (the executor answers `.trap .unreach`,
    wasmtime traps on the call). Hand-authored: `unreachable` is not an
    op-table row (a structural instr), so the fold cannot generate it.
    The dead `i64.const` keeps the module in the validator's fragment
    (the checker's final-stack discipline: a body's exit stack must
    match the results — the stop flag does not excuse it; the honest
    declared strictness of the seed validator). -/
def trapModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [.i64const 1, .unreach]⟩]
  exports := [{ name := "answer", desc := .func 0 }]

/-- The NEGATIVE CONTROL: the operand-type mismatch (`i64.add` over an
    `i32`) — Lean's checker refuses it at generation, wasmtime's
    compiler refuses it at consumption. NOT in `duelFamily` (the
    validator-at-generation would refuse the whole regen); its
    expectation is the `.refuse` row. -/
def invalidModule : Module where
  types := [⟨[], [.i64]⟩]
  funcs := [⟨0, [], [.i32const 1, .i64const 2, .op .i64add]⟩]
  exports := [{ name := "answer", desc := .func 0 }]

/-! ## The family, the paths, and the coverage audit (the C6 audit face) -/

/-- The VALID family: the op table's GENERATED rows (plain ops, then
    mem rows — normal + trap), then the scenario layer (the seed
    slice + the hand scenarios). The ORDER IS `familyPaths`'s (the
    vectors' zip pairing depends on it). Each valid member is
    validated at generation, each expectation computed by the
    executor. -/
def duelFamily : List (String × Module) :=
  duelOpFamily ++ duelMemFamily
    ++ [("slice", wasmSliceModule), ("control", controlModule),
        ("memory", memoryModule), ("trap", trapModule)]

/-- The generated rows' vector paths (the fold's names, pathed). -/
def opVecPath (o : Op) : String := duelVecName (opVecName o)
def memVecPath (m : MemOp) : String := duelVecName (memVecName m)
def memTrapVecPath (m : MemOp) : String := duelVecName (memTrapVecName m)

/-- The scenario rows' paths (the seed + the hand scenarios; the
    invalid control lives outside the valid family). -/
def scenarioPaths : List String :=
  [duelVecName "slice", duelVecName "control", duelVecName "memory",
   duelVecName "trap"]

/-- The family's paths (generated + scenarios), then the invalid
    control last. -/
def familyPaths : List String :=
  (allOps.map opVecPath) ++ (allMems.map memVecPath)
    ++ (allMems.map memTrapVecPath) ++ scenarioPaths

/-- The duel's vector paths, row order (the family, the invalid
    control last). -/
def duelPaths : List String := familyPaths ++ [duelVecName "invalid"]

/-- THE COVERAGE AUDIT AS DATA (the C6 audit face): per-row duel
    coverage, computed off the same fold that generates the vectors.
    BEFORE the fold, 10 of 19 plain-op rows and 4 of 7 mem rows had a
    duel vector — only where a hand-authored scenario HAPPENED to
    exercise them; 9 plain ops (`i64.lt_u`, `i64.le_u`, `i64.shr_u`,
    `i32.and`, `i32.xor`, `i32.eq`, `i32.lt_u`, `i32.gt_u`,
    `i32.wrap_i64`) and 3 mem rows (`i32.load`, `i32.store`,
    `i64.store8`) had NONE. The fold makes coverage structural; the
    closed-universe pins live in WasmCoreTests (and the completeness
    proofs in WatParse are the BUILD tooth). -/
def opDuelCovered (o : Op) : Bool := duelPaths.contains (opVecPath o)

/-- The mem rows' coverage audit (same fold; a mem row's coverage is
    BOTH its vectors). -/
def memDuelCovered (m : MemOp) : Bool :=
  (memVecPath m :: memTrapVecPath m :: []).all duelPaths.contains

/-! ## The path distinctness (the one-writer discipline's proof face) -/

theorem allOps_nodup : allOps.Nodup := by decide
theorem allMems_nodup : allMems.Nodup := by decide

/-- `nodup_map`'s injective face (the list-level helper — no strings). -/
theorem nodup_map_inj {α β : Type} [DecidableEq β] (f : α → β) {l : List α}
    (h : l.Nodup) (hinj : ∀ a b, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    refine List.nodup_cons.mpr ⟨?_, ih h.tail⟩
    intro he
    obtain ⟨y, hym, hfy⟩ := List.mem_map.mp he
    have hxy : y = x := hinj y x hfy
    have hxin : x ∈ xs := hxy ▸ hym
    exact List.nodup_cons.mp h |>.1 hxin

/-- The generated paths are injective in the ctor (the names fold the
    pairwise-distinct op-table spellings; the per-pair decides are the
    closed universe's decide-level pin — `opName_inj`'s pattern). -/
theorem opVecPath_inj : ∀ a b : Op, opVecPath a = opVecPath b → a = b := by
  intro a b h
  cases a <;> cases b <;>
    simp only [opVecPath, duelVecName, duelDir] at h <;>
    first | rfl | exact absurd h (by decide)

theorem memVecPath_inj : ∀ a b : MemOp, memVecPath a = memVecPath b → a = b := by
  intro a b h
  cases a <;> cases b <;>
    simp only [memVecPath, duelVecName, duelDir] at h <;>
    first | rfl | exact absurd h (by decide)

theorem memTrapVecPath_inj : ∀ a b : MemOp, memTrapVecPath a = memTrapVecPath b → a = b := by
  intro a b h
  cases a <;> cases b <;>
    simp only [memTrapVecPath, duelVecName, duelDir] at h <;>
    first | rfl | exact absurd h (by decide)

theorem opPaths_nodup : (allOps.map opVecPath).Nodup :=
  nodup_map_inj _ allOps_nodup opVecPath_inj

theorem memPaths_nodup : (allMems.map memVecPath).Nodup :=
  nodup_map_inj _ allMems_nodup memVecPath_inj

theorem memTrapPaths_nodup : (allMems.map memTrapVecPath).Nodup :=
  nodup_map_inj _ allMems_nodup memTrapVecPath_inj

theorem scenarioPaths_nodup : scenarioPaths.Nodup := by decide

/-- The families' paths are pairwise cross-distinct (the name
    prefixes decide per ctor pair; the ground decides are the closed
    universes'). -/
theorem opMemVecPath_ne : ∀ (o : Op) (m : MemOp), opVecPath o ≠ memVecPath m := by
  intro o m h
  cases o <;> cases m <;>
    simp only [opVecPath, memVecPath, duelVecName, duelDir] at h <;>
    exact absurd h (by decide)

theorem opTrapVecPath_ne : ∀ (o : Op) (m : MemOp), opVecPath o ≠ memTrapVecPath m := by
  intro o m h
  cases o <;> cases m <;>
    simp only [opVecPath, memTrapVecPath, duelVecName, duelDir] at h <;>
    exact absurd h (by decide)

theorem memTrapVecPath_ne : ∀ (m m' : MemOp), memVecPath m ≠ memTrapVecPath m' := by
  intro m m' h
  cases m <;> cases m' <;>
    simp only [memVecPath, memTrapVecPath, duelVecName, duelDir] at h <;>
    exact absurd h (by decide)

/-- The scenario names never collide with a generated path (the four
    ground scenario paths vs the derived prefixes, per ctor pair). -/
theorem scenOpVecPath_ne : ∀ b ∈ scenarioPaths, ∀ o : Op, opVecPath o ≠ b := by
  intro b hb o h
  rcases List.mem_cons.mp hb with rfl | hb
  · cases o <;> simp only [duelVecName, duelDir, opVecPath] at h <;>
      exact absurd h (by decide)
  rcases List.mem_cons.mp hb with rfl | hb
  · cases o <;> simp only [duelVecName, duelDir, opVecPath] at h <;>
      exact absurd h (by decide)
  rcases List.mem_cons.mp hb with rfl | hb
  · cases o <;> simp only [duelVecName, duelDir, opVecPath] at h <;>
      exact absurd h (by decide)
  rcases List.mem_cons.mp hb with rfl | hb
  · cases o <;> simp only [duelVecName, duelDir, opVecPath] at h <;>
      exact absurd h (by decide)
  · exact absurd hb (by simp)

theorem scenMemVecPath_ne : ∀ b ∈ scenarioPaths, ∀ m : MemOp, memVecPath m ≠ b := by
  intro b hb m h
  rcases List.mem_cons.mp hb with rfl | hb
  · cases m <;> simp only [duelVecName, duelDir, memVecPath] at h <;>
      exact absurd h (by decide)
  rcases List.mem_cons.mp hb with rfl | hb
  · cases m <;> simp only [duelVecName, duelDir, memVecPath] at h <;>
      exact absurd h (by decide)
  rcases List.mem_cons.mp hb with rfl | hb
  · cases m <;> simp only [duelVecName, duelDir, memVecPath] at h <;>
      exact absurd h (by decide)
  rcases List.mem_cons.mp hb with rfl | hb
  · cases m <;> simp only [duelVecName, duelDir, memVecPath] at h <;>
      exact absurd h (by decide)
  · exact absurd hb (by simp)

theorem scenTrapVecPath_ne : ∀ b ∈ scenarioPaths, ∀ m : MemOp, memTrapVecPath m ≠ b := by
  intro b hb m h
  rcases List.mem_cons.mp hb with rfl | hb
  · cases m <;> simp only [duelVecName, duelDir, memTrapVecPath] at h <;>
      exact absurd h (by decide)
  rcases List.mem_cons.mp hb with rfl | hb
  · cases m <;> simp only [duelVecName, duelDir, memTrapVecPath] at h <;>
      exact absurd h (by decide)
  rcases List.mem_cons.mp hb with rfl | hb
  · cases m <;> simp only [duelVecName, duelDir, memTrapVecPath] at h <;>
      exact absurd h (by decide)
  rcases List.mem_cons.mp hb with rfl | hb
  · cases m <;> simp only [duelVecName, duelDir, memTrapVecPath] at h <;>
      exact absurd h (by decide)
  · exact absurd hb (by simp)

/-- The families' paths are pairwise cross-distinct (the name
    prefixes decide per ctor pair; the ground decides are the closed
    universes'). -/
theorem opMemPaths_disj : ∀ a ∈ allOps.map opVecPath,
    ∀ b ∈ allMems.map memVecPath, a ≠ b := by
  intro a ha b hb
  obtain ⟨o, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hb
  exact opMemVecPath_ne o m

theorem opTrapPaths_disj : ∀ a ∈ allOps.map opVecPath,
    ∀ b ∈ allMems.map memTrapVecPath, a ≠ b := by
  intro a ha b hb
  obtain ⟨o, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hb
  exact opTrapVecPath_ne o m

theorem opScenPaths_disj : ∀ a ∈ allOps.map opVecPath,
    ∀ b ∈ scenarioPaths, a ≠ b := by
  intro a ha b hb
  obtain ⟨o, _, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenOpVecPath_ne _ (by simp [scenarioPaths]) o
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenOpVecPath_ne _ (by simp [scenarioPaths]) o
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenOpVecPath_ne _ (by simp [scenarioPaths]) o
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenOpVecPath_ne _ (by simp [scenarioPaths]) o
  · exact absurd hb (by simp)

theorem memScenPaths_disj : ∀ a ∈ allMems.map memVecPath,
    ∀ b ∈ scenarioPaths, a ≠ b := by
  intro a ha b hb
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenMemVecPath_ne _ (by simp [scenarioPaths]) m
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenMemVecPath_ne _ (by simp [scenarioPaths]) m
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenMemVecPath_ne _ (by simp [scenarioPaths]) m
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenMemVecPath_ne _ (by simp [scenarioPaths]) m
  · exact absurd hb (by simp)

theorem trapScenPaths_disj : ∀ a ∈ allMems.map memTrapVecPath,
    ∀ b ∈ scenarioPaths, a ≠ b := by
  intro a ha b hb
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenTrapVecPath_ne _ (by simp [scenarioPaths]) m
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenTrapVecPath_ne _ (by simp [scenarioPaths]) m
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenTrapVecPath_ne _ (by simp [scenarioPaths]) m
  rcases List.mem_cons.mp hb with rfl | hb
  · exact scenTrapVecPath_ne _ (by simp [scenarioPaths]) m
  · exact absurd hb (by simp)

theorem opMemPaths_disj_trap : ∀ a ∈
    allOps.map opVecPath ++ allMems.map memVecPath,
    ∀ b ∈ allMems.map memTrapVecPath, a ≠ b := by
  intro a ha b hb
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hb
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨o, _, rfl⟩ := List.mem_map.mp ha
    exact opTrapVecPath_ne o m
  · obtain ⟨m', _, rfl⟩ := List.mem_map.mp ha
    exact memTrapVecPath_ne m' m

theorem combined_disj_scen : ∀ a ∈
    allOps.map opVecPath ++ allMems.map memVecPath ++ allMems.map memTrapVecPath,
    ∀ b ∈ scenarioPaths, a ≠ b := by
  intro a ha b hb
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨o, _, rfl⟩ := List.mem_map.mp ha
      exact scenOpVecPath_ne b hb o
    · obtain ⟨m, _, rfl⟩ := List.mem_map.mp ha
      exact scenMemVecPath_ne b hb m
  · obtain ⟨m, _, rfl⟩ := List.mem_map.mp ha
    exact scenTrapVecPath_ne b hb m

/-- The append-level helper (the families' Nodup assembly). -/
theorem nodup_append' {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hd : ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b) :
    (l₁ ++ l₂).Nodup :=
  List.nodup_append.mpr ⟨h₁, h₂, hd⟩

/-- `familyPaths` is `++`-LEFT-associated: `((opP ++ memP) ++ trapP) ++ scenP`. -/
theorem familyPaths_nodup : familyPaths.Nodup :=
  nodup_append'
    (nodup_append'
      (nodup_append' opPaths_nodup memPaths_nodup opMemPaths_disj)
      memTrapPaths_nodup opMemPaths_disj_trap)
    scenarioPaths_nodup combined_disj_scen

theorem scen_ne_invalid : ∀ a ∈ scenarioPaths, a ≠ duelVecName "invalid" := by
  intro a ha h
  rcases List.mem_cons.mp ha with rfl | ha
  · exact absurd h (by decide)
  rcases List.mem_cons.mp ha with rfl | ha
  · exact absurd h (by decide)
  rcases List.mem_cons.mp ha with rfl | ha
  · exact absurd h (by decide)
  rcases List.mem_cons.mp ha with rfl | ha
  · exact absurd h (by decide)
  · exact absurd ha (by simp)

theorem familyPaths_ne_invalid : ∀ a ∈ familyPaths, a ≠ duelVecName "invalid" := by
  intro a ha h
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨o, _, rfl⟩ := List.mem_map.mp ha
        cases o <;>
          simp only [opVecPath, duelVecName, duelDir] at h <;>
          exact absurd h (by decide)
      · obtain ⟨m, _, rfl⟩ := List.mem_map.mp ha
        cases m <;>
          simp only [memVecPath, duelVecName, duelDir] at h <;>
          exact absurd h (by decide)
    · obtain ⟨m, _, rfl⟩ := List.mem_map.mp ha
      cases m <;>
        simp only [memTrapVecPath, duelVecName, duelDir] at h <;>
        exact absurd h (by decide)
  · exact scen_ne_invalid a ha h

/-- THE one-writer discipline over the vector paths (the emitter's
    declared `binaryOutputs` — nodup in the type via this). -/
theorem duelPaths_nodup : duelPaths.Nodup :=
  nodup_append' familyPaths_nodup
    (List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩)
    (fun a ha b hb h => by
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact familyPaths_ne_invalid a ha h
      · exact absurd hb' (by simp))

/-! ## The executor's expected outputs (the Lean side's half of every row) -/

/-- The duel's fuel budget (the executor's honest data: exhaustion is
    a generation failure for the family — every member is finite). -/
def duelFuel : Nat := 5000

/-- The duel's value vocabulary: one rendered value (`i64:42`). The
    i64 face renders SIGNED — the boundary rows' wrap values must
    render the same on BOTH sides of the duel (the host's exported
    i64 is the signed ABI type; the unsigned rendering diverged the
    instant the generated rows pushed values past 2^63 — the duel
    caught its own vocabulary). -/
def valNote : Val → String
  | .i32 n => s!"i32:{n.toUInt64}"
  | .i64 n => s!"i64:{n.toInt64}"

/-- The result values, comma-joined (head = top — the rendered order is
    bottom-up, the return order). -/
def resultNote : List Val → String :=
  String.intercalate "," ∘ (·.map valNote)

/-- The expectation for one valid family member — the executor's
    computed output (NEVER hand-spelled). A completed run pins its
    result values; a trap pins the trap; ANY OTHER outcome is a
    GENERATION FAILURE (the family is finite and total: a `branch`/
    `unmodeled`/`outOfFuel` answer means the family member is a
    generator bug — fail loudly, never emit an expectation). -/
def duelExpect (n : String) (m : Module) : Except String Kit.Duel.Expect :=
  match runFunc m 0 [] duelFuel with
  | .ok s => .ok (.run (resultNote s.stack))
  | .trap _ => .ok .trap
  | .branch _ _ => .error s!"duel: {n} branched past the driver — a generator bug"
  | .structural => .error s!"duel: {n} answered structural — a generator bug"
  | .unmodeled => .error s!"duel: {n} answered unmodeled — a generator bug"
  | .outOfFuel => .error s!"duel: {n} exhausted {duelFuel} fuel — a generator bug"

/-- The validator AT GENERATION over every valid family member (the
    CheckedProp discipline's driver face — an invalid member is a
    generation failure carrying the validator's rendered Diag, never
    an artifact). -/
def validateFamily : Except String Unit :=
  duelFamily.foldl (fun acc (n, m) =>
    match acc with
    | .error e => .error e
    | .ok () =>
      match checkModule m with
      | .ok () => .ok ()
      | .error e => .error s!"duel: module {n} does not validate — {ValidateError.render e}")
    (.ok ())

/-- The duel's rows: path + the computed expectation, family order,
    the invalid control LAST (`.refuse` — its refusal is its
    expectation). -/
def duelRows : Except String (List (String × Kit.Duel.Expect)) := do
  let _ ← validateFamily
  let valid ← duelFamily.mapM fun (n, m) =>
    (duelVecName n, ·) <$> duelExpect n m
  .ok (valid ++ [(duelVecName "invalid", .refuse)])

/-- The shape check over the computed rows: every expectation names a
    duel vector — a manifest row over an absent vector is a generator
    bug (testable; WasmCoreTests pins it `true`, the fixture pins the
    `false`). -/
def duelRowsCovered : Bool :=
  match duelRows with
  | .ok es => es.all fun (p, _) => duelPaths.contains p
  | .error _ => false

/-- The vectors: each family member's encoded bytes + the invalid
    control's bytes (the encoder is total — the control's bytes are
    well-formed wire, the VALIDATOR is what refuses them; wasmtime's
    compiler makes the same refusal the host-side control). -/
def duelVectors : List Kit.Emit.BinaryFile :=
  (duelPaths.zip (duelFamily.map (·.2) ++ [invalidModule])).map
    fun (p, m) => { path := p, contents := ByteArray.mk (encodeModule m).toArray }

/-- The duel's item count (the manifest rows + the vectors + the
    profile file — the ledger's at-a-glance size). -/
def duelItems : Nat := duelPaths.length * 2 + 1

/-! ## The sidecar lane's distinctness (the `.hdr` tails) -/

/-- A `.wasm`-suffixed string is never a `.hdr`-suffixed one (the
    general suffix argument — a string's tail cannot be both). -/
theorem wasmPath_ne_sidecar {s t : String} : (s ++ ".wasm" : String) ≠ t ++ ".hdr" := by
  intro h
  have h' : (s ++ ".wasm").toList = (t ++ ".hdr").toList :=
    String.toList_inj.mpr h
  rw [String.toList_append, String.toList_append] at h'
  rcases List.append_eq_append_iff.mp h' with ⟨as, _, has⟩ | ⟨bs, _, hbs⟩
  · have hl := congrArg List.length has
    have w5 : (".wasm".toList : List Char).length = 5 := rfl
    have h4 : (".hdr".toList : List Char).length = 4 := rfl
    rw [w5, List.length_append, h4] at hl
    rcases as with _ | ⟨c, as⟩
    · simp at has
    · have hl2 := congrArg List.length has
      have h4 : (".hdr".toList : List Char).length = 4 := rfl
      rw [List.length_append, h4, List.length_cons] at hl2
      have h0 : as.length = 0 := by omega
      have hz : as = [] := List.length_eq_zero_iff.mp h0
      rw [hz] at has
      simp at has
  · have hl := congrArg List.length hbs
    have h4 : (".hdr".toList : List Char).length = 4 := rfl
    have w5 : (".wasm".toList : List Char).length = 5 := rfl
    rw [h4, List.length_append, w5] at hl
    omega

/-- Every duel path ends `.wasm` (the family's + the control's shape). -/
theorem duelPath_suffix : ∀ a ∈ duelPaths, ∃ s, a = s ++ ".wasm" := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨o, _, rfl⟩ := List.mem_map.mp ha
          exact ⟨duelDir ++ "/" ++ ("op-" ++ opName o), rfl⟩
        · obtain ⟨m, _, rfl⟩ := List.mem_map.mp ha
          exact ⟨duelDir ++ "/" ++ ("mem-" ++ memName m), rfl⟩
      · obtain ⟨m, _, rfl⟩ := List.mem_map.mp ha
        exact ⟨duelDir ++ "/" ++ ("trap-mem-" ++ memName m), rfl⟩
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨duelDir ++ "/" ++ "slice", rfl⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨duelDir ++ "/" ++ "control", rfl⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨duelDir ++ "/" ++ "memory", rfl⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨duelDir ++ "/" ++ "trap", rfl⟩
      · exact absurd ha (by simp)
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨duelDir ++ "/" ++ "invalid", rfl⟩
    · exact absurd ha (by simp)

theorem sidecarPath_inj {a b : String} (h : Kit.Emit.sidecarPath a = Kit.Emit.sidecarPath b) :
    a = b := by
  apply String.toList_injective
  have h' : (Kit.Emit.sidecarPath a).toList = (Kit.Emit.sidecarPath b).toList := by rw [h]
  rw [Kit.Emit.sidecarPath, Kit.Emit.sidecarPath, String.toList_append,
      String.toList_append] at h'
  exact List.append_cancel_right h'

theorem duelPath_sidecar_disj : ∀ a ∈ duelPaths,
    ∀ b ∈ duelPaths.map Kit.Emit.sidecarPath, a ≠ b := by
  intro a ha b hb
  obtain ⟨s, hs⟩ := duelPath_suffix a ha
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
  intro h
  rw [hs] at h
  exact wasmPath_ne_sidecar h

/-- The emitter's declared binary surface: the vectors AND their
    sidecars — nodup through the same machinery as `duelPaths_nodup`. -/
theorem duelBinOutputs_nodup :
    (duelPaths ++ duelPaths.map Kit.Emit.sidecarPath).Nodup :=
  nodup_append' duelPaths_nodup
    (nodup_map_inj _ duelPaths_nodup (fun _a _b h => sidecarPath_inj h))
    duelPath_sidecar_disj

/-! ## The profile artifact (D1's profile-as-data, the engines' shared config) -/

/-- The deterministic profile's artifact path (INSIDE the duel
directory — the profile is the duel lane's config source; the Rust
engines — mandate-host's wasmtime applier and mandate-rt's wasmi
applier — parse THIS file, never a hand-synced config). -/
def profilePath : String := duelDir ++ "/profile.txt"

/-- The profile's file (the ONE rendering — `Profile.fileBody`; the
driver prepends the GENERATED header). -/
def profileFile : Kit.Emit.GeneratedFile where
  path := profilePath
  contents := WasmCore.Profile.fileBody

/-! ## The emitter row (the artifact spine) -/

/-- The duel's emitter: the manifest the TEXT lane
    (`Kit.Duel.manifestRows` — the ONE format, the VectorSet face
    bypassed because the expectations are computed), the vectors the
    BINARY lane. The spec is the computed expectation list — the
    writer and the gate obtain it from `duelRows` (the ONE copy; a
    generation failure writes nothing). -/
def duelEmitter : Kit.Emit.Emitter (List (String × Kit.Duel.Expect)) where
  name := "duel:wasm-exec"
  style := .hash
  specSource := "WasmCore.Duel"
  outputs := [duelDir ++ "/manifest.txt", profilePath]
  -- The vectors AND their sidecars (the binary driver writes one
  -- `.hdr` per byte file — the declaration covers BOTH writes, the
  -- ownership gate's one-writer surface; the slice emitter's
  -- precedent).
  binaryOutputs := duelPaths ++ duelPaths.map Kit.Emit.sidecarPath
  binaryOutputs_nodup := duelBinOutputs_nodup
  run expects :=
    [{ path := duelDir ++ "/manifest.txt"
     , contents := Kit.Duel.manifestRows "WasmCore.Duel" expects }
    , profileFile]
  runBinary := some fun _ => duelVectors
  -- r2: the C6 migration — the op table's generated rows joined the
  -- family; the vector bytes changed deliberately.
  -- r3: D1 — the deterministic profile joined the lane's text outputs
  -- (the engines' shared config source; the manifest + vectors
  -- unchanged).
  rev := "wasm-duel-r3"
  reads := [`WasmCore.OpTable, `WasmCore.WatParse]

/-! ## THE regen — the writer's and the gate's ONE copy -/

/-- The regen both the `wasmgen` writer and `gates gen-check` run
    (Slice.regen's discipline, duel-shaped): the validator runs at
    generation, the expectations are the executor's computed outputs,
    and a generation failure produces NOTHING. -/
def regen : Except String (List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile) := do
  let expects ← duelRows
  .ok (duelEmitter.run expects, duelVectors)

end WasmCore.Duel
