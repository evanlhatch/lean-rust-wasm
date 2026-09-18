import Lean
import WasmBackend
import WasmBackend.Check
import WasmBackend.Audit
import Oracle
import TestKit
import Tests.Audit

/-!
# WasmBackend tests — the `@[guest]` gate's pure predicate

Positive + negative controls: the rejection path is OBSERVED, not
assumed. `checkExpr` is pure — no elaboration needed to test it.
Leaves are `.bvar 0` (a de Bruijn leaf — no constant-lookup coupling).
-/

-- The gate MOVED to CodegenCore.GuestGate; WasmBackend.Check re-exports
-- the surface as ROOT aliases (`export`), so no `open` for it — an
-- `open WasmBackend.Check` poisoned the whole open command (unknown
-- namespace) and took `open Lean`'s `mkApp2` down with it.
open Lean CodegenCore.GuestGate

def leaf : Expr := .bvar 0

-- Positive control: clean scalar code → no violations.
#guard (checkExpr (Expr.const ``UInt64 [])) == []

-- Negative control: the app of a banned const (Nat.add) → surfaces.
#guard (checkExpr (mkApp2 (.const ``Nat.add []) leaf leaf)) == ["Nat"]

-- String root → the violation.
#guard (checkExpr (.const ``String.length [])) == ["String"]

-- IO root → the violation.
#guard (checkExpr (.const ``IO.println [])) == ["IO"]

-- Dedup: two Nat uses → ONE violation (deduped by root).
#guard ((checkExpr (mkApp2 (.const ``Nat.add []) leaf leaf)).count "Nat") == 1

-- Mixed: Nat + IO → both, in scan order.
#guard (checkExpr (mkApp2 (.const ``IO.println []) (.const ``Nat.add []) leaf)) == ["Nat", "IO"]

-- Non-banned consts: clean.
#guard (checkExpr (mkApp2 (.const ``UInt64.add []) leaf leaf)) == []

-- The rejection path is OBSERVED: a banned root can't slip through —
-- every `@[guest]` def's failure mode is a listed violation (the elab
-- error renders `reasons`), and the backend's `unsupported` throw backs
-- the scan up for LCNF-only shapes.

-- The STD surface: match-only Nat is LEGAL (a Nat.zero/succ app is
-- ctor-shaped — the backend handles it via cases); arithmetic stays banned.
#guard (checkExprAt .std (mkApp2 (.const ``Nat.succ []) leaf leaf)) == []
#guard (checkExprAt .std (mkApp2 (.const ``Nat.add []) leaf leaf)) == ["Nat"]
#guard (checkExprAt .std (.const ``String.length [])) == []
#guard (checkExprAt .std (.const ``IO.println [])) == ["IO"]
-- The STRICT surface still bans everything the std surface allows.
#guard (checkExprAt .strict (mkApp2 (.const ``Nat.succ []) leaf leaf)) == ["Nat"]
#guard (checkExprAt .strict (.const ``String.length [])) == ["String"]

-- Bug 0.5: `reasons` renders at the attribute's OWN ban level. A
-- std-level Nat violation is ARITHMETIC (match-only Nat is std-legal),
-- so the std error must not show the strict bignum reason.
#guard (reasons .strict ["Nat"]) ==
  "- `Nat` — Nat is bignum (GMP) — the guest has fixed-width integers only (use UInt64/Int64)"
#guard (reasons .std ["Nat"]) ==
  "- `Nat` — Nat arithmetic is GMP — std code may only MATCH on Nat (zero/succ patterns)"
-- IO is banned at BOTH levels; the std render keeps the host-capability reason.
#guard (reasons .std ["IO"]) ==
  "- `IO` — IO is a host capability — guest functions must be pure over guestlang-std's WASI layer"

/-! ## The differential oracle's corruption-negative gate (DiffSpec)

The differential gate (steel-host's wasm_diff) replays the oracle manifest
against the component; its sabotage control is Rust-side (flipped
instruction). The LEAN side now proves its own half: the oracle row
universe REJECTS a sabotaged row, naming context. -/

open TestKit

/-- The positive case: every manifest row resolves (no unknown fn, no
    arity drift between `rows` and `resultOf`). -/
def oracleRowsResolve (rs : List (String × List String)) : CheckResult :=
  allOf (rs.map fun (fn, args) =>
    (s!"row {fn} {args}", match resolve fn args with
      | .ok _ => .ok ()
      | .error e => .error e))

/-- The gate: positive fold + two engineered corruptions, each pinned to
    its context. A corruption that passes (or rejects context-free) is a
    gate failure. -/
def oracleDiffSpec : DiffSpec := ⟨"oracle rejects sabotaged rows",
  oracleRowsResolve rows,
  [ corrupt "unknown fn" (fun rs => ("doble", ["3"]) :: rs) rows oracleRowsResolve
      ["unknown fn", "doble"]
  , corrupt "arity sabotage" (fun rs => ("double", ["3", "4"]) :: rs) rows oracleRowsResolve
      ["'double' expects 1 args", "got 2"] ]⟩

/-! ## W6.3: error-equivalence modes + identity-driven rejection

`resolveOutcome` carries the error IDENTITY (an `ErrorId` ctor) separate
from the payload; `CompareMode.compare` is the truth table the Rust
replay mirrors arm-for-arm. The pins: identity never reads payloads,
full reads everything, ignore waives errors. -/

-- Test fixtures: two value outcomes + the two resolution-error
-- identities (eA1/eA2 share `arityDrift` with DIFFERENT payloads).
def vA : Outcome := { error := none, payload := "42" }
def vB : Outcome := { error := none, payload := "43" }
def eU : Outcome := resolveOutcome "doble" ["3"]        -- unknownFn
def eA1 : Outcome := resolveOutcome "double" ["3", "4"] -- arityDrift
def eA2 : Outcome := resolveOutcome "total" ["1"]       -- arityDrift, other payload

-- FULL: today's behavior — values byte-compare; errors need identity
-- AND payload; a kind mismatch fails.
#guard CompareMode.compare .full vA vA
#guard !CompareMode.compare .full vA vB
#guard !CompareMode.compare .full eA1 eA2  -- same identity, payload differs
#guard !CompareMode.compare .full eU eA1   -- identity differs
#guard !CompareMode.compare .full vA eU    -- kind mismatch

-- IDENTITY: error ctors compare; payloads (error OR value) never read.
#guard CompareMode.compare .identity eA1 eA2
#guard !CompareMode.compare .identity eU eA1
#guard CompareMode.compare .identity vA vB
#guard !CompareMode.compare .identity vA eU

-- IGNORE: an error on either side waives; values still byte-compare.
#guard CompareMode.compare .ignore eU vA
#guard CompareMode.compare .ignore vA eA1
#guard CompareMode.compare .ignore eU eA1
#guard CompareMode.compare .ignore vA vA
#guard !CompareMode.compare .ignore vA vB

-- `resolve` keeps its byte-exact string surface through the
-- `resolveOutcome` reroute (the original DiffSpec's pins still bite).
#guard resolve "doble" ["3"] == .error "oracle row: unknown fn 'doble'"
#guard resolve "double" ["3", "4"] == .error "oracle row: 'double' expects 1 args, got 2"
#guard resolve "double" ["3"] == .ok "6"

-- Every row in today's universe binds `.full` (no error rows on the
-- wire yet — phase 2 makes `modeOf` a real column).
#guard rowUniverse.all (fun (fn, _) => modeOf fn == .full)

/-! ## W6.3 phase 2: verdicts (first-divergence) + schema surface + coverage

`CompareMode.verdict` answers the same truth table as `compare` but a
FAIL carries the first-divergence witness (both outcomes, the CLASS as
a ctor, the first payload offset). `schemaSigs` is the signature table
`arityOf` now looks up; the coverage discipline: every export has ≥1
feature AND ≥1 manifest row. -/

-- arityOf's table-lookup refactor is behavior-identical to the
-- phase-1 pattern match (every arity + the unknown case pinned).
#guard arityOf "double" == some 1
#guard arityOf "order-error-valid" == some 2
#guard arityOf "total" == some 3
#guard arityOf "user-valid" == some 4
#guard arityOf "watch-users" == some 1
#guard arityOf "doble" == none
#guard schemaSigs.length == 16  -- W9.6: + verify-witness (the witness export)
#guard schemaSigs.eraseDups.length == schemaSigs.length

-- VERDICT truth arms: pass → no divergence; fail → the class names
-- the divergence KIND (a ctor), never a string.
#guard (CompareMode.verdict .full vA vA).divergence == none
#guard (CompareMode.verdict .full vA vB).divergence.map (·.category) == some .valueMismatch
#guard (CompareMode.verdict .full vA eU).divergence.map (·.category) == some .expectedValueGotError
#guard (CompareMode.verdict .full eU vA).divergence.map (·.category) == some .expectedErrorGotValue
#guard (CompareMode.verdict .full eU eA1).divergence.map (·.category) == some .errorIdentityMismatch
#guard (CompareMode.verdict .full eA1 eA2).divergence.map (·.category) == some .errorPayloadMismatch
-- IDENTITY mode: payloads never read — vA vs vB passes; the error
-- arms classify by identity only.
#guard (CompareMode.verdict .identity vA vB).divergence == none
#guard (CompareMode.verdict .identity eA1 eA2).divergence == none
#guard (CompareMode.verdict .identity eU eA1).divergence.map (·.category) == some .errorIdentityMismatch
-- IGNORE mode: errors waive — the only reachable failure class is
-- valueMismatch.
#guard (CompareMode.verdict .ignore eU vA).divergence == none
#guard (CompareMode.verdict .ignore vA vB).divergence.map (·.category) == some .valueMismatch

-- The witness carries BOTH outcomes + the first payload offset.
#guard (CompareMode.verdict .full vA vB).divergence.map (·.payloadDiffAt) == some (some 1)
#guard (CompareMode.verdict .full eU eA1).divergence.map (·.payloadDiffAt) == some (some 12)
  -- ^ error-identity divergence: the witness still locates the payloads'
  --   first differing char (the common "oracle row: " prefix is 12 chars)
#guard firstDiffAt "abc".toList "abd".toList 0 == some 2
#guard firstDiffAt "abc".toList "abc".toList 0 == none
#guard firstDiffAt "abc".toList "ab".toList 0 == some 2

-- The verdict JSON names the class + echoes the schema surface (the
-- schema hash's preimage — Lean owns the string, consumers sha256 it).
#guard jsonVerdict (CompareMode.verdict .full vA vB) ==
  "{\"ok\": false, \"category\": \"valueMismatch\", \"expected\": {\"error\": null, \"payload\": \"42\"}, \"observed\": {\"error\": null, \"payload\": \"43\"}, \"payload_diff_at\": 1, \"schema\": \"" ++ schemaSurface ++ "\"}"
#guard jsonVerdict ⟨none⟩ ==
  "{\"ok\": true, \"schema\": \"" ++ schemaSurface ++ "\"}"

-- The schema surface is canonical: fn/arity, comma-joined, WIT order.
#guard schemaSurface.takeWhile (· != ',') == "double/1"
#guard (schemaSurface.splitOn ",").length == 16  -- W9.6: + verify-witness

-- THE COVERAGE DISCIPLINE (verified-ledger: every feature row has a
-- test): every export has ≥1 feature AND ≥1 manifest row; every row's
-- fn is a known export.
#guard schemaSigs.all (fun (f, _) => !(featuresOf f).isEmpty)
#guard schemaSigs.all (fun (f, _) => rowUniverse.any (fun (g, _) => g == f))
#guard rowUniverse.all (fun (f, _) => (arityOf f).isSome)
-- The batch table covers the whole universe (counts sum).
#guard (batchTable.map (·.2.1)).foldl (· + ·) 0 == rowUniverse.length

/-- Identity-driven rejection: the check reads the structured error
    identity and the message DERIVES from the ctor — the corruption
    pins name the ctor, not a free-form payload substring. -/
def oracleRowsIdentities (rs : List Probe) : CheckResult :=
  allOf (rs.map fun (fn, args) =>
    (s!"row {fn} {args}", match (resolveOutcome fn args).error with
      | none => .ok ()
      | some id => .error s!"row '{fn}' rejected: {id}"))

/-- The identity DiffSpec: same sabotage rows as `oracleDiffSpec`,
    pinned by error IDENTITY. -/
def oracleIdentitySpec : DiffSpec := ⟨"oracle rejects sabotaged rows by error identity",
  oracleRowsIdentities rows,
  [ corrupt "unknown fn" (fun rs => ("doble", ["3"]) :: rs) rows oracleRowsIdentities
      ["unknownFn", "doble"]
  , corrupt "arity sabotage" (fun rs => ("double", ["3", "4"]) :: rs) rows oracleRowsIdentities
      ["arityDrift", "double"] ]⟩

open Plausible
open Plausible.Gen
open WasmBackend.Wat

/-! ## WAT printer property sweep (PropSpec) — pinning invariants on the renderer

Generator: small modules (1 func + export + memory) with depth-bounded
structural instructions. NO `raw` items (the raw-free invariant is a real
pin: if the escape hatch is NEVER used, the emitter text is fully typed).

Invariants:
1. Determinism: same module → same rendered bytes (a pure-function pin).
2. Parenthesis balance: every rendered WAT form has a balanced paren count
   (no parser-fatal structural errors from the renderer).
-/

/-- Count occurrences of character `c` in string `s`. -/
def countChar (c : Char) (s : String) : Nat :=
  (s.toList.filter (· == c)).length

/-- WAT module wrapper for Plausible generation. -/
structure WatModule where
  m : WasmBackend.Wat.Module

instance : Repr WatModule where
  reprPrec wm _ := s!"WatModule #{wm.m.items.length} items"

instance : Shrinkable WatModule where
  shrink _ := []

/-- A flat (non-structural) instruction generator — never block/loop/if_. -/
def genFlatInstr : Gen Instr :=
  -- `frequency fallback alternatives`: pick from weighted list, fallback on drop
  Gen.frequency (pure Instr.drop) [
    (3, do let n ← Gen.resize (fun _ => 255) Gen.chooseNat; pure (Instr.i32const n)),
    (2, do let n ← Gen.resize (fun _ => 255) Gen.chooseNat; pure (Instr.i64const n)),
    (2, pure (Instr.localget "x")),
    (2, pure (Instr.localset "x")),
    (1, pure (Instr.call "f")),
    (1, Instr.op <$> (Gen.oneOf #[pure Op.i32add, pure Op.i64add, pure Op.i32sub,
      pure Op.i64sub, pure Op.i32mul, pure Op.i64mul, pure Op.i64eq, pure Op.i64ltu]))
  ]

/-- Structural instruction: block/loop/if_ with recursively generated body. -/
def genStructuralInstr (bodyGen : Gen (List Instr)) : Gen Instr :=
  Gen.frequency (pure Instr.drop) [
    (3, Instr.block "b" <$> bodyGen),
    (3, Instr.loop "l" <$> bodyGen),
    (2, pure (Instr.if_ none [] [])),
    (2, do
      let thenI ← bodyGen
      let elseI ← bodyGen
      pure (Instr.if_ none thenI elseI))
  ]

/-- Generate a list of instructions with bounded depth for structural forms. -/
partial def genInstrs (depth : Nat) : Gen (List Instr) := do
  let len ← Gen.resize (fun _ => 5) Gen.chooseNat
  let mut xs : List Instr := []
  for _ in [0:len] do
    if depth == 0 then
      xs := (← genFlatInstr) :: xs
    else
      xs := (← Gen.frequency genFlatInstr
        [(7, genFlatInstr), (3, genStructuralInstr (genInstrs (depth-1)))]) :: xs
  pure xs.reverse

/-- A function with a depth-bounded body. -/
def genWatFunc : Gen Func := do
  let name ← Gen.oneOf #[pure "f0", pure "f1", pure "test"]
  let body ← genInstrs 3
  pure { name := name
       , params := [{ name := some "x", ty := "i64" }]
       , result := some "i64"
       , locals := []
       , body := body ++ [Instr.unreach] }

instance : Arbitrary WatModule where
  arbitrary := do
    let f ← genWatFunc
    let modName := f.name
    pure { m := { items :=
      [WasmBackend.Wat.Item.func f,
       WasmBackend.Wat.Item.export { name := modName, desc := .func modName },
       WasmBackend.Wat.Item.memory 1] } }

/-- Positive property: determinism (same input = same output) + paren balance. -/
def watPropTest : TestSeq :=
  checkPlausibleIO "WAT printer invariants"
    (∀ (wm : WatModule),
      let s := wm.m.render
      s == wm.m.render ∧
      countChar '(' s == countChar ')' s)
    .done { numInst := 200, randomSeed := some 42 }

/-- Sabotaged negative control: "left paren count equals right paren count + 1" —
    FALSE (the counts are equal, every time). The sampler MUST catch this. -/
def watControl : TestSeq :=
  checkPlausibleIO "sabotage: left parens == right parens + 1 (must be caught)"
    (∀ (wm : WatModule),
      let s := wm.m.render
      countChar '(' s == countChar ')' s + 1)
    .done { numInst := 200, randomSeed := some 42 }

/-- The PropSpec: property passes, control is caught. -/
def watPropSpec : TestKit.PropSpec :=
  { name := "WAT printer property sweep"
  , suite := watPropTest
  , control := watControl
  , controlName := "parens counting left==right+1 (must be caught)" }

-- #guard-driven (elab-time) for the `@[guest]` predicate; the exe entry
-- point runs the oracle DiffSpec (plus its own vacuous-control demo), and
-- the WAT printer PropSpec.
def main : IO UInt32 := do
  let code ← runDiffs [oracleDiffSpec, oracleIdentitySpec]
  if code != 0 then return code
  -- Negative control for the control: an identity "corruption" must be
  -- flagged (proves the runner can't go vacuously green here either).
  let (vacOk, vacVerdict) := (⟨"identity control",
      oracleRowsResolve rows,
      [corrupt "identity sabotage" id rows oracleRowsResolve]⟩ : DiffSpec).run
  IO.println vacVerdict
  if vacOk then
    IO.eprintln "FAIL: identity corruption not flagged"
    return 1
  -- WAT printer PropSpec
  let propCode ← TestKit.runSpecs [watPropSpec]
  if propCode != 0 then
    IO.eprintln "FAIL: WAT printer sweep failed"
    return propCode
  return 0