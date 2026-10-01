/-
# ComponentTests.WitFixture — the witness CHECKER's component face

The component lane's FIFTH fixture: the host-gating lane (the D6 named
follow-up). The legacy discipline: the host calls the guest-compiled
witness CHECKER to GATE processing — a proposed row + its certificate
cross into the guest's compiled checker, and the checker's verdict
gates the host's commit. The Lean side landed
(`SchemaCore.Witness`'s fuel-bounded `checkWitness` + its soundness;
`SchemaCore.WitnessGen`'s producer); THIS fixture is the HOST face:
the checker as a component export through the SAME emission the other
four lanes ride.

THE HONEST MINIMAL (the string/fault fixtures' precedent, one lane
over): `checkWitness` walks `RowVals fs` — a GADT indexed by the field
list — and `Guest.Lower`'s object model carries no dependent-index
objects (`SchemaCore.Witness`'s header names the refusal class). So
the component does not lower the GENERAL checker; it deploys the
checker at the INVARIANT's pinned shape — which is what an invariant
IS (the legacy `@[invariant]` validators are deployed code, not data).
The pinned claim (the transfer invariant: `amount > 0` and
`src ≠ dst`) rides `SchemaCore.Pred` verbatim — the spec of record,
re-used, never a parallel claim table.

THE WIRE (the certificate's flat slot face): the certificate crosses
as FIVE u64 slots — the proof term's SHAPE tags + the recorded
verdicts, at the producer's certificate shape. The tags are `WProof`'s
ctor tags in declaration order (the codec's discipline: verdict 0,
conj 1, disj 2, neg 3), so a certificate for another claim (another
schema's shape) carries different tags and REFUSES (the wrong-schema
tooth); a tampered record carries the right tags with a disagreed
verdict and REFUSES (the tamper tooth — the checker RE-FIRES every
check, verifying, not trusting). `witSlots` is the encoder; a proof
term outside the producer's certificate shape has NO encoding (`none`)
— the wrong-schema refusal at the wire. STRICTNESS, honestly named:
the landed checker's verdict arm accepts MORE terms than the producer's
shape (a bare `.verdict true` over a true claim also certifies —
soundly); the wire face deploys the PRODUCER's certificate shape, so
the component's acceptance is a SUBSET of `checkWitness`'s — a
stricter gate, which never admits what the theorem-backed checker
refuses (the sound direction is the one that matters at the boundary).

THE FAULT CHANNEL (the D6 port's typed face, the fault lane's ABI):
`witness-gate : func(src, dst, amount, t1, b1, t2, t3, b3: u64) ->
result<_, u64>` — the flattening collapses past `MAX_FLAT_RESULTS`
(the heap-return face, `Guest.Component.flatten`), and the module
writes the return area: `Ok` (accept — the gate opens) or `Err(code)`:
1 = the claim is FALSE at the proposed row (no honest certificate
exists), 2 = TAMPERED record (a recorded verdict disagrees with the
recomputed check), 3 = WRONG-SCHEMA certificate (the shape tags do not
fit the deployed invariant's certificate shape). The code table is
data HERE (the Lean SSOT) and mirrored as constants in the host
(`mandate-host`'s witness lane); the teeth pin both faces at the same
literals. A TRAP is not a refusal — the host pins the two faces apart
(the D6 trap/fault distinction).

THE PARITY DISCIPLINE (the edge lane's shape, two legs here): the Lean
EXECUTOR (`WasmCore.runFunc` over THIS fixture's module — the same
module the component embeds) answers the pinned codes, and the
wasmtime face (the host's typed calls over the COMMITTED component)
answers the same literals; the byte-tie ties the committed component
to this module, closing the circle.

THE HONEST BOUNDARY (04 §7's portable-verifier honesty, named): the
guest-compiled checker's AGREEMENT with `checkWitness` is pinned at
these points (tested parity + the Lean teeth tying the SAME witness
through `Witness.checks`), not PROVED — no compiled-body
correspondence theorem exists, and this lane does not claim one. The
checker's IDENTITY is pinned the artifact way: the committed component
(the byte-tie + the GENERATED header + the sidecar's hash tie) is the
only thing the host runs; a substituted component is a fresh
regeneration, never a silent swap. What acceptance proves: the
certificate fits the deployed invariant's certificate shape and every
recorded verdict agrees with the recomputed checks at the proposed row
— by `checkWitness_sound` (Lean side: the certificate's acceptance
implies `invPred.Sat row`) and by the parity pins (component side);
what it does NOT prove: the general checker for every claim — the
GADT walk stays Lean-side until the object model carries rows.

The five questions (notes/v3/01-core.md): the fixture is data (the
test lane's Universe face) — the answers live at the consumers
(`Guest.Component.check`/`encodeComponent`, the host's witness gate).
-/

import Guest.Component
import Wit
import Wit.World
import WasmCore.Exec
import WasmCore.Instr
import WasmCore.Module
import WasmCore.Types
import SchemaCore.Witness
import SchemaCore.WitnessGen
import TestingKit.Spec

open WasmCore
open SchemaCore

namespace ComponentTests.WitFixture

/-! ## The deployed invariant (the Lean SSOT's claim) -/

/-- THE PINNED FIELD LIST: the transfer row's three u64 columns (the
    ledger fixture's tid/src/dst/amount face — the invariant reads
    src/dst/amount). -/
def witFields : List Field :=
  [{ name := "src", ty := .u64 }
  , { name := "dst", ty := .u64 }
  , { name := "amount", ty := .u64 }]

/-- THE DEPLOYED INVARIANT (the legacy `@[invariant]`'s shape, as
    data): a transfer's amount is positive and its endpoints differ.
    The check lane's OWN fragment — the spec of record is
    `invPred.Sat`, the decidable checker `invPred.check`, the proved
    bridge `Pred.check_iff`. -/
def invPred : Pred witFields :=
  .and (.u64GtLit "amount" 0) (.not (.u64Eq "src" "dst"))

/-- The proposed row (the GADT carrier the Lean checker walks). -/
def invRow (src dst amount : UInt64) : RowVals witFields :=
  .cons (.u64 src) (.cons (.u64 dst) (.cons (.u64 amount) .nil))

/-! ## The wire (the certificate's flat slot face) -/

/-- A recorded verdict's slot value (Bool as the 0/1 wire — the
    upstream `Bool.toUInt64`'s spelling, not a copy). -/
def WProof.slotOf (b : Bool) : UInt64 := Bool.toUInt64 b

/-- THE WIRE ENCODER at the producer's certificate shape: the proof
    term's flat u64 slots — the shape tags (declaration order: conj 1,
    neg 3, verdict 0) + the recorded verdicts. `none` = the term does
    not fit the deployed invariant's certificate shape — NO wire
    exists (the wrong-schema refusal, code 3 at the checker). -/
def witSlots : WProof → Option (List UInt64)
  | .conj (.verdict b1) (.neg (.verdict b3)) =>
      some [1, WProof.slotOf b1, 3, 0, WProof.slotOf b3]
  | _ => none

/-- THE REFUSAL CODES (the SSOT — the host mirrors these as
    constants): the checker's `Err` payload over the D6 fault
    channel. -/
def WIT_CODE_CLAIM_FALSE : UInt64 := 1
def WIT_CODE_TAMPERED : UInt64 := 2
def WIT_CODE_WRONG_SCHEMA : UInt64 := 3

/-! ## The Lean legs (the landed checker's teeth, at this fixture) -/

/-- The PRODUCER's certificate for the proposed row (the untrusted
    producer's face — `WitnessGen.proofFor`, self-checked at the
    pinned fuel by construction). -/
def invWitnessOf (src dst amount : UInt64) : Option (Witness witFields) :=
  match WitnessGen.proofFor invPred (invRow src dst amount) with
  | some pr =>
      some { label := "transfer-invariant", claim := invPred
           , proof := pr, fuel := WitnessGen.fuelPinned invPred }
  | none => none

/-- The producer's certificate's wire (the slots the host ships). -/
def invWireOf (src dst amount : UInt64) : Option (List UInt64) :=
  (invWitnessOf src dst amount).bind (fun w => witSlots w.proof)

/-- The producer's certificate's proof term (the wire encoder's
    input). -/
def invProofOf (src dst amount : UInt64) : Option WProof :=
  (invWitnessOf src dst amount).map (·.proof)

/-! ## The component face (the module + the world it must match) -/

/-- THE CHECKER's world: `witness-gate : func(...) -> result<_, u64>`
    — the row's three u64 slots + the certificate's five wire slots in,
    the D6 fault channel's typed verdict out (the heap-return face:
    `[i32 disc, i64 payload]` collapses past `MAX_FLAT_RESULTS`). -/
def witGateWorld : Wit.World :=
  { name := "guest"
  , imports := []
  , exports :=
      [.func { name := "witness-gate"
             , params :=
                 [{ name := "src", ty := .atom .u64 }
                 , { name := "dst", ty := .atom .u64 }
                 , { name := "amount", ty := .atom .u64 }
                 , { name := "t1", ty := .atom .u64 }
                 , { name := "b1", ty := .atom .u64 }
                 , { name := "t2", ty := .atom .u64 }
                 , { name := "t3", ty := .atom .u64 }
                 , { name := "b3", ty := .atom .u64 }]
             , result := some (.resultErr (.atom .u64)) }] }

/-- THE CHECKER's core module: the adapter face (the exported one-page
    memory + the ABI realloc stub) + the `witness-gate` core func —
    8 × i64 → i32, the heap-return pointer. The body is the PINNED
    checker's verdict over the re-fired checks (nested `if_`s — the
    fault fixture's ABI face, no `select`: the spec's operand order is
    the pinned convention, and the frames are stack-neutral): shape
    guards first (wrong tags, a non-`false` refutation record, or a
    non-Bool record → 3), then the claim's own checks (false → 1),
    then the tamper comparison (the record disagrees with the
    recomputed verdict → 2), else accept (0). EVERY check is RE-FIRED
    here — the recorded verdicts are verified, never trusted (the
    `checkWitness` calculus' arms, verbatim at the pinned shape). -/
def witGateModule : WasmCore.Module :=
  { types := [⟨[.i32, .i32, .i32, .i32], [.i32]⟩   -- the ABI realloc
            , ⟨[.i64, .i64, .i64, .i64, .i64, .i64, .i64, .i64], [.i32]⟩]
  , funcs := [ { tyIdx := 0, locals := [], body := [.i32const 1024] }
             , { tyIdx := 1
               , locals := [.i32, .i32]   -- ptr, code
               , body :=
                   -- ptr = realloc(0, 0, 0, 0)
                   [.i32const 0, .i32const 0, .i32const 0, .i32const 0
                   , .call 0, .localset 8
                   -- code = shape_bad ? 3 : claim_inv ? 1 : tamper ? 2 : 0
                   -- (the nested `if_`s route on the RE-FIRED checks —
                   -- the shape guards OUTRANK the claim verdict; the
                   -- tamper tooth fires only on a shape-fitting
                   -- certificate. The frames are stack-neutral (the
                   -- validator's frame rule): the code lands in local 9.)
                   , .i32const 0, .localset 9
                   -- shape_bad: the five guard flags AND-combine
                   -- pairwise (4 `and`s: term, then `and` between terms
                   -- only), then the refusal routing
                   , .i64const 1, .localget 3, .op .i64eq
                   , .i64const 3, .localget 5, .op .i64eq, .op .i32and
                   , .localget 6, .i64const 0, .op .i64eq, .op .i32and
                   , .localget 7, .i64const 0, .op .i64eq, .op .i32and
                   , .localget 4, .i64const 1, .op .i64leu, .op .i32and
                   , .op .i32eqz
                   , .if_ [ .i32const 3, .localset 9 ]
                          [ .localget 2, .i64const 0, .op .i64eq, .op .i32eqz
                          , .localget 0, .localget 1, .op .i64eq, .op .i32eqz
                          , .op .i32mul, .op .i32eqz
                          , .if_ [ .i32const 1, .localset 9 ]
                                 [ .localget 4, .i64const 0, .op .i64eq
                                 , .if_ [ .i32const 2, .localset 9 ]
                                        [ .i32const 0, .localset 9 ] ] ]
                   -- the return area: [ptr+8] = code (the payload slot),
                   -- [ptr] = the discriminant (1 iff code ≠ 0)
                   , .localget 8, .localget 9, .op .i64extendi32u
                   , .mem .i64store 8 (some 3)
                   , .localget 8, .localget 9, .op .i32eqz, .op .i32eqz
                   , .mem .i32store 0 (some 2)
                   , .localget 8] } ]
  , exports := [ { name := "canonical_abi_realloc", desc := .func 0 }
               , { name := "witness-gate", desc := .func 1 }
               , { name := "memory", desc := .memory 0 } ]
  , memMin := 1 }

/-- THE WITNESS-GATE SPEC: the hand-built checker module + the world
    it must match (the emission's skew check runs at generation —
    `Guest.Component.regen`; `check` demands the adapter face: the
    heap result needs the memory + realloc exports). -/
def witGateSpec : Guest.Component.Spec :=
  { core := witGateModule, world := witGateWorld }

/-! ## The Lean-executor leg (the parity's engine face) -/

/-- One checker run through the LEAN EXECUTOR over the fixture's OWN
    module (the same module the component embeds). The args ride the
    executor's pop convention (head = TOP = the LAST param), so the
    natural-order row+wire list is reversed. -/
def gateRun (src dst amount t1 b1 t2 t3 b3 : UInt64) : WasmCore.Outcome :=
  WasmCore.runFunc witGateModule 1
    ([b3, t3, t2, b1, t1, amount, dst, src].map WasmCore.Val.i64) 1000

/-- The little-endian Nat read over the executor's memory face. -/
def memLe (n a : Nat) (mem : Nat → UInt8) : Nat :=
  (List.range n).foldl (fun acc i => acc + (mem (a + i)).toNat * 256 ^ i) 0

/-- The checker's VERDICT as data: the completed run's return area —
    (discriminant, code); the ok face is `(0, 0)`. -/
def gateVerdict : WasmCore.Outcome → Option (Nat × Nat)
  | .ok s =>
      match s.stack with
      | [WasmCore.Val.i32 p] =>
          some (memLe 4 p.toNat s.mem, memLe 8 (p.toNat + 8) s.mem)
      | _ => none
  | _ => none

/-! ## The teeth (runtime-pinned — the SchemaTests discipline; the
     theorems live in SchemaCore.Witness, these pins are their
     regression surface at the fixture) -/

/-- The producer's certificate ACCEPTS at the valid row (the gate
    opens; theorem-backed: `checkWitness_sound`'s face). -/
def legValid : Bool :=
  (invWitnessOf 1 2 5).map (·.checks (invRow 1 2 5)) == some true

/-- The valid row's WIRE (the slots the host ships — the host's
    `WITNESS_WIRE_OK` constant mirrors these). -/
def legValidWire : Bool := invWireOf 1 2 5 == some [1, 1, 3, 0, 0]

/-- THE TAMPERED record refuses (the recorded verdict disagrees with
    the recomputed check) — and its wire EXISTS (the right shape, the
    wrong record: code 2 at the checker). -/
def legTampered : Bool :=
  (Witness.checks
      { label := "t", claim := invPred
      , proof := .conj (.verdict false) (.neg (.verdict false))
      , fuel := WitnessGen.fuelPinned invPred }
      (invRow 1 2 5) = false)
  && (witSlots (.conj (.verdict false) (.neg (.verdict false)))
        == some [1, 0, 3, 0, 0])

/-- THE WRONG-SHAPE certificate refuses (a disjunction-rooted term does
    not fit the `and` claim — the catch-all arm) and has NO wire (the
    wrong-schema refusal, code 3 at the checker). -/
def legWrongSchema : Bool :=
  (Witness.checks
      { label := "w", claim := invPred, proof := .disj true (.verdict true)
      , fuel := WitnessGen.fuelPinned invPred }
      (invRow 1 2 5) = false)
  && (witSlots (.disj true (.verdict true)) = none)

/-- THE INVALID ROW refuses (amount 0; a self-transfer — the claim's
    own check fires false, no honest certificate exists;
    `Witness.check_false_refuses`). -/
def legInvalid : Bool :=
  (Witness.checks
      { label := "i", claim := invPred
      , proof := .conj (.verdict false) (.neg (.verdict false))
      , fuel := WitnessGen.fuelPinned invPred }
      (invRow 1 2 0) = false)
  && (Witness.checks
      { label := "i", claim := invPred
      , proof := .conj (.verdict true) (.neg (.verdict false))
      , fuel := WitnessGen.fuelPinned invPred }
      (invRow 3 3 5) = false)

/-- THE EXECUTOR PARITY (the Lean leg): the fixture's own module
    answers the pinned verdicts — accept (the ok face `(0, 0)`), the
    three refusal codes at their faces. The wasmtime leg (the host's
    typed calls over the COMMITTED component) pins the SAME literals. -/
def legExecutorParity : Bool :=
  -- accept: the gate OPENS
  (gateVerdict (gateRun 1 2 5 1 1 3 0 0)) == some (0, 0)
  -- the tampered record: code 2 (the recorded false vs the recomputed
  -- true — the wire exists, the record is a lie)
  && (gateVerdict (gateRun 1 2 5 1 0 3 0 0)) == some (1, 2)
  -- the claim false at the row: code 1 (amount 0; a self-transfer)
  && (gateVerdict (gateRun 1 2 0 1 1 3 0 0)) == some (1, 1)
  && (gateVerdict (gateRun 3 3 5 1 1 3 0 0)) == some (1, 1)
  -- the wrong-schema faces: code 3 (a wrong tag; a recorded-true
  -- refutation — `.neg (.verdict true)` is not the refutation record)
  && (gateVerdict (gateRun 1 2 5 0 1 3 0 0)) == some (1, 3)
  && (gateVerdict (gateRun 1 2 5 1 1 0 0 0)) == some (1, 3)
  && (gateVerdict (gateRun 1 2 5 1 1 3 0 1)) == some (1, 3)

end ComponentTests.WitFixture
