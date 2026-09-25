/-
# GuestTests.Deriv — the effects lane's integration pins (the derivation + the boundary check)

The derivation's pins + the over-claim refusal teeth + the mandatory
negative controls (15-patterns #5), over HAND-BUILT IR decls (the IR
is the whole contract — the toy frontend's conformance face: pure data
through the same derivation the real pipeline's decls ride, NO LCNF
anywhere in this module):

1. the derivation's pins — a pure scalar function's EMPTY row (with a
   Bool case: still empty — the VALUE branch touches no memory); a
   memory function's `read`+`write` row (the Nat box, the Nat arith);
   the RC op's rc-cell footprint; the object ctor's field-slot
   footprint; the unknown callee's TOP row (the honest
   over-approximation — the callee's row is not locally derivable);
2. the boundary check — the honest declaration covers; the under-claim
   passes with the slack REPORTED; the over-claim REFUSES (the leaked
   row names the hidden effects) — the named GC2023 diagnostic;
3. the obligation rows — the Prop-indexed obligation per function
   DISCHARGES for the honest declaration (the computed row, evaluated
   through the derivation's equations + `decide`) and is UNPROVABLE
   for the over-claim (the build-time tooth: the declaration fails to
   elaborate); the computed manifest (`obligationRows`) carries
   derived + declared + verdict, never hand-written;
4. the negative controls — the sabotaged claims the suite MUST catch.

Axiom self-check: the derivation's pure faces are pinned in
GuestTests.Axioms (the core triple only).
-/

import Guest
import TestingKit.Harness
import TestingKit.Spec
import LintKit

open Effects TestingKit
open Guest

namespace GuestTests.Deriv

/-! ## The hand-built IR decls (the IR-face pin: pure data, no LCNF) -/

/-- THE PURE SCALAR decl: `a := 5; b := 7; s := a + b; return s` —
    the empty row's pin. -/
def pureDecl : IR.Decl :=
  { name := "GuestTests.derivPure", params := [], resultTy := .u64
  , value :=
      .let_ { var := "a", ty := .u64, value := .litU64 5 } (
      .let_ { var := "b", ty := .u64, value := .litU64 7 } (
      .let_ { var := "s", ty := .u64
            , value := .binop .u64add #[.var "a", .var "b"] } (
      .ret "s"))) }

/-- THE PURE SCALAR decl WITH A BOOL CASE: `t := x == 0;
    cases t | true => return 1 | false => return 2` — the value branch
    touches no memory; the row stays EMPTY (the IR's dispatch lane:
    `CaseVia.value` — the scalar lane branches on the VALUE). -/
def caseDecl : IR.Decl :=
  { name := "GuestTests.derivCase", params := [], resultTy := .u64
  , value :=
      .let_ { var := "x", ty := .u64, value := .litU64 5 } (
      .let_ { var := "z", ty := .u64, value := .litU64 0 } (
      .let_ { var := "t", ty := .u8
            , value := .natFap .decEq #[.var "x", .var "z"] } (
      .cases_ "Bool" .value "t"
        [ .ctorAlt 1 (.let_ { var := "r1", ty := .u64, value := .litU64 1 } (.ret "r1"))
        , .ctorAlt 0 (.let_ { var := "r2", ty := .u64, value := .litU64 2 } (.ret "r2"))
        ]))) }

/-- THE MEMORY decl: a Nat literal's bump-arena box — the `read`+
    `write` row's pin (the allocator reads the bump pointer cell and
    writes it + the object's cells). -/
def natDecl : IR.Decl :=
  { name := "GuestTests.derivNat", params := [], resultTy := .nat
  , value := .let_ { var := "v", ty := .nat, value := .litNat 5 } (.ret "v") }

/-- THE MEMORY decl (the arith face): two Nat boxes + `Nat.add`'s
    fresh box — the same `read`+`write` row. -/
def natAddDecl : IR.Decl :=
  { name := "GuestTests.derivNatAdd", params := [], resultTy := .nat
  , value :=
      .let_ { var := "a", ty := .nat, value := .litNat 1000000000000000000 } (
      .let_ { var := "b", ty := .nat, value := .litNat 500000000000000000 } (
      .let_ { var := "r", ty := .nat
            , value := .natFap .add #[.var "a", .var "b"] } (
      .ret "r"))) }

/-- THE RC decl: box + `inc` + `dec` — the rc cell's footprint key. -/
def rcDecl : IR.Decl :=
  { name := "GuestTests.derivRc", params := [], resultTy := .obj
  , value :=
      .let_ { var := "v", ty := .u64, value := .litU64 9 } (
      .let_ { var := "b", ty := .obj, value := .box .u64 "v" } (
      .inc "b" 1 (
      .dec "b" 1 none (
      .ret "b")))) }

/-- THE OBJECT decl: a scalar-field ctor + the `sproj` read — the
    field-slot footprint key. -/
def objDecl : IR.Decl :=
  { name := "GuestTests.derivObj", params := [], resultTy := .u64
  , value :=
      .let_ { var := "a", ty := .u64, value := .litU64 7 } (
      .let_ { var := "pr", ty := .obj, value := .ctor 0 #[.var "a"] } (
      .let_ { var := "x", ty := .u64, value := .sproj 0 0 "pr" } (
      .ret "x"))) }

/-- THE TOP decl: a call on a NON-sibling (the callee's row is not
    locally derivable) — the honest top row's pin. -/
def topDecl : IR.Decl :=
  { name := "GuestTests.derivTop", params := [], resultTy := .u64
  , value :=
      .let_ { var := "x", ty := .u64, value := .litU64 5 } (
      .let_ { var := "w", ty := .u64
            , value := .call "GuestTests.noSuchFn" #[.var "x"] } (
      .ret "w")) }

/-! ## The derivation's computed faces (the pins' data) -/

def pureRow : Effects.Row := Guest.Effects.rowOf pureDecl
def caseRow : Effects.Row := Guest.Effects.rowOf caseDecl
def natRow : Effects.Row := Guest.Effects.rowOf natDecl
def natAddRow : Effects.Row := Guest.Effects.rowOf natAddDecl
def topRow : Effects.Row := Guest.Effects.rowOf topDecl

def pureFp : Effects.Fp := Guest.Effects.fpOf pureDecl
def natFp : Effects.Fp := Guest.Effects.fpOf natDecl
def rcFp : Effects.Fp := Guest.Effects.fpOf rcDecl
def objFp : Effects.Fp := Guest.Effects.fpOf objDecl
def topFp : Effects.Fp := Guest.Effects.fpOf topDecl

/-! ## The obligation rows (the Prop-indexed faces) -/

/-- The pure scalar function's derived row, EVALUATED through the
    derivation's equations (the computed face the obligations cite —
    the kernel reduces the structural residuum). -/
theorem pureRowEval : Guest.Effects.rowOf pureDecl = [] := by
  simp only [pureDecl, Guest.Effects.rowOf, Guest.Effects.derive,
    Guest.Effects.deriveCode, Guest.Effects.deriveLet,
    Guest.Effects.Deriv.join, Effects.Row.join]
  decide

/-- The Nat box's derived row, evaluated (the same face). -/
theorem natRowEval :
    Guest.Effects.rowOf natDecl = [Effect.read, Effect.write] := by
  simp only [natDecl, Guest.Effects.rowOf, Guest.Effects.derive,
    Guest.Effects.deriveCode, Guest.Effects.deriveLet,
    Guest.Effects.Deriv.join, Effects.Row.join]
  decide

/-- THE honest obligation: the pure scalar function declared pure —
    the derivation's computed face DISCHARGES it. -/
theorem pureObligation : Guest.Effects.Obligation [] pureDecl := by
  show Effects.Row.le (Guest.Effects.rowOf pureDecl) []
  rw [pureRowEval]
  decide

/-- The memory function declared with the HONEST allowance — the
    obligation discharges (the derived row is below it). -/
theorem natObligation :
    Guest.Effects.Obligation [Effect.read, Effect.write] natDecl := by
  show Effects.Row.le (Guest.Effects.rowOf natDecl) [Effect.read, Effect.write]
  rw [natRowEval]
  decide

/-- THE over-claim's refusal, at the theorem face: the refused verdict
    is EXACTLY the failed obligation (the law's soundness — cited). -/
theorem natOverNotObligation :
    ¬ Guest.Effects.Obligation [] natDecl :=
  Guest.Effects.verdict_over_refuses [] (Guest.Effects.rowOf natDecl)
    [Effect.read, Effect.write] (by rw [natRowEval]; decide)

/-- ... and the law's completeness: the over-claim is ALWAYS refused —
    no leaked row slips through (cited). -/
theorem natOverRefused :
    ∃ leaked, Guest.Effects.verdictOf [] (Guest.Effects.rowOf natDecl)
      = Guest.Effects.RowVerdict.refused leaked :=
  Guest.Effects.verdict_not_le_refuses [] (Guest.Effects.rowOf natDecl)
    natOverNotObligation

/-- The under-claim's honesty, at the theorem face: the widened
    allowance still covers the derived row (cited). -/
theorem natUnderStillCovers :
    Guest.Effects.Obligation [Effect.read, Effect.write, Effect.clock] natDecl := by
  show Effects.Row.le (Guest.Effects.rowOf natDecl) _
  rw [natRowEval]
  decide

/- THE over-claim TOOTH: the memory function declared pure — the
   obligation is FALSE, no proof exists, the declaration fails to
   elaborate (the discipline: a function declared pure that touches
   memory fails the check). -/
/-- error: Tactic `decide` proved that the proposition
  Row.le [Effect.read, Effect.write] []
is false -/
#guard_msgs in
@[nolint linter.guestlang.axiomAllowlist "the teeth: a deliberately-failing decl; Lean's error recovery plants the sorryAx"]
example : Guest.Effects.Obligation [] natDecl := by
  show Effects.Row.le (Guest.Effects.rowOf natDecl) []
  rw [natRowEval]
  decide

/-! ## The suite (the runtime pins + the mandatory negative controls) -/

-- The rows'/key-sets' membership equality (the semantics —
-- `Effects.Row.sameMembers`'s data face): the join PREPENDS
-- accumulated members, so a joined row's list order is inert; the
-- pins compare MEMBERS, never list syntax.
def sameRow {α : Type} [DecidableEq α] (a b : List α) : Bool :=
  a.length == b.length && a.all (fun e => b.contains e)

/-- THE obligation-row manifest (computed, never hand-written): the
    honest registry over the pin decls — every function declared
    pure. -/
def manifestPureRegistry : List Guest.Effects.ObligationRow :=
  Guest.Effects.obligationRows (fun _ => []) [pureDecl, natDecl]

/-- The over-claim's enforcement (the refusing face). -/
def overEnforced : Except Guest.Effects.EffectError Effects.Row :=
  Guest.Effects.enforce "GuestTests.derivNat" [] natDecl

-- The pins' ToString faces (the GuestTests.RunVerdict precedent — the
-- Repr-backed renderings for assertEq's failure messages).
instance : ToString Guest.Effects.RowVerdict := ⟨fun v => toString (repr v)⟩
instance : ToString Effects.Row := ⟨Guest.Effects.renderRow⟩

/-- The derivation + boundary check's runtime face: the computed
    verdicts, asserted (the pins' data face — the values the compiler
    computes at run time, never re-decided by hand). -/
def derivSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the effects lane: the derivation's pins + the boundary
      check + the obligation rows (the compiled functions carry rows
      DERIVED from their content — 08 §8's discipline)"
      (fun _ => do
        -- the pure scalar function's EMPTY row + EMPTY footprint
        TestingKit.assert (pureRow == ([] : Effects.Row))
          "the pure scalar function's row must be EMPTY"
        TestingKit.assert (caseRow == ([] : Effects.Row))
          "the Bool-case function's row must be EMPTY (the value branch)"
        TestingKit.assert (pureFp == ([] : Effects.Fp))
          "the pure scalar function's footprint must be EMPTY"
        -- the memory function's read+write row + the box's footprint
        TestingKit.assert ((Effect.write ∈ natRow) && (Effect.read ∈ natRow))
          "the Nat box's row must carry read+write"
        TestingKit.assert ((Effect.write ∈ natAddRow) && (Effect.read ∈ natAddRow))
          "the Nat arith's row must carry read+write"
        TestingKit.assert (natFp.contains Guest.Effects.fpBump
          && natFp.contains Guest.Effects.fpTag
          && natFp.contains Guest.Effects.fpPayload)
          "the Nat box's footprint must carry the bump/tag/payload regions"
        TestingKit.assert (rcFp.contains Guest.Effects.fpRc)
          "the RC decl's footprint must carry the rc cell"
        TestingKit.assert (objFp.contains Guest.Effects.fpField)
          "the object ctor's footprint must carry the field region"
        -- the unknown callee's TOP row (the honest over-approximation;
        -- membership-compared — the join's list order is inert)
        TestingKit.assert (sameRow topRow Guest.Effects.rowTop)
          "the unknown callee's row must be the TOP row"
        TestingKit.assert (sameRow topFp Guest.Effects.fpTop)
          "the unknown callee's footprint must be the TOP footprint"
        -- the boundary check: honest / under-claim (reported) / over-claim (refused)
        match Guest.Effects.verdictOf [Effect.read, Effect.write] natRow with
        | .covered => .ok ()
        | _ =>
            TestingKit.assert false "the honest declaration must COVER"
        match Guest.Effects.verdictOf [Effect.read, Effect.write, Effect.clock] natRow with
        | .coveredWithSlack slack =>
            TestingKit.assert (sameRow slack [Effect.clock])
              "the under-claim's slack must name exactly the unused allowance"
        | _ =>
            TestingKit.assert false
              "the under-claim must pass with the slack REPORTED"
        match Guest.Effects.verdictOf [] natRow with
        | .refused leaked =>
            TestingKit.assert (sameRow leaked [Effect.read, Effect.write])
              "the over-claim's leaked row must name exactly the hidden effects"
        | _ =>
            TestingKit.assert false "the over-claim's verdict must refuse"
        -- the enforcement: the over-claim refuses with the named diagnostic
        match overEnforced with
        | Except.error (.overClaim fn leaked) =>
            TestingKit.assertEq "the over-claim refusal names the function" fn
              "GuestTests.derivNat"
            TestingKit.assertEq "the over-claim refusal names the leaked row" leaked
              [Effect.read, Effect.write]
            TestingKit.assert (sameRow leaked [Effect.read, Effect.write])
              "the over-claim's leaked row must name the hidden effects (membership)"
            TestingKit.assert ((Guest.Effects.EffectError.render
              (.overClaim fn leaked)).contains "GC2023")
              s!"the over-claim's Diag must carry its real code GC2023: \
                 {Guest.Effects.EffectError.render (.overClaim fn leaked)}"
        | Except.ok _ =>
            TestingKit.assert false "the over-claim did NOT refuse"
        -- the manifest: computed rows, one per function
        match manifestPureRegistry with
        | [r1, r2] =>
            TestingKit.assertEq "the manifest's first function" r1.fn
              "GuestTests.derivPure"
            TestingKit.assertEq "the pure function's manifest verdict" r1.verdict
              Guest.Effects.RowVerdict.covered
            TestingKit.assert (r2.derived == natRow)
              "the manifest's derived row must be COMPUTED (never hand-written)"
            match r2.verdict with
            | .refused leaked =>
                TestingKit.assert (sameRow leaked [Effect.read, Effect.write])
                  "the manifest's refused verdict must name the leaked row"
            | _ =>
                TestingKit.assert false
                  "the manifest's memory-function row must be REFUSED"
        | _ => TestingKit.assert false "the manifest must carry one row per function")
      [ ("control: the pure function's row carries a write (wrong — caught)",
         fun _ => TestingKit.assert (Effect.write ∈ pureRow)
           "the pure derivation claimed a write (the control's wrong claim)")
      , ("control: the over-claim PASSES the boundary check (wrong — the
          refusal fires, caught)",
         fun _ => do
           match overEnforced with
           | Except.ok _ => .ok ()
           | Except.error _ =>
               TestingKit.assert false
                 "the over-claim was REFUSED (the control demanded a pass)")
      , ("control: the pure function's footprint leaks a region (wrong — caught)",
         fun _ => TestingKit.assert (pureFp.contains Guest.Effects.fpBump)
           "the pure derivation claimed a footprint region")
      ]
      (h := by simp) 1 80
  ]

end GuestTests.Deriv
