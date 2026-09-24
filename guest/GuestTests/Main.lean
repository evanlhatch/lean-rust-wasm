/-
# GuestTests — the guest slice's test battery

The end-to-end pins + the refusal teeth + the mandatory negative
controls (15-patterns #5). The driver owns the unsafe IO (the
importModules + the LCNF re-run — the legacy WasmGenMain pattern);
the suites consume the computed results as data (the InspectorTests
live-replay discipline). The HAND-BUILT LCNF decls (the loop shape +
the refusal fixtures) are PURE data lowered through the same
`lowerFunc` — the legacy `Correct.lean` discipline (the shapes the
real pipeline cannot hand over without calls).

Suites:

1. `the end-to-end pin` — add64/sel64: LCNF → the lowered module →
   the VALIDATOR accepts → the EXECUTOR runs → the result pinned
   (the negative controls: the tampered expectation, the wrong
   arg-binding order, the validator-refusing tampered body).
2. `the join points` — jpShared (the pipeline's REAL jp shape: the
   shared continuation + the gotos from the case arms) validates,
   executes, and takes both branches.
3. `the nested cases` — jpThree (a case arm carrying another case —
   the old slice's named exclusion) pins all three routes.
4. `the tag discipline` — smallTag (a scalar-representable enum) pins
   all three tags through the REAL pipeline.
5. `the op-surface growth` — the i32 lane, the u8 MASK (the
   mask-less lowering is caught by the control), the shift, the
   width conversion.
6. `the multi-decl module` — two call-disjoint decls, ONE module, the
   MAIN entry (index 0) + the second entry both pinned.
7. `the loop shape` — the hand-built tail-recursive join: the loop
   frame, the entry discipline, the restart carrying the args.
8. `the refusal teeth (the join-point discipline)` — the loop-entry
   discipline, the unregistered jmp, the arity drift: the named
   refusals fire with the named diagnostics.
9. `the refusal teeth (the boundaries)` — the cap, the bounded-Nat
   lane, the fap outside the op surface, the i64 bitwise op (the op
   table carries no row — wasmcore's lane), the cross-decl call (the
   call lane in flight). The negative controls: the good lowerings
   must NOT refuse, and the rendered diagnostics must carry the GC
   codes.
-/

import Guest
import WasmCore
import TestingKit.Harness
import TestingKit.Spec
import GuestTests.Axioms

open Guest WasmCore TestingKit

/-! ## The driver's IO face (the legacy WasmGenMain pattern) -/

/-- Import the fixture module in-process (`compiler.reuse` disabled —
    the emitter cannot lower reset/reuse joins). The search path: the
    root build dir FIRST (the gates' `loadPkgEnv` discipline — `lake
    exe` does not set LEAN_PATH for the child). -/
unsafe def importFixture : IO (Except String Lean.Environment) := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.searchPathRef.set (".lake/build/lib/lean" :: (← Lean.searchPathRef.get))
  try
    let env ← Lean.importModules #[{ module := `GuestTests.Fixture }]
      (opts := Guest.lcnfOptions) (loadExts := true)
    return .ok env
  catch e =>
    return .error s!"importModules failed: {toString e}"

/-- Read ONE fixture decl + lower it (the LOWERERROR ctor kept — the
    teeth assert on the failure KIND, not the rendered string). -/
unsafe def readAndLower (env : Lean.Environment) (target : Lean.Name) :
    IO (Except Guest.LowerError WasmCore.Module) := do
  match ← Guest.readDecl? env target with
  | .error e => return .error (.unsupportedConstruct "pipeline" e)
  | .ok d => return Guest.lowerFunc d

/-- Read SEVERAL fixture decls (the multi-decl reader; the
    tail-recursive walk). -/
unsafe def readMulti (env : Lean.Environment) :
    List Lean.Name → IO (Except String (List (Lean.Compiler.LCNF.Decl .impure)))
  | [] => return .ok []
  | t :: rest => do
    match ← Guest.readDecl? env t with
    | .error e => return .error e
    | .ok d =>
      match ← readMulti env rest with
      | .error e => return .error e
      | .ok ds => return .ok (d :: ds)

/-- Lower the read decls into ONE module. -/
def lowerDecls (ds : List (Lean.Compiler.LCNF.Decl .impure)) :
    Except Guest.LowerError WasmCore.Module :=
  Guest.lowerFuncs ds

/-! ## The execution face (the pin's oracle half) -/

/-- Run the module's function `fn` on `args` with `fuel`; the final
    stack on a completed run, else the outcome's tag. -/
def runOutcomeFn (m : WasmCore.Module) (fn : Nat) (args : List WasmCore.Val)
    (fuel : Nat) : String :=
  match WasmCore.runFunc m fn args fuel with
  | .ok s => s!"ok {repr s.stack}"
  | .branch d _ => s!"branch {d}"
  | .trap t => s!"trap {repr t}"
  | .structural => "structural"
  | .unmodeled => "unmodeled"
  | .outOfFuel => "outOfFuel"

def runOutcome (m : WasmCore.Module) (args : List WasmCore.Val) : String :=
  runOutcomeFn m 0 args 500

/-- The i64 result of a completed run (the pin's accessor). -/
def resultOf : WasmCore.Outcome → Option UInt64
  | .ok s => match s.stack with
    | [WasmCore.Val.i64 v] => some v
    | _ => none
  | _ => none

/-- The i32 result of a completed run (the i32 lane's accessor). -/
def resultOf32 : WasmCore.Outcome → Option UInt32
  | .ok s => match s.stack with
    | [WasmCore.Val.i32 v] => some v
    | _ => none
  | _ => none

/-- The module validates (the pin's checker half). -/
def validates (m : WasmCore.Module) : Bool :=
  match WasmCore.checkModule m with
  | .ok () => true | .error _ => false

/-! ## The hand-built LCNF decls (the legacy Correct.lean discipline) -/

open Lean.Compiler.LCNF in
/-- A fresh fvar (the hand-built decls' binding discipline). -/
def hbFVar (n : Lean.Name) : Lean.FVarId := Lean.FVarId.mk n

open Lean.Compiler.LCNF in
/-- The u64-typed let literal. -/
def hbLetU64 (n : Lean.Name) (v : UInt64) (k : Code .impure) : Code .impure :=
  .let { fvarId := hbFVar n, binderName := n, type := Lean.Expr.const `UInt64 []
       , value := .lit (.uint64 v) } k

open Lean.Compiler.LCNF in
/-- The Bool ctor info (payload-free — the tag discipline's rows). -/
def hbCtorInfo (n : Lean.Name) (cidx : Nat) : CtorInfo :=
  { name := n, cidx := cidx, size := 0, usize := 0, ssize := 0 }

open Lean.Compiler.LCNF in
/-- THE LOOP-COUNTDOWN DECL: the tail-recursive join the real
    pipeline cannot hand over without calls — built directly, lowered
    purely. In LCNF spelling:
    `jp L(x) = cases (x == 0) | false => jmp L(x-1) | true => return 42`
    followed by the entry `let a := 5; jmp L(a)`. The loop frame + the
    entry discipline lower it; the pin demands 42. -/
def loopDecl : Decl .impure :=
  let x := hbFVar `x
  let z := hbFVar `z
  let t := hbFVar `t
  let one := hbFVar `one
  let y := hbFVar `y
  let r := hbFVar `r
  let a := hbFVar `a
  let L := hbFVar `L
  let paramX : Param .impure :=
    { fvarId := x, binderName := `x, type := Lean.Expr.const `UInt64 []
    , borrow := false }
  -- the loop body: cases (x == 0) | false => jmp L(x-1) | true => return 42
  let bodyL : Code .impure :=
    .let { fvarId := z, binderName := `z, type := Lean.Expr.const `UInt64 []
         , value := .lit (.uint64 0) } (
    .let { fvarId := t, binderName := `t, type := Lean.Expr.const `UInt8 []
         , value := .fap `UInt64.decEq #[.fvar x, .fvar z] } (
    .cases (Cases.mk `Bool (Lean.Expr.const `UInt8 []) t #[
      .ctorAlt (hbCtorInfo `Bool.false 0) (
        .let { fvarId := one, binderName := `one
             , type := Lean.Expr.const `UInt64 []
             , value := .lit (.uint64 1) } (
        .let { fvarId := y, binderName := `y
             , type := Lean.Expr.const `UInt64 []
             , value := .fap `UInt64.sub #[.fvar x, .fvar one] } (
        .jmp L #[.fvar y]))),
      .ctorAlt (hbCtorInfo `Bool.true 1) (
        hbLetU64 `r 42 (.return r))])))
  -- the entry: let a := 5; jmp L(a)
  let kEntry : Code .impure :=
    hbLetU64 `a 5 (.jmp L #[.fvar a])
  { name := `GuestTests.loopCountdown, levelParams := []
  , type := Lean.Expr.const `UInt64 [], params := #[]
  , value := .code (.jp (FunDecl.mk L `L #[paramX]
      (Lean.Expr.const `UInt64 []) bodyL) kEntry)
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The LOOP-ENTRY discipline's refusal decl: the same loop body, but
    the continuation is a bare `return` (not the entry goto) — the
    named `loopEntry` refusal. -/
def loopEntryBadDecl : Decl .impure :=
  let x := hbFVar `x
  let a := hbFVar `a
  let L := hbFVar `L
  let paramX : Param .impure :=
    { fvarId := x, binderName := `x, type := Lean.Expr.const `UInt64 []
    , borrow := false }
  let bodyL : Code .impure :=
    hbLetU64 `z 0 (
    .let { fvarId := hbFVar `t, binderName := `t
         , type := Lean.Expr.const `UInt8 []
         , value := .fap `UInt64.decEq #[.fvar x, .fvar (hbFVar `z)] } (
    .cases (Cases.mk `Bool (Lean.Expr.const `UInt8 []) (hbFVar `t) #[
      .ctorAlt (hbCtorInfo `Bool.false 0) (
        hbLetU64 `one 1 (
        .let { fvarId := hbFVar `y, binderName := `y
             , type := Lean.Expr.const `UInt64 []
             , value := .fap `UInt64.sub #[.fvar x, .fvar (hbFVar `one)] } (
        .jmp L #[.fvar (hbFVar `y)]))),
      .ctorAlt (hbCtorInfo `Bool.true 1) (hbLetU64 `r 42 (.return (hbFVar `r)))])))
  { name := `GuestTests.loopEntryBad, levelParams := []
  , type := Lean.Expr.const `UInt64 []
  , params := #[]
  , value := .code (.jp (FunDecl.mk L `L #[paramX]
      (Lean.Expr.const `UInt64 []) bodyL) (hbLetU64 `a 5 (.return a)))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The UNREGISTERED-jmp refusal decl: a bare `jmp` with no jp. -/
def jpUnregDecl : Decl .impure :=
  { name := `GuestTests.jpUnreg, levelParams := []
  , type := Lean.Expr.const `UInt64 [], params := #[]
  , value := .code (.jmp (hbFVar `Lone) #[])
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The ARITY-DRIFT refusal decl: a one-param jp, a two-arg jmp. -/
def jpArityDecl : Decl .impure :=
  let x := hbFVar `x
  let a := hbFVar `a
  let L := hbFVar `L
  let paramX : Param .impure :=
    { fvarId := x, binderName := `x, type := Lean.Expr.const `UInt64 []
    , borrow := false }
  { name := `GuestTests.jpArity, levelParams := []
  , type := Lean.Expr.const `UInt64 [], params := #[]
  , value := .code (.jp (FunDecl.mk L `L #[paramX]
      (Lean.Expr.const `UInt64 []) (.return x))
    (hbLetU64 `a 5 (.jmp L #[.fvar a, .fvar a])))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The i64-bitwise refusal decl: `UInt64.land` — the op table carries
    no i64 bitwise row (wasmcore's lane), the named refusal. -/
def landDecl : Decl .impure :=
  { name := `GuestTests.landFn, levelParams := []
  , type := Lean.Expr.const `UInt64 [], params := #[]
  , value := .code (hbLetU64 `v 0 (
      .let { fvarId := hbFVar `w, binderName := `w
           , type := Lean.Expr.const `UInt64 []
           , value := .fap `UInt64.land #[.fvar (hbFVar `v), .fvar (hbFVar `v)] }
      (.return (hbFVar `w))))
  , inlineAttr? := none }

/-- The hand-built decls lowered ONCE (the pure data face). -/
def loopLowered : Except Guest.LowerError WasmCore.Module := Guest.lowerFunc loopDecl
def loopEntryBadLowered : Except Guest.LowerError WasmCore.Module := Guest.lowerFunc loopEntryBadDecl
def jpUnregLowered : Except Guest.LowerError WasmCore.Module := Guest.lowerFunc jpUnregDecl
def jpArityLowered : Except Guest.LowerError WasmCore.Module := Guest.lowerFunc jpArityDecl
def landLowered : Except Guest.LowerError WasmCore.Module := Guest.lowerFunc landDecl

/-! ## The pipeline pins (computed once — the driver's data face) -/

/-- The good runs, computed once. -/
structure RunPins where
  add42 : Option UInt64
  selTrue : Option UInt64
  selFalse : Option UInt64
  addValidates : Bool
  selValidates : Bool
  jpTrue : Option UInt64
  jpFalse : Option UInt64
  jpValidates : Bool
  three5 : Option UInt64
  three15 : Option UInt64
  three25 : Option UInt64
  threeValidates : Bool
  tagR : Option UInt64
  tagG : Option UInt64
  tagB : Option UInt64
  tagValidates : Bool
  lane18 : Option UInt32
  cmpT : Option UInt32
  cmpF : Option UInt32
  u8mask : Option UInt32
  shr4 : Option UInt64
  wrap5 : Option UInt32
  laneValidates : Bool
  multiA15 : Option UInt64
  multiB6 : Option UInt64
  multiValidates : Bool
  deriving Inhabited

/-- The i64-pin accessor over a read module (the multi-decl entries). -/
def pinAt (m : Except Guest.LowerError WasmCore.Module) (fn : Nat)
    (args : List WasmCore.Val) : Option UInt64 :=
  match m with
  | Except.ok mm => resultOf (WasmCore.runFunc mm fn args 500)
  | Except.error _ => none

/-- The validation pin over a read module. -/
def pinValidates (m : Except Guest.LowerError WasmCore.Module) : Bool :=
  match m with
  | Except.ok mm => validates mm
  | Except.error _ => false

/-- Compute the pins (the driver's unsafe IO + the pure faces).
    The run convention: args head = TOP = the LAST param (the `call`
    rule's pop order — the driver's binding reads param i into local
    i): `jpShared(c, a, b)` rides [b, a, c]; the i32 lane rides the
    i32 args; `multiA`/`multiB` run at their MODULE entries 0/1. -/
unsafe def computePins : IO (Except String RunPins) := do
  match ← importFixture with
  | .error e => return .error e
  | .ok env =>
    let rd (t : Lean.Name) := readAndLower env t
    let mAdd ← rd `GuestTests.add64
    let mSel ← rd `GuestTests.sel64
    let mJp ← rd `GuestTests.jpShared
    let mThree ← rd `GuestTests.jpThree
    let mTag ← rd `GuestTests.smallTag
    let mLane32 ← rd `GuestTests.u32lane
    let mCmp ← rd `GuestTests.u32cmp
    let mU8 ← rd `GuestTests.u8sub
    let mShr ← rd `GuestTests.u64shr
    let mWrap ← rd `GuestTests.i32wrap
    let dsMulti ← readMulti env [`GuestTests.multiA, `GuestTests.multiB]
    let mMulti : Except Guest.LowerError WasmCore.Module :=
      match dsMulti with
      | .ok ds => lowerDecls ds
      | .error e => .error (.unsupportedConstruct "pipeline" e)
    return .ok
      { add42 := pinAt mAdd 0 [WasmCore.Val.i64 22, WasmCore.Val.i64 20]
        , selTrue := pinAt mSel 0
            [WasmCore.Val.i64 9, WasmCore.Val.i64 7, WasmCore.Val.i32 1]
        , selFalse := pinAt mSel 0
            [WasmCore.Val.i64 9, WasmCore.Val.i64 7, WasmCore.Val.i32 0]
        , addValidates := pinValidates mAdd
        , selValidates := pinValidates mSel
        , jpTrue := pinAt mJp 0
            [WasmCore.Val.i64 9, WasmCore.Val.i64 7, WasmCore.Val.i32 1]
        , jpFalse := pinAt mJp 0
            [WasmCore.Val.i64 9, WasmCore.Val.i64 7, WasmCore.Val.i32 0]
        , jpValidates := pinValidates mJp
        , three5 := pinAt mThree 0 [WasmCore.Val.i64 5]
        , three15 := pinAt mThree 0 [WasmCore.Val.i64 15]
        , three25 := pinAt mThree 0 [WasmCore.Val.i64 25]
        , threeValidates := pinValidates mThree
        , tagR := pinAt mTag 0 [WasmCore.Val.i32 0]
        , tagG := pinAt mTag 0 [WasmCore.Val.i32 1]
        , tagB := pinAt mTag 0 [WasmCore.Val.i32 2]
        , tagValidates := pinValidates mTag
        , lane18 := match mLane32 with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 0
              [WasmCore.Val.i32 5, WasmCore.Val.i32 3] 500)
          | Except.error _ => none
        , cmpT := match mCmp with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 0
              [WasmCore.Val.i32 5, WasmCore.Val.i32 3] 500)
          | Except.error _ => none
        , cmpF := match mCmp with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 0
              [WasmCore.Val.i32 3, WasmCore.Val.i32 5] 500)
          | Except.error _ => none
        , u8mask := match mU8 with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 0
              [WasmCore.Val.i32 100, WasmCore.Val.i32 60] 500)
          | Except.error _ => none
        , shr4 := pinAt mShr 0 [WasmCore.Val.i64 8]
        , wrap5 := match mWrap with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 0
              [WasmCore.Val.i64 4294967301] 500)
          | Except.error _ => none
        , laneValidates := pinValidates mLane32 && pinValidates mCmp
            && pinValidates mU8 && pinValidates mShr && pinValidates mWrap
        , multiA15 := pinAt mMulti 0 [WasmCore.Val.i64 4, WasmCore.Val.i64 3]
        , multiB6 := pinAt mMulti 1 [WasmCore.Val.i64 5]
        , multiValidates := pinValidates mMulti
        }

/-! ## The refusal teeth (the pure faces + the real-pipeline refusals) -/

/-- The cap: a Nat literal at/above 2^62 is the DESIGN ERROR. -/
def capRefusal : Option Guest.LowerError :=
  let litDecl : Lean.Compiler.LCNF.LetDecl .impure :=
    { fvarId := Lean.FVarId.mk `x, binderName := `x
    , type := Lean.Expr.const `Nat []
    , value := .lit (.nat (Guest.natCap : Nat)) }
  let code : Lean.Compiler.LCNF.Code .impure :=
    .let litDecl (.return litDecl.fvarId)
  match StateT.run (Guest.lowerCode code 1 0 .i64) ({} : Guest.LState) with
  | .error e => some e
  | .ok _ => none

/-- Below the cap: the boxed-Nat lane refusal (still loud, still
    named). -/
def laneRefusal : Option Guest.LowerError :=
  let litDecl : Lean.Compiler.LCNF.LetDecl .impure :=
    { fvarId := Lean.FVarId.mk `x, binderName := `x
    , type := Lean.Expr.const `Nat []
    , value := .lit (.nat 5) }
  let code : Lean.Compiler.LCNF.Code .impure :=
    .let litDecl (.return litDecl.fvarId)
  match StateT.run (Guest.lowerCode code 1 0 .i64) ({} : Guest.LState) with
  | .error e => some e
  | .ok _ => none

/-- A fap outside the op surface refuses with the named boundary. -/
def fapRefusal : Option Guest.LowerError :=
  let code : Lean.Compiler.LCNF.Code .impure :=
    .let { fvarId := Lean.FVarId.mk `x, binderName := `x
         , type := Lean.Expr.const `UInt64 []
         , value := .fap `Some.Undefinable.Primitive #[] } (.return ⟨`x⟩)
  match StateT.run (Guest.lowerCode code 1 0 .i64) ({} : Guest.LState) with
  | .error e => some e
  | .ok _ => none

open Lean.Compiler.LCNF in
/-- The cross-decl call refusal (HAND-BUILT — the real pipeline's
    inliner dissolves small calls): declB's body is a fap naming its
    SIBLING declA — lowerFuncs refuses with the named call-lane
    diagnostic. -/
def crossDeclA : Decl .impure :=
  { name := `GuestTests.declA, levelParams := []
  , type := Lean.Expr.const `UInt64 [], params := #[]
  , value := .code (hbLetU64 `v 3 (.return (hbFVar `v)))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
def crossDeclB : Decl .impure :=
  { name := `GuestTests.declB, levelParams := []
  , type := Lean.Expr.const `UInt64 [], params := #[]
  , value := .code (hbLetU64 `w 0 (
    .let { fvarId := hbFVar `u, binderName := `u
         , type := Lean.Expr.const `UInt64 []
         , value := .fap `GuestTests.declA #[.fvar (hbFVar `w)] }
    (.return (hbFVar `u))))
  , inlineAttr? := none }

def crossLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.lowerFuncs [crossDeclA, crossDeclB]

/-! ## The suites (the pins consume the computed data) -/

def endToEndSpecs (pins : RunPins) : List TestingKit.Spec :=
  [ Spec.ofList "the end-to-end pin: add64 20 22 = 42 through LCNF → module → exec"
      (fun _ => TestingKit.assertEq "add42" pins.add42 (some 42))
      [ ("control: a wrong result is caught",
         fun _ => TestingKit.assertEq "add42-wrong" pins.add42 (some 43))
      , ("control: a wrongly-bound arg order would read 43+22=65 — the pin \
          demands the LCNF param order (a swapped binding fails)",
         fun _ => TestingKit.assert (pins.add42 == some 20)
          "the binding-order control demands the swapped value 20")
      ]
      (h := by simp) 1 42
  , Spec.ofList "the generated modules VALIDATE (the validator runs at the pin)"
      (fun _ => do
        TestingKit.assert pins.addValidates "add64's module must validate"
        TestingKit.assert pins.selValidates "sel64's module must validate")
      [ ("control: the validator refuses a tampered body (the stack \
          underflows)",
         fun _ =>
           let bad : WasmCore.Module :=
             { types := [⟨[.i64, .i64], [.i64]⟩]
             , funcs := [⟨0, [], [.localget 7]⟩]
             , exports := [{ name := "bad", desc := .func 0 }] }
           match WasmCore.checkModule bad with
           | .error _ => TestingKit.assert false
               "the control DEMANDS the refusal be flagged (if this fires, \
                the validator accepted an unbound local — vacuous)"
           | .ok () => .ok ())
      , ("control: the executor SILENTLY EXECUTES a call (wrong claim — \
          the ledger answers unmodeled, the control is caught)",
         fun _ => do
           let callMod : WasmCore.Module :=
             { types := [⟨[], [.i64]⟩]
             , funcs := [⟨0, [], [.call 0, .i64const 1]⟩]
             , exports := [{ name := "c", desc := .func 0 }] }
           TestingKit.assertEq "call control" (runOutcome callMod [])
             "ok [.i64 1]")
      ]
      (h := by simp) 1 43
  , Spec.ofList "the control flow: sel64 takes the Bool branches"
      (fun _ => do
        TestingKit.assertEq "selTrue" pins.selTrue (some 7)
        TestingKit.assertEq "selFalse" pins.selFalse (some 9))
      [ ("control: a wrong branch result is caught",
         fun _ => TestingKit.assertEq "selTrue-wrong" pins.selTrue (some 9))
      , ("control: a swapped Bool encoding (1 = false) is caught",
         fun _ => TestingKit.assertEq "selFalse-wrong" pins.selFalse (some 7))
      ]
      (h := by simp) 1 44
  ]

def jpSpecs (pins : RunPins) : List TestingKit.Spec :=
  [ Spec.ofList "the join points: jpShared's shared continuation takes both \
      branches (the pipeline's REAL jp shape)"
      (fun _ => do
        TestingKit.assert pins.jpValidates "jpShared's module must validate"
        TestingKit.assertEq "jpTrue" pins.jpTrue (some 8)
        TestingKit.assertEq "jpFalse" pins.jpFalse (some 10))
      [ ("control: a wrong branch result is caught",
         fun _ => TestingKit.assertEq "jpTrue-wrong" pins.jpTrue (some 10))
      , ("control: a mis-bound goto arg (the +1 on the wrong param) is \
          caught — the pin demands a+1 = 8, not b+1",
         fun _ => TestingKit.assert (pins.jpTrue == some 7)
          "the goto-binding control demands the unswapped value 7")
      ]
      (h := by simp) 1 47
  , Spec.ofList "the nested cases: jpThree takes all three routes"
      (fun _ => do
        TestingKit.assert pins.threeValidates "jpThree's module must validate"
        TestingKit.assertEq "three5" pins.three5 (some 1)
        TestingKit.assertEq "three15" pins.three15 (some 2)
        TestingKit.assertEq "three25" pins.three25 (some 3))
      [ ("control: a wrong middle route is caught",
         fun _ => TestingKit.assertEq "three15-wrong" pins.three15 (some 3))
      , ("control: a wrong outer route is caught",
         fun _ => TestingKit.assertEq "three25-wrong" pins.three25 (some 2))
      ]
      (h := by simp) 1 48
  , Spec.ofList "the tag discipline: smallTag's scalar-representable enum \
      branches on the unboxed tag"
      (fun _ => do
        TestingKit.assert pins.tagValidates "smallTag's module must validate"
        TestingKit.assertEq "tagR" pins.tagR (some 0)
        TestingKit.assertEq "tagG" pins.tagG (some 1)
        TestingKit.assertEq "tagB" pins.tagB (some 2))
      [ ("control: a wrong tag route is caught",
         fun _ => TestingKit.assertEq "tagG-wrong" pins.tagG (some 2))
      , ("control: the tag-case REFUSES the whole lowering (wrong claim — \
          the scalar-repr enum lowers, the pin sees the real module, the \
          control is caught)",
         fun _ => TestingKit.assert (pins.tagG == none)
          "the control demands the refusal (wrong claim — caught)")
      ]
      (h := by simp) 1 49
  , Spec.ofList "the op-surface growth: the i32 lane, the u8 mask, the \
      shift, the width conversion"
      (fun _ => do
        TestingKit.assert pins.laneValidates "the lane modules must validate"
        TestingKit.assertEq "lane18" pins.lane18 (some 18)
        TestingKit.assertEq "cmpT" pins.cmpT (some 1)
        TestingKit.assertEq "cmpF" pins.cmpF (some 0)
        TestingKit.assertEq "u8mask" pins.u8mask (some 216)
        TestingKit.assertEq "shr4" pins.shr4 (some 4)
        TestingKit.assertEq "wrap5" pins.wrap5 (some 5))
      [ ("control: the MASK is caught missing — an unmasked i32 sub \
          reads 4294967256 (60-100 mod 2^32), the pin demands 216",
         fun _ => TestingKit.assert (pins.u8mask == some 4294967256)
          "the mask control demands the unmasked value")
      , ("control: a wrong wrap (off by one) is caught",
         fun _ => TestingKit.assertEq "wrap5-wrong" pins.wrap5 (some 6))
      ]
      (h := by simp) 1 50
  , Spec.ofList "the multi-decl module: two call-disjoint decls, the MAIN \
      entry (index 0) + the second entry both pinned"
      (fun _ => do
        TestingKit.assert pins.multiValidates "the multi module must validate"
        TestingKit.assertEq "multiA15" pins.multiA15 (some 15)
        TestingKit.assertEq "multiB6" pins.multiB6 (some 6))
      [ ("control: a wrong MAIN result is caught",
         fun _ => TestingKit.assertEq "multiA-wrong" pins.multiA15 (some 18))
      , ("control: an entry-index drift (reading entry 1 as MAIN) is \
          caught — the pin demands the decl order",
         fun _ => TestingKit.assert (pins.multiA15 == some 6)
          "the entry control demands the drifted value 6")
      ]
      (h := by simp) 1 51
  , Spec.ofList "the loop shape: the tail-recursive join (hand-built — the \
      real pipeline needs calls to produce it)"
      (fun _ => do
        match loopLowered with
        | Except.error e =>
            TestingKit.assert false s!"the loop shape must LOWER: {e.render}"
        | Except.ok m => do
          TestingKit.assert (validates m) "the loop module must validate"
          TestingKit.assertEq "loopCountdown"
            (resultOf (WasmCore.runFunc m 0 [] 1000)) (some 42))
      [ ("control: a wrong countdown result is caught",
         fun _ =>
           match loopLowered with
           | Except.ok m => TestingKit.assertEq "loop-wrong"
               (resultOf (WasmCore.runFunc m 0 [] 1000)) (some 43)
           | Except.error _ => TestingKit.assert false "unreachable")
      , ("control: the restarts BURN fuel (a 40-unit budget is \
          outOfFuel — six counted-down iterations cost ~100 units; a \
          restartless lowering would trap or finish long before)",
         fun _ =>
           match loopLowered with
           | Except.ok m => TestingKit.assertEq "loop-fuel"
               (runOutcomeFn m 0 [] 40) "outOfFuel"
           | Except.error _ => TestingKit.assert false "unreachable")
      ]
      (h := by simp) 1 52
  ]

def teethSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the refusal teeth: the join-point discipline's named \
      refusals fire"
      (fun _ => do
        match loopEntryBadLowered with
        | Except.error (.loopEntry _) => .ok ()
        | Except.error e =>
            TestingKit.assert false
              s!"the loop-entry fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the loop-entry did NOT refuse"
        match jpUnregLowered with
        | Except.error (.jpUnregistered _) => .ok ()
        | Except.error e =>
            TestingKit.assert false
              s!"the unregistered jmp fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the unregistered jmp did NOT refuse"
        match jpArityLowered with
        | Except.error (.jpArityDrift _ 2 1) => .ok ()
        | Except.error e =>
            TestingKit.assert false
              s!"the arity drift fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the arity drift did NOT refuse")
      [ ("control: the GOOD loop decl REFUSES (wrong claim — it lowers, \
          the control is caught)",
         fun _ => do
           match loopLowered with
           | Except.error _ => .ok ()
           | Except.ok _ => TestingKit.assert false "the good loop LOWERS (the control demanded a refusal)")
      , ("control: the loop-entry diagnostic carries GC99" ++ "99 (wrong code — \
          the loopEntry's E-code is GC2010; the control is caught)",
         fun _ => do
           let r :=
             match loopEntryBadLowered with
               | Except.error e => e.render
               | Except.ok _ => ""
           TestingKit.assert (r.contains ("GC99" ++ "99"))
             (s!"the loop-entry's Diag carries its real code: {r}"))
      ]
      (h := by simp) 1 53
  , Spec.ofList "the refusal teeth: the cap, the lane, the op surface, the \
      cross-decl call"
      (fun _ => do
        match capRefusal with
        | some (.natLitCap v) =>
            TestingKit.assertEq "cap value" v Guest.natCap
        | some e =>
            TestingKit.assert false (s!"the cap fired the WRONG diagnostic: {e.render}")
        | none =>
            TestingKit.assert false "the cap did NOT refuse"
        match fapRefusal with
        | some (.unsupportedConstruct what _) =>
            TestingKit.assertEq "the fap refusal names the construct" what
              "fap Some.Undefinable.Primitive"
        | some e =>
            TestingKit.assert false (s!"the fap refused with the wrong kind: {e.render}")
        | none =>
            TestingKit.assert false "the fap did NOT refuse"
        match landLowered with
        | Except.error (.unsupportedConstruct what _) =>
            TestingKit.assertEq "the i64-bitwise refusal names the op" what
              "fap UInt64.land"
        | Except.error e =>
            TestingKit.assert false (s!"the land fired the WRONG diagnostic: {e.render}")
        | Except.ok _ =>
            TestingKit.assert false "the i64 bitwise op did NOT refuse"
        match crossLowered with
        | Except.error (.declCall fn) =>
            TestingKit.assertEq "the cross-decl call names the callee" fn
              "GuestTests.declA"
        | Except.error e =>
            TestingKit.assert false
              s!"the cross-decl call fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the cross-decl call did NOT refuse")
      [ ("control: the cap literal fires the LANE diagnostic (wrong kind — \
          the cap check comes first, the control is caught)",
         fun _ => do
           match capRefusal with
             | some (.natLane _) => .ok ()
             | some e => TestingKit.assert false (s!"the cap literal fired: {e.render} — the control demanded the lane diagnostic")
             | none => TestingKit.assert false "nothing refused")
      , ("control: the below-cap literal does NOT refuse (wrong claim — \
          the boxed-Nat lane refuses, the control is caught)",
         fun _ => do
           match laneRefusal with
             | none => .ok ()
             | some e => TestingKit.assert false (s!"the below-cap literal refused: {e.render} — the control demanded silence"))
      , ("control: the type map maps Nat to i64 (wrong claim — Nat is an \
          OBJECT, refused; the control is caught)",
         fun _ =>
           TestingKit.assert
             (Guest.wasmTyOf? {} (Lean.Expr.const `Nat []) == some .i64)
             "the type map must NOT silently scalarize Nat — the control's \
               wrong claim would pass vacuously if it did")
      , ("control: the refusal's Diag carries GC99" ++ "99 (wrong code — the \
          cap's E-code is GC2002; the control is caught)",
         fun _ => do
           let r :=
             match capRefusal with
               | some e => e.render
               | none => ""
           TestingKit.assert (r.contains ("GC99" ++ "99"))
             s!"the cap's Diag carries its real code, not the control's wrong one: {r}")
      , ("control: the NON-sibling fap fires the CROSS-DECL diagnostic \
          (wrong kind — the op-surface boundary fires, the control is caught)",
         fun _ => do
           match fapRefusal with
           | some (.declCall _) => .ok ()
           | _ => TestingKit.assert false "fired op-surface (the control demanded cross-decl)")
      ]
      (h := by simp) 1 54
  ]

/-! ## The driver -/

unsafe def main : IO UInt32 := do
  match ← computePins with
  | .error e =>
      IO.eprintln s!"GuestTests: PIPELINE FAILED — {e}"
      return 1
  | .ok pins =>
      TestingKit.mainOfSuites
        [ ("the end-to-end pin", endToEndSpecs pins)
        , ("the control flow growth", jpSpecs pins)
        , ("the refusal teeth", teethSpecs) ]
