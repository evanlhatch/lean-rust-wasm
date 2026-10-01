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
   table carries no row — wasmcore's lane), the cross-decl call ARITY
   drift (the call lane's named refusal for a malformed sibling
   call). The negative controls: the good lowerings must NOT refuse,
   and the rendered diagnostics must carry the GC codes.
10. `the cross-decl call lane` — the two-decl program (helper +
   main, hand-built so the arg order is PINNED), the self-recursive
   `sumTo` + its caller through the REAL pipeline, the fuel honesty
   (a small budget answers outOfFuel — the recursion's bound), and
   the INLINER HONESTY (`crossCall`'s small call dissolves — the
   lowering sees what LCNF produces).
11. `the closure discipline` — the REAL pipeline's `_closed` fixpoint
   family (twiceAdd5's producer + the `_boxed_const_1` literal + the
   `_lam_1` closure body + the `_lam_1._boxed` adapter, ONE pipeline
   run over the root): the module validates, the producer's entry
   runs, and the CLOSURE OBJECT's layout is read from the run's
   final memory (tag 254, the adapter's fnIdx, the rc cells, the
   captured box's payload) + the KNOWN-ARITY application (hand-built
   — the real consumers apply first-class, the indirect lane's
   boundary): the captured local feeds BOTH applications, the
   marshalling order pinned by the order-sensitive callee.
12. `the RC seed` — the rc cell's real arithmetic (init 1 at birth,
   inc/dec at the honest points) read from memory, the dead marking
   (dec-to-zero leaves rc=0 — no reuse, the size-class freelist is
   the named follow-up), the over-dec TRAP.
13. `the closure teeth` — the INDIRECT-CALL LANE: the REAL pipeline's
   first-class application LOWERS (applyTwice's body → callindirect
   at the sig registry's type index + the identity table); the
   twiceAdd5 family's PARTIAL pap applied first-class answers the
   executor's indirectSig trap (the honesty — never a wrong call);
   bigMain is the successful dispatch end to end (21/2715); the
   non-closure refusal (a scalar fvar applied) + the pap/application
   arity drifts + the pap's unknown callee + the RC-on-scalar + the
   field-cascade dec; the negative controls as everywhere.
14. `the list discipline` — the object tag dispatch's payoff: the
   REAL pipeline's cons/nil objects + the fold through the dispatch
   (the answer 15 + the objects' tag bytes read from the run's
   final memory) + the dispatch's refusal teeth (the unclassifiable
   ctor field, the usize field read).
15. `the effects lane` — the effect-row DERIVATION over the LCNF
    (Guest.Effects: the pure scalar = the empty row, the memory
    constructs = read+write, the unknown callee = the top row), the
    boundary check (the over-claim refuses with GC2023, the
    under-claim reports the slack), the obligation rows + the
    manifest, the footprint keys; the negative controls.
16. `the translation-correctness slice` — the source-vs-execution
    agreement for the REAL pipeline fixtures (the fixture defs' Lean
    evaluation vs the compiled modules' executions) + the extraction
    pin (the real lowering's output = the theorem face's template);
    the THEOREM face lives in Guest.Correct (the chain correspondence
    + the sabotaged-op-map control + the build-failing extraction
    #guards).
17. `the toy frontend` — a HAND-WRITTEN IR program (no LCNF) rides
    the lowering: its module EQUALS the LCNF frontend's (the bytes
    tie) and runs — the conformance evidence that the IR is the whole
    contract; the toy negative (an unregistered jmp via hand IR)
    pins the lowering's own teeth.
18. `the RC cascade + the del` — the cascade's honest counts (the
    dying object's ref field's rc drops with it, read from memory),
    the over-dec tooth past the cascade; the del's ownership
    assertion (rc = 1 checked at runtime) + the dead marking, the
    shared object's del TRAP.
19. `the in-place writes` — sset rides the sproj coordinates (42
    through the write + the memory face), oset stores the new pointer
    (the displaced ref's dec is the stream's obligation — the rc
    honesty pin), setTag turns the tag dispatch (the control without
    it runs the default); the LEGALITY teeth: a shared cell's write
    (rc = 2) TRAPS for both the scalar and the ref write.
20. `the extern face` — the declared trust boundary: the signature
    lands (two exports), the body traps (the host link is the named
    follow-up), the sibling call reaches the same boundary; the toy
    extern (hand IR) rides lowerFunc directly.
-/

import Guest
import WasmCore
import TestingKit.Harness
import TestingKit.Spec
import GuestTests.Axioms
import GuestTests.Deriv
import GuestTests.StdSpecs
import GuestTests.EdgeSpecs

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
  | .ok d => return Guest.compile [d]

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
  Guest.compile ds

/-! ## The execution face (the pin's oracle half) -/

/-- Run the module's function `fn` on `args` with `fuel`; the run
    VERDICT as the honest inductive (verdictCtors: the enumerated
    outcomes carrying their evidence, never a parsed-back String
    render). The evidence is the value-level half of `WasmCore.Outcome`
    (the stack list, the branch depth, the trap — `State`'s function
    fields cannot carry equality; the render never carried them). -/
inductive RunVerdict where
  | ok (stack : List WasmCore.Val)
  | branch (depth : Option Nat) (stack : List WasmCore.Val)
  | trap (t : WasmCore.Trap)
  | structural
  | unmodeled
  | outOfFuel
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The failure-message face (`assertEq`'s ToString): the SAME render
    the old String verdict parsed back — now derived evidence, never
    re-parsed. -/
def RunVerdict.render : RunVerdict → String
  | .ok vs => s!"ok {repr vs}"
  | .branch d vs => s!"branch {repr d}"
  | .trap t => s!"trap {repr t}"
  | .structural => "structural"
  | .unmodeled => "unmodeled"
  | .outOfFuel => "outOfFuel"

instance : ToString RunVerdict := ⟨RunVerdict.render⟩

def RunVerdict.ofOutcome : WasmCore.Outcome → RunVerdict
  | .ok s => .ok s.stack
  | .branch d s => .branch d s.stack
  | .trap t => .trap t
  | .structural => .structural
  | .unmodeled => .unmodeled
  | .outOfFuel => .outOfFuel

def runOutcomeFn (m : WasmCore.Module) (fn : Nat) (args : List WasmCore.Val)
    (fuel : Nat) : RunVerdict :=
  RunVerdict.ofOutcome (WasmCore.runFunc m fn args fuel)

def runOutcome (m : WasmCore.Module) (args : List WasmCore.Val) : RunVerdict :=
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

/-- The BOXED-NAT result of a completed run: the final stack's i32
    pointer (the box's address), the payload read little-endian @8
    (the legacy layout's read face). -/
def resultOfNat : WasmCore.Outcome → Option Nat
  | .ok s => match s.stack with
    | [WasmCore.Val.i32 p] => some (WasmCore.readLE 8 (p.toNat + 8) s.mem)
    | _ => none
  | _ => none

/-- The final stack's i32 AS A MEMORY ADDRESS (the object-return
    pin's face — the closure family returns the closure pointer). -/
def ptrOf : WasmCore.Outcome → Option Nat
  | .ok s => match s.stack with
    | [WasmCore.Val.i32 p] => some p.toNat
    | _ => none
  | _ => none

/-- The memory word at `addr` (width `w`, little-endian) after a
    completed run (the RC cell + the closure layout's read face). -/
def memAtW (w addr : Nat) : WasmCore.Outcome → Option Nat
  | .ok s => some (WasmCore.readLE w addr s.mem)
  | _ => none

/-- The trap tooth's structural accessor (repr's rendering is not a
    stable pin surface — the KIND is). -/
def isUnreachTrap : WasmCore.Outcome → Bool
  | .trap .unreach => true
  | _ => false

/-- The module validates (the pin's checker half). -/
def validates (m : WasmCore.Module) : Bool :=
  match WasmCore.checkModule m with
  | .ok () => true | .error _ => false

/-! ## The hand-built LCNF decls (the legacy Correct.lean discipline) -/

open Lean.Compiler.LCNF in
/-- A fresh fvar (the hand-built decls' binding discipline). The
    dup-body linter's opt-out: GuestTests.Deriv's `dFVar` carries the
    same body — the Correct.lean helpers are self-contained per module
    (Main imports Deriv, so the delegation direction is Deriv→Main,
    which cannot land). -/
@[nolint linter.guestlang.dupDefBodies "the Correct.lean discipline's helper, self-contained per module (Deriv cannot import Main); the alpha-equivalent body is the delegation that cannot land"]
def hbFVar (n : Lean.Name) : Lean.FVarId := Lean.FVarId.mk n

/-- The fixtures' type spellings, written once (the closed fragment:
    u64 scalars, the u8 compares, the tagged Nats, the boxed objects). -/
def hbU64 : Lean.Expr := Lean.Expr.const `UInt64 []
def hbU8 : Lean.Expr := Lean.Expr.const `UInt8 []
def hbTagged : Lean.Expr := Lean.Expr.const `tagged []
def hbObj : Lean.Expr := Lean.Expr.const `obj []
def hbU32 : Lean.Expr := Lean.Expr.const `UInt32 []

open Lean.Compiler.LCNF in
/-- A u64-typed param (the hand-built decls' binding discipline). -/
def hbParam (n : Lean.Name) : Param .impure :=
  { fvarId := hbFVar n, binderName := n, type := hbU64, borrow := false }

open Lean.Compiler.LCNF in
/-- THE GENERIC LET (the typed sugars' shared body): one binding, the
    type spelled, the value any fragment expression. -/
def hbLet (n : Lean.Name) (ty : Lean.Expr) (value : LetValue .impure)
    (k : Code .impure) : Code .impure :=
  .let { fvarId := hbFVar n, binderName := n, type := ty, value := value } k

open Lean.Compiler.LCNF in
/-- The u64-typed let literal. -/
def hbLetU64 (n : Lean.Name) (v : UInt64) (k : Code .impure) : Code .impure :=
  hbLet n hbU64 (.lit (.uint64 v)) k

open Lean.Compiler.LCNF in
/-- The let-fap (the sibling-call / op-surface lets' flat spelling). -/
def hbLetFap (n : Lean.Name) (fn : Lean.Name) (args : Array (Arg .impure))
    (k : Code .impure) : Code .impure :=
  hbLet n hbU64 (.fap fn args) k

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
  let paramX := hbParam `x
  -- the loop body: cases (x == 0) | false => jmp L(x-1) | true => return 42
  let bodyL : Code .impure :=
    hbLet `z hbU64 (.lit (.uint64 0)) (
    hbLet `t hbU8 (.fap `UInt64.decEq #[.fvar x, .fvar z]) (
    .cases (Cases.mk `Bool (hbU8) t #[
      .ctorAlt (hbCtorInfo `Bool.false 0) (
        hbLet `one hbU64 (.lit (.uint64 1)) (
        hbLet `y hbU64 (.fap `UInt64.sub #[.fvar x, .fvar one]) (
        .jmp L #[.fvar y]))),
      .ctorAlt (hbCtorInfo `Bool.true 1) (
        hbLetU64 `r 42 (.return r))])))
  -- the entry: let a := 5; jmp L(a)
  let kEntry : Code .impure :=
    hbLetU64 `a 5 (.jmp L #[.fvar a])
  { name := `GuestTests.loopCountdown, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (.jp (FunDecl.mk L `L #[paramX]
      (hbU64) bodyL) kEntry)
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The LOOP-ENTRY discipline's refusal decl: the same loop body, but
    the continuation is a bare `return` (not the entry goto) — the
    named `loopEntry` refusal. -/
def loopEntryBadDecl : Decl .impure :=
  let x := hbFVar `x
  let a := hbFVar `a
  let L := hbFVar `L
  let paramX := hbParam `x
  let bodyL : Code .impure :=
    hbLetU64 `z 0 (
    hbLet `t hbU8 (.fap `UInt64.decEq #[.fvar x, .fvar (hbFVar `z)]) (
    .cases (Cases.mk `Bool (hbU8) (hbFVar `t) #[
      .ctorAlt (hbCtorInfo `Bool.false 0) (
        hbLetU64 `one 1 (
        hbLet `y hbU64 (.fap `UInt64.sub #[.fvar x, .fvar (hbFVar `one)]) (
        .jmp L #[.fvar (hbFVar `y)]))),
      .ctorAlt (hbCtorInfo `Bool.true 1) (hbLetU64 `r 42 (.return (hbFVar `r)))])))
  { name := `GuestTests.loopEntryBad, levelParams := []
  , type := hbU64
  , params := #[]
  , value := .code (.jp (FunDecl.mk L `L #[paramX]
      (hbU64) bodyL) (hbLetU64 `a 5 (.return a)))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The UNREGISTERED-jmp refusal decl: a bare `jmp` with no jp. -/
def jpUnregDecl : Decl .impure :=
  { name := `GuestTests.jpUnreg, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (.jmp (hbFVar `Lone) #[])
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The ARITY-DRIFT refusal decl: a one-param jp, a two-arg jmp. -/
def jpArityDecl : Decl .impure :=
  let x := hbFVar `x
  let a := hbFVar `a
  let L := hbFVar `L
  let paramX := hbParam `x
  { name := `GuestTests.jpArity, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (.jp (FunDecl.mk L `L #[paramX]
      (hbU64) (.return x))
    (hbLetU64 `a 5 (.jmp L #[.fvar a, .fvar a])))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The i64-bitwise refusal decl: `UInt64.land` — the op table carries
    no i64 bitwise row (wasmcore's lane), the named refusal. -/
def landDecl : Decl .impure :=
  { name := `GuestTests.landFn, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (hbLetU64 `v 0 (
      hbLet `w hbU64 (.fap `UInt64.land #[.fvar (hbFVar `v), .fvar (hbFVar `v)]) (.return (hbFVar `w))))
  , inlineAttr? := none }

/-- The hand-built decls lowered ONCE (the pure data face). -/
def loopLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [loopDecl]
def loopEntryBadLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [loopEntryBadDecl]
def jpUnregLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [jpUnregDecl]
def jpArityLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [jpArityDecl]
def landLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [landDecl]

open Lean.Compiler.LCNF in
/-- THE TWO-DECL CALL PROGRAM (hand-built — the Correct.lean
discipline — so the ARG ORDER is pinned byte-exactly): the helper
`helperSub(a, b) = a - b` (the order-sensitive op: a swapped
marshalling answers b - a = the wrap of -42, never 42), and the main
`mainSub() = helperSub(50, 8)`. The call lowers at the callee's
function-table index (MAIN first → the helper is index 1). -/
def callHelperDecl : Decl .impure :=
  let a := hbFVar `a
  let b := hbFVar `b
  let t := hbFVar `t
  let paramA := hbParam `a
  let paramB := hbParam `b
  { name := `GuestTests.helperSub, levelParams := []
  , type := hbU64, params := #[paramA, paramB]
  , value := .code (hbLetFap `t `UInt64.sub #[.fvar a, .fvar b] (.return t))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
def callMainDecl : Decl .impure :=
  let _x := hbFVar `x
  let _y := hbFVar `y
  let r := hbFVar `r
  { name := `GuestTests.mainSub, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (hbLetU64 `x 50 (
    hbLetU64 `y 8 (
    hbLetFap `r `GuestTests.helperSub
      #[.fvar (hbFVar `x), .fvar (hbFVar `y)]
      (.return r))))
  , inlineAttr? := none }

def callLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [callMainDecl, callHelperDecl]

/-! ## The hand-built BOXED-NAT decls (the Correct.lean discipline) -/

open Lean.Compiler.LCNF in
/-- The Nat-typed let literal (type `tagged` — the real pipeline's
    spelling; the map's object rows ride it). -/
def hbLetNat (n : Lean.Name) (v : Nat) (k : Code .impure) : Code .impure :=
  hbLet n hbTagged (.lit (.nat v)) k

open Lean.Compiler.LCNF in
/-- The Nat-typed let-fap (the boxed-Nat arith rows' spelling). -/
def hbLetNatFap (n : Lean.Name) (fn : Lean.Name) (args : Array (Arg .impure))
    (k : Code .impure) : Code .impure :=
  hbLet n hbTagged (.fap fn args) k

open Lean.Compiler.LCNF in
/-- The Bool-typed let-fap (the boxed-Nat compare rows' spelling). -/
def hbLetNatCmp (n : Lean.Name) (fn : Lean.Name) (args : Array (Arg .impure))
    (k : Code .impure) : Code .impure :=
  hbLet n hbU8 (.fap fn args) k

open Lean.Compiler.LCNF in
def natLitSmallDecl : Decl .impure :=
  { name := `GuestTests.natLitSmall, levelParams := []
  , type := hbTagged, params := #[]
  , value := .code (hbLetNat `v 5 (.return (hbFVar `v)))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
def natAddOkDecl : Decl .impure :=
  { name := `GuestTests.natAddOk, levelParams := []
  , type := hbTagged, params := #[]
  , value := .code (
      hbLetNat `a 1000000000000000000 (
      hbLetNat `b 500000000000000000 (
      hbLetNatFap `r `Nat.add #[.fvar (hbFVar `a), .fvar (hbFVar `b)]
      (.return (hbFVar `r)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
def natSubOkDecl : Decl .impure :=
  { name := `GuestTests.natSubOk, levelParams := []
  , type := hbTagged, params := #[]
  , value := .code (
      hbLetNat `a 9 (
      hbLetNat `b 5 (
      hbLetNatFap `r `Nat.sub #[.fvar (hbFVar `a), .fvar (hbFVar `b)]
      (.return (hbFVar `r)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The SUB-UNDERFLOW tooth: 5 − 9 would wrap (u64) — the underflow
    trap fires first (the runtime cap discipline's sub face). -/
def natSubBadDecl : Decl .impure :=
  { name := `GuestTests.natSubBad, levelParams := []
  , type := hbTagged, params := #[]
  , value := .code (
      hbLetNat `a 5 (
      hbLetNat `b 9 (
      hbLetNatFap `r `Nat.sub #[.fvar (hbFVar `a), .fvar (hbFVar `b)]
      (.return (hbFVar `r)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
def natMulOkDecl : Decl .impure :=
  { name := `GuestTests.natMulOk, levelParams := []
  , type := hbTagged, params := #[]
  , value := .code (
      hbLetNat `a 2147483648 (
      hbLetNat `b 1073741824 (
      hbLetNatFap `r `Nat.mul #[.fvar (hbFVar `a), .fvar (hbFVar `b)]
      (.return (hbFVar `r)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The MUL-OVERFLOW tooth: 2⁶¹ × 4 = 2⁶³ — high word 0, the low word
    ≥ the cap → the trap (the runtime cap discipline's mul face). -/
def natMulOverDecl : Decl .impure :=
  { name := `GuestTests.natMulOver, levelParams := []
  , type := hbTagged, params := #[]
  , value := .code (
      hbLetNat `a 2305843009213693952 (
      hbLetNat `b 4 (
      hbLetNatFap `r `Nat.mul #[.fvar (hbFVar `a), .fvar (hbFVar `b)]
      (.return (hbFVar `r)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The MUL-WRAP-MASQUERADE tooth: 2⁴¹ × 2⁴¹ = 2⁸² — the u64 product
    WRAPS TO 0; the high-word guard catches it (a lowering without
    the 128-bit guard would answer the box of 0 — silently wrong). -/
def natMulWrapDecl : Decl .impure :=
  { name := `GuestTests.natMulWrap, levelParams := []
  , type := hbTagged, params := #[]
  , value := .code (
      hbLetNat `a 2199023255552 (
      hbLetNat `b 2199023255552 (
      hbLetNatFap `r `Nat.mul #[.fvar (hbFVar `a), .fvar (hbFVar `b)]
      (.return (hbFVar `r)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
def natEqDecl (a b : Nat) (n : Lean.Name) : Decl .impure :=
  { name := `GuestTests.natEqFn, levelParams := []
  , type := hbU8, params := #[]
  , value := .code (
      hbLetNat `x a (
      hbLetNat `y b (
      hbLetNatCmp n `Nat.decEq #[.fvar (hbFVar `x), .fvar (hbFVar `y)]
      (.return (hbFVar n)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
def natLtDecl (a b : Nat) (n : Lean.Name) : Decl .impure :=
  { name := `GuestTests.natLtFn, levelParams := []
  , type := hbU8, params := #[]
  , value := .code (
      hbLetNat `x a (
      hbLetNat `y b (
      hbLetNatCmp n `Nat.decLt #[.fvar (hbFVar `x), .fvar (hbFVar `y)]
      (.return (hbFVar n)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
def natLeDecl (a b : Nat) (n : Lean.Name) : Decl .impure :=
  { name := `GuestTests.natLeFn, levelParams := []
  , type := hbU8, params := #[]
  , value := .code (
      hbLetNat `x a (
      hbLetNat `y b (
      hbLetNatCmp n `Nat.decLe #[.fvar (hbFVar `x), .fvar (hbFVar `y)]
      (.return (hbFVar n)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE CTOR-CASE-ON-NAT tooth (the model's pinned throw): a hand-
    built `cases` with `Nat` as the scrutinee's type name — the
    generic tag dispatch would read the box's tag 0 and treat the
    payload as a pointer, so the model refuses loudly. -/
def natCaseDecl : Decl .impure :=
  { name := `GuestTests.natCaseFn, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
      hbLetNat `n 5 (
      .cases (Cases.mk `Nat (hbTagged) (hbFVar `n) #[
        .ctorAlt (hbCtorInfo `Nat.zero 0) (hbLetU64 `r 0 (.return (hbFVar `r))),
        .ctorAlt (hbCtorInfo `Nat.succ 1) (hbLetU64 `r 1 (.return (hbFVar `r)))])))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE BOXED-NAT × JP composition: `jp L(x) = r := x + x; return r`,
    the entry `a := 21; jmp L(a)` — a Nat BOX rides the jp param (an
    i32 pointer local), the arith reads its payload twice; the
    answer 42. The non-loop jp takes the block shape. -/
def natJpDecl : Decl .impure :=
  let x := hbFVar `x
  let r := hbFVar `r
  let a := hbFVar `a
  let L := hbFVar `L
  let paramX : Param .impure :=
    { fvarId := x, binderName := `x, type := hbTagged
    , borrow := true }
  let bodyL : Code .impure :=
    hbLetNatFap `r `Nat.add #[.fvar x, .fvar x] (.return r)
  { name := `GuestTests.natJp, levelParams := []
  , type := hbTagged, params := #[]
  , value := .code (.jp (FunDecl.mk L `L #[paramX]
      (hbTagged) bodyL) (hbLetNat `a 21 (.jmp L #[.fvar a])))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE OBJECT SEED's round trip (the legacy slot discipline: the
    header {rc reserved, tag} + field i's 8-byte slot @8 + i*8):
    ctor Pair.mk(u64 7, u32 9) + the sproj reads. -/
def objCtorInfo : CtorInfo :=
  { name := `GuestTests.Pair.mk, cidx := 0, size := 24, usize := 0, ssize := 2 }

open Lean.Compiler.LCNF in
def objRoundXDecl : Decl .impure :=
  { name := `GuestTests.objRoundX, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
      hbLetU64 `a 7 (
      hbLet `b hbU32 (.lit (.uint32 9)) (
      hbLet `pr hbObj (.ctor objCtorInfo
                      #[.fvar (hbFVar `a), .fvar (hbFVar `b)]) (
      hbLet `x hbU64 (.sproj 0 0 (hbFVar `pr)) (.return (hbFVar `x))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
def objRoundYDecl : Decl .impure :=
  { name := `GuestTests.objRoundY, levelParams := []
  , type := hbU32, params := #[]
  , value := .code (
      hbLetU64 `a 7 (
      hbLet `b hbU32 (.lit (.uint32 9)) (
      hbLet `pr hbObj (.ctor objCtorInfo
                      #[.fvar (hbFVar `a), .fvar (hbFVar `b)]) (
      hbLet `y hbU32 (.sproj 1 0 (hbFVar `pr)) (.return (hbFVar `y))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE BEYOND-U64 cap tooth: a Nat literal past 2^64 (99999999999999999999)
    refuses identically — the cap check is by Nat VALUE, never a u64
    wrap (the honest big-Nat boundary). -/
def natBeyondDecl : Decl .impure :=
  { name := `GuestTests.natBeyond, levelParams := []
  , type := hbTagged, params := #[]
  , value := .code (hbLetNat `v 99999999999999999999 (.return (hbFVar `v)))
  , inlineAttr? := none }

/-- The hand-built Nat decls lowered ONCE (the pure data face). -/
def natLitSmallLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [natLitSmallDecl]
def natAddOkLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [natAddOkDecl]
def natSubOkLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [natSubOkDecl]
def natSubBadLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [natSubBadDecl]
def natMulOkLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [natMulOkDecl]
def natMulOverLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [natMulOverDecl]
def natMulWrapLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [natMulWrapDecl]
def natEqTLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [(natEqDecl 5 5 `e1)]
def natEqFLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [(natEqDecl 5 9 `e2)]
def natLtTLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [(natLtDecl 5 9 `l1)]
def natLeTLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [(natLeDecl 9 9 `l2)]
def natLeFLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [(natLeDecl 9 5 `l3)]
def natCaseLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [natCaseDecl]
def natJpLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [natJpDecl]
def objRoundLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [objRoundXDecl, objRoundYDecl]
def natBeyondLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [natBeyondDecl]

/-! ## The hand-built CLOSURE + RC decls (the Correct.lean discipline)

The REAL pipeline's family (twiceAdd5's `_closed_0` fixpoint) pins the
closure CREATION; these hand-built decls pin the KNOWN-ARITY
APPLICATION (the pipeline cannot hand one over — every real consumer
of a closure applies it first-class, the indirect-call boundary) and
the RC cell's arithmetic with the MEMORY pins.
-/

open Lean.Compiler.LCNF in
/-- The pap's TARGET (the sibling): `subCap(a, b) = a - b` — arity 2,
    so a 1-arg pap leaves exactly 1 fresh arg. The ORDER-SENSITIVE op:
    a swapped marshalling (fresh args before the captured) answers
    b − a, never a − b — the control's teeth. -/
def papTargetDecl : Decl .impure :=
  let a := hbFVar `a
  let b := hbFVar `b
  let t := hbFVar `t
  let paramA := hbParam `a
  let paramB := hbParam `b
  { name := `GuestTests.subCap, levelParams := []
  , type := hbU64, params := #[paramA, paramB]
  , value := .code (hbLetFap `t `UInt64.sub #[.fvar a, .fvar b] (.return t))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The obj-typed box let (the closure decls' spelling; the names
    reconstruct their fvars structurally). -/
def hbLetBox (n : Lean.Name) (ty : Lean.Expr) (src : Lean.Name) (k : Code .impure) :
    Code .impure :=
  hbLet n hbObj (.box ty (hbFVar src)) k

open Lean.Compiler.LCNF in
/-- THE PAP + APPLICATION decl (the known-arity discipline's pin):
    `n := 5; c := pap addCap [n]; r1 := c(7); r2 := c(9); return r1 + r2`
    — the captured local feeds BOTH applications (closures are
    read-only under the model), the fresh args marshal after the
    captured, the answer is 12 + 14 = 26. -/
def papMainDecl : Decl .impure :=
  let n := hbFVar `n
  let c := hbFVar `c
  let seven := hbFVar `seven
  let r1 := hbFVar `r1
  let nine := hbFVar `nine
  let r2 := hbFVar `r2
  let s := hbFVar `s
  { name := `GuestTests.papMain, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `n 5 (
    hbLet `c hbObj (.pap `GuestTests.subCap #[.fvar (hbFVar `n)]) (
    hbLetU64 `seven 7 (
    hbLet `r1 hbU64 (.fvar c #[.fvar seven]) (
    hbLetU64 `nine 9 (
    hbLet `r2 hbU64 (.fvar c #[.fvar nine]) (
    hbLetFap `s `UInt64.add #[.fvar r1, .fvar r2] (.return s))))))))  
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE RC CELL's arithmetic pin: `v := 9; b := box v; inc b; w := unbox b;
    dec b; return b` — the box round trips (payload @8 = 9), the rc
    cell ends at 1+1−1 = 1 (read from the run's final memory), the
    tag stays 0. -/
def rcDecl : Decl .impure :=
  let v := hbFVar `v
  let b := hbFVar `b
  let w := hbFVar `w
  { name := `GuestTests.rcCell, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLetU64 `v 9 (
    hbLetBox `b hbU64 `v (
    .inc b 1 false false (
    hbLet `w hbU64 (.unbox b) (
    .dec b 1 false false none (
    .return b))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE DEAD-MARKING pin: `dec` to ZERO leaves rc=0 — the dead object
    is observable in memory; its slot is never reused (the size-class
    freelist is the named follow-up). -/
def rcDeadDecl : Decl .impure :=
  let v := hbFVar `v
  let b := hbFVar `b
  { name := `GuestTests.rcDead, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLetU64 `v 9 (
    hbLetBox `b hbU64 `v (
    .dec b 1 false false none (
    .return b))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE OVER-DEC TOOTH: a second dec on an rc=0 object breaches the
    guard — the unreach TRAP (a use-after-free bug, never a silent
    wrap). -/
def rcOverDecDecl : Decl .impure :=
  let v := hbFVar `v
  let b := hbFVar `b
  { name := `GuestTests.rcOverDec, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLetU64 `v 9 (
    hbLetBox `b hbU64 `v (
    .dec b 1 false false none (
    .dec b 1 false false none (
    .return b)))))
  , inlineAttr? := none }

def papLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [papMainDecl, papTargetDecl]
def rcLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [rcDecl]
def rcDeadLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [rcDeadDecl]
def rcOverDecLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [rcOverDecDecl]

open Lean.Compiler.LCNF in
/-- THE PAP-ARITY-DRIFT tooth: TWO captured args on an arity-2 callee
    (a full application arrives as fap — the drift is a malformed pap). -/
def papDriftDecl : Decl .impure :=
  let c := hbFVar `c
  { name := `GuestTests.papDrift, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLetU64 `n 5 (
    hbLetU64 `m 6 (
    hbLet `c hbObj (.pap `GuestTests.subCap #[.fvar (hbFVar `n), .fvar (hbFVar `m)]) (
    .return c))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE APPLICATION-ARITY-DRIFT tooth: 1 captured + 2 fresh vs the
    callee's arity 2. -/
def applyDriftDecl : Decl .impure :=
  let c := hbFVar `c
  let r := hbFVar `r
  { name := `GuestTests.applyDrift, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `n 5 (
    hbLet `c hbObj (.pap `GuestTests.subCap #[.fvar (hbFVar `n)]) (
    hbLet `r hbU64 (.fvar c #[.fvar (hbFVar `n), .fvar (hbFVar `n)]) (
    .return r))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE PAP-UNKNOWN-FN tooth: the pap's callee is not a sibling decl —
    never a fabricated function index. -/
def papUnknownDecl : Decl .impure :=
  let c := hbFVar `c
  { name := `GuestTests.papUnknown, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLetU64 `n 5 (
    hbLet `c hbObj (.pap `GuestTests.noSuchFn #[.fvar (hbFVar `n)]) (
    .return c)))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE RC-ON-SCALAR tooth: an `inc` on a u64 fvar — Perceus only RCs
    objects (the lowering-internal inconsistency). -/
def rcScalarDecl : Decl .impure :=
  { name := `GuestTests.rcScalar, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (hbLetU64 `v 9 (
    .inc (hbFVar `v) 1 false false (.return (hbFVar `v))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE FIELD CASCADE (landed): a ref-field object dies and its
    field's rc drops with it — `dec p 1 ... (some 1)`: p's rc 1→0, the
    ref field's (the box's) rc 1→0, the counts HONEST (read from the
    run's final memory; the DEEP cascade — a field's own fields — is
    the named follow-up, the count is the immediate fields). -/
def refBoxCtorInfo : CtorInfo :=
  { name := `GuestTests.RefBox.mk, cidx := 0, size := 1, usize := 0, ssize := 0 }

open Lean.Compiler.LCNF in
def cascadeDecl : Decl .impure :=
  let v := hbFVar `v
  let b := hbFVar `b
  let p := hbFVar `p
  { name := `GuestTests.cascade, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLetU64 `v 9 (
    hbLetBox `b hbU64 `v (
    hbLet `p hbObj (.ctor refBoxCtorInfo #[.fvar b]) (
    .dec p 1 false false (some 1) (
    .return p)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE CASCADE's OVER-DEC TOOTH: after the cascade dropped the
    field's rc to 0, a further dec breaches the over-dec guard — the
    unreach TRAP (the cascade's counts stay honest — the teeth). -/
def cascadeOverDecDecl : Decl .impure :=
  let v := hbFVar `v
  let b := hbFVar `b
  let p := hbFVar `p
  { name := `GuestTests.cascadeOverDec, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLetU64 `v 9 (
    hbLetBox `b hbU64 `v (
    hbLet `p hbObj (.ctor refBoxCtorInfo #[.fvar b]) (
    .dec p 1 false false (some 1) (
    .dec b 1 false false none (
    .return p))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE DEL (the honest deallocation within the arena's model): the
    ownership assertion `rc = 1` checked at runtime, then the DEAD
    MARKING (rc = 0 — observable; the size-class freelist reuse is
    the named follow-up). -/
def delDecl : Decl .impure :=
  let v := hbFVar `v
  let b := hbFVar `b
  { name := `GuestTests.delObj, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLetU64 `v 9 (
    hbLetBox `b hbU64 `v (
    .del b (
    .return b))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE DEL's OWNERSHIP TOOTH: a del on an rc=2 object — the
    statically-owned claim is CHECKED at runtime; the shared object's
    del TRAPS (never a premature free). -/
def delSharedDecl : Decl .impure :=
  let v := hbFVar `v
  let b := hbFVar `b
  { name := `GuestTests.delShared, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLetU64 `v 9 (
    hbLetBox `b hbU64 `v (
    .inc b 1 false false (
    .del b (
    .return b)))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE IN-PLACE WRITE (the scalar field, landed): `n := 42; sset pr 0 0
    n; x := sproj pr 0 0` — the write rides the SAME coordinates the
    read does (`8 + i*8 + offset`); the rc=1 legality guard passes (one
    reference); the answer 42. -/
def scalarCtorInfo : CtorInfo :=
  { name := `GuestTests.Scalar.mk, cidx := 0, size := 0, usize := 0, ssize := 1 }

open Lean.Compiler.LCNF in
def ssetDecl : Decl .impure :=
  { name := `GuestTests.ssetFn, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `a 7 (
    hbLet `b hbU32 (.lit (.uint32 9)) (
    hbLet `pr hbObj (.ctor scalarCtorInfo #[.fvar (hbFVar `a), .fvar (hbFVar `b)]) (
    hbLetU64 `n 42 (
    .sset (hbFVar `pr) 0 0 (hbFVar `n) (hbU64) (
    hbLet `x hbU64 (.sproj 0 0 (hbFVar `pr)) (
    .return (hbFVar `x))))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE IN-PLACE WRITE's LEGALITY TOOTH: the target made SHARED first
    (`inc pr` — rc = 2); the sset's rc=1 guard breaches — the unreach
    TRAP (a shared cell's in-place write would corrupt every other
    reference's view; the copy-on-shared discipline is the named
    follow-up). -/
def ssetSharedDecl : Decl .impure :=
  { name := `GuestTests.ssetShared, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `a 7 (
    hbLet `b hbU32 (.lit (.uint32 9)) (
    hbLet `pr hbObj (.ctor scalarCtorInfo #[.fvar (hbFVar `a), .fvar (hbFVar `b)]) (
    .inc (hbFVar `pr) 1 false false (
    hbLetU64 `n 42 (
    .sset (hbFVar `pr) 0 0 (hbFVar `n) (hbU64) (
    .return (hbFVar `n))))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE IN-PLACE WRITE (the ref field, landed): `oset pr 0 b2; h :=
    oproj pr 0; w := unbox h` — the pointer store at the packing law's
    ref coordinates; the read sees the NEW value (11); the DISPLACED
    reference's dec is the STREAM's obligation (b1's rc stays 1 — the
    honesty pin). -/
def osetDecl : Decl .impure :=
  { name := `GuestTests.osetFn, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `v1 9 (
    hbLetBox `b1 hbU64 `v1 (
    hbLet `p hbObj (.ctor refBoxCtorInfo #[.fvar (hbFVar `b1)]) (
    hbLetU64 `v2 11 (
    hbLetBox `b2 hbU64 `v2 (
    .oset (hbFVar `p) 0 (.fvar (hbFVar `b2)) (
    hbLet `h hbObj (.oproj 0 (hbFVar `p)) (
    hbLet `w hbU64 (.unbox (hbFVar `h)) (
    .return (hbFVar `w))))))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE REF-WRITE's LEGALITY TOOTH: the shared target's oset TRAPS
    (the same rc=1 guard). -/
def osetSharedDecl : Decl .impure :=
  let v1 := hbFVar `v1
  let b1 := hbFVar `b1
  let p := hbFVar `p
  let v2 := hbFVar `v2
  let b2 := hbFVar `b2
  { name := `GuestTests.osetShared, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `v1 9 (
    hbLetBox `b1 hbU64 `v1 (
    hbLet `p hbObj (.ctor refBoxCtorInfo #[.fvar b1]) (
    .inc p 1 false false (
    hbLetU64 `v2 11 (
    hbLetBox `b2 hbU64 `v2 (
    .oset p 0 (.fvar b2) (
    .return v2))))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE IN-PLACE WRITE (the tag byte, landed): `setTag pr 1` then the
    OBJECT DISPATCH (the tag lane — the alts' ctor infos carry fields,
    so the prescan keeps the object lane): the cidx-1 arm runs (5);
    the control (no setTag) falls to the default (6). -/
def tagCtorInfo : CtorInfo :=
  { name := `GuestTests.TagBox.other, cidx := 1, size := 1, usize := 0, ssize := 0 }

open Lean.Compiler.LCNF in
def setTagDecl : Decl .impure :=
  let p := hbFVar `p
  let r := hbFVar `r
  { name := `GuestTests.setTagFn, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `v 9 (
    hbLetBox `b hbU64 `v (
    hbLet `p hbObj (.ctor refBoxCtorInfo #[.fvar (hbFVar `b)]) (
    .setTag p 1 (
    .cases (Lean.Compiler.LCNF.Cases.mk `obj hbU64 p #[
      .ctorAlt tagCtorInfo (hbLetU64 `r 5 (.return r)),
      .default (hbLetU64 `r 6 (.return r))]))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE SETTAG CONTROL: the same dispatch WITHOUT the setTag — the
    object keeps tag 0, no cidx-0 alt exists, the default runs (6). -/
def setTagCtlDecl : Decl .impure :=
  let p := hbFVar `p
  let r := hbFVar `r
  { name := `GuestTests.setTagCtl, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `v 9 (
    hbLetBox `b hbU64 `v (
    hbLet `p hbObj (.ctor refBoxCtorInfo #[.fvar (hbFVar `b)]) (
    .cases (Lean.Compiler.LCNF.Cases.mk `obj hbU64 p #[
      .ctorAlt tagCtorInfo (hbLetU64 `r 5 (.return r)),
      .default (hbLetU64 `r 6 (.return r))])))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE EXTERN DECLARATION (the declared trust boundary): a decl whose
    body is an `extern` — the signature's faces map like any decl's;
    the lowering emits the declared function with the `unreach` body
    (the host link step is the named follow-up). -/
def extFnDecl : Decl .impure :=
  let x := hbFVar `x
  let paramX := hbParam `x
  { name := `GuestTests.extFn, levelParams := []
  , type := hbU64, params := #[paramX]
  , value := .extern { entries := [] }
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- The extern's CALLER: a sibling call to the extern (the call lane
    treats the declared boundary like any decl — the index is real). -/
def extCallerDecl : Decl .impure :=
  { name := `GuestTests.extCaller, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `x 4 (
    hbLetFap `r `GuestTests.extFn #[.fvar (hbFVar `x)] (.return (hbFVar `r))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE NON-CLOSURE TOOTH (the first-class lane's honesty): a SCALAR
    fvar applied (a UInt64 fvar has no fnIdx slot @8 — the dispatch
    would be garbage) — the `closureApplyUnknown` refusal, the lane's
    honesty face. -/
def nonClosureDecl : Decl .impure :=
  let x := hbFVar `x
  let y := hbFVar `y
  let r := hbFVar `r
  let paramX := hbParam `x
  { name := `GuestTests.nonClosure, levelParams := []
  , type := hbU64, params := #[paramX]
  , value := .code (
    hbLetU64 `y 7 (
    hbLet `r hbU64 (.fvar x #[.fvar y]) (
    .return r)))
  , inlineAttr? := none }

def nonClosureLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [nonClosureDecl]

def papDriftLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [papDriftDecl, papTargetDecl]
def applyDriftLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [applyDriftDecl, papTargetDecl]
def papUnknownLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [papUnknownDecl]
def rcScalarLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [rcScalarDecl]
def cascadeLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [cascadeDecl]
def cascadeOverDecLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [cascadeOverDecDecl]
def delLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [delDecl]
def delSharedLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [delSharedDecl]
def ssetLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [ssetDecl]
def ssetSharedLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [ssetSharedDecl]
def osetLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [osetDecl]
def osetSharedLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [osetSharedDecl]
def setTagLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [setTagDecl]
def setTagCtlLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [setTagCtlDecl]
def extLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [extFnDecl, extCallerDecl]

def toyExternLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.lowerFunc { name := "toyExt", params := [("x", .u64)]
                  , resultTy := .u64
                  , value := .extern
                      { params := [.u64], result := .u64, effect := .host
                      , note := "the toy face's declared trust boundary: \
                                 the host link step is the named follow-up" } }

open Lean.Compiler.LCNF in
/-- THE EXTERN CONTRACT's DECLARATION-DRIFT TOOTH (hand IR): the decl
    carries a u32 param but the contract declares u64 — the faces and
    the boundary's data disagree, the `externSigDrift` refusal fires
    BEFORE anything is emitted. -/
def toyExtDriftLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.lowerFunc { name := "toyExtDrift", params := [("x", .u32)]
                  , resultTy := .u64
                  , value := .extern
                      { params := [.u64], result := .u64, effect := .host
                      , note := "the contract's declared row vs the decl's" } }

/-- THE EXTERN CONTRACT's CALL-SITE-DRIFT TOOTH (hand IR): the caller
    passes a u32 row at a u64-declared boundary — the
    `externCallDrift` refusal (the call site is type-checked against
    the declared contract). -/
def toyExtCallerDecl : Guest.IR.Decl :=
  { name := "toyExtCaller", params := []
  , resultTy := .u64
  , value := .let_ { var := "x", ty := .u32, value := .litU32 4 }
      (.let_ { var := "r", ty := .u64, value := .call "toyExt" #[.var "x"] }
        (.ret "r")) }

def toyExtCallDriftLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.lowerFuncs
    [ { name := "toyExt", params := [("x", .u64)]
      , resultTy := .u64
      , value := .extern
          { params := [.u64], result := .u64, effect := .host
          , note := "the declared boundary" } }
    , toyExtCallerDecl ]

open Lean.Compiler.LCNF in
/-- THE EXTERN CONTRACT's CALL-SITE MATCH (the control): the same
    caller passing the RIGHT row (u64) lowers and validates — the
    check is the row's, not the call's existence. -/
def toyExtCallOkLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.lowerFuncs
    [ { name := "toyExt", params := [("x", .u64)]
      , resultTy := .u64
      , value := .extern
          { params := [.u64], result := .u64, effect := .host
          , note := "the declared boundary" } }
    , { name := "toyExtCallerOk", params := []
      , resultTy := .u64
      , value := .let_ { var := "x", ty := .u64, value := .litU64 4 }
          (.let_ { var := "r", ty := .u64, value := .call "toyExt" #[.var "x"] }
            (.ret "r")) } ]

/-! ## The RC reuse fixtures (the memory discipline's pins) -/

open Lean.Compiler.LCNF in
/-- THE RC REUSE's BEHAVIOR-IDENTITY PAIR, program P1 (NO del): two
    16-byte boxes; the second lands at the fresh bump (heapBase+16). -/
def reuseNoDelDecl : Decl .impure :=
  let v1 := hbFVar `v1
  let b1 := hbFVar `b1
  let v2 := hbFVar `v2
  let b2 := hbFVar `b2
  let w := hbFVar `w
  { name := `GuestTests.reuseNoDel, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `v1 9 (
    hbLetBox `b1 hbU64 `v1 (
    hbLetU64 `v2 11 (
    hbLetBox `b2 hbU64 `v2 (
    hbLet `w hbU64 (.unbox b2) (
    .return w))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE RC REUSE's PAIR, program P2 (the del between): the same two
    boxes, the first DEL'd — the second box HANDS BACK the dead slot
    (the shape match: both are 16-byte boxes). The reuse changes WHERE
    b2 lands, never WHAT the program observes. -/
def reuseDelDecl : Decl .impure :=
  let v1 := hbFVar `v1
  let b1 := hbFVar `b1
  let v2 := hbFVar `v2
  let b2 := hbFVar `b2
  let w := hbFVar `w
  { name := `GuestTests.reuseDel, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `v1 9 (
    hbLetBox `b1 hbU64 `v1 (
    .del b1 (
    hbLetU64 `v2 11 (
    hbLetBox `b2 hbU64 `v2 (
    hbLet `w hbU64 (.unbox b2) (
    .return w)))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE SHAPE-MATCH TOOTH: a 16-byte box del'd, then a 20-byte object
    (the u64+u32 scalar ctor — 8 header + 8 + 4 packed, the packing
    law's extent) allocated after — the shape MISMATCH keeps the fresh
    bump path (the dead slot stays published for a later same-size
    allocation). -/
def reuseShapeDecl : Decl .impure :=
  let v1 := hbFVar `v1
  let b1 := hbFVar `b1
  let a2 := hbFVar `a2
  let b2 := hbFVar `b2
  let obj := hbFVar `obj
  { name := `GuestTests.reuseShape, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLetU64 `v1 9 (
    hbLetBox `b1 hbU64 `v1 (
    .del b1 (
    hbLetU64 `a2 7 (
    hbLet `b2 hbU32 (.lit (.uint32 8)) (
    hbLet `obj hbObj (.ctor scalarCtorInfo #[.fvar a2, .fvar b2]) (
    .return obj)))))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE HONEST-BOUNDARY TOOTH: the del of a shape-UNKNOWN var (a
    copy's target — the allocation happened at ANOTHER variable's
    birth) passes the rc=1 guard (the copy is a local move, no rc
    change) and keeps the dead marking only — NO publish, NO reuse
    (the next box lands fresh; the cache stays empty). -/
def reuseUnknownDecl : Decl .impure :=
  let v1 := hbFVar `v1
  let b1 := hbFVar `b1
  let c := hbFVar `c
  let v2 := hbFVar `v2
  let b2 := hbFVar `b2
  let w := hbFVar `w
  { name := `GuestTests.reuseUnknown, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLetU64 `v1 9 (
    hbLetBox `b1 hbU64 `v1 (
    hbLet `c hbObj (.fvar b1 #[]) (
    .del c (
    hbLetU64 `v2 11 (
    hbLetBox `b2 hbU64 `v2 (
    hbLet `w hbU64 (.unbox b2) (
    .return w))))))))
  , inlineAttr? := none }

def reuseNoDelLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [reuseNoDelDecl]
def reuseDelLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [reuseDelDecl]
def reuseShapeLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [reuseShapeDecl]
def reuseUnknownLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [reuseUnknownDecl]

/-! ## The hand-built TAG-DISPATCH teeth (the Correct.lean discipline) -/

open Lean.Compiler.LCNF in
/-- THE CTOR-FIELD-CLASS tooth: a ctor field whose class is outside the
    layout's classification (a Char-typed fvar — the pipeline's
    enum/Char repr depends on the ctor count, unknowable from the
    lowering's data) — the named `ctorFieldClass` refusal. -/
def charFieldDecl : Decl .impure :=
  { name := `GuestTests.charField, levelParams := []
  , type := hbObj, params := #[]
  , value := .code (
    hbLet `c (Lean.Expr.const `Char []) (.lit (.uint32 5)) (
    hbLet `o hbObj (.ctor objCtorInfo #[.fvar (hbFVar `c)]) (
    .return (hbFVar `o))))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
/-- THE USIZE-FIELD-READ tooth: an `uproj` — the non-scalar payload
    shape (the usize face) — the tag dispatch's named refusal. -/
def uprojDecl : Decl .impure :=
  let o := hbFVar `o
  { name := `GuestTests.uprojFn, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (
    hbLet `o hbObj (.ctor objCtorInfo #[]) (
    hbLet `u hbU64 (.uproj 0 o) (
    .return (hbFVar `u))))
  , inlineAttr? := none }

def charFieldLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [charFieldDecl]
def uprojLowered : Except Guest.LowerError WasmCore.Module := Guest.compile [uprojDecl]

/-- Does the instruction list contain a `call`? (The INLINER-HONESTY
    scanner: `crossCall`'s small callee is inlined away by LCNF, so
    the lowered body must be call-free — the lowering sees what LCNF
    PRODUCES, and pins it here.) -/
def anyCall : List WasmCore.Instr → Bool
  | [] => false
  | .call _ :: _ => true
  | .block b :: is => anyCall b || anyCall is
  | .loop b :: is => anyCall b || anyCall is
  | .if_ t e :: is => anyCall t || anyCall e || anyCall is
  | _ :: is => anyCall is

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
  -- the cross-decl call lane (the two-decl program + the recursion)
  callAnswer : Option UInt64
  callValidates : Bool
  sumMainPin : Option UInt64
  sumRecPin : Option UInt64
  laneCallValidates : Bool
  callFuel : Option RunVerdict
  -- the inliner honesty (crossCall's small callee dissolves)
  inlineLowered : Bool
  inlineCallFree : Bool
  inlineAnswer : Option UInt64
  -- the BOXED-NAT lane (the real pipeline's face: the folded literal
  -- box end-to-end + the folded overflow's compile-time cap refusal
  -- + the 2-param tobj decls' lower-only pins)
  natMainPin : Option Nat
  natMainValidates : Bool
  foldCap : Option Nat
  natAddValidates : Bool
  natCmpValidates : Bool
  -- the boxed-Nat lane (the hand-built runtime face)
  natLitSmall : Option Nat
  hbAdd : Option Nat
  hbSub : Option Nat
  hbSubBad : Bool
  hbMulOk : Option Nat
  hbMulOver : Bool
  hbMulWrap : Bool
  hbEqT : Option UInt32
  hbEqF : Option UInt32
  hbLtT : Option UInt32
  hbLeT : Option UInt32
  hbLeF : Option UInt32
  hbJp : Option Nat
  hbJpValidates : Bool
  -- the object seed (the hand-built round trip)
  objX : Option UInt64
  objY : Option UInt32
  objValidates : Bool
  -- the CLOSURE discipline (the real pipeline's _closed fixpoint family:
  -- the closure object's layout read from the run's final memory)
  closureValidates : Bool
  closureTag : Option Nat
  closureFnIdx : Option Nat
  closureRc : Option Nat
  closureBoxPayload : Option Nat
  closureBoxRc : Option Nat
  -- the known-arity application (hand-built — the real consumers apply
  -- first-class, the indirect lane's boundary)
  papValidates : Bool
  papAnswer : Option UInt64
  -- the RC seed (the rc cell's real arithmetic, read from memory)
  rcPayload : Option Nat
  rcTag : Option Nat
  rcCell : Option Nat
  rcDeadCell : Option Nat
  rcOverDecTrap : Bool
  -- THE INDIRECT-CALL LANE (the first-class application, landed: the
  -- real pipeline's applyTwice body LOWERS; the sig registry + the
  -- identity table; the twiceAdd5 family's partial pap applied
  -- first-class answers the executor's indirectSig trap; bigMain is
  -- the SUCCESSFUL dispatch end to end)
  firstClassValidates : Bool
  firstClassSigs : Bool
  twiceValidates : Bool
  twiceTrap : Option RunVerdict
  bigValidates : Bool
  bigMain0 : Option UInt64
  bigMain5 : Option UInt64
  -- the lane's honesty (a NON-closure applied refuses — the hand-built
  -- scalar-applied tooth)
  nonClosureRefused : Bool
  nonClosureRender : String
  -- the LIST discipline (the object tag dispatch's payoff: the real
  -- pipeline's cons/nil objects + the fold through the dispatch)
  listValidates : Bool
  listAnswer : Option Nat
  listNilTag : Option Nat
  listConsTag : Option Nat
  listConsHead : Option Nat
  -- the overlap-class regression (the 3-element literal's agreement)
  list3Validates : Bool
  list3Answer : Option Nat
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

/-- The BOXED-NAT pin over a read module (the payload read face). -/
def pinNatAt (m : Except Guest.LowerError WasmCore.Module) (fn : Nat)
    (args : List WasmCore.Val) : Option Nat :=
  match m with
  | Except.ok mm => resultOfNat (WasmCore.runFunc mm fn args 2000)
  | Except.error _ => none

/-- The final stack's i32 AS AN ADDRESS, over a read module. -/
def pinPtr (m : Except Guest.LowerError WasmCore.Module) (fn : Nat)
    (args : List WasmCore.Val) : Option Nat :=
  match m with
  | Except.ok mm => ptrOf (WasmCore.runFunc mm fn args 2000)
  | Except.error _ => none

/-- The memory word at `addr` (width `w`) after a read module's run. -/
def pinMem (m : Except Guest.LowerError WasmCore.Module) (fn : Nat)
    (args : List WasmCore.Val) (w addr : Nat) : Option Nat :=
  match m with
  | Except.ok mm => memAtW w addr (WasmCore.runFunc mm fn args 2000)
  | Except.error _ => none

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
    -- THE CALL LANE: the REAL pipeline's two-decl program (sumMain
    -- calls sumTo — the recursive callee survives the inliner) + the
    -- hand-built arg-order pair + the inliner-honesty fixture.
    let dsCall ← readMulti env [`GuestTests.sumMain, `GuestTests.sumTo]
    let mCall : Except Guest.LowerError WasmCore.Module :=
      match dsCall with
      | .ok ds => lowerDecls ds
      | .error e => .error (.unsupportedConstruct "pipeline" e)
    let mInline ← rd `GuestTests.crossCall
    -- THE BOXED-NAT LANE: the real pipeline's face. natMain's
    -- operands FOLD (observed) — the module is one boxed literal;
    -- natMulRun's folded product arrives ≥ the cap — the compile-time
    -- design-error refusal; the 2-param tobj decls lower (the fap
    -- rows + the pointer type map) but take no run (boxes cannot
    -- cross the driver's arg seam — the model's boundary).
    let mNatMain ← rd `GuestTests.natMain
    let mNatMulRun ← rd `GuestTests.natMulRun
    let mNatAdd ← rd `GuestTests.natAdd
    let mNatLt ← rd `GuestTests.natLt
    let mNatEq ← rd `GuestTests.natEq
    -- THE CLOSURE FAMILY (the real pipeline's _closed fixpoint): ONE
    -- pipeline run over the ROOT (`twiceAdd5` — an internal `_closed`
    -- constant cannot root its own run), the family fetched from that
    -- run's local cache — the family module's entries (decl order):
    -- 0 = _closed_0 (the producer), 1 = _boxed_const_1, 2 = _lam_1,
    -- 3 = _lam_1._boxed. The pap's stored fnIdx is the adapter's index
    -- (3). The consumer decl `twiceAdd5` itself is NOT lowered: its
    -- `fap applyTwice` callee's body is the FIRST-CLASS application —
    -- the indirect-call lane's pinned refusal (mApply below).
    let dsCl ←
      match ← Guest.readFamily? env `GuestTests.twiceAdd5
          [`GuestTests.twiceAdd5._closed_0
          , `GuestTests.twiceAdd5._closed_0._boxed_const_1
          , `GuestTests.twiceAdd5._lam_1
          , `GuestTests.twiceAdd5._lam_1._boxed] with
      | .ok ds => pure (Except.ok ds : Except String _)
      | .error e => pure (Except.error e)
    let mCl : Except Guest.LowerError WasmCore.Module :=
      match dsCl with
      | .ok ds => lowerDecls ds
      | .error e => .error (.unsupportedConstruct "pipeline" e)
    let mApply ← rd `GuestTests.applyTwice
    -- THE INDIRECT-CALL LANE (the first-class application, landed):
    -- twiceAdd5's REAL pipeline module — the family + applyTwice —
    -- the PARTIAL pap applied first-class answers the executor's
    -- indirectSig trap (the honesty; the decl order: twiceAdd5 = 0,
    -- the family 1-4, applyTwice 5). bigMain is the SUCCESSFUL
    -- dispatch end to end: the closure (pap mkTriple._boxed) flows
    -- through useFnBig's first-class applications, the sig registry's
    -- type index, the identity table — the answers 21 / 2715. The
    -- decl order: bigMain = 0, its producer 1, the adapter 2,
    -- mkTriple 3, useFnBig 4.
    let dsTwice : Except String _ ←
      match ← Guest.readFamily? env `GuestTests.twiceAdd5
          [`GuestTests.twiceAdd5._closed_0
          , `GuestTests.twiceAdd5._closed_0._boxed_const_1
          , `GuestTests.twiceAdd5._lam_1
          , `GuestTests.twiceAdd5._lam_1._boxed] with
      | .ok ds => pure (.ok ds)
      | .error e => pure (.error e)
    let mTwice : Except Guest.LowerError WasmCore.Module :=
      match dsTwice, ← Guest.readDecl? env `GuestTests.twiceAdd5,
            ← Guest.readDecl? env `GuestTests.applyTwice with
      | .ok fam, .ok mainD, .ok appD => lowerDecls ([mainD] ++ fam ++ [appD])
      | .error e, _, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, .error e, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, _, .error e => .error (.unsupportedConstruct "pipeline" e)
    let dsBig : Except String _ ←
      match ← Guest.readFamily? env `GuestTests.bigMain
          [`GuestTests.bigMain._closed_0] with
      | .ok ds => pure (.ok ds)
      | .error e => pure (.error e)
    let dsMtFam : Except String _ ←
      match ← Guest.readFamily? env `GuestTests.mkTriple
          [`GuestTests.mkTriple._boxed] with
      | .ok ds => pure (.ok ds)
      | .error e => pure (.error e)
    let mBig : Except Guest.LowerError WasmCore.Module :=
      match dsBig, dsMtFam, ← Guest.readDecl? env `GuestTests.bigMain,
            ← Guest.readDecl? env `GuestTests.useFnBig,
            ← Guest.readDecl? env `GuestTests.mkTriple with
      | .ok bfam, .ok mtfam, .ok bmD, .ok ufbD, .ok mtD =>
          lowerDecls ([bmD] ++ bfam ++ mtfam ++ [mtD, ufbD])
      | .error e, _, _, _, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, .error e, _, _, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, _, .error e, _, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, _, _, .error e, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, _, _, _, .error e => .error (.unsupportedConstruct "pipeline" e)
    -- THE LIST DISCIPLINE (the object tag dispatch's payoff): listSum
    -- rides its OWN pipeline run (a top-level decl is not in the
    -- root's family cache — probed), the literal family rides
    -- listMain's run; the concat is ONE module (the sibs registry
    -- covers the cross-references). Module entries (decl order): 0 =
    -- listSum (the fold), 1 = _closed_2 (the literal face — the
    -- entry the run pins), 2 = _closed_1, 3 = _closed_0.
    let dListSum ← Guest.readDecl? env `GuestTests.listSum
    let dsFam ←
      match ← Guest.readFamily? env `GuestTests.listMain
          [`GuestTests.listMain._closed_2, `GuestTests.listMain._closed_1,
           `GuestTests.listMain._closed_0] with
      | .ok ds => pure (Except.ok ds : Except String _)
      | .error e => pure (Except.error e)
    let mList : Except Guest.LowerError WasmCore.Module :=
      match dListSum, dsFam with
      | .ok d, .ok fam => lowerDecls (d :: fam)
      | .error e, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, .error e => .error (.unsupportedConstruct "pipeline" e)
    -- THE OVERLAP-CLASS REGRESSION: the THREE-element literal (the
    -- size classes alternate 8/16/24 — the bump allocator's per-object
    -- advance against the cons-tail clobber). Module entries (decl
    -- order): 0 = listSum, 1 = _closed_3 (the root — the entry the run
    -- pins), 2 = _closed_2, 3 = _closed_1, 4 = _closed_0.
    let dListSum3 := dListSum
    let dsFam3 ←
      match ← Guest.readFamily? env `GuestTests.listMain3
          [`GuestTests.listMain3._closed_3, `GuestTests.listMain3._closed_2,
           `GuestTests.listMain3._closed_1, `GuestTests.listMain3._closed_0] with
      | .ok ds => pure (Except.ok ds : Except String _)
      | .error e => pure (Except.error e)
    let mList3 : Except Guest.LowerError WasmCore.Module :=
      match dListSum3, dsFam3 with
      | .ok d, .ok fam => lowerDecls (d :: fam)
      | .error e, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, .error e => .error (.unsupportedConstruct "pipeline" e)
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
        , callAnswer := pinAt callLowered 0 []
        , callValidates := pinValidates callLowered
        , sumMainPin := pinAt mCall 0 [WasmCore.Val.i64 5]
        , sumRecPin := pinAt mCall 1 [WasmCore.Val.i64 5]
        , laneCallValidates := pinValidates mCall
        , callFuel := match mCall with
          | Except.ok mm => some (runOutcomeFn mm 1 [WasmCore.Val.i64 5] 60)
          | Except.error _ => none
        , inlineLowered := match mInline with
          | Except.ok _ => true | Except.error _ => false
        , inlineCallFree := match mInline with
          | Except.ok mm => !mm.funcs.any (fun f => anyCall f.body)
          | Except.error _ => false
        , inlineAnswer := pinAt mInline 0 [WasmCore.Val.i64 6]
        , natMainPin := pinNatAt mNatMain 0 []
        , natMainValidates := pinValidates mNatMain
        , foldCap := match mNatMulRun with
          | Except.error (.natLitCap v) => some v
          | _ => none
        , natAddValidates := pinValidates mNatAdd
        , natCmpValidates := pinValidates mNatLt && pinValidates mNatEq
        , natLitSmall := pinNatAt natLitSmallLowered 0 []
        , hbAdd := pinNatAt natAddOkLowered 0 []
        , hbSub := pinNatAt natSubOkLowered 0 []
        , hbSubBad := match natSubBadLowered with
          | Except.ok mm => isUnreachTrap (WasmCore.runFunc mm 0 [] 2000)
          | Except.error _ => false
        , hbMulOk := pinNatAt natMulOkLowered 0 []
        , hbMulOver := match natMulOverLowered with
          | Except.ok mm => isUnreachTrap (WasmCore.runFunc mm 0 [] 2000)
          | Except.error _ => false
        , hbMulWrap := match natMulWrapLowered with
          | Except.ok mm => isUnreachTrap (WasmCore.runFunc mm 0 [] 2000)
          | Except.error _ => false
        , hbEqT := match natEqTLowered with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 0 [] 2000)
          | Except.error _ => none
        , hbEqF := match natEqFLowered with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 0 [] 2000)
          | Except.error _ => none
        , hbLtT := match natLtTLowered with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 0 [] 2000)
          | Except.error _ => none
        , hbLeT := match natLeTLowered with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 0 [] 2000)
          | Except.error _ => none
        , hbLeF := match natLeFLowered with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 0 [] 2000)
          | Except.error _ => none
        , hbJp := pinNatAt natJpLowered 0 []
        , hbJpValidates := pinValidates natJpLowered
        , objX := match objRoundLowered with
          | Except.ok mm => resultOf (WasmCore.runFunc mm 0 [] 2000)
          | Except.error _ => none
        , objY := match objRoundLowered with
          | Except.ok mm => resultOf32 (WasmCore.runFunc mm 1 [] 2000)
          | Except.error _ => none
        , objValidates := pinValidates objRoundLowered
        -- THE CLOSURE DISCIPLINE's pins: run the family's producer
        -- (entry 0), read the closure object's layout from the run's
        -- final memory — the tag, the adapter's fnIdx, the rc cells,
        -- the captured box's payload.
        , closureValidates := pinValidates mCl
        , closureTag :=
            match pinPtr mCl 0 [] with
            | some p => pinMem mCl 0 [] 4 (p + 4)
            | none => none
        , closureFnIdx :=
            match pinPtr mCl 0 [] with
            | some p => pinMem mCl 0 [] 4 (p + 8)
            | none => none
        , closureRc :=
            match pinPtr mCl 0 [] with
            | some p => pinMem mCl 0 [] 4 p
            | none => none
        , closureBoxPayload :=
            match pinPtr mCl 0 [] with
            | some p =>
                match pinMem mCl 0 [] 4 (p + 16) with
                | some q => pinMem mCl 0 [] 8 (q + 8)
                | none => none
            | none => none
        , closureBoxRc :=
            match pinPtr mCl 0 [] with
            | some p =>
                match pinMem mCl 0 [] 4 (p + 16) with
                | some q => pinMem mCl 0 [] 4 q
                | none => none
            | none => none
        -- THE KNOWN-ARITY APPLICATION (hand-built): subCap(5,7) +
        -- subCap(9,11) through ONE captured local, both applications
        , papValidates := pinValidates papLowered
        , papAnswer := pinAt papLowered 0 []
        -- THE RC SEED: the box round trip + the rc cell's arithmetic
        , rcPayload :=
            match pinPtr rcLowered 0 [] with
            | some p => pinMem rcLowered 0 [] 8 (p + 8)
            | none => none
        , rcTag :=
            match pinPtr rcLowered 0 [] with
            | some p => pinMem rcLowered 0 [] 4 (p + 4)
            | none => none
        , rcCell :=
            match pinPtr rcLowered 0 [] with
            | some p => pinMem rcLowered 0 [] 4 p
            | none => none
        , rcDeadCell :=
            match pinPtr rcDeadLowered 0 [] with
            | some p => pinMem rcDeadLowered 0 [] 4 p
            | none => none
        , rcOverDecTrap := match rcOverDecLowered with
          | Except.ok mm => isUnreachTrap (WasmCore.runFunc mm 0 [] 2000)
          | Except.error _ => false
        , -- THE INDIRECT-CALL LANE's pins: applyTwice's body LOWERS
          -- (the first-class application; the sig registered + the
          -- identity table present); the twiceAdd5 family's partial
          -- pap applied first-class TRAPS (indirectSig); bigMain is
          -- the successful dispatch (21 / 2715).
          firstClassValidates := pinValidates mApply
        , firstClassSigs := match mApply with
          | .ok mm => mm.tables.length == 1 && mm.types.length == 2
          | .error _ => false
        , twiceValidates := pinValidates mTwice
        , twiceTrap := match mTwice with
          | .ok mm => some (runOutcomeFn mm 0 [WasmCore.Val.i64 5] 500)
          | .error _ => none
        , bigValidates := pinValidates mBig
        , bigMain0 := pinAt mBig 0 [WasmCore.Val.i64 0]
        , bigMain5 := pinAt mBig 0 [WasmCore.Val.i64 5]
        , nonClosureRefused := match nonClosureLowered with
          | .error (.closureApplyUnknown _) => true
          | _ => false
        , nonClosureRender := match nonClosureLowered with
          | .error e => e.render
          | .ok _ => ""
        -- THE LIST DISCIPLINE: the fold's answer + the objects' tag
        -- bytes read from the run's final memory (the bump arena's
        -- determinism — the closure pins' face): the nil box's base is
        -- the arena's first address (heapBase — the allocator's addr =
        -- max(p, heapBase) discipline), the outer cons is the fifth
        -- (nil 8 + box 16 + cons 24 + box 16 = 80 = heapBase + 64).
        , listValidates := pinValidates mList
        , listAnswer := pinNatAt mList 1 []
        , listNilTag := pinMem mList 1 [] 4 (Guest.heapBase + 4)
        , listConsTag := pinMem mList 1 [] 4 (Guest.heapBase + 64 + 4)
        , listConsHead := pinMem mList 1 [] 4 (Guest.heapBase + 64 + 8)
        , list3Validates := pinValidates mList3
        , list3Answer := pinNatAt mList3 1 []
        }

/-! ## The refusal teeth (the pure faces + the real-pipeline refusals) -/

/-- The cap: a Nat literal at/above 2^62 is the DESIGN ERROR. THE
    TOY-FRONTEND FACE: the refusal is pinned on a HAND-WRITTEN IR
    program — the IR alone carries the contract (no LCNF in sight). -/
def capRefusal : Option Guest.LowerError :=
  let code : Guest.IR.Code :=
    .let_ { var := "x", ty := .nat, value := .litNat Guest.natCap } (.ret "x")
  match StateT.run (Guest.lowerCode code 1 0 .i64) ({} : Guest.LState) with
  | .error e => some e
  | .ok _ => none

/-- Below the cap: the boxed-Nat lane LOWERS (the lane landed — the
    below-cap literal allocates its box; the pin runs it end to
    end). -/
def laneLowered : Bool :=
  match natLitSmallLowered with
  | Except.ok _ => true | Except.error _ => false

/-- A fap outside the op surface refuses with the named boundary.
    THE TOY-FRONTEND FACE: a hand-written IR `call` naming no sibling
    — the lowering's own refusal (the frontend never produces one, so
    the IR alone must carry the honesty). -/
def fapRefusal : Option Guest.LowerError :=
  let code : Guest.IR.Code :=
    .let_ { var := "x", ty := .u64
          , value := .call "Some.Undefinable.Primitive" #[] } (.ret "x")
  match StateT.run (Guest.lowerCode code 1 0 .i64) ({} : Guest.LState) with
  | .error e => some e
  | .ok _ => none

open Lean.Compiler.LCNF in
/-- The cross-decl call's ARITY-DRIFT fixture (HAND-BUILT — the real
    pipeline's inliner dissolves small calls): declB's body is a fap
    naming its SIBLING declA with a WRONG ARITY (declA takes 0
    params, the fap passes 1) — lowerFuncs refuses with the named
    arity diagnostic (the GOOD sibling call lowers — callSpecs). -/
def crossDeclA : Decl .impure :=
  { name := `GuestTests.declA, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (hbLetU64 `v 3 (.return (hbFVar `v)))
  , inlineAttr? := none }

open Lean.Compiler.LCNF in
def crossDeclB : Decl .impure :=
  { name := `GuestTests.declB, levelParams := []
  , type := hbU64, params := #[]
  , value := .code (hbLetU64 `w 0 (
    hbLet `u hbU64 (.fap `GuestTests.declA #[.fvar (hbFVar `w)]) (.return (hbFVar `u))))
  , inlineAttr? := none }

def crossLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.compile [crossDeclA, crossDeclB]

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
             (RunVerdict.ok [WasmCore.Val.i64 1]))
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
               (runOutcomeFn m 0 [] 40) RunVerdict.outOfFuel
           | Except.error _ => TestingKit.assert false "unreachable")
      ]
      (h := by simp) 1 52
  ]

def callSpecs (pins : RunPins) : List TestingKit.Spec :=
  [ Spec.ofList "the cross-decl call lane: the two-decl program (helper +
      main) and the self-recursive sumTo — the executor's calling
      convention end to end"
      (fun _ => do
        TestingKit.assert pins.callValidates "the hand-built call module must validate"
        TestingKit.assertEq "callAnswer" pins.callAnswer (some 42)
        TestingKit.assert pins.laneCallValidates "the REAL pipeline's call module must validate"
        TestingKit.assertEq "sumMainPin" pins.sumMainPin (some 16)
        TestingKit.assertEq "sumRecPin" pins.sumRecPin (some 15)
        TestingKit.assertEq "callFuel" pins.callFuel (some RunVerdict.outOfFuel)
        TestingKit.assert pins.inlineLowered "crossCall must LOWER (the inlined body is in-fragment)"
        TestingKit.assert pins.inlineCallFree
          "crossCall's body must be call-free (LCNF inlined add64 away)"
        TestingKit.assertEq "inlineAnswer" pins.inlineAnswer (some 7))
      [ ("control: a swapped arg marshalling (b before a) would answer
          8-50 = the wrap of -42 — the pin demands the executor's
          param-i-to-local-i binding",
         fun _ => TestingKit.assertEq "callAnswer-swapped" pins.callAnswer
           (some 18446744073709551574))
      , ("control: an off-by-one recursion pin (sumTo 5 = 10) is caught",
         fun _ => TestingKit.assertEq "sumRecPin-wrong" pins.sumRecPin (some 10))
      , ("control: an entry-index drift (sumMain read as entry 1) is
          caught — the pin demands the decl order",
         fun _ => TestingKit.assertEq "sumEntry-drift" pins.sumMainPin
           (match pins.sumRecPin with | some v => some v | none => none))
      , ("control: the fuel honesty is a LIE (a 60-unit budget
          completes — the control demands outOfFuel; if this fires the
          recursion is bounded by something other than the budget)",
         fun _ => TestingKit.assert (pins.callFuel != some RunVerdict.outOfFuel)
           "the fuel control demands a completed run")
      , ("control: the inliner dishonesty (a call SURVIVES in
          crossCall's body — the honesty pin would be vacuous)",
         fun _ => TestingKit.assert (!pins.inlineCallFree)
           "the inliner control demands a call in the body")
      ]
      (h := by simp) 1 55
  ]

def natSpecs (pins : RunPins) : List TestingKit.Spec :=
  [ Spec.ofList "the boxed-Nat lane: the REAL pipeline's literal box end to end
      (the folded sum's box allocated, run, the payload read @8)"
      (fun _ => do
        TestingKit.assert pins.natMainValidates "natMain's module must validate"
        TestingKit.assertEq "natMain" pins.natMainPin (some 1700000000000000000)
        -- THE FOLDED OVERFLOW: the compiler's constant folding delivers
        -- the statically-overflowing product as a DIRECT literal ≥ cap —
        -- the compile-time design-error refusal (the model's honesty
        -- where static)
        TestingKit.assertEq "foldCap" pins.foldCap (some 9223372036854775804))
      [ ("control: a wrong payload pin (off by one) is caught",
         fun _ => TestingKit.assertEq "natMain-wrong" pins.natMainPin
           (some 1700000000000000001))
      , ("control: the STATIC overflow refusal is a LIE (the folded product ≥
          cap lowers — the control demands the lowering succeed; caught)",
         fun _ => TestingKit.assert (pins.foldCap == none)
           "the folded overflow must refuse at compile time")
      ]
      (h := by simp) 1 56
  , Spec.ofList "the boxed-Nat runtime face (hand-built — the compiler folds
      the real pipeline's small arith): add/sub/mul + the compare rows"
      (fun _ => do
        TestingKit.assertEq "natLitSmall" pins.natLitSmall (some 5)
        TestingKit.assertEq "hbAdd" pins.hbAdd (some 1500000000000000000)
        TestingKit.assertEq "hbSub" pins.hbSub (some 4)
        TestingKit.assertEq "hbMulOk" pins.hbMulOk (some 2305843009213693952)
        TestingKit.assertEq "hbEqT" pins.hbEqT (some 1)
        TestingKit.assertEq "hbEqF" pins.hbEqF (some 0)
        TestingKit.assertEq "hbLtT" pins.hbLtT (some 1)
        TestingKit.assertEq "hbLeT" pins.hbLeT (some 1)
        TestingKit.assertEq "hbLeF" pins.hbLeF (some 0)
        TestingKit.assert pins.hbSubBad "the sub underflow must TRAP (never wrap)"
        TestingKit.assert pins.hbMulOver "the mul past the cap must TRAP (never wrap)"
        TestingKit.assert pins.hbMulWrap "the mul past 2^64 must TRAP (the wrap-masquerade guard)")
      [ ("control: the MUL-WRAP-MASQUERADE — a lowering without the 128-bit
          guard answers the wrapped payload 0 (2⁴¹·2⁴¹ = 2⁸² wraps); the
          control demands the silent wrap and is caught",
         fun _ => TestingKit.assert (!pins.hbMulWrap)
           "the wrap guard is a lie — the control demanded the silent wrap")
      , ("control: a wrong mul answer (2⁶¹·4 off by one) is caught",
         fun _ => TestingKit.assertEq "hbMulOk-wrong" pins.hbMulOk
           (some 2305843009213693953))
      ]
      (h := by simp) 1 57
  , Spec.ofList "the boxed-Nat × jp composition: a box rides the jp param; the
      arith reads its payload twice (the answer 42)"
      (fun _ => do
        TestingKit.assert pins.hbJpValidates "natJp's module must validate"
        TestingKit.assertEq "natJp" pins.hbJp (some 42))
      [ ("control: a wrong jp answer is caught",
         fun _ => TestingKit.assertEq "natJp-wrong" pins.hbJp (some 43))
      , ("control: the jp validation pin is a LIE (the module is rejected —
          the control demands the invalid lowering; caught)",
         fun _ => TestingKit.assert (!pins.hbJpValidates)
           "the validation pin is a lie — the control demands rejection")
      ]
      (h := by simp) 1 58
  ]

def objSpecs (pins : RunPins) : List TestingKit.Spec :=
  [ Spec.ofList "the object seed: a scalar-field ctor allocated + the sproj
      reads (the legacy slot discipline, hand-built — the real pipeline's
      ctor path is the _closed closure fixpoint, the named follow-up)"
      (fun _ => do
        TestingKit.assert pins.objValidates "the object module must validate"
        TestingKit.assertEq "objX" pins.objX (some 7)
        TestingKit.assertEq "objY" pins.objY (some 9))
      [ ("control: a slot-drift read (field 1 answered from field 0's slot)
          is caught — the pin demands 9 from slot 1",
         fun _ => TestingKit.assertEq "objY-wrong" pins.objY (some 7))
      , ("control: a wrong field-0 pin is caught",
         fun _ => TestingKit.assertEq "objX-wrong" pins.objX (some 8))
      ]
      (h := by simp) 1 59
  ]

def closureSpecs (pins : RunPins) : List TestingKit.Spec :=
  [ Spec.ofList "the closure discipline: the REAL pipeline's _closed fixpoint
      family — the closure object allocated, its layout read from the run's
      final memory"
      (fun _ => do
        TestingKit.assert pins.closureValidates "the closure family's module must validate"
        TestingKit.assertEq "closureTag" pins.closureTag (some Guest.closureTag)
        TestingKit.assertEq "closureFnIdx" pins.closureFnIdx (some 3)
        TestingKit.assertEq "closureRc" pins.closureRc (some 1)
        TestingKit.assertEq "closureBoxPayload" pins.closureBoxPayload (some 5)
        TestingKit.assertEq "closureBoxRc" pins.closureBoxRc (some 2))
      [ ("control: a wrong tag (253 — the pap tag off by one) is caught",
         fun _ => TestingKit.assertEq "closureTag-wrong" pins.closureTag (some 253))
      , ("control: an fnIdx drift (the adapter read as entry 2 — the scalar
          _lam_ body — is caught); the pin demands the family's decl order",
         fun _ => TestingKit.assertEq "closureFnIdx-wrong" pins.closureFnIdx (some 2))
      , ("control: the captured box's INC is a LIE (rc stays 1 — the pin
          demands the persistent inc's 2; caught)",
         fun _ => TestingKit.assertEq "closureBoxRc-wrong" pins.closureBoxRc (some 1))
      ]
      (h := by simp) 1 60
  , Spec.ofList "the known-arity application (hand-built — the real pipeline's
      consumers apply FIRST-CLASS, the indirect lane's boundary): the captured
      local (param a) feeds BOTH applications, the fresh args marshal after
      the captured"
      (fun _ => do
        TestingKit.assert pins.papValidates "the pap module must validate"
        TestingKit.assertEq "papAnswer" pins.papAnswer (some 18446744073709551610))
      [ ("control: a swapped marshalling (fresh args BEFORE the captured)
          would answer sub(7,5) + sub(11,9) = 4 — the pin demands the
          captured-first order",
         fun _ => TestingKit.assertEq "papAnswer-swapped" pins.papAnswer (some 4))
      , ("control: a provenance loss at the second application (the captured
          local consumed by the first call) would refuse — the module must
          LOWER and answer",
         fun _ => TestingKit.assert (pins.papAnswer == none)
          "the provenance-loss control demands the refusal")
      ]
      (h := by simp) 1 61
  , Spec.ofList "the RC seed: the rc cell's real arithmetic (inc/dec at the
      honest points), the dead marking, the over-dec trap"
      (fun _ => do
        TestingKit.assertEq "rcPayload" pins.rcPayload (some 9)
        TestingKit.assertEq "rcTag" pins.rcTag (some 0)
        TestingKit.assertEq "rcCell" pins.rcCell (some 1)
        TestingKit.assertEq "rcDeadCell" pins.rcDeadCell (some 0)
        TestingKit.assert pins.rcOverDecTrap "the over-dec must TRAP (never wrap)")
      [ ("control: the rc init is a LIE (the cell starts at 0 — the pin
          demands one reference at birth; caught)",
         fun _ => TestingKit.assertEq "rcCell-wrong" pins.rcCell (some 0))
      , ("control: the dead marking is a LIE (the dec-to-zero leaves rc=1 —
          caught)",
         fun _ => TestingKit.assertEq "rcDeadCell-wrong" pins.rcDeadCell (some 1))
      , ("control: the over-dec is SILENT (the guard would not fire — caught)",
         fun _ => TestingKit.assert (!pins.rcOverDecTrap)
          "the over-dec control demands a silent wrap")
      ]
      (h := by simp) 1 62
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
      cross-decl call's ARITY drift"
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
        -- THE CALL LANE's named refusal: a sibling call whose ARITY
        -- drifts (declA takes 0 params, declB passes 1) — the
        -- malformed-call tooth (the GOOD sibling call LOWERS; the
        -- callSpecs pin proves it).
        match crossLowered with
        | Except.error (.unsupportedConstruct what detail) => do
            TestingKit.assertEq "the arity drift names the callee" what
              "fap GuestTests.declA"
            TestingKit.assertEq "the arity drift's detail" detail
              "arity 1 on a decl of arity 0"
        | Except.error e =>
            TestingKit.assert false
              s!"the cross-decl arity drift fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the cross-decl arity drift did NOT refuse"
        -- THE CTOR-CASE-ON-NAT THROW (the model's pinned loud refusal)
        match natCaseLowered with
        | Except.error .natCtorCase => .ok ()
        | Except.error e =>
            TestingKit.assert false
              s!"the Nat ctor-case fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the Nat ctor-case did NOT refuse"
        -- THE BEYOND-U64 CAP: the cap check is by Nat VALUE — a literal
        -- past 2^64 refuses identically (never a u64 wrap)
        match natBeyondLowered with
        | Except.error (.natLitCap v) =>
            TestingKit.assertEq "the beyond-u64 value" v 99999999999999999999
        | Except.error e =>
            TestingKit.assert false
              s!"the beyond-u64 literal fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the beyond-u64 literal did NOT refuse")
      [ ("control: the cap literal fires the LANE diagnostic (wrong kind — \
          the cap check comes first, the control is caught)",
         fun _ => do
           match capRefusal with
             | some (.natLane _) => .ok ()
             | some e => TestingKit.assert false (s!"the cap literal fired: {e.render} — the control demanded the lane diagnostic")
             | none => TestingKit.assert false "nothing refused")
      , ("control: the below-cap literal still refuses (wrong claim — the \
          boxed-Nat lane LANDED, the literal lowers; the control is caught)",
         fun _ => do
           TestingKit.assert (!laneLowered)
             "the below-cap literal lowered — the control demanded the old \
               refusal (wrong claim — caught)")
      , ("control: the type map maps Nat to the u64 row (wrong claim — Nat \
          rides the object rows; the control is caught)",
         fun _ =>
           TestingKit.assert
             (Guest.irTyOf? {} (Lean.Expr.const `Nat []) == some .u64)
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

def listSpecs (pins : RunPins) : List TestingKit.Spec :=
  [ Spec.ofList "the list discipline: the cons/nil objects + the tag dispatch
      driving the fold (the REAL pipeline's listSum + the literal family —
      the objects' tags read from the run's final memory)"
      (fun _ => do
        TestingKit.assert pins.listValidates "the list module must validate"
        TestingKit.assertEq "listAnswer" pins.listAnswer (some 15)
        TestingKit.assertEq "listNilTag" pins.listNilTag (some 0)
        TestingKit.assertEq "listConsTag" pins.listConsTag (some 1)
        TestingKit.assertEq "listConsHead" pins.listConsHead (some 64))
      [ ("control: a wrong fold answer (off by one) is caught",
         fun _ => TestingKit.assertEq "listAnswer-wrong" pins.listAnswer (some 16))
      , ("control: the NIL tag pin is a LIE (the nil object's tag reads 1 —
          the cons tag; the dispatch would take the cons arm on nil and
          the fold would flood — caught)",
         fun _ => TestingKit.assertEq "listNilTag-wrong" pins.listNilTag (some 1))
      ]
      (h := by simp) 1 64
  , Spec.ofList "the overlap-class regression: the 3-element literal agrees
      (the bump allocator's non-overlap law — the allocation size classes
      alternate 8/16/24; the former cons-tail clobber class)"
      (fun _ => do
        TestingKit.assert pins.list3Validates "the 3-element list module must validate"
        TestingKit.assertEq "list3Answer" pins.list3Answer (some 18))
      [ ("control: a dropped element (the clobber class regressed — the
          fold answers 15) is caught",
         fun _ => TestingKit.assertEq "list3Answer-wrong" pins.list3Answer (some 15))
      , ("control: a tampered validation (the module refused — the law
          over-closed) is caught",
         fun _ => TestingKit.assert (¬ pins.list3Validates)
           "the 3-element module validates — the control demanded a refusal")
      ]
      (h := by simp) 1 66
  ]

def listTeethSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the tag dispatch's refusal teeth: the unclassifiable ctor
      field + the non-scalar payload shapes fire the named refusals"
      (fun _ => do
        match charFieldLowered with
        | Except.error (.ctorFieldClass ty) =>
            TestingKit.assertEq "the field-class refusal names the type" ty "Char"
        | Except.error e =>
            TestingKit.assert false
              s!"the ctor field class fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the ctor field class did NOT refuse"
        match uprojLowered with
        | Except.error (.unsupportedConstruct what _) =>
            TestingKit.assertEq "the uproj refusal names the construct" what
              "projection"
        | Except.error e =>
            TestingKit.assert false
              s!"the uproj fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the uproj did NOT refuse")
      [ ("control: the GOOD list module REFUSES (wrong claim — it lowers,
          the control is caught)",
         fun _ => TestingKit.assert false
           "the good list module LOWERS (the control demanded a refusal)")
      , ("control: the field-class diagnostic carries GC99" ++ "99 (wrong code —
          ctorFieldClass's E-code is GC2022; the control is caught)",
         fun _ => do
           let r := match charFieldLowered with
             | Except.error e => e.render
             | Except.ok _ => ""
           TestingKit.assert (r.contains ("GC99" ++ "99"))
             s!"the field-class Diag carries its real code: {r}")
      ]
      (h := by simp) 1 65
  ]

def closureTeethSpecs (pins : RunPins) : List TestingKit.Spec :=
  [ Spec.ofList "the indirect-call lane's teeth: the first-class
      application LOWERS (the lane landed), the partial-pap honesty
      traps, the non-closure refusal fires; + the pap/RC teeth"
      (fun _ => do
        -- THE FIRST-CLASS APPLICATION (landed): applyTwice's body
        -- (`f _uniq.4` — the applied fvar has no pap provenance)
        -- lowers to callindirect at the sig registry's type index;
        -- the module carries the identity table + ONE sig type
        TestingKit.assert pins.firstClassValidates
          "applyTwice must LOWER (the indirect-call lane landed)"
        TestingKit.assert pins.firstClassSigs
          "applyTwice's module must carry the identity table + the sig type"
        -- THE PARTIAL-PAP HONESTY: the twiceAdd5 family's closure is a
        -- pap of the 2-param adapter (1 captured); applied first-class
        -- at the 1-arg sig, the executor's table TYPE CHECK traps —
        -- never a wrong call
        TestingKit.assert pins.twiceValidates
          "the twiceAdd5 family module must validate"
        TestingKit.assertEq "twiceTrap" pins.twiceTrap
          (some (RunVerdict.trap .indirectSig))
        -- THE SUCCESSFUL DISPATCH: bigMain end to end — the closure
        -- flows through the sibling call + useFnBig's first-class
        -- applications + the identity table; the answers 21 / 2715
        TestingKit.assert pins.bigValidates
          "the bigMain module must validate"
        TestingKit.assertEq "bigMain0" pins.bigMain0 (some 21)
        TestingKit.assertEq "bigMain5" pins.bigMain5 (some 2715)
        -- THE NON-CLOSURE REFUSAL (the lane's honesty face): a scalar
        -- fvar applied — no fnIdx slot to dispatch through
        TestingKit.assert pins.nonClosureRefused
          "a scalar fvar applied must refuse with closureApplyUnknown"
        -- the pap arity drift (2 captured on an arity-2 callee)
        match papDriftLowered with
        | Except.error (.papArityDrift _ 2 2) => .ok ()
        | Except.error e =>
            TestingKit.assert false
              s!"the pap arity drift fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the pap arity drift did NOT refuse"
        -- the application arity drift (1 captured + 2 fresh vs 2)
        match applyDriftLowered with
        | Except.error (.closureApplyArityDrift _ 3 2) => .ok ()
        | Except.error e =>
            TestingKit.assert false
              s!"the application arity drift fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the application arity drift did NOT refuse"
        -- the pap's callee is not a sibling (never a fabricated index)
        match papUnknownLowered with
        | Except.error (.papUnknownFn _) => .ok ()
        | Except.error e =>
            TestingKit.assert false
              s!"the pap unknown-fn fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the pap unknown-fn did NOT refuse"
        -- the RC-on-scalar inconsistency
        match rcScalarLowered with
        | Except.error (.rcOnScalar "inc") => .ok ()
        | Except.error e =>
            TestingKit.assert false
              s!"the rc-on-scalar fired the WRONG diagnostic: {e.render}"
        | Except.ok _ =>
            TestingKit.assert false "the rc-on-scalar did NOT refuse")
      [ ("control: the GOOD pap module REFUSES (wrong claim — it lowers,
          the control is caught)",
         fun _ => do
           match papLowered with
           | Except.error _ => .ok ()
           | Except.ok _ =>
               TestingKit.assert false
                 "the good pap module LOWERS (the control demanded a refusal)")
      , ("control: the partial-pap application SUCCEEDS (wrong claim —
          the executor's table type check traps; caught)",
         fun _ =>
           TestingKit.assertEq "twiceTrap-wrong" pins.twiceTrap
             (some (RunVerdict.ok [WasmCore.Val.i64 15])))
      , ("control: a wrong bigMain answer (the dispatch dropped a
          factor) is caught",
         fun _ => TestingKit.assertEq "bigMain0-wrong" pins.bigMain0 (some 20))
      , ("control: the non-closure diagnostic carries GC99" ++ "99 (wrong
          code — closureApplyUnknown's E-code is GC2018; the control is
          caught)",
         fun _ =>
           TestingKit.assert (pins.nonClosureRender.contains ("GC99" ++ "99"))
             s!"the non-closure Diag carries its real code: \
                {pins.nonClosureRender}")
      ]
      (h := by simp) 1 63
  ]

/-- The translation-correctness slice's runtime half (the theorem face
lives in Guest.Correct). The SOURCE half: the fixture defs' bodies,
evaluated by Lean (the static import is the fixture module's discipline
— the driver loads its OLEAN at runtime for the LCNF re-run — so the
source semantics rides the defs' unfolds, restated; the drift risk is
carried by the theorem face's build-failing extraction #guards in
Guest.Correct):
    add64 a b = a + b
    sumTo n   = if n = 0 then 0 else n + sumTo (n - 1)
    sumMain n = sumTo n + 1
    listSum   = nil => 0 | cons h t => h + listSum t -/
def correctnessSpecs (pins : RunPins) : List TestingKit.Spec :=
  [ Spec.ofList "the source-vs-execution agreement: the REAL pipeline
      fixtures' source values (the fixture defs' bodies, evaluated by
      Lean) pinned against the compiled modules' executions"
      (fun _ => do
        -- add64: the source (22 + 20) vs the execution (the compiled
        -- module's run on the SAME args)
        TestingKit.assertEq "add64-src-exec" pins.add42
          (some ((22 : UInt64) + 20))
        -- sumTo: the self-recursive source (5+4+3+2+1+0) vs the
        -- compiled recursion
        TestingKit.assertEq "sumTo-src-exec" pins.sumRecPin
          (some ((5 : UInt64) + 4 + 3 + 2 + 1 + 0))
        -- sumMain: the two-decl program's source (sumTo 5 + 1) vs
        -- execution
        TestingKit.assertEq "sumMain-src-exec" pins.sumMainPin
          (some ((5 : UInt64) + 4 + 3 + 2 + 1 + 0 + 1))
        -- listSum: the object-dispatch fold's source (7 + 8) vs
        -- execution
        TestingKit.assertEq "listSum-src-exec" pins.listAnswer
          (some (7 + 8 : Nat))
        -- the extraction pin: the REAL lowering's adder output IS the
        -- theorem face's template (the full Func value, build-pinned
        -- in Guest.Correct's #guards; re-pinned here at runtime)
        TestingKit.assert Guest.Correct.adderExtraction
          "lowerFunc's adder output must equal the fnBody template"
        TestingKit.assert (!Guest.Correct.adderExtractionBuggy)
          "the sabotaged template must NOT equal the real emission")
      [ ("control: a tampered source value for add64 (off by one) is
          caught",
         fun _ =>
           TestingKit.assertEq "add64-tampered" pins.add42
             (some ((22 : UInt64) + 20 + 1)))
      , ("control: a tampered source value for sumTo (off by one) is
          caught",
         fun _ =>
           TestingKit.assertEq "sumTo-tampered" pins.sumRecPin
             (some ((5 : UInt64) + 4 + 3 + 2 + 1 + 0 + 1)))
      , ("control: the source-vs-execution agreement BROKEN (the
          compiled execution pinned to a WRONG constant) is caught",
         fun _ =>
           TestingKit.assertEq "listSum-tampered" pins.listAnswer (some 14))
      ]
      (h := by simp) 1 62
  ]

/-! ## The toy frontend (the hand-written IR — the conformance evidence) -/

/-! ## The source fragment AS a machine (Guest.SrcMachine — wave 30's A4) -/

/-- The machine face of the adder chain: the mini-executor's run lands
    on the bindings' env, and the read at the result local is the
    source value 42 (the theorem face is `Guest.adder_machine`,
    kernel-checked; pinned here at runtime). -/
def machineSrcProp : Tape → CheckResult := fun _ => do
  TestingKit.assert
    (match srcMachine.run Correct.env40 (chainTape Correct.adderSrc) with
      | some env' => env' 3 == 42
      | none => false)
    "the source machine's adder run drifted from the source value"
  TestingKit.assert
    (Correct.evalS Correct.adderSrc Correct.env40 == 42)
    "the source value drifted"

/-- Control: the tape TRUNCATED by one binding — the run lands on the
    un-bound env, the read is the fallback 0, never the source value
    (the run tie is load-bearing). -/
def machineSrcNegDrop : Tape → CheckResult := fun _ =>
  TestingKit.assert
    (match srcMachine.run Correct.env40 (chainTape Correct.adderSrc).dropLast with
      | some env' => env' 3 == 42
      | none => false)
    "control fired: the truncated binding chain still tied"

/-- Control: the WRONG-local read (the result local is 3, not 2) — the
    landing env's discipline is pinned, not laundered. -/
def machineSrcNegRead : Tape → CheckResult := fun _ =>
  TestingKit.assert
    (match srcMachine.run Correct.env40 (chainTape Correct.adderSrc) with
      | some env' => env' 2 == 42
      | none => false)
    "control fired: the wrong-local read was accepted"

def machineSrcSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the source fragment AS a machine: the adder chain's
      machine run lands on the bindings' env (the theorem face
      Guest.adder_machine is kernel-checked)"
      machineSrcProp
      [ ("control: the truncated binding chain still tied", machineSrcNegDrop)
      , ("control: the wrong-local read accepted", machineSrcNegRead) ]
      1 42 ]

open Guest.IR in
/-- THE TOY FRONTEND's program: the adder as a HAND-WRITTEN IR decl —
    no LCNF anywhere. It is EXACTLY what the LCNF frontend produces
    for this module's LCNF face of the same program (`adderLcnfDecl`):
    the conformance check compares the two lowerings' MODULES (and
    their encoded bytes) — the proof that the IR is the whole
    contract, the lowering consumable by ANY frontend.
    (`Guest.Correct.adderDecl` pins the SAME program at the IR face —
    the theorem suite's fixture.) -/
def toyAdd : Guest.IR.Decl :=
  { name := "Guest.Correct.adder"
  , params := [("a", .u64), ("b", .u64)]
  , resultTy := .u64
  , value := .let_ { var := "c", ty := .u64
                    , value := .binop .u64add #[.var "a", .var "b"] }
            (.ret "c") }

open Lean.Compiler.LCNF in
/-- THE ADDER's LCNF decl (this module's LCNF face of the toy
    program — the old `Guest.Correct.adderDecl` fixture's spelling,
    moved here now that the Correct.lean pin rides the IR face
    directly): params a b; `c := fap UInt64.add [a, b]; return c`. -/
def adderLcnfDecl : Decl .impure :=
  let a := hbFVar `a
  let b := hbFVar `b
  let c := hbFVar `c
  let paramA := hbParam `a
  let paramB := hbParam `b
  { name := `Guest.Correct.adder, levelParams := []
  , type := hbU64, params := #[paramA, paramB]
  , value := .code (
      hbLet `c hbU64 (.fap `UInt64.add #[.fvar a, .fvar b]) (.return c))
  , inlineAttr? := none }

def toyAddLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.lowerFunc toyAdd

/-- The CONFORMANCE check: the hand-written IR's module == the LCNF
    frontend's module for the same program (`adderLcnfDecl`) (the
    full Module value, BEq) AND the encoded BYTES tie (the wire
    face). -/
def toyConformance : Bool :=
  match toyAddLowered, Guest.compile [adderLcnfDecl] with
  | .ok m1, .ok m2 =>
      m1 == m2
        && WasmCore.encodeModule m1
          == WasmCore.encodeModule m2
  | _, _ => false

/-- The toy run: 40 + 2 = 42 through the hand-written IR (the
    executor never asks which frontend produced the IR). -/
def toyRun : Option UInt64 :=
  match toyAddLowered with
  | .ok m => resultOf (WasmCore.runFunc m 0
              [WasmCore.Val.i64 2, WasmCore.Val.i64 40] 500)
  | .error _ => none

open Guest.IR in
/-- The toy frontend's negative control: a hand-written IR `jmp` with
    no jp — the lowering's OWN `jpUnregistered` refusal (the IR alone
    carries the discipline's teeth; the frontend is not the police). -/
def toyUnregLowered : Except Guest.LowerError WasmCore.Module :=
  Guest.lowerFunc { name := "toyUnreg", params := [], resultTy := .u64
                  , value := .jmp "L" #[] }

def toySpecs : List TestingKit.Spec :=
  [ Spec.ofList "the toy frontend: a HAND-WRITTEN IR program rides the
      lowering — its module equals the LCNF frontend's (the bytes tie)
      and it runs (40 + 2 = 42)"
      (fun _ => do
        TestingKit.assert toyConformance
          "the hand-written IR's module must equal the LCNF frontend's"
        TestingKit.assertEq "toyRun" toyRun (some 42))
      [("control: the conformance is a LIE (the modules differ — caught)",
         fun _ => TestingKit.assert (!toyConformance)
           "the conformance control demanded a module mismatch")
      , ("control: the toy negative (an unregistered jmp via hand IR) \
          lowers (wrong claim — the refusal fires; caught)",
         fun _ => do
           match toyUnregLowered with
           | .ok _ => .ok ()
           | .error _ =>
               TestingKit.assert false
                 "the toy unregistered-jmp REFUSED — the control demanded \
                   it lower (wrong claim — caught)")]
      (h := by simp) 1 67
  ]

/-! ## The RC cascade + the del (the honest deallocation's pins) -/

/-- The run outcome of a lowered module (the refusal face answers
    unmodeled — the specs' accessor). -/
def runOf (m : Except Guest.LowerError WasmCore.Module) (fn : Nat)
    (args : List WasmCore.Val) : WasmCore.Outcome :=
  match m with
  | .ok mm => WasmCore.runFunc mm fn args 2000
  | .error _ => .unmodeled

def rcSuiteSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the RC cascade: the dying object's ref field's rc \
      drops with it (the counts stay honest, read from memory)"
      (fun _ => do
        TestingKit.assert (pinValidates cascadeLowered)
          "the cascade module must validate"
        -- the box (b) is the FIRST allocation (heapBase), the ref
        -- object (p) the second (heapBase + 16)
        TestingKit.assertEq "cascade-p-rc"
          (memAtW 4 (Guest.heapBase + 16) (runOf cascadeLowered 0 []))
          (some 0))
      [("control: the field's rc did NOT drop (the lie is caught)",
         fun _ => TestingKit.assertEq "cascade-b-rc"
           (memAtW 4 Guest.heapBase (runOf cascadeLowered 0 [])) (some 1))
      , ("control: the payload corrupted by the cascade (caught)",
         fun _ => TestingKit.assertEq "cascade-payload"
           (memAtW 8 (Guest.heapBase + 8) (runOf cascadeLowered 0 []))
           (some 8))
      ]
      (h := by simp) 1 71
  , Spec.ofList "the cascade's over-dec tooth: a dec past the \
      cascaded field's zero TRAPS (the counts stay honest)"
      (fun _ =>
        TestingKit.assert (isUnreachTrap (runOf cascadeOverDecLowered 0 []))
          "the over-dec after the cascade must trap")
      [("control: the cascaded dec LOWERS (wrong claim — it must; the \
          control is the trap's absence being asserted wrong)",
         fun _ =>
           TestingKit.assert (!pinValidates cascadeOverDecLowered)
             "the control demanded the module NOT validate (caught)")
      , ("control: the plain cascade module traps (wrong claim — caught)",
         fun _ =>
           TestingKit.assert (isUnreachTrap (runOf cascadeLowered 0 []))
             "the control demanded the good cascade trap (caught)")
      ]
      (h := by simp) 1 72
  , Spec.ofList "the del: the ownership assertion (rc = 1) passes, \
      the dead marking lands (rc = 0, the payload intact; no reuse)"
      (fun _ => do
        TestingKit.assert (pinValidates delLowered)
          "the del module must validate"
        TestingKit.assertEq "del-rc"
          (memAtW 4 Guest.heapBase (runOf delLowered 0 [])) (some 0)
        TestingKit.assertEq "del-payload"
          (memAtW 8 (Guest.heapBase + 8) (runOf delLowered 0 [])) (some 9))
      [("control: the del left the object alive (the lie is caught)",
         fun _ => TestingKit.assertEq "del-rc-wrong"
           (memAtW 4 Guest.heapBase (runOf delLowered 0 [])) (some 1))
      , ("control: the del wiped the payload (caught)",
         fun _ => TestingKit.assertEq "del-payload-wrong"
           (memAtW 8 (Guest.heapBase + 8) (runOf delLowered 0 [])) (some 0))
      ]
      (h := by simp) 1 73
  , Spec.ofList "the del's ownership tooth: a del on a SHARED object \
      (rc = 2) TRAPS — never a premature free"
      (fun _ =>
        TestingKit.assert (isUnreachTrap (runOf delSharedLowered 0 []))
          "the shared object's del must trap")
      [("control: the owned del traps (wrong claim — caught)",
         fun _ =>
           TestingKit.assert (isUnreachTrap (runOf delLowered 0 []))
             "the control demanded the owned del trap (caught)")
      , ("control: the shared del marks dead anyway (caught)",
         fun _ =>
           TestingKit.assertEq "delShared-rc"
             (match runOf delSharedLowered 0 [] with
              | .ok s => some (WasmCore.readLE 4 Guest.heapBase s.mem)
              | _ => none) (some 0))
      ]
      (h := by simp) 1 74
  ]

/-! ## The in-place writes (the mutation family's pins) -/

def mutationSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the in-place write (the scalar field): sset rides \
      the SAME coordinates the sproj read does (42 through the write)"
      (fun _ => do
        TestingKit.assert (pinValidates ssetLowered)
          "the sset module must validate"
        TestingKit.assertEq "sset-read" (resultOf (runOf ssetLowered 0 []))
          (some 42)
        TestingKit.assertEq "sset-memory"
          (memAtW 8 (Guest.heapBase + 8) (runOf ssetLowered 0 []))
          (some 42))
      [("control: the write did not land (the read sees the OLD 7 — caught)",
         fun _ => TestingKit.assertEq "sset-old"
           (resultOf (runOf ssetLowered 0 [])) (some 7))
      , ("control: the write's memory face wrong (caught)",
         fun _ => TestingKit.assertEq "sset-mem-wrong"
           (memAtW 8 (Guest.heapBase + 8) (runOf ssetLowered 0 []))
           (some 7))
      ]
      (h := by simp) 1 75
  , Spec.ofList "the in-place write's legality: a SHARED cell's sset \
      (rc = 2) TRAPS — the loud refusal, never a silent corruption"
      (fun _ =>
        TestingKit.assert (isUnreachTrap (runOf ssetSharedLowered 0 []))
          "the shared cell's sset must trap")
      [("control: the owned write traps (wrong claim — caught)",
         fun _ =>
           TestingKit.assert (isUnreachTrap (runOf ssetLowered 0 []))
             "the control demanded the owned sset trap (caught)")
      , ("control: the shared write lands silently (caught)",
         fun _ =>
           TestingKit.assertEq "ssetShared-landed"
             (resultOf (runOf ssetSharedLowered 0 [])) (some 42))
      ]
      (h := by simp) 1 76
  , Spec.ofList "the in-place write (the ref field): oset stores the \
      NEW pointer (the read sees 11); the displaced reference's dec is \
      the stream's obligation (b1's rc stays 1 — the honesty pin)"
      (fun _ => do
        TestingKit.assert (pinValidates osetLowered)
          "the oset module must validate"
        TestingKit.assertEq "oset-read" (resultOf (runOf osetLowered 0 []))
          (some 11)
        TestingKit.assertEq "oset-displaced-rc"
          (memAtW 4 Guest.heapBase (runOf osetLowered 0 [])) (some 1))
      [("control: the read sees the OLD value (the store did not land — caught)",
         fun _ => TestingKit.assertEq "oset-old"
           (resultOf (runOf osetLowered 0 [])) (some 9))
      , ("control: the oset silently dec'd the displaced ref (caught)",
         fun _ => TestingKit.assertEq "oset-displaced-rc-wrong"
           (memAtW 4 Guest.heapBase (runOf osetLowered 0 [])) (some 0))
      ]
      (h := by simp) 1 77
  , Spec.ofList "the ref write's legality: a SHARED target's oset \
      TRAPS (the same rc=1 guard)"
      (fun _ =>
        TestingKit.assert (isUnreachTrap (runOf osetSharedLowered 0 []))
          "the shared target's oset must trap")
      [("control: the owned oset traps (wrong claim — caught)",
         fun _ =>
           TestingKit.assert (isUnreachTrap (runOf osetLowered 0 []))
             "the control demanded the owned oset trap (caught)")
      , ("control: the shared oset lands (caught)",
         fun _ =>
           TestingKit.assertEq "osetShared-landed"
             (resultOf (runOf osetSharedLowered 0 [])) (some 11))
      ]
      (h := by simp) 1 78
  , Spec.ofList "the in-place write (the tag byte): setTag turns the \
      dispatch (the cidx-1 arm runs — 5; the no-setTag control runs \
      the default — 6)"
      (fun _ => do
        TestingKit.assert (pinValidates setTagLowered)
          "the setTag module must validate"
        TestingKit.assertEq "setTag-dispatch"
          (resultOf (runOf setTagLowered 0 [])) (some 5)
        TestingKit.assertEq "setTag-control"
          (resultOf (runOf setTagCtlLowered 0 [])) (some 6)
        TestingKit.assertEq "setTag-memory"
          (memAtW 4 (Guest.heapBase + 16 + 4) (runOf setTagLowered 0 []))
          (some 1))
      [("control: the setTag did not turn the dispatch (caught)",
         fun _ => TestingKit.assertEq "setTag-wrong"
           (resultOf (runOf setTagLowered 0 [])) (some 6))
      , ("control: the CONTROL mutated (caught)",
         fun _ => TestingKit.assertEq "setTag-ctl-wrong"
           (resultOf (runOf setTagCtlLowered 0 [])) (some 5))
      ]
      (h := by simp) 1 79
  ]

/-! ## The RC reuse (the memory discipline's pins) -/

def reuseSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the RC reuse: the del'd box's slot is HANDED BACK to
      the next same-size allocation (the shape match), and the
      behavior is IDENTICAL to the same program without the del (the
      reuse is a memory discipline, invisible to the semantics)"
      (fun _ => do
        TestingKit.assert (pinValidates reuseDelLowered)
          "the reuse module must validate"
        -- the BEHAVIOR IDENTITY: both programs return 11 — the del
        -- + reuse changed where the box landed, never what it holds
        TestingKit.assertEq "reuse-behavior"
          (resultOf (runOf reuseDelLowered 0 []))
          (resultOf (runOf reuseNoDelLowered 0 []))
        -- the address face: P2's bump did NOT advance past the first
        -- box (the reuse handed the slot back); P1's did
        TestingKit.assertEq "reuse-bump"
          (memAtW 4 0 (runOf reuseDelLowered 0 [])) (some (Guest.heapBase + 16))
        TestingKit.assertEq "reuse-bump-fresh"
          (memAtW 4 0 (runOf reuseNoDelLowered 0 []))
          (some (Guest.heapBase + 32))
        -- the cache cleared on the reuse (the slot is spent)
        TestingKit.assertEq "reuse-cache"
          (memAtW 4 Guest.rcCacheSizeOff (runOf reuseDelLowered 0 [])) (some 0))
      [("control: the reuse did NOT fire (the no-reuse address — caught)",
         fun _ => TestingKit.assertEq "reuse-bump-wrong"
           (memAtW 4 0 (runOf reuseDelLowered 0 [])) (some (Guest.heapBase + 32)))
      , ("control: the reused box kept the DEAD payload (caught)",
         fun _ => TestingKit.assertEq "reuse-dead-payload"
           (resultOf (runOf reuseDelLowered 0 [])) (some 9))
      ]
      (h := by simp) 1 90
  , Spec.ofList "the reuse's shape-match tooth: a 16-byte box del'd,
      then a 20-byte object — the shape MISMATCH keeps the fresh bump
      path (the dead slot stays published, the cache not cleared)"
      (fun _ => do
        TestingKit.assert (pinValidates reuseShapeLowered)
          "the shape-match module must validate"
        TestingKit.assertEq "shape-fresh"
          (ptrOf (runOf reuseShapeLowered 0 []))
          (some (Guest.heapBase + 16))
        TestingKit.assertEq "shape-cache-kept"
          (memAtW 4 Guest.rcCacheSizeOff (runOf reuseShapeLowered 0 []))
          (some 16))
      [("control: the mismatched shape reused the slot (caught)",
         fun _ => TestingKit.assertEq "shape-reuse-wrong"
           (ptrOf (runOf reuseShapeLowered 0 [])) (some Guest.heapBase))
      , ("control: the mismatch cleared the cache (caught)",
         fun _ => TestingKit.assertEq "shape-cache-cleared"
           (memAtW 4 Guest.rcCacheSizeOff (runOf reuseShapeLowered 0 []))
           (some 0))
      ]
      (h := by simp) 1 91
  , Spec.ofList "the reuse's honest boundary: a shape-UNKNOWN del (a
      copy's target) passes the rc=1 guard, keeps the dead marking
      only — no publish (the cache stays empty), no reuse (the next
      box lands fresh)"
      (fun _ => do
        TestingKit.assert (pinValidates reuseUnknownLowered)
          "the unknown-shape module must validate"
        TestingKit.assertEq "unknown-no-publish"
          (memAtW 4 Guest.rcCacheSizeOff (runOf reuseUnknownLowered 0 []))
          (some 0)
        TestingKit.assertEq "unknown-no-reuse"
          (memAtW 4 0 (runOf reuseUnknownLowered 0 []))
          (some (Guest.heapBase + 32)))
      [("control: the copy's del published the slot (caught)",
         fun _ => TestingKit.assertEq "unknown-publish-wrong"
           (memAtW 4 Guest.rcCacheSizeOff (runOf reuseUnknownLowered 0 []))
           (some 16))
      , ("control: the del blocked the second allocation (caught)",
         fun _ => TestingKit.assertEq "unknown-bump-wrong"
           (memAtW 4 0 (runOf reuseUnknownLowered 0 []))
           (some (Guest.heapBase + 16)))
      ]
      (h := by simp) 1 92
  ]

/-! ## The extern face (the declared trust boundary's pins) -/

def externSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the extern declaration: the signature lands (the \
      module validates, TWO exports), the body is the declared trust \
      boundary — running it TRAPS (the host link is the named \
      follow-up), and the sibling call reaches the same boundary"
      (fun _ => do
        TestingKit.assert (pinValidates extLowered)
          "the extern module must validate"
        TestingKit.assertEq "extern-exports"
          (match extLowered with
           | .ok mm => some mm.exports.length
           | .error _ => none) (some 2)
        TestingKit.assert (isUnreachTrap (runOf extLowered 0 [WasmCore.Val.i64 4]))
          "the extern's own entry must trap (the unmodeled body)"
        TestingKit.assert (isUnreachTrap (runOf extLowered 1 []))
          "the caller's call into the extern must trap (the boundary)")
      [("control: the extern ANSWERS (wrong claim — caught)",
         fun _ => TestingKit.assertEq "extern-answer"
           (resultOf (runOf extLowered 0 [WasmCore.Val.i64 4])) (some 4))
      , ("control: the call lane SKIPS the boundary (caught)",
         fun _ => TestingKit.assertEq "extern-call"
           (resultOf (runOf extLowered 1 [])) (some 4))
      ]
      (h := by simp) 1 80
  , Spec.ofList "the toy extern: a HAND-WRITTEN IR extern decl rides \
      lowerFunc directly (the IR alone carries the trust-boundary face)"
      (fun _ => do
        TestingKit.assert (pinValidates toyExternLowered)
          "the toy extern must validate"
        TestingKit.assert
          (isUnreachTrap (runOf toyExternLowered 0 [WasmCore.Val.i64 1]))
          "the toy extern must trap")
      [("control: the toy extern answers (caught)",
         fun _ => TestingKit.assertEq "toy-extern"
           (resultOf (runOf toyExternLowered 0 [WasmCore.Val.i64 1]))
           (some 1))
      , ("control: the toy extern does not validate (caught)",
         fun _ => TestingKit.assert (!pinValidates toyExternLowered)
           "the control demanded the module be rejected (caught)")
      ]
      (h := by simp) 1 81
  , Spec.ofList "the extern contract's DECLARATION check: the decl's
      faces must match the contract the ctor carries (a u32 param
      against a u64-declared boundary refuses BEFORE anything is
      emitted — an undeclared/skewed boundary never lands)"
      (fun _ => do
        match toyExtDriftLowered with
        | .error e =>
            TestingKit.assert ((Guest.LowerError.render e).contains "GC2024")
              s!"the sig-drift Diag must carry its real code GC2024: \
                 {Guest.LowerError.render e}"
        | .ok _ =>
            TestingKit.assert false
              "the drifted contract did NOT refuse (the boundary is skewed)")
      [("control: the matching contract refuses (caught)",
         fun _ => TestingKit.assert (!pinValidates toyExternLowered)
           "the control demanded the matching contract be rejected (caught)")
      , ("control: the drifted contract LANDS (caught)",
         fun _ => TestingKit.assert (pinValidates toyExtDriftLowered)
           "the control demanded the drift be accepted (caught)")
      ]
      (h := by simp) 1 93
  , Spec.ofList "the extern contract's CALL-SITE check: a call passing
      a u32 row at a u64-declared boundary refuses (externCallDrift);
      the right row lowers and validates (the check is the row's,
      not the call's existence)"
      (fun _ => do
        match toyExtCallDriftLowered with
        | .error e =>
            TestingKit.assert ((Guest.LowerError.render e).contains "GC2025")
              s!"the call-drift Diag must carry its real code GC2025: \
                 {Guest.LowerError.render e}"
        | .ok _ =>
            TestingKit.assert false
              "the drifted call did NOT refuse (the marshalling would skew)")
      [("control: the well-rowed call refuses (caught)",
         fun _ => TestingKit.assert (!pinValidates toyExtCallOkLowered)
           "the control demanded the matched call be rejected (caught)")
      , ("control: the drifted call LANDS (caught)",
         fun _ => TestingKit.assert (pinValidates toyExtCallDriftLowered)
           "the control demanded the drift be accepted (caught)")
      ]
      (h := by simp) 1 94
  , Spec.ofList "the extern contract as DATA: the well-rowed call site
      validates (the contract rode the ctor; the call lane consumed
      it — the declared boundary with its effect row and trust note)"
      (fun _ =>
        TestingKit.assert (pinValidates toyExtCallOkLowered)
          "the well-rowed extern call must validate")
      [("control: the module was rejected (caught)",
         fun _ => TestingKit.assert (!pinValidates toyExtCallOkLowered)
           "the control demanded rejection (caught)")
      , ("control: the module traps at LOWER time (wrong claim — the
          boundary is runtime, caught)",
         fun _ => TestingKit.assertEq "call-ok-lower"
           (match toyExtCallOkLowered with | .error _ => true | .ok _ => false)
           true)
      ]
      (h := by simp) 1 95
  ]

/-! ## The driver -/

unsafe def main : IO UInt32 := do
  -- The std battery's pins first (the P2 merge: the ex-GuestStdTests
  -- specs joined this runner; its pins' IO face computed here so a
  -- pipeline failure reports under the std driver's own label).
  match ← stdComputePins with
  | .error e =>
      IO.eprintln s!"GuestStdTests: PIPELINE FAILED — {e}"
      return 1
  | .ok stdPins =>
    match ← computePins with
    | .error e =>
        IO.eprintln s!"GuestTests: PIPELINE FAILED — {e}"
        return 1
    | .ok pins =>
        TestingKit.mainOfSuites
          ([ ("the end-to-end pin", endToEndSpecs pins)
        , ("the control flow growth", jpSpecs pins)
        , ("the cross-decl call lane", callSpecs pins)
        , ("the boxed-Nat lane", natSpecs pins)
        , ("the object seed", objSpecs pins)
        , ("the list discipline", listSpecs pins)
        , ("the closure discipline", closureSpecs pins)
        , ("the refusal teeth", teethSpecs)
        , ("the tag-dispatch teeth", listTeethSpecs)
        , ("the closure teeth", closureTeethSpecs pins)
        , ("the toy frontend", toySpecs)
        , ("the RC cascade + the del", rcSuiteSpecs)
        , ("the RC reuse", reuseSpecs)
        , ("the in-place writes", mutationSpecs)
        , ("the extern face", externSpecs)
        , ("the translation-correctness slice", correctnessSpecs pins)
        , ("the source machine (A4)", machineSrcSpecs)
        , ("the effects lane", GuestTests.Deriv.derivSpecs) ]
        ++ GuestTests.Edge.edgeSuites
        ++ stdSuites stdPins)
