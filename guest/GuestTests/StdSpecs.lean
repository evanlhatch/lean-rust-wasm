/-
# GuestTests.StdSpecs — the guest std library's test battery (the specs)

The std functions' pins + the compiled-vs-native agreements + the
refusal teeth + the mandatory negative controls (15-patterns #5). The
driver owns the unsafe IO (the importModules + the LCNF re-run — the
GuestTests pattern); the suites consume the computed results as data.

Suites:

1. `the string-oracle pins` — the StrOps oracle bodies' native
   semantics on the ASCII rows (the differential oracle's authority)
   + the closed-universe metadata folds (`runtimeName`/
   `resultWasmTy`/`ofName?` — ONE place per spelling).
2. `the list-ops oracle pins` — the guest-fragment utilities' native
   semantics + the spec theorems' evaluated faces.
3. `the guest-mark discipline` — the elaboration gate's registry: the
   `@[guest_std]` marks replay from the oleans (the compile roots) +
   the ban LEVELS' pure pins (strict bans String; std allows it; Nat
   arithmetic banned at both).
4. `the compiled-vs-native agreement` — the std folds lowered through
   the REAL pipeline (LCNF → `Guest.compile` → the validator) and
   executed: the 2-element fold's compiled answer IS the native
   answer (the per-function dual evidence; Correct.lean's lane owns
   the general theorem) + the std modules validate.
5. `the 3-element agreement row` — the former known-divergence row,
   FIXED: the 3-element literal's compiled answer AGREES with the
   native (the bump allocator's non-overlap law — the object's address
   is the bump pointer, the bump advances past the object; the
   allocator bug had the next allocation start at prev_addr + sz_NEXT,
   clobbering the cons tail field). The agreement pin holds forever —
   the divergence can never return quietly.
6. `the refusal teeth (the std boundary)` — the string oracle's
   lowering REFUSES (the fap outside the op surface — the honest
   boundary: the intrinsics' compiled lane is the backend's name
   mapping, the named follow-up) + the negative controls.

-/

import Guest
import WasmCore
import LintKit.GuestBan
import TestingKit.Harness
import Guest.Std

open Guest WasmCore TestingKit

/-! ## The driver's IO face (the GuestTests pattern) -/

/-- Import the fixture module in-process (the LCNF re-run's env —
    the marks replay with `loadExts := true`). -/
unsafe def stdImportFixture : IO (Except String Lean.Environment) := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.searchPathRef.set (".lake/build/lib/lean" :: (← Lean.searchPathRef.get))
  try
    let env ← Lean.importModules #[{ module := `GuestTests.StdFixture }]
      (opts := Guest.lcnfOptions) (loadExts := true)
    return .ok env
  catch e =>
    return .error s!"importModules failed: {toString e}"

/-- Read ONE decl + lower it (the LOWERERROR ctor kept — the teeth
    assert on the failure KIND). -/
unsafe def stdReadAndLower (env : Lean.Environment) (target : Lean.Name) :
    IO (Except Guest.LowerError WasmCore.Module) := do
  match ← Guest.readDecl? env target with
  | .error e => return .error (.unsupportedConstruct "pipeline" e)
  | .ok d => return Guest.compile [d]

/-- The one-root family read (the `_closed` producers + the nested
    `_boxed_const` boxes — the observed spellings, pinned exactly per
    root; a name outside the root's cache refuses loudly). -/
unsafe def readFam (env : Lean.Environment) (root : Lean.Name)
    (names : List Lean.Name) :
    IO (Except String (List (Lean.Compiler.LCNF.Decl .impure))) :=
  Guest.readFamily? env root names

/-- The 2-element literal family (the pinned spellings). -/
def demoSum2Family (root : Lean.Name := `GuestTests.StdFixture.demoSum2) :
    List Lean.Name :=
  [ Lean.Name.mkStr root "_closed_2"
  , Lean.Name.mkStr root "_closed_1"
  , Lean.Name.mkStr (Lean.Name.mkStr root "_closed_1") "_boxed_const_1"
  , Lean.Name.mkStr root "_closed_0"
  , Lean.Name.mkStr (Lean.Name.mkStr root "_closed_0") "_boxed_const_1" ]

/-- The 3-element literal family (the pinned spellings). -/
def demoSumFamily (root : Lean.Name := `GuestTests.StdFixture.demoSum) :
    List Lean.Name :=
  [ Lean.Name.mkStr root "_closed_3"
  , Lean.Name.mkStr root "_closed_2"
  , Lean.Name.mkStr (Lean.Name.mkStr root "_closed_2") "_boxed_const_1"
  , Lean.Name.mkStr root "_closed_1"
  , Lean.Name.mkStr (Lean.Name.mkStr root "_closed_1") "_boxed_const_1"
  , Lean.Name.mkStr root "_closed_0"
  , Lean.Name.mkStr (Lean.Name.mkStr root "_closed_0") "_boxed_const_1" ]

/-! ## The execution face -/

/-- The i64 result of a completed run (the pin's accessor). -/
def stdResultOf : WasmCore.Outcome → Option UInt64
  | .ok s => match s.stack with
    | [WasmCore.Val.i64 v] => some v
    | _ => none
  | _ => none

/-- The module stdValidates. -/
def stdValidates (m : WasmCore.Module) : Bool :=
  match WasmCore.checkModule m with
  | .ok () => true | .error _ => false

/-- The validation pin over the read face. -/
def stdValidatesP (m : Except Guest.LowerError WasmCore.Module) : Bool :=
  match m with | .ok mm => stdValidates mm | .error _ => false

/-- The compiled answer of a lowered module's entry 0 (no args). -/
def compiledOf (m : Except Guest.LowerError WasmCore.Module) :
    Option UInt64 :=
  match m with
  | Except.ok mm => stdResultOf (WasmCore.runFunc mm 0 [] 2000)
  | Except.error _ => none

/-- The pinned std marks (the compile roots — the registry's expected
    content after the Fixture + GuestStd replay). -/
def expectedMarks : List Lean.Name :=
  [ `GuestTests.StdFixture.demoLen, `GuestTests.StdFixture.demoSum2
  , `GuestTests.StdFixture.demoSum
  , `GuestStd.sumU64, `GuestStd.listLenU64
  , `GuestStd.strof, `GuestStd.streq, `GuestStd.strcat, `GuestStd.strlen ]

/-! ## The pins -/

structure StdRunPins where
  -- the std modules (the folds' own lowering faces)
  sumU64Validates : Bool
  listLenU64Validates : Bool
  -- the 2-element agreement (the compiled answer + the native face)
  demoSum2Validates : Bool
  demoSum2Compiled : Option UInt64
  -- the 3-element agreement row (the flipped pin)
  demoSumValidates : Bool
  demoSumCompiled : Option UInt64
  -- the string oracle's compiled-lane refusal (the honest boundary)
  strlenRefused : Bool
  strlenRefusalKind : String
  -- the registry replay
  marks : List Lean.Name
  deriving Inhabited

unsafe def stdComputePins : IO (Except String StdRunPins) := do
  match ← stdImportFixture with
  | .error e => return .error e
  | .ok env =>
    let mSum ← stdReadAndLower env `GuestStd.sumU64
    let mLen ← stdReadAndLower env `GuestStd.listLenU64
    -- the 2-element agreement program: root + fold sibling + family
    let d2? ← Guest.readDecl? env `GuestTests.StdFixture.demoSum2
    let s? ← Guest.readDecl? env `GuestStd.sumU64
    let fam2? ← readFam env `GuestTests.StdFixture.demoSum2 (demoSum2Family)
    let mDemo2 : Except Guest.LowerError WasmCore.Module :=
      match d2?, s?, fam2? with
      | .ok d, .ok s, .ok fam => Guest.compile (d :: s :: fam)
      | .error e, _, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, .error e, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, _, .error e => .error (.unsupportedConstruct "pipeline" e)
  -- the 3-element agreement program (same shape; the former
  -- known-divergence target — the allocator's non-overlap law fixed it)
    let d3? ← Guest.readDecl? env `GuestTests.StdFixture.demoSum
    let fam3? ← readFam env `GuestTests.StdFixture.demoSum (demoSumFamily)
    let mDemo3 : Except Guest.LowerError WasmCore.Module :=
      match d3?, s?, fam3? with
      | .ok d, .ok s, .ok fam => Guest.compile (d :: s :: fam)
      | .error e, _, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, .error e, _ => .error (.unsupportedConstruct "pipeline" e)
      | _, _, .error e => .error (.unsupportedConstruct "pipeline" e)
    -- the string oracle's compiled-lane refusal (the honest boundary)
    let mStrlen ← stdReadAndLower env `GuestStd.strlen
    let strlenRefusalKind : String :=
      match mStrlen with
      | .error e => (e.render.take 12).toString
      | .ok _ => "NO REFUSAL"
    return .ok
      { sumU64Validates := stdValidatesP mSum
      , listLenU64Validates := stdValidatesP mLen
      , demoSum2Validates := stdValidatesP mDemo2
      , demoSum2Compiled := compiledOf mDemo2
      , demoSumValidates := stdValidatesP mDemo3
      , demoSumCompiled := compiledOf mDemo3
      , strlenRefused := match mStrlen with | .error _ => true | .ok _ => false
      , strlenRefusalKind := strlenRefusalKind
      , marks := LintKit.GuestGate.guestMarkedDecls env }

/-! ## The suites -/

/-- 1. The string-oracle pins (the native differential oracle). -/
def strOpsSpecs : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList "the string-oracle pins"
      (fun _ => do
        TestingKit.assertEq "strlen oracle" (GuestStd.strlen "hello world") 11
        TestingKit.assertEq "strlen empty" (GuestStd.strlen "") 0
        TestingKit.assertEq "strcat oracle" (GuestStd.strcat "hello " "guest") "hello guest"
        TestingKit.assertEq "strcat left-empty" (GuestStd.strcat "" "b") "b"
        TestingKit.assertEq "streq reflexive" (GuestStd.streq "hello" "hello") true
        TestingKit.assertEq "streq length-mismatch" (GuestStd.streq "hello" "hell") false
        TestingKit.assertEq "streq content-mismatch" (GuestStd.streq "abcdef" "abcxyz") false
        TestingKit.assertEq "strof ascii" (GuestStd.strof (String.toList "pq")) "pq"
        TestingKit.assertEq "strof empty" (GuestStd.strof []) "")
      [ ("control: a tampered strlen (the oracle dropped a byte) is caught",
         fun _ => TestingKit.assertEq "strlen-wrong" (GuestStd.strlen "hello world") 10)
      , ("control: a tampered streq (the content check skipped) is caught",
         fun _ => TestingKit.assertEq "streq-wrong" (GuestStd.streq "abcdef" "abcxyz") true)
      ]
      1 41 (h := by simp)

  -- the closed universe's metadata folds (ONE place per spelling)
  , TestingKit.Spec.ofList "the intrinsic metadata folds"
      (fun _ => do
        TestingKit.assertEq "runtimeName strlen"
          (GuestStd.Intrinsic.runtimeName .strlen) "string_len"
        TestingKit.assertEq "runtimeName strcat"
          (GuestStd.Intrinsic.runtimeName .strcat) "string_cat"
        TestingKit.assertEq "runtimeName streq"
          (GuestStd.Intrinsic.runtimeName .streq) "string_eq"
        TestingKit.assertEq "runtimeName strof"
          (GuestStd.Intrinsic.runtimeName .strof) "string_oflist"
        TestingKit.assertEq "resultWasmTy strlen"
          (GuestStd.Intrinsic.resultWasmTy .strlen) "i64"
        TestingKit.assertEq "resultWasmTy strcat"
          (GuestStd.Intrinsic.resultWasmTy .strcat) "i32"
        TestingKit.assertEq "ofName? wrapper"
          (GuestStd.Intrinsic.ofName? `GuestStd.strlen) (some .strlen)
        TestingKit.assertEq "ofName? decEq"
          (GuestStd.Intrinsic.ofName? `String.decEq) (some .streq)
        TestingKit.assertEq "ofName? BEq"
          (GuestStd.Intrinsic.ofName? `instBEqString.beq) (some .streq)
        TestingKit.assertEq "ofName? ofList"
          (GuestStd.Intrinsic.ofName? `String.ofList) (some .strof)
        TestingKit.assertEq "ofName? unknown"
          (GuestStd.Intrinsic.ofName? `GuestStd.unknown) none)
      [ ("control: a wrong runtimeName (the emit arm would call a missing
          primitive) is caught",
         fun _ => TestingKit.assertEq "runtimeName-wrong"
           (GuestStd.Intrinsic.runtimeName .strlen) "string_len_x")
      , ("control: ofName? accepting the unknown name (a folded-in spelling
          drift) is caught",
         fun _ => TestingKit.assertEq "ofName?-wrong"
           (GuestStd.Intrinsic.ofName? `GuestStd.unknown) (some .strlen))
      ]
      1 42 (h := by simp)
  ]

/-- 2. The list-ops oracle pins (the native face + the spec theorems). -/
def listOpsSpecs : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList "the list-ops oracle pins"
      (fun _ => do
        TestingKit.assertEq "sumU64 oracle" (GuestStd.sumU64 [7, 8, 3]) 18
        TestingKit.assertEq "sumU64 empty" (GuestStd.sumU64 []) 0
        TestingKit.assertEq "listLenU64 oracle" (GuestStd.listLenU64 ["a", "b", "c", "d"]) 4
        TestingKit.assertEq "listLenU64 empty" (GuestStd.listLenU64 []) 0
        -- the spec theorems' evaluated faces (the count tie + the fold tie)
        TestingKit.assertEq "listLenU64_eq_length"
          ((GuestStd.listLenU64 ["a", "b", "c"]).toNat) 3
        TestingKit.assertEq "sumU64_eq_foldr"
          (GuestStd.sumU64 [9, 1]) (([9, 1] : List UInt64).foldr (· + ·) 0)
        TestingKit.assertEq "strlen_strcat"
          (GuestStd.strlen (GuestStd.strcat "hello " "guest"))
          (GuestStd.strlen "hello " + GuestStd.strlen "guest"))
      [ ("control: a tampered sumU64 (the cons arm dropped a tail) is caught",
         fun _ => TestingKit.assertEq "sumU64-wrong" (GuestStd.sumU64 [7, 8, 3]) 15)
      , ("control: a tampered listLenU64 (the nil arm counted) is caught",
         fun _ => TestingKit.assertEq "listLenU64-wrong" (GuestStd.listLenU64 []) 1)
      ]
      1 43 (h := by simp)
  ]

/-- 3. The guest-mark discipline (the registry replay + the ban levels). -/
def markSpecs (pins : StdRunPins) : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList "the guest-mark discipline"
      (fun _ => do
        TestingKit.assert (pins.marks.length ≥ expectedMarks.length)
          s!"the mark registry replayed {pins.marks.length} marks — expected at
             least {expectedMarks.length}: {repr pins.marks}"
        TestingKit.assert
          (expectedMarks.all (fun n => pins.marks.contains n))
          s!"the registry misses a std compile root: {repr pins.marks}")
      [ ("control: an unmarked name reads as a compile root (a forged
          registry row) is caught",
         fun _ => TestingKit.assert (pins.marks.contains `GuestStd.Intrinsic.strlen)
           "the FORGED row control: `GuestStd.Intrinsic.strlen` is unmarked — the claim must fail")
      , ("control: a tampered mark list (the fold dropped the oracle
          wrappers) is caught",
         fun _ => TestingKit.assert ((pins.marks.filter (· != `GuestStd.strcat)).isEmpty)
           "the LOSSY-replay control: the registry kept `GuestStd.strcat` — the claim must fail")
      ]
      1 44 (h := by simp)

  -- the ban LEVELS (the pure predicate — the gate's teeth, unit-pinned)
  , TestingKit.Spec.ofList "the ban levels (the pure predicate)"
      (fun _ => do
        -- strict bans String (the app surface); std allows it
        TestingKit.assert (LintKit.GuestBan.bannedAt? .strict `String.length |>.isSome)
          "strict must ban String"
        TestingKit.assert (LintKit.GuestBan.bannedAt? .std `String.length |>.isNone)
          "std must allow String"
        -- Nat arithmetic banned at BOTH levels (GMP)
        TestingKit.assert (LintKit.GuestBan.bannedAt? .std `Nat.add |>.isSome)
          "std must ban Nat arithmetic"
        TestingKit.assert (LintKit.GuestBan.bannedAt? .strict `Nat.add |>.isSome)
          "strict must ban Nat arithmetic"
        -- the IO family banned at both
        TestingKit.assert (LintKit.GuestBan.bannedAt? .std `IO.println |>.isSome)
          "std must ban IO"
        TestingKit.assert (LintKit.GuestBan.bannedAt? .std `Task.map |>.isSome)
          "std must ban Task"
        -- match-only Nat is std-legal (the ctor dispatch, no GMP)
        TestingKit.assert (LintKit.GuestBan.bannedAt? .std `Nat.succ |>.isNone)
          "std must allow match-only Nat (the ctor dispatch)"
        -- UInt64 ops are the guest's fixed-width face — legal
        TestingKit.assert (LintKit.GuestBan.bannedAt? .std `UInt64.add |>.isNone)
          "std must allow UInt64 (the fixed-width face)")
      [ ("control: the strict level opening String (the level collapse) is caught",
         fun _ => TestingKit.assert (LintKit.GuestBan.bannedAt? .strict `String.length |>.isNone)
           "strict opened String — the levels collapsed")
      , ("control: the std level opening Nat arithmetic (the GMP leak) is caught",
         fun _ => TestingKit.assert (LintKit.GuestBan.bannedAt? .std `Nat.mul |>.isNone)
           "std opened Nat arithmetic — the GMP leak")
      ]
      1 45 (h := by simp)
  ]

/-- 4. The compiled-vs-native agreement (the per-function dual evidence). -/
def agreementSpecs (pins : StdRunPins) : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList "the compiled-vs-native agreement"
      (fun _ => do
        -- the std folds' modules validate (the lowering accepts the std shape)
        TestingKit.assert pins.sumU64Validates "the sumU64 module did not validate"
        TestingKit.assert pins.listLenU64Validates "the listLenU64 module did not validate"
        TestingKit.assert pins.demoSum2Validates "the demoSum2 module did not validate"
        -- THE AGREEMENT: the 2-element fold's compiled answer IS the native
        -- answer (the oracle body's eval — Correct.lean's lane owns the
        -- general theorem; this is the per-function evidence)
        TestingKit.assertEq "demoSum2 compiled vs native"
          pins.demoSum2Compiled (some (GuestStd.sumU64 [7, 8])))
      [ ("control: a tampered compiled answer (the fold dropped a cons) is caught",
         fun _ => TestingKit.assertEq "demoSum2-wrong" pins.demoSum2Compiled (some 7))
      , ("control: a tampered native eval (the oracle drifted from the spec)
          is caught",
         fun _ => TestingKit.assertEq "native-wrong"
           (GuestStd.sumU64 [7, 8]) (19 : UInt64))
      ]
      1 46 (h := by simp)

  -- the validator's teeth over a std module: the good module must NOT
  -- refuse (the paired control for suite 6's refusal row)
  , TestingKit.Spec.ofList "the std module's validator accepts"
      (fun _ => do
        TestingKit.assert pins.sumU64Validates
          "the validator refused the std fold's module")
      [ ("control: a tampered stdValidates pin (claiming a refusal) is caught",
         fun _ => TestingKit.assert (¬ pins.sumU64Validates)
           "the good std module validated — the control demanded a refusal")
      , ("control: the listLenU64 module answering a validation (drift) is caught",
         fun _ => TestingKit.assert (¬ pins.listLenU64Validates)
           "the DRIFT control: the listLenU64 module stdValidates — the claim must fail")
      ]
      1 47 (h := by simp)
  ]

/-- 5. The 3-element agreement row (the former known-divergence pin,
    flipped: the allocator's non-overlap law fixed the cons-tail
    clobber). -/
def divergenceSpecs (pins : StdRunPins) : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList "the 3-element agreement row (the divergence fixed)"
      (fun _ => do
        -- THE FLIPPED ROW: the 3-element literal LOWERS, VALIDATES, and
        -- answers the NATIVE sum (was the pinned-wrong 15 — the bump
        -- allocator's overlap bug; the fix is allocSeq's non-overlap
        -- law: bump = addr + sz, never addr as the next object's base).
        TestingKit.assertEq "demoSum3 agreement (the fixed answer)"
          pins.demoSumCompiled (some (GuestStd.sumU64 [7, 8, 3])))
      [ ("control: a tampered 3-element answer (the fold drops an element
          again) is caught",
         fun _ => TestingKit.assertEq "demoSum3-wrong" pins.demoSumCompiled (some 15))
      , ("control: a tampered native eval (the oracle drifted from the spec)
          is caught",
         fun _ => TestingKit.assertEq "demoSum3-native-wrong"
           (GuestStd.sumU64 [7, 8, 3]) (19 : UInt64))
      ]
      1 48 (h := by simp)
  ]

/-- 6. The refusal teeth (the std's honest boundary). -/
def refusalSpecs (pins : StdRunPins) : List TestingKit.Spec :=
  [ TestingKit.Spec.ofList "the refusal teeth (the std boundary)"
      (fun _ => do
        -- the string oracle's body does NOT compile (yet): the fap
        -- outside the op surface — the named boundary. The intrinsics'
        -- compiled lane is the backend's NAME mapping (StrOps' header),
        -- the named follow-up.
        TestingKit.assert pins.strlenRefused "the strlen lowering did NOT refuse"
        TestingKit.assert (pins.strlenRefusalKind.startsWith "[GC2004]")
          s!"the strlen refusal fired the WRONG E-code: {pins.strlenRefusalKind}")
      [ ("control: the good std fold refusing (the boundary over-closed) is caught",
         fun _ => TestingKit.assert (¬ pins.strlenRefused)
           "the sumU64 lowering refused — the boundary over-closed")
      , ("control: a wrong refusal kind (the module-level pipeline error)
          is caught",
         fun _ => TestingKit.assertEq "refusal-kind-wrong"
           pins.strlenRefusalKind "pipelinex")
      ]
      1 49 (h := by simp)
  ]

/-! ## The suites (the runner is GuestTests.Main's driver — the P2
    merge: the ex-GuestStdTests exe's groups appended to its
    `mainOfSuites` list; the pins' IO face is all this module runs —
    the suite assembly below is pure over the pins) -/

/-- The std battery's pins (the IO face the driver runs). -/
unsafe def stdPins : IO (Except String StdRunPins) := stdComputePins

/-- The std battery's suite groups (pure over the pins; `Spec` is
    `Type 1`, so only the pins cross the IO face). -/
def stdSuites (stdPins : StdRunPins) : List (String × List TestingKit.Spec) :=
  [("the string-oracle pins", strOpsSpecs)
  , ("the list-ops oracle pins", listOpsSpecs)
  , ("the guest-mark discipline", markSpecs stdPins)
  , ("the compiled-vs-native agreement", agreementSpecs stdPins)
  , ("the 3-element agreement row", divergenceSpecs stdPins)
  , ("the refusal teeth", refusalSpecs stdPins)]
