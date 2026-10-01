/-
# GuestTests.EdgeSpecs — the SECOND FRONTEND's test battery

The edgepython frontend's teeth (15-patterns #5): the PARITY face (the
text surface reads; the junk refuses), the CHECK face (the lattice's
refusals — the repr-split teeth, the packing-law class set, the index
discipline), the LOWERING face (the Py AST → IR → the SHARED lowering
→ module), and THE END-TO-END: the surface text → wasm → the
EXECUTOR's answer — pinned against the PYTHON reference semantics
(`Py.pyEval`, the parity set's authority — the legacy Parity.lean's
discipline, run as runtime assertions, NOT native_decide theorems: the
native-policy gate's allowlist is empty and stays empty).

The parity set is the LEGACY's fixture set (`EdgePython.lean`) —
`double`, `adder`, `dec1`, `loop_sum`, `if_max` — GROWN by E6's
productive fragment: `ops_mix` (the comparison/logic/negation
spellings over the EXISTING binop rows), `tup_second` (the tuple
literal + the index read, nested), `list_sum` (the list literal + the
`for` cons-walk), `list_head` (the head read) — the same scalar
program shapes plus the object faces, now through the IR SEAM.

The mandatory negative controls: the parser's junk refusals, the
checker's type refusals (a bool return, a bool arith operand — the
repr split — an int `not` operand, a bool list element, a
heterogeneous literal, a dynamic index, a deep list index), the
loop-boundary refusal, and the parity controls (a tampered
expectation, a swapped operand order) — each must FAIL (the sweep's
vacuity guard).

The five questions (notes/v3/01-core.md): test data (no root, no
carrier, no spine, rung n/a); the GuestTests gate row covers it.
-/

import Guest
import Guest.EdgePython.Fe
import WasmCore
import TestingKit.Harness
import TestingKit.Spec
import ComponentTests.EdgeFixture

namespace GuestTests.Edge

open Guest WasmCore TestingKit

/-! ## The fixture surface (the legacy's parity set + E6's fragment, as
    TEXT — the ONE copy lives in `ComponentTests.EdgeFixture`, the
    component lane's wasmtime face shares it; this namespace re-exports
    the fixture's products under the battery's names). -/

open ComponentTests.EdgeFixture (edgeSrc edgeFns edgeCore idxOf)

/-- The compiled module (the pipeline's product; a compile failure is
    the EMPTY module — every execution pin fails loudly against it,
    the legacy `fixturesModule` discipline). -/
def edgeModule : WasmCore.Module := ComponentTests.EdgeFixture.edgeCore

/-! ## The execution face -/

def runAt (name : String) (args : List Int) : WasmCore.Outcome :=
  ComponentTests.EdgeFixture.execAt name args

/-- The i64 result of a completed run. -/
def resultOf : WasmCore.Outcome → Option Int :=
  ComponentTests.EdgeFixture.resultOf

/-- The PYTHON model's answer (the parity oracle). -/
def pyAt (name : String) (args : List Int) : Option Int :=
  ComponentTests.EdgeFixture.pyAt name args

def validates : Bool :=
  match WasmCore.checkModule edgeModule with
  | .ok _ => true
  | .error _ => false

/-! ## The suites -/

/-! ## the drawn-text sweep (08 §11 over the EdgePython surface; no
    printer exists for the Py surface — `Guest.EdgePython.Parse`'s
    header names the boundary — so the accepted fragment's honest pin
    is the VALUE face: the parsed AST carries the drawn pieces) -/

/-- The drawn expression fragments (the productive face's shapes —
    every one inside the accepted language). -/
def exprTable : List String :=
  ["1", "x + 1", "x < 1", "not (x < 1)", "(1, 2)", "[1, 2]", "x"]

/-- The drawn surface text's property: HALF the draws are legal
one-fn modules (the parsed AST must carry the drawn name, the drawn
param, the drawn expr — the value-level round trip), half are the
same module with the header's COLON dropped (the refusal must be the
STRUCTURED envelope — `parseProgram`'s Diag rendering, never an
unstructured failure). Both verdicts are data: the parser is total
over the drawn texts, never panics. -/
def surfaceProp : Tape → CheckResult := fun t => do
  let (kind, t1) := t.below 2
  let (fi, t2) := t1.below 2
  let (pi, t3) := t2.below 2
  let (ei, _) := t3.below (exprTable.length.toUInt64)
  let f := ["f", "g"][fi]!
  let p := ["x", "y"][pi]!
  let e := exprTable[ei]!
  if kind == 0 then
    match Guest.EdgePython.Parse.parseProgram s!"def {f}({p}):\n  return {e}" with
    | .ok fns =>
        -- the parsed AST carries the drawn pieces (the value-level
        -- round trip; the Py surface has no printer)
        assert (fns.length == 1
          && (fns.headD ⟨"", [], []⟩).name == f
          && (fns.headD ⟨"", [], []⟩).params == [p])
          s!"the AST lost the drawn pieces ({f}({p}))"
    | .error m =>
        assert false s!"the legal module refused: {m}"
  else
    match Guest.EdgePython.Parse.parseProgram s!"def {f}({p})\n  return {e}" with
    | .ok _ => assert false "the colon-less header parsed"
    | .error m =>
        assert (m.startsWith "edgepython parse:")
          s!"the refusal was unstructured: {m}"

def edgeParseSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the parity face: the parity set's text reads back \
      (the nine fns, the params in order)"
      (fun _ =>
        TestingKit.assertEq "edge-fns"
          (edgeFns.map (fun f => (f.name, f.params)))
          [("double", ["x"]), ("adder", ["a", "b"]), ("dec1", ["n"]),
           ("loop_sum", ["n"]), ("if_max", ["a", "b"]),
           ("ops_mix", ["a", "b"]), ("tup_second", ["a", "b"]),
           ("list_sum", ["n"]), ("list_head", ["n"])])
      [("control: the parity face REFUSES junk (wrong claim — caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Parse.parseProgram
                  "def f(:\n  return 1" with
            | .ok _ => true | .error _ => false)
           "the control demanded the junk parse (caught)")
      , ("control: the parity face ACCEPTS the excluded string literal \
          (wrong claim — caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Parse.parseProgram
                  "def f(x):\n  return \"ab\"" with
            | .ok _ => true | .error _ => false)
           "the control demanded the string literal parse (caught)")
      ]
      (h := by simp) 1 91
  , Spec.ofList "the parse refusals: the indentation discipline (a \
      flat body refuses, a tab indent refuses, a bad dedent refuses)"
      (fun _ => do
        TestingKit.assert
          (match Guest.EdgePython.Parse.parseProgram
                 "def f(x):\nreturn x" with
           | .ok _ => false | .error _ => true)
          "a non-indented body must refuse"
        TestingKit.assert
          (match Guest.EdgePython.Parse.parseProgram
                 "def f(x):\n\treturn x" with
           | .ok _ => false | .error _ => true)
          "a tab-indented body must refuse"
        TestingKit.assert
          (match Guest.EdgePython.Parse.parseProgram
                 "def f(x):\n  return x\n   return x" with
           | .ok _ => false | .error _ => true)
          "a bad dedent must refuse")
      [("control: the indentation discipline accepts a legal module \
          (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Parse.parseProgram edgeSrc with
            | .ok _ => false | .error _ => true)
           "the control demanded edgeSrc be refused (caught)")
      , ("control: the tab face accepts a space-indented body (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Parse.parseProgram
                  "def f(x):\n  return x" with
            | .ok _ => false | .error _ => true)
           "the control demanded the legal body be refused (caught)")
      ]
      (h := by simp) 1 92
  , Spec.ofList "the drawn-text sweep (08 §11): drawn surface texts — \
      the accepted fragment parses to the drawn pieces, the refusals \
      are the structured envelope"
      surfaceProp
      [("control: the colon-less header PARSES (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Parse.parseProgram "def f(x)\n  return 1" with
            | .ok _ => true | .error _ => false)
           "the control demanded the junk parse (caught)")
      , ("control: the legal module REFUSES (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Parse.parseProgram "def f(x):\n  return 1" with
            | .ok _ => false | .error _ => true)
           "the control demanded the legal module be refused (caught)")
      ]
      24 91
  ]

def edgeCheckSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the check refusals: a bool return, a bool call arg, \
      a duplicate fn name"
      (fun _ => do
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def h(x):\n  b = x < 1\n  return b" |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
          "a bool return must refuse"
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def i(x):\n  b = x < 1\n  return j(b)\n\ndef j(y):\n  return y"
                |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
          "a bool call arg must refuse"
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def d(x):\n  return x\n\ndef d(y):\n  return y"
                |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
          "a duplicate fn name must refuse")
      [("control: the checker accepts the parity set (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Fe.lowerProgram edgeFns with
            | .ok _ => false | .error _ => true)
           "the control demanded the parity set be refused (caught)")
      , ("control: the checker refuses a legal int return (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Fe.lowerProgram edgeFns with
            | .ok ds => !(ds.length == 9) | .error _ => true)
           "the control demanded the checked decls be wrong (caught)")
      ]
      (h := by simp) 1 93
  , Spec.ofList "THE REPR-SPLIT teeth: bool arith operands, an int \
      logic operand, mixed-typed literals"
      (fun _ => do
        -- a bool operand for `+` refuses (i32 into the i64 lane = the
        -- invalid-module face, caught at CHECK)
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def r1(x):\n  b = x < 1\n  return b + 1" |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
          "a bool arith operand must refuse"
        -- an int operand for `not` refuses (the mirror face)
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def r2(x):\n  return not x" |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
          "an int `not` operand must refuse"
        -- a bool LIST element refuses (the packing law's class set)
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def r3(x):\n  xs = [x < 1, x < 2]\n  return 0" |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
          "a bool list element must refuse"
        -- a heterogeneous literal refuses
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def r4(x):\n  xs = [1, x < 2]\n  return 0" |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
          "a heterogeneous list literal must refuse"
        -- a DYNAMIC index refuses (the named deferral)
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def r5(x):\n  t = (1, 2)\n  return t[x]" |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
          "a dynamic index must refuse"
        -- a deep LIST index refuses (the bounds-checked walk's deferral)
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def r6(x):\n  xs = [1, 2]\n  return xs[1]" |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
          "a deep list index must refuse")
      [("control: the teeth ACCEPT the same shapes typed honestly \
          (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Fe.lowerProgram
              (Guest.EdgePython.Parse.parseProgram
                 "def ok1(x):\n  b = x < 1\n  c = not b\n  return x + 1"
                 |>.toOption |>.getD [])
             with
             | .ok _ => false | .error _ => true)
           "the control demanded the honest shapes be refused (caught)")
      , ("control: the teeth fire on the parity set (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Fe.lowerProgram edgeFns with
            | .ok _ => false | .error _ => true)
           "the control demanded the parity set be refused (caught)")
      ]
      (h := by simp) 1 99
  , Spec.ofList "the lowering's boundary: a loop-carried variable must \
      be bound BEFORE the loop (the entry args' face — while AND for)"
      (fun _ => do
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def w(n):\n  while n < 5:\n    m = n + 1\n    n = m\n  return n"
                |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
           "the while loop-boundary refusal must fire"
        TestingKit.assert
          (match Guest.EdgePython.Fe.lowerProgram
             (Guest.EdgePython.Parse.parseProgram
                "def f(n):\n  for x in [1, 2]:\n    m = x + 1\n  return m"
                |>.toOption |>.getD [])
           with
           | .ok _ => false | .error _ => true)
           "the for loop-boundary refusal must fire")
      [("control: the boundary accepts a pre-bound loop var (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Fe.lowerProgram
              (Guest.EdgePython.Parse.parseProgram
                 "def w(n):\n  m = 0\n  while n < 5:\n    m = n + 1\n    n = m\n  return n"
                 |>.toOption |>.getD [])
             with
             | .ok _ => false | .error _ => true)
           "the control demanded the legal loop be refused (caught)")
      , ("control: the boundary fires on the parity set (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Fe.lowerProgram edgeFns with
            | .ok _ => false | .error _ => true)
           "the control demanded the parity set be refused (caught)")
      ]
      (h := by simp) 1 94
  ]

/-- The parity pin: the executor's answer == the Python model's. -/
def parityPin (name : String) (args : List Int) : Bool :=
  resultOf (runAt name args) == pyAt name args

def edgeEndToEndSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the pipeline: the surface text → IR → the SHARED \
      lowering → the module VALIDATES"
      (fun _ => TestingKit.assert validates
        "the compiled edgepython module must validate")
      [("control: the parity set FAILS validation (caught)",
         fun _ => TestingKit.assert (!validates)
           "the control demanded the module be rejected (caught)")
      , ("control: the pipeline refuses the excluded `%` (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Fe.compileModule "def f(x):\n  return x % 2" with
            | .ok _ => true | .error _ => false)
           "the control demanded the junk compile (caught)")
      ]
      (h := by simp) 1 95
  , Spec.ofList "the executor answers: double 21 = 42, adder 40+2 = 42, \
      dec1 5 = 4 (the i64 surface)"
      (fun _ => do
        TestingKit.assertEq "double-21" (resultOf (runAt "double" [21])) (some 42)
        TestingKit.assertEq "adder-42" (resultOf (runAt "adder" [40, 2])) (some 42)
        TestingKit.assertEq "dec1-4" (resultOf (runAt "dec1" [5])) (some 4))
      [("control: double 21 = 43 (caught)",
         fun _ => TestingKit.assertEq "double-wrong"
           (resultOf (runAt "double" [21])) (some 43))
      , ("control: dec1's operand order SWAPPED answers 1 (caught)",
         fun _ => TestingKit.assert
           (resultOf (runAt "dec1" [5]) == some 1)
           "the control demanded the swapped answer (caught)")
      ]
      (h := by simp) 1 96
  , Spec.ofList "the loop + the branch + THE E6 FACES: loop_sum 10 = 45, \
      if_max takes both routes, ops_mix's spellings, the tuple/list \
      reads, the for walk"
      (fun _ => do
        TestingKit.assertEq "loop_sum-45" (resultOf (runAt "loop_sum" [10])) (some 45)
        TestingKit.assertEq "loop_sum-0" (resultOf (runAt "loop_sum" [0])) (some 0)
        TestingKit.assertEq "if_max-9a" (resultOf (runAt "if_max" [3, 9])) (some 9)
        TestingKit.assertEq "if_max-9b" (resultOf (runAt "if_max" [9, 3])) (some 9)
        -- the comparison/logic/negation spellings (the ring's faces;
        -- the wrapped-u64 answers — `0 - 3` wraps to 2^64-3)
        TestingKit.assertEq "ops_mix-3-9"
          (resultOf (runAt "ops_mix" [3, 9])) (some 18446744073709551610)
        TestingKit.assertEq "ops_mix-9-3" (resultOf (runAt "ops_mix" [9, 3])) (some 6)
        TestingKit.assertEq "ops_mix-5-5"
          (resultOf (runAt "ops_mix" [5, 5])) (some 18446744073709551611)
        TestingKit.assertEq "ops_mix-2-1" (resultOf (runAt "ops_mix" [2, 1])) (some 1)
        -- the tuple literal + the (nested) index reads
        TestingKit.assertEq "tup_second-15" (resultOf (runAt "tup_second" [3, 9])) (some 15)
        TestingKit.assertEq "tup_second-40" (resultOf (runAt "tup_second" [10, 20])) (some 40)
        -- the list literal + the for cons-walk + the head read
        TestingKit.assertEq "list_sum-16" (resultOf (runAt "list_sum" [10])) (some 16)
        TestingKit.assertEq "list_sum-6" (resultOf (runAt "list_sum" [0])) (some 6)
        TestingKit.assertEq "list_head-42" (resultOf (runAt "list_head" [42])) (some 42))
      [("control: loop_sum 10 = 44 (caught)",
         fun _ => TestingKit.assertEq "loop-wrong"
           (resultOf (runAt "loop_sum" [10])) (some 44))
      , ("control: ops_mix's `a - b` operand order SWAPPED (caught)",
         fun _ => TestingKit.assert
           (resultOf (runAt "ops_mix" [9, 3]) == some 18446744073709551610)
           "the control demanded the swapped answer (caught)")
      ]
      (h := by simp) 1 97
  , Spec.ofList "THE PARITY: the compiled wasm == the Python reference \
      semantics on the parity set, at multiple points"
      (fun _ => do
        TestingKit.assert (parityPin "double" [21]) "parity double 21"
        TestingKit.assert (parityPin "double" [0]) "parity double 0"
        TestingKit.assert (parityPin "adder" [40, 2]) "parity adder"
        TestingKit.assert (parityPin "dec1" [5]) "parity dec1 5"
        TestingKit.assert (parityPin "loop_sum" [10]) "parity loop_sum 10"
        TestingKit.assert (parityPin "loop_sum" [1]) "parity loop_sum 1"
        TestingKit.assert (parityPin "loop_sum" [0]) "parity loop_sum 0"
        TestingKit.assert (parityPin "if_max" [3, 9]) "parity if_max 3 9"
        TestingKit.assert (parityPin "if_max" [9, 3]) "parity if_max 9 3"
        TestingKit.assert (parityPin "ops_mix" [3, 9]) "parity ops_mix 3 9"
        TestingKit.assert (parityPin "ops_mix" [9, 3]) "parity ops_mix 9 3"
        TestingKit.assert (parityPin "ops_mix" [5, 5]) "parity ops_mix 5 5"
        TestingKit.assert (parityPin "ops_mix" [2, 1]) "parity ops_mix 2 1"
        TestingKit.assert (parityPin "tup_second" [3, 9]) "parity tup_second 3 9"
        TestingKit.assert (parityPin "tup_second" [10, 20]) "parity tup_second 10 20"
        TestingKit.assert (parityPin "list_sum" [10]) "parity list_sum 10"
        TestingKit.assert (parityPin "list_sum" [0]) "parity list_sum 0"
        TestingKit.assert (parityPin "list_head" [42]) "parity list_head 42")
      [("control: the parity claim BROKEN (double 21 = 999) is caught",
         fun _ => TestingKit.assert
           (resultOf (runAt "double" [21]) == some 999)
           "the control demanded the broken parity (caught)")
      , ("control: the parity oracle disagrees with itself is caught \
          (pyEval loop_sum 10 = 999)",
         fun _ => TestingKit.assert
           (pyAt "loop_sum" [10] == some 999)
           "the control demanded the broken oracle (caught)")
      ]
      (h := by simp) 1 98
  ]

/-- The second frontend's suites (the runner's appended group). -/
def edgeSuites : List (String × List TestingKit.Spec) :=
  [ ("the edgepython parse face", edgeParseSpecs)
  , ("the edgepython check + lowering faces", edgeCheckSpecs)
  , ("the edgepython end-to-end (the second frontend)", edgeEndToEndSpecs)
  ]

end GuestTests.Edge
