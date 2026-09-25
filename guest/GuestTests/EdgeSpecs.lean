/-
# GuestTests.EdgeSpecs — the SECOND FRONTEND's test battery

The edgepython frontend's teeth (15-patterns #5): the PARSE face (the
text surface reads; the junk refuses), the CHECK face (the lattice's
refusals), the LOWERING face (the Py AST → IR → the SHARED lowering →
module), and THE END-TO-END: the surface text → wasm → the EXECUTOR's
answer — pinned against the PYTHON reference semantics (`Py.pyEval`,
the parity set's authority — the legacy Parity.lean's discipline, run
as runtime assertions, NOT native_decide theorems: the native-policy
gate's allowlist is empty and stays empty).

The parity set is the LEGACY's fixture set (`EdgePython.lean`):
`double`, `adder`, `dec1`, `loop_sum`, `if_max` — the same scalar
program shapes, now through the IR SEAM (the legacy compiled straight
to the WAT AST; this frontend proves the seam's neutrality).

The mandatory negative controls: the parser's junk refusals, the
checker's type refusals, the loop-boundary refusal, and the parity
controls (a tampered expectation, a swapped operand order) — each must
FAIL (the sweep's vacuity guard).

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

/-! ## The fixture surface (the legacy's parity set, as TEXT — the
    ONE copy lives in `ComponentTests.EdgeFixture`, the component
    lane's wasmtime face shares it; this namespace re-exports the
    fixture's products under the battery's names). -/

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

def edgeParseSpecs : List TestingKit.Spec :=
  [ Spec.ofList "the parse face: the legacy parity set's text reads \
      back (the five fns, the params in order)"
      (fun _ =>
        TestingKit.assertEq "edge-fns"
          (edgeFns.map (fun f => (f.name, f.params)))
          [("double", ["x"]), ("adder", ["a", "b"]), ("dec1", ["n"]),
           ("loop_sum", ["n"]), ("if_max", ["a", "b"])])
      [("control: the parse face REFUSES junk (wrong claim — caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Parse.parseProgram
                  "def f(:\n  return 1" with
            | .ok _ => true | .error _ => false)
           "the control demanded the junk parse (caught)")
      , ("control: the parse face ACCEPTS the excluded op `>` (wrong \
          claim — caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Parse.parseProgram
                  "def f(x):\n  return x > 1" with
            | .ok _ => true | .error _ => false)
           "the control demanded `>` parse (caught)")
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
            | .ok ds => !(ds.length == 5) | .error _ => true)
           "the control demanded the checked decls be wrong (caught)")
      ]
      (h := by simp) 1 93
  , Spec.ofList "the lowering's boundary: a loop-carried variable must \
      be bound BEFORE the loop (the entry args' face)"
      (fun _ => TestingKit.assert
        (match Guest.EdgePython.Fe.lowerProgram
           (Guest.EdgePython.Parse.parseProgram
              "def w(n):\n  while n < 5:\n    m = n + 1\n    n = m\n  return n"
              |>.toOption |>.getD [])
          with
          | .ok _ => false | .error _ => true)
        "the loop-boundary refusal must fire")
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
      , ("control: the pipeline refuses (caught)",
         fun _ => TestingKit.assert
           (match Guest.EdgePython.Fe.compileModule "def f(x):\n  return x > 1" with
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
  , Spec.ofList "the loop + the branch: loop_sum 10 = 45, if_max takes \
      both routes (the jp loop shape + the value-dispatch lane)"
      (fun _ => do
        TestingKit.assertEq "loop_sum-45" (resultOf (runAt "loop_sum" [10])) (some 45)
        TestingKit.assertEq "loop_sum-0" (resultOf (runAt "loop_sum" [0])) (some 0)
        TestingKit.assertEq "if_max-9a" (resultOf (runAt "if_max" [3, 9])) (some 9)
        TestingKit.assertEq "if_max-9b" (resultOf (runAt "if_max" [9, 3])) (some 9))
      [("control: loop_sum 10 = 44 (caught)",
         fun _ => TestingKit.assertEq "loop-wrong"
           (resultOf (runAt "loop_sum" [10])) (some 44))
      , ("control: if_max 3 9 = 3 (caught)",
         fun _ => TestingKit.assertEq "ifmax-wrong"
           (resultOf (runAt "if_max" [3, 9])) (some 3))
      ]
      (h := by simp) 1 97
  , Spec.ofList "THE PARITY: the compiled wasm == the Python reference \
      semantics on the legacy parity set, at multiple points"
      (fun _ => do
        TestingKit.assert (parityPin "double" [21]) "parity double 21"
        TestingKit.assert (parityPin "double" [0]) "parity double 0"
        TestingKit.assert (parityPin "adder" [40, 2]) "parity adder"
        TestingKit.assert (parityPin "dec1" [5]) "parity dec1 5"
        TestingKit.assert (parityPin "loop_sum" [10]) "parity loop_sum 10"
        TestingKit.assert (parityPin "loop_sum" [1]) "parity loop_sum 1"
        TestingKit.assert (parityPin "loop_sum" [0]) "parity loop_sum 0"
        TestingKit.assert (parityPin "if_max" [3, 9]) "parity if_max 3 9"
        TestingKit.assert (parityPin "if_max" [9, 3]) "parity if_max 9 3")
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
