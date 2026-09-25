/-
# ComponentTests.EdgeFixture — the edgepython component lane's fixture

The component lane's THIRD fixture: the edgepython frontend's parity
set as a COMPONENT (`Guest.EdgePython.Fe.compileModule` — parse →
check → IR → the SHARED lowering → the core module — all PURE, no LCNF
re-run: the string-lane's no-LCNF shape with a REAL frontend's
product). The fixture module owns the ONE copy of the parity source +
the world + the spec, consumed by three faces:

- `GuestTests.EdgeSpecs` (the Lean executor's battery — the source's
  original home, adopted here so the text has ONE owner);
- the component emission (the writer `componentgen` + the gate
  `gen-check` + the byte-tie pins in ComponentTests.Main);
- the Rust host (`crates/mandate-host`'s edge lane — the parity
  points' goldens, typed through wasmtime).

THE THREE-WAY PARITY: `pyAt` (the legacy Python oracle) ≡ `execAt`
(the Lean executor over the SAME core module the component embeds) ≡
the wasmtime execution of the committed component (the Rust host's
goldens — the same numbers, pinned there). The Lean side pins the
first two legs + the literals; the Rust side pins the literals through
the engine; the byte-tie ties the embedded module to the committed
component. A parity point's module: `pyAt name args == execAt name
args == the literal`.

The five questions (notes/v3/01-core.md): the fixture is data (the
test lane's Universe face) — the answers live at the consumers.
-/

import Guest
import Guest.Component
import Guest.EdgePython.Fe
import Wit
import Wit.World
import WasmCore.Instr
import WasmCore.Module
import WasmCore.Types

open Guest WasmCore

namespace ComponentTests.EdgeFixture

/-! ## The parity source (ONE copy — EdgeSpecs adopts it) -/

/-- THE fixture surface (the legacy's parity set, as TEXT) — the ONE
    copy; `GuestTests.EdgeSpecs` renders its teeth from this. -/
def edgeSrc : String :=
"def double(x):\n" ++
"  return x + x\n" ++
"\n" ++
"def adder(a, b):\n" ++
"  return a + b\n" ++
"\n" ++
"def dec1(n):\n" ++
"  return n - 1\n" ++
"\n" ++
"def loop_sum(n):\n" ++
"  s = 0\n" ++
"  i = 0\n" ++
"  while i < n:\n" ++
"    s = s + i\n" ++
"    i = i + 1\n" ++
"  return s\n" ++
"\n" ++
"def if_max(a, b):\n" ++
"  if a < b:\n" ++
"    return b\n" ++
"  else:\n" ++
"    return a\n"

/-! ## The frontend's products (pure — no LCNF re-run) -/

/-- The parsed fixtures (the parse face's product). -/
def edgeFns : List Guest.EdgePython.Py.Fn :=
  match Guest.EdgePython.Parse.parseProgram edgeSrc with
  | .ok fns => fns
  | .error _ => []

/-- The compiled module (the pipeline's product; a compile failure is
    the EMPTY module — every execution pin fails loudly against it,
    the legacy `fixturesModule` discipline). -/
def edgeCore : WasmCore.Module :=
  match Guest.EdgePython.Fe.compileModule edgeSrc with
  | .ok m => m
  | .error _ => { types := [], funcs := [], exports := [] }

/-- The decl order IS the function-table index (the call lane's). -/
def idxOf (name : String) : Nat :=
  (edgeFns.map (·.name)).idxOf name

/-! ## The world (the component boundary's contract side) -/

/-- The component face's extern names: WIT requires kebab-case (the
    component-model validator refuses `loop_sum` — extern names are
    kebab), Python's are snake_case. The boundary mangles the
    underscore — the ONE name adapter the frontend needs (the bodies
    and the indices are untouched; the parity faces key on the SAME
    decl order). -/
def kebab (s : String) : String := String.intercalate "-" (s.splitOn "_")

/-- THE EDGE WORLD: the five parity functions, the honest ABI surface
    of the frontend's product — every fn is the u64-scalar shape
    (`int` = the IR u64 row, the frontend's exported surface), so the
    canonical-ABI lift needs no adapter face. The decl order below IS
    the module's export order (`lowerFuncs`'s discipline); the names
    are the component face's kebab forms (`kebab`). -/
def edgeWorld : Wit.World :=
  { name := "edge"
  , imports := []
  , exports :=
      [ .func { name := "double"
              , params := [{ name := "x", ty := .atom .u64 }]
              , result := some (.atom .u64) }
      , .func { name := "adder"
              , params := [{ name := "a", ty := .atom .u64 }
                         , { name := "b", ty := .atom .u64 }]
              , result := some (.atom .u64) }
      , .func { name := "dec1"
              , params := [{ name := "n", ty := .atom .u64 }]
              , result := some (.atom .u64) }
      , .func { name := "loop-sum"
              , params := [{ name := "n", ty := .atom .u64 }]
              , result := some (.atom .u64) }
      , .func { name := "if-max"
              , params := [{ name := "a", ty := .atom .u64 }
                         , { name := "b", ty := .atom .u64 }]
              , result := some (.atom .u64) } ] }

/-- The component face's core module: the frontend's product with the
    exports' names under the kebab mangling (the world names the same
    functions — `check`'s by-name discipline ties them). The Lean
    executor's battery runs the UNmangled module (`edgeCore`); the
    component embeds THIS one. -/
def edgeComponentCore : WasmCore.Module :=
  { edgeCore with
      exports := edgeCore.exports.map
        (fun e => { e with name := kebab e.name }) }

/-- THE EDGE SPEC: the frontend's module + the world it must match
    (the emission's skew check runs at generation — `Guest.Component.
    regen`). -/
def edgeSpec : Guest.Component.Spec :=
  { core := edgeComponentCore, world := edgeWorld }

/-! ## The parity faces (the two Lean legs) -/

/-- The Lean EXECUTOR's answer (the landed engine over the frontend's
    module). -/
def execAt (name : String) (args : List Int) : WasmCore.Outcome :=
  WasmCore.runFunc edgeCore (idxOf name)
    (args.map (fun z => WasmCore.Val.i64 z.toNat.toUInt64)) 2000

/-- The i64 result of a completed run. -/
def resultOf : WasmCore.Outcome → Option Int
  | .ok s => match s.stack with
    | [WasmCore.Val.i64 v] => some v.toNat
    | _ => none
  | _ => none

/-- The PYTHON model's answer (the parity oracle — `Py.pyEval`). -/
def pyAt (name : String) (args : List Int) : Option Int :=
  Guest.EdgePython.Py.pyEval edgeFns name args

end ComponentTests.EdgeFixture
