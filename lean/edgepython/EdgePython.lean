/-
# EdgePython — the SECOND FRONTEND over the IR seam (the root module)

Owner: the EDGEPYTHON lane. The deliverable: a Python subset compiled to
the SAME typed WAT AST the LCNF backend emits (`WasmBackend.Wat` —
imported, FROZEN, zero new constructors), running on the SAME runtimes
(steel-host's wasmtime via the `edgepython` Rust test, guestlang-rt's
wasmi via its `edgepython` test). Multi-frontend conformance: same
fixtures → same IR → same results across THREE engines (this Lean eval
+ wasmtime + wasmi).

THE FIXTURES (the parity set, shared with the Rust duel tests):
`double`, `adder`, `loop_sum`, `if_max`, `dec1` — the same
scalar-program shapes the guestlang demo exports (double/adder parity
by name; loop/if replace the guestlang heap-backed list/cases with the
scalars-only equivalents).

Deliberate exclusions (see Ast.lean's header for the full ledger):
no strings/lists/objects (no heap, hence no alloc/RC splice), no
`>`/`<=`/`>=`/`!=` (frozen `Wat.Op` gap — REPORTED), no recursion, no
negative literals.
-/

import WasmBackend.Wat
import EdgePython.Ast
import EdgePython.Compiler
import EdgePython.Eval

namespace EdgePython

open WasmBackend.Wat EdgePython.Py

/-! ## The fixtures (the parity set) -/

def fixtures : List Py.Fn :=
  [{ name := "double", params := ["x"]
     body := [.ret (.bin .add (.var "x") (.var "x"))] },
   { name := "adder", params := ["a", "b"]
     body := [.ret (.bin .add (.var "a") (.var "b"))] },
   { name := "dec1", params := ["n"]
     body := [.ret (.bin .sub (.var "n") (.int 1))] },
   { name := "loop_sum", params := ["n"]
     body := [.assign "s" (.int 0),
              .assign "i" (.int 0),
              .while (.cmp .lt (.var "i") (.var "n"))
                [.assign "s" (.bin .add (.var "s") (.var "i")),
                 .assign "i" (.bin .add (.var "i") (.int 1))],
              .ret (.var "s")] },
   { name := "if_max", params := ["a", "b"]
     body := [.ifelse (.cmp .lt (.var "a") (.var "b"))
                [.ret (.var "b")] [.ret (.var "a")]] }]

/-- THE compiled module: the fixtures through the compiler into the
    FROZEN Wat AST. `none` = a compile error (the type checker rejected
    something) — the tests pin this to `some`. -/
def compiledModule? : Option Module := Compiler.compModule fixtures

/-- The total form for the drivers: the fixtures DO compile (pinned by
    `compiles_ok` in Tests); if they ever stop, this is the empty module
    and every parity guard fails loudly. -/
def fixturesModule : Module :=
  match compiledModule? with
  | some m => m
  | none => { items := [] }

/-- The compiled funcs (the eval surface). -/
def compiledFns : List Func := WEval.modFns fixturesModule

end EdgePython
