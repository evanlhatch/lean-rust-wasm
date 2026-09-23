/-
# EdgePython.SemExec — the thin adapter over the SHARED Sem machine (M3)

Owner: the EDGEPYTHON lane (M3, 2026-12). THE REPLACEMENT for the
deleted evaluator (EdgePython.Eval — the `WEval` frame machine). This
module is a THIN ADAPTER: it translates the compiled `Wat.Instr`
bodies into the `Sem.Instr` fragment and runs `WasmBackend.Sem.exec` —
the wasm-backend's PROVED machine. Nothing here re-implements a frame
machine or per-op semantics: the `.op o` translation goes through
`WasmBackend.SemOp.opInstr` (the per-op table next to `Wat.Op`, whose
rows delegate to `Sem.step`). The adapter is edgepython-owned ONLY
because the name→index local resolution, the label→depth branch
resolution, and the `.ret` return-convention truncation are
Wat-specific — the translator of the seam, not a second semantics.

THE TRANSLATION (the compiled fragment):

* `i32const`/`i64const` — Wat stores Nat, Sem stores UInt32/UInt64
  (the casts; the fragment's literals are in range).
* `localget`/`localset` — the NAME → INDEX resolution (Sem locals are
  Nat-keyed; the index = first match in params ++ declared locals).
* `.op o` — via `SemOp.opInstr` (`none` = an op outside the modeled
  fragment — explicit).
* `br`/`brif` — the LABEL → DEPTH resolution (Sem's `br n` counts
  frames from the innermost enclosing block/loop/if_; `if_` is
  UNLABELED in the frozen AST, so it pushes nothing on the label
  stack — the same discipline the deleted Eval.lean used).
* `block`/`loop` — recurse, label pushed; `if_` — recurse, result
  must be `none`.
* `.ret` — the RETURN CONVENTION: ends the translation of the current
  instruction list (the caller's value sits on the stack top; the
  callee's final stack top IS the return value). The compiler's
  trailing `.unreach` seal is never translated. NOTE the honest limit:
  a `.ret` inside a NESTED frame (a `while` body) truncates only that
  frame's list — full host wat's return unwinds ALL frames — outside
  the compiled surface (no fixture has a ret in a loop), documented;
  the fragment's `ret` is a top-level-or-if-branch construct.
* everything else (`call`, `callindirect`, `returncall`, `mem*`,
  `global*`, `localtee`, `select`, `raw`) — `none` (out of the
  fragment — the same failure surface as the deleted Eval.lean's
  fallback arm).

FUEL: `Sem.exec` at `defaultFuel` (1000). The compiled fixtures'
budgets (derived 2026-12, R3 of design-one-instr-ast.md): the deepest
fixture is `loop_sum n` ≈ 15 fuel per iteration + a fixed setup, so
budgets 1000 ≫ 10×15 + tail — computed by running the machine. At the
old WEval budget of 400 the same fixtures also fit; `defaultFuel`
keeps the adapter on Sem's canonical entry point.
-/

import WasmBackend.Sem
import WasmBackend.SemOp
import WasmBackend.Wat

namespace EdgePython.SemExec

-- NOTE: bare `Instr` is AMBIGUOUS between the two opened inductives
-- (WasmBackend.Wat.Instr and WasmBackend.Sem.Instr), so this module
-- opens ONLY Wat and qualifies the Sem fragment's types explicitly
-- (WasmBackend.Sem.*); the produced constructors resolve by expected
-- type at each site.
open WasmBackend.Wat

/-- The module's functions (the `Item.func` fold) — moved here verbatim
    from the deleted Eval.lean (module plumbing, not semantics). -/
def modFns (m : Module) : List Func :=
  m.items.foldr (fun i acc =>
    match i with
    | .func f => f :: acc
    | _ => acc) []

/-- The function record by name. -/
def findFn : List Func → String → Option Func
  | [], _ => none
  | f :: rest, name => if f.name == name then some f else findFn rest name

/-- First-match index of a name in a string list. -/
def indexOfName : List String → String → Option Nat
  | [], _ => none
  | y :: ys, x => if y == x then some 0 else (indexOfName ys x).map (· + 1)

/-- The local INDEX of a name (first match: params then declared
    locals) — Sem locals are `Nat`-keyed; the name→index resolution is
    the adapter's (the emitter/backend's job per Sem.lean's header). -/
def localIdxOf (g : Func) (x : String) : Option Nat :=
  match indexOfName (g.params.filterMap (fun p => p.name)) x with
  | some i => some i
  | none => (indexOfName (g.locals.map Prod.fst) x).map (fun i => i + g.params.length)

/-- Branch-target depth: the FIRST matching label, innermost-first (the
    label stack's head is the innermost frame) — the counter Sem's
    `br n`/`brif n` count. Verbatim from the deleted Eval.lean. -/
def labelDepth : List String → String → Option Nat
  | [], _ => none
  | l :: rest, name => if l == name then some 0 else (labelDepth rest name).map (· + 1)

/-- One `Wat.Instr` → the `Sem.Instr` for the compiled fragment
    (recursing into the frame bodies). `none` = outside the fragment
    (calls, mem-ops, globals, raw — explicit, as in the deleted
    evaluator's fallback). -/
def toSemBody (labels : List String) (g : Func) : List Instr → Option (List WasmBackend.Sem.Instr)
  | [] => some []
  | .ret :: _ => some []  -- the return convention: the value is on the stack
  | .unreach :: _ => some [] -- the compiled fall-off-the-end SEAL is dead
    -- code here (fix 2026-12, found on if_max): under WEval's frame
    -- machine a branch-`ret` returned BEFORE the seal ever ran; Sem has
    -- NO `ret` — an if-branch whose body was a ret-translated localget
    -- FALLS THROUGH under Sem's value-returning if_, so a faithfully
    -- translated trailing seal would TRAP (step .unreach = .error
    -- .trap) and the fixture would read `none`. Truncating at the seal
    -- is exactly the old reach: the compiler emits it only as the one
    -- terminal marker after compSs (compS emits no unreach), so it is
    -- never load-bearing.
  | i :: is => do
      let i' ← toSem labels g i
      let is' ← toSemBody labels g is
      some (i' :: is')
where
  toSem : List String → Func → Instr → Option WasmBackend.Sem.Instr
    | labels, g, .i32const n => some (.i32const n.toUInt32)
    | labels, g, .i64const n => some (.i64const n.toUInt64)
    | labels, g, .localget x => do let i ← localIdxOf g x; some (.localget i)
    | labels, g, .localset x => do let i ← localIdxOf g x; some (.localset i)
    | labels, g, .op o => WasmBackend.SemOp.opInstr o
    | labels, g, .drop => some .drop
    | labels, g, .br l => do let k ← labelDepth labels l; some (.br k)
    | labels, g, .brif l => do let k ← labelDepth labels l; some (.brif k)
    | labels, g, .unreach => some .unreach
    | labels, g, .block l body => do let b ← toSemBody (l :: labels) g body; some (.block b)
    | labels, g, .loop l body => do let b ← toSemBody (l :: labels) g body; some (.loop b)
    | labels, g, .if_ res t e =>
        match res with
        | none =>
            do let t' ← toSemBody labels g t
               let e' ← toSemBody labels g e
               some (.if_ t' e')
        | some _ => none  -- result-carrying if: outside the no-result fragment
    | _, _, _ => none

/-- The callee's entry state: the args bound to the param locals
    (param i = the i-th arg — locals 0..k-1), empty operand stack,
    zeroed 64-byte memory. Out-of-range local indices default to
    `i64 0` (the deleted Eval.lean's `getLocal` default). -/
def initState (g : Func) (args : List Int) : WasmBackend.Sem.State :=
  ⟨fun n => .i64 (UInt64.ofInt (args.getD n 0)), [], fun _ => (0 : UInt8), 64⟩

/-- The i64/i32 value → the Python reference world (`Int`). The UNSIGNED
    view (`toNat`) — pinned on the fixtures' concrete values, NOT proven
    in general (design-one-instr-ast.md R2: no general wrap theorem). -/
def valToInt : WasmBackend.Sem.Val → Int
  | .i64 n => (n.toNat : Int)
  | .i32 n => (n.toNat : Int)

/-- Run one function over Sem: translate, bind the args, `Sem.exec`,
    read the TOP of the final stack (the return convention). A
    translation failure or any Sem error = `none`. -/
def execFn (g : Func) (args : List Int) : Option WasmBackend.Sem.Val :=
  match toSemBody [] g g.body with
  | none => none
  | some body' =>
      match WasmBackend.Sem.exec (initState g args) body' with
      | .ok s' => s'.stack.head?
      | .error _ => none

/-- THE top level: run exported fn `name(args...)` over the module's
    funcs — the signature of the deleted `WEval.callModule` (the parity
    theorems restate engine-side with this in place of it). -/
def callModule (fns : List Func) (name : String) (args : List Int) : Option Int :=
  match findFn fns name with
  | none => none
  | some g =>
      match execFn g args with
      | some v => some (valToInt v)
      | none => none

end EdgePython.SemExec
