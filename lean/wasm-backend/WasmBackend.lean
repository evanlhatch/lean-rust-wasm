import Lean
import Lean.Compiler.LCNF
import WasmBackend.Check
import WasmBackend.Layout
import WasmBackend.Sem
import WasmBackend.Wat
import GuestlangStd.StrOps

/-!
# WasmBackend — LCNF → WAT emission

The `leanir` re-run pattern (see GenMain): the final impure-phase LCNF →
WebAssembly Text. Toolchain: `wasm-tools parse -g` → validate → wasmtime.

TYPED WAT (the doctrine): the module is assembled as a `Wat.Module` and
rendered by `Wat.Module.render` (`Std.Format` — never string
interpolation for structure). The adapters' field offsets come from the
PROVED `Layout.offsets` (user_offsets = [0,8,16,24], user_size = 32) —
the emitted instrs are structurally the proved function's outputs. The
`Instr.raw` ledger is 0 since the raw→typed migration: everything — the
adapters, the general path (emitCode/emitLet/emitCases/goAlts/
emitReturn/emitArg), the trampolines, the callbacks, cabi_realloc, the
module assembly — is typed. The ONE raw is the `Wat.Item.raw
"  ;;RUNTIME-SPLICE"` marker (GenMain replaces those exact bytes with
runtime.wat) — not an instruction, so the raw-count stays 0.

Record-param adapter's ABI fact (probed against the encoder): a record
param crosses FLAT while its flattened form fits MAX_FLAT_PARAMS=16 —
the demo's user (u64 + 3×(ptr,len) = 7 flat values) arrives as 7 core
params `[i64, i32×6]`; a POINTER-form adapter FAILS `component new`
(`expected [I64, I32, …]`). The adapter reconstructs the guest object:
strings = alloc(16+len) {tag=250, len@8, memory.copy bytes@16}, the
tags list = a cons chain built by walking the flat (ptr,len) array
BACKWARD, the User = the refs-first object {tag, name@8, email@16,
tags@24, id@32}. Design-essay details: notes/wasm-backend-notes.md.

Layout (guestlang-owned): `{rc u32@0, tag u8@4, class u8@5, fields @8}`.
Lean's field conventions: ref fields at `8+i*8` (oproj[i]); scalar
fields after the ref slots at `8+size*8+off` (sproj[i,off]). Special
tag: 254 = closure `{rc, 254, class, fnIdx u32@8, partial args@16…}`.

Runtime (runtime.wat, spliced in): pooled allocator (size-class free
lists) + $rc_inc/$rc_dec. inc/dec EMIT — the freelist reuse makes them
load-bearing (a dec-freed persistent global = use-after-free).

Closures: pap → trampoline-per-(fn,partial-arity) in a funcref table;
closure apply = `call_indirect` (closure ptr, fresh args, fnIdx).
ROBUSTNESS: unsupported constructs THROW (compile error), never emit
comments; arity checks against the target decl's signature at emission.
-/

namespace WasmBackend

open Lean Compiler.LCNF

/-! ## Scalar ABI -/

/-- Wasm scalar type for an LCNF type expression. `none` = object →
i32 pointer. (Nat is an OBJECT too — see the bounded-Nat note at the
`emitLet` arms.) -/
def wasmTyOf? : Expr → Option String
  | .const c _ =>
    if c == `UInt64 then some "i64"
    else if c == `UInt32 || c == `UInt8 || c == `Bool then some "i32"
    -- Char: the single-u32-field structure erases to its scalar in the
    -- LCNF (the decChar? x-ray: `Char.ofNat n` then a direct `box`) —
    -- the guest model is the raw i32 codepoint.
    else if c == `Char then some "i32"
    else none
  | _ => none

/-- Param → wasm type. Borrowed scalars are objects (tagged pointers). -/
def paramWasmTy (p : Param .impure) : String :=
  match p.borrow, wasmTyOf? p.type with
  | false, some t => t
  | _, _ => "i32"

/-! ## State -/

structure S where
  fvars : Std.HashMap FVarId (String × String) := {}
  locals : Array (String × String) := #[]
  out : Array Wat.Instr := #[]
  /-- the `Instr.raw` count so far — the migration's progress metric.
      Zero raw = fully typed. -/
  rawCount : Nat := 0
  n : Nat := 0
  /-- trampolines emitted so far (pap closures): (fnName, nPartial). -/
  tramps : Array (Name × Nat) := #[]
  /-- every decl's wasm (param types, result type) — populated by
  emitModule BEFORE the decls emit (the fap result-type lookup needs
  the CALLEE's wasm result: object-returning calls with args = i32,
  scalar = i64 — the type default alone miscasts the local). -/
  sigs : Std.HashMap Name (Array String × String) := {}
  /-- the join points IN SCOPE, by their fvar: (label, (param local, ty)…)
      — the `.jmp` sites' store/branch targets. -/
  jps : Std.HashMap FVarId (String × Array (String × String)) := {}
  deriving Inhabited

abbrev M := StateT S (Except String)

/-- The PRIMITIVE: emit one typed instruction. -/
def emitI (i : Wat.Instr) : M Unit := do
  let bump := match i with | .raw _ => 1 | _ => 0
  modify fun s => { s with out := s.out.push i, rawCount := s.rawCount + bump }

def unsupported (what : String) : M Unit :=
  throw s!"WasmBackend: unsupported construct: {what}"

def bindLocal (fvarId : FVarId) (ty : String) : M String := do
  let name := s!"l{S.n (← get)}"
  modify fun s => { s with
    fvars := s.fvars.insert fvarId (name, ty)
    locals := s.locals.push (name, ty)
    n := s.n + 1 }
  pure name

def bindNamed (fvarId : FVarId) (name : String) (ty : String) : M Unit :=
  modify fun s => { s with fvars := s.fvars.insert fvarId (name, ty) }

def bindFresh (ty : String) : M String := do
  let name := s!"l{S.n (← get)}"
  modify fun s => { s with locals := s.locals.push (name, ty), n := s.n + 1 }
  pure name

def localTy? (fvarId : FVarId) : M (Option String) := do
  match (← get).fvars[fvarId]? with
  | some (_, ty) => pure (some ty)
  | none => pure none
/-- The local's NAME (typed emission wraps it in `.localget`). -/
def load (fvarId : FVarId) : M String := do
  match (← get).fvars[fvarId]? with
  | some (n, _) => pure n
  | none => throw s!"WasmBackend: unbound fvar {fvarId.name}"

/-! ## Primitives -/

def binop? : Name → Option Wat.Op
  | ``UInt64.add => some .i64add
  | ``UInt64.sub => some .i64sub
  | ``UInt64.mul => some .i64mul
  | ``UInt64.decLt => some .i64ltu
  | ``UInt64.decEq => some .i64eq
  | _ => none

/-- The LCNF specialization-product naming (the audit's gap 4): the
    spec pass names a specialized instance-method call by its SOURCE —
    `<method>._at_.<caller>.spec_<n>`. The `Option.instBEq.beq` spec
    never joins impureExt (it is a base-phase decl only, not in
    `env.constants`), so its call sites are inline-lowered. -/
def isSpecBEqName (n : Name) : Bool :=
  n.toString.startsWith "Option.instBEq.beq._at_."

/-- The bounded-Nat fap surface the emitter INLINE-lowers at the
    `emitLet .fap` arms: no callee decl exists (extern primitives),
    nothing to compile or call — the operand-arity-checked arms
    (Nat.decEq/beq/sub/add, the UInt64↔Nat seam). The callee COLLECTOR
    and the UNSUPPORTED-LCNF diagnostic must agree with this surface:
    chasing these names adds extern stubs + broken adapters (the
    Nat.decEq_abi validate failure); flagging them re-bans the
    sanctioned surface. -/
def inlineNatFap? (fn : Name) (arity : Nat) : Bool :=
  ((fn == ``UInt64.toNat || fn == ``Nat.toUInt64 || fn == ``UInt8.toNat
        || fn == ``UInt64.ofNat || fn == ``Char.ofNat) && arity == 1)
    || ((fn == ``Nat.decEq || fn == ``Nat.beq
        || fn == ``Nat.sub || fn == ``Nat.add || fn == ``Nat.mul
        || fn == ``Nat.decLt || fn == ``Nat.decLe) && arity == 2)
    || ((fn == ``UInt8.decEq
        || fn == ``UInt32.decEq
       ) && arity == 2)
/-- The spec-BEq call's args are fvars (LCNF is ANF). -/
def specBEqArg : Arg .impure → M FVarId
  | .fvar f => pure f
  | _ => throw "WasmBackend: spec-BEq non-fvar arg"

/-! ## The ONE impure-`Code` traversal skeleton (the layering audit's
consolidation: the walker shape was hand-duplicated — `jumpsTo`, the
`resultTy` family here, `fapCalleesOf` in GenMain.lean — each re-writing
the same structural recursion).

`Code.foldImpure` is a structural fold; a WALKER = a `spineAcc` + a
`step` algebra + a seed. The skeleton's policy (stated, so each
walker's fit is checkable):

- the SPINE (`k`-bearing nodes: let/sset/uset/oset/setTag/inc/dec/del/
  jp/fun) folds its `k` with the `spineAcc`-updated accumulator — a
  `let` may REPLACE the accumulator (`resultTyOf`'s
  most-recent-let type);
- the NESTED bodies (jp/fun `FunDecl.value`, the case alts) fold with
  the SEED — a nested body RESTARTS the fold (`resultTyOfAlt`'s
  walk-from-none semantics);
- `step` sees the node, the node's own accumulator, the nested folds,
  the alt folds (ctor/default order), and the continuation's fold
  (`none` where the node has no `k`): every short-circuit, kill, and
  leaf decision is the walker's — no forced unification. EAGER (pure
  walkers only; every consumer is).

Exposed (not private): GenMain.lean's `fapCalleesOf` walks with it —
same exposure surface as `binop?`/`inlineNatFap?`.

Walkers that do NOT fit (left alone, honestly): the `emitCode` mutual
family (stateful `M` emission — per-node instruction ORDERING, state
FORKING in `emitScoped`, let/return tail-call fusion; not a fold), and
GenMain.lean's `reportUnsupportedLCNF` walk (its diagnostic PATHS are
child-position labels — `/jpK`, `/caseD` — the skeleton does not
carry). -/

-- The skeleton stays in the WasmBackend namespace (the file's `open`s
-- open Lean/Compiler/LCNF SEPARATELY, so `Code.foldImpure` would NOT
-- resolve through Lean.Compiler.LCNF from here); exposed (not private)
-- for GenMain.lean's `fapCalleesOf` — the same exposure surface as
-- `binop?`/`inlineNatFap?`. Referenced cross-file as
-- `WasmBackend.Code.foldImpure`.

/-- The alt walker's impossible-ctor discharge (the `.alt` ctor carries
    a `False` proof — every walker `absurd`s it; here once). -/
private def Alt.foldImpure {α : Type}
    (go : Code .impure → α → α) (a : Alt .impure) (seed : α) : α :=
  match a with
  | .ctorAlt _ code => go code seed
  | .default code => go code seed
  | .alt _ _ _ h => absurd h (by simp)

partial def Code.foldImpure {α : Type}
    (spineAcc : Code .impure → α → α)
    (step : Code .impure → α → List α → List α → Option α → α)
    (seed : α) (code : Code .impure) (acc : α) : α :=
  match code with
  | .jp fd k =>
      step code acc [Code.foldImpure spineAcc step seed fd.value seed]
        [] (some (Code.foldImpure spineAcc step seed k (spineAcc code acc)))
  | .fun fd k _ =>
      step code acc [Code.foldImpure spineAcc step seed fd.value seed]
        [] (some (Code.foldImpure spineAcc step seed k (spineAcc code acc)))
  | .cases c =>
      step code acc []
        (c.alts.toList.map fun a => Alt.foldImpure (Code.foldImpure spineAcc step seed) a seed)
        none
  | .jmp .. | .return _ | .unreach _ => step code acc [] [] none
  | .let _ k | .sset _ _ _ _ _ k | .uset _ _ _ k | .oset _ _ _ k | .setTag _ _ k
  | .inc _ _ _ _ k | .dec _ _ _ _ _ k | .del _ k =>
      step code acc [] []
        (some (Code.foldImpure spineAcc step seed k (spineAcc code acc)))

/-- Does this code jump to the given jp? (A loop-shaped jp — the body
    jumping back to ITSELF — is unreachable in the block lowering:
    the body sits outside the label's scope. Conservative reject.) -/
private def jumpsToStep (target : FVarId) :
    Code .impure → Bool → List Bool → List Bool → Option Bool → Bool
  | .jmp j _, _, _, _, _ => j == target
  | .jp _ _, _, nested, _, k => nested.foldl (· || ·) false || k.getD false
  | .fun _ _ _, _, nested, _, k => nested.foldl (· || ·) false || k.getD false
  | .cases _, _, _, alts, _ => alts.foldl (· || ·) false
  | .return _, _, _, _, _ => false
  | .unreach _, _, _, _, _ => false
  | .oset .., _, _, _, _ => false
  | .uset .., _, _, _, _ => false
  | .setTag .., _, _, _, _ => false
  | _, _, _, _, k => k.getD false

private def jumpsTo (target : FVarId) : Code .impure → Bool :=
  fun code => Code.foldImpure (fun _ a => a) (jumpsToStep target) false code false

/-! ## guestlang-std string intrinsics

The std intrinsics fold the CLOSED `GuestlangStd.Intrinsic` universe
(`GuestlangStd/StrOps.lean`): `Intrinsic.ofName?` maps a Lean decl name
to its ctor. The Lean bodies are never compiled (they are the
differential ORACLE — see DemoFn).
Guest string layout: `{rc@0, tag=250@4, len u32@8, bytes@16}` — a
variable-size object (16 + len); the bytes live INLINE so RC frees the
whole string. Byte-length ≠ char-length off ASCII (documented, v1). -/

/-- The guest string tag byte. -/
def stringTag : Nat := 250

def storeMemOp (ty : Option String) : Wat.MemOp :=
  match ty with | some "i32" => .i32store | _ => .i64store

def loadMemOp (tyS : String) : Wat.MemOp :=
  if tyS == "i64" then .i64load else .i32load

def emitIs (is : List Wat.Instr) : M Unit :=
  is.forM emitI

def emitArg : Arg .impure → M Unit
  | .fvar fvarId => do emitI (.localget (← load fvarId))
  -- erased args push NOTHING (a no-op then and now — LCNF is ANF, so
  -- real args are always fvars; the erased case is the unit filler)
  | _ => pure ()

/-- The spine accumulator: a `let` REPLACES the accumulated type with
    its own wasm type (the most-recent-let rule); every other node
    threads it unchanged. (Object-typed lets — ctor/pap/fn-typed — are
    i32 pointers: the `getD \"i32\"` default.) -/
private def resultTyOfSpineAcc : Code .impure → Option String → Option String
  | .let decl _, _ => some ((wasmTyOf? decl.type).getD "i32")
  | _, a => a

/-- `resultTyOf`'s algebra over `Code.foldImpure`. -/
private def resultTyOfStep :
    Code .impure → Option String → List (Option String) → List (Option String) →
    Option (Option String) → Option String
  | .let _ _, _, _, _, k => k.join
  | .return _, acc, _, _, _ => acc
  | .cases _, _, _, alts, _ => (alts.filterMap id).head?
  | .unreach _, _, _, _, _ => none
  | .jmp .., _, _, _, _ => none
  | .oset .., _, _, _, _ => none
  | .uset .., _, _, _, _ => none
  | .setTag .., _, _, _, _ => none
  | .fun _ _ h, _, _, _, _ => absurd h (by simp)
  -- sset/inc/dec/del/jp: the spine threads the accumulator through `k`
  | _, _, _, _, k => k.join

partial def resultTyOf : Code .impure → Option String :=
  fun c => Code.foldImpure resultTyOfSpineAcc resultTyOfStep none c none

/-- The alt walker: each alt's code walked from the SEED (`none`) —
    the walk-from-none semantics the skeleton's nested rule supplies. -/
partial def resultTyOfAlt (a : Alt .impure) : Option String :=
  Alt.foldImpure (fun c _ => resultTyOf c) a none

mutual

partial def emitCode (code : Code .impure) : M Unit := do
  match code with
  | .let decl k =>
      -- TAIL-CALL FUSION: `let x := fap f args; return x` → return_call
      -- (the tail-call proposal; wasm-tools parse --enable-tail-call).
      -- The WASM stack stays flat for tail-recursive Lean functions.
      match k, decl.value with
      | .return rv, .fap fn args _ =>
          -- intrinsics are NOT fusion targets (the primitive is not a
          -- Lean decl; its mapped call has its own convention) — std ops
          -- fall through to the normal let path
          if rv == decl.fvarId && (binop? fn).isNone
              && (GuestlangStd.Intrinsic.ofName? fn).isNone
              && !isSpecBEqName fn && !inlineNatFap? fn args.size then
            for a in args do emitArg a
            emitI (.returncall fn.toString)
          else
            emitLet decl; emitCode k
      | _, _ => emitLet decl; emitCode k
  | .return fvarId => emitReturn fvarId
  | .cases c =>
      emitCases c
      -- THE FALLTHROUGH SEAL: an LCNF case is TERMINAL in its spine
      -- (every arm ends return/jmp/unreach or another case), but the
      -- VALIDATOR keeps the enclosing frame reachable at the case's
      -- end, and a fallthrough with an empty stack fails the
      -- result-type check (the checkWitness probe). The unreachable
      -- is semantically dead.
      emitI .unreach
  | .inc fvarId _ _ _ k =>
      emitI (.localget (← load fvarId)); emitI (.call "rc_inc"); emitCode k
  | .dec fvarId _ _ _ _ k =>
      emitI (.localget (← load fvarId)); emitI (.call "rc_dec"); emitCode k
  | .del _ k => emitCode k
  | .jp fd k =>
      -- JOIN POINT WITH ARGS: WAT has no goto, so the jp lowers to
      -- the block-and-fallthrough shape:
      --   block $skip
      --     block $jpL           ;; the gotos' label
      --       <k; a goto = arg stores + br $jpL>
      --       br $skip           ;; the fallthrough never reaches the body
      --     end
      --     <the jp body>         ;; a br $jpL lands HERE
      --   end
      -- The arg(s) ride LOCALS (blocks pass no values); the body must
      -- not jump BACK (loop-shaped jp throws). The jp's params bind to
      -- fresh locals, registered in `jps` so the `.jmp` sites find
      -- them by the jp's OWN fvar.
      let jpL := s!"jp{S.n (← get)}"
      let skipL := s!"sk{S.n (← get)}"
      let mut paramLocals : Array (String × String) := #[]
      for p in fd.params do
        let l ← bindLocal p.fvarId (paramWasmTy p)
        paramLocals := paramLocals.push (l, paramWasmTy p)
      -- loop-shaped jp = the body jumps to ITSELF: unreachable in this
      -- lowering (the body sits outside the label's scope) — reject
      if jumpsTo fd.fvarId fd.value then
        unsupported "loop-shaped jp (the body jumps back)"
      modify fun s => { s with jps := s.jps.insert fd.fvarId (jpL, paramLocals) }
      let kI ← emitScoped k
      let bodyI ← emitScoped fd.value
      emitI (.block skipL ([.block jpL (kI ++ [.br skipL])] ++ bodyI))
      -- SEAL: every k-path branches, and the jp body's paths are
      -- terminal — control never REACHES past the $skip block's end.
      -- But the validator keeps the enclosing frame REACHABLE there
      -- (block-internal unreachability does not leak out); the
      -- unreachable closes the frame.
      emitI .unreach
  | .jmp fvarId args =>
      -- the goto: store the args into the jp's param locals, branch
      match (← get).jps[fvarId]? with
      | none => unsupported s!"jmp to unregistered jp {fvarId.name}"
      | some (jpL, paramLocals) => do
        if args.size != paramLocals.size then
          unsupported s!"jp arity drift: {args.size} args vs {paramLocals.size} params"
        for h : i in [0:args.size] do
          emitArg args[i]!
          emitI (.localset paramLocals[i]!.1)
        emitI (.br jpL)
  | .unreach _ => emitI .unreach
  | .sset _f i offset y ty k =>
      -- field store: sset var[slot, off] := y → mem[var + 8 + slot*8 + off]
      -- (the RC pass reorders fields REF-FIRST: the slot index = the
      -- field's position in the REORDERED layout — the id of a {u64,
      -- string, string, list} record is slot 3 AFTER the three ref
      -- slots. The old emission discarded `i` — the id CLOBBERED the
      -- first ref's pointer.)
      emitI (.localget (← load _f))
      emitI (.localget (← load y))
      emitI (.mem (storeMemOp (wasmTyOf? ty)) (8 + i * 8 + offset) none)
      emitCode k
  | .oset .. | .uset .. | .setTag .. =>
    unsupported "in-place mutation (oset/uset/setTag)"
  | .fun _ _ h => absurd h (by simp)

partial def emitReturn (fvarId : FVarId) : M Unit := do
  emitI (.localget (← load fvarId))
  emitI .ret

/-- Run `emitCode` in a FORKED state (fresh `out`), returning the branch
    body as a nested instr list while KEEPING the fork's local bindings,
    the fresh-local counter, and the trampolines in the outer state
    (wasm locals are function-scoped; LCNF branches terminate, so the
    branch's fvars are dead after — keeping them bound is harmless,
    the fresh-name counter guarantees uniqueness). -/
partial def emitScoped (code : Code .impure) : M (List Wat.Instr) := do
  let s ← get
  let ((), s2) ← (emitCode code).run { s with out := #[] }
  set { s2 with out := s.out }
  pure s2.out.toList

partial def emitCases (c : Cases .impure) : M Unit := do
  -- SCALAR scrutinees (Bool/UInt8 — the impl param is a raw flat
  -- value): branch on the VALUE itself. OBJECT scrutinees: tag =
  -- i32.load8_u offset=4, stashed in a temp local.
  let scalar := c.typeName == `Bool || c.typeName == `UInt8
    || c.typeName == `UInt32 || c.typeName == `UInt64
  if scalar then
    let v ← load c.discr
    emitIs (← goAlts v ((c.alts.toList.filterMap resultTyOfAlt).head?) c.alts.toList)
  else do
    emitI (.localget (← load c.discr))
    emitI (.mem .i32load8u 4 none)
    let tag ← bindFresh "i32"
    emitI (.localset tag)
    emitIs (← goAlts tag ((c.alts.toList.filterMap resultTyOfAlt).head?) c.alts.toList)

-- ONE result type for the WHOLE alt chain: a per-suffix read lets
-- the chain's LAST alt (a jp-fed arm ends in `.jmp`) pick a VOID if
-- while an EARLIER alt's `if (result i32)` owns the else slot — an
-- unreachable-but-REACHABLE empty stack at the enclosing `end`
-- (validator: unreachability does not leak out of a block end — the
-- checkWitness 3-way WProp chain). Safe because every RESOLVING arm
-- is terminal, the else path is the sole consumer, and the `.cases`
-- FALLTHROUGH SEAL discards any leftover at the chain's end.
partial def goAlts (scrut : String) : Option String → List (Alt .impure) → M (List Wat.Instr)
  | _, [] => pure [.unreach]
  | resTy, alt :: rest => do
      match alt with
      | .ctorAlt info code =>
          let thenI ← emitScoped code
          let elseI ← goAlts scrut resTy rest
          pure ([.localget scrut, .i32const info.cidx, .op .i32eq]
            ++ [.if_ resTy thenI elseI])
      | .default code => emitScoped code
      | .alt _ _ _ h => absurd h (by simp)

partial def emitLet (decl : LetDecl .impure) : M Unit := do
  let ty := wasmTyOf? decl.type
  match decl.value with
  | .lit (.uint64 v) =>
      let l ← bindLocal decl.fvarId "i64"
      emitI (.i64const v.toNat); emitI (.localset l)
  | .lit (.uint8 v) | .lit (.uint32 v) =>
      let l ← bindLocal decl.fvarId "i32"
      emitI (.i32const v.toNat); emitI (.localset l)
  | .lit (.nat v) =>
      -- THE BOUNDED-NAT LOWERING (W9.6). THE MODEL: a guest Nat is a
      -- BOXED machine int — {rc, tag, i64 payload @8} — because the
      -- pipeline RCs Nats as objects AND its compatible-types pass
      -- hands single-Nat-field structures (WStep) where Nats are
      -- expected: ONE boxed layout is the only sound representation.
      -- The owner's bounded decision pins the PAYLOAD: machine u64,
      -- never GMP; a literal at/above the cap is a DESIGN ERROR (fuel
      -- is sized `consumed × 4`). The lowered surface: Nat.lit,
      -- Nat.decEq/Nat.beq, Nat.sub (countdown), Nat.add (length-walk
      -- counter) — the fap arms below. Ctor-case dispatch on a Nat
      -- scrutinee is NOT lowered (nothing in the sanctioned closure
      -- matches on Nat): the generic tag-dispatch path would read the
      -- box's tag 0 and treat the payload as a POINTER — silently
      -- wrong — so a Nat cases reaching the emitter throws loudly.
      if v >= 4611686018427387904 then
        unsupported s!"bounded-Nat: literal {v} at/above the pinned cap 2^62 (fuel is a bounded countdown — the `consumed × 4` sizing makes this a design error)"
      let l ← bindLocal decl.fvarId "i32"
      emitI (.i32const 16); emitI (.call "alloc"); emitI (.localset l)
      emitI (.localget (← load decl.fvarId)); emitI (.i32const 0); emitI (.mem .i32store8 4 none)
      emitI (.localget (← load decl.fvarId)); emitI (.i64const v); emitI (.mem .i64store 8 none)
  | .lit (.str v) =>
      -- guestlang-std string literal: variable-size object {rc, tag=250,
      -- len@8, bytes@16} — the UTF-8 bytes stored inline (i32.store8 per
      -- byte; v1 literals are short — no data segments, no heap patch)
      let bytes := v.toByteArray
      let n := bytes.size
      let l ← bindLocal decl.fvarId "i32"
      emitI (.i32const (16 + n)); emitI (.call "alloc"); emitI (.localset l)
      emitI (.localget (← load decl.fvarId))
      emitI (.i32const stringTag)
      emitI (.mem .i32store8 4 none)
      emitI (.localget (← load decl.fvarId))
      emitI (.i32const n)
      emitI (.mem .i32store 8 none)
      let mut off := 16
      for b in bytes do
        emitI (.localget (← load decl.fvarId))
        emitI (.i32const b.toNat)
        emitI (.mem .i32store8 off none)
        off := off + 1
  | .lit _ => unsupported "literal kind (uint16/usize)"
  | .erased => pure ()
  | .fvar fvarId args =>
      if args.isEmpty then
        let l ← bindLocal decl.fvarId (ty.getD "i64")
        emitI (.localget (← load fvarId)); emitI (.localset l)
      else
        -- CLOSURE APPLICATION: f is an object; call its trampoline:
        -- push closure-ptr, fresh args (boxed), fnIdx; call_indirect.
        -- The sig is picked by the FRESH-arg count (sig_1box, sig_2box…).
        let l ← bindLocal decl.fvarId "i32"  -- result: boxed obj
        emitI (.localget (← load fvarId))  -- closure ptr (also the trampoline's 1st arg)
        for a in args do emitArg a
        emitI (.localget (← load fvarId))
        emitI (.mem .i32load 8 none)  -- fnIdx
        emitI (.callindirect s!"sig_{args.size}box")
        emitI (.localset l)
  | .fap fn args =>
      -- the bounded-Nat boundary conversion: fuel crosses the export
      -- seam as u64 and checks as Nat — the conversion BOXES the
      -- machine int (the model note at the lit arm). The unboxing
      -- direction (Nat → scalar) is NOT sanctioned: nothing in the
      -- checker's closure reads a Nat back as a raw scalar, and a
      -- silent unbox would hide the layout decision.
      if (fn == ``UInt64.toNat || fn == ``Nat.toUInt64) && args.size == 1 then
        let l ← bindLocal decl.fvarId "i32"
        emitI (.i32const 16); emitI (.call "alloc"); emitI (.localset l)
        emitI (.localget (← load decl.fvarId)); emitI (.i32const 0); emitI (.mem .i32store8 4 none)
        emitArg args[0]!
        emitI (.mem .i64store 8 none)
      else if fn == ``Nat.decEq || fn == ``Nat.beq then
        -- boxed-payload compare → the raw i32 Bool
        if args.size != 2 then unsupported s!"{fn} arity {args.size}"
        let a ← specBEqArg args[0]!
        let b ← specBEqArg args[1]!
        let l ← bindLocal decl.fvarId "i32"
        emitI (.localget (← load a)); emitI (.mem .i64load 8 none)
        emitI (.localget (← load b)); emitI (.mem .i64load 8 none)
        emitI (.op .i64eq)
        emitI (.localset l)
      else if fn == ``Nat.sub || fn == ``Nat.add || fn == ``Nat.mul then
        -- boxed-payload arith → a FRESH box (Nats are immutable under
        -- RC). All bounded: the counters walk in-memory lists, the
        -- fuel is `consumed × 4`, a decoded Nat is at most its own
        -- byte length × 7 bits — overflow is a design error (the lit
        -- arm's cap pin; no wrap check on the ops).
        if args.size != 2 then unsupported s!"{fn} arity {args.size}"
        let a ← specBEqArg args[0]!
        let b ← specBEqArg args[1]!
        let l ← bindLocal decl.fvarId "i32"
        let r ← bindFresh "i64"
        emitI (.localget (← load a)); emitI (.mem .i64load 8 none)
        emitI (.localget (← load b)); emitI (.mem .i64load 8 none)
        emitI (.op (if fn == ``Nat.sub then .i64sub
          else if fn == ``Nat.mul then .i64mul else .i64add))
        emitI (.localset r)
        emitI (.i32const 16); emitI (.call "alloc"); emitI (.localset l)
        emitI (.localget (← load decl.fvarId)); emitI (.i32const 0); emitI (.mem .i32store8 4 none)
        emitI (.localget (← load decl.fvarId)); emitI (.localget r); emitI (.mem .i64store 8 none)
      else if fn == ``Nat.decLt || fn == ``Nat.decLe then
        -- the decode lane's domain tests: the varint digit's `b.toNat <
        -- 128` (decLt) and decBytes?'s length gate `n ≤ rest.length`
        -- (decLe) — the same bounded-Nat positions as the countdown
        -- (the encoded length IS the bound). Boxed-payload compare,
        -- UNSIGNED (a Nat's machine payload is its magnitude; the
        -- bounded cap keeps signed/unsigned equal) → the RAW i32 Bool
        -- (the decEq convention — the LCNF consumes it in a Bool cases,
        -- and emitCases branches SCALAR Bool scrutinees on the value).
        if args.size != 2 then unsupported s!"{fn} arity {args.size}"
        let a ← specBEqArg args[0]!
        let b ← specBEqArg args[1]!
        let l ← bindLocal decl.fvarId "i32"
        emitI (.localget (← load a)); emitI (.mem .i64load 8 none)
        emitI (.localget (← load b)); emitI (.mem .i64load 8 none)
        emitI (.op (if fn == ``Nat.decLt then .i64ltu else .i64leu))
        emitI (.localset l)
      else if (fn == ``UInt8.toNat) && args.size == 1 then
        -- the decode lane's digit read: `b.toNat` — the raw u8 scalar
        -- (the cons head's unbox) → a BOXED Nat (payload = the
        -- zero-extended value). The bounded model: a digit is < 256.
        let l ← bindLocal decl.fvarId "i32"
        emitI (.i32const 16); emitI (.call "alloc"); emitI (.localset l)
        emitI (.localget (← load decl.fvarId)); emitI (.i32const 0); emitI (.mem .i32store8 4 none)
        emitI (.localget (← load decl.fvarId))
        emitArg args[0]!
        emitI (.op .i64extendi32u)
        emitI (.mem .i64store 8 none)
      else if (fn == ``UInt64.ofNat) && args.size == 1 then
        -- the decode lane's u64 atom: the boxed Nat payload → the raw
        -- u64 (IDENTITY at the machine model: the box payload IS the
        -- u64; the owner's bounded decision covers the decode
        -- direction — a decoded value above the u64 range is the wrap,
        -- the encoder's range is always in-domain).
        if args.size != 1 then unsupported s!"{fn} arity {args.size}"
        let l ← bindLocal decl.fvarId "i64"
        emitArg args[0]!
        emitI (.mem .i64load 8 none)
        emitI (.localset l)
      else if (fn == ``Char.ofNat) && args.size == 1 then
        -- the decode lane's char atom: `Char.ofNat n` — the boxed Nat
        -- payload → the raw u32 codepoint (WRAP: Char's scalar is u32;
        -- the codec's encoder range is the char set — the guest's
        -- $string_oflist UTF-8-encodes it).
        let l ← bindLocal decl.fvarId "i32"
        emitArg args[0]!
        emitI (.mem .i64load 8 none)
        emitI (.op .i32wrapi64)
        emitI (.localset l)
      else if (fn == ``UInt8.decEq || fn == ``UInt32.decEq
         ) && args.size == 2 then
        -- the SCALAR equality family (the decode lane's byte-pattern
        -- matches: `decOpt?`'s `0 :: rest` / `1 :: rest` compile to
        -- `UInt8.decEq` faps — the core decl is `@[extern]`, so the
        -- closure fixpoint compiles it as an unreachable stub: the
        -- inline lowering is the only body it gets). RAW scalar args
        -- (the unbox happens at the pattern's head read), the raw i32
        -- Bool result — the binop convention. A u64 beq rides i64eq;
        -- the i32 family rides i32eq.
        let a ← specBEqArg args[0]!
        let b ← specBEqArg args[1]!
        let l ← bindLocal decl.fvarId "i32"
        emitI (.localget (← load a))
        emitI (.localget (← load b))
        emitI (.op .i32eq)
        emitI (.localset l)
      else if isSpecBEqName fn then
        -- the SPECIALIZATION PRODUCT of `Option.instBEq.beq` (the audit's
        -- gap 4: the spec pass names it by its SOURCE TYPE and it never
        -- joins impureExt — the call is inline-lowered here instead).
        -- Scope: the CHECKER's spec decls ONLY (`.spec_` under the
        -- WitnessCheck `_at_` — anything else throws loudly). The
        -- payload is the checker's `Option UInt64` (boxed u64): tag
        -- compare, both-none = true, both-some = unbox + i64.eq. A
        -- different payload type would silently mis-compare — the
        -- name-scope + the checker's duel rows are the guards.
        if !(fn.toString.startsWith "Option.instBEq.beq._at_.SchemaLang.WitnessCheck.") then
          unsupported s!"specialization product outside the checker's scope: {fn}"
        if args.size != 2 then
          unsupported s!"spec-BEq arity {args.size}"
        let l ← bindLocal decl.fvarId "i32"
        let a ← specBEqArg args[0]!
        let b ← specBEqArg args[1]!
        let ta ← bindFresh "i32"
        emitI (.localget (← load a)); emitI (.mem .i32load8u 4 none); emitI (.localset ta)
        let tb ← bindFresh "i32"
        emitI (.localget (← load b)); emitI (.mem .i32load8u 4 none); emitI (.localset tb)
        -- same tag? both none (0) → 1; both some → deref each option's
        -- box ptr (@8 = the INNER UInt64 BOX) then payload i64.eq.
        -- (The @8 direct load compared the POINTERS-as-i64 — latent
        -- until a runtime value flowed: the constant sites folded at
        -- compile.)
        emitI (.localget ta); emitI (.localget tb); emitI (.op .i32eq)
        emitI (.if_ (some "i32")
          [ .localget ta, .op .i32eqz
          , .if_ (some "i32") [ .i32const 1 ]
              [ .localget (← load a), .mem .i32load 8 none, .mem .i64load 8 none
              , .localget (← load b), .mem .i32load 8 none, .mem .i64load 8 none
              , .op .i64eq ] ]
          [ .i32const 0 ])
        emitI (.localset l)
      else match binop? fn, GuestlangStd.Intrinsic.ofName? fn with
      | some op, _ =>
          let l ← bindLocal decl.fvarId (ty.getD "i64")
          for a in args do emitArg a
          emitI (.op op)
          emitI (.localset l)
      | _, some i =>
          -- std intrinsic: strlen (obj) → raw i64; strcat (obj obj) → obj
          let l ← bindLocal decl.fvarId i.resultWasmTy
          for a in args do emitArg a
          emitI (.call i.runtimeName)
          emitI (.localset l)
      | none, _ =>
          -- the local's type = the CALLEE's actual wasm result type
          -- (scalar i64 vs object i32) — the LCNF type default alone
          -- miscasts (an object-returning call stored into an i64 local
          -- = the core module INVALID).
          let calleeTy := (← get).sigs[fn]?.map (·.2)
          let l ← bindLocal decl.fvarId
            (if args.isEmpty then "i32" else calleeTy.getD (ty.getD "i64"))
          -- 0-ary fap = top-level closure const (obj); else a scalar call
          for a in args do emitArg a
          emitI (.call fn.toString)
          emitI (.localset l)
  | .pap fn args =>
      -- closure: alloc {rc, tag=254, class, fnIdx, partial args…}
      let nA := args.size
      let _tramp := s!"pap_{fn.toString}_{nA}"
      -- table slot: position in the deduped tramp list (push-order)
      let idx : Nat ← do
        let ts := (← get).tramps
        match ts.idxOf? (fn, nA) with
        | some i => pure i
        | none =>
            modify fun s => { s with tramps := s.tramps.push (fn, nA) }
            pure ts.size
      let l ← bindLocal decl.fvarId "i32"
      emitI (.i32const (16 + nA * 8))
      emitI (.call "alloc")
      emitI (.localset l)
      emitI (.localget (← load decl.fvarId))
      emitI (.i32const 254)
      emitI (.mem .i32store8 4 none)
      emitI (.localget (← load decl.fvarId))
      emitI (.i32const idx)
      emitI (.mem .i32store 8 none)
      let mut off := 16
      for a in args do
        emitI (.localget (← load decl.fvarId))
        emitArg a
        emitI (.mem .i32store off none)
        off := off + 8
  | .sproj n offset var _ =>
      -- the slot index n = the field's position in the REORDERED
      -- (ref-first) layout, offset = the byte offset within the slot —
      -- the SAME convention as the sset WRITER below. (The pre-migration
      -- emitter discarded n — it read the byte offset alone: latent
      -- until userValid, the first reader of a slot-3 scalar.)
      let tyS := ty.getD "i64"
      let l ← bindLocal decl.fvarId tyS
      emitI (.localget (← load var))
      emitI (.mem (loadMemOp tyS) (8 + n * 8 + offset) none)
      emitI (.localset l)
  | .oproj i var _ =>
      -- ref field: 8-byte slot at 8+i*8, an object pointer
      let l ← bindLocal decl.fvarId "i32"
      emitI (.localget (← load var))
      emitI (.mem .i32load (8 + i * 8) none)
      emitI (.localset l)
  | .box ty var _ =>
      -- scalar → object: alloc 16, store the scalar @8 (op by scalar ty)
      let l ← bindLocal decl.fvarId "i32"
      emitI (.i32const 16)
      emitI (.call "alloc")
      emitI (.localset l)
      emitI (.localget (← load decl.fvarId))
      emitI (.localget (← load var))
      emitI (.mem (storeMemOp (wasmTyOf? ty)) 8 none)
  | .unbox var _ =>
      -- the box's slot type = the unboxed scalar's type (Bool→i32, u64→i64)
      let tyS := ty.getD "i64"
      let l ← bindLocal decl.fvarId tyS
      emitI (.localget (← load var))
      emitI (.mem (loadMemOp tyS) 8 none)
      emitI (.localset l)
  | .ctor info args =>
      -- bare alloc + tag; REF args stored @8+i*8. Scalar fields arrive
      -- via sset afterwards (the RC pass splits scalar ctors — verified:
      -- `ctor_0.0.8[Shape.circle]` then `sset [0,0]`); ref ctors keep
      -- their args (verified: `ctor_1[List.cons] _f.2 _x.1`).
      let p ← bindLocal decl.fvarId "i32"
      emitI (.i32const (8 + info.size * 8 + info.ssize))
      emitI (.call "alloc")
      emitI (.localset p)
      emitI (.localget (← load decl.fvarId))
      emitI (.i32const info.cidx)
      emitI (.mem .i32store8 4 none)
      let mut refOff := 8
      for a in args do
        emitI (.localget (← load decl.fvarId))
        emitArg a
        emitI (.mem .i32store refOff none)
        refOff := refOff + 8
  | .proj .. | .uproj .. =>
      unsupported "proj/uproj"
  | .reset .. | .reuse .. | .isShared .. =>
      unsupported "Perceus reset/reuse/isShared"
  | .const fn _ args _ =>
      match binop? fn, args.isEmpty with
      | some op, false =>
          let l ← bindLocal decl.fvarId (ty.getD "i64")
          for a in args do emitArg a
          emitI (.op op)
          emitI (.localset l)
      | none, true =>
          -- 0-ary const: a top-level closure constant (_closed decls)
          let l ← bindLocal decl.fvarId "i32"
          emitI (.call fn.toString)
          emitI (.localset l)
      | _, _ => unsupported s!"const {fn}"

end

/-! ## Decl emission -/

/-- TYPED: the decl's func = a `Wat.Func` — the general path's body is
    fully typed `Instr`s (the raw→typed migration; the header's ledger). -/
def emitDecl (d : Decl .impure) : M Wat.Func := do
  let code := match d.value with
    | .code c => c
    | .extern .. => .unreach (Expr.const `Unit [])
  let resultTy := resultTyOf code
  for p in d.params do
    bindNamed p.fvarId p.binderName.toString (paramWasmTy p)
  emitCode code
  let s ← get
  pure { name := d.name.toString
       , params := d.params.toList.map fun p =>
           { name := some p.binderName.toString, ty := paramWasmTy p }
       , result := resultTy
       , locals := s.locals.toList
       , body := s.out.toList }

/-- Dedup trampolines (the same (fn, nPartial) pap may appear at several
    sites; the table gets ONE func per distinct trampoline). -/
def dedupTramps : List (Name × Nat) → List (Name × Nat)
  | [] => []
  | (f, n) :: rest =>
      let rest := dedupTramps rest
      if rest.any (fun p => p.1 == f && p.2 == n) then rest else (f, n) :: rest

/-! ## The adapter SHAPES (the canonical-ABI lowering table)

The adapter generator needs each export's RESULT SHAPE (how to flatten
the guest object into the canonical layout). v1: a HAND TABLE (the
generalization — schema-driven adapters — lands with the schema-typed
adapter work). The shapes' authority: the WIT world (byte-tied); a
wrong shape = a differential failure (the host misreads).

- `string`: [bytes-ptr, byte-len] — the static return area holds the
  pair; bytes-ptr = obj + 16 (bytes INLINE).
- `optionUser`: option<user> — the area holds the option's MEMORY
  layout: discr u32 @0, the record @8 (aligned 8 by the u64); the
  record's refs sit at @8/16/24, the id scalar at @32.
- default: the scalar/object conventions (scalar → raw i64; object →
  unbox).
-/

/-- The ASYNC-marked exports (the wire names; the world marks them
    `async func` — the canon lift's async option + the [callback]).
    The full async-lift recipe (the wasmparser-derived requirements:
    async func type, task-intrinsic imports, `[async-lift]`/`[callback]`
    export shapes, the task-return delivery): notes/wasm-backend-notes.md
    §async-lift. -/
def asyncFns : List String := ["watch-orders", "watch-counts", "watch-users"]

/-- The adapter result shape per export (kebab name). -/
def adapterShape? : String → Option String
  | "get-user" => some "optionUser"
  | "watch-orders" => some "listUser"
  | "watch-counts" => some "streamU64"
  | "watch-users" => some "streamUser"
  | "user-valid" => some "userParam"
  | "user-complete" => some "userParam"
  | "order-error-valid" => some "variantParam"
  -- the W9.6 witness export: bytes in (the canonical list<u8> = the
  -- (ptr, len) pair), verdict out (the raw i32 Bool)
  | "verify-witness" => some "bytesParam"
  | _ => none

/-- The TYPED WAT for walking a guest List cons chain into a canonical
    (array-ptr, count) pair written at `areaOff`/`areaOff+4`. Two passes:
    COUNT the cons cells, `$alloc(n × elemSize)`, then FILL each element
    via `lowerElem` (the per-element instrs; `$cur{suffix}` = the cons —
    its head object = `load($cur{suffix} + 8)` — `$w{suffix}` = the
    element's destination address). `suffix` uniquifies the locals/labels
    (the NESTED walks: the list-of-records' elements carry their own
    lists — the inner walk = the same generator, a different suffix). The
    cons's layout: {tag@4 (nil=0/cons=1), head@8, tail@16}. -/
def listWalk (loadSeq : List Wat.Instr) (areaOff : Nat)
    (elemSize : Nat) (suffix : String) (lowerElem : List Wat.Instr) : List Wat.Instr :=
  let cur := s!"cur{suffix}"
  let n := s!"n{suffix}"
  let arr := s!"arr{suffix}"
  let w := s!"w{suffix}"
  let doneL := s!"done{suffix}"
  let countL := s!"count{suffix}"
  let doneF := s!"donef{suffix}"
  let fillL := s!"fill{suffix}"
  let countBody : List Wat.Instr :=
    [ .localget cur, .mem .i32load8u 4 none, .op .i32eqz, .brif doneL
    , .localget n, .i32const 1, .op .i32add, .localset n
    , .localget cur, .mem .i32load 16 none, .localset cur  -- tail @16
    , .br countL ]
  let fillBody : List Wat.Instr :=
    [ .localget cur, .mem .i32load8u 4 none, .op .i32eqz, .brif doneF ]
    ++ lowerElem
    ++ [ .localget w, .i32const elemSize, .op .i32add, .localset w
       , .localget cur, .mem .i32load 16 none, .localset cur
       , .br fillL ]
  let countLoop : List Wat.Instr :=
    loadSeq ++ [ .localset cur
    , .i32const 0, .localset n
    , .block doneL [.loop countL countBody] ]
  let fillLoop : List Wat.Instr :=
    loadSeq ++ [ .localset cur
    , .localget n, .i32const elemSize, .op .i32mul, .call "alloc", .localset arr
    , .localget arr, .localset w
    , .block doneF [.loop fillL fillBody] ]
  -- the (ptr, len) stores: STATIC areaOff only. `areaOff = 0` means
  -- NO MEMORY WRITE: callers who need the list's (ptr,len) read the
  -- walk's `$arr`/`$n` LOCALS — the old scratch write at the fill-end
  -- cursor CORRUPTED the next bump allocation (it landed on the first
  -- inner-walk array). Scratch writes to "unused" memory are not
  -- unused: the bump allocator hands that region out next.
  countLoop ++ fillLoop ++
    (if areaOff == 0 then []
     else [ .i32const areaOff, .localget arr, .mem .i32store 0 none
          , .i32const (areaOff + 4), .localget n, .mem .i32store 0 none ])

/-- The per-element lowering of a `String` element (the flat pair =
    (head+16 [bytes inline], load(head+8) [len]) at `$w{suffix}`). -/
def strElemLower (suffix : String) : List Wat.Instr :=
  let cur := s!"cur{suffix}"
  let w := s!"w{suffix}"
  [ .localget w, .localget cur, .mem .i32load 8 none, .i32const 16, .op .i32add
  , .mem .i32store 0 none
  , .localget w, .localget cur, .mem .i32load 8 none, .mem .i32load 8 none
  , .mem .i32store 4 none ]

/-- The PROVED canonical-ABI flat layout of the demo's user record
    (id@0, name@8, email@16, tags@24 — size 32): the adapters' field
    offsets are THIS function's outputs, structurally. CERTIFIED: the
    caller must discharge `Layout.user_offsets` — a layout change
    without re-proving the ABI table fails to elaborate. -/
def userLayout (_cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24]) : List Nat :=
  WasmBackend.Layout.offsets WasmBackend.Layout.userTys

/-- The PROVED record size (= the stream/element-array stride),
    CERTIFIED against `Layout.user_size` (same re-proof discipline). -/
def userSize (_cert : WasmBackend.Layout.size WasmBackend.Layout.userTys = 32) : Nat :=
  WasmBackend.Layout.size WasmBackend.Layout.userTys

/-- (ptr, len) pair of the string object `src` → ABSOLUTE memory at
    `off`/`off+4` (bytes inline at src+16, len at src+8). -/
def pairAbs (off : Nat) (src : String) : List Wat.Instr :=
  [ .i32const off, .localget src, .i32const 16, .op .i32add, .mem .i32store 0 none
  , .i32const (off + 4), .localget src, .mem .i32load 8 none, .mem .i32store 0 none ]

/-- (ptr, len) pair of the string object `src` → the address in local
    `base` at `off`/`off+4` (the element-lowering form). -/
def pairRel (base : String) (off : Nat) (src : String) : List Wat.Instr :=
  [ .localget base, .localget src, .i32const 16, .op .i32add
  , .mem .i32store off none
  , .localget base, .localget src, .mem .i32load 8 none
  , .mem .i32store (off + 4) none ]

/-- The canonical-ABI variant RE-BOX: the flat (discr i32, joined-payload
    i64) arrives as core params; alloc(16) {rc, tag=discr @4, payload i64
    @8} reconstructs the guest's variant object. Shared by `variantParam`
    (order-error-valid) and `listUser` (watch-orders) — the same five
    instructions, the only difference being what follows the box. -/
def variantBox (disc payload : String) : List Wat.Instr :=
  [ .i32const 16, .call "alloc", .localset "v"
  , .localget "v", .localget disc, .mem .i32store8 4 none
  , .localget "v", .localget payload, .mem .i64store 8 none
  , .localget "v" ]

/-! ## The record-PARAM adapter (the canonical ABI's input direction)

A record param crosses the boundary FLAT while its flattened form fits
MAX_FLAT_PARAMS=16 (probed: the encoder DEMANDS `[I64, I32, I32, I32,
I32, I32, I32] -> [I32]` for the demo's user — a pointer-form core sig
fails `component new`). The adapter INVERTS the result-side lowering:
strings = alloc(16+len) + {tag=250, len@8, memory.copy bytes@16}; the
tags list = the cons chain; the user = the refs-first guest object.
The flat param list — DERIVED from the field types: a u64 flattens to
one i64; a string/list flattens to the (ptr, len) i32 pair. -/

def userFieldTys (_cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24]) : List SchemaLang.Ty :=
  WasmBackend.Layout.userTys

/-- One flat core type per canonical-ABI field flattening. -/
def flatTyOf : SchemaLang.Ty → List String
  | .u64 | .i64 => ["i64"]
  | .f64 => ["f64"]
  | .f32 => ["f32"]
  | .bool | .u8 | .u16 | .u32 | .i8 | .i16 | .i32 => ["i32"]
  | .string | .bytes | .list _ | .option _ | .result _ _ | .future _
  -- map/set flatten to the (ptr, len) pair of their wire list form
  -- (the association/element list — the `list` precedent); no
  -- map-specific ABI handling yet (W8.1: deliberate, not missing)
  | .stream _ | .tensor _ _ | .map _ _ | .set _ | .ty _ => ["i32", "i32"]

def userFlatTys (cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24]) : List String :=
  (userFieldTys cert).flatMap flatTyOf

/-- The flat params' NAMES: the id, then (ptr, len) per ref field
    (name, email, tags) — same order as `userFlatTys`. The length pin
    (below) makes a drift with the field types a BUILD failure — the
    `getD` fallback at the emission site is then dead, not a mask. -/
def userParamNames : List String := ["id", "np", "nl", "ep", "el", "tp", "tl"]

/-- THE LENGTH PIN: one name per flat core value. If `userTys` (via
    `Layout.userTys`) grows or reorders fields, this `rfl` breaks the
    build until the names list follows. -/
theorem userParamNames_length :
    userParamNames.length = (Layout.userTys.flatMap flatTyOf).length := rfl

/-- String-object construction from a flat (bytes-ptr, len) pair held
    in locals `src`/`len`: alloc(16+len) — rc=1 by the allocator — then
    tag=250 @4, len @8, and `memory.copy` moves the bytes to +16 (the
    inline form the result-side lowerings READ: strElemLower's
    inverse). The object ptr lands in local `dst`. -/
def stringCtor (src len dst : String) : List Wat.Instr :=
  [ .localget len, .i32const 16, .op .i32add, .call "alloc", .localset dst
  , .localget dst, .i32const stringTag, .mem .i32store8 4 none
  , .localget dst, .localget len, .mem .i32store 8 none
  , .localget dst, .i32const 16, .op .i32add
  , .localget src, .localget len, .memcopy ]

/-- The cons chain from the flat tags array: locals `arr` (array ptr)
    and `n` (count) → the guest List<string> head in local `acc`.
    Walks the flat array BACKWARD (i = n-1 … 0), consing each element
    onto the accumulator — the chain comes out in order. The cons
    object: {rc=1 (alloc), tag=1 @4, head@8 = the string object,
    tail@16}. The EMPTY list = an ALLOCATED `{rc, tag=0 @4}` block
    (the runtime's own `[]` ctor representation), NOT the null
    pointer: the compiled list readers (listLenU64, toVList) DEREFERENCE
    the nil tail (their tag read at offset=4) — a null acc landed that
    read on the allocator's freelist bytes at 0..4 (the user-complete
    trap: the row gate's list walk read memory[4] as a tag). -/
def consChain (arr n : String) : List Wat.Instr :=
  let i := "ti"; let p := "tq"; let src := "tsp"; let len := "tln"
  let s := "ts"; let c := "tc"; let acc := "acc"
  let body : List Wat.Instr :=
    [ .localget i, .op .i32eqz, .brif "tags-done"
    , .localget i, .i32const 1, .op .i32sub, .localset i
    -- p = arr + i*8: the i-th (ptr, len) pair
    , .localget i, .i32const 8, .op .i32mul, .localget arr, .op .i32add
    , .localset p
    , .localget p, .mem .i32load 0 none, .localset src
    , .localget p, .mem .i32load 4 none, .localset len ]
    ++ stringCtor src len s
    ++ [ .i32const 24, .call "alloc", .localset c
       , .localget c, .i32const 1, .mem .i32store8 4 none
       , .localget c, .localget s, .mem .i32store 8 none
       , .localget c, .localget acc, .mem .i32store 16 none
       , .localget c, .localset acc
       , .br "tags-loop" ]
  [ .i32const 8, .call "alloc", .localset acc
  , .localget acc, .i32const 0, .mem .i32store8 4 none
  , .localget n, .localset i
  , .block "tags-done" [.loop "tags-loop" body] ]

/-- The per-element lowering of a USER record (listUser + streamUser
    share it): the cons head = load(curU+8) → the guest User object e;
    the 32-byte flat record lands at $wU — id (the u64 @32 in the guest
    object — the ref-first order), then the (ptr,len) pairs; the tags =
    a NESTED string-list walk (the inner walk's own (ptr,len) dst = its
    scratch cursor at areaOff=0 — the ELEMENT slot is dynamic, so copy
    the (arrT,nT) into the tags field after). -/
def userElemLower (cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24]) : List Wat.Instr :=
  let fld (i : Nat) : Nat := (userLayout cert).getD i 0
  [ .localget "curU", .mem .i32load 8 none, .localset "e"
  , .localget "wU", .localget "e", .mem .i64load 32 none
  , .mem .i64store (fld 0) none
  , .localget "e", .mem .i32load 8 none, .localset "p2" ]
  ++ pairRel "wU" (fld 1) "p2"
  ++ [ .localget "e", .mem .i32load 16 none, .localset "p2" ]
  ++ pairRel "wU" (fld 2) "p2"
  ++ listWalk [.localget "e", .mem .i32load 24 none] 0 8 "T" (strElemLower "T")
  ++ [ .localget "wU", .localget "arrT", .mem .i32store (fld 3) none
     , .localget "wU", .localget "nT", .mem .i32store (fld 3 + 4) none ]

/-- Canonical-ABI adapter: flat component args → the impl's calling
convention. Borrowed-scalar params (objects in the impl) get BOXED;
raw scalars pass through; an object RESULT gets unboxed to the flat
i64. Exported under the WIT name; the impl stays internal (internal
callers keep calling it directly).

TYPED: every shape builds a `Wat.Func` — ZERO `Instr.raw` (the offsets
are structured fields fed from the PROVED `userLayout`). -/
def emitAdapter (certLayout : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (certSize : WasmBackend.Layout.size WasmBackend.Layout.userTys = 32)
    (d : Decl .impure) (shape : String) (kebab : String) : Wat.Func := Id.run do
  -- pass-through of the flat params (every shape's prologue)
  let pass : List Wat.Instr :=
    d.params.toList.map fun p => .localget p.binderName.toString
  let paramsOf : List Wat.Param :=
    d.params.toList.map fun p => { name := some p.binderName.toString, ty := paramWasmTy p }
  -- STRING result: the post-return convention — the core signature
  -- takes the return-area pointer as its LAST param; the adapter calls
  -- the impl (→ the string object), then writes (bytes-ptr, byte-len)
  -- into it. (The STRING-ness comes from the ORIGINAL def type —
  -- GenMain looks it up in the imported env — the LCNF type is erased
  -- to `obj` for every object result.)
  if shape == "string" then
    -- the shim: pass the flat args through, call the impl, write the
    -- canonical-ABI string flattening (bytes-ptr, byte-len) into a
    -- STATIC return area, return the area pointer (`[I64] -> [I32]`:
    -- MAX_FLAT_RESULTS=1; the caller copies out of OUR memory via the
    -- canon-lift memory option). The area is the fixed scratch slot at
    -- 48 (the freelist owns 0..24, the heap starts at 64; 24..64 is
    -- dead space — single-threaded, no clobber). bytes-ptr = obj + 16
    -- (bytes INLINE).
    let body : List Wat.Instr :=
      pass ++ [ .call d.name.toString, .localset "p"
      , .i32const 48, .localget "p", .i32const 16, .op .i32add
      , .mem .i32store 0 none
      , .i32const 48, .localget "p", .mem .i32load 8 none, .mem .i32store 4 none
      , .i32const 48 ]
    { name := s!"{d.name.toString}_abi"
      params := paramsOf, result := some "i32"
      locals := [("p", "i32")], body }
  else if shape == "optionUser" then
    -- option<user> lowering: the return area (56..96) holds the
    -- option's MEMORY representation: discr u32 @56, the record @64
    -- (aligned 8 by the u64). The tags list<string>: the cons-chain
    -- walk fills an 8n-byte array of (ptr,len) pairs. Option ctor
    -- tags: none = 0, some = 1 (Lean's ctor order); payload rides @8.
    let area := 56
    -- the record sits @64 (area+8); the FIELD offsets = the PROVED
    -- canonical-ABI flat layout (Layout.user_offsets = [0,8,16,24])
    let fld (i : Nat) : Nat := area + 8 + (userLayout certLayout).getD i 0
    let thenI : List Wat.Instr :=
      [ .localget "opt", .mem .i32load 8 none, .localset "u"
      -- the id (the u64 @32 in the guest object — the ref-first order)
      , .i32const (fld 0), .localget "u", .mem .i64load 32 none
      , .mem .i64store 0 none
      -- the STRING fields: the record's slot holds the STRING OBJECT's
      -- POINTER (p); the flat pair = (p+16 [bytes inline], load(p+8)
      -- [len])
      , .localget "u", .mem .i32load 8 none, .localset "p" ]
      ++ pairAbs (fld 1) "p"
      ++ [ .localget "u", .mem .i32load 16 none, .localset "p" ]
      ++ pairAbs (fld 2) "p"
      ++ listWalk [.localget "u", .mem .i32load 24 none] (fld 3) 8 "" (strElemLower "")
    let body : List Wat.Instr :=
      pass ++ [ .call d.name.toString, .localset "opt"
      -- discr = the option's ctor tag (none=0 / some=1)
      , .localget "opt", .mem .i32load8u 4 none, .localset "tag"
      , .i32const area, .localget "tag", .mem .i32store 0 none
      -- the some branch: flatten the user record (the condition = tag==1)
      , .localget "tag", .i32const 1, .op .i32eq
      , .if_ none thenI []
      , .i32const area ]
    { name := s!"{d.name.toString}_abi"
      params := paramsOf, result := some "i32"
      locals := [("opt", "i32"), ("tag", "i32"), ("u", "i32"), ("p", "i32")
                 , ("cur", "i32"), ("n", "i32"), ("arr", "i32"), ("w", "i32")]
      body }
  else if shape == "userParam" then
    -- The RECORD-PARAM adapter (user-valid): the canonical ABI hands
    -- the record FLAT — id i64 + (ptr, len) per ref field (7 core
    -- params; the encoder rejects the pointer form — see the ledger).
    -- RECONSTRUCT the guest object: string objects from the flat
    -- (bytes-ptr, len) pairs (memory.copy the bytes inline), the tags
    -- cons chain from the flat (ptr, len) array, then the refs-first
    -- User object {rc, tag@4, name@8, email@16, tags@24, id@32} (the
    -- ctor alloc 8 + 3 refs * 8 + the u64 ssize = 40; the id scalar
    -- rides the sproj [3, 0] slot = 8 + 3*8). The impl reads only the
    -- id — the validator's guest-legal shape.
    let params : List Wat.Param :=
      (userFlatTys certLayout).zipIdx.map fun (ty, i) =>
        { name := some (userParamNames.getD i "flat"), ty }
    let body : List Wat.Instr :=
      consChain "tp" "tl"
      ++ stringCtor "np" "nl" "ns"
      ++ stringCtor "ep" "el" "es"
      ++ [ .i32const 40, .call "alloc", .localset "u"
         , .localget "u", .i32const 0, .mem .i32store8 4 none
         , .localget "u", .localget "ns", .mem .i32store 8 none
         , .localget "u", .localget "es", .mem .i32store 16 none
         , .localget "u", .localget "acc", .mem .i32store 24 none
         , .localget "u", .localget "id", .mem .i64store 32 none
         , .localget "u"
         , .call d.name.toString ]
    { name := s!"{d.name.toString}_abi"
      params := params, result := some "i32"
      locals := [("ti", "i32"), ("tq", "i32"), ("tsp", "i32"), ("tln", "i32")
                , ("ts", "i32"), ("tc", "i32"), ("acc", "i32")
                , ("ns", "i32"), ("es", "i32"), ("u", "i32")]
      body }
  else if shape == "variantParam" then
    -- The VARIANT-PARAM adapter (order-error-valid): the canonical ABI
    -- hands a variant FLAT — the discr i32 + the JOINED payload (the
    -- max of the cases' flat types: invalid-item's [i64] and
    -- insufficient-funds' [f64] join to i64). The RE-BOX (variantBox)
    -- reconstructs the guest's variant object. The SYNC bool result:
    -- the impl's Bool = raw i32 — no return area.
    let body : List Wat.Instr :=
      variantBox "into_disc" "into_payload"
      ++ [ .call d.name.toString ]
    { name := s!"{d.name.toString}_abi"
      params := [ { name := some "into_disc", ty := "i32" }
                , { name := some "into_payload", ty := "i64" } ]
      result := some "i32"
      locals := [("v", "i32")]
      body }
  else if shape == "listUser" then
    -- list<user> lowering (the ASYNC watch-orders' result): the outer
    -- walk lowers EACH user into a 32-byte flat record (the tags = a
    -- NESTED string-list walk). The return area (56..64) = the list's
    -- own (ptr, len). The VARIANT param: the canonical ABI flattens a
    -- variant = the discr + the max payload — the adapter RE-BOXES.
    let boxed : List Wat.Instr := variantBox "into_disc" "into_payload"
    -- the ASYNC delivery (the listUser shape = watch-orders-specific,
    -- and watch-orders = the async fn): call task-return(ptr, len) —
    -- the flat results — then return 0 (the task = complete at the
    -- first poll; the callback = Exit). The area (56..64) = still
    -- filled (the lift's copy-out = the task-return's arg-based).
    let areaTail : List Wat.Instr :=
      [ .i32const 56, .localget "arrU", .mem .i32store 0 none
      , .i32const 60, .localget "nU", .mem .i32store 0 none
      , .i32const 56, .i32const 60, .mem .i32load 0 none, .call s!"tr_{kebab}"
      , .i32const 0 ]
    let body : List Wat.Instr :=
      boxed
      ++ [ .call d.name.toString, .localset "lst" ]
      ++ listWalk [.localget "lst"] 0 (userSize certSize) "U" (userElemLower certLayout)
      ++ areaTail
    { name := s!"{d.name.toString}_abi"
      params := [ { name := some "into_disc", ty := "i32" }
                , { name := some "into_payload", ty := "i64" } ]
      result := some "i32"
      locals := [("v", "i32"), ("lst", "i32"), ("curU", "i32"), ("nU", "i32")
                 , ("arrU", "i32"), ("wU", "i32"), ("e", "i32"), ("p2", "i32")
                 , ("curT", "i32"), ("nT", "i32"), ("arrT", "i32"), ("wT", "i32")]
      body }
  else if shape == "streamU64" || shape == "streamUser" then
    -- STREAM lowering (the ASYNC watch-counts/watch-users):
    -- stream.new → the i64 handle PAIR ((write << 32) | read —
    -- wasmtime's ResourcePair packing); the List walk lowers each
    -- element into a contiguous item array; stream.write = the
    -- ASYNC-lowered name. THE DELIVERY DANCE: the abi fn =
    -- task-return(read) + stash (wr, arr, n) in the GLOBALS + return 1
    -- (YIELD — 0 = Exit tears the task down and the in-flight write's
    -- items are LOST); the HOST registers the consumer post-call; the
    -- writer's resumption event fires the CALLBACK = the WRITE SITE:
    -- write into the waiting consumer, then Exit.
    -- the per-element lowering + the walk's shape, by the payload
    let (elemSize, elemLower, walkSuffix, extraLocals) :=
      if shape == "streamU64" then
        (8,
         [ .localget "w", .localget "cur", .mem .i32load 8 none
         , .mem .i64load 8 none, .mem .i64store 0 none ],
         "", [])
      else
        -- the SAME proved layout as watch-orders' listUser (the element
        -- encoding = the canonical record — userLayout + userSize)
        (userSize certSize, userElemLower certLayout, "U",
         [ ("curU", "i32"), ("nU", "i32"), ("arrU", "i32"), ("wU", "i32")
         , ("e", "i32"), ("p2", "i32"), ("curT", "i32"), ("nT", "i32")
         , ("arrT", "i32"), ("wT", "i32") ])
    let arrN := if shape == "streamU64" then "arr" else "arrU"
    let nN := if shape == "streamU64" then "n" else "nU"
    let body : List Wat.Instr :=
      pass ++ [ .call d.name.toString, .localset "lst"
      , .call s!"sn_{kebab}", .localset "h"
      , .localget "h", .op .i32wrapi64, .localset "rd"
      , .localget "h", .i64const 32, .op .i64shru, .op .i32wrapi64, .localset "wr" ]
      ++ listWalk [.localget "lst"] 0 elemSize walkSuffix elemLower
      ++ [ -- the stash + the yield (the callback = the write site)
           .localget "wr", .globalset "wr_g"
        , .localget arrN, .globalset "arr_g"
        , .localget nN, .globalset "n_g"
        , .localget "rd", .call s!"tr_{kebab}"
        , .i32const 1 ]
    { name := s!"{d.name.toString}_abi"
      params := paramsOf, result := some "i32"
      locals := [("h", "i64"), ("rd", "i32"), ("wr", "i32"), ("lst", "i32")
                 , ("cur", "i32"), ("n", "i32"), ("arr", "i32"), ("w", "i32")]
                 ++ extraLocals
      body }
  else if shape == "bytesParam" then
    -- The BYTES-PARAM adapter (verify-witness, the W9.6 decode lane):
    -- the canonical ABI flattens a `list<u8>` param to the (ptr, len)
    -- i32 pair of a byte array the lift copied into guest memory; the
    -- adapter reconstructs the guest List UInt8 cons chain: elements =
    -- BOXED u8s, cells = {tag=1@4, head@8, tail@16}, built BACKWARD
    -- (the consChain discipline); the EMPTY list = the allocated
    -- {rc, tag=0} block (never the null pointer). The verdict = the
    -- impl's raw i32 Bool, returned directly.
    let body : List Wat.Instr :=
      [ .i32const 8, .call "alloc", .localset "acc"
      , .localget "acc", .i32const 0, .mem .i32store8 4 none
      , .localget "len", .localset "i"
      , .block "bts-done" [.loop "bts-loop"
            [ .localget "i", .op .i32eqz, .brif "bts-done"
            , .localget "i", .i32const 1, .op .i32sub, .localset "i"
            -- the element's u8 box
            , .i32const 16, .call "alloc", .localset "bx"
            , .localget "bx", .i32const 0, .mem .i32store8 4 none
            , .localget "bx", .localget "ptr", .localget "i", .op .i32add
            , .mem .i32load8u 0 none, .mem .i32store 8 none
            -- the cons cell
            , .i32const 24, .call "alloc", .localset "c"
            , .localget "c", .i32const 1, .mem .i32store8 4 none
            , .localget "c", .localget "bx", .mem .i32store 8 none
            , .localget "c", .localget "acc", .mem .i32store 16 none
            , .localget "c", .localset "acc"
            , .br "bts-loop" ] ]
      , .localget "acc", .call d.name.toString ]
    { name := s!"{d.name.toString}_abi"
      params := [ { name := some "ptr", ty := "i32" }
                , { name := some "len", ty := "i32" } ]
      result := some "i32"
      locals := [("acc", "i32"), ("i", "i32"), ("bx", "i32"), ("c", "i32")]
      body }
  else
    -- the GENERAL prologue: pass through / re-box the flat params, call
    -- the impl, return its result (the object case unboxes the flat i64
    -- from the box's slot @8). TYPED (the adapters' minimum).
    let code := match d.value with | .code c => c | .extern .. => .unreach (Expr.const `Unit [])
    let resultTy := resultTyOf code
    let mut body : List Wat.Instr := []
    let mut boxLocals : Array String := #[]
    let mut pIdx := 0
    for p in d.params do
      let flat := paramWasmTy p
      if p.borrow then
        -- box the flat arg (scalar op: i32 for Bool/u8/u32, else i64).
        -- The TAG byte = the flat value for i32 params (bools are CASES'd
        -- — the impl reads the tag); i64 params get tag 0.
        let stOp : Wat.MemOp := if flat == "i64" then .i64store else .i32store
        let pName := s!"b{pIdx}"
        body := body ++ [ .i32const 16, .call "alloc", .localset pName
          , .localget pName, .localget p.binderName.toString, .mem stOp 8 none
          , .localget pName ]
        if flat == "i32" then
          body := body ++ [ .localget p.binderName.toString, .mem .i32store8 4 none ]
        else
          body := body ++ [ .i32const 0, .mem .i32store8 4 none ]
        body := body ++ [ .localget pName ]
        boxLocals := boxLocals.push pName
      else
        body := body ++ [ .localget p.binderName.toString ]
      pIdx := pIdx + 1
    body := body ++ (match resultTy with
      | some _ => [ .call d.name.toString ]
      | none => [ .call d.name.toString, .mem .i64load 8 none ])
    { name := s!"{d.name.toString}_abi"
      params := paramsOf, result := some (resultTy.getD "i64")
      locals := boxLocals.toList.map fun n => (n, "i32")
      body }

/-- Emit the module: runtime + funcs + trampolines + table + adapters +
exports. The state THREADS across decls (tramps accumulate). -/
def emitModule (decls : List (Decl .impure))
    (exportTargets : List (String × Name))
    (stringResult? : Name → Bool := fun _ => false) : M String := do
  -- decl signatures FIRST (the fap emitter needs the callee's wasm
  -- result type during the decls' emit)
  let sigs : Std.HashMap Name (Array String × String) :=
    decls.foldl (fun m d =>
      let rt := match d.value with | .code c => resultTyOf c | .extern .. => none
      m.insert d.name (d.params.map (fun p => paramWasmTy p), rt.getD "i32")) {}
  let mut st : S := { sigs := sigs }
  let mut funcs : List Wat.Func := []
  for d in decls do
    let (f, s2) ← emitDecl d |>.run st
    st := { s2 with out := #[], locals := #[] }
    funcs := funcs ++ [f]
  -- Trampolines: (closure i32, boxed fresh args…) → boxed result.
  -- The FRESH count = the target's arity − nA; every arg (captured or
  -- fresh) is a boxed object; the target's param types decide
  -- unbox-vs-forward; a raw i64 result gets boxed.
  let mut trampFuncs : List Wat.Func := []
  let mut elem : List String := []
  for (fn, nA) in dedupTramps st.tramps.toList do
    let name := s!"pap_{fn.toString}_{nA}"
    let (paramTys, resTy) := sigs[fn]?.getD (#[], "i32")
    let nFresh := paramTys.size - nA
    let boxed := fn.toString.endsWith "_boxed" || fn.toString.endsWith "_closed"
    let mut body : List Wat.Instr := []
    let mut off := 16
    -- THE CLOSURE-APPLICATION RC CONTRACT (the use-after-free repair):
    -- Lean's `lean_apply_N` CONSUMES one reference of the closure (the
    -- LCNF's `inc[ref] f` before a fap protects f for later uses), and
    -- the target-wrapper DECS its borrowed params — including the
    -- forwarded CAPTURED fields. The trampoline therefore (a) INCs each
    -- forwarded captured field (the wrapper's dec consumes THAT ref; the
    -- closure keeps its own for later applications) and (b) DECs the
    -- closure itself after the call. Without (a), a closure applied
    -- twice loses its captured field's only ref at the first application
    -- (the differential batch's tampered rows: use-after-free → the
    -- freelist poisoning → the alloc fault). Without (b), closures leak.
    if boxed then
      -- boxed target: forward every arg as-is (objects in, object out)
      for _ in [0:nA] do
        body := body ++ [ .localget "c", .mem .i32load off none, .call "rc_inc"
                        , .localget "c", .mem .i32load off none ]
        off := off + 8
      for i in [0:nFresh] do
        body := body ++ [ .localget s!"x{i}" ]
      body := body ++ [ .call fn.toString, .localget "c", .call "rc_dec" ]
    else if resTy == "i64" then
      -- raw SCALAR target: unbox captured + fresh args, call, box
      -- result. The convention split is the CALLEE's OWN signature
      -- (the sigs table): a raw i64 param is the scalar convention
      -- (unbox), an i32 param is the OBJECT convention (forward — the
      -- decode lane's first-class fns pass a list-taking decoder as a
      -- closure value; the old blanket unbox-everything unboxed the
      -- cons HEAD SLOT as the argument). A raw i32 param is ambiguous
      -- (Bool scalar OR object) — no Bool-param target joins a
      -- trampoline in the sanctioned closure; a drift throws at
      -- validate, never silently misreads.
      for i in [0:nA] do
        let tyI := (paramTys.getD i "i32")
        if tyI == "i64" then
          body := body ++ [ .localget "c", .mem .i32load off none, .mem .i64load 8 none ]
        else
          -- object captured field: the target-convention transfer — INC
          -- (the closure keeps its own ref; see the RC contract note above)
          body := body ++ [ .localget "c", .mem .i32load off none, .call "rc_inc"
                          , .localget "c", .mem .i32load off none ]
        off := off + 8
      for i in [0:nFresh] do
        let tyI := (paramTys.getD (nA + i) "i32")
        if tyI == "i64" then
          body := body ++ [ .localget s!"x{i}", .mem .i64load 8 none ]
        else
          body := body ++ [ .localget s!"x{i}" ]
      body := body ++ [ .call fn.toString, .localset "r", .i32const 16
        , .call "alloc", .localtee "p", .localget "r", .mem .i64store 8 none
        , .localget "p", .localget "c", .call "rc_dec" ]
    else
      -- raw OBJECT target (an i32 result): forward every arg as-is —
      -- the boxed branch's shape at an unsuffixed name (the decode
      -- lane's first-class decoders: object in, Option object out)
      for _ in [0:nA] do
        body := body ++ [ .localget "c", .mem .i32load off none, .call "rc_inc"
                        , .localget "c", .mem .i32load off none ]
        off := off + 8
      for i in [0:nFresh] do
        body := body ++ [ .localget s!"x{i}" ]
      body := body ++ [ .call fn.toString, .localget "c", .call "rc_dec" ]
    let params : List Wat.Param :=
      { name := some "c", ty := "i32" } ::
        (List.range nFresh).map fun i => { name := some s!"x{i}", ty := "i32" }
    let locals : List (String × String) :=
      if resTy == "i64" then [("r", "i64"), ("p", "i32")] else []
    trampFuncs := trampFuncs ++
      [ { name, params, result := some "i32", locals, body } ]
    elem := elem ++ [name]
  -- the call_indirect TYPE per distinct fresh count (all params i32:
  -- the closure ptr + boxed fresh args — the result is always a box)
  let mut freshCounts : List Nat := []
  for (fn, nA) in dedupTramps st.tramps.toList do
    let nF := (sigs[fn]?.getD (#[], "i32")).1.size - nA
    if !freshCounts.contains nF then freshCounts := freshCounts ++ [nF]
  let sigTypes : List Wat.Item := freshCounts.map fun nF =>
    .ty { name := s!"sig_{nF}box"
        , params := (List.range (nF + 1)).map fun _ => { name := none, ty := "i32" }
        , result := some "i32" }
  -- canonical-ABI adapters for the export targets
  let mut abiFuncs : List Wat.Func := []
  for (kebab, n) in exportTargets do
    for d in decls do
      if d.name.toString == n.toString then
        let shape := if stringResult? n then "string" else adapterShape? kebab |>.getD "default"
        abiFuncs := abiFuncs ++ [emitAdapter WasmBackend.Layout.user_offsets WasmBackend.Layout.user_size d shape kebab]
  -- DECISION (the post-return functions): wit-bindgen's modules carry
  -- `cabi_post_<name>` (the dealloc hook the canon lift calls after
  -- copying the results). OURS don't — the adapters use the STATIC
  -- return area (nothing to free) and `component new`'s encoder
  -- accepts the post-return's ABSENCE (emitting one with a wrong
  -- shape FAILS the encode: the encoder validates cabi_post_* against
  -- the function's flat params). Omit until the async work needs the
  -- real task dealloc.

  -- the ASYNC-lifted exports: the main export (the SYNC convention:
  -- the params + the return-area result) + the [callback] companion
  -- (the canonical lift POLLS it: (i32 ordinal, i32 handle, i32
  -- result) -> i32 CallbackCode; Exit=0/Yield=1). OUR compiled bodies
  -- are SYNC-computable — the task completes on the FIRST poll — the
  -- callback = the constant Exit.
  let asyncTargets := exportTargets.filter fun (kebab, _) => asyncFns.contains kebab
  -- the ASYNC-lifted exports' CORE NAMES = the encoder's convention:
  -- the main = `[async-lift]{name}` (the world-level key = the BARE
  -- kebab; the plain-name export is INVISIBLE to the async encoder),
  -- the callback = `[callback][async-lift]{name}`, sig (i32 ordinal,
  -- i32 handle, i32 result) -> i32.
  let cbFuncs : List Wat.Func := asyncTargets.map fun (kebab, _) =>
    let sig3 : List Wat.Param :=
      [{ name := none, ty := "i32" }, { name := none, ty := "i32" }, { name := none, ty := "i32" }]
    match adapterShape? kebab with
    | some "streamU64" | some "streamUser" =>
      -- the write SITE: the writer's resumption (the reader = ready)
      -- re-enters here; write the stashed (wr, arr, n) into the
      -- waiting consumer, then Exit (0)
      { name := s!"[callback][async-lift]{kebab}"
        params := sig3, result := some "i32", locals := []
        body := [ .globalget "wr_g", .globalget "arr_g", .globalget "n_g"
                , .call s!"sw_{kebab}", .drop, .i32const 0 ] }
    | _ =>
      { name := s!"[callback][async-lift]{kebab}"
        params := sig3, result := some "i32", locals := []
        body := [ .i32const 0 ] }
  let cbExports : List Wat.Item := asyncTargets.map fun (kebab, _) =>
    .export { name := s!"[callback][async-lift]{kebab}"
            , desc := .func s!"[callback][async-lift]{kebab}" }
  -- the task intrinsics' imports (the async lift requires them —
  -- notes/wasm-backend-notes.md §async-lift); the waitables/context =
  -- ONCE (shared); the task-return + the stream intrinsics = PER
  -- async export, shaped by the adapter's RESULT: the list = (i32,
  -- i32); the stream = the READ handle + the stream-new/write/
  -- drop-writable intrinsics (the write = the ASYNC-lowered name).
  -- The stream TYPE index (0) = the payload's position in the fn's
  -- futures-and-streams list.
  let waitables : List Wat.Item :=
    [ .imp { module := "$root", name := "[waitable-set-poll]", id := none
           , params := [{ name := none, ty := "i32" }, { name := none, ty := "i32" }]
           , result := some "i32" }
    , .imp { module := "$root", name := "[waitable-set-new]", id := none
           , params := [], result := some "i32" }
    , .imp { module := "$root", name := "[waitable-join]", id := none
           , params := [{ name := none, ty := "i32" }, { name := none, ty := "i32" }]
           , result := none }
    , .imp { module := "$root", name := "[context-get-0]", id := none
           , params := [], result := some "i32" }
    , .imp { module := "$root", name := "[context-set-0]", id := none
           , params := [{ name := none, ty := "i32" }], result := none }
    , .imp { module := "[export]$root", name := "[task-cancel]", id := none
           , params := [], result := none }
    , .imp { module := "$root", name := "[waitable-set-drop]", id := none
           , params := [{ name := none, ty := "i32" }], result := none } ]
  let perExport : String → List Wat.Item := fun kebab =>
    match adapterShape? kebab with
    | some "streamU64" | some "streamUser" =>
      [ .imp { module := "[export]$root", name := s!"[task-return]{kebab}"
             , id := some s!"tr_{kebab}", params := [{ name := none, ty := "i32" }]
             , result := none }
      , .imp { module := "[export]$root", name := s!"[stream-new-0]{kebab}"
             , id := some s!"sn_{kebab}", params := [], result := some "i64" }
      , .imp { module := "[export]$root", name := s!"[async-lower][stream-write-0]{kebab}"
             , id := some s!"sw_{kebab}"
             , params := [{ name := none, ty := "i32" }, { name := none, ty := "i32" }
                        , { name := none, ty := "i32" }]
             , result := some "i32" }
      , .imp { module := "[export]$root", name := s!"[stream-drop-writable-0]{kebab}"
             , id := some s!"sdw_{kebab}", params := [{ name := none, ty := "i32" }]
             , result := none } ]
    | _ =>
      [ .imp { module := "[export]$root", name := s!"[task-return]{kebab}"
             , id := some s!"tr_{kebab}"
             , params := [{ name := none, ty := "i32" }, { name := none, ty := "i32" }]
             , result := none } ]
  let asyncImports : List Wat.Item :=
    if asyncTargets.isEmpty then []
    else waitables ++ asyncTargets.flatMap fun (kebab, _) => perExport kebab
  -- the canon lift's indirect calls go through the table + the async
  -- shims realloc through cabi_realloc (the bump alloc ignores the
  -- old-ptr/old-size/align args)

  -- the EXPORT-NAME map: ALL exports = the world-level (the async =
  -- the [async-lift]-prefixed bare name; the interface-split = the
  -- wit-component fused-adapter mismatch).
  let exports : List Wat.Item := exportTargets.map fun (kebab, n) =>
    .export { name := if asyncFns.contains kebab then s!"[async-lift]{kebab}" else kebab
            , desc := .func s!"{n.toString}_abi" }
  let table : List Wat.Item := if !sigTypes.isEmpty then
    sigTypes ++
    [ .table { size := st.tramps.size, elemTy := "funcref" }
    , .elem { offset := .i32const 0, funcs := elem } ]
  else []
  -- the canon lift reads guest memory (string/list results are copied
  -- out of it) — the memory MUST be exported under the canonical name
  let memExport : List Wat.Item := [ .export { name := "memory", desc := .memory 0 } ]
  let isStream : String → Bool := fun k =>
    match adapterShape? k with | some "streamU64" | some "streamUser" => true | _ => false
  let streamGlobals : List Wat.Item := if asyncFns.iter.any isStream
    then [ .global { name := "wr_g", ty := "i32", isMut := true, init := .i32const 0 }
         , .global { name := "arr_g", ty := "i32", isMut := true, init := .i32const 0 }
         , .global { name := "n_g", ty := "i32", isMut := true, init := .i32const 0 } ]
    else []
  let cabiRealloc : Wat.Func :=
    { name := "cabi_realloc"
      params := (List.range 4).map fun _ => { name := none, ty := "i32" }
      result := some "i32", locals := []
      body := [ .localget "3", .call "alloc" ] }
  let asyncEnv : List Wat.Item := if asyncFns.isEmpty then []
    else asyncImports
      ++ streamGlobals
      ++ [ .func cabiRealloc
         , .export { name := "cabi_realloc", desc := .func "cabi_realloc" } ]
      ++ (if st.tramps.isEmpty
          then [ .table { size := 4, elemTy := "funcref" }
               , .export { name := "__indirect_function_table", desc := .table 0 } ]
          else [ .export { name := "__indirect_function_table", desc := .table 0 } ])
  -- THE TYPED MODULE: rendered by Wat.Module.render (Std.Format). The
  -- splice marker = the ONE module-level raw (GenMain replaces its exact
  -- bytes with runtime.wat).
  let mod : Wat.Module :=
    { start := none
      items := asyncEnv ++ [ .raw "  ;;RUNTIME-SPLICE", .memory 1 ]
        ++ (funcs.map Wat.Item.func) ++ (abiFuncs.map Wat.Item.func)
        ++ (cbFuncs.map Wat.Item.func) ++ (trampFuncs.map Wat.Item.func)
        ++ table ++ exports ++ cbExports ++ memExport }
  -- the outer StateT state = the mut var's final value (the decl loop
  -- runs in INNER .run's — without this put, StateT.run returns the
  -- initial {}). GenMain reads rawCount from it.
  modify (fun _ => st)
  pure mod.render

end WasmBackend
