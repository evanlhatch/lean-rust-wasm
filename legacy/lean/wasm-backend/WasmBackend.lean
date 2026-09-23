import Lean
import Lean.Compiler.LCNF
import WasmBackend.Check
import WasmBackend.Layout
import WasmBackend.Sem
import WasmBackend.Wat
import GuestlangStd.StrOps

/-!
# WasmBackend — LCNF → WAT emission

The `leanir` re-run pattern (see WasmGenMain): the final impure-phase LCNF →
WebAssembly Text, `wasm-tools parse -g` → validate → wasmtime. Owned by the
wasm-backend package; the ONE intentional raw is the module-level
`;;RUNTIME-SPLICE` marker (WasmGenMain splices runtime.wat) — `Instr.raw` is
banned (Audit.lean). Driving decisions: TYPED WAT (everything is a
`Wat.Module`/`Wat.Func`, offsets from the PROVED `Layout.offsets`), the
bounded-Nat boxed model, unsupported constructs THROW at emission (never
emit comments). Essays: notes/wasm-backend-notes.md.
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
    -- LCNF — the guest model is the raw i32 codepoint.
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
  n : Nat := 0
  /-- trampolines emitted so far (pap closures): (fnName, nPartial). -/
  tramps : Array (Name × Nat) := #[]
  /-- every decl's (param types, result type) — populated by emitModule
  BEFORE the decls emit (the fap result-type lookup needs the callee's
  wasm result: object = i32, scalar = i64 — the type default alone
  miscasts the local). -/
  sigs : Std.HashMap Name (Array String × String) := {}
  /-- the join points IN SCOPE, by their fvar: (label, (param local, ty)…)
      — the `.jmp` sites' store/branch targets. -/
  jps : Std.HashMap FVarId (String × Array (String × String)) := {}
  deriving Inhabited

abbrev M := StateT S (Except String)

/-- The PRIMITIVE: emit one typed instruction. -/
def emitI (i : Wat.Instr) : M Unit :=
  modify fun s => { s with out := s.out.push i }

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

/-- The LCNF specialization-product naming: the spec pass names a
    specialized instance-method call by its SOURCE —
    `<method>._at_.<caller>.spec_<n>`. The `Option.instBEq.beq` spec
    never joins impureExt (a base-phase decl only, not in
    `env.constants`), so its call sites are inline-lowered here. -/
def isSpecBEqName (n : Name) : Bool :=
  n.toString.startsWith "Option.instBEq.beq._at_."

/-- The bounded-Nat fap surface the emitter INLINE-lowers at the
    `emitLet .fap` arms: no callee decl exists (extern primitives),
    nothing to compile or call — the operand-arity-checked arms
    (Nat.decEq/beq/sub/add, the UInt64↔Nat seam). The callee
    COLLECTOR and the UNSUPPORTED-LCNF diagnostic must agree with this
    surface: chasing these names adds extern stubs + broken adapters;
    flagging them re-bans the sanctioned surface. -/
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

/-! ## The ONE impure-`Code` traversal skeleton

`Code.foldImpure` is a structural fold; a WALKER = a `spineAcc` + a
`step` algebra + a seed. Policy (stated, so each walker's fit is
checkable):

- the SPINE (`k`-bearing nodes) folds its `k` with the
  `spineAcc`-updated accumulator — a `let` may REPLACE the accumulator
  (resultTyOf's most-recent-let type);
- the NESTED bodies (jp/fun values, the case alts) fold with the SEED
  — a nested body RESTARTS the fold (walk-from-none);
- `step` sees the node, its accumulator, the nested folds, the alt
  folds (ctor/default order), and the continuation's fold (`none`
  where the node has no `k`): every short-circuit, kill, and leaf
  decision is the walker's — no forced unification. EAGER (pure
  walkers only; every consumer is).

The MONADIC variant (`Code.foldImpureM`): the EMITTER is one of its
algebras (`emitStep` below) — the same traversal with the folds handed
to `step` LAZY (eagerness would break the fresh-local-counter ORDER,
part of the byte-tie) and the continuation's RAW code exposed beside
its fold (the `let x := fap …; return x` tail-call fusion inspects the
`k` shape). BYTE-TIE: the emitted stream is pinned by `just
wasm-compile && just wasm-diff-check` (bytes identical) plus
`Correct.lean`'s `runEmit` extraction checks.

Walkers that do NOT fit (left alone, honestly): WasmGenMain.lean's
`reportUnsupportedLCNF` walk (its diagnostic PATHS are child-position
labels — `/jpK`, `/caseD` — the skeleton does not carry). -/

-- The skeleton stays in the WasmBackend namespace (the file's `open`s
-- open Lean/Compiler/LCNF SEPARATELY — `Code.foldImpure` would NOT
-- resolve through Lean.Compiler.LCNF from here); referenced cross-file
-- as `WasmBackend.Code.foldImpure`.

/-- The alt walker's impossible-ctor discharge (the `.alt` ctor carries
    a `False` proof — every walker `absurd`s it; here once). -/
private def Alt.foldImpure {α : Type}
    (go : Code .impure → α → α) (a : Alt .impure) (seed : α) : α :=
  match a with
  | .ctorAlt _ code => go code seed
  | .default code => go code seed
  | .alt _ _ _ h => absurd h (by simp)

private def Alt.foldImpureM {α : Type} {m : Type → Type} [Monad m]
    (go : Code .impure → m α) (a : Alt .impure) : m α :=
  match a with
  | .ctorAlt _ code => go code
  | .default code => go code
  | .alt _ _ _ h => absurd h (by simp)

/-- The MONADIC traversal skeleton: `Code.foldImpure` with the folds
    handed to `step` LAZY — a `step` that sequences effects (the
    emitter: instruction ORDER, fresh-local-counter ORDER, state
    forking) controls exactly when each child fold runs. -/
partial def Code.foldImpureM {α : Type} {m : Type → Type} [Monad m]
    (spineAcc : Code .impure → α → α)
    (step : Code .impure → α → Option (m α) → List (m α) →
        Option (Code .impure × m α) → m α)
    (seed : α) (code : Code .impure) (acc : α) : m α :=
  match code with
  | .jp fd k =>
      step code acc (some (Code.foldImpureM spineAcc step seed fd.value seed))
        [] (some (code, Code.foldImpureM spineAcc step seed k (spineAcc code acc)))
  | .fun fd k _ =>
      step code acc (some (Code.foldImpureM spineAcc step seed fd.value seed))
        [] (some (code, Code.foldImpureM spineAcc step seed k (spineAcc code acc)))
  | .cases c =>
      step code acc none
        (c.alts.toList.map fun a =>
            Alt.foldImpureM (fun c' => Code.foldImpureM spineAcc step seed c' seed) a)
        none
  | .jmp .. | .return _ | .unreach _ => step code acc none [] none
  | .let _ k | .sset _ _ _ _ _ k | .uset _ _ _ k | .oset _ _ _ k | .setTag _ _ k
  | .inc _ _ _ _ k | .dec _ _ _ _ _ k | .del _ k =>
      step code acc none []
        (some (k, Code.foldImpureM spineAcc step seed k (spineAcc code acc)))

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

/-- Loop-shaped jp (the body jumping back to ITSELF) is unreachable in
    the block lowering — the body sits outside the label's scope.
    Conservative reject. -/
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
variable-size object (16 + len), the bytes INLINE. Byte-length ≠
char-length off ASCII (documented, v1). -/

def stringTag : Nat := 250

def storeMemOp (ty : Option String) : Wat.MemOp :=
  match ty with | some "i32" => .i32store | _ => .i64store

def loadMemOp (tyS : String) : Wat.MemOp :=
  if tyS == "i64" then .i64load else .i32load

def emitIs (is : List Wat.Instr) : M Unit :=
  is.forM emitI

def emitArg : Arg .impure → M Unit
  | .fvar fvarId => do emitI (.localget (← load fvarId))
  -- erased args push NOTHING (LCNF is ANF, so real args are always
  -- fvars; the erased case is the unit filler)
  | _ => pure ()

/-- The spine accumulator: a `let` REPLACES the accumulated type with
    its own wasm type (the most-recent-let rule); every other node
    threads it unchanged. (Object-typed lets — ctor/pap/fn-typed — are
    i32 pointers.) -/
private def resultTyOfSpineAcc : Code .impure → Option String → Option String
  | .let decl _, _ => some ((wasmTyOf? decl.type).getD "i32")
  | _, a => a

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

partial def resultTyOfAlt (a : Alt .impure) : Option String :=
  Alt.foldImpure (fun c _ => resultTyOf c) a none

/-- Run `act` in a FORKED state (fresh `out`), returning the emitted
    instrs while KEEPING the fork's local bindings, the fresh-local
    counter, and the trampolines in the outer state (wasm locals are
    function-scoped; the branch's fvars are dead after — keeping them
    bound is harmless, the fresh-name counter guarantees uniqueness). -/
private def scopedOut (act : M Unit) : M (List Wat.Instr) := do
  let s ← get
  let ((), s2) ← act.run { s with out := #[] }
  set { s2 with out := s.out }
  pure s2.out.toList

partial def emitReturn (fvarId : FVarId) : M Unit := do
  emitI (.localget (← load fvarId))
  emitI .ret

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
      -- THE BOUNDED-NAT LOWERING. THE MODEL: a guest Nat is a BOXED
      -- machine int — {rc, tag, i64 payload @8} — because the pipeline
      -- RCs Nats as objects AND its compatible-types pass hands
      -- single-Nat-field structures (WStep) where Nats are expected:
      -- ONE boxed layout is the only sound representation. The owner's
      -- bounded decision pins the PAYLOAD: machine u64, never GMP; a
      -- literal at/above the cap is a DESIGN ERROR (fuel is sized
      -- `consumed × 4`). The lowered surface: Nat.lit, Nat.decEq/beq,
      -- Nat.sub (countdown), Nat.add (length-walk counter) — the fap
      -- arms below. Ctor-case on a Nat scrutinee is NOT lowered: the
      -- generic tag-dispatch path would read the box's tag 0 and treat
      -- the payload as a POINTER — silently wrong — so such a cases
      -- reaching the emitter throws loudly.
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
        -- RC). All bounded: the counters walk in-memory lists, fuel is
        -- `consumed × 4`, a decoded Nat ≤ its byte length × 7 bits —
        -- overflow is a design error (the lit arm's cap pin; no wrap
        -- check on the ops).
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
        -- 128` (decLt), decBytes?'s length gate `n ≤ rest.length`
        -- (decLe) — the encoded length IS the bound. Boxed-payload
        -- compare, UNSIGNED (a Nat's machine payload is its magnitude;
        -- the cap keeps signed/unsigned equal) → the raw i32 Bool (the
        -- decEq convention — emitCases branches SCALAR Bool scrutinees
        -- on the value).
        if args.size != 2 then unsupported s!"{fn} arity {args.size}"
        let a ← specBEqArg args[0]!
        let b ← specBEqArg args[1]!
        let l ← bindLocal decl.fvarId "i32"
        emitI (.localget (← load a)); emitI (.mem .i64load 8 none)
        emitI (.localget (← load b)); emitI (.mem .i64load 8 none)
        emitI (.op (if fn == ``Nat.decLt then .i64ltu else .i64leu))
        emitI (.localset l)
      else if (fn == ``UInt8.toNat) && args.size == 1 then
        -- the decode lane's digit read: the raw u8 scalar (the cons
        -- head's unbox) → a BOXED Nat (payload = the zero-extended
        -- value). Bounded: a digit < 256.
        let l ← bindLocal decl.fvarId "i32"
        emitI (.i32const 16); emitI (.call "alloc"); emitI (.localset l)
        emitI (.localget (← load decl.fvarId)); emitI (.i32const 0); emitI (.mem .i32store8 4 none)
        emitI (.localget (← load decl.fvarId))
        emitArg args[0]!
        emitI (.op .i64extendi32u)
        emitI (.mem .i64store 8 none)
      else if (fn == ``UInt64.ofNat) && args.size == 1 then
        -- the decode lane's u64 atom: the boxed Nat payload → the raw
        -- u64 — IDENTITY at the machine model (the box payload IS the
        -- u64); a decoded value above the u64 range is the wrap, the
        -- encoder's range is always in-domain.
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
        -- inline lowering is its only body). RAW scalar args (the unbox
        -- happens at the pattern's head read), the raw i32 Bool
        -- result — the binop convention.
        let a ← specBEqArg args[0]!
        let b ← specBEqArg args[1]!
        let l ← bindLocal decl.fvarId "i32"
        emitI (.localget (← load a))
        emitI (.localget (← load b))
        emitI (.op .i32eq)
        emitI (.localset l)
      else if isSpecBEqName fn then
        -- the SPECIALIZATION PRODUCT of `Option.instBEq.beq` (named by
        -- its SOURCE TYPE; it never joins impureExt — the call inline-
        -- lowers here). Scope: the CHECKER's spec decls ONLY (`.spec_`
        -- under the WitnessCheck `_at_` — anything else throws loudly).
        -- The payload is the checker's `Option UInt64` (boxed u64):
        -- tag compare, both-none = true, both-some = unbox + i64.eq. A
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
        -- box ptr (@8 = the INNER UInt64 box) then payload i64.eq.
        -- TRAP: the @8 direct load compared the POINTERS-as-i64 —
        -- latent until a runtime value flowed (the constant sites
        -- folded at compile).
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
      -- the SAME convention as the sset WRITER below.
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

private def emitCont : Option (Code .impure × M Unit) → M Unit
  | some (_, kF) => kF
  | none => pure ()

/-- Over the fold's LAZY alt folds: a ctorAlt wraps its forked body and
    the REST of the chain into an `if_`; a default's body IS the whole
    chain (the remaining alt folds are never run — their state effects
    with them); an exhausted chain is the base `[.unreach]`. Effect
    order: thenI before elseI, recursively (the fresh-local-counter
    order is part of the byte-tie).

-- ONE result type for the WHOLE alt chain: a per-suffix read lets the
-- chain's LAST alt (a jp-fed arm ends in `.jmp`) pick a VOID if while
-- an EARLIER alt's `if (result i32)` owns the else slot — an
-- unreachable-but-REACHABLE empty stack at the enclosing `end`
-- (validator: unreachability does not leak out of a block end). Safe
-- because every RESOLVING arm is terminal, the else path is the sole
-- consumer, and the `.cases` FALLTHROUGH SEAL discards any leftover
-- at the chain's end. -/
private def buildAlts (scrut : String) (resTy : Option String) :
    List (Alt .impure) → List (M Unit) → M (List Wat.Instr)
  | [], _ => pure [.unreach]
  | _, [] => pure [.unreach]
  | .alt _ _ _ h :: _, _ => absurd h (by simp)
  | .default _ :: _, f :: _ => scopedOut f
  | .ctorAlt info _ :: rest, f :: restF => do
      let thenI ← scopedOut f
      let elseI ← buildAlts scrut resTy rest restF
      pure ([.localget scrut, .i32const info.cidx, .op .i32eq]
        ++ [.if_ resTy thenI elseI])

/-- THE EMITTER as a `Code.foldImpureM` algebra: the fold hands the
    node, its NESTED body fold (the jp/fun value — `none` elsewhere),
    the ALT folds (ctor/default order), and the continuation's fold
    WITH ITS RAW CODE (the tail-call fusion inspects the `k` shape) —
    all LAZY: the step runs them in the exact handwalk order (the
    fresh-local-counter order is part of the byte-tie). Nested/alt/
    continuation folds run under `scopedOut` (the fork). -/
private def emitStep :
    Code .impure → Unit → Option (M Unit) → List (M Unit) →
      Option (Code .impure × M Unit) → M Unit := fun code _ nested altFs cont => do
  match code with
  | .let decl _ =>
      -- TAIL-CALL FUSION: `let x := fap f args; return x` → return_call
      -- (the tail-call proposal; wasm-tools parse --enable-tail-call).
      -- The WASM stack stays flat for tail-recursive Lean functions.
      -- The fused `k`'s SHAPE rides the fold's `cont` pair.
      match cont with
      | some (k, kF) =>
          match k, decl.value with
          | .return rv, .fap fn args _ =>
              -- intrinsics are NOT fusion targets (the primitive is not a
              -- Lean decl; its mapped call has its own convention) — std ops
              -- fall through to the normal let path
              if rv == decl.fvarId && (binop? fn).isNone
                  && (GuestlangStd.Intrinsic.ofName? fn).isNone
                  && !isSpecBEqName fn && !inlineNatFap? fn args.size then do
                for a in args do emitArg a
                emitI (.returncall fn.toString)
              else do emitLet decl; kF
          | _, _ => do emitLet decl; kF
      | none => emitCont cont
  | .return fvarId => emitReturn fvarId
  | .cases c =>
      -- SCALAR scrutinees (Bool/UInt8 — the impl param is a raw flat
      -- value): branch on the VALUE itself. OBJECT scrutinees: tag =
      -- i32.load8_u offset=4, stashed in a temp local.
      let scalar := c.typeName == `Bool || c.typeName == `UInt8
        || c.typeName == `UInt32 || c.typeName == `UInt64
      let resTy := (c.alts.toList.filterMap resultTyOfAlt).head?
      let scrut ←
        if scalar then
          load c.discr
        else do
          emitI (.localget (← load c.discr))
          emitI (.mem .i32load8u 4 none)
          let tag ← bindFresh "i32"
          emitI (.localset tag)
          pure tag
      -- the alt folds run left-to-right under the fork — goAlts's order
      let altsI ← buildAlts scrut resTy c.alts.toList altFs
      emitIs altsI
      -- THE FALLTHROUGH SEAL: an LCNF case is TERMINAL in its spine
      -- (every arm ends return/jmp/unreach or another case), but the
      -- VALIDATOR keeps the enclosing frame reachable at the case's
      -- end, and a fallthrough with an empty stack fails the
      -- result-type check (the checkWitness probe). The unreachable
      -- is semantically dead.
      emitI .unreach
  | .inc fvarId _ _ _ _ =>
      emitI (.localget (← load fvarId)); emitI (.call "rc_inc"); emitCont cont
  | .dec fvarId _ _ _ _ _ =>
      emitI (.localget (← load fvarId)); emitI (.call "rc_dec"); emitCont cont
  | .del _ _ => emitCont cont
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
      -- the CONTINUATION fold first, then the body fold (the old
      -- emitScoped order — the counter is part of the byte-tie)
      match nested, cont with
      | some bodyF, some (_, kF) =>
        let kI ← scopedOut kF
        let bodyI ← scopedOut bodyF
        emitI (.block skipL ([.block jpL (kI ++ [.br skipL])] ++ bodyI))
        -- SEAL: every k-path branches, and the jp body's paths are
        -- terminal — control never REACHES past the $skip block's end.
        -- But the validator keeps the enclosing frame REACHABLE there
        -- (block-internal unreachability does not leak out); the
        -- unreachable closes the frame.
        emitI .unreach
      | _, _ => unsupported "jp: malformed fold shape (unreachable)"
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
  | .sset _f i offset y ty _ =>
      -- field store: sset var[slot, off] := y → mem[var + 8 + slot*8 + off]
      -- (the RC pass reorders fields REF-FIRST: the slot index = the
      -- field's position in the REORDERED layout — the id of a {u64,
      -- string, string, list} record is slot 3 AFTER the three ref
      -- slots. The old emission discarded `i` — the id CLOBBERED the
      -- first ref's pointer.)
      emitI (.localget (← load _f))
      emitI (.localget (← load y))
      emitI (.mem (storeMemOp (wasmTyOf? ty)) (8 + i * 8 + offset) none)
      emitCont cont
  | .oset .. | .uset .. | .setTag .. =>
    unsupported "in-place mutation (oset/uset/setTag)"
  | .fun _ _ h => absurd h (by simp)

/-- THE EMITTER: the `Code.foldImpureM` traversal with the `emitStep`
    algebra. BYTE-TIE: the emitted stream is pinned by `just
    wasm-compile && just wasm-diff-check` (bytes identical) and
    `Correct.lean`'s `runEmit` extraction checks. -/
def emitCode (code : Code .impure) : M Unit :=
  Code.foldImpureM (fun _ a => a) emitStep () code ()

/-! ## Decl emission -/

/-- TYPED: the decl's func = a `Wat.Func` — the general path's body is
    fully typed `Instr`s. -/
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
the guest object into the canonical layout). W10.2: the registry is a
FOLD over the registered `FuncSig` (`adapterShapeOf` — was the
String-keyed hand list `adapterShape?`, the audit's last hand mirror);
the five record shapes' BODIES are the SCHEMA-TYPED generator's
instantiations (each pinned ≡ the hand shape it replaced — the
`legacy*` fixtures). The shapes' authority: the WIT world
(byte-tied); a wrong shape = a differential failure (the host
misreads).

- `string`: [bytes-ptr, byte-len] — the static return area holds the
  pair; bytes-ptr = obj + 16 (bytes INLINE).
- `optionUser`: option<user> — the area holds the option's MEMORY
  layout: discr u32 @0, the record @8 (aligned 8 by the u64); the
  record's refs sit at @8/16/24, the id scalar at @32.
- default: the scalar/object conventions (scalar → raw i64; object →
  unbox).
-/

-- The ASYNC-marked exports: NOT hand-listed anywhere — `emitModule`
-- takes them as `asyncFns`, DERIVED by the driver from the schema
-- registry (`WasmGenMain.asyncExportsOf`). Recipe:
-- notes/wasm-backend-notes.md §async-lift.

/-- W10.2: the ADAPTER SHAPE, FOLDED from the registered `FuncSig` —
    was `adapterShape?`, the String-keyed hand list (the audit's last
    hand mirror: a new export with a shaped ret needed a second site
    here). The shape is a function of the SIGNATURE: the ret decides
    the result-side shape (the canonical-ABI return lowering); a
    scalar ret falls through to the PARAM-side arms (the single
    record/variant/bytes param reboxes). The arms are the CLOSED shape
    set — `emitAdapter`'s arms mirror them 1:1; a signature outside
    the set folds to `none` = the default scalar lowering (a drifted
    shape surfaces at the differential gate, never silently). The
    record/variant param distinction rides the REGISTERED type name
    (the sig carries the `.ty` ref; the record/variant KIND lives in
    the universe, which a pure sig fold cannot see — the name is the
    sig-local witness; a renamed schema type fails loudly at the
    differential gate, the same authority the hand list had). -/
def adapterShapeOf : SchemaLang.FuncSig → Option String
  | s =>
    match s.ret with
    | .future (.list .u64) => some "streamU64"
    | .future (.list _) =>
        if s.sem.delivery == (.stream : SchemaLang.Delivery)
          then some "streamUser" else some "listUser"
    | .option _ => some "optionUser"
    | .list _ => some "listUser"
    -- the W10.2 error channel: the result<T, fault> export's return
    -- lowering. The CLOSED arm is the demo's result<u64, order-error>
    -- (emitAdapter's resultOrderError arm — the ok payload u64, the err
    -- payload the scalar-joined order-error variant); another result
    -- shape joins here only by growing the arm, never by reusing this
    -- one (the differential gate + the flat-form pin catch a drift).
    | .result _ _ => some "resultOrderError"
    | _ =>
        match s.params with
        | [(_, .ty "User")] => some "userParam"
        | [(_, .ty "OrderError")] => some "variantParam"
        -- the witness export: bytes in (the canonical list<u8> = the
        -- (ptr, len) pair), verdict out (the raw i32 Bool)
        | [(_, .list .u8)] => some "bytesParam"
        | _ => none

/-- Walking a guest List cons chain into a canonical (array-ptr, count)
    pair: COUNT the cons cells, `$alloc(n × elemSize)`, then FILL each
    element via `lowerElem` (`$cur{suffix}` = the cons — its head =
    `load(+8)`; `$w{suffix}` = the element's destination address).
    `suffix` uniquifies the locals/labels (nested walks reuse the same
    generator). Cons layout: {tag@4 (nil=0/cons=1), head@8, tail@16}. -/
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
  -- walk's `$arr`/`$n` LOCALS. TRAP: a scratch write at the fill-end
  -- cursor CORRUPTED the next bump allocation (it landed on the first
  -- inner-walk array) — "unused" memory is not unused.
  countLoop ++ fillLoop ++
    (if areaOff == 0 then []
     else [ .i32const areaOff, .localget arr, .mem .i32store 0 none
          , .i32const (areaOff + 4), .localget n, .mem .i32store 0 none ])

/-- A `String` element's flat pair ((head+16, load(head+8)) — bytes
    inline, len) written at `$w{suffix}`. -/
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
    and `listUser` — the same five instructions; what follows differs. -/
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
  -- (the `list` precedent); no map-specific ABI handling yet
  -- (deliberate, not missing)
  | .stream _ | .tensor _ _ | .map _ _ | .set _ | .ty _ => ["i32", "i32"]

def userFlatTys (cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24]) : List String :=
  (userFieldTys cert).flatMap flatTyOf

/-- The flat params' NAMES: the id, then (ptr, len) per ref field
    (name, email, tags) — same order as `userFlatTys`. THE LENGTH PIN
    below: one name per flat value — a `userTys` growth/reorder breaks
    the build until the names follow (the `getD` fallback at the
    emission site is then dead, not a mask). -/
def userParamNames : List String := ["id", "np", "nl", "ep", "el", "tp", "tl"]
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

/-! ## The SCHEMA-TYPED adapter generator

ONE generator over the schema data replaces five hand-built record
shapes (`optionUser`/`listUser`/`userParam`/`streamUser`/`bytesParam`).
The machinery:

- `Dst` — where a field's flat bytes land: the STATIC return area (a
  pushed const; store offset 0) or a DYNAMIC cursor (the base local;
  store offset = the field's offset).
- `pairOf` — the (ptr, len) pair write (`pairAbs`/`pairRel` are its
  specializations — pinned).
- `lowerFields` — the FORWARD flattener: per field, by `flatTyOf` +
  the certified `Layout.offsets`, guest object → flat area.
- `listRebox` — the canonical list param's guest cons chain
  (`consChain` = its string instantiation — pinned; the witness lane's
  boxed-u8 walk = its u8 instantiation).
- `reboxRecord` — the param direction: per-field builders + the
  refs-first guest object.

The field universe (`lowered?`/`reboxed?`): the flat scalars, the
inline-pair kinds (string/bytes), `list<string>`, and (param side)
`list<u8>`. `emitModule` GATES every generic shape's schema against
the universe — outside it, THROW at emission (the robustness rule),
never a silently-wrong adapter. A NEW record shape names its tys in
`shapeTys?` and the generator builds the adapter — no new hand shape
(the `tripleTys` fixture pins the drift class).

EQUIVALENCE: each generic body ≡ the previous hand shape, pinned
(`*_tie`, rfl — the adapters are data before emission) under the
byte-tie. The `legacy*` bodies are FROZEN, generator-free fixtures
serving the pins only; their helpers (`pairAbs`/`pairRel`/`consChain`/
`userElemLower`/`userFlatTys`) are untouched for exactly that. -/

/-- Where a lowered field's bytes land. -/
inductive Dst where
  | /-- the STATIC return area: the address = `area + off` pushed as a
       const; the store's mem-offset operand = 0. -/ abs (area : Nat)
  | /-- the DYNAMIC cursor: the address = the base local; the store's
       mem-offset operand = the field's offset. -/ rel (base : String)

def Dst.push : Dst → Nat → List Wat.Instr
  | .abs area, off => [.i32const (area + off)]
  | .rel base, _ => [.localget base]

def Dst.stOff : Dst → Nat → Nat
  | .abs _, _ => 0
  | .rel _, off => off

/-- The (ptr, len) pair write of the string-like object `src` (the
    bytes inline at src+16, the len at src+8) at `dst off`/`dst
    (off+4)`. `pairAbs`/`pairRel` = its specializations (pinned). -/
def pairOf (dst : Dst) (off : Nat) (src : String) : List Wat.Instr :=
  dst.push off ++ [ .localget src, .i32const 16, .op .i32add
                  , .mem .i32store (dst.stOff off) none ]
  ++ dst.push (off + 4) ++ [ .localget src, .mem .i32load 8 none
                  , .mem .i32store (dst.stOff (off + 4)) none ]

/-- The guest-object REF fields: everything crossing as a (ptr, len)
    pair — an 8-byte pointer slot in the guest object (the RC pass's
    ref-first rule). -/
def isRefTy (t : SchemaLang.Ty) : Bool := (flatTyOf t).length == 2

def isListTy : SchemaLang.Ty → Bool
  | .list _ => true | _ => false

/-- The guest scalar's byte width (by the flat form: the i64 family
    = 8). -/
def scalarWidth (t : SchemaLang.Ty) : Nat :=
  if (flatTyOf t).getD 0 "" == "i64" then 8 else 4

def scalarLoadOp (t : SchemaLang.Ty) : Wat.MemOp :=
  if (flatTyOf t).getD 0 "" == "i64" then .i64load else .i32load

def scalarStoreOp (t : SchemaLang.Ty) : Wat.MemOp :=
  if (flatTyOf t).getD 0 "" == "i64" then .i64store else .i32store

/-- The guest object's scalar base: after ALL ref slots (ref-first). -/
def guestScalarBase (ts : List SchemaLang.Ty) : Nat :=
  8 + (ts.filter isRefTy).length * 8

/-- The guest object's byte size: header + ref slots + scalar area
    (the ctor's alloc size — 40 for the demo user, 28 for the
    tripleTys fixture). -/
def guestSize (ts : List SchemaLang.Ty) : Nat :=
  8 + (ts.filter isRefTy).length * 8
    + (ts.filter (fun t => !isRefTy t)).foldl (fun a t => a + scalarWidth t) 0

/-- The FORWARD flattener's field universe: the flat scalars (the i64
    + i32 families), the inline-pair kinds (string/bytes), and
    `list<string>` (the cons-walk). f64/f32 have no `Wat.MemOp` yet;
    the exotic pair kinds (option/result/map/…) have no certified
    lowering — a shape carrying them THROWS at the emitModule gate. -/
def lowered? : SchemaLang.Ty → Bool
  | .u64 | .i64 | .bool | .u8 | .u16 | .u32 | .i8 | .i16 | .i32 => true
  | .string | .bytes => true
  | .list .string => true
  | _ => false

/-- The PARAM-direction universe: `lowered?` + `list<u8>` (the
    boxed-byte rebox — the witness decode lane). -/
def reboxed? : SchemaLang.Ty → Bool
  | .list .u8 => true
  | t => lowered? t

/-- THE FORWARD FLATTENER: the guest record (its address pushed by
    `src`) → the canonical flat fields at `dst`, per field by
    `flatTyOf` + the certified offsets: scalar = load the guest
    ref-first scalar area (`gBase + scOff`); string/bytes = load the
    ref slot's pointer into `scratch` + `pairOf`; `list string` = the
    cons-walk into an 8n-byte array, its (arr, n) landing at the
    field's pair (inner-walk locals named by `suffix`). Kinds outside
    `lowered?` lower to [] — unreachable via the emitModule gate. -/
def lowerFields : List SchemaLang.Ty → List Nat → Nat → Nat → Nat →
    List Wat.Instr → Dst → String → String → List Wat.Instr
  | [], _, _, _, _, _, _, _, _ => []
  -- offsets exhausted: unreachable (the callers pass Layout.offsets ts)
  | _ :: _, [], _, _, _, _, _, _, _ => []
  | t :: ts, off :: offs, refIdx, scOff, gBase, src, dst, scratch, suffix =>
      let head : List Wat.Instr :=
        if isRefTy t then
          let refLoad : List Wat.Instr :=
            src ++ [ .mem .i32load (8 + refIdx * 8) none ]
          if t == .string || t == .bytes then
            refLoad ++ [ .localset scratch ] ++ pairOf dst off scratch
          else if t == .list .string then
            listWalk refLoad 0 8 suffix (strElemLower suffix)
              ++ dst.push off
                ++ [ .localget (s!"arr{suffix}"), .mem .i32store (dst.stOff off) none ]
              ++ dst.push (off + 4)
                ++ [ .localget (s!"n{suffix}"), .mem .i32store (dst.stOff (off + 4)) none ]
          else []
        else
          dst.push off ++ src
            ++ [ .mem (scalarLoadOp t) (gBase + scOff) none
               , .mem (scalarStoreOp t) (dst.stOff off) none ]
      head ++ lowerFields ts offs (if isRefTy t then refIdx + 1 else refIdx)
        (if isRefTy t then scOff else scOff + scalarWidth t) gBase src dst scratch suffix

/-- The canonical list PARAM's guest rebox: the cons chain built
    BACKWARD (i = n … 0) from the flat source — `srcA` = the element
    source (the array pointer for strings, the byte pointer for u8s),
    `srcB` = the count — each element consed {tag=1@4, head@8, tail@16}
    onto `acc`; the EMPTY list = the allocated {rc, tag=0} block
    (never the null pointer — the user-complete trap). `consChain` =
    the string instantiation (pinned); the witness lane's boxed-u8
    walk = the u8 instantiation. ONE list field per record (the
    accumulator local is shape-fixed). Kinds outside the rebox gate
    lower to [] — unreachable via the emitModule gate. -/
def listRebox (elem : SchemaLang.Ty) (srcA srcB : String) : List Wat.Instr :=
  let doneL := if elem == .string then "tags-done" else "bts-done"
  let loopL := if elem == .string then "tags-loop" else "bts-loop"
  let cnt := if elem == .string then "ti" else "i"
  let consL := if elem == .string then "tc" else "c"
  let headL := if elem == .string then "ts" else "bx"
  let fetch : List Wat.Instr :=
    if elem == .string then
      [ .localget "ti", .i32const 8, .op .i32mul, .localget srcA, .op .i32add
        , .localset "tq"
      , .localget "tq", .mem .i32load 0 none, .localset "tsp"
      , .localget "tq", .mem .i32load 4 none, .localset "tln" ]
      ++ stringCtor "tsp" "tln" "ts"
    else if elem == .u8 then
      [ .i32const 16, .call "alloc", .localset "bx"
      , .localget "bx", .i32const 0, .mem .i32store8 4 none
      , .localget "bx", .localget srcA, .localget "i", .op .i32add
      , .mem .i32load8u 0 none, .mem .i32store 8 none ]
    else []
  [ .i32const 8, .call "alloc", .localset "acc"
  , .localget "acc", .i32const 0, .mem .i32store8 4 none
  , .localget srcB, .localset cnt
  , .block doneL [.loop loopL
      ( [ .localget cnt, .op .i32eqz, .brif doneL
        , .localget cnt, .i32const 1, .op .i32sub, .localset cnt ]
        ++ fetch
        ++ [ .i32const 24, .call "alloc", .localset consL
           , .localget consL, .i32const 1, .mem .i32store8 4 none
           , .localget consL, .localget headL, .mem .i32store 8 none
           , .localget consL, .localget "acc", .mem .i32store 16 none
           , .localget consL, .localset "acc"
           , .br loopL ] ) ] ]

/-- One ref field's builder: the guest object the field's flat
    (ptr, len) pair reconstructs; scalars never reach the plan, other
    ref kinds are gate-excluded. -/
def reboxOne : SchemaLang.Ty → List String → String → List Wat.Instr
  | .list .string, ns, _ => listRebox .string (ns.getD 0 "") (ns.getD 1 "")
  | .list .u8, ns, _ => listRebox .u8 (ns.getD 0 "") (ns.getD 1 "")
  | .string, ns, dst => stringCtor (ns.getD 0 "") (ns.getD 1 "") dst
  | _, _, _ => []

/-- The ref fields' rebox plan: (ty, flat names, builder dst local) in
    WIT order. -/
def refPlan : List SchemaLang.Ty → List String → List String →
    List (SchemaLang.Ty × List String × String)
  | [], _, _ => []
  | t :: ts, names, refDsts =>
      let k := (flatTyOf t).length
      let rest := refPlan ts (names.drop k)
        (if isRefTy t then refDsts.drop 1 else refDsts)
      if isRefTy t then (t, names.take k, refDsts.getD 0 "") :: rest else rest

/-- The builders: LISTS first, then the other ref fields in WIT order
    (the demo-certified emission order, pinned by `userParamBody_tie`). -/
def reboxBuilders (plan : List (SchemaLang.Ty × List String × String)) : List Wat.Instr :=
  let lists := plan.filter fun p => isListTy p.1
  let others := plan.filter fun p => !isListTy p.1
  (lists ++ others).flatMap fun p => reboxOne p.1 p.2.1 p.2.2

/-- The refs-first guest object's REF stores: the pointer slots
    @8+i*8, WIT ref order — the pin caught a WIT-order draft here. -/
def reboxRefStores : List SchemaLang.Ty → Nat → List String → List String → String →
    List Wat.Instr
  | [], _, _, _, _ => []
  | t :: ts, refIdx, names, refDsts, obj =>
      let k := (flatTyOf t).length
      let rest := reboxRefStores ts (if isRefTy t then refIdx + 1 else refIdx)
        (names.drop k) (if isRefTy t then refDsts.drop 1 else refDsts) obj
      (if isRefTy t then
        [ .localget obj, .localget (refDsts.getD 0 ""), .mem .i32store (8 + refIdx * 8) none ]
      else []) ++ rest

/-- The refs-first guest object's SCALAR stores: after all ref slots
    (gBase + the running scalar offset), WIT scalar order. -/
def reboxScalarStores : List SchemaLang.Ty → Nat → Nat → List String → String →
    List Wat.Instr
  | [], _, _, _, _ => []
  | t :: ts, gBase, scOff, names, obj =>
      let k := (flatTyOf t).length
      (if isRefTy t then []
      else [ .localget obj, .localget (names.getD 0 ""),
             .mem (scalarStoreOp t) (gBase + scOff) none ])
      ++ reboxScalarStores ts gBase (if isRefTy t then scOff else scOff + scalarWidth t)
        (names.drop k) obj

/-- The refs-first guest object: alloc(guestSize), tag=0 @4, the ref +
    scalar stores, then the impl call (the object rides the stack). -/
def reboxObject (ts : List SchemaLang.Ty) (names refDsts : List String)
    (obj impl : String) : List Wat.Instr :=
  [ .i32const (guestSize ts), .call "alloc", .localset obj
  , .localget obj, .i32const 0, .mem .i32store8 4 none ]
  ++ reboxRefStores ts 0 names refDsts obj
  ++ reboxScalarStores ts (guestScalarBase ts) 0 names obj
  ++ [ .localget obj, .call impl ]

/-- THE PARAM-DIRECTION GENERATOR: the canonical flat params → the
    guest record object in `obj`, then the impl call. The demo user
    instantiation = `userParamBody` (pinned ≡ the hand shape). -/
def reboxRecord (ts : List SchemaLang.Ty) (names refDsts : List String)
    (obj impl : String) : List Wat.Instr :=
  reboxBuilders (refPlan ts names refDsts)
    ++ reboxObject ts names refDsts obj impl

/-- A record-param shape's flat core params: one per flatTyOf value,
    named by the shape's name table (the length pin
    `userParamNames_length` keeps the table in lockstep with the
    schema). -/
def reboxParams (ts : List SchemaLang.Ty) (names : List String) : List Wat.Param :=
  (ts.flatMap flatTyOf).zipIdx.map fun (ty, i) =>
    { name := some (names.getD i "flat"), ty }

inductive StreamElem where
  | /-- raw u64 items (watch-counts) -/ u64
  | /-- user records (watch-users) -/ user

/-- The per-item lowering — the generator's instantiation by the
    payload schema: the u64 = the boxed payload read (INLINE head load
    — no scratch local); the user = the record flattener over
    Layout.userTys (the cons head via the `e` scratch). -/
def streamElemLower (cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24]) :
    StreamElem → List Wat.Instr
  | .u64 => lowerFields [.u64] [0] 0 0 (guestScalarBase [.u64])
      [ .localget "cur", .mem .i32load 8 none ] (.rel "w") "p" ""
  | .user => [ .localget "curU", .mem .i32load 8 none, .localset "e" ]
      ++ lowerFields Layout.userTys (userLayout cert) 0 0 (guestScalarBase Layout.userTys)
        [ .localget "e" ] (.rel "wU") "p2" "T"

/-- The outer walk's shape by the payload: the item stride (u64 = 8,
    user = userSize), the walk suffix, and the (arr, n) local names
    the stash reads. -/
def streamWalk (certSize : WasmBackend.Layout.size WasmBackend.Layout.userTys = 32) :
    StreamElem → Nat × String × String × String
  | .u64 => (8, "", "arr", "n")
  | .user => (userSize certSize, "U", "arrU", "nU")

/-- The optionUser shape's body (the generator's instantiation over
    Layout.userTys): the impl call → the option tag @56 → the SOME
    branch flattens the payload record into the area @64 (the static
    `abs` destination) → the area pointer. -/
def optionUserBody (pass : List Wat.Instr)
    (cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (impl : String) : List Wat.Instr :=
  let area := 56
  let thenI : List Wat.Instr :=
    [ .localget "opt", .mem .i32load 8 none, .localset "u" ]
    ++ lowerFields Layout.userTys (userLayout cert) 0 0 (guestScalarBase Layout.userTys)
      [ .localget "u" ] (.abs (area + 8)) "p" ""
  pass ++ [ .call impl, .localset "opt"
  , .localget "opt", .mem .i32load8u 4 none, .localset "tag"
  , .i32const area, .localget "tag", .mem .i32store 0 none
  , .localget "tag", .i32const 1, .op .i32eq
  , .if_ none thenI []
  , .i32const area ]

/-- The userParam body: the record-param rebox over userTys (flat
    names = userParamNames; string builders' dsts ns/es; tags cons
    chain's acc). -/
def userParamBody (impl : String) : List Wat.Instr :=
  reboxRecord Layout.userTys userParamNames ["ns", "es", "acc"] "u" impl

/-- The listUser body (watch-orders): the variant param re-boxed, the
    impl call, the outer walk lowering each user into a 32-byte flat
    record (the tags = the NESTED string-list walk), the async
    task-return delivery. -/
def listUserBody
    (certLayout : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (certSize : WasmBackend.Layout.size WasmBackend.Layout.userTys = 32)
    (impl kebab : String) : List Wat.Instr :=
  variantBox "into_disc" "into_payload"
  ++ [ .call impl, .localset "lst" ]
  ++ listWalk [.localget "lst"] 0 (userSize certSize) "U" (streamElemLower certLayout .user)
  ++ [ .i32const 56, .localget "arrU", .mem .i32store 0 none
     , .i32const 60, .localget "nU", .mem .i32store 0 none
     , .i32const 56, .i32const 60, .mem .i32load 0 none, .call s!"tr_{kebab}"
     , .i32const 0 ]

/-- The stream bodies (watch-counts/watch-users): the handle pair
    unpack, the walk, the stash + yield (the callback = the write
    site). -/
def streamBody (pass : List Wat.Instr)
    (certLayout : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (certSize : WasmBackend.Layout.size WasmBackend.Layout.userTys = 32)
    (impl kebab : String) (elem : StreamElem) : List Wat.Instr :=
  let (elemSize, walkSuffix, arrN, nN) := streamWalk certSize elem
  pass ++ [ .call impl, .localset "lst"
  , .call s!"sn_{kebab}", .localset "h"
  , .localget "h", .op .i32wrapi64, .localset "rd"
  , .localget "h", .i64const 32, .op .i64shru, .op .i32wrapi64, .localset "wr" ]
  ++ listWalk [.localget "lst"] 0 elemSize walkSuffix (streamElemLower certLayout elem)
  ++ [ .localget "wr", .globalset "wr_g"
     , .localget arrN, .globalset "arr_g"
     , .localget nN, .globalset "n_g"
     , .localget "rd", .call s!"tr_{kebab}"
     , .i32const 1 ]

/-- The bytesParam body (verify-witness): the list<u8> rebox, then the
    impl call (the raw i32 Bool verdict). -/
def bytesParamBody (impl : String) : List Wat.Instr :=
  listRebox .u8 "ptr" "len" ++ [ .localget "acc", .call impl ]

/-- The SHAPE REGISTRY's schema: the field types each record shape
    lowers. THE DRIFT-CLASS SURFACE: a new record shape names its tys
    HERE and the generator builds the adapter — no new hand shape (the
    tripleTys fixture pins it). -/
def shapeTys? : String → Option (List SchemaLang.Ty)
  | "optionUser" | "userParam" | "listUser" | "streamUser" => some Layout.userTys
  | "streamU64" => some [.u64]
  | "bytesParam" => some [.list .u8]
  -- the W10.2 error channel: the ok payload's scalar (the err side is
  -- the scalar-joined variant rebox, not a record shape — no fields)
  | "resultOrderError" => some [.u64]
  | _ => none

/-- The record shapes' DIRECTION: `true` = param (flat → guest). The
    emitModule gate picks the generator's universe by it. -/
def paramShape? : String → Bool
  | "userParam" | "bytesParam" => true
  | _ => false

/-! ## The equivalence pins: generic ≡ the hand shapes

The old hand bodies, FROZEN as fixtures (generator-free; their
helpers — pairAbs, pairRel, consChain, userElemLower, userFlatTys —
are untouched legacy surface), and the rfl pins: the generator's
output IS the hand shape's, instruction for instruction. The byte-tie
(wasm-diff-check) is the end-to-end arbiter; these pins make the
equivalence a BUILD fact. -/

private def legacyOptionUserBody (pass : List Wat.Instr)
    (cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (impl : String) : List Wat.Instr :=
  let area := 56
  let fld (i : Nat) : Nat := area + 8 + (userLayout cert).getD i 0
  let thenI : List Wat.Instr :=
    [ .localget "opt", .mem .i32load 8 none, .localset "u"
    , .i32const (fld 0), .localget "u", .mem .i64load 32 none
    , .mem .i64store 0 none
    , .localget "u", .mem .i32load 8 none, .localset "p" ]
    ++ pairAbs (fld 1) "p"
    ++ [ .localget "u", .mem .i32load 16 none, .localset "p" ]
    ++ pairAbs (fld 2) "p"
    ++ listWalk [.localget "u", .mem .i32load 24 none] (fld 3) 8 "" (strElemLower "")
  pass ++ [ .call impl, .localset "opt"
  , .localget "opt", .mem .i32load8u 4 none, .localset "tag"
  , .i32const area, .localget "tag", .mem .i32store 0 none
  , .localget "tag", .i32const 1, .op .i32eq
  , .if_ none thenI []
  , .i32const area ]

private def legacyUserParamBody (impl : String) : List Wat.Instr :=
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
     , .call impl ]

private def legacyListUserBody
    (certLayout : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (certSize : WasmBackend.Layout.size WasmBackend.Layout.userTys = 32)
    (impl kebab : String) : List Wat.Instr :=
  let boxed : List Wat.Instr := variantBox "into_disc" "into_payload"
  let areaTail : List Wat.Instr :=
    [ .i32const 56, .localget "arrU", .mem .i32store 0 none
    , .i32const 60, .localget "nU", .mem .i32store 0 none
    , .i32const 56, .i32const 60, .mem .i32load 0 none, .call s!"tr_{kebab}"
    , .i32const 0 ]
  boxed
  ++ [ .call impl, .localset "lst" ]
  ++ listWalk [.localget "lst"] 0 (userSize certSize) "U" (userElemLower certLayout)
  ++ areaTail

private def legacyStreamBody (pass : List Wat.Instr)
    (certLayout : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (certSize : WasmBackend.Layout.size WasmBackend.Layout.userTys = 32)
    (impl kebab : String) (u64Payload : Bool) : List Wat.Instr :=
  let (elemSize, elemLower, walkSuffix) :=
    if u64Payload then
      (8, [ .localget "w", .localget "cur", .mem .i32load 8 none
          , .mem .i64load 8 none, .mem .i64store 0 none ], "")
    else (userSize certSize, userElemLower certLayout, "U")
  let arrN := if u64Payload then "arr" else "arrU"
  let nN := if u64Payload then "n" else "nU"
  pass ++ [ .call impl, .localset "lst"
  , .call s!"sn_{kebab}", .localset "h"
  , .localget "h", .op .i32wrapi64, .localset "rd"
  , .localget "h", .i64const 32, .op .i64shru, .op .i32wrapi64, .localset "wr" ]
  ++ listWalk [.localget "lst"] 0 elemSize walkSuffix elemLower
  ++ [ .localget "wr", .globalset "wr_g"
     , .localget arrN, .globalset "arr_g"
     , .localget nN, .globalset "n_g"
     , .localget "rd", .call s!"tr_{kebab}"
     , .i32const 1 ]

private def legacyBytesParamBody (impl : String) : List Wat.Instr :=
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
  , .localget "acc", .call impl ]

/-- THE PINS: each generic body = the hand shape, instruction for
    instruction (rfl — the adapters are data before emission). -/
-- (`0 + off` does not kernel-reduce for symbolic `off` — Nat.add
-- recurses on its SECOND argument — so the abs pin is concrete; the
-- five body pins cover the deployed abs sites.)
theorem pairOf_abs_tie (src : String) :
    pairOf (.abs 0) 8 src = pairAbs 8 src := rfl

theorem pairOf_rel_tie (base : String) (off : Nat) (src : String) :
    pairOf (.rel base) off src = pairRel base off src := rfl

theorem listRebox_string_tie (arr n : String) :
    listRebox .string arr n = consChain arr n := rfl

theorem optionUser_tie (pass : List Wat.Instr)
    (cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (impl : String) :
    optionUserBody pass cert impl = legacyOptionUserBody pass cert impl := rfl

theorem userParamBody_tie (impl : String) :
    userParamBody impl = legacyUserParamBody impl := rfl

theorem userParamParams_tie
    (cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24]) :
    reboxParams Layout.userTys userParamNames
      = (userFlatTys cert).zipIdx.map fun (ty, i) =>
          { name := some (userParamNames.getD i "flat"), ty } := rfl

theorem listUserBody_tie
    (certLayout : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (certSize : WasmBackend.Layout.size WasmBackend.Layout.userTys = 32)
    (impl kebab : String) :
    listUserBody certLayout certSize impl kebab
      = legacyListUserBody certLayout certSize impl kebab := rfl

theorem streamBody_u64_tie (pass : List Wat.Instr)
    (certLayout : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (certSize : WasmBackend.Layout.size WasmBackend.Layout.userTys = 32)
    (impl kebab : String) :
    streamBody pass certLayout certSize impl kebab .u64
      = legacyStreamBody pass certLayout certSize impl kebab true := rfl

theorem streamBody_user_tie (pass : List Wat.Instr)
    (certLayout : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24])
    (certSize : WasmBackend.Layout.size WasmBackend.Layout.userTys = 32)
    (impl kebab : String) :
    streamBody pass certLayout certSize impl kebab .user
      = legacyStreamBody pass certLayout certSize impl kebab false := rfl

theorem bytesParamBody_tie (impl : String) :
    bytesParamBody impl = legacyBytesParamBody impl := rfl

/-! ## The drift-class pin: a NEW record shape, NO new hand shape

The synthetic 3-field fixture `{id : u64, name : string, tag : u32}`
(no demo record carries it): the generator builds BOTH directions from
the schema alone — `shapeTys?`-registerable, gate-clean, with the
ref-first guest geometry and the canonical offsets all DERIVED. -/

abbrev tripleTys : List SchemaLang.Ty := [.u64, .string, .u32]

/-- The name table (1 name per flat value: id, the string's (ptr,
    len), the u32). -/
def tripleNames : List String := ["id", "np", "nl", "tag"]

-- The schema's flat ABI: 4 core values ≤ MAX_FLAT_PARAMS = 16 (the
-- record crosses FLAT); the canonical layout the forward direction
-- flattens onto.
theorem triple_flat : tripleTys.flatMap flatTyOf = ["i64", "i32", "i32", "i32"] := rfl
theorem triple_params : (reboxParams tripleTys tripleNames).length = 4 := rfl
theorem triple_offsets : WasmBackend.Layout.offsets tripleTys = [0, 8, 16] := rfl

-- The param direction: the string's pointer slot @8 (ref-first), the
-- u64 @16 + the u32 @24 in the derived scalar area, size 28 — no hand
-- numbers.
theorem triple_guest_size : guestSize tripleTys = 28 := rfl

/-- The fixture's param-direction adapter body (reboxObject emits no
    structural forms — the store offsets are flat-visible). -/
def tripleObj (obj impl : String) : List Wat.Instr :=
  reboxObject tripleTys tripleNames ["ns"] obj impl

def storeOff? : Wat.Instr → Option Nat
  | .mem .i32store off _ => some off
  | .mem .i64store off _ => some off
  | _ => none

def storeOffsets (is : List Wat.Instr) : List Nat := is.filterMap storeOff?

def constAddr? : Wat.Instr → Option Nat
  | .i32const n => some n
  | _ => none

def constAddrs (is : List Wat.Instr) : List Nat := is.filterMap constAddr?

theorem triple_guest_stores : storeOffsets (tripleObj "u" "f") = [8, 16, 24] := rfl

-- The forward direction: the canonical offsets [0, 8, 16] land at the
-- area base 16 — the u64 store's pushed address @16, the string pair
-- @24/28, the u32 @32 (the middle 16 = pairOf's inline-bytes offset).
theorem triple_lower_consts : constAddrs (lowerFields tripleTys
  (WasmBackend.Layout.offsets tripleTys) 0 0 (guestScalarBase tripleTys)
  [ .localget "r" ] (.abs 16) "p" "") = [16, 24, 16, 28, 32] := rfl

/-- Canonical-ABI adapter: flat component args → the impl's calling
convention. Borrowed-scalar params (objects in the impl) get BOXED;
raw scalars pass through; an object RESULT gets unboxed to the flat
i64. Exported under the WIT name; the impl stays internal (internal
callers keep calling it directly). The five record shapes = the
schema-typed generator's instantiations (pinned ≡ the hand shapes);
the `string`/`variantParam`/default shapes stay hand-built (no record
schema to drive). TYPED: every shape builds a `Wat.Func` — ZERO
`Instr.raw` (offsets from the PROVED `userLayout`). -/
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
  -- into it. (The STRING-ness comes from the ORIGINAL def type — the
  -- LCNF type is erased to `obj` for every object result.)
  if shape == "string" then
    -- the shim: a STATIC return area (the fixed scratch slot at 48 —
    -- the freelist owns 0..24, the heap starts at 64), return the area
    -- pointer (`[I64] -> [I32]`: MAX_FLAT_RESULTS=1; the caller copies
    -- out via the canon-lift memory option). bytes-ptr = obj + 16.
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
    -- option<user> lowering: the generator's instantiation over userTys
    -- (optionUser_tie): the SOME branch flattens the payload record
    -- into the static area @64 (the discr @56; the tags = the
    -- cons-chain walk's (ptr,len) array). Option ctor tags: none = 0,
    -- some = 1 (Lean's ctor order); payload rides @8.
    let body := optionUserBody pass certLayout d.name.toString
    { name := s!"{d.name.toString}_abi"
      params := paramsOf, result := some "i32"
      locals := [("opt", "i32"), ("tag", "i32"), ("u", "i32"), ("p", "i32")
                 , ("cur", "i32"), ("n", "i32"), ("arr", "i32"), ("w", "i32")]
      body }
  else if shape == "userParam" then
    -- The RECORD-PARAM adapter (user-valid): the generator's reboxRecord
    -- instantiation over userTys (userParamBody). The flat params =
    -- reboxParams userTys userParamNames (pinned ≡ userFlatTys); the
    -- body reconstructs the guest object (string ctors, tags cons
    -- chain, refs-first User {name@8, email@16, tags@24, id@32}).
    let params : List Wat.Param := reboxParams Layout.userTys userParamNames
    let body := userParamBody d.name.toString
    { name := s!"{d.name.toString}_abi"
      params := params, result := some "i32"
      locals := [("ti", "i32"), ("tq", "i32"), ("tsp", "i32"), ("tln", "i32")
                , ("ts", "i32"), ("tc", "i32"), ("acc", "i32")
                , ("ns", "i32"), ("es", "i32"), ("u", "i32")]
      body }
  else if shape == "variantParam" then
    -- The VARIANT-PARAM adapter (order-error-valid): the canonical ABI
    -- hands a variant FLAT — discr i32 + the JOINED payload (the max
    -- of the cases' flat types: invalid-item's [i64] and
    -- insufficient-funds' [f64] join to i64). variantBox reconstructs
    -- the guest's variant object; the impl's Bool = raw i32 — no
    -- return area.
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
    -- list<user> lowering (the ASYNC watch-orders' result): the
    -- generator's instantiation (listUserBody) — the outer walk lowers
    -- EACH user into a 32-byte flat record (the tags = a NESTED
    -- string-list walk); the return area (56..64) = the list's own
    -- (ptr, len); the async task-return delivery.
    let body := listUserBody certLayout certSize d.name.toString kebab
    { name := s!"{d.name.toString}_abi"
      params := [ { name := some "into_disc", ty := "i32" }
                , { name := some "into_payload", ty := "i64" } ]
      result := some "i32"
      locals := [("v", "i32"), ("lst", "i32"), ("curU", "i32"), ("nU", "i32")
                 , ("arrU", "i32"), ("wU", "i32"), ("e", "i32"), ("p2", "i32")
                 , ("curT", "i32"), ("nT", "i32"), ("arrT", "i32"), ("wT", "i32")]
      body }
  else if shape == "streamU64" || shape == "streamUser" then
    -- STREAM lowering (the ASYNC watch-counts/watch-users): the
    -- generator's instantiation (streamBody); the payload schema picks
    -- the element lowering + walk shape. THE DELIVERY DANCE: the abi
    -- fn = task-return(read) + stash (wr, arr, n) in the GLOBALS +
    -- return 1 (YIELD); the callback = the WRITE SITE.
    let elem : StreamElem := if shape == "streamU64" then .u64 else .user
    let body := streamBody pass certLayout certSize d.name.toString kebab elem
    { name := s!"{d.name.toString}_abi"
      params := paramsOf, result := some "i32"
      locals := [("h", "i64"), ("rd", "i32"), ("wr", "i32"), ("lst", "i32")
                 , ("cur", "i32"), ("n", "i32"), ("arr", "i32"), ("w", "i32")]
                 ++ (if shape == "streamU64" then []
                     else [("curU", "i32"), ("nU", "i32"), ("arrU", "i32"), ("wU", "i32")
                          , ("e", "i32"), ("p2", "i32"), ("curT", "i32"), ("nT", "i32")
                          , ("arrT", "i32"), ("wT", "i32")])
      body }
  else if shape == "resultOrderError" then
    -- W10.2: the RESULT<T, FAULT> return lowering — the first
    -- result<T, fault> in the committed world (place-order:
    -- result<u64, order-error>). The canonical flat form = [i32
    -- result-discr, i64, i64]: the ok case's u64 and the err case's
    -- variant discr join per position, the err case's joined payload
    -- rides the third slot; 3 flat results > MAX_FLAT_RESULTS=1 → the
    -- return-area-POINTER convention (the callee writes the lowered
    -- results and returns the area ptr — the string shape's; the canon
    -- lift copies out of guest memory). Area @56: the result discr
    -- i32 @56 (ok=0/inl, err=1/inr — Sum's ctor order = the WIT
    -- result's {ok, err} case order); ok → the u64 is BOXED (the LCNF
    -- boxes the Sum.inl scalar field — the ctor keeps it as a REF arg):
    -- the box ptr @8, the raw i64 at box+8; err → the OrderError box
    -- @8 (the ctor-SPLIT form): its discr i32 @4, its joined payload
    -- i64 @8 (raw — the invalidItem sset convention). Pinned
    -- end-to-end: the duel's place-order rows (Lean's eval) + the
    -- host's result_channel round-trip.
    let body : List Wat.Instr :=
      pass ++ [ .call d.name.toString, .localset "r"
      , .localget "r", .mem .i32load8u 4 none, .localset "tag"
      , .i32const 56, .localget "tag", .mem .i32store 0 none
      , .localget "tag", .i32const 0, .op .i32eq
      , .if_ none
          [ .localget "r", .mem .i32load 8 none, .localset "p"
          , .i32const 64, .localget "p", .mem .i64load 8 none
          , .mem .i64store 0 none ]
          [ .localget "r", .mem .i32load 8 none, .localset "e"
          , .i32const 64, .localget "e", .mem .i32load 4 none
          , .mem .i32store 0 none
          , .i32const 72, .localget "e", .mem .i64load 8 none
          , .mem .i64store 0 none ]
      , .i32const 56 ]
    { name := s!"{d.name.toString}_abi"
      params := paramsOf, result := some "i32"
      locals := [("r", "i32"), ("tag", "i32"), ("e", "i32"), ("p", "i32")]
      body }
  else if shape == "bytesParam" then
    -- The BYTES-PARAM adapter (verify-witness, the decode lane): the
    -- generator's listRebox .u8 instantiation (bytesParamBody) — the
    -- guest List UInt8 cons chain (elements = BOXED u8s, built
    -- BACKWARD; the EMPTY list = the allocated {rc, tag=0} block); the
    -- verdict = the impl's raw i32 Bool, returned directly.
    let body := bytesParamBody d.name.toString
    { name := s!"{d.name.toString}_abi"
      params := [ { name := some "ptr", ty := "i32" }
                , { name := some "len", ty := "i32" } ]
      result := some "i32"
      locals := [("acc", "i32"), ("i", "i32"), ("bx", "i32"), ("c", "i32")]
      body }
  else
    -- the GENERAL prologue: pass through / re-box the flat params, call
    -- the impl, return its result (the object case unboxes the flat
    -- i64 from the box's slot @8).
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
exports; the state THREADS across decls (tramps accumulate).
`asyncFns` = the ASYNC-marked exports, DERIVED by the driver from the
schema registry (a hand list could drift: a new async `@[schema_fn]`
needed a second site). `sigOf?` = the registered FuncSig per decl name
(W10.2: the adapter shapes FOLD from it — `adapterShapeOf`; the driver
builds it from `worldExportsOf`). Full async-lift recipe
(wasmparser-derived): notes/wasm-backend-notes.md §async-lift. -/
def emitModule (decls : List (Decl .impure))
    (exportTargets : List (String × Name))
    (stringResult? : Name → Bool := fun _ => false)
    (asyncFns : List String := [])
    (sigOf? : Name → Option SchemaLang.FuncSig := fun _ => none) : M String := do
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
      -- closure value; a blanket unbox-everything unboxed the cons
      -- HEAD SLOT as the argument). A raw i32 param is ambiguous
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
  -- canonical-ABI adapters for the export targets. THE SHAPE: the
  -- W10.2 FOLD (adapterShapeOf over the registered FuncSig — was the
  -- String-keyed hand list), the string result special-cased first
  -- (its shape comes from the ORIGINAL def type, not the sig).
  let shapeOfName (_kebab : String) (n : Name) : Option String :=
    if stringResult? n then some "string"
    else match sigOf? n with | some s => adapterShapeOf s | none => none
  let mut abiFuncs : List Wat.Func := []
  for (kebab, n) in exportTargets do
    for d in decls do
      if d.name.toString == n.toString then
        let shape := (shapeOfName kebab n).getD "default"
        -- THE SCHEMA-TYPED GATE: a record shape's schema must sit
        -- in the generator's field universe (lowered?/reboxed? by
        -- direction) — outside it, THROW (the robustness rule), never
        -- a silently-wrong adapter. The five demo shapes are pinned
        -- inside (shapeTys? + the *_tie pins).
        match shapeTys? shape with
        | some ts =>
            let ok := if paramShape? shape then ts.all reboxed? else ts.all lowered?
            if !ok then
              unsupported s!"adapter shape {shape}: schema field outside the generator's universe"
        | none => pure ()
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
  let cbFuncs : List Wat.Func := asyncTargets.map fun (kebab, n) =>
    let sig3 : List Wat.Param :=
      [{ name := none, ty := "i32" }, { name := none, ty := "i32" }, { name := none, ty := "i32" }]
    match shapeOfName kebab n with
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
  let isStreamShape : Option String → Bool :=
    fun sh => match sh with | some "streamU64" | some "streamUser" => true | _ => false
  let perExport : String → Bool → List Wat.Item := fun kebab stream =>
    if stream then
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
    else
      [ .imp { module := "[export]$root", name := s!"[task-return]{kebab}"
             , id := some s!"tr_{kebab}"
             , params := [{ name := none, ty := "i32" }, { name := none, ty := "i32" }]
             , result := none } ]
  let asyncImports : List Wat.Item :=
    if asyncTargets.isEmpty then []
    else waitables ++ asyncTargets.flatMap fun (kebab, n) =>
      perExport kebab (isStreamShape (shapeOfName kebab n))
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
  let streamGlobals : List Wat.Item := if asyncTargets.any fun (k, n) =>
    isStreamShape (shapeOfName k n)
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
  -- splice marker = the ONE module-level raw (WasmGenMain replaces its
  -- exact bytes with runtime.wat).
  let mod : Wat.Module :=
    { start := none
      items := asyncEnv ++ [ .raw "  ;;RUNTIME-SPLICE", .memory 1 ]
        ++ (funcs.map Wat.Item.func) ++ (abiFuncs.map Wat.Item.func)
        ++ (cbFuncs.map Wat.Item.func) ++ (trampFuncs.map Wat.Item.func)
        ++ table ++ exports ++ cbExports ++ memExport }
  -- the outer StateT state = the mut var's final value (the decl loop
  -- runs in INNER .run's — without this put, StateT.run returns the
  -- initial {}). The caller discards it.
  modify (fun _ => st)
  pure mod.render

end WasmBackend
