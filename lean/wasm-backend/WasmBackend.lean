import Lean
import Lean.Compiler.LCNF
import WasmBackend.Check

/-!
# WasmBackend — LCNF → WAT emission

The `leanir` re-run pattern (see GenMain): the final impure-phase LCNF →
WebAssembly Text. Toolchain: `wasm-tools parse -g` → validate → wasmtime.

Layout (guestlang-owned): `{rc u32@0, tag u8@4, class u8@5, fields @8}`.
Lean's field conventions: ref fields at `8+i*8` (oproj[i]); scalar fields
after the ref slots at `8+size*8+off` (sproj[i,off]).
Special tags: 254 = closure `{rc, 254, class, fnIdx u32@8, partial args@16…}`.

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
i32 pointer. -/
def wasmTyOf? : Expr → Option String
  | .const c _ =>
    if c == `UInt64 then some "i64"
    else if c == `UInt32 || c == `UInt8 || c == `Bool then some "i32"
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
  out : Array String := #[]
  n : Nat := 0
  /-- trampolines emitted so far (pap closures): (fnName, nPartial). -/
  tramps : Array (Name × Nat) := #[]
  deriving Inhabited

abbrev M := StateT S (Except String)

def emit (line : String) : M Unit := modify fun s => { s with out := s.out.push line }

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
def load (fvarId : FVarId) : M String := do
  match (← get).fvars[fvarId]? with
  | some (n, _) => pure s!"local.get ${n}"
  | none => throw s!"WasmBackend: unbound fvar {fvarId.name}"

/-! ## Primitives -/

def binop? : Name → Option String
  | ``UInt64.add => some "i64.add"
  | ``UInt64.sub => some "i64.sub"
  | ``UInt64.mul => some "i64.mul"
  | ``UInt64.decLt => some "i64.lt_u"
  | ``UInt64.decEq => some "i64.eq"
  | _ => none

def storeOp (ty : Option String) : String :=
  match ty with | some "i32" => "i32.store" | _ => "i64.store"

def emitArg : Arg .impure → M Unit
  | .fvar fvarId => do emit (← load fvarId)
  | _ => emit ";; ERASED arg"

mutual

partial def emitCode (code : Code .impure) : M Unit := do
  match code with
  | .let decl k => emitLet decl; emitCode k
  | .return fvarId => emitReturn fvarId
  | .cases c => emitCases c
  | .inc fvarId _ _ _ k =>
      emit (← load fvarId); emit "call $rc_inc"; emitCode k
  | .dec fvarId _ _ _ _ k =>
      emit (← load fvarId); emit "call $rc_dec"; emitCode k
  | .del _ k => emitCode k
  | .jp _ k => emitCode k
  | .jmp .. => unsupported "Code.jmp"
  | .unreach _ => emit "unreachable"
  | .sset _f _i offset y ty k =>
      -- field store: sset var[i, off] := y → mem[var + 8 + off] = y
      -- (the RC pass splits ctor-alloc from field-init)
      emit (← load _f)
      emit (← load y)
      emit s!"{storeOp (wasmTyOf? ty)} offset={8 + offset}"
      emitCode k
  | .oset .. | .uset .. | .setTag .. =>
    unsupported "in-place mutation (oset/uset/setTag)"
  | .fun _ _ h => absurd h (by simp)

partial def emitReturn (fvarId : FVarId) : M Unit := do
  emit (← load fvarId)
  emit "return"

partial def emitCases (c : Cases .impure) : M Unit := do
  emit (← load c.discr)
  emit "i32.load8_u offset=4"
  let tag ← bindFresh "i32"
  emit s!"local.set ${tag}"
  goAlts tag c.alts.toList

partial def goAlts (tag : String) : List (Alt .impure) → M Unit
  | [] => emit "unreachable ;; no matching ctor tag"
  | alt :: rest => do
      match alt with
      | .ctorAlt info code =>
          emit s!"local.get ${tag}"
          emit s!"i32.const {info.cidx}"
          emit "i32.eq"
          emit "if (result i64)"
          emitCode code
          emit "else"
          goAlts tag rest
          emit "end"
      | .default code => emitCode code
      | .alt _ _ _ h => absurd h (by simp)

partial def emitLet (decl : LetDecl .impure) : M Unit := do
  let ty := wasmTyOf? decl.type
  match decl.value with
  | .lit (.uint64 v) =>
      let l ← bindLocal decl.fvarId "i64"
      emit s!"i64.const {v}"; emit s!"local.set ${l}"
  | .lit (.uint8 v) | .lit (.uint32 v) =>
      let l ← bindLocal decl.fvarId "i32"
      emit s!"i32.const {v}"; emit s!"local.set ${l}"
  | .lit (.nat _) => unsupported "Nat literal (GMP — banned in the guest)"
  | .lit _ => unsupported "literal kind (str/uint16/usize)"
  | .erased => pure ()
  | .fvar fvarId args =>
      if args.isEmpty then
        let l ← bindLocal decl.fvarId (ty.getD "i64")
        emit (← load fvarId); emit s!"local.set ${l}"
      else
        -- CLOSURE APPLICATION: f is an object; call its trampoline:
        -- push closure-ptr, fresh args, fnIdx; call_indirect.
        let l ← bindLocal decl.fvarId "i32"  -- result: boxed obj
        emit (← load fvarId)  -- closure ptr (also the trampoline's 1st arg)
        for a in args do emitArg a
        emit (← load fvarId)
        emit "i32.load offset=8"  -- fnIdx
        emit "call_indirect (type $sig_1box)"
        emit s!"local.set ${l}"
  | .fap fn args =>
      match binop? fn with
      | some op =>
          let l ← bindLocal decl.fvarId (ty.getD "i64")
          for a in args do emitArg a
          emit op
          emit s!"local.set ${l}"
      | none =>
          let l ← bindLocal decl.fvarId
            (if args.isEmpty then "i32" else ty.getD "i64")
          -- 0-ary fap = top-level closure const (obj); else a scalar call
          for a in args do emitArg a
          emit s!"call ${fn.toString}"
          emit s!"local.set ${l}"
  | .pap fn args =>
      -- closure: alloc {rc, tag=254, class, fnIdx, partial args…}
      let nA := args.size
      let tramp := s!"pap_{fn.toString}_{nA}"
      -- table slot: position in the deduped tramp list (push-order)
      let idx : Int ← do
        let ts := (← get).tramps
        match ts.idxOf? (fn, nA) with
        | some i => pure (i : Int)
        | none =>
            modify fun s => { s with tramps := s.tramps.push (fn, nA) }
            pure (ts.size : Int)
      let l ← bindLocal decl.fvarId "i32"
      emit s!"i32.const {16 + nA * 8}"
      emit "call $alloc"
      emit s!"local.set ${l}"
      emit (← load decl.fvarId)
      emit "i32.const 254"
      emit "i32.store8 offset=4"
      emit (← load decl.fvarId)
      emit s!"i32.const {idx}"
      emit "i32.store offset=8"
      let mut off := 16
      for a in args do
        emit (← load decl.fvarId)
        emitArg a
        emit s!"i32.store offset={off}"
        off := off + 8
  | .sproj _ offset var _ =>
      let tyS := ty.getD "i64"
      let l ← bindLocal decl.fvarId tyS
      emit (← load var)
      let loadOp := if tyS == "i64" then "i64.load" else "i32.load"
      emit s!"{loadOp} offset={8 + offset}"
      emit s!"local.set ${l}"
  | .oproj i var _ =>
      -- ref field: 8-byte slot at 8+i*8, an object pointer
      let l ← bindLocal decl.fvarId "i32"
      emit (← load var)
      emit s!"i32.load offset={8 + i * 8}"
      emit s!"local.set ${l}"
  | .box ty var _ =>
      -- scalar → object: alloc 16, store the scalar @8 (op by scalar ty)
      let l ← bindLocal decl.fvarId "i32"
      emit "i32.const 16"
      emit "call $alloc"
      emit s!"local.set ${l}"
      emit (← load decl.fvarId)
      emit (← load var)
      emit s!"{storeOp (wasmTyOf? ty)} offset=8"
  | .unbox var _ =>
      -- the box's slot type = the unboxed scalar's type (Bool→i32, u64→i64)
      let tyS := ty.getD "i64"
      let l ← bindLocal decl.fvarId tyS
      emit (← load var)
      let loadOp := if tyS == "i64" then "i64.load" else "i32.load"
      emit s!"{loadOp} offset=8"
      emit s!"local.set ${l}"
  | .ctor info args =>
      -- bare alloc + tag; REF args stored @8+i*8. Scalar fields arrive
      -- via sset afterwards (the RC pass splits scalar ctors — verified:
      -- `ctor_0.0.8[Shape.circle]` then `sset [0,0]`); ref ctors keep
      -- their args (verified: `ctor_1[List.cons] _f.2 _x.1`).
      let p ← bindLocal decl.fvarId "i32"
      emit s!"i32.const {8 + info.size * 8 + info.ssize}"
      emit "call $alloc"
      emit s!"local.set ${p}"
      emit (← load decl.fvarId)
      emit s!"i32.const {info.cidx}"
      emit "i32.store8 offset=4"
      let mut refOff := 8
      for a in args do
        emit (← load decl.fvarId)
        emitArg a
        emit s!"i32.store offset={refOff}"
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
          emit op
          emit s!"local.set ${l}"
      | none, true =>
          -- 0-ary const: a top-level closure constant (_closed decls)
          let l ← bindLocal decl.fvarId "i32"
          emit s!"call ${fn.toString}"
          emit s!"local.set ${l}"
      | _, _ => unsupported s!"const {fn}"

end

/-! ## Result types -/

mutual

partial def resultTyOfAlt : Alt .impure → Option String
  | .ctorAlt _ code => resultTyOf code
  | .default code => resultTyOf code
  | .alt _ _ _ h => absurd h (by simp)

partial def resultTyOf : Code .impure → Option String :=
  resultTyOfWalk none

partial def resultTyOfWalk (acc : Option String) : Code .impure → Option String
  | .let decl k => resultTyOfWalk (some ((wasmTyOf? decl.type).getD "i32")) k
  -- (object-typed lets — ctor/pap/fn-typed — are i32 pointers)
  | .return _ => acc
  | .cases c => (c.alts.toList.filterMap resultTyOfAlt).head?
  | .sset _ _ _ _ _ k => resultTyOfWalk acc k
  | .inc _ _ _ _ k => resultTyOfWalk acc k
  | .dec _ _ _ _ _ k => resultTyOfWalk acc k
  | .del _ k => resultTyOfWalk acc k
  | .jp _ k => resultTyOfWalk acc k
  | .unreach _ => none
  | .jmp .. => none
  | .oset .. | .uset .. | .setTag .. => none
  | .fun _ _ h => absurd h (by simp)

end

/-! ## Decl emission -/

def emitDecl (d : Decl .impure) : M String := do
  let code := match d.value with
    | .code c => c
    | .extern .. => .unreach (Expr.const `Unit [])
  let params := d.params.toList.map fun p =>
    s!"(param ${p.binderName.toString} {paramWasmTy p})"
  let resultTy := resultTyOf code
  let header :=
    s!"(func ${d.name.toString} {String.intercalate " " params}"
      ++ (match resultTy with | some t => s!" (result {t})" | none => "")
  for p in d.params do
    bindNamed p.fvarId p.binderName.toString (paramWasmTy p)
  emitCode code
  let s ← get
  let locals := s.locals.toList.map fun (n, t) => s!"  (local ${n} {t})"
  let body := String.intercalate "\n  " (locals ++ s.out.toList)
  pure s!"{header}\n  {body}\n)"

/-- Emit the module: runtime + funcs + trampolines + table + exports.
The state THREADS across decls (tramps accumulate; l-counter keeps
locals globally unique). -/
def emitModule (decls : List (Decl .impure)) (exports : List String) : M String := do
  let mut st : S := {}
  let mut funcs : List String := []
  for d in decls do
    let (f, s2) ← emitDecl d |>.run st
    st := { s2 with out := #[], locals := #[] }
    funcs := funcs ++ [f]
  -- trampolines: (closure i32, boxed fresh arg i32) → boxed result i32.
  -- Unbox the fresh arg, apply captured args (raw @16…), box the result.
  let mut trampFuncs : List String := []
  let mut elem : List String := []
  for (fn, nA) in st.tramps.toList do
    let name := s!"pap_{fn.toString}_{nA}"
    let boxed := fn.toString.endsWith "_boxed" || fn.toString.endsWith "_closed"
    let mut body : List String := []
    let mut off := 16
    if boxed then
      -- boxed target: forward args as-is (objects in, object out)
      for _ in [0:nA] do
        body := body ++ [s!"local.get $c", s!"i32.load offset={off}"]
        off := off + 8
      body := body ++ ["local.get $x0", s!"call ${fn.toString}"]
    else
      -- raw scalar target: unbox captured + fresh args, call, box result
      for _ in [0:nA] do
        body := body ++ [s!"local.get $c", s!"i32.load offset={off}", "i64.load offset=8"]
        off := off + 8
      body := body ++ ["local.get $x0", "i64.load offset=8", s!"call ${fn.toString}", "local.set $r",
        "i32.const 16", "call $alloc", "local.tee $p", "local.get $r", "i64.store offset=8", "local.get $p"]
    let f :=
      if boxed then
        s!"(func ${name} (param $c i32) (param $x0 i32) (result i32)\n  " ++
          String.intercalate "\n  " body ++ "\n)"
      else
        s!"(func ${name} (param $c i32) (param $x0 i32) (result i32)\n" ++
          String.intercalate "\n  " ["  (local $r i64)", "  (local $p i32)"] ++ "\n  " ++
          String.intercalate "\n  " body ++ "\n)"
    trampFuncs := trampFuncs ++ [f]
    elem := elem ++ [s!"${name}"]
  let nT := st.tramps.size
  let table := if nT > 0 then
    ["  (type $sig_1box (func (param i32 i32) (result i32)))",
     s!"  (table {nT} funcref)",
     s!"  (elem (i32.const 0) {String.intercalate " " elem})"]
  else []
  pure <| String.intercalate "\n" ((["(module", "  (memory 1)"] ++ funcs ++ trampFuncs ++ table) ++ exports ++ [")"])

end WasmBackend
