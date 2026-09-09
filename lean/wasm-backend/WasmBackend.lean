import Lean
import Lean.Compiler.LCNF

/-!
# WasmBackend — LCNF → WAT emission

Consumes the final impure-phase LCNF (the `leanir` re-run pattern —
see GenMain) and emits WebAssembly Text Format. The toolchain:

    WAT → `wasm-tools parse -g` (binary + DWARF + name section)
        → `wasm-tools validate` → `wasm-tools component new`

The guest runtime is OURS: the object layout is guestlang's, not Lean's
C runtime's:

    { rc : u32 @0, tag : u8 @4, pad : u8[3], field_0 @8, field_1 @16, … }

LCNF's `sproj[n, off]` offsets are field-area relative — absolute offset
is `8 + off` (one 8-byte slot per scalar field, matching the dump:
`rect` fields at sproj[0,0] / sproj[0,8]).

v1 scope (the scalar core): let/return/cases/const-primitives/lits/
sproj, `inc`/`dec`/`del` erased (leak — bump allocator comes with
guestlang-std). `._boxed` wrappers are skipped: the erased-Type calling
convention is replaced at the boundary by the canonical ABI.
-/

namespace WasmBackend

open Lean Compiler.LCNF

/-! ## Scalar ABI -/

/-- Wasm scalar type for an LCNF type expression. `none` = object
(inductive/erased) → i32 pointer. -/
def wasmTyOf? : Expr → Option String
  | .const c _ =>
    if c == `UInt64 then some "i64"
    else if c == `UInt32 || c == `UInt8 || c == `Bool then some "i32"
    else none
  | _ => none

/-- Param → wasm type. Borrowed scalars are objects (tagged pointers):
the `@&s : UInt64` shape — i32. -/
def paramWasmTy (p : Param .impure) : String :=
  match p.borrow, wasmTyOf? p.type with
  | false, some t => t
  | _, _ => "i32"

/-! ## Emission state -/

structure S where
  /-- fvarId → wasm local name (without `$`). -/
  fvars : Std.HashMap FVarId String := {}
  /-- declared locals (name, ty) — params excluded (they're decl'd in the header). -/
  locals : Array (String × String) := #[]
  /-- emitted instruction lines (in order). -/
  out : Array String := #[]
  /-- fresh local counter. -/
  n : Nat := 0
  deriving Inhabited

abbrev M := StateM S

def emit (line : String) : M Unit := modify fun s => { s with out := s.out.push line }

/-- Fresh local bound to an fvar. -/
def bindLocal (fvarId : FVarId) (ty : String) : M String := do
  let name := s!"l{S.n (← get)}"
  modify fun s => { s with
    fvars := s.fvars.insert fvarId name
    locals := s.locals.push (name, ty)
    n := s.n + 1 }
  pure name

/-- Bind an fvar to an EXISTING wasm name (params: the declared `$name`). -/
def bindNamed (fvarId : FVarId) (name : String) : M Unit :=
  modify fun s => { s with fvars := s.fvars.insert fvarId name }

def load (fvarId : FVarId) : M String := do
  let s ← get
  match s.fvars[fvarId]? with
  | some n => pure s!"local.get ${n}"
  | none => pure s!";; UNBOUND fvar {fvarId.name}"

/-! ## Primitive operations -/

/-- Scalar binops: LCNF `const` applications lowered to wasm ops.
Arg order matches wasm (decLt a b = a < b = i64.lt_u a b). -/
def binop? : Name → Option String
  | ``UInt64.add => some "i64.add"
  | ``UInt64.sub => some "i64.sub"
  | ``UInt64.mul => some "i64.mul"
  | ``UInt64.decLt => some "i64.lt_u"
  | ``UInt64.decEq => some "i64.eq"
  | _ => none

/-! ## Code emission -/

/-- Emit an Arg load (v1: fvar args only). -/
def emitArg : Arg .impure → M Unit
  | .fvar fvarId => do emit (← load fvarId)
  | _ => emit ";; ERASED arg"

mutual

/-- Emit code: leaves the result on the wasm stack (functions end in
`return`, so the last emitted shape is the `return` instruction). -/
partial def emitCode (code : Code .impure) : M Unit := do
  match code with
  | .let decl k => emitLet decl; emitCode k
  | .return fvarId => emitReturn fvarId
  | .cases c => emitCases c
  | .inc _ _ _ _ k => emitCode k  -- Perceus inc: leak (v1)
  | .dec _ _ _ _ _ k => emitCode k  -- Perceus dec: leak (v1)
  | .del _ k => emitCode k
  | .fun _ _ h => absurd h (by simp)  -- pure-only ctor: unreachable
  | .jp _ k => emitCode k  -- v1: join points inlined-away by elim (not observed)
  | .jmp .. => emit ";; JMP: unsupported in v1"
  | .unreach _ => emit "unreachable"
  | .oset .. | .uset .. | .sset .. | .setTag .. =>
    emit ";; mutation: unsupported in v1"

/-- One let binding. -/
partial def emitLet (decl : LetDecl .impure) : M Unit := do
  let ty := wasmTyOf? decl.type
  match decl.value with
  | .lit (.uint64 v) =>
      let l ← bindLocal decl.fvarId "i64"
      emit s!"i64.const {v}"
      emit s!"local.set ${l}"
  | .lit (.uint8 v) | .lit (.uint32 v) =>
      let l ← bindLocal decl.fvarId "i32"
      emit s!"i32.const {v}"
      emit s!"local.set ${l}"
  | .lit (.nat _) => emit ";; NAT literal: GMP — unsupported in the guest"
  | .lit _ => emit ";; literal: unsupported kind"
  | .erased => pure ()  -- types/proofs: no runtime value
  | .fvar fvarId args =>
      if args.isEmpty then
        let l ← bindLocal decl.fvarId (ty.getD "i64")
        emit (← load fvarId)
        emit s!"local.set ${l}"
      else
        emit ";; fvar application: unsupported in v1"
  | .const fn _ args _ =>
      match binop? fn, args.isEmpty with
      | some op, false =>
          let l ← bindLocal decl.fvarId (ty.getD "i64")
          for a in args do emitArg a
          emit op
          emit s!"local.set ${l}"
      | _, _ => emit s!";; const {fn}: unsupported in v1"
  | .sproj _ offset var _ =>
      -- object field: 8-byte scalar slots, header is 8 bytes
      let tyS := ty.getD "i64"
      let l ← bindLocal decl.fvarId tyS
      emit (← load var)
      let loadOp := if tyS == "i64" then "i64.load" else "i32.load"
      emit s!"{loadOp} offset={8 + offset}"
      emit s!"local.set ${l}"
  | .ctor _ _ _ => emit ";; ctor alloc: needs the bump allocator (guestlang-std)"
  | .box _ var _ =>
      -- scalar → object: v1 passes the scalar raw (boundary layer decides)
      let l ← bindLocal decl.fvarId "i32"
      emit (← load var)
      emit s!"local.set ${l} ;; BOX: v1 passes the scalar raw"
  | .unbox var _ =>
      let l ← bindLocal decl.fvarId (ty.getD "i64")
      emit (← load var)
      emit s!"local.set ${l} ;; UNBOX: raw pass-through in v1"
  | .fap fn args =>
      -- impure-phase applications: primitives (binop table) AND calls
      match binop? fn with
      | some op =>
          let l ← bindLocal decl.fvarId (ty.getD "i64")
          for a in args do emitArg a
          emit op
          emit s!"local.set ${l}"
      | none =>
          -- real call: push args, call, capture
          let l ← bindLocal decl.fvarId (ty.getD "i64")
          for a in args do emitArg a
          emit s!"call ${fn.toString}"
          emit s!"local.set ${l}"
  | .proj .. | .oproj .. | .uproj .. =>
      emit ";; proj family: unsupported in v1"
  | .pap .. | .reset .. | .reuse .. | .isShared .. =>
      emit ";; Perceus/closure op: unsupported in v1"

partial def emitReturn (fvarId : FVarId) : M Unit := do
  emit (← load fvarId)
  emit "return"

/-- Constructor dispatch: tag = i32.load8_u offset=4 (our header),
stashed in a temp local (each alt level re-tests it); chain of
if/else on the tag, each arm leaves the result on the stack. -/
partial def emitCases (c : Cases .impure) : M Unit := do
  emit (← load c.discr)
  emit "i32.load8_u offset=4"
  let tag ← bindLocal c.discr "i32"  -- fresh local holding the tag
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
      | .alt _ _ _ h => absurd h (by simp)  -- pure-only ctor: unreachable

end

/-! ## Decl emission -/

mutual

/-- The wasm result type of an alt's code. -/
partial def resultTyOfAlt : Alt .impure → Option String
  | .ctorAlt _ code => resultTyOf code
  | .default code => resultTyOf code
  | .alt _ _ _ h => absurd h (by simp)

/-- The wasm result type of a code block (the final let's type). -/
partial def resultTyOf : Code .impure → Option String
  | .let decl k =>
    match k with
    | .return _ => wasmTyOf? decl.type
    | _ => resultTyOf k
  | .cases c => (c.alts.toList.filterMap resultTyOfAlt).head?
  | _ => none

end

/-- Emit one function: `(func $name (param …) (result …) …)`. -/
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
    bindNamed p.fvarId p.binderName.toString
  emitCode code
  -- the body lines were appended to state; pull them out
  let s ← get
  let locals := s.locals.toList.map fun (n, t) => s!"  (local ${n} {t})"
  let body := String.intercalate "\n  " (locals ++ s.out.toList)
  let full := s!"{header}\n  {body}\n)"
  -- reset output for the next decl (fresh scope)
  modify fun s => { s with out := #[] }
  pure full

/-- Emit the whole module for the final impure decls. -/
def emitModule (decls : List (Decl .impure)) (exports : List String) : String :=
  let funcs := decls.map fun d => (emitDecl d {}).1
  String.intercalate "\n" ((["(module", "  (memory 1)"] ++ funcs) ++ exports ++ [")"])

end WasmBackend
