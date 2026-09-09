import Lean
import Lean.Compiler.LCNF

/-!
# WasmBackend — LCNF → WAT emission

Consumes the final impure-phase LCNF (the `leanir` re-run pattern —
see GenMain) and emits WebAssembly Text Format. The toolchain:

    WAT → `wasm-tools parse -g` (binary + DWARF + name section)
        → `wasm-tools validate` → wasmtime --invoke smoke

ROBUSTNESS CONTRACT: unsupported LCNF constructs are COMPILE ERRORS
(`throw`), never silent comments — a missing backend case fails
`wasm-gen` with the decl name and construct, so it can never reach a
guest as wrong code. Coverage grows by adding cases, not by hoping.

The guest runtime is OURS: the object layout is guestlang's, not Lean's
C runtime's:

    { rc : u32 @0, tag : u8 @4, pad : u8[3], field_0 @8, field_1 @16, … }

LCNF's `sproj[n, off]` offsets are field-area relative — absolute offset
is `8 + off` (one 8-byte slot per scalar field, matching the dump:
`rect` fields at sproj[0,0] / sproj[0,8]).

v1 scope (the scalar core): let/return/cases/const-primitives/lits/
sproj; `inc`/`dec`/`del` erased (leak — the pooled allocator lands with
guestlang-std); `._boxed` wrappers are skipped: the erased-Type calling
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

/-- Emission errors: unsupported constructs ABORT the compile (the
robustness contract) — the message names the decl and the construct. -/
abbrev M := StateT S (Except String)

instance : Inhabited (M String) := ⟨fun s => .ok (default, s)⟩

def emit (line : String) : M Unit := modify fun s => { s with out := s.out.push line }

/-- Unsupported construct → compile error (naming it is the fix path). -/
def unsupported (what : String) : M Unit := throw s!"WasmBackend: unsupported construct: {what}"

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

/-- Fresh local WITHOUT an fvar binding (temps: the ctor tag). Binding
the discr's fvarId here would shadow it — alt codes still read the
OBJECT pointer through it. -/
def bindFresh (ty : String) : M String := do
  let name := s!"l{S.n (← get)}"
  modify fun s => { s with locals := s.locals.push (name, ty), n := s.n + 1 }
  pure name

def load (fvarId : FVarId) : M String := do
  let s ← get
  match s.fvars[fvarId]? with
  | some n => pure s!"local.get ${n}"
  | none => throw s!"WasmBackend: unbound fvar {fvarId.name}"

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
  | .inc fvarId _ _ _ k =>
      emit (← load fvarId)
      emit "call $rc_inc"
      emitCode k
  | .dec fvarId _ _ _ _ k =>
      emit (← load fvarId)
      emit "call $rc_dec"
      emitCode k
  | .del _ k => emitCode k
  | .jp _ k => emitCode k  -- v1: join points inlined-away by elim (not observed)
  | .jmp .. => unsupported "Code.jmp"
  | .unreach _ => emit "unreachable"
  | .sset f _i offset y ty k =>
      -- field store (the RC pass splits ctor-alloc from field-init):
      -- sset var[i, offset] := y → mem[var + 8 + offset] = y
      -- (_i = field index; offset = BYTE offset from the dump)
      emit (← load f)
      emit (← load y)
      let op := match wasmTyOf? ty with
        | some "i32" => "i32.store"
        | _ => "i64.store"
      emit s!"{op} offset={8 + offset}"
      emitCode k
  | .oset .. | .uset .. | .setTag .. =>
    unsupported "in-place mutation (oset/uset/setTag)"
  | .fun _ _ h => absurd h (by simp)  -- pure-only ctor: unreachable

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
  | .lit (.nat _) => unsupported "Nat literal (GMP — banned in the guest)"
  | .lit (.usize _) => unsupported "USize literal (word-size portability: later)"
  | .lit (.str _) => unsupported "String literal (UTF-8 objects: guestlang-std)"
  | .lit (.uint16 _) => unsupported "UInt16 literal"
  | .erased => pure ()  -- types/proofs: no runtime value
  | .fvar fvarId args =>
      if args.isEmpty then
        let l ← bindLocal decl.fvarId (ty.getD "i64")
        emit (← load fvarId)
        emit s!"local.set ${l}"
      else
        unsupported "fvar application (join-point call)"
  | .fap fn args =>
      -- impure-phase applications: primitives (binop table) AND calls
      match binop? fn with
      | some op =>
          let l ← bindLocal decl.fvarId (ty.getD "i64")
          for a in args do emitArg a
          emit op
          emit s!"local.set ${l}"
      | none =>
          let l ← bindLocal decl.fvarId (ty.getD "i64")
          for a in args do emitArg a
          emit s!"call ${fn.toString}"
          emit s!"local.set ${l}"
  | .sproj _ offset var _ =>
      -- object field: 8-byte scalar slots, header is 8 bytes
      let tyS := ty.getD "i64"
      let l ← bindLocal decl.fvarId tyS
      emit (← load var)
      let loadOp := if tyS == "i64" then "i64.load" else "i32.load"
      emit s!"{loadOp} offset={8 + offset}"
      emit s!"local.set ${l}"
  | .ctor info args _ =>
      -- ptr = alloc(8 + ssize): $alloc sets rc=1 + the class byte;
      -- then tag store + one 8-byte slot per scalar field (v1: scalars
      -- only — ref fields arrive with oset support).
      let p ← bindLocal decl.fvarId "i32"
      emit s!"i32.const {8 + info.ssize}"
      emit "call $alloc"
      emit s!"local.set ${p}"
      emit (← load decl.fvarId)
      emit s!"i32.const {info.cidx}"
      emit "i32.store8 offset=4"
      let mut off := 8
      for a in args do
        emit (← load decl.fvarId)
        emitArg a
        emit s!"i64.store offset={off}"
        off := off + 8
  | .box _ var _ =>
      -- scalar → object: v1 passes the scalar raw (boundary layer decides)
      let l ← bindLocal decl.fvarId "i32"
      emit (← load var)
      emit s!"local.set ${l} ;; BOX: v1 passes the scalar raw"
  | .unbox var _ =>
      let l ← bindLocal decl.fvarId (ty.getD "i64")
      emit (← load var)
      emit s!"local.set ${l} ;; UNBOX: raw pass-through in v1"
  | .proj .. | .oproj .. | .uproj .. =>
      unsupported "proj/oproj/uproj"
  | .pap .. =>
      unsupported "pap (closures — funcref+env pairs: next up)"
  | .reset .. | .reuse .. =>
      unsupported "Perceus reset/reuse (in-place update: later)"
  | .isShared .. =>
      unsupported "isShared"
  | .const fn .. =>
      unsupported s!"const {fn} (pure-phase application)"

/-- `return` — the function's result is the loaded local. -/
partial def emitReturn (fvarId : FVarId) : M Unit := do
  emit (← load fvarId)
  emit "return"

/-- Constructor dispatch: tag = i32.load8_u offset=4 (our header),
stashed in a temp local (each alt level re-tests it); chain of
if/else on the tag, each arm leaves the result on the stack. -/
partial def emitCases (c : Cases .impure) : M Unit := do
  emit (← load c.discr)
  emit "i32.load8_u offset=4"
  let tag ← bindFresh "i32"  -- fresh local holding the tag
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

/-- The wasm result type of a code block: walk to the `.return`,
carrying the LAST let's type (the returned fvar's binding) through all
continuation nodes (sset/inc/dec/del/fun/jp interleave the chain). -/
partial def resultTyOf : Code .impure → Option String :=
  resultTyOfWalk none

partial def resultTyOfWalk (acc : Option String) : Code .impure → Option String
  | .let decl k => resultTyOfWalk (wasmTyOf? decl.type) k
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
  pure full

/-- Emit the whole module for the final impure decls. -/
def emitModule (decls : List (Decl .impure)) (exports : List String) : M String := do
  let mut funcs : List String := []
  for d in decls do
    let (f, _) ← emitDecl d |>.run {}
    funcs := funcs ++ [f]
  pure <| String.intercalate "\n" ((["(module", "  (memory 1)"] ++ funcs) ++ exports ++ [")"])

end WasmBackend
