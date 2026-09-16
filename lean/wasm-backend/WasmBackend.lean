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
the emitted instrs are structurally the proved function's outputs.

The HONEST LEDGER of `Instr.raw` (the escape hatch, counted at emission;
the count is printed by GenMain — 0 since the raw→typed migration:
everything — the adapters (string/optionUser/listUser/streamU64/
streamUser + the userParam RECORD-PARAM adapter), the general path's
instruction emission (emitCode/emitLet/emitCases/goAlts/emitReturn/
emitArg — restructured: goAlts builds NESTED `if_` bodies via
`emitScoped` instead of flat if/else/end lines), the trampolines, the
callbacks, cabi_realloc, and the module-level assembly — is typed.
* The `Wat.Item.raw "  ;;RUNTIME-SPLICE"` marker is BY DESIGN raw
  (GenMain replaces those exact bytes with runtime.wat) — the ONE
  module-level raw; it is not an instruction, so the emitted raw-count
  stays 0.
* The record-param adapter's ABI fact (probed against the encoder):
  a record param crosses FLAT while its flattened form fits
  MAX_FLAT_PARAMS=16 — the demo's user (u64 + 3×(ptr,len) = 7 flat
  values) arrives as 7 core params `[i64, i32×6]`; a POINTER-form
  adapter FAILS the `component new` encode (`expected [I64, I32, …]`).
  The adapter reconstructs the guest object: strings = alloc(16+len)
  {tag=250, len@8, memory.copy bytes@16}, the tags list = a cons chain
  built by walking the flat (ptr,len) array BACKWARD, the User = the
  refs-first object {tag, name@8, email@16, tags@24, id@32}.

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

/-! ## guestlang-std string intrinsics

The std intrinsics fold the CLOSED `GuestlangStd.Intrinsic` universe
(`GuestlangStd/StrOps.lean` — the oracle bodies, the runtime
spellings, the wasm result types all derive from the one inductive):
`Intrinsic.ofName?` maps a Lean declaration name to its ctor. The
Lean bodies are never compiled (they are the differential ORACLE —
see DemoFn).
Guest string layout: `{rc@0, tag=250@4, len u32@8, bytes@16}` — a
variable-size object (16 + len); the bytes live INLINE so RC frees the
whole string (no separate byte allocation to leak). Byte-length ≠
char-length off ASCII (documented, v1). -/

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
              && (GuestlangStd.Intrinsic.ofName? fn).isNone then
            for a in args do emitArg a
            emitI (.returncall fn.toString)
          else
            emitLet decl; emitCode k
      | _, _ => emitLet decl; emitCode k
  | .return fvarId => emitReturn fvarId
  | .cases c => emitCases c
  | .inc fvarId _ _ _ k =>
      emitI (.localget (← load fvarId)); emitI (.call "rc_inc"); emitCode k
  | .dec fvarId _ _ _ _ k =>
      emitI (.localget (← load fvarId)); emitI (.call "rc_dec"); emitCode k
  | .del _ k => emitCode k
  | .jp _ k => emitCode k
  | .jmp .. => unsupported "Code.jmp"
  | .unreach _ => emitI .unreach
  | .sset _f i offset y ty k =>
      -- field store: sset var[slot, off] := y → mem[var + 8 + slot*8 + off]
      -- (the RC pass splits ctor-alloc from field-init AND reorders the
      -- fields REF-FIRST: the slot index = the field's position in the
      -- REORDERED layout — the id of a {u64, string, string, list} record
      -- is slot 3 (@8+3*8) AFTER the three ref slots. The old emission
      -- discarded `i` — the id CLOBBERED the first ref's pointer: the
      -- object case was never exercised before the schema records.)
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
    emitIs (← goAlts v c.alts.toList)
  else do
    emitI (.localget (← load c.discr))
    emitI (.mem .i32load8u 4 none)
    let tag ← bindFresh "i32"
    emitI (.localset tag)
    emitIs (← goAlts tag c.alts.toList)

partial def goAlts (scrut : String) : List (Alt .impure) → M (List Wat.Instr)
  | [] => pure [.unreach]
  | alt :: rest => do
      match alt with
      | .ctorAlt info code =>
          -- the if's result = the BRANCH JOIN's type: the first alt in
          -- the CHAIN whose code RESOLVES (a bare `return` arm resolves
          -- to none — the join defers to a later alt's shape; the old
          -- first-alt-only read emitted i64 for a mixed join and
          -- mis-typed the nested-case else — userComplete's gate)
          let resTy := ((alt :: rest).filterMap resultTyOfAlt).head?.getD "i64"
          let thenI ← emitScoped code
          let elseI ← goAlts scrut rest
          pure ([.localget scrut, .i32const info.cidx, .op .i32eq]
            ++ [.if_ (some resTy) thenI elseI])
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
  | .lit (.nat _) => unsupported "Nat literal (GMP — banned in the guest)"
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
      match binop? fn, GuestlangStd.Intrinsic.ofName? fn with
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
          -- miscasts (the watchOrdersImpl._boxed lesson: the object-
          -- returning call stored into an i64 local = the core module
          -- INVALID — the `fused-adapter` mismatch was THIS, not a
          -- wit-component bug).
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
  layout: discr u32 @0, the record @8 (aligned 8 by the u64):
  id i64 @8, name (ptr,len) @16/20, email @24/28, tags (ptr,len)
  @32/36 — 40 bytes. The record's refs (name/email/tags) sit at
  @8/16/24, the id scalar at @32 (the LCNF's sset [3, 0]).
  The LIST<string> field: a cons-chain walk (two passes: count, then
  fill an 8n-byte array of (ptr,len) pairs) — nil = tag 0, cons = tag 1
  (head @8, tail @16).
- default: the scalar/object conventions (scalar → raw i64; object →
  unbox).
-/

/-- The ASYNC-marked exports (the wire names; the world marks them
    `async func` — the canon lift's async option + the [callback]). -/
  -- the ASYNC-lifted exports (the async gate). THE RECIPE (cracked via
  -- the minimal-module bisection against wasmparser 0.257's
  -- check_asyncness): (a) the WIT function must be declared `async func`
  -- (the component func type's async flag — the SYNC-marked fn = the
  -- `async canonical option requires an async function type` error);
  -- (b) the core module IMPORTS the task intrinsics: the per-fn
  -- `[export]$root`/`[export]<iface-key>` `[task-return]<fn>` (the flat
  -- results — the list = (ptr, len)) + `$root`'s [waitable-set-poll/new/
  -- drop], [waitable-join], [context-get-0/set-0] + `[export]$root`
  -- [task-cancel] (NO params); (c) the core exports: memory,
  -- __indirect_function_table, cabi_realloc, `[async-lift]<key>#<fn>`
  -- (the params = the flat form; the result = i32 = the task handle-ish
  -- 0) + `[callback][async-lift]<key>#<fn>` ((i32,i32,i32)->i32); (d)
  -- the callee DELIVERS results by CALLING task-return(flat-results)
  -- then returning 0 (the sync-computable body = done at the first
  -- poll; the callback = the constant Exit=0). The fused-adapter
  -- `type mismatch` seen earlier = the missing task-return import+call.
def asyncFns : List String := ["watch-orders", "watch-counts", "watch-users"]
  -- [async-lift] emission is LIVE: the callback + interface-qualified
  -- exports are emitted (verified against the wit-bindgen 0.61
  -- reference), and the callee delivers results by calling
  -- task-return(flat-results) then returning 0 — the task-return
  -- import+call is the piece the fused-adapter type mismatch was missing.

/-- The adapter result shape per export (kebab name). -/
def adapterShape? : String → Option String
  | "get-user" => some "optionUser"
  | "watch-orders" => some "listUser"
  | "watch-counts" => some "streamU64"
  | "watch-users" => some "streamUser"
  | "user-valid" => some "userParam"
  | "user-complete" => some "userParam"
  | "order-error-valid" => some "variantParam"
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
  -- the (ptr, len) stores: STATIC areaOff only (e.g. get-user's tags
  -- at 88/92). `areaOff = 0` means NO MEMORY WRITE: the callers who need
  -- the list's (ptr,len) read the walk's `$arr`/`$n` LOCALS (the stream
  -- stash, the per-element tags copy) — the old scratch write at the
  -- fill-end cursor CORRUPTED the next bump allocation (it landed on the
  -- first inner-walk array — element 1's tags became the outer walk's
  -- own (ptr,len) pair). Scratch writes to "unused" memory are not
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
fails `component new`). The caller's flat values are IN GUEST MEMORY
the same way the result-side flat forms are (the lower wrote (ptr,len)
pairs; the lift wrote (ptr,len) pairs) — the adapter INVERTS the
result-side lowering: strings = alloc(16+len) + {tag=250, len@8,
memory.copy bytes@16} (strElemLower's read form, constructed); the
tags list = the cons chain; the user = the refs-first guest object.

The flat param list for the user record — DERIVED from the field types
(the same `.u64/.string/.list` list Layout.offsets consumes): a u64
flattens to one i64; a string/list flattens to the (ptr, len) i32
pair. -/

def userFieldTys (_cert : WasmBackend.Layout.offsets WasmBackend.Layout.userTys = [0, 8, 16, 24]) : List SchemaLang.Ty :=
  WasmBackend.Layout.userTys

/-- One flat core type per canonical-ABI field flattening. -/
def flatTyOf : SchemaLang.Ty → List String
  | .u64 | .i64 => ["i64"]
  | .f64 => ["f64"]
  | .f32 => ["f32"]
  | .bool | .u8 | .u16 | .u32 | .i8 | .i16 | .i32 => ["i32"]
  | .string | .bytes | .list _ | .option _ | .result _ _ | .future _
  | .stream _ | .tensor _ _ | .ty _ => ["i32", "i32"]

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
  -- STRING result: the post-return convention — the core signature takes
  -- the return-area pointer as its LAST param; the adapter calls the impl
  -- (→ the string object), then writes (bytes-ptr, byte-len) into it.
  -- The host's canonical lift reads the UTF-8 from the bytes-ptr. The
  -- guest string's bytes live INLINE at +16 (see the intrinsics layout).
  -- (The STRING-ness comes from the ORIGINAL def type — GenMain looks it
  -- up in the imported env — the LCNF type is erased to `obj` for every
  -- object result, Shape and String alike.)
  if shape == "string" then
    -- the shim: pass the flat args through, call the impl, write the
    -- canonical-ABI string flattening (bytes-ptr, byte-len) into a STATIC
    -- return area, return the area pointer — the embedder's convention
    -- (`[I64] -> [I32]`: MAX_FLAT_RESULTS=1 — an oversized result flattens
    -- to a single i32 pointer to the results tuple; the caller copies out
    -- of OUR memory via the canon-lift memory option). The area is the
    -- fixed scratch slot at 48 (the freelist owns 0..24, the heap starts
    -- at 64; 24..64 is dead space — single-threaded, no clobber). The
    -- guest string's bytes live INLINE at +16, so bytes-ptr = obj + 16.
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
    -- option's MEMORY representation (packed, aligned — wasmtime's
    -- lift reads the area as the type's memory layout): discr u32 @56,
    -- the record @64 (aligned 8 by the u64): id @64, name (ptr,len)
    -- @72/76, email @80/84, tags (ptr,len) @88/92. The guest User
    -- object: refs @8/16/24 (name/email/tags), the id scalar @32
    -- (sset [3, 0]).
    -- The tags list<string>: the cons-chain walk (listWalk) fills an
    -- 8n-byte array of (ptr,len) pairs. The option's ctor tags:
    -- none = 0, some = 1 (Lean's ctor order); the payload rides @8.
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
      -- [len]) — ONE more indirection than greet (whose result WAS the
      -- string object)
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
    -- max of the cases' flat types: invalid-item's [i64] (u64) and
    -- insufficient-funds' [f64] join to i64 — the SAME flat form the
    -- listUser adapter's variantBox consumes for watch-orders). The
    -- RE-BOX: alloc(16) {rc, tag=discr @4, payload i64 @8} → the
    -- guest's variant object. The SYNC bool result: the impl's Bool =
    -- raw i32 (the userParam convention) — no return area.
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
    -- list<user> lowering (the ASYNC watch-orders' result): the impl
    -- returns the List-User cons chain; the outer walk lowers EACH
    -- user into a 32-byte flat record (id i64 @0; name (ptr,len) @8/12;
    -- email @16/20; tags (ptr,len) @24/28 — the tags = a NESTED
    -- string-list walk (the inner walk's dst = the enclosing record's
    -- cursor + 24 — the EMBEDDED mode)). The return area (56..64) =
    -- the list's own (ptr, len).
    --
    -- The VARIANT param: the canonical ABI flattens a variant = the
    -- discr + the max payload ([i32, i64] for the order-error) — the
    -- encoder VALIDATES the async export's core sig against the FLAT
    -- form. The adapter RE-BOXES: alloc(16) {rc, tag=discr, payload
    -- i64@8} -> the guest's variant object.
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
    -- STREAM lowering (the ASYNC watch-counts/watch-users): stream.new
    -- → the i64 handle PAIR ((write << 32) | read — wasmtime's
    -- libcalls.rs ResourcePair packing); the List walk lowers each
    -- element into a contiguous item array (the u64: the cons head = a
    -- BOX ptr @cur+8, the value @box+8 → 8 bytes; the user: the
    -- 32-byte flat record — the NESTED tags walk embedded); the
    -- stream.write = the ASYNC-lowered name (the sync form = the
    -- more-async-builtins feature, not enabled). THE DELIVERY DANCE:
    -- the abi fn = task-return(read) + stash (wr, arr, n) in the
    -- GLOBALS + return 1 (YIELD — the abi fn's result = the callback
    -- code; 0 = Exit tears the task down and the in-flight write's
    -- items are LOST); the HOST registers the consumer post-call (the
    -- stream = the returned result); the writer's resumption event
    -- fires the CALLBACK = the WRITE SITE: write into the waiting
    -- consumer, then Exit.
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
  -- (The `sigs` fold ran once above — decl signatures are immutable
  -- across the module — the trampoline loop reads that same table.)
  -- The FRESH count = the target's arity − nA; every arg (captured or
  -- fresh) is a boxed object; the target's param types decide unbox-vs-
  -- forward; a raw i64 result gets boxed.
  let mut trampFuncs : List Wat.Func := []
  let mut elem : List String := []
  for (fn, nA) in dedupTramps st.tramps.toList do
    let name := s!"pap_{fn.toString}_{nA}"
    let (paramTys, resTy) := sigs[fn]?.getD (#[], "i32")
    let nFresh := paramTys.size - nA
    let boxed := fn.toString.endsWith "_boxed" || fn.toString.endsWith "_closed"
    let mut body : List Wat.Instr := []
    let mut off := 16
    if boxed then
      -- boxed target: forward every arg as-is (objects in, object out)
      for _ in [0:nA] do
        body := body ++ [ .localget "c", .mem .i32load off none ]
        off := off + 8
      for i in [0:nFresh] do
        body := body ++ [ .localget s!"x{i}" ]
      body := body ++ [ .call fn.toString ]
    else
      -- raw scalar target: unbox captured + fresh args, call, box result
      for _i in [0:nA] do
        body := body ++ [ .localget "c", .mem .i32load off none, .mem .i64load 8 none ]
        off := off + 8
      for i in [0:nFresh] do
        body := body ++ [ .localget s!"x{i}", .mem .i64load 8 none ]
      body := body ++ [ .call fn.toString, .localset "r", .i32const 16
        , .call "alloc", .localtee "p", .localget "r", .mem .i64store 8 none
        , .localget "p" ]
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
  -- return area (nothing to free — the leak-free-by-construction case)
  -- and `component new`'s encoder accepts the post-return's ABSENCE
  -- (emitting one with a wrong shape FAILS the encode: the encoder
  -- validates cabi_post_* against the function's flat params — the
  -- empirically-discovered shape). Omit until the async work needs the
  -- real task dealloc.

  -- the ASYNC-lifted exports: the wit-bindgen 0.61 protocol — the main
  -- export (the SYNC convention: the params + the return-area result)
  -- + the [callback] companion (the canonical lift POLLS it:
  -- (i32 ordinal, i32 handle, i32 result) -> i32 CallbackCode; the
  -- codes: Exit=0/Yield=1). OUR compiled bodies are SYNC-computable —
  -- the task completes on the FIRST poll — the callback = the constant
  -- Exit. The async-ness = the canon-lift's option (the world's
  -- `async func` marking).
  let asyncTargets := exportTargets.filter fun (kebab, _) => asyncFns.contains kebab
  -- the ASYNC-lifted exports' CORE NAMES = the encoder's convention
  -- (dissected from the wit-bindgen 0.61 component): the main =
  -- `[async-lift]{name}` (the strip-prefix convention: the REMAINING
  -- name = matched against the world's export keys — the world-level
  -- key = the BARE kebab (the interface-qualified form = for the
  -- interface exports); the plain-name export is INVISIBLE to the
  -- async encoder), the callback = `[callback][async-lift]{name}`. The callback's sig =
  -- (i32 ordinal, i32 handle, i32 result) -> i32 (the CallbackCode:
  -- Exit=0); our sync-computable bodies = Exit on the first poll.
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
  -- the task intrinsics' imports (the async lift requires them — see
  -- the asyncFns' note); the names = the bare kebab (the world-level
  -- key) for both the task-return and the async-lift pair
  -- the waitables/context = ONCE (shared); the task-return + the
  -- stream intrinsics = PER async export, shaped by the adapter's
  -- RESULT: the list = (ptr, len) = (i32, i32); the stream = the READ
  -- handle = (i32) + the stream-new/write/drop-writable intrinsics
  -- (the write = the ASYNC-lowered name — the sync form needs the
  -- more-async-builtins feature). The stream TYPE index (0) = the
  -- payload's position in the fn's futures-and-streams list.
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

  -- the EXPORT-NAME map: the SCHEMA fns (get-user/watch-orders) live in
  -- the demo-exports INTERFACE -> the core export = the LEGACY mangling's
  -- `{interface-key}#{fn}` (the resolve's own-package key = the BARE
  -- "demo-exports" — the foreign-package references carry the full
  -- pkg:iface path); the world-level scalars = the bare kebab; the async
  -- ones = the [async-lift] prefix (see asyncFns).
  -- ALL exports = the world-level (the async = the [async-lift]-prefixed
  -- bare name; the interface-split = the wit-component 47's fused
  -- adapter mismatch — see the asyncFns' note + the plan doc's 1b).
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
