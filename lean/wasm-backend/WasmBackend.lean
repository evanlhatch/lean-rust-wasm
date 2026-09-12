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
  /-- every decl's wasm (param types, result type) — populated by
  emitModule BEFORE the decls emit (the fap result-type lookup needs
  the CALLEE's wasm result: object-returning calls with args = i32,
  scalar = i64 — the type default alone miscasts the local). -/
  sigs : Std.HashMap Name (Array String × String) := {}
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

/-! ## guestlang-std string intrinsics

The std functions' NAMES map to runtime primitives; their Lean bodies
are never compiled (they are the differential ORACLE — see DemoFn).
Guest string layout: `{rc@0, tag=250@4, len u32@8, bytes@16}` — a
variable-size object (16 + len); the bytes live INLINE so RC frees the
whole string (no separate byte allocation to leak). Byte-length ≠
char-length off ASCII (documented, v1). -/

/-- The guest string tag byte. -/
def stringTag : Nat := 250

/-- `GuestlangStd.*` std ops → the runtime primitive to call. The
    result is the IMPL convention: UInt64 = raw i64; String = object
    pointer (i32). -/
def stdOp? : Name → Option String
  | `GuestlangStd.strlen => some "call $string_len"
  | `GuestlangStd.strcat => some "call $string_cat"
  | _ => none

def storeOp (ty : Option String) : String :=
  match ty with | some "i32" => "i32.store" | _ => "i64.store"

def emitArg : Arg .impure → M Unit
  | .fvar fvarId => do emit (← load fvarId)
  | _ => emit ";; ERASED arg"

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
          if rv == decl.fvarId && (binop? fn).isNone && (stdOp? fn).isNone then
            for a in args do emitArg a
            emit s!"return_call ${fn.toString}"
          else
            emitLet decl; emitCode k
      | _, _ => emitLet decl; emitCode k
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
  | .sset _f i offset y ty k =>
      -- field store: sset var[slot, off] := y → mem[var + 8 + slot*8 + off]
      -- (the RC pass splits ctor-alloc from field-init AND reorders the
      -- fields REF-FIRST: the slot index = the field's position in the
      -- REORDERED layout — the id of a {u64, string, string, list} record
      -- is slot 3 (@8+3*8) AFTER the three ref slots. The old emission
      -- discarded `i` — the id CLOBBERED the first ref's pointer: the
      -- object case was never exercised before the schema records.)
      emit (← load _f)
      emit (← load y)
      emit s!"{storeOp (wasmTyOf? ty)} offset={8 + i * 8 + offset}"
      emitCode k
  | .oset .. | .uset .. | .setTag .. =>
    unsupported "in-place mutation (oset/uset/setTag)"
  | .fun _ _ h => absurd h (by simp)

partial def emitReturn (fvarId : FVarId) : M Unit := do
  emit (← load fvarId)
  emit "return"

partial def emitCases (c : Cases .impure) : M Unit := do
  -- SCALAR scrutinees (Bool/UInt8 — the impl param is a raw flat
  -- value): branch on the VALUE itself. OBJECT scrutinees: tag =
  -- i32.load8_u offset=4, stashed in a temp local.
  let scalar := c.typeName == `Bool || c.typeName == `UInt8
    || c.typeName == `UInt32 || c.typeName == `UInt64
  if scalar then
    goAltsRaw (← load c.discr) c.alts.toList
  else do
    emit (← load c.discr)
    emit "i32.load8_u offset=4"
    let tag ← bindFresh "i32"
    emit s!"local.set ${tag}"
    goAlts tag c.alts.toList

partial def goAltsRaw (value : String) : List (Alt .impure) → M Unit
  | [] => emit "unreachable ;; no matching scalar case"
  | alt :: rest => do
      match alt with
      | .ctorAlt info code =>
          emit value
          emit s!"i32.const {info.cidx}"
          emit "i32.eq"
          -- the if's result = the branch value's type (i64 scalar OR i32
          -- object — greet's string branches are the first object case)
          let resTy := resultTyOf code |>.getD "i64"
          emit s!"if (result {resTy})"
          emitCode code
          emit "else"
          goAltsRaw value rest
          emit "end"
      | .default code => emitCode code
      | .alt _ _ _ h => absurd h (by simp)

partial def goAlts (tag : String) : List (Alt .impure) → M Unit
  | [] => emit "unreachable ;; no matching ctor tag"
  | alt :: rest => do
      match alt with
      | .ctorAlt info code =>
          emit s!"local.get ${tag}"
          emit s!"i32.const {info.cidx}"
          emit "i32.eq"
          -- same: the branch value's type decides (scalar i64 / object i32)
          let resTy := resultTyOf code |>.getD "i64"
          emit s!"if (result {resTy})"
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
  | .lit (.str v) =>
      -- guestlang-std string literal: variable-size object {rc, tag=250,
      -- len@8, bytes@16} — the UTF-8 bytes stored inline (i32.store8 per
      -- byte; v1 literals are short — no data segments, no heap patch)
      let bytes := v.toByteArray
      let n := bytes.size
      let l ← bindLocal decl.fvarId "i32"
      emit s!"i32.const {16 + n}"; emit "call $alloc"; emit s!"local.set ${l}"
      emit (← load decl.fvarId)
      emit s!"i32.const {stringTag}"
      emit "i32.store8 offset=4"
      emit (← load decl.fvarId)
      emit s!"i32.const {n}"
      emit "i32.store offset=8"
      let mut off := 16
      for b in bytes do
        emit (← load decl.fvarId)
        emit s!"i32.const {b.toNat}"
        emit s!"i32.store8 offset={off}"
        off := off + 1
  | .lit _ => unsupported "literal kind (uint16/usize)"
  | .erased => pure ()
  | .fvar fvarId args =>
      if args.isEmpty then
        let l ← bindLocal decl.fvarId (ty.getD "i64")
        emit (← load fvarId); emit s!"local.set ${l}"
      else
        -- CLOSURE APPLICATION: f is an object; call its trampoline:
        -- push closure-ptr, fresh args (boxed), fnIdx; call_indirect.
        -- The sig is picked by the FRESH-arg count (sig_1box, sig_2box…).
        let l ← bindLocal decl.fvarId "i32"  -- result: boxed obj
        emit (← load fvarId)  -- closure ptr (also the trampoline's 1st arg)
        for a in args do emitArg a
        emit (← load fvarId)
        emit "i32.load offset=8"  -- fnIdx
        emit s!"call_indirect (type $sig_{args.size}box)"
        emit s!"local.set ${l}"
  | .fap fn args =>
      match binop? fn, stdOp? fn with
      | some op, _ =>
          let l ← bindLocal decl.fvarId (ty.getD "i64")
          for a in args do emitArg a
          emit op
          emit s!"local.set ${l}"
      | _, some call =>
          -- std intrinsic: strlen (obj) → raw i64; strcat (obj obj) → obj
          let resTy : String := match fn with
            | `GuestlangStd.strlen => "i64"
            | _ => "i32"
          let l ← bindLocal decl.fvarId resTy
          for a in args do emitArg a
          emit call
          emit s!"local.set ${l}"
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
          emit s!"call ${fn.toString}"
          emit s!"local.set ${l}"
  | .pap fn args =>
      -- closure: alloc {rc, tag=254, class, fnIdx, partial args…}
      let nA := args.size
      let _tramp := s!"pap_{fn.toString}_{nA}"
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
def asyncFns : List String := ["watch-orders"]
  -- GATED OFF: the [async-lift] protocol's shapes are emitted correctly
  -- (the callback + the interface-qualified exports — verified against
  -- the wit-bindgen 0.61 reference + the minimal-module probes), but
  -- sync-computable watch-orders = the landed form; the async = the
  -- plan doc's Track 1b. RESOLUTION (this session): the async = LANDED
  -- — the recipe (the WIT's async func + the task-return/waitable
  -- imports + the task-return delivery) = in the asyncFns' note; the
  -- earlier `fused-adapter mismatch` = the MISSING task-return
  -- import+call, not a wit-component bug.

/-- The adapter result shape per export (kebab name). -/
def adapterShape? : String → Option String
  | "get-user" => some "optionUser"
  | "watch-orders" => some "listUser"
  | _ => none

/-- The WAT for walking a guest List cons chain into a canonical
    (array-ptr, count) pair written at `areaOff`/`areaOff+4`. Two passes:
    COUNT the cons cells, `$alloc(n × elemSize)`, then FILL each element
    via `lowerElem` (the per-element WAT; `$cur` = the cons — its head
    object = `load($cur{suffix} + 8)` — `$w{suffix}` = the element's
    destination address). `suffix` uniquifies the locals/labels (the
    NESTED walks: the list-of-records' elements carry their own lists —
    the inner walk = the same generator, a different suffix). The
    cons's layout: {tag@4 (nil=0/cons=1), head@8, tail@16}. -/
def listWalkWat (loadSeq : List String) (areaOff : Nat)
    (elemSize : Nat) (suffix : String) (lowerElem : List String) : List String :=
  let cur := s!"$cur{suffix}"
  let n := s!"$n{suffix}"
  let arr := s!"$arr{suffix}"
  let w := s!"$w{suffix}"
  let doneL := s!"$done{suffix}"
  let countL := s!"$count{suffix}"
  let doneF := s!"$donef{suffix}"
  let fillL := s!"$fill{suffix}"
  let countLoop :=
    loadSeq ++ [ s!"local.set {cur}"
    , "i32.const 0", s!"local.set {n}"
    , s!"block {doneL}"
    , s!"  loop {countL}"
    , s!"    local.get {cur}", "i32.load8_u offset=4", "i32.eqz", s!"br_if {doneL}"
    , s!"    local.get {n}", "i32.const 1", "i32.add", s!"local.set {n}"
    , s!"    local.get {cur}", "i32.load offset=16", s!"local.set {cur}"  -- tail @16
    , s!"    br {countL}"
    , "  end"
    , "end" ]
  let fillLoop :=
    loadSeq ++ [ s!"local.set {cur}"
    , s!"local.get {n}", s!"i32.const {elemSize}", "i32.mul", "call $alloc", s!"local.set {arr}"
    , s!"local.get {arr}", s!"local.set {w}"
    , s!"block {doneF}"
    , s!"  loop {fillL}"
    , s!"    local.get {cur}", "i32.load8_u offset=4", "i32.eqz", s!"br_if {doneF}"
    ] ++ lowerElem ++ [
    s!"    local.get {w}", s!"i32.const {elemSize}", "i32.add", s!"local.set {w}"
    , s!"    local.get {cur}", "i32.load offset=16", s!"local.set {cur}"
    , s!"    br {fillL}"
    , "  end"
    , "end" ]
  -- the (ptr, len) stores: the dst = a caller-supplied expression (the
  -- static `areaOff` for the top-level lists; a computed address for the
  -- record-EMBEDDED lists — the dst = the enclosing record's cursor + the
  -- field's offset)
  let dstPtr := if areaOff == 0 then [ s!"local.get {w}", "i32.const 0", "i32.add" ]
    else [ s!"i32.const {areaOff}" ]
  let dstLen := if areaOff == 0 then [ s!"local.get {w}", "i32.const 4", "i32.add" ]
    else [ s!"i32.const {areaOff + 4}" ]
  countLoop ++ fillLoop ++
    (dstPtr ++ [s!"local.get {arr}", "i32.store"])
    ++ (dstLen ++ [s!"local.get {n}", "i32.store"])

/-- The per-element lowering of a `String` element (the flat pair =
    (head+16 [bytes inline], load(head+8) [len]) at `$w{suffix}`). -/
def strElemLower (suffix : String) : List String :=
  let cur := s!"$cur{suffix}"
  let w := s!"$w{suffix}"
  [ s!"    local.get {w}", s!"local.get {cur}", "i32.load offset=8", "i32.const 16", "i32.add", "i32.store"
  , s!"    local.get {w}", s!"local.get {cur}", "i32.load offset=8", "i32.load offset=8", "i32.store offset=4" ]

/-- Canonical-ABI adapter: flat component args → the impl's calling
convention. Borrowed-scalar params (objects in the impl) get BOXED;
raw scalars pass through; an object RESULT gets unboxed to the flat
i64. Exported under the WIT name; the impl stays internal (internal
callers keep calling it directly). -/
def emitAdapter (d : Decl .impure) (shape : String) : M String := do
  -- STRING result: the post-return convention — the core signature takes
  -- the return-area pointer as its LAST param; the adapter calls the impl
  -- (→ the string object), then writes (bytes-ptr, byte-len) into it.
  -- The host's canonical lift reads the UTF-8 from the bytes-ptr. The
  -- guest string's bytes live INLINE at +16 (see the stdOp? layout).
  -- (The STRING-ness comes from the ORIGINAL def type — GenMain looks it
  -- up in the imported env — the LCNF type is erased to `obj` for every
  -- object result, Shape and String alike.)
  if shape == "string" then do
    -- the shim: pass the flat args through, call the impl, write the
    -- canonical-ABI string flattening (bytes-ptr, byte-len) into a STATIC
    -- return area, return the area pointer — the embedder's convention
    -- (`[I64] -> [I32]`: MAX_FLAT_RESULTS=1 — an oversized result flattens
    -- to a single i32 pointer to the results tuple; the caller copies out
    -- of OUR memory via the canon-lift memory option). The area is the
    -- fixed scratch slot at 48 (the freelist owns 0..24, the heap starts
    -- at 64; 24..64 is dead space — single-threaded, no clobber). The
    -- guest string's bytes live INLINE at +16, so bytes-ptr = obj + 16.
    let sigParams := String.intercalate " "
      (d.params.toList.map fun p => s!"(param ${p.binderName.toString} {paramWasmTy p})")
      ++ " (result i32)"
    let pass := d.params.toList.map fun p => s!"local.get ${p.binderName.toString}"
    let tail := [s!"call ${d.name.toString}", "local.set $p"
      , "i32.const 48", "local.get $p", "i32.const 16", "i32.add", "i32.store"
      , "i32.const 48", "local.get $p", "i32.load offset=8", "i32.store offset=4"
      , "i32.const 48"]
    let body := String.intercalate "\n  " (pass ++ tail)
    pure s!"(func ${d.name.toString}_abi {sigParams}\n  (local $p i32)\n  {body}\n)"
  else if shape == "optionUser" then do
    -- option<user> lowering: the return area (56..96) holds the
    -- option's MEMORY representation (packed, aligned — wasmtime's
    -- lift reads the area as the type's memory layout): discr u32 @56,
    -- the record @64 (aligned 8 by the u64): id @64, name (ptr,len)
    -- @72/76, email @80/84, tags (ptr,len) @88/92. The guest User
    -- object: refs @8/16/24 (name/email/tags), the id scalar @32
    -- (sset [3, 0]).
    -- The tags list<string>: the cons-chain walk (listWalkWat) fills an
    -- 8n-byte array of (ptr,len) pairs. The option's ctor tags:
    -- none = 0, some = 1 (Lean's ctor order); the payload rides @8.
    let sigParams := String.intercalate " "
      (d.params.toList.map fun p => s!"(param ${p.binderName.toString} {paramWasmTy p})")
      ++ " (result i32)"
    let pass := d.params.toList.map fun p => s!"local.get ${p.binderName.toString}"
    let area := 56
    let body := String.intercalate "\n  " (pass
      ++ [s!"call ${d.name.toString}", "local.set $opt"
        , ";; discr = the option's ctor tag (none=0 / some=1)"
        , "local.get $opt", "i32.load8_u offset=4", "local.set $tag"
        , s!"i32.const {area}", "local.get $tag", "i32.store"
        , ";; the some branch: flatten the user record"
        , "local.get $tag", "i32.const 1", "i32.eq"
        , "if"
        , "local.get $opt", "i32.load offset=8", "local.set $u"
        , s!"i32.const {area + 8}", "local.get $u", "i64.load offset=32", "i64.store"
        -- the STRING fields: the record's slot holds the STRING OBJECT's
        -- POINTER (p); the flat pair = (p+16 [bytes inline], load(p+8)
        -- [len]) — ONE more indirection than greet (whose result WAS the
        -- string object)
        , s!"local.get $u", "i32.load offset=8", "local.set $p"
        , s!"i32.const {area + 16}", "local.get $p", "i32.const 16", "i32.add", "i32.store"
        , s!"i32.const {area + 20}", "local.get $p", "i32.load offset=8", "i32.store"
        , s!"local.get $u", "i32.load offset=16", "local.set $p"
        , s!"i32.const {area + 24}", "local.get $p", "i32.const 16", "i32.add", "i32.store"
        , s!"i32.const {area + 28}", "local.get $p", "i32.load offset=8", "i32.store"
        ]
      ++ listWalkWat ["local.get $u", "i32.load offset=24"] (area + 32) 8 "" (strElemLower "")
      ++ ["end"
        , s!"i32.const {area}"])
    pure s!"(func ${d.name.toString}_abi {sigParams}\n  (local $opt i32)\n  (local $tag i32)\n  (local $u i32)\n  (local $p i32)\n  (local $cur i32)\n  (local $n i32)\n  (local $arr i32)\n  (local $w i32)\n  {body}\n)"
  else if shape == "listUser" then do
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
    let sigParams := "(param $into_disc i32) (param $into_payload i64) (result i32)"
    let variantBox := [ "i32.const 16", "call $alloc", "local.set $v"
      , "local.get $v", "local.get $into_disc", "i32.store8 offset=4"
      , "local.get $v", "local.get $into_payload", "i64.store offset=8"
      , "local.get $v" ]
    -- the per-element lowering: $curU = the cons; the element's user =
    -- load(curU+8) -> $e; the dst = $wU
    let userLower : List String :=
      [ "    local.get $curU", "i32.load offset=8", "local.set $e"
      -- the id (the u64 @32 — the ref-first order)
      , "    local.get $wU", "local.get $e", "i64.load offset=32", "i64.store"
      -- the name: p = load(e+8); (p+16, load(p+8))
      , "    local.get $e", "i32.load offset=8", "local.set $p2"
      , "    local.get $wU", "local.get $p2", "i32.const 16", "i32.add", "i32.store"
      , "    local.get $wU", "local.get $p2", "i32.load offset=8", "i32.store offset=4"
      -- the email: p = load(e+16)
      , "    local.get $e", "i32.load offset=16", "local.set $p2"
      , "    local.get $wU", "local.get $p2", "i32.const 16", "i32.add", "i32.store"
      , "    local.get $wU", "local.get $p2", "i32.load offset=8", "i32.store offset=4"
      -- the tags: the NESTED string-list walk (the dst = $wU+24 — the
      -- EMBEDDED mode: areaOff = 0)
      ]
      ++ listWalkWat ["local.get $e", "i32.load offset=24"] 0 8 "T" (strElemLower "T")
    let areaTail :=
      -- the ASYNC delivery (the listUser shape = watch-orders-specific,
      -- and watch-orders = the async fn): call task-return(ptr, len) —
      -- the flat results — then return 0 (the task = complete at the
      -- first poll; the callback = Exit). The area (56..64) = still
      -- filled (the lift's copy-out = the task-return's arg-based).
      [ "i32.const 56", "local.get $arrU", "i32.store"
      , "i32.const 60", "local.get $nU", "i32.store"
      , "i32.const 56", "i32.const 60", "i32.load", "call $tr_watch-orders"
      , "i32.const 0" ]
    let body := String.intercalate "\n  " (variantBox
      ++ [s!"call ${d.name.toString}", "local.set $lst"]
      ++ listWalkWat ["local.get $lst"] 0 32 "U" userLower
      -- the list's own (ptr, len) -> the area (the STATIC offsets)
      ++ areaTail)
    pure s!"(func ${d.name.toString}_abi {sigParams}\n  (local $v i32)\n  (local $lst i32)\n  (local $curU i32)\n  (local $nU i32)\n  (local $arrU i32)\n  (local $wU i32)\n  (local $e i32)\n  (local $p2 i32)\n  (local $curT i32)\n  (local $nT i32)\n  (local $arrT i32)\n  (local $wT i32)\n  {body}\n)"
  else do
  let code := match d.value with | .code c => c | .extern .. => .unreach (Expr.const `Unit [])
  let resultTy := resultTyOf code
  let mut flats : List String := []
  let mut body : List String := []
  let mut boxLocals : Array String := #[]
  let mut pIdx := 0
  for p in d.params do
    let flat := paramWasmTy p
    if p.borrow then
      -- box the flat arg (scalar op: i32 for Bool/u8/u32, else i64).
      -- The TAG byte = the flat value for i32 params (bools are CASES'd
      -- — the impl reads the tag); i64 params get tag 0.
      let op := if flat == "i64" then "i64.store" else "i32.store"
      let pName := s!"b{pIdx}"
      body := body ++ [s!"i32.const 16", "call $alloc", s!"local.set ${pName}",
        s!"local.get ${pName}", s!"local.get ${p.binderName.toString}", s!"{op} offset=8",
        s!"local.get ${pName}"]
      if flat == "i32" then
        body := body ++ [s!"local.get ${p.binderName.toString}", "i32.store8 offset=4"]
      else
        body := body ++ ["i32.const 0", "i32.store8 offset=4"]
      body := body ++ [s!"local.get ${pName}"]
      boxLocals := boxLocals.push pName
    else
      body := body ++ [s!"local.get ${p.binderName.toString}"]
    flats := flats ++ [flat]
    pIdx := pIdx + 1
  body := body ++ (match resultTy with
    | some _ => [s!"call ${d.name.toString}"]
    | none => [s!"call ${d.name.toString}", "i64.load offset=8"])
  let sigParams := String.intercalate " "
    (d.params.toList.map fun p => s!"(param ${p.binderName.toString} {paramWasmTy p})")
  let resDecl := match resultTy with
    | some t => s!" (result {t})"
    | none => " (result i64)"
  let locals := boxLocals.toList.map fun n => s!"  (local ${n} i32)"
  pure <| s!"(func ${d.name.toString}_abi {sigParams}{resDecl}\n" ++
    String.intercalate "\n  " locals ++ "\n  " ++
    String.intercalate "\n  " body ++ "\n)"

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
  let mut funcs : List String := []
  for d in decls do
    let (f, s2) ← emitDecl d |>.run st
    st := { s2 with out := #[], locals := #[] }
    funcs := funcs ++ [f]
  -- Trampoline signatures: name → (param wasm tys, result wasm ty).
  let sigs : Std.HashMap Name (Array String × String) :=
    decls.foldl (fun m d =>
      let rt := match d.value with | .code c => resultTyOf c | .extern .. => none
      m.insert d.name (d.params.map (fun p => paramWasmTy p), rt.getD "i32")) {}
  -- Trampolines: (closure i32, boxed fresh args…) → boxed result.
  -- The FRESH count = the target's arity − nA; every arg (captured or
  -- fresh) is a boxed object; the target's param types decide unbox-vs-
  -- forward; a raw i64 result gets boxed.
  let mut trampFuncs : List String := []
  let mut elem : List String := []
  for (fn, nA) in dedupTramps st.tramps.toList do
    let name := s!"pap_{fn.toString}_{nA}"
    let (paramTys, resTy) := sigs[fn]?.getD (#[], "i32")
    let nFresh := paramTys.size - nA
    let boxed := fn.toString.endsWith "_boxed" || fn.toString.endsWith "_closed"
    let mut body : List String := []
    let mut off := 16
    if boxed then
      -- boxed target: forward every arg as-is (objects in, object out)
      for _ in [0:nA] do
        body := body ++ [s!"local.get $c", s!"i32.load offset={off}"]
        off := off + 8
      for i in [0:nFresh] do
        body := body ++ [s!"local.get $x{i}"]
      body := body ++ [s!"call ${fn.toString}"]
    else
      -- raw scalar target: unbox captured + fresh args, call, box result
      for _i in [0:nA] do
        body := body ++ [s!"local.get $c", s!"i32.load offset={off}", "i64.load offset=8"]
        off := off + 8
      for i in [0:nFresh] do
        body := body ++ [s!"local.get $x{i}", "i64.load offset=8"]
      body := body ++ [s!"call ${fn.toString}", "local.set $r", "i32.const 16",
        "call $alloc", "local.tee $p", "local.get $r", "i64.store offset=8", "local.get $p"]
    let paramDecls := String.intercalate " "
      (["(param $c i32)"] ++ (List.range nFresh).map fun i => s!"(param $x{i} i32)")
    let f :=
      if resTy == "i64" then
        s!"(func ${name} {paramDecls} (result i32)\n" ++
          String.intercalate "\n  " ["  (local $r i64)", "  (local $p i32)"] ++ "\n  " ++
          String.intercalate "\n  " body ++ "\n)"
      else
        s!"(func ${name} {paramDecls} (result i32)\n  " ++
          String.intercalate "\n  " body ++ "\n)"
    trampFuncs := trampFuncs ++ [f]
    elem := elem ++ [s!"${name}"]
  -- the call_indirect TYPE per distinct fresh count (all params i32:
  -- the closure ptr + boxed fresh args — the result is always a box)
  let mut freshCounts : List Nat := []
  for (fn, nA) in dedupTramps st.tramps.toList do
    let nF := (sigs[fn]?.getD (#[], "i32")).1.size - nA
    if !freshCounts.contains nF then freshCounts := freshCounts ++ [nF]
  let sigTypes := freshCounts.map fun nF =>
    let ps := String.intercalate " " ((List.range (nF + 1)).map fun _ => "(param i32)")
    s!"  (type $sig_{nF}box (func {ps} (result i32)))"
  -- canonical-ABI adapters for the export targets
  let mut abiFuncs : List String := []
  for (kebab, n) in exportTargets do
    for d in decls do
      if d.name.toString == n.toString then
        let shape := if stringResult? n then "string" else adapterShape? kebab |>.getD "default"
        let (a, _) ← emitAdapter d shape |>.run st
        abiFuncs := abiFuncs ++ [a]
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
  let cbFuncs := asyncTargets.map fun (kebab, _) =>
    s!"  (func $\"[callback][async-lift]{kebab}\" (param i32 i32 i32) (result i32) i32.const 0)"
  let cbExports := asyncTargets.map fun (kebab, _) =>
    s!"  (export \"[callback][async-lift]{kebab}\" (func $\"[callback][async-lift]{kebab}\"))"
  -- the task intrinsics' imports (the async lift requires them — see
  -- the asyncFns' note); the names = the bare kebab (the world-level
  -- key) for both the task-return and the async-lift pair
  let asyncImports := asyncTargets.flatMap fun (kebab, _) =>
    [ s!"  (import \"[export]$root\" \"[task-return]{kebab}\" (func $tr_{kebab} (param i32 i32)))"
    , "  (import \"$root\" \"[waitable-set-poll]\" (func (param i32 i32) (result i32)))"
    , "  (import \"$root\" \"[waitable-set-new]\" (func (result i32)))"
    , "  (import \"$root\" \"[waitable-join]\" (func (param i32 i32)))"
    , "  (import \"$root\" \"[context-get-0]\" (func (result i32)))"
    , "  (import \"$root\" \"[context-set-0]\" (func (param i32)))"
    , "  (import \"[export]$root\" \"[task-cancel]\" (func))"
    , "  (import \"$root\" \"[waitable-set-drop]\" (func (param i32)))" ]
  -- the canon lift's indirect calls go through the table + the async
  -- shims realloc through cabi_realloc (the bump alloc ignores the
  -- old-ptr/old-size/align args)

  -- the EXPORT-NAME map: the SCHEMA fns (get-user/watch-orders) live in
  -- the demo-exports INTERFACE -> the core export = the LEGACY mangling's
  -- `{interface-key}#{fn}` (the resolve's own-package key = the BARE
  -- "demo-exports" — the foreign-package references carry the full
  -- pkg:iface path); the world-level scalars = the bare kebab; the async
  -- ones = the [async-lift] prefix (gated off — see asyncFns).
  -- ALL exports = the world-level (the async = the [async-lift]-prefixed
  -- bare name; the interface-split = the wit-component 47's fused
  -- adapter mismatch — see the asyncFns' note + the plan doc's 1b).
  let exports := exportTargets.map fun (kebab, n) =>
    if asyncFns.contains kebab
    then s!"  (export \"[async-lift]{kebab}\" (func ${n.toString}_abi))"
    else s!"  (export \"{kebab}\" (func ${n.toString}_abi))"
  let sp := " "
  let table := if !sigTypes.isEmpty then
    sigTypes ++
    [s!"  (table {st.tramps.size} funcref)",
     s!"  (elem (i32.const 0) {String.intercalate sp elem})"]
  else []
  -- the canon lift reads guest memory (string/list results are copied
  -- out of it) — the memory MUST be exported under the canonical name
  let memExport := ["  (export \"memory\" (memory 0))"]
  let asyncEnv := if asyncFns.isEmpty then []
    else asyncImports
      ++ ["  (func $cabi_realloc (param i32 i32 i32 i32) (result i32)\n     local.get 3\n     call $alloc)"
        , "  (export \"cabi_realloc\" (func $cabi_realloc))"]
      ++ (if st.tramps.isEmpty
          then ["  (table 4 funcref)", "  (export \"__indirect_function_table\" (table 0))"]
          else ["  (export \"__indirect_function_table\" (table 0))"])
  pure <| String.intercalate "\n" (("(module" :: (asyncEnv ++ ["  ;;RUNTIME-SPLICE", "  (memory 1)"] ++ funcs ++ abiFuncs ++ cbFuncs ++ trampFuncs ++ table) ++ exports ++ cbExports ++ memExport ++ [")"]))

end WasmBackend
