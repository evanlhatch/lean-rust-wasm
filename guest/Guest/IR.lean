/-
# Guest.IR — the frontend-agnostic intermediate (the pipeline's CONTRACT)

The guest stack's honest middle: the frontends are per-language
(guestlang-lean via LCNF, guestlang-edgepython via Python's AST, …),
and THIS module is what they all produce — the per-language front
halves share their machinery through the kit (`Guest.Frontend`: the
pipeline tail, the fold disciplines, the third-frontend checklist),
 the fragment the lowering
covers TODAY, reified as the IR's constructors (the ANF-flavored
discipline: one let spine, every value form resolved to a variable
reference, the scalar/box/object/closure/control rows exactly as
`Guest.Lower` consumes them). The IR is the CONTRACT: the frontends
produce it, the lowering consumes it — the lowering core imports
NOTHING language-specific.

The constructors' discipline (each is a lowering lane, read off
`Guest.Lower`'s LCNF consumption):

- **The scalar spine**: `let_`/`ret`/`unreach` — ANF lets over
  `LetValue`, the return through the function's result variable.
- **The value forms**: the scalar literals (`litU64`/`litU32`/`litU8`),
  the boxed-Nat literal (`litNat` — the bump-arena box), the copy
  (`copy`), the op-surface calls reified as rows (`natFap` — the
  boxed-Nat compare/arith rows; `binop` — the u64/u32/u8 machine-op
  rows, arity carried by the ctor), the cross-decl sibling call
  (`call`), the closure application (`apply` — the lowering decides
  pap-provenance vs first-class from its own state), the ctor
  (`ctor` — the cidx; the lowering picks the tag/object face from the
  result type's row), the closure allocation (`pap`), the field reads
  (`sproj`/`oproj`), the scalar-box lane (`box`/`unbox`), and the
  0-ary top-level constant (`const`).
- **The control forms**: `cases_` (the alt chain as a LIST; the
  scrutinee's dispatch lane `CaseVia` reifies the frontend's prescan
  verdict — the scalar lane branches on the VALUE, the object lane reads
  the tag byte @4), `jp`/`jmp` (the join points — the lowering owns the
  loop-vs-block shape dispatch), `inc`/`dec` (the RC discipline's real
  rc-cell arithmetic; `dec`'s `cascade` carries the field-cascade's
  REF-FIELD COUNT — the object's fields' refs decrement when the object
  dies, the count riding the landed layout: the ref slots are
  `0..count-1`), `del` (the honest deallocation: the ownership assertion
  `rc = 1` + the dead marking — the freelist reuse stays the named
  follow-up).
- **The in-place writes** (the mutation family): `sset` (a scalar field
  write — the SAME coordinates the `sproj` read rides), `oset` (a
  ref-field write), `setTag` (the tag byte's write) — each under the rc=1
  legality guard (a shared cell's in-place write is the loud runtime
  trap; the copy discipline is the named follow-up). The `uset` face (a
  USize slot write) stays OUTSIDE the IR — no modeled row — the
  frontend's named refusal.
- **The extern face**: `extern` — a DECLARED TRUST BOUNDARY: the decl
  carries its signature, its body is NOT modeled (the lowering emits the
  declared function with the `unreach` body — the host link step is the
  named follow-up); a call to it rides the call lane's index like any
  sibling.
- **The type rows** (`Ty`): the closed set the lowering's type map
  covered — the machine scalars (`u64`/`u32`/`u8`), the source
  scalars with the i32 repr (`bool`/`char`), the prescan's
  scalar-representable enums (`enum`), and the object rows riding the
  ONE pointer repr (`nat`/`tobj`/`tagged`/`obj` — the lowering's
  boxed-Nat lane + the object/closure discipline). Every row renders
  back to the name the diagnostics spell (`Ty.render`).
- **The refusal envelope** (`Guest.LowerError`, shared with the
  lowering): the closed-world vocabulary BOTH ends of the contract
  throw — the frontend for the LCNF forms the IR cannot express, the
  lowering for the IR values the wasm model refuses. One envelope, the
  GC-family E-codes, the ONE `Kit.Diag` (05 §4).

The five questions (notes/v3/01-core.md):

- **Root**: Universe (the IR is finite closed data — the fragment's
  constructors).
- **Carrier grade**: none — plain data; the refusals ride `Kit.Diag`.
- **Spine reading**: the `Code` spine is what the lowering folds (one
  traversal, the frame-depth parameter); the frontends PRODUCE it.
- **Ladder rung**: rung 1 (closed data; every non-fragment input
  refuses — at the frontend when reading, at the lowering when
  lowering).
- **Gate row**: `gates kernel-check` + lintkit's gated roots.

Consumer trail: `Guest.Frontend` (the shared frontend kit — the
per-language front halves' common machinery), `Guest.Lcnf` (the LCNF
frontend — the reading face), `Guest.Lower` (the lowering's ONLY
input), the toy frontend (GuestTests' hand-written IR — the
conformance evidence that the IR alone is the whole contract).
-/

import Kit.Diag

namespace Guest

/-! ## The refusal vocabulary (the envelope discipline, 05 §4) -/

/-- THE closed-world refusal vocabulary: the pipeline's failure KINDS
    as ctors with their payload data. Shared by the frontends (the
    LCNF forms the IR cannot express) and the lowering (the IR values
    the wasm model refuses). Closed on purpose: a new fragment region
    is a new ctor, and the compiler drives the extension (15-patterns
    #15). -/
inductive LowerError where
  /-- A Lean type outside the scalar fragment (`what` names the
      position, `ty` the Lean type's rendering). -/
  | typeOutsideFragment (what : String) (ty : String)
  /-- THE bounded-Nat cap: a `Nat` literal at/above 2^62 is a DESIGN
      ERROR (the boxed-Nat model's pinned refusal — the legacy
      discipline, ported verbatim). -/
  | natLitCap (v : Nat)
  /-- A below-cap `Nat` literal: the boxed-Nat lane is the named
      follow-up — refused, never silently scalarized. RETIRED: the
      boxed-Nat lane LANDED (the bump-arena allocation + the
      `{rc, tag, i64 payload}` layout). The ctor stays in the closed
      vocabulary — its E-code GC2003 is an allocated row of the
      registry's history, and a retired code is never reused — but
      the lowering never fires it again. -/
  | natLane (v : Nat)
  /-- THE BOXED-NAT MODEL's pinned throw: a ctor-case on a `Nat`
      scrutinee. The generic tag dispatch would read the box's tag 0
      and treat the payload as a POINTER — silently wrong — so such a
      case throws loudly (the legacy discipline). The real pipeline
      never produces one (Nat cases compile to decEq fap chains); the
      hand-built face can. -/
  | natCtorCase
  /-- A construct outside the fragment (`what` = the source/IR form,
      `detail` = the named boundary it sits behind). -/
  | unsupportedConstruct (what : String) (detail : String)
  /-- An fvar read with no binding (a pipeline-internal
      inconsistency — the IR is ANF; this names the bug, never
      fabricates an index). -/
  | unboundFVar (name : String)
  /-- A non-fvar argument where ANF demands an fvar. -/
  | argShape (what : String)
  /-- A returned fvar's bound type does not match the result local's
      type. -/
  | armTypeMismatch (expected got : String)
  /-- A `jmp` whose target jp has no live registration (the jp's
      structure already ended, or there is no jp). -/
  | jpUnregistered (name : String)
  /-- A `jmp` whose arg count differs from the jp's param count. -/
  | jpArityDrift (jp : String) (got want : Nat)
  /-- The loop-entry discipline: a self-jumping jp whose continuation
      is not a straight-line let spine ending in the entry `jmp`. -/
  | loopEntry (detail : String)
  /-- RETIRED: the cross-decl call lane LANDED (the sibling `fap`
      lowers to `call` at the function-table index). The ctor stays in
      the closed vocabulary — its E-code GC2011 is an allocated row of
      the registry's history, and a retired code is never reused —
      but the lowering never fires it again. -/
  | declCall (fn : String)
  /-- A `pap` whose callee is not a SIBLING decl of the module — never
      a fabricated function index. -/
  | papUnknownFn (fn : String)
  /-- A `pap` whose captured-arg count is not below the callee's arity
      (a full application arrives as `fap`, an over-application is a
      drift). -/
  | papArityDrift (fn : String) (got want : Nat)
  /-- A NON-CLOSURE value applied first-class (the applied fvar's row
      is not a closure-pointer row — a scalar/boxed-scalar fvar has no
      fnIdx slot to dispatch through). The first-class lane LANDED
      (closure values lower to `callindirect`); this refusal is the
      lane's HONESTY face. -/
  | closureApplyUnknown (name : String)
  /-- A closure application whose captured + fresh count differs from
      the callee's arity. -/
  | closureApplyArityDrift (fn : String) (got want : Nat)
  /-- An `inc`/`dec` on a scalar-repr fvar (Perceus only RCs objects;
      this is a pipeline-internal inconsistency). -/
  | rcOnScalar (op : String)
  /-- RETIRED: the field-cascade dec LANDED (the ref fields' decs ride
      the landed layout, the count reified in `Code.dec`'s `cascade`).
      The ctor stays in the closed vocabulary — its E-code GC2021 is an
      allocated row of the registry's history, and a retired code is
      never reused — but the lowering never fires it again. -/
  | rcCascade
  /-- A ctor field whose pipeline layout class is outside the
      fragment's classification (an enum/Char-typed field — the
      pipeline's u8/u16/u32 enum repr depends on the ctor count, which
      is unknowable from the lowering's data; a non-const type). The
      field-packing law needs the field's size class. -/
  | ctorFieldClass (ty : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-! The E-code CONSTANTS (the GC family): one place, ready for the
persisted registry (the WV-family precedent — the registry's stable
allocation is a later integration step; the in-file numbering is
monotone — a retired ctor's code is never reused). -/
namespace LowerError

def ecTypeOutsideFragment : Kit.ECode := ⟨"GC2001"⟩
def ecNatLitCap : Kit.ECode := ⟨"GC2002"⟩
def ecNatLane : Kit.ECode := ⟨"GC2003"⟩
def ecUnsupported : Kit.ECode := ⟨"GC2004"⟩
def ecUnboundFVar : Kit.ECode := ⟨"GC2005"⟩
def ecArgShape : Kit.ECode := ⟨"GC2006"⟩
def ecArmTypeMismatch : Kit.ECode := ⟨"GC2007"⟩
def ecJpUnregistered : Kit.ECode := ⟨"GC2008"⟩
def ecJpArityDrift : Kit.ECode := ⟨"GC2009"⟩
def ecLoopEntry : Kit.ECode := ⟨"GC2010"⟩
def ecDeclCall : Kit.ECode := ⟨"GC2011"⟩
def ecNatCtorCase : Kit.ECode := ⟨"GC2012"⟩
def ecPapUnknownFn : Kit.ECode := ⟨"GC2016"⟩
def ecPapArityDrift : Kit.ECode := ⟨"GC2017"⟩
def ecClosureApplyUnknown : Kit.ECode := ⟨"GC2018"⟩
def ecClosureApplyArityDrift : Kit.ECode := ⟨"GC2019"⟩
def ecRcOnScalar : Kit.ECode := ⟨"GC2020"⟩
def ecRcCascade : Kit.ECode := ⟨"GC2021"⟩
def ecCtorFieldClass : Kit.ECode := ⟨"GC2022"⟩

end LowerError

/-- THE diagnostic envelope: every refusal renders into the ONE Diag —
    the GC-family E-code, the payload data in `got`, the named
    boundary in the valid-space slot (the did-you-mean engine fills
    the suggestion face). -/
def LowerError.toDiag : LowerError → Kit.Diag
  | .typeOutsideFragment what ty =>
      Kit.Diag.closedWorld ecTypeOutsideFragment
        s!"{what} is outside the scalar fragment"
        .error ty
        ["UInt64 (i64)", "UInt32/UInt8/Bool/Char (i32)",
         "a scalar-representable enum (the tag discipline)"]
  | .natLitCap v =>
      Kit.Diag.closedWorld ecNatLitCap
        s!"bounded-Nat: literal {v} at/above the pinned cap 2^62 — a design \
           error (the boxed-Nat model refuses overflow by construction)"
        .error (toString v)
        ["a Nat literal below 2^62"]
  | .natLane _v =>
      Kit.Diag.closedWorld ecNatLane
        "bounded-Nat: the boxed-Nat lane is not landed (RETIRED — the \
         lane landed; this ctor is never fired again)"
        .error (toString _v)
        ["the boxed-Nat lane"]
  | .natCtorCase =>
      Kit.Diag.closedWorld ecNatCtorCase
        "ctor-case on a Nat scrutinee — the boxed-Nat model refuses: the \
         generic tag dispatch would read the box's tag 0 and treat the \
         payload as a pointer (silently wrong)"
        .error "Nat"
        ["Nat cases compile to decEq fap chains (the pipeline's shape)"]
  | .unsupportedConstruct what detail =>
      Kit.Diag.closedWorld ecUnsupported
        s!"unsupported LCNF construct: {what}"
        .error what
        [detail]
  | .unboundFVar name =>
      { code := ecUnboundFVar
      , message := s!"unbound fvar {name} — a lowering-internal \
                      inconsistency (LCNF is ANF; this is a bug)"
      , got := some name }
  | .argShape what =>
      { code := ecArgShape
      , message := s!"non-fvar argument where ANF demands an fvar: {what}"
      , got := some what }
  | .armTypeMismatch expected got =>
      Kit.Diag.closedWorld ecArmTypeMismatch
        "returned value's type differs from the function result's type"
        .error got [expected]
  | .jpUnregistered name =>
      Kit.Diag.closedWorld ecJpUnregistered
        "jmp to a join point with no live registration — the jp's \
         structure already ended (a br cannot enter a frame)"
        .error name
        ["a jmp inside its jp's structure"]
  | .jpArityDrift _jp got want =>
      Kit.Diag.closedWorld ecJpArityDrift
        s!"jmp arity drift: {got} args vs the jp's {want} params"
        .error (toString got)
        [s!"{want} args"]
  | .loopEntry detail =>
      Kit.Diag.closedWorld ecLoopEntry
        s!"the loop-entry discipline: {detail}"
        .error detail
        ["a straight-line let spine ending in the entry jmp"]
  | .declCall fn =>
      Kit.Diag.closedWorld ecDeclCall
        "cross-decl call: the call lane is wasmcore's in-flight work — \
         the module's decls stay call-disjoint in this slice"
        .error fn
        ["the op-surface faps (binop?) only"]
  | .papUnknownFn fn =>
      Kit.Diag.closedWorld ecPapUnknownFn
        "pap: the callee is not a sibling decl of the module — never a \
         fabricated function index"
        .error fn
        ["a pap naming a decl in the lowered set"]
  | .papArityDrift fn got want =>
      Kit.Diag.closedWorld ecPapArityDrift
        s!"pap arity drift on {fn}: {got} captured args vs the callee's \
           arity {want} (a full application arrives as fap, an \
           over-application is a drift)"
        .error (toString got)
        [s!"fewer than {want} captured args"]
  | .closureApplyUnknown name =>
      Kit.Diag.closedWorld ecClosureApplyUnknown
        s!"first-class closure application: {name} is not a closure value \
           (its row is not a closure-pointer row — no fnIdx to dispatch \
           through)"
        .error name
        ["a closure value (the pipeline's tobj/obj rows — the fnIdx @8 \
          is the table index)"]
  | .closureApplyArityDrift fn got want =>
      Kit.Diag.closedWorld ecClosureApplyArityDrift
        s!"closure application arity drift on {fn}: {got} (captured + \
           fresh) vs the callee's arity {want}"
        .error (toString got)
        [s!"{want} total args"]
  | .rcOnScalar op =>
      Kit.Diag.closedWorld ecRcOnScalar
        s!"Perceus RC ({op}) on a scalar-repr fvar — Perceus only RCs \
           objects (a lowering-internal inconsistency)"
        .error op
        ["an object-repr (i32) fvar"]
  | .rcCascade =>
      Kit.Diag.closedWorld ecRcCascade
        "Perceus RC: the field-cascade dec (RETIRED — the cascade landed;
         this ctor is never fired again)"
        .error "dec (cascade)"
        ["a dec of an object with no ref fields"]
  | .ctorFieldClass ty =>
      Kit.Diag.closedWorld ecCtorFieldClass
        "ctor field outside the layout's size classes — the pipeline's \
         packing law (refs first, then scalars by size) needs the \
         field's size class, and an enum/Char repr's class depends on \
         the ctor count (unknowable from the lowering's data)"
        .error ty
        ["a field of UInt64/UInt32/UInt8 or an object-row type"]

/-- The one-line rendering (the envelope's `.toString`). -/
def LowerError.render (e : LowerError) : String := Kit.Diag.toString e.toDiag

/-! ## The IR's data (the contract's constructors) -/

namespace IR

/-- The IR's variable: the frontend's binding identity (the LCNF
    fvar's rendered name — unique within a decl; the diagnostics and
    the jp/pap registries key on it). -/
abbrev Var := String

/-- THE TYPE ROWS (the closed set the lowering's type map covered):
    the machine scalars (`u64`/`u32`/`u8`), the source scalars with
    the i32 repr (`bool`/`char`), the prescan's scalar-representable
    enums (`enum name`), and the object rows riding the ONE pointer
    repr (`nat`/`tobj`/`tagged`/`obj`). -/
inductive Ty where
  | u64 | u32 | u8 | bool | char
  | enum (name : String)
  | nat | tobj | tagged | obj
  deriving BEq, DecidableEq, Inhabited, Repr

/-- The row's rendering — the name the diagnostics spell (the Lean
    type's own name: `UInt64`, `Char`, the enum's name, the object
    rows' spellings). -/
def Ty.render : Ty → String
  | .u64 => "UInt64" | .u32 => "UInt32" | .u8 => "UInt8"
  | .bool => "Bool" | .char => "Char"
  | .enum name => name
  | .nat => "Nat" | .tobj => "tobj" | .tagged => "tagged" | .obj => "obj"

/-- The OBJECT ROWS (the boxed-Nat lane's + the object discipline's
    faces): everything riding the ONE pointer repr. -/
def Ty.isObjRow : Ty → Bool
  | .nat | .tobj | .tagged | .obj => true
  | _ => false

/-- The CLOSURE-POINTER rows (the first-class application's acceptance
    face): the pipeline's closure values ride `tobj`/`obj` (the
    probe-observed shapes). A scalar row (a UInt64 fvar applied) is
    the NON-CLOSURE refusal (`closureApplyUnknown`); `tagged`/`nat`
    (boxed scalars) refuse too — a boxed scalar applied is garbage the
    source type system prevents, and the model refuses what it cannot
    witness. -/
def Ty.isClosureRow : Ty → Bool
  | .tobj | .obj => true
  | _ => false

/-- The argument rows: a variable reference (ANF), the erased arg
    (pushes nothing — the pipeline's erased bindings), or a type
    argument (each lane names its own refusal). -/
inductive Arg where
  | var (v : Var)
  | erased
  | typeArg
  deriving BEq, DecidableEq, Inhabited, Repr

/-- THE BOXED-NAT FAP rows (the legacy's sanctioned surface; the
    probe-observed pipeline rows: `Nat.add`/`mul`/`sub`/`decLt`/
    `decEq`/`decLe` — `Nat.beq` joins the family for the hand-built
    face). All arity 2 over the boxes' payloads. -/
inductive NatFap where
  | decEq | beq | decLt | decLe | add | sub | mul
  deriving BEq, DecidableEq, Inhabited, Repr

/-- THE OP-SURFACE rows (the legacy `binop?`'s surface, reified): the
    `UInt64` add/sub/mul/decLt/decEq/shiftRight family, the `UInt32`
    lane, the `UInt8` lane (the arith rows carry the `and 0xFF` mask
    at the lowering), and the width conversions. The ARITY is carried
    by the ctor shape (`Binop.arity`). -/
inductive Binop where
  | u64add | u64sub | u64mul | u64ltu | u64eq | u64shru | u64wrap
  | u32add | u32sub | u32mul | u32and | u32xor | u32ltu | u32eq
  | u32shru | u32ext
  | u8add | u8sub | u8mul | u8and | u8xor | u8ltu | u8eq | u8shru
  | u8ext
  deriving BEq, DecidableEq, Inhabited, Repr

/-- The row's arity (the conversions are the 1-ary rows). -/
def Binop.arity : Binop → Nat
  | .u64wrap | .u32ext | .u8ext => 1
  | _ => 2

/-- The let-bound VALUE forms (the reified lanes; see the module
    header). -/
inductive LetValue where
  | litU64 (v : Nat)
  | litU32 (v : Nat)
  | litU8 (v : Nat)
  | litNat (v : Nat)
  | copy (v : Var)
  | natFap (k : NatFap) (args : Array Arg)
  | binop (op : Binop) (args : Array Arg)
  | call (fn : Var) (args : Array Arg)
  | apply (f : Var) (args : Array Arg)
  | ctor (cidx : Nat) (args : Array Arg)
  | pap (fn : Var) (args : Array Arg)
  | sproj (n : Nat) (offset : Nat) (v : Var)
  | oproj (i : Nat) (v : Var)
  | box (ty : Ty) (v : Var)
  | unbox (v : Var)
  | const (fn : Var) (args : Array Arg)
  deriving BEq, DecidableEq, Inhabited, Repr

/-- The ANF let binding: one variable, one type row, one value form. -/
structure LetDecl where
  var : Var
  ty : Ty
  value : LetValue
  deriving BEq, DecidableEq, Inhabited, Repr

/-- The scrutinee's dispatch lane (the frontend's prescan verdict
    reified): `value` — the SCALAR lane branches on the value itself
    (Bool/UInt8/the prescan's scalar-representable enums); `tag` — the
    OBJECT lane reads the tag byte @4 of the pointer repr. -/
inductive CaseVia where
  | value | tag
  deriving BEq, DecidableEq, Inhabited, Repr

-- One case node's per-alt arm: the ctor-index branch or the default
-- (the chain's else face). Mutual with `Code` (the alts' codes are
-- the spine's subterms — the structural recursion's face; no
-- well-founded measures needed anywhere over the IR).
mutual
inductive Alt where
  | ctorAlt (cidx : Nat) (code : Code)
  | default (code : Code)

/-- THE IR's code spine (the ANF let chain + the control forms). The
    ONE tree the lowering folds (one traversal, the frame-depth
    parameter) and every frontend produces. -/
inductive Code where
  | let_ (decl : LetDecl) (k : Code)
  | ret (v : Var)
  | unreach
  | cases_ (name : String) (via : CaseVia) (discr : Var) (alts : List Alt)
  | jp (name : Var) (params : List (Var × Ty)) (value : Code) (k : Code)
  | jmp (target : Var) (args : Array Arg)
  | inc (v : Var) (n : Nat) (k : Code)
  | dec (v : Var) (n : Nat) (cascade : Option Nat) (k : Code)
  | del (v : Var) (k : Code)
  -- THE IN-PLACE WRITES (the mutation family): the value-form writes
  -- are STATEMENTS (no result binding — the ANF spine's continuity).
  -- Each rides the rc=1 legality guard at the lowering (a shared
  -- cell's in-place write is the loud runtime trap).
  | sset (v : Var) (i : Nat) (offset : Nat) (val : Var) (ty : Ty) (k : Code)
  | oset (v : Var) (i : Nat) (val : Var) (k : Code)
  | setTag (v : Var) (cidx : Nat) (k : Code)
  -- THE EXTERN FACE: a declared trust boundary (a leaf — no body; the
  -- lowering emits the declared function with the `unreach` body, the
  -- host link step is the named follow-up).
  | extern
  deriving Inhabited, Repr
end

/-- The IR's decl: one function — the export name, the params (in
    order, the executor's param-i-to-local-i convention), the result
    row, the body. -/
structure Decl where
  name : String
  params : List (Var × Ty)
  resultTy : Ty
  value : Code
  deriving Inhabited, Repr

end IR

end Guest
