/-
# Guest.Lower — the impure-phase LCNF → the ONE wasm AST

Ported from `legacy/lean/wasm-backend/WasmBackend.lean` (the emitter's
INTENT; the new tree's substrate differs honestly — index-keyed
locals, the closed `WasmCore.Instr`, the frame-DEPTH discipline in
place of the legacy's WAT labels, the op meanings in
`WasmCore.OpTable`):

- **The scalar type map** (the legacy `wasmTyOf?`): `UInt64 → i64`;
  `UInt32`/`UInt8`/`Bool`/`Char → i32`; a SCALAR-REPRESENTABLE ENUM
  (the tag discipline, below) `→ i32`; EVERYTHING ELSE refuses loudly
  — a type outside the fragment is a named diagnostic, never a silent
  `i32` pointer guess (the object model is not landed).
- **The tag discipline (the scalar-representable enums)**: a `cases`
  whose ctor alts are ALL payload-free (`CtorInfo.isScalar` —
  size/usize/ssize = 0) with every tag below 256 registers the
  scrutinee's TYPE NAME as scalar-representable (a prescan over the
  decl's OWN code — the observed evidence, no env threading): the
  enum's runtime repr is the unboxed ctor TAG, so the value branches
  like a `UInt8`. A payload ctor anywhere in the case keeps the type
  an OBJECT — refused (the boxed-object model).
- **The op surface** (the legacy `binop?`, grown): the `UInt64`
  add/sub/mul/decLt/decEq family, the shifts (`shiftRight`), the
  `UInt32` lane (add/sub/mul/land/xor/decLt/decEq/shiftRight), the
  `UInt8` lane (the arith rows carry the `and 0xFF` mask — i32
  arithmetic wraps mod 2^32, a `UInt8` wraps mod 2^8), the width
  conversions (`toUInt32`/`toUInt64`), all → `WasmCore.Op`'s ctors
  consumed from `WasmCore.OpTable`'s projections (the ONE table,
  07-extensibility R6). A fap outside the rows refuses loudly; a fap
  naming a SIBLING decl of the same module refuses as the CROSS-DECL
  CALL (the call lane is wasmcore's in-flight work — the named
  refusal).
- **The bounded-Nat boundary** (the legacy `emitLet`'s lit arm): a
  `Nat` literal at/above the pinned cap 2^62 is a DESIGN ERROR
  (refused with the cap diagnostic); below the cap it refuses with
  the not-yet-lowered diagnostic (the boxed-Nat lane is a named
  follow-up — this slice has no allocator).
- **The control flow** (the legacy `emitStep`'s jp/jmp + `buildAlts`,
  re-shaped for the frame-depth AST — the ONE AST's `br`/`brif` carry
  the frame DEPTH, not a label, so the lowering TRACKS the runtime
  frame depth `d` as its single walk parameter):
  - **The exit-frame discipline**: every `.return` stores the
    function's result local and branches `br (d-1)` — the outermost
    frame (emitted once per function around the whole body) absorbs
    the branch, and `localget res` after it hands the value to the
    run convention (the final stack). Values NEVER ride the stack
    across a branch (wasmcore's frames are no-result; a branch
    restores the frame-ENTRY stack) — every value crossing control
    rides a LOCAL.
  - **`cases`**: the alt chain folds to nested `if_`s keyed on the
    ctor index over the SCALAR-REPR scrutinee (branch on the VALUE,
    not a boxed tag); arm i of the chain lowers at depth `d+i` (each
    chain link is one `if_` frame). The case is TERMINAL in LCNF's
    impure spine (every arm ends return/jmp/unreach or a nested
    case) — no join local, no fallthrough value. A scrutinee/ctor
    outside the scalar discipline refuses loudly.
  - **`jp`/`jmp` (the join-point discipline)**: WAT has no goto; the
    legacy's block-and-fallthrough shape, in depths:
    ```
    block                    ;; $skip (outer)
      block                  ;; $jpL  (inner) — the gotos' target
        <k; a goto = arg stores + br into the jp>
        br 1                 ;; the fallthrough never reaches the body
      end
      <the jp body>          ;; a br to $jpL lands HERE
    end
    unreach                  ;; the seal (every k-path branched)
    ```
    The jmp's depth: the jp registers the offset `X = d_jp + 2` (the
    inner block sits two frames below the jp's own walk depth); a jmp
    at depth `d` emits `br (d - X)` — through any `if_` nesting, out
    of the inner block, into the body. The body is reached ONLY by a
    branch; control never falls past the seal.
  - **The loop shape (the growth beyond the legacy's conservative
    reject)**: a jp whose body jumps back to ITSELF (`jumpsTo` — the
    audit's loop-shaped-jp detection) cannot use the block shape (the
    body sits outside its own label's scope), but IT FITS the `loop`
    frame: the body inside `block [ loop [body; br 1] ]`, the
    self-goto = arg stores + `br (d - X)` restarting the loop (the
    loop frame absorbs `.branch 0` as the restart, carrying the
    branch-point locals — the stored args ride in). The ENTRY
    discipline: LCNF runs `k` FIRST, and a `br` cannot ENTER a frame,
    so `k` must be a straight-line let spine ending in the entry
    `jmp` (its arg stores fall through into the loop's first
    iteration); anything else refuses with the named `loopEntry`
    diagnostic (the entry-duplication transform is the named
    follow-up).
  - **The jmp scoping**: a jp's registration lives exactly as long as
    its structure's emission (deregistered after) — a jmp with no
    live registration (into a finished structure, or with no jp at
    all) refuses (`jpUnregistered`); an arity drift between the jmp's
    args and the jp's params refuses (`jpArityDrift`).
- **The multi-decl module**: `lowerFuncs` lowers SEVERAL decls into
  ONE module (one type + one function + one export each; the entry
  index = the decl order). The decls stay CALL-DISJOINT: a cross-decl
  `fap` is the named call-lane refusal until wasmcore's call support
  lands — never a fabricated index-0 call.
- **The refusal discipline** (05 §4's envelope): every refusal is a
  closed `LowerError` ctor rendered into the ONE `Kit.Diag` (the
  GC-family E-codes); never a bare string, never a silent wrong
  lowering.
- **The recursion is WELL-FOUNDED over explicit total measures** (the
  `codeSize`/`altSize`/`altSizes` block): the LCNF `Code.size` is
  `partial` — unusable for a termination proof, and a `partial`
  lowering is a stub lie. The size measures ride the derived
  `sizeOf` (the pair measure's lex-order facts `lt_left`/`lt_right`
  are proven once); the READER folds (the prescan, `jumpsTo`) and
  the LOWERING itself (`lowerCode`/`chainWalk`) are then well-founded
  over those measures — the decrease proofs are simp+omega over the
  measure equations, kernel-checked, core-triple axioms only.

THE FRAGMENT'S EXACT COVERAGE (the honest boundary, this slice):

- covered: straight-line `let` chains of scalar literals, scalar
  copies, the payload-free-ctor tag lets, and the `binop?` faps (both
  widths + the u8 mask + the shifts + the conversions); `return` of a
  scalar fvar; `cases` on a Bool/U8-repr OR scalar-repr-enum
  scrutinee, with NESTED cases in the arms; `jp`/`jmp` — the block
  shape (shared joins), the loop shape (tail-recursive joins, the
  entry discipline), multiple jps, jps under cases; the multi-decl
  module (call-disjoint decls); `unreach`.
- NOT covered (each lands with its named follow-up): the bounded-Nat
  boxed lane (alloc + the memory layout), object types/payload ctors/
  projections, closures (`pap`/closure application), the cross-decl
  call lane (wasmcore's in-flight work), loop-jp entries that are not
  a straight-line let spine (the entry-duplication transform),
  in-place mutation (`oset`/`uset`/`sset`/`setTag`), Perceus RC
  (`inc`/`dec`/`del`), `extern` decl values.

The five questions (notes/v3/01-core.md):

- **Root**: none — a lowering is a CROSSING (the LCNF decl read
  into the wasm module); its law face lands with the first
  correctness wave (the template pins are the tests' runtime face).
- **Carrier grade**: none new — the refusals ride `Kit.Diag` (the
  ONE envelope); the module output rides WasmCore's grades.
- **Spine reading**: the LCNF `Code` is the spine this module folds
  (one traversal, ONE parameter — the runtime frame depth `d`; the
  legacy `foldImpure` consolidation's discipline).
- **Ladder rung**: rung 1 (total folds over closed data; every
  non-fragment input refuses).
- **Gate row**: `gates kernel-check` + lintkit's gated roots.

Consumer trail: rides `Guest.Lcnf` (the input face), `WasmCore`
(the ONE AST + the op table + the module model), `Kit.Diag` (the
ONE envelope). Host-side (imports Lean via Guest.Lcnf).
-/

import Guest.Lcnf
import Kit.Diag
import WasmCore

namespace Guest

open Lean Compiler.LCNF

/-! ## The refusal vocabulary (the envelope discipline, 05 §4) -/

/-- THE closed-world refusal vocabulary: the lowering's failure KINDS
    as ctors with their payload data. Closed on purpose: a new
    fragment region is a new ctor, and the compiler drives the
    extension (15-patterns #15). -/
inductive LowerError where
  /-- A Lean type outside the scalar fragment (`what` names the
      position, `ty` the Lean type's rendering). -/
  | typeOutsideFragment (what : String) (ty : String)
  /-- THE bounded-Nat cap: a `Nat` literal at/above 2^62 is a DESIGN
      ERROR (the boxed-Nat model's pinned refusal — the legacy
      discipline, ported verbatim). -/
  | natLitCap (v : Nat)
  /-- A below-cap `Nat` literal: the boxed-Nat lane is the named
      follow-up — refused, never silently scalarized. -/
  | natLane (v : Nat)
  /-- A construct outside the fragment (`what` = the LCNF form,
      `detail` = the named boundary it sits behind). -/
  | unsupportedConstruct (what : String) (detail : String)
  /-- An fvar read with no binding (a lowering-internal
      inconsistency — LCNF is ANF; this names the bug, never
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
  /-- A fap naming a SIBLING decl of the same module: the cross-decl
      call lane (wasmcore's in-flight call support). -/
  | declCall (fn : String)
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
  | .natLane v =>
      Kit.Diag.closedWorld ecNatLane
        "bounded-Nat: the boxed-Nat lane (alloc + the memory layout) is not \
         landed in this slice — a Nat is an OBJECT, never a silent scalar"
        .error (toString v)
        ["the scalar fragment: UInt64/UInt32/UInt8/Bool/Char"]
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

/-- The one-line rendering (the envelope's `.toString`). -/
def LowerError.render (e : LowerError) : String := Kit.Diag.toString e.toDiag

/-! ## The scalar type map (the legacy `wasmTyOf?`) -/

/-- The BASE scalar names (the legacy `wasmTyOf?`'s rows). -/
def scalarTyOf? (c : Lean.Name) : Option WasmCore.ValType :=
  if c == `UInt64 then some .i64
  else if c == `UInt32 || c == `UInt8 || c == `Bool || c == `Char then some .i32
  else none

/-- The Lean type expression → the wasm scalar type. `enums` = the
    decl's scalar-representable enum registry (the prescan's observed
    evidence — `collectScalarEnums`); `none` = outside the fragment
    (the object model is not landed — the caller refuses with the
    named diagnostic). -/
def wasmTyOf? (enums : Std.HashMap Lean.Name Unit) : Lean.Expr → Option WasmCore.ValType
  | .const c _ =>
    match scalarTyOf? c with
    | some t => some t
    | none => if enums.contains c then some .i32 else none
  | _ => none

/-! ## The size measures (the well-founded substrate) -/

/-- The pair measure's LEFT fact (the lex order's first component). -/
theorem lt_left {p q : Nat × Nat} (h : p.1 < q.1) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) p q := by
  cases p with
  | mk p₁ p₂ =>
    cases q with
    | mk q₁ q₂ =>
      exact Prod.Lex.left (ra := fun a₁ a₂ => a₁ < a₂) (rb := fun a₁ a₂ => a₁ < a₂) p₂ q₂ h

/-- The pair measure's RIGHT fact (equal heads, decreasing tails). -/
theorem lt_right {p q : Nat × Nat} (heq : p.1 = q.1) (h : p.2 < q.2) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) p q := by
  cases p with
  | mk p₁ p₂ =>
    cases q with
    | mk q₁ q₂ =>
      subst heq
      exact Prod.Lex.right (ra := fun a₁ a₂ => a₁ < a₂) (rb := fun a₁ a₂ => a₁ < a₂)
        (b₁ := p₂) (b₂ := q₂) p₁ h

-- THE size measure over the LCNF `Code` (total, unlike the
-- toolchain's `partial` `Code.size`). The `FunDecl`/`Cases` hops
-- (the nested structures the derived sizeOf cannot see through on a
-- variable) are the two lemmas below, proven BEFORE the group.
theorem fd_sizeOf (fd : FunDecl .impure) : sizeOf fd.value < sizeOf fd := by
  cases fd with
  | mk _ _ _ _ v => simp [FunDecl.value]; omega
theorem cases_sizeOf (c : Cases .impure) : sizeOf c.alts < sizeOf c := by
  cases c with
  | mk _ _ _ alts => simp [Cases.alts]; omega

mutual
def codeSize : Code .impure → Nat
  | .let _ k => 1 + codeSize k
  | .jp fd k => 1 + codeSize fd.value + codeSize k
  | .cases c => 1 + altSizes c.alts 0
  | .return _ | .jmp .. | .unreach _ | .fun .. => 1
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ => 1 + codeSize k
  termination_by c => (sizeOf c, 0)
  decreasing_by
    all_goals (try have hfd := fd_sizeOf fd)
    all_goals (try have hcs := cases_sizeOf c)
    all_goals (first
      | exact lt_left (by simp <;> omega)
      | exact lt_right (rfl) (by omega))
def altSize : Alt .impure → Nat
  | .ctorAlt _ code => 1 + codeSize code
  | .default code => 1 + codeSize code
  | .alt _ _ _ _ => 0
  termination_by a => (sizeOf a, 0)
  decreasing_by
    all_goals exact lt_left (by simp <;> omega)
/-- The suffix sum of the arm sizes from index `i` (the chain walk's
    measure: the index step AND the chain→walk cross-call both
    decrease it). -/
def altSizes (alts : Array (Alt .impure)) (i : Nat) : Nat :=
  if h : i < alts.size then altSize alts[i] + altSizes alts (i + 1) else 0
  termination_by (sizeOf alts, alts.size - i)
  decreasing_by
    all_goals (first
      | exact lt_left (p := (sizeOf alts[i], 0))
          (q := (sizeOf alts, alts.size - i)) (by simp)
      | exact lt_right (p := (sizeOf alts, alts.size - (i + 1)))
          (q := (sizeOf alts, alts.size - i)) (rfl) (by omega))
end

theorem altSize_pos (a : Alt .impure) : 1 ≤ altSize a := by
  cases a with
  | ctorAlt info code => simp [altSize]
  | default code => simp [altSize]
  | alt _ _ _ h => exact absurd h (by simp)

/-- The chain walk's index step decreases the suffix measure. -/
theorem altSizes_suffix (alts : Array (Alt .impure)) (i : Nat) (h : i < alts.size) :
    altSizes alts (i + 1) < altSizes alts i := by
  have h1 : altSizes alts i = altSize alts[i] + altSizes alts (i + 1) := by
    rw [altSizes]; simp [h]
  have h2 := altSize_pos alts[i]
  omega

/-- The chain walk's ARM call decreases the suffix measure (the ctor
    arm's code is a summand). -/
theorem altSizes_gt_ctor (alts : Array (Alt .impure)) (i : Nat) (h : i < alts.size)
    (info : CtorInfo) (code : Code .impure) (hget : alts[i] = Alt.ctorAlt info code) :
    codeSize code < altSizes alts i := by
  have h1 : altSizes alts i = altSize alts[i] + altSizes alts (i + 1) := by
    rw [altSizes]; simp [h]
  rw [h1, hget]
  have h2 : altSize (Alt.ctorAlt info code) = 1 + codeSize code := by rw [altSize]
  rw [h2]; omega

/-- The chain walk's DEFAULT-arm call (the same shape). -/
theorem altSizes_gt_default (alts : Array (Alt .impure)) (i : Nat) (h : i < alts.size)
    (code : Code .impure) (hget : alts[i] = Alt.default code) :
    codeSize code < altSizes alts i := by
  have h1 : altSizes alts i = altSize alts[i] + altSizes alts (i + 1) := by
    rw [altSizes]; simp [h]
  rw [h1, hget]
  have h2 : altSize (Alt.default code) = 1 + codeSize code := by rw [altSize]
  rw [h2]; omega

/-! ## The tag prescan (the scalar-representable enums) -/

/-- The scalar-enum registration criterion: at least one ctor alt, and
    EVERY ctor alt is payload-free (`CtorInfo.isScalar`) with its tag
    below 256 (the unboxed-tag repr boundary). -/
def altsScalarRepr? (alts : List (Alt .impure)) : Bool :=
  let ctorAlts := alts.filterMap
    (fun a => match a with | .ctorAlt info _ => some info | _ => none)
  ctorAlts.length > 0
    && ctorAlts.all (fun i => i.isScalar && i.cidx < 256)

/-- The registry union (insertMany over the toList). -/
def enumUnion (m1 m2 : Std.HashMap Lean.Name Unit) : Std.HashMap Lean.Name Unit :=
  m1.insertMany m2.toList

/-- The alt-list's size (the list walkers' measure — structural over
    the list, so it needs no well-founded machinery of its own). -/
def listAltSize : List (Alt .impure) → Nat
  | [] => 0
  | a :: rest => altSize a + listAltSize rest

/-! The prescan: the decl's code → the scalar-representable enum
registry (the type names whose OBSERVED cases are all payload-free
ctor alts). Purely structural; the registry feeds `wasmTyOf?` (the
tag discipline — a scalar enum's repr IS the unboxed ctor tag).
NOTE the field orders the patterns spell: a `uset` carries
`y : FVarId` third and a `del` the fvar FIRST — the or-pattern's `k`
binds the CODE field in every arm. -/
mutual
def collectScalarEnums (code : Code .impure) : Std.HashMap Lean.Name Unit :=
  match code with
  | .let _ k => collectScalarEnums k
  | .jp fd k => enumUnion (collectScalarEnums fd.value) (collectScalarEnums k)
  | .cases c =>
    let here :=
      if altsScalarRepr? c.alts.toList
      then ({} : Std.HashMap Lean.Name Unit).insert c.typeName ()
      else ({} : Std.HashMap Lean.Name Unit)
    altScan c.alts 0 here
  | .return _ | .jmp .. | .unreach _ => ({} : Std.HashMap Lean.Name Unit)
  | .fun .. => ({} : Std.HashMap Lean.Name Unit)
  | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _ | .setTag _ _ k _
  | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ => collectScalarEnums k
  termination_by codeSize code
  decreasing_by all_goals (simp only [codeSize]; omega)
def altScan (alts : Array (Alt .impure)) (i : Nat) (m : Std.HashMap Lean.Name Unit) :
    Std.HashMap Lean.Name Unit :=
  if h : i < alts.size then
    match hget : alts[i] with
    | .ctorAlt _ code => altScan alts (i + 1) (enumUnion m (collectScalarEnums code))
    | .default code => altScan alts (i + 1) (enumUnion m (collectScalarEnums code))
    | .alt _ _ _ hp => absurd hp (by simp)
  else
    m
  termination_by altSizes alts i
  decreasing_by
    all_goals (first
      | exact altSizes_suffix alts i h
      | exact altSizes_gt_ctor alts i h _ _ hget
      | exact altSizes_gt_default alts i h _ hget
      | omega)
end

/-! ## The loop-shape detector (the audit's `jumpsTo`) -/

-- Does `code` contain a `jmp` to `target`? (The loop-shape
-- detector — the audit's `jumpsTo`, ported as a plain structural
-- fold; the same field-order spell as `collectScalarEnums`.)
mutual
def jumpsTo (target : Lean.FVarId) (code : Code .impure) : Bool :=
  match code with
  | .jmp f _ => f == target
  | .jp fd k => jumpsTo target fd.value || jumpsTo target k
  | .cases c => altJumps target c.alts 0
  | .let _ k | .oset _ _ _ k _ | .uset _ _ _ k _ | .sset _ _ _ _ _ k _
  | .setTag _ _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ =>
    jumpsTo target k
  | .return _ | .unreach _ => false
  | .fun .. => false
  termination_by codeSize code
  decreasing_by all_goals (simp only [codeSize]; omega)
def altJumps (target : Lean.FVarId) (alts : Array (Alt .impure)) (i : Nat) : Bool :=
  if h : i < alts.size then
    match hget : alts[i] with
    | .ctorAlt _ code => jumpsTo target code || altJumps target alts (i + 1)
    | .default code => jumpsTo target code || altJumps target alts (i + 1)
    | .alt _ _ _ hp => absurd hp (by simp)
  else
    false
  termination_by altSizes alts i
  decreasing_by
    all_goals (first
      | exact altSizes_suffix alts i h
      | exact altSizes_gt_ctor alts i h _ _ hget
      | exact altSizes_gt_default alts i h _ hget
      | omega)
end

/-! ## The op surface (the legacy `binop?`, grown) -/

/-- The LCNF callee name → (arity, instructions). The closed row set
    is the legacy's proven surface grown by the probe-mined rows; a
    fap outside it refuses loudly (the named boundary — never a
    silent wrong lowering). The u8 arith rows end in the `and 0xFF`
    mask (i32 arithmetic wraps mod 2^32; a `UInt8` wraps mod 2^8).
    Ops are consumed from `WasmCore.OpTable`'s projections everywhere
    downstream (the ONE table, 07-extensibility R6). -/
def binop? : Lean.Name → Option (Nat × List WasmCore.Instr)
  | ``UInt64.add => some (2, [.op .i64add])
  | ``UInt64.sub => some (2, [.op .i64sub])
  | ``UInt64.mul => some (2, [.op .i64mul])
  | ``UInt64.decLt => some (2, [.op .i64ltu])
  | ``UInt64.decEq => some (2, [.op .i64eq])
  | ``UInt64.shiftRight => some (2, [.op .i64shru])
  | ``UInt64.toUInt32 => some (1, [.op .i32wrapi64])
  | ``UInt32.add => some (2, [.op .i32add])
  | ``UInt32.sub => some (2, [.op .i32sub])
  | ``UInt32.mul => some (2, [.op .i32mul])
  | ``UInt32.land => some (2, [.op .i32and])
  | ``UInt32.xor => some (2, [.op .i32xor])
  | ``UInt32.decLt => some (2, [.op .i32ltu])
  | ``UInt32.decEq => some (2, [.op .i32eq])
  | ``UInt32.shiftRight => some (2, [.op .i32shru])
  | ``UInt32.toUInt64 => some (1, [.op .i64extendi32u])
  | ``UInt8.add => some (2, [.op .i32add, .i32const 255, .op .i32and])
  | ``UInt8.sub => some (2, [.op .i32sub, .i32const 255, .op .i32and])
  | ``UInt8.mul => some (2, [.op .i32mul, .i32const 255, .op .i32and])
  | ``UInt8.decLt => some (2, [.op .i32ltu])
  | ``UInt8.decEq => some (2, [.op .i32eq])
  | ``UInt8.land => some (2, [.op .i32and])
  | ``UInt8.xor => some (2, [.op .i32xor])
  | ``UInt8.shiftRight => some (2, [.op .i32shru])
  | ``UInt8.toUInt64 => some (1, [.op .i64extendi32u])
  | _ => none

/-- THE bounded-Nat cap: 2^62 (the legacy's pinned design constant —
    a literal at/above it is a design error, refused before anything
    else is asked about it). -/
def natCap : Nat := 4611686018427387904

/-! ## The lowering state -/

/-- One lowering's state: the fvar → (local index, type) bindings,
    the DECLARED locals beyond the params (creation order — the
    encoder's local groups), the next fresh index, the emitted
    instructions (accumulated REVERSED; `emitted` reverses at the
    end), the LIVE jp registrations (target → the depth offset `X`
    with `br (d - X)` + the param locals), the decl's scalar-enum
    registry (the prescan), and the module's sibling decl names (the
    cross-decl call refusal's evidence). -/
structure LState where
  fvars : Std.HashMap Lean.FVarId (Nat × WasmCore.ValType) := {}
  locals : List WasmCore.ValType := []
  next : Nat := 0
  out : List WasmCore.Instr := []
  jps : Std.HashMap Lean.FVarId (Nat × List Nat) := {}
  enums : Std.HashMap Lean.Name Unit := {}
  sibs : List Lean.Name := []
  deriving Inhabited

/-- The lowering monad: state threading over the closed refusal
    envelope (the legacy `StateT S (Except String)` shape, with the
    envelope in place of the bare string). -/
abbrev M := StateT LState (Except LowerError)

/-- The PRIMITIVE: emit one instruction (appended at the tail of the
    reversed accumulator). -/
def emitI (i : WasmCore.Instr) : M Unit :=
  modify fun s => { s with out := i :: s.out }

/-- The emitted instructions IN ORDER (the accumulator reversed). -/
def emitted : M (List WasmCore.Instr) :=
  return (← get).out.reverse

/-- The type map inside the monad (the state carries the prescan's
    enum registry). -/
def tyMap? (e : Lean.Expr) : M (Option WasmCore.ValType) := do
  return wasmTyOf? (← get).enums e

/-- Bind a fresh local of type `t` to the fvar (the legacy
    `bindLocal`). The index is beyond the params (params bind first,
    0..n-1), so it lands in the DECLARED list. -/
def bindLocal (fvarId : Lean.FVarId) (t : WasmCore.ValType) : M Nat := do
  let s ← get
  let idx := s.next
  set { s with
    fvars := s.fvars.insert fvarId (idx, t)
    locals := s.locals ++ [t]
    next := s.next + 1 }
  return idx

/-- Bind PARAM local i (index in order; NOT in the declared-locals
    list — wasmcore's `Func.locals` means locals BEYOND the params,
    and the validator/types read `params ++ locals`). -/
def bindParam (fvarId : Lean.FVarId) (t : WasmCore.ValType) : M Nat := do
  let s ← get
  let idx := s.next
  set { s with fvars := s.fvars.insert fvarId (idx, t), next := s.next + 1 }
  return idx

/-- Bind a fresh local of type `t` with NO fvar (the function's
    result local — the exit-frame discipline's carrier). -/
def bindFresh (t : WasmCore.ValType) : M Nat := do
  let s ← get
  let idx := s.next
  set { s with locals := s.locals ++ [t], next := s.next + 1 }
  return idx

/-- The local's INDEX (the legacy `load`; unbound = the loud bug
    diagnostic, never a fabricated index). -/
def load (fvarId : Lean.FVarId) : M Nat := do
  match (← get).fvars[fvarId]? with
  | some (n, _) => return n
  | none => throw (.unboundFVar fvarId.name.toString)

/-- The fvar's BOUND type (the return-type check's lookup). -/
def tyOf? (fvarId : Lean.FVarId) : M (Option WasmCore.ValType) := do
  return (← get).fvars[fvarId]? |>.map (·.2)

/-- Run `act` with a FRESH output buffer, returning the emitted
    instructions in order while KEEPING the bindings, the
    fresh-local counter, and the jp registrations (wasm locals are
    function-scoped; the legacy `scopedOut` discipline). -/
def scopedOut (act : M Unit) : M (List WasmCore.Instr) := do
  let s ← get
  match StateT.run act { s with out := [] } with
  | .error e => throw e
  | .ok ((), s2) =>
      set { s2 with out := s.out }
      return s2.out.reverse

/-! ## The argument + let emission -/

/-- Emit one argument's load (LCNF is ANF: a real arg is always an
    fvar; an erased arg pushes nothing — the legacy `emitArg`). -/
def emitArg : Arg .impure → M Unit
  | .fvar fvarId => do emitI (.localget (← load fvarId))
  | .erased => pure ()
  | .type .. => throw (.argShape "a type argument")

/-- The literal kinds' rendering (LitValue has no Repr — the closed
    universe's explicit spellings). -/
def litKind : LitValue → String
  | .nat _ => "nat" | .str _ => "str" | .uint8 _ => "uint8"
  | .uint16 _ => "uint16" | .uint32 _ => "uint32" | .uint64 _ => "uint64"
  | .usize _ => "usize"

/-- THE `let` lowering (the legacy `emitLet`'s slice, grown): the
    scalar literals, the copy, the payload-free-ctor tag, and the
    `binop?` faps; every other value form refuses with its named
    boundary. -/
def emitLet (decl : LetDecl .impure) : M Unit := do
  let ty? ← tyMap? decl.type
  match decl.value with
  | .lit (.uint64 v) =>
      let l ← bindLocal decl.fvarId .i64
      emitI (.i64const v.toNat); emitI (.localset l)
  | .lit (.uint32 v) | .lit (.uint8 v) =>
      let l ← bindLocal decl.fvarId .i32
      emitI (.i32const v.toNat); emitI (.localset l)
  | .lit (.nat v) =>
      -- THE BOUNDED-NAT BOUNDARY. The cap check is the model's pinned
      -- behavior (a literal at/above 2^62 is a design error — the
      -- legacy discipline, ported); below the cap, the boxed-Nat lane
      -- itself is the named follow-up (no allocator in this slice).
      if v >= natCap then
        throw (.natLitCap v)
      else
        throw (.natLane v)
  | .lit v =>
      throw (.typeOutsideFragment "literal kind"
        s!"{litKind v} (only uint64/uint32/uint8 (+ Nat, refused) are modeled)")
  | .erased =>
      -- binds nothing; an erased arg pushes nothing (the legacy arm)
      pure ()
  | .fvar fvarId args =>
      if args.isEmpty then
        match ty? with
        | some t =>
            let l ← bindLocal decl.fvarId t
            emitI (.localget (← load fvarId)); emitI (.localset l)
        | none =>
            throw (.typeOutsideFragment "copy type" (toString decl.type))
      else
        throw (.unsupportedConstruct "closure application (fvar with args)"
          "the closure model (pap/trampolines) is the named follow-up")
  | .fap fn args =>
      match binop? fn with
      | some (nargs, instrs) =>
          -- the legacy's arg order: args emitted left to right, the op
          -- pops the row's sig — `semOp`'s convention consumes them
          -- (first popped first)
          if args.size != nargs then
            throw (.unsupportedConstruct s!"fap {fn}"
              s!"arity {args.size} on a row of arity {nargs}")
          for a in args do emitArg a
          match ty? with
          | none =>
              throw (.typeOutsideFragment "fap result type" (toString decl.type))
          | some t =>
              let l ← bindLocal decl.fvarId t
              instrs.forM emitI
              emitI (.localset l)
      | none =>
          if (← get).sibs.contains fn then
            throw (.declCall fn.toString)
          else
            throw (.unsupportedConstruct s!"fap {fn}"
              "the primitive op surface (binop?) — everything else is the \
               named follow-up")
  | .ctor info args =>
      -- THE TAG DISCIPLINE's value face: a payload-free ctor's value
      -- IS the unboxed tag (the same repr the cases branch on).
      if info.isScalar && args.isEmpty then
        match ty? with
        | some t =>
            let l ← bindLocal decl.fvarId t
            emitI (.i32const info.cidx); emitI (.localset l)
        | none =>
            throw (.typeOutsideFragment "ctor type" (toString decl.type))
      else
        throw (.unsupportedConstruct "ctor"
          "the boxed-object model (allocation + the memory layout)")
  | .pap .. =>
      throw (.unsupportedConstruct "pap"
        "the closure model (partial applications/trampolines)")
  | .proj .. | .oproj .. | .uproj .. | .sproj .. =>
      throw (.unsupportedConstruct "projection"
        "the boxed-object model (the memory layout reads)")
  | .box .. =>
      throw (.unsupportedConstruct "box" "the boxed-object model")
  | .unbox .. =>
      throw (.unsupportedConstruct "unbox" "the boxed-object model")
  | .reset .. | .reuse .. | .isShared .. =>
      throw (.unsupportedConstruct "Perceus reset/reuse/isShared"
        "the object model (no object enters this fragment)")
  | .const .. =>
      throw (.unsupportedConstruct "const"
        "top-level closure constants (the closure model)")

/-! ## The join-point discipline (jp/jmp) -/

/-- The LOOP-ENTRY discipline's splitter: the loop shape's `k` must
    be a straight-line let spine ending in the entry `jmp target` —
    a br cannot ENTER a frame, so the entry falls through into the
    loop's first iteration. -/
def splitEntry (target : Lean.FVarId) : Code .impure →
    Option (List (LetDecl .impure) × Array (Arg .impure))
  | .let decl k =>
      splitEntry target k |>.map (fun (ls, a) => (decl :: ls, a))
  | .jmp f args => if f == target then some ([], args) else none
  | _ => none

/-! ## The ONE code walk (the legacy foldImpure consolidation's
##    discipline) -/

-- Lower the LCNF `Code`. ONE traversal; the single parameter `d` is
-- the RUNTIME FRAME DEPTH at the emission point (how many wasm
-- frames will enclose the emitted instructions when they run — the
-- ONE AST's frame-depth discipline). `res`/`resTy` = the function's
-- result local (index + type) — every `.return` stores it and
-- branches out to the function level (the exit-frame discipline).
-- Well-founded over `codeSize`/`altSizes`.
mutual
def lowerCode (code : Code .impure) (d : Nat) (res : Nat)
    (resTy : WasmCore.ValType) : M Unit :=
  match code with
  | .let decl k => do
      emitLet decl
      lowerCode k d res resTy
  | .return fvarId => do
      let idx ← load fvarId
      let fty ← tyOf? fvarId
      if fty != some resTy then
        throw (.armTypeMismatch (WasmCore.renderValType resTy)
          (WasmCore.renderValType (fty.getD .i64)))
      emitI (.localget idx); emitI (.localset res)
      -- the exit-frame discipline: branch to the OUTERMOST frame
      if d >= 1 then
        emitI (.br (d - 1))
      else
        throw (.loopEntry "a return outside the exit frame (depth 0) — \
          the exit-frame discipline's own inconsistency")
  | .unreach _ => emitI .unreach
  | .cases c => do
      -- THE SCALAR-SCRUTINEE DISCIPLINE (the legacy's scalar cases):
      -- branch on the VALUE. A Bool match compiles to the U8
      -- representation (observed: `cases UInt8` carrying Bool ctorAlts
      -- — the Bool runtime repr is the U8 value); a scalar-repr enum's
      -- repr IS the ctor tag (the prescan's registry — the tag
      -- discipline). Any other type needs the boxed-object tag read —
      -- the named boundary (and the ctor-case-on-Nat throw the
      -- bounded-Nat model demands).
      unless c.typeName == `Bool || c.typeName == `UInt8
        || (← get).enums.contains c.typeName do
        throw (.unsupportedConstruct s!"cases on {c.typeName}"
          "the boxed-object model (tag dispatch) — the ctor-case-on-Nat \
           boundary included")
      let scrutIdx ← load c.discr
      -- the alt chain: arm i runs one chain link deeper (i+1 if_s)
      let altsI ← chainWalk scrutIdx c.alts (d + 1) 0 res resTy
      altsI.forM emitI
      -- the case is TERMINAL in LCNF's impure spine: every arm ends
      -- return/jmp/unreach or a nested case — nothing follows
  | .jp fd k => do
      -- THE JOIN-POINT DISCIPLINE. Shape dispatch on the loop
      -- detector: a body that jumps back to ITSELF lowers to the
      -- loop frame; anything else takes the legacy's
      -- block-and-fallthrough shape. Either way the jp's params bind
      -- to fresh locals and the registration (depth offset X, param
      -- locals) lives exactly as long as the structure's emission.
      let mut ps : List Nat := []
      for p in fd.params do
        if p.borrow then
          throw (.unsupportedConstruct "borrowed jp param"
            "the object model (borrowed params are objects)")
        match ← tyMap? p.type with
        | some t => ps := ps ++ [← bindLocal p.fvarId t]
        | none =>
            throw (.typeOutsideFragment "jp param type" (toString p.type))
      modify fun s => { s with jps := s.jps.insert fd.fvarId (d + 2, ps) }
      if jumpsTo fd.fvarId fd.value then
        -- THE LOOP SHAPE: the entry discipline (k = lets + entry jmp)
        match splitEntry fd.fvarId k with
        | none =>
            throw (.loopEntry "the loop shape's continuation must be a \
              straight-line let spine ending in the entry jmp (a br \
              cannot ENTER a frame; the entry-duplication transform is \
              the named follow-up)")
        | some (lets, args) =>
            for l in lets do emitLet l
            if args.size != ps.length then
              throw (.jpArityDrift fd.fvarId.name.toString args.size ps.length)
            -- the entry arg stores: the first iteration's params
            for (a, p) in args.toList.zip ps do
              emitArg a
              emitI (.localset p)
            let bodyI ← scopedOut (lowerCode fd.value (d + 2) res resTy)
            emitI (.block [.loop (bodyI ++ [.br 1])])
            emitI .unreach
      else
        -- THE BLOCK SHAPE (the legacy's block-and-fallthrough, in
        -- depths): k inside the inner block, the body after it, the
        -- fallthrough br skips the body, the seal closes.
        let kI ← scopedOut (lowerCode k (d + 2) res resTy)
        let bodyI ← scopedOut (lowerCode fd.value (d + 1) res resTy)
        emitI (.block ([.block (kI ++ [.br 1])] ++ bodyI))
        emitI .unreach
      -- the registration's scope ends with the structure
      modify fun s => { s with jps := s.jps.erase fd.fvarId }
  | .jmp fvarId args => do
      -- the goto: store the args into the jp's param locals, branch
      -- out to the jp's structure (br (d - X) — through any if_
      -- nesting)
      match (← get).jps[fvarId]? with
      | none =>
          throw (.jpUnregistered fvarId.name.toString)
      | some (x, ps) =>
          if args.size != ps.length then
            throw (.jpArityDrift fvarId.name.toString args.size ps.length)
          for (a, p) in args.toList.zip ps do
            emitArg a
            emitI (.localset p)
          if d >= x then
            emitI (.br (d - x))
          else
            throw (.jpUnregistered fvarId.name.toString)
  | .fun .. =>
      throw (.unsupportedConstruct "fun"
        "local function values (the closure model)")
  | .oset .. =>
      throw (.unsupportedConstruct "in-place mutation (oset)"
        "the object model (oset/uset/sset/setTag)")
  | .uset .. =>
      throw (.unsupportedConstruct "in-place mutation (uset)"
        "the object model (oset/uset/sset/setTag)")
  | .sset .. =>
      throw (.unsupportedConstruct "in-place mutation (sset)"
        "the object model (oset/uset/sset/setTag)")
  | .setTag .. =>
      throw (.unsupportedConstruct "in-place mutation (setTag)"
        "the object model (oset/uset/sset/setTag)")
  | .inc .. =>
      throw (.unsupportedConstruct "Perceus RC (inc)"
        "the object model (no object enters this fragment)")
  | .dec .. =>
      throw (.unsupportedConstruct "Perceus RC (dec)"
        "the object model (no object enters this fragment)")
  | .del .. =>
      throw (.unsupportedConstruct "Perceus RC (del)"
        "the object model (no object enters this fragment)")
  termination_by codeSize code
  decreasing_by all_goals (simp only [codeSize]; omega)
def chainWalk (scrutIdx : Nat) (alts : Array (Alt .impure)) (d : Nat) (i : Nat)
    (res : Nat) (resTy : WasmCore.ValType) : M (List WasmCore.Instr) := do
  -- The alt-chain fold (the legacy `buildAlts`): nested `if_`s keyed
  -- on the ctor index, a `default` alt as the final else, an
  -- uncovered ctor set as `[unreach]` (the alt chain is exhaustive at
  -- runtime). LCNF impure alts carry NO `.alt` (the pure ctor's
  -- proof discharges like the legacy's `absurd`). Arm i of the chain
  -- lowers at depth `d` (each chain link is one `if_` frame).
  if h : i < alts.size then
    match hget : alts[i] with
    | .ctorAlt info code => do
        let thenI ← scopedOut (lowerCode code d res resTy)
        let elseI ← chainWalk scrutIdx alts (d + 1) (i + 1) res resTy
        return ([.localget scrutIdx, .i32const info.cidx, .op .i32eq]
          ++ [.if_ thenI elseI])
    | .default code => scopedOut (lowerCode code d res resTy)
    | .alt _ _ _ hp => absurd hp (by simp)
  else
    return [.unreach]
  termination_by altSizes alts i
  decreasing_by
    all_goals (first
      | exact altSizes_suffix alts i h
      | exact altSizes_gt_ctor alts i h _ _ hget
      | exact altSizes_gt_default alts i h _ hget
      | omega)
end

/-! ## The decl lowering -/

/-- The per-decl walk: bind the param locals (0..n-1 in order — the
    executor driver's binding discipline: param i lands in local i),
    bind the result local, walk the body at depth 1 (inside the exit
    frame), collect the emitted instructions + the result index. -/
def declWalk (code : Code .impure) (params : Array (Param .impure))
    (resTy : WasmCore.ValType) : M (List WasmCore.Instr × Nat) := do
  for p in params do
    if p.borrow then
      throw (.unsupportedConstruct "borrowed param"
        "the object model (borrowed params are objects)")
    match ← tyMap? p.type with
    | some t => discard <| bindParam p.fvarId t
    | none =>
        throw (.typeOutsideFragment "param type" (toString p.type))
  let res ← bindFresh resTy
  lowerCode code 1 res resTy
  let body ← emitted
  pure (body, res)

/-- Lower SEVERAL impure-phase LCNF decls into ONE module: one type +
    one function + one export per decl (the entry index = the decl
    order). The decls stay CALL-DISJOINT: a fap naming a sibling decl
    refuses as the cross-decl call (the call lane is wasmcore's
    in-flight work) — never a fabricated call. -/
def lowerFuncs (ds : List (Decl .impure)) : Except LowerError WasmCore.Module :=
  let sibs := ds.map (·.name)
  let one (i : Nat) (d : Decl .impure) :
      Except LowerError (WasmCore.FuncType × WasmCore.Func × String) :=
    match d.value with
    | .extern .. =>
        throw (.unsupportedConstruct "extern decl"
          "a decl with a body (a plain `def`)")
    | .code code =>
      let enums := collectScalarEnums code
      match wasmTyOf? enums d.type with
      | none => throw (.typeOutsideFragment "result type" (toString d.type))
      | some resTy =>
        match StateT.run (declWalk code d.params resTy)
            ({ fvars := {}, locals := [], next := 0, out := []
             , jps := {}, enums := enums, sibs := sibs } : LState) with
        | .error e => .error e
        | .ok ((bodyI, res), st) =>
            let ft : WasmCore.FuncType :=
              ⟨d.params.toList.filterMap (fun p => wasmTyOf? enums p.type), [resTy]⟩
            let f : WasmCore.Func :=
              { tyIdx := i, locals := st.locals
              , body := [.block bodyI, .localget res] }
            .ok (ft, f, d.name.toString)
  match (ds.zipIdx.mapM (fun p => one p.2 p.1)) with
  | .error e => .error e
  | .ok rows =>
    .ok
      { types := rows.map (·.1)
        funcs := rows.zipIdx.map (fun p => { p.1.2.1 with tyIdx := p.2 })
        exports := rows.zipIdx.map
          (fun p => { name := p.1.2.2, desc := WasmCore.ExportDesc.func p.2 })
        memMin := 0 }

/-- Lower ONE impure-phase LCNF decl to a one-function module: one
    type (the params → the mapped scalars, the result → its mapped
    scalar), one function (the exit-frame discipline: the body inside
    the outermost frame, `localget res` after), exported under the
    decl's own name. The decl's `type` in the impure phase IS the
    return type (LCNF's erasure — the Basic.lean note); `extern`
    decls refuse (no body). -/
def lowerFunc (d : Decl .impure) : Except LowerError WasmCore.Module :=
  lowerFuncs [d]

end Guest
