/-
# Guest.Lcnf — the LCNF frontend (the lane's host-side input face)

The guest compiler's LEAN frontend: a compiled Lean environment + a
target function name → the function's impure-phase LCNF as data, and
— the frontend's product — the LCNF → `Guest.IR` reading (`toIR`):
the LCNF walking that used to live in the lowering is THE FRONTEND,
because the lowering core consumes ONLY the IR (no LCNF imports in
`Guest.Lower`). The frontends are per-language (this one reads LCNF;
a guestlang-edgepython frontend would read Python's AST); the IR is
the contract every frontend produces and the lowering consumes.

Host-side discipline: `import Lean` + `Lean.Compiler.LCNF` — the Lean
compiler's internals are HOST tooling (the C2/host cone; the EMITTED
code is the guest). Mined from
`legacy/lean/wasm-backend/WasmGenMain.lean` (the LCNF re-run pattern):

- the pipeline runs IN THIS PROCESS (the impure phase is not
  persisted in oleans — `LCNF.main` over the imported environment);
- `compiler.reuse` is DISABLED (the emitter cannot lower
  reset/reuse joins — the legacy driver's standing option);
- the decl is fetched from the pipeline's LOCAL cache
  (`getLocalImpureDecl?` — the compiled decl never joins the
  environment's constants).

The reading face (the frontend proper):

- **The tag prescan** (`collectScalarEnums`): the decl's own code →
  the scalar-representable enum registry (the observed evidence, no
  env threading) — the IR's `cases_` `CaseVia` verdict and the `enum`
  type rows are its reified product.
- **The type map** (`irTyOf?`): the Lean type expr → the IR's closed
  `Ty` rows (the machine scalars, the i32-repr source scalars, the
  prescan's enums, the object rows); anything else is the named
  `typeOutsideFragment` refusal at the reification site.
- **The fap dispatch** (`natFapOf?`/`binopOf?` + the sibling
  registry): the callee NAME matching is Lean-specific, so it lives
  here; the IR carries the reified rows (`IR.NatFap`/`IR.Binop`/
  `IR.LetValue.call`).
- **The honest drop**: an erased let binds nothing (the legacy arm) —
  the frontend drops it, the spine continues.
- **The composed pipeline** (`compile`): toIR ∘ lowerFuncs — the
  frontends' product riding the lowering end to end.

The five questions (notes/v3/01-core.md):

- **Root**: none — a host-side READER (the input face of the lane).
- **Carrier grade**: none — the output is the IR's own data; the
  crossing discipline (the Diag refusals) is `Guest.LowerError`'s
  shared envelope (Guest.IR).
- **Spine reading**: the LCNF decl is the registry-content this
  frontend folds into the IR spine (`Guest.Lower`'s spine).
- **Ladder rung**: n/a (host machinery; the IR is closed data).
- **Gate row**: `gates kernel-check` (the module replays through the
  pure kernel) — the lane's modules are gated source.

Consumer trail: `Guest.Lower` is NOT a consumer (the split — the
lowering consumes only the IR); `Guest.Lcnf.compile` is the composed
pipeline the drivers call (`GuestTests.Main` — the std battery's
`GuestTests.StdSpecs` groups included, the P2 merge —,
`Guest.ComponentGenMain`, `Guest.GenMain`'s clients). Host-side
(imports Lean); NOT core-only, and not a cone-low module: the guest
lane is C2/host.
-/

import Lean
import Lean.Compiler.LCNF
import Guest.IR
import Guest.Lower
import Guest.Frontend
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Guest

open Lean Compiler.LCNF

/-- The driver options: `compiler.reuse` disabled (the emitter cannot
    lower reset/reuse joins — the legacy WasmGenMain discipline). -/
def lcnfOptions : Lean.Options :=
  (default : Lean.Options).setBool `compiler.reuse false

/-- THE LCNF RUNNER (the drivers' shared body, written once): one
    pipeline run over `roots` in a CoreM context on `env`; `fetch`
    reads the caller's decls from the run's local cache; every failure —
    a thrown pipeline error or a fetch refusal — is the named envelope
    (an `.error` answer, never a crash). -/
def runLcnf (env : Lean.Environment) (roots : Array Lean.Name) (tag : String)
    (fetch : Lean.CoreM (Except String α)) : IO (Except String α) := do
  let ctx : Lean.Core.Context :=
    { fileName := s!"<{tag}>", fileMap := default, options := lcnfOptions }
  let state : Lean.Core.State := { env := env }
  try
    let act : Lean.CoreM (Except String α) := do
      Lean.Compiler.LCNF.main roots lcnfOptions
      fetch
    let (r, _) ← act.toIO ctx state
    return r
  catch e =>
    return .error
      s!"Guest.Lcnf: the LCNF pipeline failed for `{tag}`: {toString e}"

/-- Read ONE function's impure-phase LCNF (the runner's single-decl
    face): a target that is not a compilable `def` answers `.error`,
    never a crash. -/
def readDecl? (env : Lean.Environment) (target : Lean.Name) :
    IO (Except String (Decl .impure)) :=
  runLcnf env #[target] s!"readDecl `{target}`" do
    match ← Lean.Compiler.LCNF.getLocalImpureDecl? target with
    | some d => pure (Except.ok d)
    | none => pure (Except.error
        s!"Guest.Lcnf: no impure-phase LCNF decl for `{target}` — \
           the target did not compile (is it a `def`?)")

/-- Read a ROOT decl + a FAMILY of names from the SAME pipeline run (the
    closure discipline's reader face): the pipeline's roots are the USER
    decls — an internal `_closed`/`_lam` constant CANNOT root its own
    run (observed: `Unknown constant` — the pipeline compiles the
    user-level closure and pulls the family into its local cache), so
    the family rides the root's run and each name is fetched from that
    one cache. The order of `family` IS the module's decl order (the
    function-table indices the pap stores). -/
def readFamily? (env : Lean.Environment) (root : Lean.Name)
    (family : List Lean.Name) :
    IO (Except String (List (Decl .impure))) :=
  runLcnf env #[root] s!"readFamily `{root}`" do
    let mut out : List (Decl .impure) := []
    for t in family do
      match ← Lean.Compiler.LCNF.getLocalImpureDecl? t with
      | some d => out := out ++ [d]
      | none =>
          return .error
            s!"Guest.Lcnf: no impure-phase LCNF decl for `{t}` in the \
               root `{root}`'s family run"
    pure (Except.ok out)

/-! ## The size measures (the well-founded substrate over LCNF)

The LCNF `Code` is a FOREIGN tree (the Lean compiler's), and its
`FunDecl`/`Cases` hops hide the recursive occurrences behind structure
projectors the sizeOf-based termination cannot see through on a
variable — so the frontend's walkers ride the explicit total measures
(the derived `sizeOf` + the pair's lex-order facts, proven once; the
IR itself needs NONE of this — its spine is the structural face).
-/

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

/-! The prescan: the decl's code → the scalar-representable enum
registry (the type names whose OBSERVED cases are all payload-free
ctor alts). Well-founded over the measures above (the FunDecl/Cases
hops). NOTE the field orders the patterns spell: a `uset` carries
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

/-! ## The type map (the Lean type expr → the IR's Ty rows) -/

/-- THE OBJECT ROWS' names (the object discipline's faces): the impure
    pipeline's object types — `tobj` (an object param/result), `tagged`
    (a boxed scalar or a payload-free ctor of an object type), `obj`
    (a compound object), and the source-level `Nat`. -/
def objectRowName (c : Lean.Name) : Bool :=
  c == `tobj || c == `tagged || c == `obj || c == `Nat

/-- The Lean type expression → the IR type row. `enums` = the prescan's
    scalar-enum registry (`collectScalarEnums`); `none` = outside the
    fragment (the caller refuses with the named diagnostic at its
    reification site). The rows: the machine scalars (u64/u32/u8), the
    i32-repr source scalars (bool/char), the object rows (nat/tobj/
    tagged/obj — the ONE pointer repr), and the prescan's enums. -/
def irTyOf? (enums : Std.HashMap Lean.Name Unit) : Lean.Expr → Option IR.Ty
  | .const c _ =>
      if c == `UInt64 then some .u64
      else if c == `UInt32 then some .u32
      else if c == `UInt8 then some .u8
      else if c == `Bool then some .bool
      else if c == `Char then some .char
      else if objectRowName c then
        some (if c == `Nat then .nat else if c == `tobj then .tobj
              else if c == `tagged then .tagged else .obj)
      else if enums.contains c then some (.enum c.toString) else none
  | _ => none

/-! ## The fap dispatch (the Lean-name → IR-row tables) -/

/-- The literal kinds' rendering (LitValue has no Repr — the closed
    universe's explicit spellings). -/
def litKind : LitValue → String
  | .nat _ => "nat" | .str _ => "str" | .uint8 _ => "uint8"
  | .uint16 _ => "uint16" | .uint32 _ => "uint32" | .uint64 _ => "uint64"
  | .usize _ => "usize"

/-- The boxed-Nat fap names → the IR rows (the legacy's sanctioned
    surface; the probe-observed pipeline rows: `Nat.add`/`mul`/`sub`/
    `decLt`/`decEq`/`decLe` — `Nat.beq` joins the family for the
    hand-built face). -/
def natFapOf? : Lean.Name → Option IR.NatFap
  | ``Nat.decEq => some .decEq | ``Nat.beq => some .beq
  | ``Nat.decLt => some .decLt | ``Nat.decLe => some .decLe
  | ``Nat.add => some .add | ``Nat.sub => some .sub
  | ``Nat.mul => some .mul
  | _ => none

/-- The op-surface names → the IR rows (the legacy `binop?`'s row set,
    reified; the u8 arith rows' `and 0xFF` masks ride the LOWERING's
    instruction table — the name matching is the frontend's). A fap on
    NEITHER table (and no sibling) refuses at the reification site. -/
def binopOf? : Lean.Name → Option IR.Binop
  | ``UInt64.add => some .u64add
  | ``UInt64.sub => some .u64sub
  | ``UInt64.mul => some .u64mul
  | ``UInt64.decLt => some .u64ltu
  | ``UInt64.decEq => some .u64eq
  | ``UInt64.shiftRight => some .u64shru
  | ``UInt64.toUInt32 => some .u64wrap
  | ``UInt32.add => some .u32add
  | ``UInt32.sub => some .u32sub
  | ``UInt32.mul => some .u32mul
  | ``UInt32.land => some .u32and
  | ``UInt32.xor => some .u32xor
  | ``UInt32.decLt => some .u32ltu
  | ``UInt32.decEq => some .u32eq
  | ``UInt32.shiftRight => some .u32shru
  | ``UInt32.toUInt64 => some .u32ext
  | ``UInt8.add => some .u8add
  | ``UInt8.sub => some .u8sub
  | ``UInt8.mul => some .u8mul
  | ``UInt8.land => some .u8and
  | ``UInt8.xor => some .u8xor
  | ``UInt8.decLt => some .u8ltu
  | ``UInt8.decEq => some .u8eq
  | ``UInt8.shiftRight => some .u8shru
  | ``UInt8.toUInt64 => some .u8ext
  | _ => none

/-! ## The LCNF → IR reading (the frontend proper) -/

/-- The args' reification: fvars → the rendered variable, erased/type
    args ride (each lane names its own refusal at the lowering). -/
def trArgs (args : Array (Arg .impure)) : Array IR.Arg :=
  args.map (fun a =>
    match a with
    | .fvar f => .var f.name.toString
    | .erased => .erased
    | .type .. => .typeArg)

/-- THE LET REIFICATION: one LCNF let → one IR `LetDecl`. The type map
    runs at the reification site (the position-appropriate refusal);
    the value forms reify per the module header's table. The literal
    lets whose Lean type is outside the map ride the VALUE's implied
    row (the lowering binds the width from the value — the recorded
    row's only consumer is the field-class law, and a lit-bound fvar
    never feeds a ctor face in the fragment). -/
def trLet (enums : Std.HashMap Lean.Name Unit) (sibs : List Lean.Name)
    (decl : LetDecl .impure) (k : IR.Code) :
    Except LowerError IR.Code := do
  let ty? := irTyOf? enums decl.type
  let v := decl.fvarId.name.toString
  let value ←
    match decl.value with
    | .lit (.uint64 v) => .ok (.litU64 v.toNat)
    | .lit (.uint32 v) => .ok (.litU32 v.toNat)
    | .lit (.uint8 v) => .ok (.litU8 v.toNat)
    | .lit (.nat v) => .ok (.litNat v)
    | .lit v =>
        throw (.typeOutsideFragment "literal kind"
          s!"{litKind v} (only uint64/uint32/uint8 (+ the boxed Nat) are modeled)")
    | .erased =>
        -- UNREACHABLE: trCode drops the erased let before calling
        -- trLet (the honest drop); the case is the match's
        -- exhaustiveness face.
        throw (.unsupportedConstruct "erased let"
          "dropped at the frontend's spine (the honest drop)")
    | .proj .. | .uproj .. =>
        throw (.unsupportedConstruct "projection"
          "the non-scalar payload shapes (proj/uproj — the pure-projection \
           and usize faces) — the tag dispatch's named refusal")
    | .fvar fvarId args =>
        if args.isEmpty then
          -- THE COPY (the ty? face: the mapped row or the refusal)
          match ty? with
          | some _ => .ok (.copy (fvarId.name.toString))
          | none =>
              throw (.typeOutsideFragment "copy type" (toString decl.type))
        else
          -- THE CLOSURE APPLICATION (the lowering decides
          -- pap-provenance vs first-class from its own state)
          match ty? with
          | none =>
              throw (.typeOutsideFragment "closure application result \
                type" (toString decl.type))
          | some _ => .ok (.apply (fvarId.name.toString) (trArgs args))
    | .fap fn args =>
        -- THE FAP DISPATCH (the name matching is the frontend's): the
        -- boxed-Nat rows, then the op surface, then the sibling call
        -- lane; anything else is the named refusal.
        match natFapOf? fn with
        | some row =>
            if args.size != 2 then
              throw (.unsupportedConstruct s!"fap {fn}"
                s!"arity {args.size} on a boxed-Nat row of arity 2")
            match ty? with
            | none =>
                match row with
                | .add | .sub | .mul =>
                    throw (.typeOutsideFragment "boxed-Nat result type"
                      (toString decl.type))
                | _ =>
                    throw (.typeOutsideFragment "fap result type"
                      (toString decl.type))
            | some _ => .ok (.natFap row (trArgs args))
        | none =>
        match binopOf? fn with
        | some op =>
            if args.size != IR.Binop.arity op then
              throw (.unsupportedConstruct s!"fap {fn}"
                s!"arity {args.size} on a row of arity {IR.Binop.arity op}")
            match ty? with
            | none =>
                throw (.typeOutsideFragment "fap result type"
                  (toString decl.type))
            | some _ => .ok (.binop op (trArgs args))
        | none =>
            if sibs.contains fn then
              match ty? with
              | none =>
                  throw (.typeOutsideFragment "call result type"
                    (toString decl.type))
              | some _ => .ok (.call fn.toString (trArgs args))
            else
              throw (.unsupportedConstruct s!"fap {fn}"
                "the primitive op surface (binop?) — everything else is \
                 the named follow-up")
    | .ctor info args =>
        -- THE CTOR VALUE's two faces, keyed on the RESULT TYPE's row
        -- (the lowering re-derives the face from the IR's row): an
        -- object-row result → the object face; a scalar-row result →
        -- the tag face. An unmappable result type is the named
        -- refusal (the tag face's `ctor type`).
        let objRow := match decl.type with
          | .const c _ => objectRowName c | _ => false
        if objRow then
          .ok (.ctor info.cidx (trArgs args))
        else
          match ty? with
          | none =>
              throw (.typeOutsideFragment "ctor type" (toString decl.type))
          | some _ => .ok (.ctor info.cidx (trArgs args))
    | .pap fn args =>
        match ty? with
        | none =>
            throw (.typeOutsideFragment
              "pap result type (the closure object's pointer)"
              (toString decl.type))
        | some _ => .ok (.pap fn.toString (trArgs args))
    | .sproj n offset var _ =>
        match ty? with
        | none =>
            throw (.typeOutsideFragment "sproj result type"
              (toString decl.type))
        | some _ => .ok (.sproj n offset var.name.toString)
    | .oproj i var =>
        match ty? with
        | none =>
            throw (.typeOutsideFragment "oproj operand types (the base's \
              object repr, the field's pointer result)"
              s!"{toString decl.type} ← field {i}")
        | some _ => .ok (.oproj i var.name.toString)
    | .box bty src =>
        -- THE SCALAR-BOX LANE's row resolution: the boxed type's expr
        -- must resolve to a row (the object rows ride identity at the
        -- lowering, the scalars box); anything else is the scalar
        -- branch's refusal (the objRow check comes first there, but a
        -- non-row name is never an object row).
        let boxed? : Option IR.Ty :=
          match bty with
          | .const _ _ => irTyOf? ({} : Std.HashMap Lean.Name Unit) bty
          | _ => none
        let scalarRefusal : Except LowerError IR.LetValue :=
          throw (.typeOutsideFragment "box operand types (the boxed \
            scalar's width, the result's pointer repr, the source \
            local's bound width)"
            s!"{toString bty} → {toString decl.type}")
        match boxed? with
        | none => scalarRefusal
        | some row =>
            if row.isObjRow then
              match ty? with
              | none =>
                  throw (.typeOutsideFragment "box (object-row) operand \
                    types" s!"{toString bty} ← {toString decl.type}")
              | some _ => .ok (.box row src.name.toString)
            else
              match ty? with
              | none => scalarRefusal
              | some _ => .ok (.box row src.name.toString)
    | .unbox src =>
        match ty? with
        | none =>
            throw (.typeOutsideFragment "unbox operand types (the box \
              pointer's object repr, the result's scalar width)"
              (toString decl.type))
        | some _ => .ok (.unbox src.name.toString)
    | .reset .. | .reuse .. | .isShared .. =>
        throw (.unsupportedConstruct "Perceus reset/reuse/isShared"
          "the object model (no object enters this fragment)")
    | .const fn _us args .. =>
        match ty? with
        | none =>
            throw (.typeOutsideFragment "const result type"
              (toString decl.type))
        | some _ => .ok (.const fn.toString (trArgs args))
  let tyRow : IR.Ty :=
    match decl.value with
    | .lit (.uint64 _) => ty?.getD .u64
    | .lit (.uint32 _) => ty?.getD .u32
    | .lit (.uint8 _) => ty?.getD .u8
    | .lit (.nat _) => ty?.getD .nat
    | _ => ty?.getD .u64  -- unreachable: the arms above threw
  .ok (.let_ { var := v, ty := tyRow, value := value } k)

-- The LCNF → IR code spine (the frontend's ONE walk; well-founded
-- over `codeSize`). The LCNF forms the IR cannot express refuse here
-- (the SAME closed vocabulary, the SAME texts) — the lowering core
-- never sees them. The BORROW HONESTY: a jp param's `borrow` flag is
-- the RC face's flag (the callee skips inc/dec) — the no-RC slice
-- has no decrements to elide, so the flag is recorded-and-ignored
-- (dropped at the IR's boundary).
mutual
def trCode (enums : Std.HashMap Lean.Name Unit) (sibs : List Lean.Name)
    (code : Code .impure) : Except LowerError IR.Code :=
  match code with
  | .let decl k =>
      -- THE HONEST DROP: an erased let binds nothing (the legacy arm)
      match decl.value with
      | .erased => trCode enums sibs k
      | _ => do
        let kc ← trCode enums sibs k
        trLet enums sibs decl kc
  | .return fvarId => .ok (.ret fvarId.name.toString)
  | .unreach _ => .ok .unreach
  | .cases c => do
      -- THE SCRUTINEE DISPATCH's verdict (the prescan's, reified):
      -- the SCALAR lane branches on the value (Bool/UInt8/the
      -- prescan's enums); everything else rides the object lane's tag
      -- read — the lowering re-checks the repr (the named refusal).
      let via : IR.CaseVia :=
        if c.typeName == `Bool || c.typeName == `UInt8
          || enums.contains c.typeName then .value else .tag
      let alts ← trAlts enums sibs c.alts 0
      .ok (.cases_ c.typeName.toString via c.discr.name.toString alts)
  | .jp fd k => do
      let mut ps : List (IR.Var × IR.Ty) := []
      for p in fd.params do
        match irTyOf? enums p.type with
        | some t => ps := ps ++ [(p.fvarId.name.toString, t)]
        | none =>
            throw (.typeOutsideFragment "jp param type" (toString p.type))
      let v ← trCode enums sibs fd.value
      let kc ← trCode enums sibs k
      .ok (.jp fd.fvarId.name.toString ps v kc)
  | .jmp f args => .ok (.jmp f.name.toString (trArgs args))
  | .fun .. =>
      throw (.unsupportedConstruct "fun"
        "local function values (the closure model)")
  | .oset fvarId i y k => do
      -- THE IN-PLACE WRITE (the ref field): the value must be an fvar
      -- (the store's pointer); the row checks ride the lowering.
      let kc ← trCode enums sibs k
      match y with
      | .fvar yf => .ok (.oset fvarId.name.toString i yf.name.toString kc)
      | .erased =>
          throw (.argShape "an oset value (the write's pointer)")
      | .type .. =>
          throw (.argShape "an oset type argument (the write's pointer)")
  | .uset _ _ _ k => do
      -- THE NAMED REFUSAL (the mutation family's boundary): the
      -- `uset` face is a USize slot write — USize has no modeled row
      -- (the 64-bit scalar face outside the fragment's type map).
      let _kc ← trCode enums sibs k
      throw (.unsupportedConstruct "in-place mutation (uset)"
        "the USize slot face — USize has no modeled row in the type map \
         (the sset/oset/setTag family landed around it)")
  | .sset fvarId i offset y ty k => do
      -- THE IN-PLACE WRITE (the scalar field): the field's TYPE EXPR
      -- must map to a row (the store's width rides it); the rc=1
      -- legality guard lives at the lowering.
      let kc ← trCode enums sibs k
      match irTyOf? enums ty with
      | some row =>
          .ok (.sset fvarId.name.toString i offset y.name.toString row kc)
      | none =>
          throw (.typeOutsideFragment "sset field type" (toString ty))
  | .setTag fvarId cidx k => do
      -- THE IN-PLACE WRITE (the tag byte).
      let kc ← trCode enums sibs k
      .ok (.setTag fvarId.name.toString cidx kc)
  | .inc fvarId n _check _persistent k => do
      let kc ← trCode enums sibs k
      .ok (.inc fvarId.name.toString n kc)
  | .dec fvarId n _check _persistent objs? k => do
      let kc ← trCode enums sibs k
      -- THE FIELD CASCADE's count (the ref-field count, reified
      -- directly — the lowering rides the landed layout: the ref
      -- slots are 0..count-1)
      .ok (.dec fvarId.name.toString n objs? kc)
  | .del fvarId k => do
      -- THE DEL (the honest deallocation): the ownership assertion +
      -- the dead marking + the reuse publish at the lowering (the
      -- shape provenance keys the publish — the lowering's record).
      let kc ← trCode enums sibs k
      .ok (.del fvarId.name.toString kc)
  termination_by codeSize code
  decreasing_by all_goals (simp only [codeSize]; omega)
def trAlts (enums : Std.HashMap Lean.Name Unit) (sibs : List Lean.Name)
    (alts : Array (Alt .impure)) (i : Nat) : Except LowerError (List IR.Alt) :=
  if h : i < alts.size then
    match hget : alts[i] with
    | .ctorAlt info code => do
        let c ← trCode enums sibs code
        let r ← trAlts enums sibs alts (i + 1)
        -- THE ORDER PRESERVED: the rest (later arms) ride `r`; THIS
        -- arm is EARLier — cons at the head (a tail-append here would
        -- REVERSE the chain — and a default arm would land FIRST, the
        -- chain-walk short-circuiting every ctorAlt away; the
        -- setTag fixture's teeth caught exactly that).
        .ok (IR.Alt.ctorAlt info.cidx c :: r)
    | .default code => do
        let c ← trCode enums sibs code
        let r ← trAlts enums sibs alts (i + 1)
        .ok (IR.Alt.default c :: r)
    | .alt _ _ _ hp => absurd hp (by simp)
  else
    .ok []
  termination_by altSizes alts i
  decreasing_by
    all_goals (first
      | exact altSizes_suffix alts i h
      | exact altSizes_gt_ctor alts i h _ _ hget
      | exact altSizes_gt_default alts i h _ hget
      | omega)
end

/-- THE FRONTEND's product: the LCNF decls → the IR decls (the
    pipeline's contract). The sibling registry (the decl NAMES — the
    fap dispatch's call lane) spans the WHOLE list (a decl's fap may
    name any sibling). The per-decl order: the extern refusal, the
    prescan, the result type, the params, the body — the lowering's
    old `one` walk's order verbatim. -/
def toIR (ds : List (Decl .impure)) : Except LowerError (List IR.Decl) := do
  let sibs := ds.map (·.name)
  let mut out : List IR.Decl := []
  for d in ds do
    match d.value with
    | .extern _ =>
        -- THE EXTERN DECLARATION (the declared trust boundary): the
        -- signature's faces map like any decl (the result type, the
        -- params — both must land in the fragment's rows); the BODY
        -- is not modeled — the IR's `extern` leaf, the lowering's
        -- `unreach` body (the host link step is the named follow-up).
        -- Calls to it ride the call lane's index like any sibling.
        let resultTy ←
          match irTyOf? ({} : Std.HashMap Lean.Name Unit) d.type with
          | some t => .ok t
          | none => throw (.typeOutsideFragment "extern result type"
            (toString d.type))
        let mut ps : List (IR.Var × IR.Ty) := []
        for p in d.params do
          match irTyOf? ({} : Std.HashMap Lean.Name Unit) p.type with
          | some t => ps := ps ++ [(p.fvarId.name.toString, t)]
          | none =>
              throw (.typeOutsideFragment "extern param type"
                (toString p.type))
        out := out ++ [{ name := d.name.toString
                       , params := ps, resultTy := resultTy
                       , value := .extern
                           { params := ps.map (·.2), result := resultTy
                           , effect := .host
                           , note := "the LCNF frontend's extern: the \
                                      body is unmodeled (the host link \
                                      step is the named follow-up); the \
                                      declared rows are the mapped \
                                      faces above" } }]
    | .code code =>
        let enums := collectScalarEnums code
        let resultTy ←
          match irTyOf? enums d.type with
          | some t => .ok t
          | none => throw (.typeOutsideFragment "result type" (toString d.type))
        let mut ps : List (IR.Var × IR.Ty) := []
        for p in d.params do
          match irTyOf? enums p.type with
          | some t => ps := ps ++ [(p.fvarId.name.toString, t)]
          | none =>
              throw (.typeOutsideFragment "param type" (toString p.type))
        let value ← trCode enums sibs code
        out := out ++ [{ name := d.name.toString
                       , params := ps, resultTy := resultTy, value }]
  return out

/-- THE COMPOSED PIPELINE: the LCNF decls → the IR → the wasm module.
    The drivers' one call (the fixtures ride the IR end to end — the
    frontend's product IS the lowering's whole input). The tail is the
    kit's (`Guest.Frontend.link` — the shared face, both frontends). -/
def compile (ds : List (Decl .impure)) : Except LowerError WasmCore.Module :=
  Frontend.link (toIR ds)

end Guest
