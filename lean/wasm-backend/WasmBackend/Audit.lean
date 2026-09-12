import WasmBackend.Wat
import WasmBackend.Layout

/-!
# WasmBackend.Audit — the emitted-WAT store-shape audit (seam #6)

The seam-contract #6 promotion: "the walk's region-disjointness check =
the 6.5.3 recipe applied to the backend's own output". This module is
the Lean-side STATIC check over the backend's emitted instruction
lists. Every memory store's ADDRESS is checked twice, for two
independent properties:

1. PROVENANCE — the pointer is trackable (the vouch for the POINTER);
2. RANGE — the store's `(offset, width)` fits the region's KNOWN
   extent (the vouch for the FIT: this module's range-tracking lane).

## The model: the PROVENANCE WALK (honest v1 = store-SHAPE, not full dataflow)

An abstract walk over a `List Instr` tracks, per local, the abstract
VALUE it was last set from:

* `allocPtr`  — `i32const N; call $alloc` (a fresh region, runtime size)
* `const n`   — an `i32const`/`i64const` (a scalar, or a STATIC base —
  the VALUE is tracked so the range lane can check static extents)
* `param`     — a function parameter (the caller's object) — `auditFunc` only
* `glob`      — `global.get` (a tracked global root)
* `localRef`  — `local.get n` (resolved through the env at USE time)
* `loaded v`  — a memory load from abstract address `v` (the
  pointer-copy chain: the load of a KNOWN object's field)
* `plus a b`  — pointer arithmetic; tracked ONLY in the shape
  (known base, const offset) — the `dst + 16` idiom
* `opaque`    — anything unmodeled (non-alloc calls, mul-based
  addresses, values left by structured forms, unbound locals)

A store (`i32.store`/`i64.store`/`i32.store8`/`i64.store8`) or a
`memory.copy` DESTINATION is checked: its abstract address must be a
KNOWN ROOT — const / allocPtr / param / glob / a local whose defining
value is a known root / a load from a known root / (known base +
const). The flagged class = the watch-users bug's class: stores
through UNINITIALIZED or UNKNOWN-provenance pointers.

Fail-closed by design: an underflowed abstract stack, an `Instr.raw`
line, or an unmodeled address producer produces a FINDING, never a
silent pass.

## The RANGE lane: the store's (offset, width) vs the region's extent

Each store's byte range `[addr + offset, addr + offset + width)` (the
width from `widthOf`: 4 for `i32.store`, 8 for `i64.store`, 1 for the
`store8`s) is checked against the region the address resolves to
(`regionOf`):

* `.static base` — an ABSOLUTE const base (the return-area idiom).
  The caller supplies the registry `statics : List (Nat × Nat)` — the
  `(base, extent)` pairs (the demo's return-area = `(56, 8)`). The
  check: some registered region CONTAINS the byte range. An
  unregistered static base = FLAGGED (fail-closed: v1 has no way to
  know the extent, honest over silent).
* `.alloc rel` — an alloc'd record region (the walk-cursor /
  element-base shape), `rel` = the folded const offset from the
  tracked `base + const` idiom. The check: `rel + offset + width ≤
  stride`, where `stride` = `Layout.size` of the canonical-ABI user
  record — the PROVED 32 (`Layout.user_size`). The demo's four field
  stores (offsets 0/8/16/24, widths 8) end exactly at the stride =
  clean; a 4-wide store at offset 30 ends at byte 34 = FLAGGED.
* `.unchecked` — param/glob bases and `loaded`-pointer stores: the
  region's extent is NOT a static fact in v1 (a loaded pointer's
  VALUE is a runtime fact), so the range is not checked. The
  provenance walk still vouches for the pointer.

THE RANGE THEOREM: any store whose `rel + offset + width ≤` a
Layout-record's PROVED `size` is range-clean on a region of that size
(`layout_clean_of_size` — the corollary of `Layout.size`); the
concrete pins (`user_fields_clean`, the negative `rfl` pin) instance
it on the demo's record.

What the range lane does NOT re-prove: the FIELD-disjointness (the
same-offset clobber class — the watch-users `+0/+4` bug) is
OVERLAP-detection and is ALREADY PROVEN in `Layout.go_pairwise` (the
offsets are strictly increasing, so a field-i store cannot touch
field j > i). The range lane catches the ORTHOGONAL class: the
PAST-END / PAST-STRIDE stores (offset + width overrunning the
region's bound).

## Deliberate exclusions (v1)

* DYNAMIC extents are a RUNTIME fact: `$alloc`'s size arg is not
  tracked as a bound in v1 (only the record STRIDE bounds alloc
  regions); a store past a particular allocation's runtime size
  through a known pointer with a small offset passes. The audit is a
  static APPROXIMATION, sound-by-construction: every flag is
  conservative, every pass is vouched by a proved bound (the stride)
  or an unchecked-by-documentation class.
* `memory.copy` is range-UNCHECKED (its length is a runtime value;
  only its destination's PROVENANCE is vouched).
* Branch joins are CONSERVATIVE: a local set in one branch only (or to
  different abstract values per branch) degrades to unknown — the
  post-`if_` store through it is flagged (a false positive for
  emit-shaped joins that always run one branch; honest over silent).
* Control flow (br targets, loops' back edges) is ignored — the walk
  is one linear pass; a `local.set` before a `br` back-edge is seen in
  program order only.
* Loads are not checked (a garbage READ is a different bug class).
* `Func.locals` declarations are NOT consulted (WAT zero-inits them —
  a store through a declared-but-never-set local is exactly the bug
  class, so it stays flagged).
* The findings' index = the LEAF position in the depth-first
  traversal (structured forms do not consume an index).

Ownership: wasm-backend's audit lane (NOT Sem/Correct — the
translation-correctness lane owns those). Imports `Wat` + `Layout`
(the PROVED record extents the range lane checks against).
-/

namespace WasmBackend.Wat.Audit

/-! ## The abstract values -/

/-- The abstract value kinds the provenance walk tracks. -/
inductive Val where
  /-- A scalar constant (incl. an i32 base of a STATIC region) —
      the VALUE is tracked for the range lane's static-extent check. -/
  | const (n : Nat)
  /-- `call $alloc`'s result — a fresh region of runtime size. -/
  | allocPtr
  /-- A function parameter — the caller's object (`auditFunc` seeds). -/
  | param
  /-- A global's value — a tracked global root. -/
  | glob
  /-- `local.get n` — resolved through the env at USE time. -/
  | localRef (n : String)
  /-- A value loaded from abstract address `v` — the pointer-copy chain. -/
  | loaded (v : Val)
  /-- Pointer arithmetic; tracked ONLY as (known base, const offset). -/
  | plus (a b : Val)
  /-- Anything unmodeled: non-alloc call results, mul-based addresses,
      values left by structured forms, unbound locals. -/
  | opaque
  deriving BEq, Inhabited

/-- The local-provenance environment (assoc list; latest binding wins). -/
abbrev Env := List (String × Val)

/-- Memory-write ops (stores). Local to the audit — Wat.lean is
    read-only for this lane. -/
def memOpIsStore : MemOp → Bool
  | .i32store | .i64store | .i32store8 | .i64store8 => true
  | _ => false

/-- The byte width of a memory op (the range lane's store width:
    4 for `i32.store`, 8 for `i64.store`, 1 for the `store8`s). -/
def widthOf : MemOp → Nat
  | .i32load8u => 1 | .i32load => 4 | .i64load => 8
  | .i32store => 4 | .i64store => 8 | .i32store8 => 1 | .i64store8 => 1

/-! ## The known-root predicate -/

/-- Is this abstract value a scalar const? (the `plus` shape's test). -/
def isConstV : Val → Bool
  | .const _ => true
  | _ => false

/-- Is this abstract value an address whose PROVENANCE is vouchable?
    A known root vouches for the pointer; the RANGE is the range
    lane's separate check. Pointer arithmetic is tracked ONLY as
    (known base, const offset) — the `dst + 16` idiom; two pointers
    added (or a non-const offset: the `i * 8` array-index idiom) =
    unknown (v1). The fuel bounds the local-def/pointer-copy CHAIN
    depth (each `localRef`/`loaded` level consumes one; a deeper
    chain — impossible for any real body — degrades to unknown). -/
def knownRoot : Nat → Val → Env → Bool
  | 0, _, _ => false
  | _+1, .const _, _ => true
  | _+1, .allocPtr, _ => true
  | _+1, .param, _ => true
  | _+1, .glob, _ => true
  | k+1, .localRef n, env => knownRoot k (env.lookup n |>.getD .opaque) env
  | k+1, .loaded v, env => knownRoot k v env
  | k+1, .plus a b, env =>
      (knownRoot k a env && isConstV b) || (isConstV a && knownRoot k b env)
  | _, .opaque, _ => false

/-- The audit's chain-depth fuel (well above any real body's
    local-def/pointer-copy chain depth). -/
def fuel : Nat := 64

/-- The finding's reason, named by the failed address's shape. A
    `plus` descends to its non-const side (the unknown component). -/
def reasonOf (v : Val) : String :=
  match v with
  | .localRef n =>
      s!"store through local '{n}' of unknown provenance (never set from alloc/const/load/param)"
  | .loaded _ =>
      "store through a pointer loaded from an object of unknown provenance"
  | .plus a b => if isConstV a then reasonOf b else reasonOf a
  | _ => "store through an opaque/unmodeled value"

/-! ## The range model: regions and their KNOWN bounds -/

/-- The region an address resolves to (the range lane's classification). -/
inductive Rgn where
  /-- An ABSOLUTE const base — the extent = the caller's registry. -/
  | static (base : Nat)
  /-- An alloc'd record region; `rel` = the folded const offset from
      the tracked `base + const` idiom. The extent = the record's
      stride (`stride` = Layout's proved `size`). -/
  | alloc (rel : Nat)
  /-- No static extent in v1: param/glob bases, `loaded`-pointer
      stores (a loaded pointer's VALUE is a runtime fact), opaque. -/
  | unchecked

/-- The region classification of an abstract address (same fuel/chain
    discipline as `knownRoot`). -/
def regionOf : Nat → Val → Env → Rgn
  | 0, _, _ => .unchecked
  | _+1, .const n, _ => .static n
  | _+1, .allocPtr, _ => .alloc 0
  | _+1, .param, _ => .unchecked
  | _+1, .glob, _ => .unchecked
  | k+1, .localRef n, env => regionOf k (env.lookup n |>.getD .opaque) env
  | _+1, .loaded _, _ => .unchecked
  | k+1, .plus a b, env =>
      match regionOf k a env, regionOf k b env with
      | .static x, .static y => .static (x + y)
      | .alloc r, .static y => .alloc (r + y)
      | .static y, .alloc r => .alloc (r + y)
      -- anything mixed with an unbounded side (param/opaque) or a
      -- second pointer loses the bound — honest over silent
      | _, _ => .unchecked
  | _, .opaque, _ => .unchecked

/-- The record-stride bound for alloc regions: the canonical-ABI user
    record's size — Layout's PROVED `size` (`Layout.user_size` = 32).
    v1: ONE stride for every alloc-shaped region (the demo's record
    set); a different record's stride is v2 work with the emitter's
    type info threaded through. -/
def stride : Nat := Layout.size Layout.userTys

theorem stride_eq_32 : stride = 32 := rfl

/-- Does some registered static region CONTAIN the byte range
    `[base + off, base + off + w)`? -/
def staticFits (base off w : Nat) (statics : List (Nat × Nat)) : Bool :=
  statics.any fun (b, e) =>
    Nat.ble b (base + off) && Nat.ble (base + off + w) (b + e)

/-- The range check for one store: `none` = the byte range fits the
    region's known bound; `some msg` = the finding. -/
def rangeFinding (r : Rgn) (off w : Nat) (statics : List (Nat × Nat)) :
    Option String :=
  match r with
  | .static base =>
      if staticFits base off w statics then none
      else some s!"static-region overflow: the store's byte range [{base + off}, {base + off + w}) escapes every registered static region"
  | .alloc rel =>
      if rel + off + w ≤ stride then none
      else some s!"record-stride overflow: the store's offset {rel + off} + width {w} exceeds the record's size {stride}"
  | .unchecked => none

/-! ## The walk -/

/-- Conservative branch join: keep a local's provenance only where BOTH
    branches agree; everything else degrades to unknown (dropped —
    `knownRoot`'s `getD .opaque` supplies the unknown). -/
def joinEnv (a b : Env) : Env :=
  a.filterMap fun (n, v) =>
    match b.lookup n with
    | some v2 => if v == v2 then some (n, v) else none
    | none => none

-- The instruction-list SIZE (the walk's termination measure: every
-- recursive call descends into a strict subtree).
mutual
def sizeI : Instr → Nat
  | .i32const _ => 1 | .i64const _ => 1
  | .localget _ => 1 | .localset _ => 1 | .localtee _ => 1
  | .globalget _ => 1 | .globalset _ => 1
  | .call _ => 1 | .returncall _ => 1 | .callindirect _ => 1
  | .mem _ _ _ => 1 | .memcopy => 1 | .op _ => 1
  | .br _ => 1 | .brif _ => 1
  | .block _ b => 1 + sizeL b
  | .loop _ b => 1 + sizeL b
  | .if_ _ t e => 1 + sizeL t + sizeL e
  | .ret => 1 | .drop => 1 | .select => 1 | .unreach => 1
  | .raw _ => 1

def sizeL : List Instr → Nat
  | [] => 0
  | i :: is => sizeI i + sizeL is
end

theorem sizeI_pos : ∀ i : Instr, 0 < sizeI i := by
  intro i
  cases i <;> simp [sizeI, sizeL] <;> omega

/-- The walk: one linear pass, threading (findings, env, stack).
    The stack holds the abstract values of the WAT operand stack; the
    env maps locals to their defining abstract value. `idx` = the leaf
    index (structured forms do not consume one). `statics` = the
    static-region registry for the range lane. Structured bodies
    recurse with the SAME walk; the returned env threads on. -/
def go :
    List Instr → Nat → Env → List Val → List (Nat × String) →
    List (Nat × Nat) → (List (Nat × String) × Env × Nat)
  | [], idx, env, _, find, _ => (find, env, idx)
  | .i32const n :: rest, idx, env, stack, find, statics =>
      go rest (idx+1) env (.const n :: stack) find statics
  | .i64const n :: rest, idx, env, stack, find, statics =>
      go rest (idx+1) env (.const n :: stack) find statics
  | .localget n :: rest, idx, env, stack, find, statics =>
      go rest (idx+1) env (.localRef n :: stack) find statics
  | .localset n :: rest, idx, env, stack, find, statics =>
      match stack with
      | v :: s => go rest (idx+1) ((n, v) :: env) s find statics
      | [] => go rest (idx+1) ((n, .opaque) :: env) [] find statics
  | .localtee n :: rest, idx, env, stack, find, statics =>
      match stack with
      | v :: s => go rest (idx+1) ((n, v) :: env) (.localRef n :: s) find statics
      | [] => go rest (idx+1) ((n, .opaque) :: env) [.localRef n] find statics
  | .globalget _ :: rest, idx, env, stack, find, statics =>
      go rest (idx+1) env (.glob :: stack) find statics
  | .globalset _ :: rest, idx, env, stack, find, statics =>
      match stack with
      | _ :: s => go rest (idx+1) env s find statics
      | [] => go rest (idx+1) env [] find statics
  | .call "alloc" :: rest, idx, env, stack, find, statics =>
      go rest (idx+1) env (.allocPtr :: stack) find statics
  | .call _ :: rest, idx, env, stack, find, statics =>
      go rest (idx+1) env (.opaque :: stack) find statics
  | .returncall _ :: rest, idx, env, _stack, find, statics =>
      go rest (idx+1) env [] find statics
  | .callindirect _ :: rest, idx, env, stack, find, statics =>
      go rest (idx+1) env (.opaque :: stack) find statics
  | .mem op off _ :: rest, idx, env, stack, find, statics =>
      if memOpIsStore op then
        match stack with
        | _v :: a :: s =>
            -- TWO checks: provenance (the pointer) + range (the fit).
            -- The range check runs only on a vouched pointer — an
            -- unknown-provenance address has no classifiable region.
            let find :=
              if knownRoot fuel a env then
                match rangeFinding (regionOf fuel a env) off (widthOf op) statics with
                | none => find
                | some msg => find ++ [(idx, msg)]
              else find ++ [(idx, reasonOf a)]
            go rest (idx+1) env s find statics
        | _ =>
            go rest (idx+1) env []
              (find ++ [(idx, "unanalyzable store: abstract stack underflow")]) statics
      else
        -- a load: pop the address, push the loaded value
        match stack with
        | a :: s => go rest (idx+1) env (.loaded a :: s) find statics
        | [] => go rest (idx+1) env [.opaque] find statics
  | .memcopy :: rest, idx, env, stack, find, statics =>
      -- range-UNCHECKED (the length is a runtime value) — provenance only
      match stack with
      | _len :: _src :: d :: s =>
          let find := if knownRoot fuel d env then find
                      else find ++ [(idx, s!"memory.copy {reasonOf d}")]
          go rest (idx+1) env s find statics
      | _ =>
          go rest (idx+1) env []
            (find ++ [(idx, "unanalyzable memory.copy destination: abstract stack underflow")]) statics
  | .op o :: rest, idx, env, stack, find, statics =>
      match o with
      | .i32eqz =>
          match stack with
          | _ :: s => go rest (idx+1) env (.opaque :: s) find statics
          | [] => go rest (idx+1) env [.opaque] find statics
      | .i32add =>
          -- the ONE tracked arithmetic shape: (known base, const offset)
          match stack with
          | b :: a :: s => go rest (idx+1) env (.plus a b :: s) find statics
          | _ => go rest (idx+1) env [.opaque] find statics
      | _ =>
          match stack with
          | _ :: _ :: s => go rest (idx+1) env (.opaque :: s) find statics
          | _ => go rest (idx+1) env [.opaque] find statics
  | .br _ :: rest, idx, env, stack, find, statics =>
      go rest (idx+1) env stack find statics
  | .brif _ :: rest, idx, env, stack, find, statics =>
      match stack with
      | _ :: s => go rest (idx+1) env s find statics
      | [] => go rest (idx+1) env [] find statics
  | .block _ body :: rest, idx, env, stack, find, statics =>
      let (find1, env1, idx1) := go body idx env stack find statics
      go rest idx1 env1 stack find1 statics
  | .loop _ body :: rest, idx, env, stack, find, statics =>
      let (find1, env1, idx1) := go body idx env stack find statics
      go rest idx1 env1 stack find1 statics
  | .if_ res thenI elseI :: rest, idx, env, stack, find, statics =>
      let (findT, envT, idxT) := go thenI idx env stack find statics
      -- the else walk starts from the ENTRY env (a branch must not
      -- see the other branch's assignments); an empty elseI walks to
      -- the same env — the join below does the conservative merge
      let (findE, envE, idxE) := go elseI idxT env stack findT statics
      let envJ := joinEnv envT envE
      let stack := match res with | some _ => .opaque :: stack | none => stack
      go rest idxE envJ stack findE statics
  | .ret :: rest, idx, env, stack, find, statics =>
      match stack with
      | _ :: s => go rest (idx+1) env s find statics
      | [] => go rest (idx+1) env [] find statics
  | .drop :: rest, idx, env, stack, find, statics =>
      match stack with
      | _ :: s => go rest (idx+1) env s find statics
      | [] => go rest (idx+1) env [] find statics
  | .select :: rest, idx, env, stack, find, statics =>
      match stack with
      | _ :: _ :: _ :: s => go rest (idx+1) env (.opaque :: s) find statics
      | _ => go rest (idx+1) env [.opaque] find statics
  | .unreach :: rest, idx, env, _stack, find, statics =>
      go rest (idx+1) env [] find statics
  | .raw _ :: rest, idx, env, stack, find, statics =>
      go rest (idx+1) env stack
        (find ++ [(idx, "raw instruction — the audit cannot analyze a verbatim WAT line")]) statics
termination_by is => sizeL is
decreasing_by
  all_goals simp only [sizeL, sizeI]
  all_goals omega

/-! ## The audit -/

/-- THE AUDIT: `audit body statics` walks a function body's instruction
    list and reports one finding per memory write that fails the
    provenance check or the range check. `statics` = the static-region
    registry `(base, extent)` (the return-areas); default empty = every
    static-base store is flagged (fail-closed). The GOOD program = [];
    the BAD = the named findings. NOTE: with the bare list, function
    PARAMS are not knowable — a store through a param pointer is
    flagged; use `auditFunc` when the `Wat.Func` (and its params) are
    at hand. -/
def audit (body : List Instr) (statics : List (Nat × Nat) := []) :
    List (Nat × String) :=
  (go body 0 [] [] [] statics).1

/-- Func-level audit: the params are seeded as known roots (the
    caller's objects cross the call boundary with provenance). -/
def auditFunc (f : Func) (statics : List (Nat × Nat) := []) :
    List (Nat × String) :=
  let env : Env :=
    f.params.map fun p =>
      (match p.name with | some n => n | none => "", .param)
  (go f.body 0 env [] [] statics).1

/-! ## The theorems -/

/-- The trivial soundness-shape theorem: the empty program has no
    findings (the audit is a CHECKER — the tests are the evidence for
    the rest; only the trivially-provable is a theorem here). -/
theorem audit_nil : audit [] = [] := by
  simp [audit, go]

/-- A store inside a registered static region is range-clean (the
    containment check is exactly the two inequalities). -/
theorem staticFits_of_containment {base off w b e : Nat}
    {statics : List (Nat × Nat)}
    (hm : (b, e) ∈ statics) (h1 : b ≤ base + off) (h2 : base + off + w ≤ b + e) :
    staticFits base off w statics = true := by
  unfold staticFits
  exact List.any_eq_true.2 ⟨(b, e), hm, by
    simp only [Nat.ble_eq, Bool.and_eq_true]
    exact ⟨h1, h2⟩⟩

/-- The range check on an alloc region is exactly the stride
    inequality — a store that fits the bound is range-clean. -/
theorem rangeFinding_alloc_clean (rel off w : Nat)
    (h : rel + off + w ≤ stride) :
    rangeFinding (.alloc rel) off w [] = none := by
  simp only [rangeFinding]
  rw [if_pos h]

/-- THE RANGE-CLEAN COROLLARY (the range lane's statement of the
    seam-contract's #6): any store whose `rel + offset + width` fits a
    Layout-record's PROVED `size` is range-clean on an alloc region of
    that size. The bound-check IS the Layout size-theorem's
    corollary — nothing new is assumed. -/
theorem layout_clean_of_size (ts : List SchemaLang.Ty) (rel off w : Nat)
    (h : rel + off + w ≤ Layout.size ts) (he : Layout.size ts = stride) :
    rangeFinding (.alloc rel) off w [] = none := by
  rw [he] at h
  exact rangeFinding_alloc_clean rel off w h

/-- The demo's user record: all four PROVED field stores (offsets
    0/8/16/24, widths 8 — `Layout.user_offsets`/`Layout.user_size`)
    are range-clean; the last ends EXACTLY at the stride
    (24 + 8 = 32). -/
theorem user_fields_clean :
    rangeFinding (.alloc 0) 0 8 [] = none ∧
    rangeFinding (.alloc 0) 8 8 [] = none ∧
    rangeFinding (.alloc 0) 16 8 [] = none ∧
    rangeFinding (.alloc 0) 24 8 [] = none := by decide

/-- The negative's pin: a 4-wide store at offset 30 ends at byte 34 —
    past the user record's PROVED 32-byte stride = FLAGGED (computed). -/
example : ∃ msg, rangeFinding (.alloc 0) 30 4 [] = some msg := ⟨_, rfl⟩

end WasmBackend.Wat.Audit
