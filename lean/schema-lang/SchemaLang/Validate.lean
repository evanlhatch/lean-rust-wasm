/-
# SchemaLang.Validate — the schema-INDEXED predicate layer

The template's differentiator: the user writes an invariant over their
schema's records; the misspelled field = an ELABORATION error; the
compiled validator runs at the host's boundary.

Design (a layer ABOVE the closed `Ty` universe — no new ctors):

- `VExpr (s : List Field) (t : Ty)` — the indexed expression: field refs
  are `HasCol`-typed (the misspelled name = NO instance = the
  elaboration error), u64 literals, the comparisons (>, ==), &&, and
  the SPEC-level `strlen` (see Phase 2). MINIMAL by design — `id > 0`
  is the driving example.
- `RowVals` — the value-aligned row: one `Value` per field, in schema
  order, indexed BY the schema.
- `evalV` — the boxed evaluator (`VExpr → RowVals → Value t`) — the
  SPEC reading, consumed by the schema-lang tests.
- `evalU`/`evalB` — the RAW-scalar evaluators — the COMPILED reading:
  `evalU` yields bare `UInt64`; `evalB` yields the 0/1 u64 (Bool is
  computed in u64 — see `boolToU64`). WHY RAW: the guest's RC pass
  turns ctor-after-dec (a matched-away `Value` box feeding a fresh
  ctor) into `reset/reuse` join-point code the wasm backend does not
  emit — the raw scalars construct NOTHING, so the pass finds no
  firing site. The tie between the readings is pinned by the executed
  equivalence in Tests; the differential duel is the end-to-end
  authority.
- `validates` — the registered validator's body (`evalB == 1`).

The CLOSURE-FREE rule (the `_lam_0._boxed` lesson): the field
extraction is a `ColPath` — a `here`/`there` CONSTRUCTOR PATH built at
elaboration from the `HasCol` instance — NOT a stored function. A
class-field getter compiles to a pap trampoline whose lambda lives
under the instance decl; the instance is elaboration-time only (not a
backend target), so the call dangles. Constructor data has no such
tail: `ColPath.get` is an ordinary recursive target.

Ownership: this module (the validator lane). The wasm backend compiles
`evalU`/`evalB`/`validates`/`ColPath.get` as ordinary targets — they are
marked `@[guest_std]` (the guest-mark registry; the backend's manifest
fold — GenMain.lean's `targetDeclsOf` — picks marked decls up, no
hand-list). `evalV` stays UNMARKED (the boxed reading constructs `Value`
boxes the guest cannot compile); the `user-valid` differential duel
rows (GenMain's oracle) are the end-to-end proof.

Deliberate exclusions: option's is-some, string/order comparisons,
arithmetic on anything but u64 — they join when a schema needs them
(the constructors extend exhaustively; the universe stays closed).
No runtime ordinals: the extraction rides the path constructors — the
guest never boxes a `Nat` (the `HasField.index` route would compile to
GMP objects).

## Phase 2 — the validators' range (the honest scoping)

The STRLEN node LANDED — the fix-(ii) shape (the spec-level
primitive): the boxed `Value .string` carries the Lean `String`
itself, so `evalV` computes the length IN the evaluator with NO std
import (the acyclic edge: schema-lang cannot import
`GuestlangStd.strlen` one package up). The COMPILED path is WIRED:
`evalU`'s `.strlen` arm reads the row's boxed string and returns the
RAW length via `string_len` (below) — the (ptr,len) pair's SECOND
half (the guest string object's len slot @+8, the runtime primitive
`$string_len`'s exact read). The old LOUD-0 marker is gone; a
registered validator over `strlen` now evaluates the REAL length in
the raw reading, and `userComplete` (GuestImpl) rides the
VExpr-strlen check (`userNameLenCheck`, now marked) — the duel's
user-complete rows are the end-to-end regression. Length semantics:
Lean's `String.length` (chars) = the std `$string_len` (bytes) on
ASCII — the StrOps v1 byte/char stance.

The VARIANT family LANDED (Phase 3, below) at the SPEC level: the
variant-row (`VRow` — the fired tag's position + the payload at it),
the tag resolution (`HasCase`/`CaseTag` — the misspelled case is an
elaboration error), the arm-typed SOME-payload accessor
(`HasPayload`/`CasePath` — a NONE-payload case has NO accessor BY
CONSTRUCTION), the second expression family (`VCase`) and its
evaluator (`evalCase`), tied to the demo by the case-soundness pin
(`evalCase_here_sound`). The COMPILED lane stays the hand `match`
(the DECISION in Phase 3's header): a raw variant evaluator needs the
discr + joined-payload scalar level the backend does not emit (the
canonical ABI's f64→i64 payload join makes the slot non-scalar — the
demo's f64 arm is deliberately UNREAD), and the hand body's `match`
IS the payload access in the shape the backend already emits (the
tag case + the payload sproj — the `area` ctor-dispatch pattern).
Flip this when the backend emits the variant raw lane.

The differential duel rows (GenMain's oracle) are the authority for
BOTH lanes; the validator pattern = the registered compiled fn, the
GADT = the scalar-condition story (Phase 3's family = the SPEC-side
story, the strlen precedent).
-/

import Lean
import SchemaLang.Field
import CodegenCore.GuestGate
import LintKit

namespace SchemaLang

/-! ## The value-aligned row -/

/-- One `Value` per field of the schema `s`, in schema order — the
    runtime half of a record, indexed BY the schema (a row for
    `["id", "name"]` cannot hold the values of `["name", "id"]`). -/
inductive RowVals : List Field → Type where
  | nil : RowVals []
  | cons : {f : Field} → {fs : List Field} → Value f.ty → RowVals fs →
      RowVals (f :: fs)

/-! ## The field path — the resolution's RUNTIME half -/

/-- `ColPath n t fs` — the CONSTRUCTOR path from a schema's head to the
    field `n : t`: `here` = the head field IS `⟨n, t⟩` (the list index
    says so — the value needs no cast); `there` = it lives deeper. Pure
    data: the wasm backend emits the walk as ordinary tag cases, no
    closure, no dictionary. -/
inductive ColPath (n : String) (t : Ty) : List Field → Type where
  | here : ColPath n t (({ name := n, ty := t }) :: fs)
  | there : {f : Field} → {fs : List Field} → ColPath n t fs →
      ColPath n t (f :: fs)

/-- Walk the path: the field's value, out of the schema-aligned row.
    `@[guest_std]`: the compiled field extraction (the guest-mark
    registry — the backend's manifest fold compiles it). -/
@[guest_std]
def ColPath.get : ColPath n t fs → RowVals fs → Value t
  | .here, .cons v _ => v
  | .there p, .cons _ vs => p.get vs

/-! ## The field resolution's ELABORATION half -/

/-- `HasCol` — `HasField`'s companion: the SAME two-parameter-class
    idiom (the name binds in TWO positions — the record's head field AND
    the query — so a misspelled name finds no instance and fails at
    elaboration), but the class carries the extraction PATH: head
    instance answers `here`; the step instance prepends `there`. The
    instance is elaboration-time only — the path (data) is what runs. -/
class HasCol (fs : List Field) (name : String) (t : outParam Ty) where
  /-- The structural path to the field. -/
  path : ColPath name t fs

/-- Head match: the queried name IS the head field's name and the
    queried type IS its type. (Priority: same-name shadowing resolves
    to the FIRST field.) -/
@[instance 100]
def hasColHead {n : String} {t : Ty} {fs : List Field} :
    HasCol ({ name := n, ty := t } :: fs) n t :=
  ⟨.here⟩

/-- Step: the name lives deeper — prepend `there`. -/
@[instance]
def hasColTail {f : Field} {fs : List Field} {n : String} {t : Ty}
    [h : HasCol fs n t] : HasCol (f :: fs) n t :=
  ⟨.there h.path⟩

/-! ## The indexed expression -/

/-- The schema-indexed expression over the record `s`. The `t` index is
    the expression's schema type — a `gt` branch CANNOT compare a
    string. Field refs carry the `ColPath` data (built by `colOf` from
    the `HasCol` evidence): the misspelled variant is an elaboration
    error (no instance), and the path rides the extraction. -/
inductive VExpr (s : List Field) : Ty → Type where
  /-- A field reference: the name (diagnostics) + the extraction path. -/
  | col (n : String) {t : Ty} (p : ColPath n t s) : VExpr s t
  /-- A u64 literal. -/
  | lit (v : UInt64) : VExpr s .u64
  /-- `a > b` on the u64 scalars. -/
  | gt (a b : VExpr s .u64) : VExpr s .bool
  /-- `a == b` on the u64 scalars. -/
  | eq (a b : VExpr s .u64) : VExpr s .bool
  /-- Conjunction on the booleans (the evaluator matches — no core
      `Bool.and` call in the compiled path). -/
  | and (a b : VExpr s .bool) : VExpr s .bool
  /-- `strlen e` — the operand string's length as a u64. The boxed
      `Value .string` carries the Lean `String`, so `evalV` reads the
      length in place — no std import, the acyclic edge stays clean.
      COMPILED too: `evalU`'s arm reads the same box's length via the
      raw `string_len` (the header's Phase 2 — the wire-up). -/
  | strlen (e : VExpr s .string) : VExpr s .u64
  /-- Negation (the ≤-shaped invariants: `not (gt x y)` = x ≤ y —
      the dogfood's rollout ≤ 100 gate demanded it). -/
  | not (e : VExpr s .bool) : VExpr s .bool

/-- The field-ref BUILDER — where the `HasCol` instance search happens.
    Misspell the name and THIS call fails to elaborate. `@[inline]`: the
    builder folds away — the VExpr constant must be pure ctor data (a
    call to the builder compiles to a specialized spec decl the backend
    never emits — the `colOf._at_.userCheck.spec_0` lesson). -/
@[inline]
def VExpr.colOf (n : String) {t : Ty} [h : HasCol s n t] : VExpr s t :=
  .col n h.path

/-! ## The evaluators -/

/-- The boxed (SPEC) evaluator: expression + row → the field's value.
    Total by construction: the GADT indices make every match
    exhaustive at the type's own constructor set. NOT compiled — the
    guest bans the ctor-after-dec shape (see the header). -/
def evalV : VExpr s t → RowVals s → Value t
  | .col _ p, row => p.get row
  | .lit v, _ => .u64 v
  | .gt a b, row =>
      match evalV a row, evalV b row with
      | .u64 x, .u64 y => .bool (x > y)
      | _, _ => .bool false
  | .eq a b, row =>
      match evalV a row, evalV b row with
      | .u64 x, .u64 y => .bool (x == y)
      | _, _ => .bool false
  | .and a b, row =>
      match evalV a row with
      | .bool x =>
          match x, evalV b row with
          | true, .bool y => .bool y
          | _, _ => .bool false
      | _ => .bool false
  | .strlen e, row =>
      match evalV e row with
      | .string s => .u64 s.length.toUInt64
      | _ => .u64 0
  | .not e, row =>
      match evalV e row with
      | .bool b => .bool (!b)
      | _ => .bool false

/-- The RAW string length: the (ptr,len) pair's SECOND half. The Lean
    body (`String.length` → chars) is the oracle ONLY — the decl is
    never a compile target (unmarked, and the root name falls outside
    every target's namespace fold), so the compiled callers' `call
    $string_len` resolves to the SPLICED RUNTIME's primitive (the
    `i32.load offset=8` on the string object) — the same name
    resolution the `GuestlangStd.strlen`/`strcat` intrinsics ride
    (`WasmBackend.stdOp?`). The root NAME IS THE CONTRACT (`string_len`
    below, outside the namespace). Byte-length ≠ char-length off
    ASCII (the StrOps v1 stance). -/
@[nolint linter.guestlang.dupDefBodies "deliberate mirror of root `string_len` (below): the namespaced copy is the oracle compiled into evalU's strlen arm (`$SchemaLang.string_len`); the ROOT copy is the spliced-runtime wire-up contract — identical bodies keep oracle == contract"]
def string_len (s : String) : UInt64 := s.length.toUInt64

/-- The RAW u64 evaluator (the compiled reading): operands surface as
    bare `UInt64` — the `Value .u64` box is unboxed and dropped, and
    NOTHING is constructed (the guest's reset/reuse pass finds no
    firing site). The strlen arm reads the row's boxed string via the
    root-namespace `string_len` (above — the namespace reopens for the
    evaluators; a root name is visible inside). -/
@[guest_std]
def evalU : VExpr s .u64 → RowVals s → UInt64
  | .lit v, _ => v
  | .col _ p, row =>
      match p.get row with
      | .u64 x => x
      | _ => 0
  -- the strlen node's RAW reading (WIRED — the header's Phase 2): the
  -- operand is a field ref (the only `.string`-typed VExpr shape), the
  -- row's string box → the raw length via `string_len` — the
  -- (ptr,len) pair's second half (the runtime `$string_len` read).
  | .strlen e, row =>
      match e with
      | .col _ p =>
          match p.get row with
          | .string s => string_len s
          | _ => 0
      | _ => 0
  | _, _ => 0

/-- Bool → the 0/1 u64 the raw evaluator computes in (constant arms —
    a Bool-valued bare-return arm would hit `resultTyOf`'s i64 default
    in the frozen backend — the `evalB._redArg` lesson). -/
@[guest_std]
def boolToU64 : Bool → UInt64
  | true => 1
  | false => 0

/-- The RAW evaluator (the compiled reading): a `.bool`-shaped
    expression computes to the 0/1 u64 (the registered validator's
    `validates` projects back to Bool with `== 1`). NO Bool matches in
    the compiled path: conjunction = the 0/1 MULTIPLICATION (UInt64.mul
    — a binop the backend emits); the comparisons route through
    `boolToU64` (constant arms). The scalar-match arm shapes the backend
    can't type (bare variable-returns) never occur. -/
@[guest_std]
def evalB : VExpr s .bool → RowVals s → UInt64
  | .col _ p, row =>
      match p.get row with
      | .bool b => boolToU64 b
      | _ => 0
  | .gt a b, row => boolToU64 (evalU a row > evalU b row)
  | .eq a b, row => boolToU64 (evalU a row == evalU b row)
  | .and a b, row => evalB a row * evalB b row
  -- the negation on the 0/1 raw reading: 1-x wraps safely on {0,1}
  | .not e, row => 1 - evalB e row
  | _, _ => 0

/-- The registered validator's body: a `.bool`-shaped expression over a
    schema-aligned row → Bool (the raw evaluator's 0/1 → the Bool
    verdict; the projection = a binop, no match). -/
@[guest_std]
def validates (e : VExpr s .bool) (row : RowVals s) : Bool :=
  evalB e row == 1

/-! ## Phase 3 — the variant family (the second indexed-expr family)

The honest-skip's scope, RESOLVED at the spec level. The second
family's full inventory, as predicted: its own variant-row type, its
own resolution classes, its own expression level, its own evaluator —
and the pin.

THE COMPILED-LANE DECISION (the strlen precedent, applied): the VCase
family is SPEC-LEVEL ONLY. `evalCase` constructs `Value` boxes (the
boxed reading — `evalV`'s reason, unmarked), and a RAW variant
evaluator would need the discr + joined-payload scalar level the
backend does not emit (the canonical ABI's f64→i64 payload join makes
the slot non-scalar — the demo's f64 arm is deliberately UNREAD). So
the registered variant validator (`GuestImpl.orderErrorValid`) KEEPS
the hand `match` — the tag case + the payload sproj is the shape the
backend already emits — and the VCase form (`orderErrorSpecValid`)
rides beside it, eval-tested against the mirrored case list in the
schema-lang tests.

Payload-access rules, BY CONSTRUCTION:
- SOME-payload cases get the arm-typed accessor (`payload`, its type
  index = the case's payload type); a NONE-payload case has NO
  accessor (`CasePath.here` exists only over `some t` heads) — the
  read fails at ELABORATION, never at runtime.
- The MISS case (the row's fired tag is NOT the queried arm) yields
  the 0-analog (`HasPayload.miss`) — an unfired slot's read is
  meaningless, so the guarded-usage pattern (`isCase` ∧ `payload`)
  discards it. The 0-analog exists for the valueable scalar fragment
  (u64/f64/bool/string); other payload types get no accessor yet
  (additive — the instances extend, the universe stays closed).
- `.ty`-ref payloads: a named ref has NO `Value` ctor (the boxed lane
  cannot value it), so those arms get no instance — the honest skip.
-/

/-- The payload's type-driven view: a NONE-payload case carries no
    value (the unit — nothing to access); a SOME-payload case carries
    the boxed `Value t`. REDUCIBLE: the `VRow`/`CasePath` GADT
    patterns must see through it at implicit transparency (the plain
    def blocked the equation lemmas' reduction — the `here`-payload
    elaboration stuck). -/
@[reducible]
def PayloadOf : Option Ty → Type
  | none => Unit
  | some t => Value t

/-- The variant-row (the runtime half of a variant value, indexed BY
    the case list): the fired tag's POSITION + that position's
    payload. `here` = the head case fired (its payload, typed by the
    head's Option Ty); `there` = a deeper case fired. A row for the
    case list `[a, b, c]` cannot name a case the item lacks, and the
    payload cannot detach from its position. SPEC-LEVEL: the compiled
    adapter's re-box (`GuestImpl.orderErrorRow`) feeds the eval only. -/
inductive VRow : List VariantCase → Type where
  | here : {n : String} → {t : Option Ty} → {cs : List VariantCase} →
      PayloadOf t → VRow ((n, t) :: cs)
  | there : {n : String} → {t : Option Ty} → {cs : List VariantCase} →
      VRow cs → VRow ((n, t) :: cs)

/-- Does the row's fired tag name `m`? The walk pairs the case list
    (the names) with the row (the position) — no runtime ordinals. -/
def VRow.isName : {cs : List VariantCase} → VRow cs → String → Bool
  | ((n, _) :: _), .here _, m => n == m
  | (_ :: _), .there r, m => r.isName m

/-- The tag position of case `n` — pure data, the `ColPath` pattern.
    `here` binds BOTH name positions (the head case's name AND the
    query), so a misspelled case finds no instance and fails at
    ELABORATION (the `HasCol` idiom over the case list). -/
inductive CaseTag (n : String) : List VariantCase → Type where
  | here : {t : Option Ty} → {cs : List VariantCase} →
      CaseTag n ((n, t) :: cs)
  | there : {m : String} → {u : Option Ty} → {cs : List VariantCase} →
      CaseTag n cs → CaseTag n ((m, u) :: cs)

/-- `HasCase` — the tag-test's resolution evidence. Elaboration-time
    only; the eval compares names (`VRow.isName`), so the class
    carries no runtime tail. -/
class HasCase (cs : List VariantCase) (n : String) where
  tag : CaseTag n cs

/-- Head match (priority: same-name shadowing resolves to the FIRST
    case — the `hasColHead` rule). -/
@[instance 100]
def hasCaseHead {n : String} {t : Option Ty} {cs : List VariantCase} :
    HasCase ((n, t) :: cs) n := ⟨.here⟩

/-- Step: the case lives deeper. -/
@[instance]
def hasCaseTail {n m : String} {u : Option Ty} {cs : List VariantCase}
    [h : HasCase cs n] : HasCase ((m, u) :: cs) n := ⟨.there h.tag⟩

/-- The SOME-payload case's path: `here` exists ONLY over a
    `(n, some t)` head — a NONE-payload case has no accessor BY
    CONSTRUCTION (the honest NONE rule; the misspelled name fails the
    same way — no instance). -/
inductive CasePath (n : String) (t : Ty) : List VariantCase → Type where
  | here : {cs : List VariantCase} → CasePath n t ((n, some t) :: cs)
  | there : {m : String} → {u : Option Ty} → {cs : List VariantCase} →
      CasePath n t cs → CasePath n t ((m, u) :: cs)

/-- `HasPayload` — the arm-typed accessor's evidence: the extraction
    path PLUS the 0-analog (`miss`) the evaluator yields when the
    fired tag is NOT this arm. Payload types without a 0-analog (e.g.
    a `.ty` ref — no `Value` ctor) get no instance: the accessor
    fails to elaborate. Elaboration-time only (the ColPath
discipline — the PATH is data, the class is not a backend target). -/
class HasPayload (cs : List VariantCase) (n : String) (t : outParam Ty) where
  path : CasePath n t cs
  miss : Value t

/-- The 0-analog instances: the valueable scalar fragment. Each is a
    head match over a `some`-payload head of its OWN type — add a
    fragment type by adding one head instance (the universe stays
    closed; the extension is additive). -/
@[instance 100]
def hasPayloadHead_u64 {n : String} {cs : List VariantCase} :
    HasPayload ((n, some .u64) :: cs) n .u64 := ⟨.here, .u64 0⟩

@[instance 100]
def hasPayloadHead_f64 {n : String} {cs : List VariantCase} :
    HasPayload ((n, some .f64) :: cs) n .f64 := ⟨.here, .f64 0⟩

@[instance 100]
def hasPayloadHead_bool {n : String} {cs : List VariantCase} :
    HasPayload ((n, some .bool) :: cs) n .bool := ⟨.here, .bool false⟩

@[instance 100]
def hasPayloadHead_string {n : String} {cs : List VariantCase} :
    HasPayload ((n, some .string) :: cs) n .string := ⟨.here, .string ""⟩

/-- Step: the case lives deeper (any head shape — the payload type
    rides the recursion). -/
@[instance]
def hasPayloadTail {n m : String} {u : Option Ty} {cs : List VariantCase}
    {t : Ty} [h : HasPayload cs n t] : HasPayload ((m, u) :: cs) n t :=
  ⟨.there h.path, h.miss⟩

/-! ### The variant expression -/

/-- The variant-indexed expression over the case list `cs`. The `t`
    index is the expression's schema type. The `isCase` tag test and
    the arm-typed `payload` accessor are the NEW leaves; the scalar
    spine (`litU`/`gt`/`and`/`not`) mirrors `VExpr`'s shape over the
    second subject. A misspelled case name — or a payload access on a
    NONE-payload case — fails at the NODE (no instance): the
    elaboration gate. -/
inductive VCase (cs : List VariantCase) : Ty → Type where
  /-- The tag test: the row's fired case IS `n` (the Bool). -/
  | isCase (n : String) [h : HasCase cs n] : VCase cs .bool
  /-- The arm-typed payload of the SOME-payload case `n`. -/
  | payload (n : String) {t : Ty} [h : HasPayload cs n t] : VCase cs t
  /-- A u64 literal. -/
  | litU (v : UInt64) : VCase cs .u64
  /-- `a > b` on the u64 scalars. -/
  | gt (a b : VCase cs .u64) : VCase cs .bool
  /-- Conjunction. -/
  | and (a b : VCase cs .bool) : VCase cs .bool
  /-- Negation (the validator's refusal shape). -/
  | not (a : VCase cs .bool) : VCase cs .bool

/-- The payload walk: the path against the row. `some` iff the row's
    fired tag IS the queried arm (the four position combinations are
    total: any divergence → none → the evaluator's 0-analog). The
    indices are AUTO-BOUND (the `evalV` style — the matcher splits on
    the ctors, so the equations reduce definitionally). -/
def CasePath.payloadOf : CasePath n t cs → VRow cs → Option (Value t)
  | .here, .here p => some p
  | .here, .there _ => none
  | .there _, .here _ => none
  | .there p, .there r => p.payloadOf r

/-- The SECOND evaluator (the variant-row subject): expression + row →
    the case's value. Total by construction (the same GADT-index
    argument as `evalV`, whose auto-bound-implicit style this mirrors —
    the matcher splits on the ctors, so the equations reduce). SPEC-
    LEVEL ONLY — UNMARKED (it constructs `Value` boxes; the guest's
    ctor-after-dec ban — the `evalV` reason). -/
def evalCase : VCase cs t → VRow cs → Value t
  | @VCase.isCase _ n _, row => .bool (row.isName n)
  | @VCase.payload _ _ _ h, row =>
      match h.path.payloadOf row with
      | some v => v
      | none => h.miss
  | .litU v, _ => .u64 v
  | .gt a b, row =>
      match evalCase a row, evalCase b row with
      | .u64 x, .u64 y => .bool (x > y)
      | _, _ => .bool false
  | .and a b, row =>
      match evalCase a row, evalCase b row with
      | .bool x, .bool y => .bool (x && y)
      | _, _ => .bool false
  | .not a, row =>
      match evalCase a row with
      | .bool x => .bool (!x)
      | _ => .bool false

/-- The variant validator's body (the `validates` analog over the
    second family): the spec-level Bool projection. The compiled lane
    stays the hand `match` (the Phase-3 decision) — there is NO raw
    reading to mirror, so no 0/1 detour. -/
def validatesCase (e : VCase cs .bool) (row : VRow cs) : Bool :=
  match evalCase e row with
  | .bool b => b
  | _ => false

/-- THE CASE-SOUNDNESS PIN (the general u64 shape): when the fired tag
    IS the queried arm, the tag test answers true AND the accessor
    yields the row's OWN payload — not the 0-analog. The payload
    conjunct is `rfl` (the paths line up by construction); the tag
    conjunct is `n == n` after the walk. The tests execute the pin on
    the demo rows. -/
theorem evalCase_here_sound (n : String) (cs : List VariantCase)
    (p : Value .u64) :
    evalCase (VCase.isCase (cs := (n, some .u64) :: cs) n) (.here p)
      = .bool true
    ∧ evalCase (VCase.payload (cs := (n, some .u64) :: cs) n) (.here p) = p := by
  apply And.intro
  · show Value.bool (n == n) = Value.bool true
    rw [beq_self_eq_true]
  · rfl

/-! ## The `[inv| …]` surface syntax — the DSL embedding (the ch. 8 pattern)

The Metaprogramming-in-Lean book's chapter 8 ("Embedding DSLs by
Elaboration"), IMP shape: a `declare_syntax_cat` for the invariant
language + a RECURSIVE elaborator into the `VExpr` constructors + a
`term`-level quoter. ADDITIVE: the `VExpr` ctors and the evaluators
above are untouched — this section only SPELLS them.

- The field-ref leaf rides `VExpr.colOf` — the `HasCol` instance
  search happens at the elaboration site, so the MISSPELLED field is a
  BUILD error (the same gate the hand spelling has, now through the
  syntax).
- Precedence: the book's `:50/:40` shape — `&&` binds tighter than
  `||`, the comparisons (`>`, `==`) tighter than both; the right
  operand parses at prec+1 (left associativity, the `infixl` recipe).
- `||` has NO VExpr constructor — it elaborates to the De Morgan form
  `not (and (not a) (not b))` (exact on Bool; no ctor added, the
  universe stays closed). `!` is the `not` node's spelling — it exists
  so the unexpanders (below) can round-trip EVERY tree the syntax can
  build.
- The unexpanders are the book's Pretty Printing pattern: per-ctor
  `@[app_unexpander]`, each matching the delaborated form INSIDE the
  pattern (the children arrive already unexpanded to `[inv| … ]`
  terms — the inner syntax is unwrapped and re-spliced, parenthesized
  when the child's top node binds looser than the operand position
  demands — the tree parses back to the SAME constructor tree).

No `set_option hygiene false`: the book's `myid` case is about a macro
EXPOSING a local name through hygiene marks; the unexpanders here run
at pp-time and construct RAW syntax (no marks), and every other name
is a global constant (resolved through marks).
-/

open Lean in
/-- The invariant language's syntax category (the book's `arith`/
`boolean` shape, one cat). -/
declare_syntax_cat vexpr

-- the atoms (atom-like rules default to `maxPrec` — parseable at any
-- operand position)
scoped syntax ident : vexpr
scoped syntax num : vexpr
scoped syntax "strlen" noWs "(" ident ")" : vexpr
scoped syntax "(" vexpr ")" : vexpr
scoped syntax "!" vexpr:65 : vexpr
-- the operators: the book's `:50/:40` precedence pattern (higher
-- number = tighter); the right operand at prec+1 = left assoc
scoped syntax:60 vexpr " > " vexpr:61 : vexpr
scoped syntax:60 vexpr " == " vexpr:61 : vexpr
scoped syntax:50 vexpr " && " vexpr:51 : vexpr
scoped syntax:40 vexpr " || " vexpr:41 : vexpr

/-- The term-level embedding: `def myCheck : VExpr s .bool :=
[inv| id > 0 && strlen(name) > 3]`. -/
scoped syntax "[inv| " vexpr " ]" : term

open Lean in
/-- The string literal as a `Term` (the colOf argument). -/
private def strLitTerm (s : String) : Term := ⟨Syntax.mkStrLit s⟩

open Lean in
/-- The schema index out of an operand's type (`VExpr s t` → `s`). -/
private def vexprSchemaOf? (ty : Expr) : Option Expr :=
  match ty with
  | .app (.app _ s) _ => some s
  | _ => none

open Lean Elab Meta Term in
/-- Force the operand's type INDEX (the ctor's requirement — this pins
the field-ref's type BEFORE the postponed instance synth runs, so the
misspelling error renders the CONCRETE type, never a raw mvar). -/
private def forceIndex (s : Expr) (t : Expr) (e : Expr) : TermElabM Unit := do
  let te ← inferType e
  let want := mkAppN (mkConst ``SchemaLang.VExpr) #[s, t]
  unless (← isDefEq te want) do
    throwError "[inv| … ]: operand index mismatch (expected {t})"

open Lean Elab Meta Term in
/-- Unify the operands' types (this THREADS the schema mvar through the
node — the `mkAppM` role) and return the schema. -/
private def unifyOperands (a b : Expr) : TermElabM Expr := do
  let ta ← inferType a
  let tb ← inferType b
  unless (← isDefEq ta tb) do
    throwError "[inv| … ]: operand type mismatch ({ta} vs {tb})"
  match vexprSchemaOf? ta with
  | some s => return s
  | none => throwError "[inv| … ]: operand is not a VExpr"

open Lean Elab Term in
/-- The field-ref leaf, shared by the ident and `strlen` arms: the
REAL term elaborator on quoted `colOf` syntax (see `elabVExpr`'s doc
for why the leaf cannot ride `mkAppM`). -/
private def elabFieldLeaf (n : TSyntax `ident) : TermElabM Expr := do
  Term.elabTerm (← `(SchemaLang.VExpr.colOf $(strLitTerm n.getId.toString))) none

open Lean Elab Meta Term in
/-- The recursive elaborator (the book's `elabIMPExpr` mirror):
`vexpr` syntax → the `VExpr` constructor tree via `mkAppM`. One
deliberate deviation from the naive `MetaM` shape: the field-ref leaf
is elaborated by the REAL term elaborator on quoted `colOf` syntax —
`mkAppM` synthesizes instance arguments EAGERLY (`mkAppMFinal`), which
fails against the still-open schema metavariable even for CORRECT
spellings; the real elaborator POSTPONES the instance search until the
expected type names the schema. The gate is unchanged: a misspelled
field fails to synthesize `HasCol` HERE. -/
partial def elabVExpr : TSyntax `vexpr → TermElabM Expr
  | `(vexpr| $n:ident) => elabFieldLeaf n
  | `(vexpr| $v:num) => do
      let e ← Term.elabTerm v (some (mkConst ``UInt64))
      -- the literal's schema is a fresh mvar — the PARENT's operand
      -- unification (or the expected type at the root) assigns it
      let s ← mkFreshExprMVar none
      return mkAppN (mkConst ``SchemaLang.VExpr.lit) #[s, e]
  | `(vexpr| strlen($n:ident)) => do
      let e ← elabFieldLeaf n
      let te ← inferType e
      let some s := vexprSchemaOf? te |
        throwError "[inv| … ]: strlen operand is not a VExpr"
      forceIndex s (mkConst ``SchemaLang.Ty.string) e
      return mkAppN (mkConst ``SchemaLang.VExpr.strlen) #[s, e]
  | `(vexpr| $a > $b) => do
      let a ← elabVExpr a
      let b ← elabVExpr b
      let s ← unifyOperands a b
      forceIndex s (mkConst ``SchemaLang.Ty.u64) a
      forceIndex s (mkConst ``SchemaLang.Ty.u64) b
      return mkAppN (mkConst ``SchemaLang.VExpr.gt) #[s, a, b]
  | `(vexpr| $a == $b) => do
      let a ← elabVExpr a
      let b ← elabVExpr b
      let s ← unifyOperands a b
      forceIndex s (mkConst ``SchemaLang.Ty.u64) a
      forceIndex s (mkConst ``SchemaLang.Ty.u64) b
      return mkAppN (mkConst ``SchemaLang.VExpr.eq) #[s, a, b]
  | `(vexpr| $a && $b) => do
      let a ← elabVExpr a
      let b ← elabVExpr b
      let s ← unifyOperands a b
      forceIndex s (mkConst ``SchemaLang.Ty.bool) a
      forceIndex s (mkConst ``SchemaLang.Ty.bool) b
      return mkAppN (mkConst ``SchemaLang.VExpr.and) #[s, a, b]
  -- no `or` ctor: the De Morgan form (exact on Bool)
  | `(vexpr| $a || $b) => do
      let a ← elabVExpr a
      let b ← elabVExpr b
      let s ← unifyOperands a b
      let na := mkAppN (mkConst ``SchemaLang.VExpr.not) #[s, a]
      let nb := mkAppN (mkConst ``SchemaLang.VExpr.not) #[s, b]
      let conj := mkAppN (mkConst ``SchemaLang.VExpr.and) #[s, na, nb]
      return mkAppN (mkConst ``SchemaLang.VExpr.not) #[s, conj]
  | `(vexpr| !$a) => do
      let a ← elabVExpr a
      let ta ← inferType a
      let some s := vexprSchemaOf? ta |
        throwError "[inv| … ]: ! operand is not a VExpr"
      forceIndex s (mkConst ``SchemaLang.Ty.bool) a
      return mkAppN (mkConst ``SchemaLang.VExpr.not) #[s, a]
  | `(vexpr| ($a)) => elabVExpr a
  | _ => throwUnsupportedSyntax

open Lean Elab Term in
scoped elab "[inv| " e:vexpr " ]" : term => elabVExpr e

/-! ### The unexpanders — a VExpr pretty-prints back to `[inv| … ]` -/

open Lean in
/-- A node's precedence, from its delaborated syntax (the splice
decision's input; unknown shapes count as atoms — conservative). -/
private def vexprPrec? : TSyntax `vexpr → Option Nat
  | `(vexpr| $_ > $_) => some 60
  | `(vexpr| $_ == $_) => some 60
  | `(vexpr| $_ && $_) => some 50
  | `(vexpr| $_ || $_) => some 40
  | `(vexpr| !$_) => some 65
  | _ => some 100

open Lean in
/-- Splice a child's inner syntax into an operand position: parenthesize
when the child's top node binds looser than the position demands (the
right-nested-chain rule — the re-parsed tree must be the SAME tree;
left splices at the parent's own precedence flatten safely). -/
private def vexprSplice (min : Nat) (e : TSyntax `vexpr) :
    Lean.PrettyPrinter.UnexpandM (TSyntax `vexpr) :=
  if (vexprPrec? e).getD 100 >= min then pure e else `(vexpr| ($e))

open Lean in
@[app_unexpander SchemaLang.VExpr.colOf]
private def unexpVExprColOf : Lean.PrettyPrinter.Unexpander
  | `($(_) $s:str) => do
      let t ← (`([inv| $(mkIdent s.getString.toName):ident ]) :
        Lean.PrettyPrinter.UnexpandM (TSyntax `term))
      return t.raw
  | _ => throw ()

open Lean in
@[app_unexpander SchemaLang.VExpr.lit]
private def unexpVExprLit : Lean.PrettyPrinter.Unexpander
  | `($(_) $n:num) => do
      let t ← (`([inv| $n:num ]) : Lean.PrettyPrinter.UnexpandM (TSyntax `term))
      return t.raw
  | `($(_) ($n:num : $_)) => do
      let t ← (`([inv| $n:num ]) : Lean.PrettyPrinter.UnexpandM (TSyntax `term))
      return t.raw
  | _ => throw ()

open Lean in
@[app_unexpander SchemaLang.VExpr.strlen]
private def unexpVExprStrlen : Lean.PrettyPrinter.Unexpander
  | `($(_) [inv| $n:ident ]) => do
      let t ← (`([inv| strlen($n:ident) ]) : Lean.PrettyPrinter.UnexpandM (TSyntax `term))
      return t.raw
  | _ => throw ()

open Lean in
@[app_unexpander SchemaLang.VExpr.gt]
private def unexpVExprGt : Lean.PrettyPrinter.Unexpander
  | `($(_) [inv| $a:vexpr ] [inv| $b:vexpr ]) => do
      let a' ← vexprSplice 60 a
      let b' ← vexprSplice 61 b
      let t ← (`([inv| $a' > $b' ]) : Lean.PrettyPrinter.UnexpandM (TSyntax `term))
      return t.raw
  | _ => throw ()

open Lean in
@[app_unexpander SchemaLang.VExpr.eq]
private def unexpVExprEq : Lean.PrettyPrinter.Unexpander
  | `($(_) [inv| $a:vexpr ] [inv| $b:vexpr ]) => do
      let a' ← vexprSplice 60 a
      let b' ← vexprSplice 61 b
      let t ← (`([inv| $a' == $b' ]) : Lean.PrettyPrinter.UnexpandM (TSyntax `term))
      return t.raw
  | _ => throw ()

open Lean in
@[app_unexpander SchemaLang.VExpr.and]
private def unexpVExprAnd : Lean.PrettyPrinter.Unexpander
  | `($(_) [inv| $a:vexpr ] [inv| $b:vexpr ]) => do
      let a' ← vexprSplice 50 a
      let b' ← vexprSplice 51 b
      let t ← (`([inv| $a' && $b' ]) : Lean.PrettyPrinter.UnexpandM (TSyntax `term))
      return t.raw
  | _ => throw ()

open Lean in
@[app_unexpander SchemaLang.VExpr.not]
private def unexpVExprNot : Lean.PrettyPrinter.Unexpander
  -- the De Morgan shape (`||`'s elaboration) renders back as `||`:
  -- the `!`s are stripped and the operands re-spliced at `||`'s
  -- operand positions
  | `($(_) [inv| !$x && !$y ]) => do
      let x' ← vexprSplice 41 x
      let y' ← vexprSplice 40 y
      let t ← (`([inv| $x' || $y' ]) : Lean.PrettyPrinter.UnexpandM (TSyntax `term))
      return t.raw
  -- a plain `not` renders as `!`
  | `($(_) [inv| $e:vexpr ]) => do
      let e' ← vexprSplice 65 e
      let t ← (`([inv| !$e' ]) : Lean.PrettyPrinter.UnexpandM (TSyntax `term))
      return t.raw
  | _ => throw ()

-- The namespace CLOSES here: the raw-length decl below must be a ROOT
-- name (the compiled `call $string_len` contract — see its doc).
end SchemaLang

/-- The RAW string length: the (ptr,len) pair's SECOND half. The Lean
    body (`String.length` → chars) is the oracle ONLY — the decl is
    never a compile target (unmarked, and the root name falls outside
    every target's namespace fold), so the compiled callers' `call
    $string_len` resolves to the SPLICED RUNTIME's primitive (the
    `i32.load offset=8` on the string object) — the same name
    resolution the `GuestlangStd.strlen`/`strcat` intrinsics ride
    (`WasmBackend.stdOp?`). ROOT NAME IS THE CONTRACT: a namespaced
    name emits prefixed in the LCNF (`$SchemaLang.string_len`) and
    would NOT resolve (the `unknown func` lesson). Byte-length ≠
    char-length off ASCII (the StrOps v1 stance). -/
@[nolint linter.guestlang.dupDefBodies "deliberate mirror of `SchemaLang.string_len` (above): the ROOT name is the `call $string_len` runtime splice contract (a namespaced name emits prefixed and fails to resolve — the `unknown func` lesson); identical bodies by design"]
def string_len (s : String) : UInt64 := s.length.toUInt64

namespace SchemaLang

end SchemaLang
