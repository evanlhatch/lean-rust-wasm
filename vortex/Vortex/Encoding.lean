/-
# Vortex.Encoding — the encoding selection as a PURE STATIC FUNCTION

Owner: the Vortex agent (the mandate tree, `vortex/`).
Driving decisions: notes/design-vortex-encodings.md (THE DESIGN: the
selection is a pure function from static shape facts, never a runtime
tree search — flatland's locked policy "compiler predicts, never
searches"; BTrBlocks is the anti-model) + notes/v3/07-extensibility.md
R1 (the target recipe: a lowering over the closed `Ty`, never a new
universe) + notes/v3/05-codegen.md §2 (the emitter spine, consumed by
`Vortex.Emit`).

## The model (the vortex layout's honest fragment at seed size)

A schema field's column is stored under an `EncodingSpec`; the layout
is the encoding plus the validity layer (nullability — the outer
layer; kernels peel layers). The vocabulary is the design's, MINUS the
rows with no static consumer (the anti-museum rule: an encoding enters
with its consumer, each exclusion named below):

- `identity` — the universal fallback (the legacy `EncodingKind.identity`).
- `bitPacked w` — fixed-width bits; the fallback for fixed-width scalars.
- `foR w` — frame-of-reference: a base plus `w`-bit offsets (design:
  "small int range → FoR over BitPacked(width)").
- `dict` — dictionary: the design's "FK/enum/low-card → Dict".
- `sequence` — the design's "declared sorted+fixed-step → Sequence".
- `constant` — the design's "is-constant → Constant" (a static
  cardinality bound of exactly 1).

EXCLUDED at this size (each names its trigger): `runEnd` and the
data-dependent half of the design's tree (runs/actual cardinality are
DATA facts — they discharge on the obligation ladder's `oracleSwept`
tier, not statically; the seed selects on static facts only), `ALP`
(no float in the boundary `Ty` — W8.1's exclusion), `Sparse`/frame
codecs (no consumer). The PHYSICAL bit-layout codecs (the dict/run-end
block formats) stay out of Lean (the legacy lane's Part-10 containment)
— the retention exemplars below are the seed's lossless semantic core.

## The selection function and its discipline

`select : Ty → ShapeFacts → EncodingSpec` is PURE and TOTAL — the
decision tree's guard order is flatland's locked policy (constant →
sequence → dict → FoR → the bitpack/identity fallback), each guard
DECIDABLE over the static facts. The laws:

- `select_applicable` — the selection never picks an inapplicable
  encoding (the design's law shape: the chosen row's guard holds). The
  fallback row (identity) is what makes this provable for EVERY input
  — the design's "totality proof (the fallback row)".
- Purity/determinism is definitional (a pure total function; no
  runtime search exists to be nondeterministic).
- The SEMANTIC content — the encoding holds the field's values
  losslessly — is carried at this size by the retention exemplars
  (FoR + constant, ported from the legacy lane's `Encoding.lean`): the
  admissible-subdomain statement is the honest one (constant loses on
  non-constant columns BY THE PIN, never by silence).

The facts DERIVE from the boundary universe (`factsOfColumn` over the
closed `Ty` — R1's "lowering instance over the closed Ty, leaves +
wrappers"): the option wrapper peels to the validity layer, the set's
element rides the key sub-universe, cardinality is static where the
Ty says so (`staticCard?`). Sortedness is NEVER inferred (the design's
"declared only" rule) — the seed's `factsOfColumn` leaves
`sorted? := none`.

The five questions (notes/v3/01-core.md): root = Universe (the closed
`Ty` lowered into the encoding vocabulary; no new type universe);
carrier = `ColumnLayout` — the encoding + validity, with the
applicability law stated over the selection; spine reading = the
REGISTRY → interpretation (select) → artifact (`Vortex.Emit`'s layout
spec); ladder rung = `decidableNow` (every guard is a Bool over
concrete facts; `select_applicable` is a `Bool` law, discharged by
case analysis); gate row = the byte-tie (`VortexTests`' golden pins
over `layoutEmitter`; the GenCheck/Ownership wiring is the write
path's named follow-up) + the axiom report.

Core-only (imports Kit + SchemaCore.{Ty,Item,Fold} — the cone rule).
-/

import Kit
import SchemaCore.Ty
import SchemaCore.Item
import SchemaCore.Fold

open Kit SchemaCore

namespace Vortex

/-! ## The static shape facts (design doc's `ShapeFacts`, the seed's
    fragment) -/

/-- A DECLARED sort direction. Sortedness is never inferred (the
    design's §4 rule: declared only, no inference without evidence). -/
inductive SortDir where
  | asc | desc
deriving Repr, BEq, DecidableEq, Inhabited

/-- The static shape facts a selection reads. Every field is decided
    BEFORE encoding (elaboration/generation time) — the facts ride the
    schema, never the data. -/
structure ShapeFacts where
  /-- A static cardinality bound (an enum's case count, a capped
      type's cap). `none` = no static bound. -/
  cardBound : Option Nat
  /-- The column rides a KEY position (a map key / set element / a
      declared foreign key) — the design's "FK → Dict". -/
  isKey : Bool
  /-- DECLARED sortedness (`none` = not declared — never inferred). -/
  sorted? : Option SortDir
  /-- DECLARED fixed-step arithmetic (a sequence column's step). -/
  fixedStep : Bool
  /-- The column carries a validity layer (the option wrapper). -/
  nullable : Bool
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## The encoding vocabulary (the layout's honest fragment) -/

/-- An encoding spec: HOW a column is physically stored. The width
    parameters are FIXED BY THE SELECTION from the static facts (the
    base of a FoR and the dictionary's values are write-time data —
    the spec fixes only what the static facts determine). -/
inductive EncodingSpec where
  /-- The universal fallback: the values as-is (lossless by
      construction). -/
  | identity
  /-- Fixed-width bits, `width` bits per element. -/
  | bitPacked (width : Nat)
  /-- Frame-of-reference: a base plus `width`-bit offsets. -/
  | foR (width : Nat)
  /-- Dictionary: deduplicated values + per-row codes. -/
  | dict
  /-- Sorted fixed-step arithmetic progression (declared facts only). -/
  | sequence
  /-- One shared value + a row count (a cardinality-1 column). -/
  | constant
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## The guards (the decision tree's rows, as decidable facts) -/

/-- The low-cardinality threshold (flatland's locked policy's
    small-card row; a named policy constant, not a search). -/
def lowCardMax : Nat := 256

/-- The FoR range ceiling: a static cardinality bound above this is
    not a "small int range" — the fallback takes it. -/
def forMaxRange : Nat := 65536

/-- Bits needed to index a card-`c` universe (offsets `0..c-1`).
    Total; the selection reads it only when a bound exists. -/
def bitsFor : Option Nat → Nat
  | some c => Nat.log2 c + 1
  | none => 0

/-- Guard: a static cardinality bound of exactly one (is-constant). -/
def isConstantGuard (f : ShapeFacts) : Bool := f.cardBound == some 1

/-- Guard: declared sorted AND declared fixed-step. -/
def sequenceGuard (f : ShapeFacts) : Bool := f.sorted?.isSome && f.fixedStep

/-- Guard: key position or low static cardinality. -/
def dictGuard (f : ShapeFacts) : Bool :=
  f.isKey || (f.cardBound.map (fun c => decide (c ≤ lowCardMax))).getD false

/-- Guard: a static cardinality bound within the FoR ceiling. -/
def foRGuard (f : ShapeFacts) : Bool :=
  (f.cardBound.map (fun c => decide (c ≤ forMaxRange))).getD false

/-- The integer-shaped scalars (FoR's admissible element types). -/
def intShape : Ty → Bool
  | .u64 | .i64 | .bounded _ => true
  | _ => false

/-- The fixed-width scalar widths (bits per element). `none` = the
    type has no fixed-width binary layout (a nested/wrapper type — the
    fallback row takes it). -/
def scalarWidth? : Ty → Option Nat
  | .bool => some 1
  | .u64 => some 64
  | .i64 => some 64
  | .bounded _ => some 64
  | _ => none

/-- The per-encoding APPLICABILITY predicate — decidable over the
    static facts (the design: `applicable` is decidable; the selection
    law rides it). -/
def applicable (e : EncodingSpec) (t : Ty) (f : ShapeFacts) : Bool :=
  match e with
  | .identity => true
  | .bitPacked w => scalarWidth? t == some w
  | .foR w => foRGuard f && intShape t && (w == bitsFor f.cardBound)
  | .dict => dictGuard f
  | .sequence => sequenceGuard f
  | .constant => isConstantGuard f

/-! ## THE SELECTION FUNCTION (the design's core move) -/

/-- THE selection: a PURE TOTAL function from the boundary type + the
    static shape facts to the encoding — never a runtime search. The
    guard order is flatland's locked policy, adapted: is-constant →
    declared sorted+fixed-step → key/low-card → small int range →
    the bitpack/identity fallback. (Nested matches on the guard Bools —
    the equation-lemma-friendly shape; the proofs case on the same
    guards.) -/
def select (t : Ty) (f : ShapeFacts) : EncodingSpec :=
  match isConstantGuard f with
  | true => .constant
  | false =>
    match sequenceGuard f with
    | true => .sequence
    | false =>
      match dictGuard f with
      | true => .dict
      | false =>
        match foRGuard f, intShape t with
        | true, true => .foR (bitsFor f.cardBound)
        | _, _ =>
          match scalarWidth? t with
          | some w => .bitPacked w
          | none => .identity

/-- THE SELECTION LAW: the selection never picks an inapplicable
    encoding — `applicable` holds on the chosen row, for EVERY input
    (the design's per-rule applicability + the fallback row's
    totality, one theorem). The negative control in VortexTests pins
    that a MIS-WIRED tree (a guard/order sabotage) breaks exactly this
    law — the law has teeth. -/
theorem select_applicable (t : Ty) (f : ShapeFacts) :
    applicable (select t f) t f = true := by
  simp only [select, applicable]
  cases h1 : isConstantGuard f <;> cases h2 : sequenceGuard f <;>
    cases h3 : dictGuard f <;> cases h4 : foRGuard f <;> cases h5 : intShape t <;>
    cases h6 : scalarWidth? t <;> simp

/-! ## The facts derivation (the design's step 2: facts from the
    universe) -/

/-- A field's Ty lowered to its COLUMN: the element type the values
    live in, the nullability (the option wrapper peels to the validity
    layer), and the key-position flag (a set's element rides the key
    sub-universe). R1's lowering over the closed `Ty` — leaves +
    wrappers, no new universe. -/
def columnOf : Ty → Ty × Bool × Bool
  | .option e => (e, true, false)
  | .set k => (k.toTy, false, true)
  | t => (t, false, false)

/-- The STATIC cardinality a type declares (an enum's case count / a
    cap): bool is a two-valued enum; `.bounded cap` is exactly the
    cap's universe; everything else is statically unbounded here. -/
def staticCard? : Ty → Option Nat
  | .bool => some 2
  | .bounded cap => some cap
  | _ => none

/-- The facts a schema field's Ty DERIVES (the seed's static half of
    the design's ShapeFacts): cardinality from the type, key-ness from
    the key positions, nullability from the wrapper. Sortedness and
    the fixed-step are DECLARED facts — nothing infers them here (the
    design's no-sortedness-inference rule). -/
def factsOfColumn (t : Ty) : ShapeFacts :=
  { cardBound := staticCard? (columnOf t).1
    isKey := (columnOf t).2.2
    sorted? := none
    fixedStep := false
    nullable := (columnOf t).2.1 }

/-- The facts of a KEY-position column (a map FIELD's keys — the key
    sub-universe's column): the key rides the dict row (the design's
    "FK → Dict"; the map column's keys lane). -/
def keyFacts (k : KeyTy) : ShapeFacts :=
  { cardBound := staticCard? k.toTy
    isKey := true
    sorted? := none
    fixedStep := false
    nullable := false }

/-- The key-position law: EVERY key selects the dict row — total over
    the closed key sub-universe (the design's "FK/enum/low-card →
    Dict", stated once for all four keys). -/
theorem keyFacts_dict (k : KeyTy) : select k.toTy (keyFacts k) = .dict := by
  simp only [select, keyFacts, isConstantGuard, sequenceGuard, dictGuard]
  cases k <;> simp [staticCard?]

/-- The layout of one schema field's column: the selected encoding +
    the validity layer. THE EMITTER'S ROW (the artifact's unit). -/
structure ColumnLayout where
  encoding : EncodingSpec
  validity : Bool
deriving Repr, BEq, DecidableEq, Inhabited

/-- The layout selection: the element's encoding + the wrapper's
    validity layer. -/
def layoutOf (t : Ty) : ColumnLayout :=
  { encoding := select (columnOf t).1 (factsOfColumn t)
    validity := (columnOf t).2.1 }

/-- The layout law: every layout's encoding is applicable to the
    element type + the derived facts — `select_applicable`'s instance
    at the layout's own arguments (one citation, never a re-proof). -/
theorem layoutOf_applicable (t : Ty) :
    applicable (layoutOf t).encoding (columnOf t).1 (factsOfColumn t) = true :=
  select_applicable _ _

/-! ## The retention exemplars (the lossless semantic core, ported
    fresh from the legacy lane's `SchemaLang.Vortex.Encoding`)

    The design's law shape: `applicable enc facts → decode (encode xs)
    = xs` on the encoding's ADMISSIBLE SUBDOMAIN. At this size the
    ported content is FoR (unconditionally lossless) and constant
    (lossless on the admissible subdomain ONLY — the negative control
    pins the loss, the honesty discipline). The block-format codecs
    (dict/run-end bit layouts) port with the wire lane — the named
    follow-up; the legacy lane's full family (rle/dict/comp) is the
    mining source. -/

/-- A frame-of-reference encoding: a base value plus per-row offsets
    from it (the legacy lane's shape-only model; no bit layout). -/
structure FoRData where
  base : Int
  offsets : List Int

/-- Encode: the frame base is the head value (head-or-0) and each row
    stores its offset from it. -/
def forEncode (xs : List Int) : FoRData :=
  { base := xs.headD 0, offsets := xs.map (fun x => x - xs.headD 0) }

/-- Readback: re-add the base to every offset. -/
def forRead (d : FoRData) : List Int :=
  d.offsets.map (fun o => o + d.base)

/-- FoR RETENTION: decode ∘ encode = id — the encoding holds the
    field's values losslessly (the design's law, unconditional for
    FoR). Ported from the legacy lane's `forRead_forEncode`. -/
theorem forRead_forEncode : ∀ (xs : List Int), forRead (forEncode xs) = xs := by
  intro xs
  simp [forRead, forEncode, List.map_map, Function.comp_def]

/-- A constant encoding: the row count plus the (optional) shared
    value (the legacy lane's honest model). -/
structure ConstantData (α : Type) where
  count : Nat
  value : Option α

/-- Encode: the count and the head value (if any). -/
def constEncode (xs : List α) : ConstantData α :=
  { count := xs.length, value := xs.head? }

/-- Readback: the shared value, replicated to the count. -/
def constRead : ConstantData α → List α
  | ⟨n, some v⟩ => List.replicate n v
  | ⟨_count, none⟩ => []

/-- CONSTANT RETENTION, on the admissible subdomain: a column whose
    every value equals its head round-trips exactly. On a non-constant
    column the readback LOSES (the VortexTests negative control pins
    the loss) — pretending a universal law here would be the lie the
    zero-sorry discipline exists to prevent. Ported from the legacy
    lane's `constRead_constEncode`. -/
theorem constRead_constEncode [DecidableEq α] (v : α) (vs : List α)
    (h : vs.all (fun w => w == v) = true) :
    constRead (constEncode (v :: vs)) = v :: vs := by
  induction vs with
  | nil => rfl
  | cons w ws ih =>
      have hall : (w == v) = true ∧ ws.all (fun u => u == v) = true := by
        simpa using List.all_eq_true.mp h
      have hweq : w = v := beq_iff_eq.mp hall.1
      subst hweq
      have hws := ih hall.2
      simp only [constEncode, List.length_cons, constRead, List.head?_cons] at hws ⊢
      rw [List.replicate_succ, hws]

end Vortex
