/-
# SchemaCore.Fold — the recursion schemes over the closed universes

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/01-core.md §1 (Universe = the
initial-algebra side: closed codes + total folds — the fold IS the
Universe root's working face) + notes/v3/07-extensibility.md R1 ("a
lowering instance over the closed `Ty` — never a new universe") +
notes/v3/15-patterns.md #15 (the closed-universe exhaustiveness
discipline — the fold's match IS the compiler-driven extension point).

THE FINDING this module retires: `Ty` carried a hand-rolled recursive
fold per consumer (the WIT `renderTy`, the Rust `tyRustPrim`, the
snapshot `tyText`, the lossless flag) — each re-deriving the same
structural walk. The initial-algebra discipline: ONE fold, consumers
are ALGEBRAS (a record with one field per constructor, receiving the
folded children). A new constructor breaks `foldTy`'s exhaustiveness
exactly once; every algebra grows its row through the same compile
error. The same discipline over the GADT family (`Value`/`VList`/
`VMap`): ONE dependent fold (`foldValue`), the motive riding the index
(06 §2), the algebra record carrying the whole sibling family's rows —
the codec's encoder is its first migrated consumer (Codec.lean's
`valEncAlg`).

The laws (the initial-algebra ones, stated over the ONE fold):

- UNIQUE (the initiality law): a function that commutes with the
  algebra on every constructor IS the fold —
  `foldTy_unique`. This is the migration's theorem: it pins a migrated
  renderer to its algebra rows by induction, once, instead of trusting
  two parallel recurrences.
- FUSION: a map that commutes with both algebras passes the fold —
  `foldTy_fusion` (the cheap h∘fold = fold′ form).

The same pair over `KeyTy` (`foldKeyTy`, `foldKeyTy_unique`): the
scalar sub-universe's key positions route through `KeyTy.toTy` (below
the first fold a key position is a plain `Ty` again — Ty.lean's
discipline), so the key fold needs no `Ty` recursion inside it.

UPDATE (the `declare_fold` migration): the `KeyTy`/`Ty` entourages are
GENERATED now — two `Kit.Derive.Fold.declare_fold` calls replace the
hand-written algebra/fold/equations/initiality families (~120 LOC
down); the generated names + statements are exactly the hand ones',
so every consumer is untouched and the byte-tie over the migrated
renderers (`gates gen-check`) proves the generated fold
defeq-compatible with the hand walk. The DEPENDENT fold (`foldValue`)
STAYS hand-written — the GADT family is outside the generator's honest
scope (its refusal names the extension).

HONEST RESIDUE (the consumers that do NOT migrate, each named with its
proof-level reason):

- the codec's `decVal` (Codec.lean) stays a hand match: the DECODER's
  recursion is over the INPUT BYTE STREAM (a parser: it CONSUMES bytes
  and PRODUCES `Value t` subresults bottom-up through the parser
  state), while the fold's recursion is over the VALUE STRUCTURE — an
  algebra's rows receive already-built subresults (`P` at the child
  index), never the byte stream. The initial-algebra fold states the
  catamorphism direction only; `decVal` is the unfold/parse direction
  and no `ValueAlg` row can state it. Its laws keep their own proofs
  (`decVal_encVal_append` — pattern #2), now citing the FOLD's
  equation lemmas for the encoder side.
- the snapshot's `tyText` MIGRATED (the pushback's re-payment: the
  char-level round-trip proofs re-keyed onto the fold's equation
  lemmas `tyText_*` — one walk, the law re-paid once).

Core-only (imports SchemaCore.Ty/Value only — the cone rule; Value
itself imports Ty alone, so the cone is preserved).

The five questions (notes/v3/01-core.md): root = Universe (the
initial-algebra fold over the closed codes); carrier = the algebra
record (one field per ctor, exhaustiveness in the type); spine reading
= the Interpretation stage's SHARED recursion (01 §5 — every emitter
reads through ONE walk); ladder rung = total structural, kernel-visible
reduction (`rfl`/`decide` over concrete types); gate row = the axiom
report + SchemaTests' fold suite + the byte-tie over the migrated
emitters' artifacts.
-/

import SchemaCore.Ty
import SchemaCore.Value
import Kit.Derive.Fold

namespace SchemaCore

/-! ## The KeyTy fold (the scalar sub-universe) -/

/- THE KEY FOLD ENTOURAGE, GENERATED: `declare_fold KeyTy` emits the
   whole family — the algebra record (`KeyTyAlg`), the fold
   (`foldKeyTy`), the equation set (`foldKeyTy_<ctor>`, all `rfl`) and
   the initiality law (`foldKeyTy_unique`) — from the inductive's own
   constructor data (06 §7: a family of near-identical decls is a macro
   that hasn't been written). The generated names + statements are
   exactly the hand entourage's (the migration is DEFEQ-compatible —
   the byte-tie over the migrated renderers is the proof). -/
declare_fold KeyTy

/-! ## The Ty fold (the boundary universe) -/

/- THE FOLD ENTOURAGE, GENERATED: `declare_fold Ty` — the algebra
   (`TyAlg`: one field per ctor, a key field receives the KEY, the cap
   arrives raw — a `Nat` has no fold), the fold (`foldTy`, total,
   structural, kernel-visible), the equation set (`foldTy_<ctor>`) and
   the initiality law (`foldTy_unique` — the migration's theorem,
   cited by every migrated renderer). The DEPENDENT half (`foldValue`
   and its siblings) STAYS hand-written below — the GADT family is
   outside the generator's honest scope (the generator's own refusal
   names it: the motive rides the index, 06 §2). -/
declare_fold Ty

/-- THE FUSION LAW: a map that carries one algebra to the other passes
    the fold — `h ∘ foldTy alg = foldTy alg'`. The consumers'
    post-processing (e.g. a wrapper that renames one row) composes
    with the fold instead of forking it. -/
theorem foldTy_fusion {α β : Type} {alg : TyAlg α} {alg' : TyAlg β} {h : α → β}
    (hb : h alg.bool = alg'.bool) (hu : h alg.u64 = alg'.u64)
    (hi : h alg.i64 = alg'.i64) (hs : h alg.string = alg'.string)
    (ho : ∀ a, h (alg.option a) = alg'.option (h a))
    (hl : ∀ a, h (alg.list a) = alg'.list (h a))
    (hr : ∀ ok err, h (alg.result ok err) = alg'.result (h ok) (h err))
    (hm : ∀ k a, h (alg.map k a) = alg'.map k (h a))
    (he : ∀ k, h (alg.set k) = alg'.set k)
    (hd : ∀ n, h (alg.bounded n) = alg'.bounded n)
    (t : Ty) : h (foldTy alg t) = foldTy alg' t := by
  induction t with
  | bool => exact hb
  | u64 => exact hu
  | i64 => exact hi
  | string => exact hs
  | option a iha => simp only [foldTy_option, ho, iha]
  | list a iha => simp only [foldTy_list, hl, iha]
  | result ok err iha ihb => simp only [foldTy_result, hr, iha, ihb]
  | map k v iha => simp only [foldTy_map, hm, iha]
  | set k => simp only [foldTy_set, he k]
  | bounded n => simp only [foldTy_bounded, hd n]

/-! ## The dependent value fold (the GADT family's one walk, 06 §2) -/

/-- The DEPENDENT value algebra: ONE record carrying the whole sibling
    family's rows (`Value`/`VList`/`VMap` — 06 §2's sibling discipline:
    the record rows are the family, no nested `List (Value t)` data),
    each row's result riding its index — `P` at the value's index, `Q`
    at the list sibling's, `R` at the map sibling's. A new family ctor
    refuses to compile until the algebra grows its row (the same
    compiler-driven extension point as `foldTy`, one level up). -/
structure ValueAlg (P : Ty → Type) (Q : Ty → Type) (R : KeyTy → Ty → Type) where
  bool : Bool → P .bool
  u64 : UInt64 → P .u64
  i64 : Int64 → P .i64
  string : String → P .string
  none : {t : Ty} → P (.option t)
  some : {t : Ty} → P t → P (.option t)
  ok : {ok err : Ty} → P ok → P (.result ok err)
  err : {ok err : Ty} → P err → P (.result ok err)
  list : {t : Ty} → Q t → P (.list t)
  map : {k : KeyTy} → {v : Ty} → R k v → P (.map k v)
  set : {k : KeyTy} → Q k.toTy → P (.set k)
  bounded : {cap : Nat} → Fin cap → P (.bounded cap)
  vnil : {t : Ty} → Q t
  vcons : {t : Ty} → P t → Q t → Q t
  mnil : {k : KeyTy} → {v : Ty} → R k v
  mcons : {k : KeyTy} → {v : Ty} → P k.toTy → P v → R k v → R k v

-- THE DEPENDENT FOLD: the GADT family's one walk (01 §1's
-- initial-algebra shape for an INDEXED family — the motive rides the
-- index, `06` §2's discipline). Mutual over the sibling family,
-- structural, kernel-visible: concrete values reduce by `rfl`.
mutual
def foldValue {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    (alg : ValueAlg P Q R) : (t : Ty) → Value t → P t
  | .bool, .bool b => alg.bool b
  | .u64, .u64 n => alg.u64 n
  | .i64, .i64 n => alg.i64 n
  | .string, .string s => alg.string s
  | .option _, .none => alg.none
  | .option t, .some v => alg.some (foldValue alg t v)
  | .result ok _, .ok v => alg.ok (foldValue alg ok v)
  | .result _ err, .err v => alg.err (foldValue alg err v)
  | .list _, .list vl => alg.list (foldVList alg vl)
  | .map _ _, .map m => alg.map (foldVMap alg m)
  | .set _, .set vl => alg.set (foldVList alg vl)
  | .bounded _, .bounded f => alg.bounded f

def foldVList {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    (alg : ValueAlg P Q R) : {t : Ty} → VList t → Q t
  | _, .nil => alg.vnil
  | _, .cons v vs => alg.vcons (foldValue alg _ v) (foldVList alg vs)

def foldVMap {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    (alg : ValueAlg P Q R) : {k : KeyTy} → {v : Ty} → VMap k v → R k v
  | _, _, .nil => alg.mnil
  | _, _, .cons kv vv m =>
      alg.mcons (foldValue alg _ kv) (foldValue alg _ vv) (foldVMap alg m)
end

/-- The dependent fold's equation set (06 §5 — consumers prove against
    these, never against brecOn plumbing). All `rfl`: the recursion is
    structural, so the equations are kernel reduction, not opacity. -/
theorem foldValue_bool {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} (b : Bool) :
    foldValue alg .bool (.bool b) = alg.bool b := rfl
theorem foldValue_u64 {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} (n : UInt64) :
    foldValue alg .u64 (.u64 n) = alg.u64 n := rfl
theorem foldValue_i64 {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} (n : Int64) :
    foldValue alg .i64 (.i64 n) = alg.i64 n := rfl
theorem foldValue_string {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} (s : String) :
    foldValue alg .string (.string s) = alg.string s := rfl
theorem foldValue_none {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {t : Ty} :
    foldValue alg (.option t) .none = alg.none := rfl
theorem foldValue_some {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {t : Ty} (v : Value t) :
    foldValue alg (.option t) (.some v) = alg.some (foldValue alg t v) := rfl
theorem foldValue_ok {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {ok err : Ty} (v : Value ok) :
    foldValue alg (.result ok err) (.ok v) = alg.ok (foldValue alg ok v) := rfl
theorem foldValue_err {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {ok err : Ty} (v : Value err) :
    foldValue alg (.result ok err) (.err v) = alg.err (foldValue alg err v) := rfl
theorem foldValue_list {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {t : Ty} (vl : VList t) :
    foldValue alg (.list t) (.list vl) = alg.list (foldVList alg vl) := rfl
theorem foldValue_map {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {k : KeyTy} {v : Ty} (m : VMap k v) :
    foldValue alg (.map k v) (.map m) = alg.map (foldVMap alg m) := rfl
theorem foldValue_set {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {k : KeyTy} (vl : VList k.toTy) :
    foldValue alg (.set k) (.set vl) = alg.set (foldVList alg vl) := rfl
theorem foldValue_bounded {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {cap : Nat} (f : Fin cap) :
    foldValue alg (.bounded cap) (.bounded f) = alg.bounded f := rfl
theorem foldVList_nil {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {t : Ty} :
    foldVList alg (.nil : VList t) = alg.vnil := rfl
theorem foldVList_cons {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {t : Ty} (v : Value t) (vs : VList t) :
    foldVList alg (.cons v vs) = alg.vcons (foldValue alg t v) (foldVList alg vs) := rfl
theorem foldVMap_nil {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {k : KeyTy} {v : Ty} :
    foldVMap alg (.nil : VMap k v) = alg.mnil := rfl
theorem foldVMap_cons {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R} {k : KeyTy} {v : Ty}
    (kv : Value k.toTy) (vv : Value v) (m : VMap k v) :
    foldVMap alg (.cons kv vv m)
      = alg.mcons (foldValue alg k.toTy kv) (foldValue alg v vv) (foldVMap alg m) := rfl

/-- THE DEPENDENT INITIALITY LAW (the dependent fold's uniqueness, the
    motive discipline of 06 §2 made a theorem): a triple of functions
    over the sibling family that commutes with the algebra on every ctor
    IS the fold — one mutual induction over the family, proved ONCE
    here, cited by every migrated dependent consumer. -/
theorem foldValue_unique {P : Ty → Type} {Q : Ty → Type} {R : KeyTy → Ty → Type}
    {alg : ValueAlg P Q R}
    {f : (t : Ty) → Value t → P t}
    {fL : {t : Ty} → VList t → Q t}
    {fM : {k : KeyTy} → {v : Ty} → VMap k v → R k v}
    (hb : ∀ b, f .bool (.bool b) = alg.bool b)
    (hu : ∀ n, f .u64 (.u64 n) = alg.u64 n)
    (hi : ∀ n, f .i64 (.i64 n) = alg.i64 n)
    (hst : ∀ s, f .string (.string s) = alg.string s)
    (hnone : ∀ t, f (.option t) .none = alg.none)
    (hsome : ∀ (t : Ty) (v : Value t), f (.option t) (.some v) = alg.some (f t v))
    (hok : ∀ (ok err : Ty) (v : Value ok),
      f (.result ok err) (.ok v) = alg.ok (f ok v))
    (herr : ∀ (ok err : Ty) (v : Value err),
      f (.result ok err) (.err v) = alg.err (f err v))
    (hlist : ∀ (t : Ty) (vl : VList t), f (.list t) (.list vl) = alg.list (fL vl))
    (hmap : ∀ (k : KeyTy) (v : Ty) (m : VMap k v), f (.map k v) (.map m) = alg.map (fM m))
    (hset : ∀ (k : KeyTy) (vl : VList k.toTy), f (.set k) (.set vl) = alg.set (fL vl))
    (hbd : ∀ (cap : Nat) (fv : Fin cap), f (.bounded cap) (.bounded fv) = alg.bounded fv)
    (hvnil : ∀ t, fL (.nil : VList t) = alg.vnil)
    (hvcons : ∀ (t : Ty) (v : Value t) (vs : VList t),
      fL (.cons v vs) = alg.vcons (f t v) (fL vs))
    (hmnil : ∀ (k : KeyTy) (v : Ty), fM (.nil : VMap k v) = alg.mnil)
    (hmcons : ∀ (k : KeyTy) (v : Ty) (kv : Value k.toTy) (vv : Value v) (m : VMap k v),
      fM (.cons kv vv m) = alg.mcons (f k.toTy kv) (f v vv) (fM m)) :
    ∀ (t : Ty) (v : Value t), f t v = foldValue alg t v := by
  apply Value.rec
    (motive_1 := fun t v => f t v = foldValue alg t v)
    (motive_2 := fun t vl => fL vl = foldVList alg vl)
    (motive_3 := fun k v m => fM m = foldVMap alg m)
  case bool => intro b; exact hb b
  case u64 => intro n; exact hu n
  case i64 => intro n; exact hi n
  case string => intro s; exact hst s
  case none => intro t; exact hnone t
  case some => intro t v ih; rw [hsome t v, ih]; rfl
  case ok => intro ok err v ih; rw [hok ok err v, ih]; rfl
  case err => intro ok err v ih; rw [herr ok err v, ih]; rfl
  case list => intro t vl ihL; rw [hlist t vl, ihL]; rfl
  case map => intro k v m ihM; rw [hmap k v m, ihM]; rfl
  case set => intro k vl ihL; rw [hset k vl, ihL]; rfl
  case bounded => intro cap fv; exact hbd cap fv
  next => intro t; exact hvnil t
  next => intro t v vs ihV ihL; rw [hvcons t v vs, ihV, ihL]; rfl
  next => intro k v; exact hmnil k v
  next => intro k v kv vv m ihKV ihVV ihM; rw [hmcons k v kv vv m, ihKV, ihVV, ihM]; rfl

/-! ## The migrated consumers, as algebras -/

/-! ### The WIT lowering (the slice's emitter face) -/

/-- The key's WIT row (the `renderKeyTy` rows as the sub-universe
    algebra). Coherence with Ty.lean's leaf rendering is the theorem
    below — the fold and the leaf agree by initiality. -/
def keyWitAlg : KeyTyAlg String where
  bool := "bool"
  u64 := "u64"
  i64 := "i64"
  string := "string"

/-- THE KEY COHERENCE: Ty.lean's leaf key rendering IS the key fold
    over `keyWitAlg` — the KeyTy uniqueness law's exercise (a
    four-rfl-commute check, then initiality does the rest). -/
theorem renderKeyTy_eq (k : KeyTy) : renderKeyTy k = foldKeyTy keyWitAlg k :=
  foldKeyTy_unique (x := k) rfl rfl rfl rfl

/-- The WIT lowering as an ALGEBRA (07 R1 step 1 — the rows, verbatim
    from the pre-fold `renderTy`; the graded correspondence table per
    row lives in Ty.lean's header: LOSSLESS for the scalars + the
    three wrappers, RETRACTION-WITH-NOTE for map/set/bounded). -/
def witAlg : TyAlg String where
  bool := "bool"
  u64 := "u64"
  i64 := "i64"
  string := "string"
  option a := "option<" ++ a ++ ">"
  list a := "list<" ++ a ++ ">"
  result ok err := "result<" ++ ok ++ ", " ++ err ++ ">"
  map k v := "list<tuple<" ++ renderKeyTy k ++ ", " ++ v ++ ">>"
  set k := "list<" ++ renderKeyTy k ++ ">"
  bounded _ := "u64"

/-- THE WIT RENDERING = the fold over `witAlg` (the migration: the
    ONE walk, the emitter's rows as data). -/
def renderTy : Ty → String := foldTy witAlg

/-! ### The lossless fragment flag -/

/-- The lossless FRAGMENT's verdict algebra: `true` on the lossless
    rows, `false` on the three declared-loss rows (Ty.lean's graded
    table as a `TyAlg Bool`). -/
def witLosslessAlg : TyAlg Bool where
  bool := true
  u64 := true
  i64 := true
  string := true
  option a := a
  list a := a
  result ok err := ok && err
  map _ _ := false
  set _ := false
  bounded _ := false

/-- The lossless FRAGMENT: `t.witLossless = true` iff `renderTy t`
    determines `t` (the map/set/bounded rows are OUT — the named
    losses). Migrated to the fold. -/
def Ty.witLossless : Ty → Bool := foldTy witLosslessAlg

/-! ### The Rust rendering (the codec-consumer lane's type face) -/

/-- The Rust scalar-key table (the scalar sub-universe's rows of the
    Rust rendering — the map/set arms consume the KEY directly, so the
    fold needs no re-entry into `Ty` at all). One scalar table serves
    both the key positions and the type face (Rust.lean's note). -/
def keyRustAlg : KeyTyAlg String where
  bool := "bool"
  u64 := "u64"
  i64 := "i64"
  string := "String"

/-- The Rust rendering of a key (the key fold over `keyRustAlg`). -/
def keyRustPrim : KeyTy → String := foldKeyTy keyRustAlg

/-- The Rust type rendering as an ALGEBRA (the rows verbatim from the
    pre-fold `tyRustPrim`). The map/set key positions ride the scalar
    sub-universe through `keyRustPrim` (the `KeyTy.toTy`-injection's
    route — the coherence is the theorem below). The wf-recursion the
    old hand walk needed (`tyNodeCount` + `termination_by`) is GONE —
    the fold is structural. Deliberate byte-collisions kept (the
    declared losses): map → `Vec<(K, V)>` (order-preserving wire),
    set → `Vec<K>`, bounded → `u64`. -/
def rustAlg : TyAlg String where
  bool := "bool"
  u64 := "u64"
  i64 := "i64"
  string := "String"
  option a := "Option<" ++ a ++ ">"
  list a := "Vec<" ++ a ++ ">"
  result ok err := "Result<" ++ ok ++ ", " ++ err ++ ">"
  map k v := "Vec<(" ++ keyRustPrim k ++ ", " ++ v ++ ")>"
  set k := "Vec<" ++ keyRustPrim k ++ ">"
  bounded _ := "u64"

/-- THE RUST TYPE RENDERING = the fold over `rustAlg` (the migration).
    The option/list arms stay correct for totality (unreachable through
    `descrOfTy`'s lift, which takes them as wrappers — Rust.lean's
    note). -/
def tyRustPrim : Ty → String := foldTy rustAlg

/-! ## The migrated consumers' carried theorems -/

/-- THE NAMED COLLISION (the lossy `set` row): a set's lowering is
    byte-identical to the plain list over the same key type — the
    collision is the declared loss, pinned here as data. -/
theorem renderTy_set_list_collision (k : KeyTy) :
    renderTy (.set k) = renderTy (.list k.toTy) := by cases k <;> rfl

/-- THE NAMED COLLISION (the lossy `bounded` row): every cap lowers to
    `u64` — caps conflate with each other and with plain `u64`. -/
theorem renderTy_bounded_u64_collision (cap : Nat) :
    renderTy (.bounded cap) = renderTy .u64 := rfl

/-- The key position's rendering coherence (Ty.lean's pin, carried): a
    key's rendering IS the fold at its injected type. -/
theorem renderKeyTy_toTy (k : KeyTy) : renderKeyTy k = renderTy k.toTy := by
  cases k <;> rfl

/-- The WIT ALGEBRA'S ROW COHERENCE at the scalar leaves (the key
    sub-universe's slice of `witAlg` — one scalar table, the fold's
    `map`/`set` fields consume the KEY directly). -/
theorem witAlg_key_coherence (k : KeyTy) :
    foldTy witAlg k.toTy = foldKeyTy keyWitAlg k := by
  cases k <;> rfl

/-- Pairwise surface distinctness over a CONCRETE type list (decidable;
    the lossless injectivity PIN at the slice's granularity — the
    fragment's lowerings are pairwise distinct on the ctor sample,
    `decide`-checked, not asserted). A `false` verdict names a surface
    collision; the named ones are the lossy rows' pins. -/
def witSurfaceDistinct : List Ty → Bool
  | [] => true
  | t :: rest =>
      rest.all (fun t' => renderTy t != renderTy t') && witSurfaceDistinct rest

/-- THE PIN: the lossless ctor sample's lowerings are pairwise distinct
    (kernel `decide` over the one fold). -/
example : witSurfaceDistinct
    [.bool, .u64, .i64, .string, .option .u64, .list .string,
     .result .u64 .string] = true := by decide

/-- The lossy rows' fragment verdicts (the flagged exclusions). -/
example : (Ty.map .string .u64).witLossless = false := rfl
example : (Ty.set .u64).witLossless = false := rfl
example : (Ty.bounded 42).witLossless = false := rfl
example : (Ty.result .u64 .string).witLossless = true := rfl

example : witSurfaceDistinct [.list .string, .set .string] = false := by decide
example : witSurfaceDistinct [.u64, .bounded 42] = false := by decide

end SchemaCore
