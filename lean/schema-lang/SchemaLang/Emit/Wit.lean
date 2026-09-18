/-
# SchemaLang.Emit.Wit — the WIT target

Fold `Item`s to a WIT world. Names arrive pre-mangled (kebab via
`Emit.kebab`); output is `Std.Format` → text; byte-tie CI is the drift
guard (wit-parser roundtrip in CI — the canonical parser, not this
printer, is the correctness authority).

Text assembly: structural `Std.Format` (hard `line`s — NO `group`s, so
`.pretty` cannot reflow; `nest` for block bodies, `joinSep` for comma
lists, `.pretty` once at the `String` boundary). The bytes are pinned
identical to the pre-Format emitter by the goldens (`goldens/wit/`,
`goldens/wit-fixtures/`); the one deliberate quirk: func decls sit at a
4-space column (`worldOf` nests each under `nest 4 (line ++ …)`) while
every other interface member sits at 2. Leaf payloads (`tyFmt`'s type
atoms, the `package` line) interpolate — never join.

Lowering (target-neutral universe → WIT): `option t` → `option<t>`;
`result ok err` → `result<ok, err>`; `map k v` → `list<tuple<K, V>>`,
`set k` → `list<K>` (WIT has no map/set — the association-list form;
key/element uniqueness is a documented payload invariant, not WIT
data); `future`/`stream` native (WASI 0.3); records → `record`,
variants → `variant` (payload cases → `case(ty)`); funcs → `func` in
the world's export interface; resources → `resource`.

ILLEGAL EMISSION IS WF-GATED, not an emitter concern: the two caught
bugs (post-mangle name collisions, zero-case variants) refuse at
ELABORATION — `SchemaLang.Item.mangleCollDiags` / `Item.check`'s
`emptyVariant` arm, bridged into `SchemaLang.Wf`'s `WellFormed`. The
target renderings below assume a checked universe; a raw universe that
violates the gate must be routed through `universeCheck` first (the
emitters' `GenCtx.checkedItems?` lane is the route).

Omitted: worlds/packages layout policy (the caller names the world;
one world per universe today), interface splitting (small interfaces
are the wasmtron rule).
-/

module

public import CodegenCore
public import SchemaLang.Item
public import SchemaLang.Emit.GenCtx

@[expose] public section

namespace SchemaLang.Emit.Wit

open CodegenCore.Emit (kebab)
open Std.Format

/-- The map/set KEY rendering, DIRECT (the `KeyTy.toTy` indirection
    breaks `tyFmt`'s structural recursion; the arms are exactly the
    scalar atoms `tyFmt` gives the injected types). -/
def keyFmt : KeyTy → Std.Format
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "s8" | .i16 => "s16" | .i32 => "s32" | .i64 => "s64"
  | .string => "string"

/-- Lower a `Ty` to WIT type text as a format ATOM (no `line`s —
    `.pretty` is the identity on it, so `tyWit`'s bytes are the old
    `s!` interpolation's, exactly). -/
def tyFmt : Ty → Std.Format
  | .bool => "bool"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .i8 => "s8" | .i16 => "s16" | .i32 => "s32" | .i64 => "s64"
  | .f32 => "f32" | .f64 => "f64"
  | .string => "string"
  | .bytes => "list<u8>"
  -- the flat form: WIT has no tensors — dims dropped (schema metadata
  -- the WIT boundary cannot carry)
  | .tensor _ a => f!"list<{tyFmt a}>"
  -- WIT has no map/set: the association-list form; keys render via
  -- `keyFmt` (ordinary WIT scalars)
  | .map k v => f!"list<tuple<{keyFmt k}, {tyFmt v}>>"
  | .set k => f!"list<{keyFmt k}>"
  | .option a => f!"option<{tyFmt a}>"
  | .result ok err => f!"result<{tyFmt ok}, {tyFmt err}>"
  | .list a => f!"list<{tyFmt a}>"
  | .future a => f!"future<{tyFmt a}>"
  | .stream a => f!"stream<{tyFmt a}>"
  | .ty n => kebab n

/-- Lower a `Ty` to WIT type text. -/
def tyWit (t : Ty) : String := (tyFmt t).pretty

/-- The body of a brace block at column 0: first `line` nested 2 (the
    members' indent), hard lines BETWEEN the members — none after the
    last, so no trailing whitespace — and an empty member list degrades
    to a bare `line` (header and close brace on consecutive lines, the
    pre-Format fold's shape). -/
def blockBody (members : List Std.Format) : Std.Format :=
  match members with
  | [] => line
  | _ => nest 2 (line ++ joinSep members line)

/-- One type item as WIT text (record/variant/resource; non-type items
    are the empty format — `worldOf` filters them out first). -/
def typeDecl : Item → Std.Format
  | .record n fields =>
      f!"record {kebab n} \{" ++ blockBody
        (fields.map fun f => f!"{kebab f.name}: {tyFmt f.ty},") ++ line ++ f!"}"
  | .variant n cases =>
      f!"variant {kebab n} \{" ++ blockBody
        (cases.map fun (c, payload) =>
          match payload with
          | some t => f!"{kebab c}({tyFmt t}),"
          | none => f!"{kebab c},") ++ line ++ f!"}"
  | .resource n => f!"resource {kebab n};"
  | _ => ""

/-- One function as a WIT func declaration (UNINDENTED — `worldOf`
    nests it, giving the 4-space column the goldens pin). A `future a`
    return becomes `async func` returning `a` — the wasi 0.3 async
    ABI: the async-ness lives in the FUNCTION TYPE (the component
    validator rejects a sync func returning `future`). `delivery =
    stream` renders the result as `stream<a>` — the delta-shaped
    contract: the host consumes the impl's list elements
    incrementally. -/
def funcDecl : FuncSig → Std.Format :=
  fun s =>
    let params := joinSep (s.params.map fun (p, t) => f!"{kebab p}: {tyFmt t}") (text ", ")
    -- the RESULT: delivery=stream surfaces the list's ELEMENT as the
    -- stream's item type (the impl's `List a` = the buffered stream)
    let witRet (t : Ty) : Std.Format :=
      match t with
      | .list a => f!"stream<{tyFmt a}>"
      | a => tyFmt a
    match s.ret with
    | .future a =>
        let r := if s.sem.delivery == (.stream : Delivery) then witRet a else tyFmt a
        f!"{kebab s.name}: async func({params}) -> {r};"
    | ret =>
        f!"{kebab s.name}: func({params}) -> {tyFmt ret};"

/-- The world, in the wasmtron small-interfaces shape:

    interface <world>-types { records, variants, resources }
    interface <world>-exports { use <world>-types.{...}; funcs }
    world <world> { export <world>-exports; }

Types live in their own interface; the exports interface `use`s exactly
the type names its signatures reference (deduped, kebab-mangled).
-/
def worldOf (packageName worldName : String) (items : List Item) : String :=
  let typeItems := items.filter fun it =>
    match it with | .record _ _ | .variant _ _ | .resource _ => true | _ => false
  let funcs := items.filterMap fun it =>
    match it with | .func s => some s | _ => none
  -- types referenced by func signatures (deduped, registration order)
  let refs :=
    (funcs.flatMap fun s => s.params.map (·.2) ++ [s.ret])
      |>.flatMap Ty.tyRefs
      |>.eraseDups
  let usePart : Std.Format :=
    if refs.isEmpty then ""
    else line ++ f!"  use {kebab worldName}-types.\{{joinSep (refs.map kebab) (text ", ")}};"
  let typesIface : Std.Format :=
    f!"interface {kebab worldName}-types \{"
      ++ typeItems.foldl (fun acc it => acc ++ line ++ typeDecl it) ""
      ++ line ++ "}"
  let exportsIface : Std.Format :=
    f!"interface {kebab worldName}-exports \{" ++ usePart
      ++ funcs.foldl (fun acc s => acc ++ nest 4 (line ++ funcDecl s)) ""
      ++ line ++ "}"
  (f!"package {packageName};" ++ line ++ line ++ typesIface ++ line ++ line
    ++ exportsIface ++ line ++ line
    ++ f!"world {kebab worldName} \{" ++ line
    ++ f!"  export {kebab worldName}-exports;" ++ line ++ "}" ++ line
  ).pretty

end SchemaLang.Emit.Wit

/-! ## The WIT lossless fragment (Route A: the lossless FRAGMENT as data
    + the injectivity law per schema)

The WIT emitter is LOSSY — two distinct `Ty`s can emit identical WIT —
so WIT-level schema diffing is UNSOUND in general. The lossless
FRAGMENT is the types whose rendering determines them. The four lossy
corners (the audit of `tyFmt`/`funcDecl`'s arms):

1. `tensor dims a` → `list<a>` — the DIMS are dropped.
2. `bytes` → `list<u8>` — byte-collides with `.list .u8` (single-node
   vs tree, same `.pretty`; the trees differ — the corner the
   Format-level lemma cannot see), excluded on the documented
   byte-level rendering.
3. `set k` → `list<keyFmt k>` — Format-collides with `.list k.toTy`
   (the witness `wit_collision_set_list` in Tests pins it).
4. func-ret: `delivery = stream` renders a `.list` return as
   `stream<…>` — a FUNC-level corner; the universe check refuses
   stream-delivery funcs with list returns.

`.ty n` stays IN the fragment under a name condition (`witLossless`'s
arm): canonical kebab (`kebab n = n`), not a scalar atom, no angle
bracket. -/
namespace SchemaLang

open CodegenCore.Emit (kebab)

/-- The scalar atoms' name test (a string pattern-match — the
    decide-path's kernel reduction exhausts this, where a List-contains
    fold does not). -/
def Emit.Wit.atomName? : String → Bool
  | "bool" => true | "u8" => true | "u16" => true | "u32" => true
  | "u64" => true | "s8" => true | "s16" => true | "s32" => true
  | "s64" => true | "f32" => true | "f64" => true | "string" => true
  | _ => false

/-- The lossless FRAGMENT: `Ty.witLossless t = true` iff `t`'s WIT
    rendering determines `t`. Structural; recursive on the subtypes. -/
def Ty.witLossless : Ty → Bool
  | .tensor _ _ => false
  | .bytes => false
  | .set _ => false
  | .ty n =>
      (kebab n == n) && !Emit.Wit.atomName? n && !(n.toList.contains '<')
  | .bool => true
  | .u8 => true | .u16 => true | .u32 => true | .u64 => true
  | .i8 => true | .i16 => true | .i32 => true | .i64 => true
  | .f32 => true | .f64 => true
  | .string => true
  | .option a => a.witLossless
  | .result a b => a.witLossless && b.witLossless
  | .list a => a.witLossless
  | .map _ v => v.witLossless
  | .future a => a.witLossless
  | .stream a => a.witLossless

/-- The key atoms' partial inverse at the FORMAT level (the cheap
    injectivity route: 10 `rfl` cases instead of a 100-case
    string-diseq sweep). -/
def KeyTy.ofFmt? : Std.Format → Option KeyTy
  | .text "bool" => some .bool
  | .text "u8" => some .u8 | .text "u16" => some .u16
  | .text "u32" => some .u32 | .text "u64" => some .u64
  | .text "s8" => some .i8 | .text "s16" => some .i16
  | .text "s32" => some .i32 | .text "s64" => some .i64
  | .text "string" => some .string
  | _ => none

theorem KeyTy.ofFmt?_keyFmt (k : KeyTy) : KeyTy.ofFmt? (Emit.Wit.keyFmt k) = some k := by
  cases k <;> rfl

/-- The key rendering is injective. -/
theorem KeyTy.keyFmt_inj {k k' : KeyTy}
    (h : Emit.Wit.keyFmt k = Emit.Wit.keyFmt k') : k = k' := by
  have h1 := KeyTy.ofFmt?_keyFmt k
  have h2 := KeyTy.ofFmt?_keyFmt k'
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

theorem Emit.Wit.fmtAppend_inj {a b c d : Std.Format}
    (h : (a ++ b) = (c ++ d)) : a = c ∧ b = d :=
  Std.Format.append.injEq .. |>.mp h

theorem Emit.Wit.fmtAppend_inj_eq {a b c d : Std.Format} :
    ((a ++ b) = (c ++ d)) = (a = c ∧ b = d) :=
  Std.Format.append.injEq ..

/-- The `.ty` name class's canon (extracted from the lossless flag). -/
theorem Ty.witLossless_ty_canon (n : String) (hl : Ty.witLossless (.ty n) = true) :
    (kebab n = n ∧ Emit.Wit.atomName? n = false) ∧
      n.toList.contains '<' = false := by
  simp only [Ty.witLossless, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hl
  exact hl

/-- An atom-named ref is outside the fragment: the atom collides. -/
theorem Ty.witLossless_ty_not_atom (n : String) {a : String}
    (hl : Ty.witLossless (.ty n) = true)
    (h : a = kebab n)
    (ha : Emit.Wit.atomName? a = true) : False := by
  have ⟨⟨hc, hnfa⟩, _⟩ := Ty.witLossless_ty_canon n hl
  have hnn : n = a := hc.symm.trans h.symm
  have hna : Emit.Wit.atomName? n = true := by
    rw [hnn]; exact ha
  exact Bool.noConfusion (hna.symm.trans hnfa)

/-- text-vs-append: distinct Format constructors, no confusion. -/
theorem Emit.Wit.fmtText_append_iff {s : String} {a b : Std.Format} :
    (Std.Format.text s = (a ++ b)) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

theorem Emit.Wit.fmtAppend_text_iff {s : String} {a b : Std.Format} :
    ((a ++ b) = Std.Format.text s) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

/-- The text/c coerced-atom injections (the four spelling combinations
    the renderer's eq-lemmas produce). -/
theorem Emit.Wit.fmtText_inj_eq {s t : String} :
    (Std.Format.text s = Std.Format.text t) = (s = t) :=
  Std.Format.text.injEq ..

theorem Emit.Wit.fmtCoe_inj_eq {s t : String} :
    (Std.format s = Std.format t) = (s = t) := by
  show (Std.Format.text s = Std.Format.text t) = (s = t)
  exact Std.Format.text.injEq ..

theorem Emit.Wit.fmtText_coe_inj_eq {s t : String} :
    (Std.Format.text s = Std.format t) = (s = t) := by
  show (Std.Format.text s = Std.Format.text t) = (s = t)
  exact Std.Format.text.injEq ..

theorem Emit.Wit.fmtCoe_text_inj_eq {s t : String} :
    (Std.format s = Std.Format.text t) = (s = t) := by
  show (Std.Format.text s = Std.Format.text t) = (s = t)
  exact Std.Format.text.injEq ..

/-- The excluded ctors' lossless verdicts (the wit_simp set's
    non-recursive refutations — no decide-on-open). -/
theorem Ty.witLossless_set (k : KeyTy) : Ty.witLossless (.set k) = false := rfl
theorem Ty.witLossless_tensor (d : List Nat) (a : Ty) :
    Ty.witLossless (.tensor d a) = false := rfl
theorem Ty.witLossless_bytes : Ty.witLossless .bytes = false := rfl

/-- The cross-shape fallback's simp set (the lossless flag refutes the
    excluded ctors' subcases directly; the prefixes carry the rest). -/
syntax "wit_simp" Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| wit_simp $loc:location) =>
    `(tactic| simp [Emit.Wit.tyFmt, Emit.Wit.fmtAppend_inj_eq, Emit.Wit.fmtText_inj_eq,
        Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_append_iff,
        Emit.Wit.fmtAppend_text_iff, Ty.witLossless_set, Ty.witLossless_tensor,
        Ty.witLossless_bytes] $loc)

/-- THE FRAGMENT LEMMA: the renderer restricted to the lossless
    fragment is injective — `tyFmt t = tyFmt t'` with both types
    lossless forces `t = t'`. (Format-level: the byte-level `.pretty`
    step is the emitter's documented identity-on-atoms, byte-tie-pinned
    — the named corner, see the section header.) -/
theorem Ty.witFmt_inj : ∀ (t t' : Ty), t.witLossless = true → t'.witLossless = true →
    Emit.Wit.tyFmt t = Emit.Wit.tyFmt t' → t = t' := by
  intro t
  induction t with
  | bool | u8 | u16 | u32 | u64 | i8 | i16 | i32 | i64 | f32 | f64 | string =>
      intro t' _ hl' h
      cases t' with
      | ty n =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h (fun hc => Ty.witLossless_ty_not_atom _ hl' hc (by rfl))
      | _ =>
          all_goals first
            | rfl
            | wit_simp at h hl'
  | bytes | set k | tensor d a => intro t' hl _ _; simp [Ty.witLossless] at hl
  | option a ih =>
      intro t' hl hl' h
      cases t' with
      | option b =>
          obtain ⟨hAB, -⟩ := Emit.Wit.fmtAppend_inj h
          obtain ⟨-, hAB⟩ := Emit.Wit.fmtAppend_inj hAB
          exact congrArg _ (ih b hl hl' hAB)
      | _ => wit_simp at h hl'
  | result ok err ihok iherr =>
      intro t' hl hl' h
      cases t' with
      | result ok' err' =>
          obtain ⟨h1, -⟩ := Emit.Wit.fmtAppend_inj h
          obtain ⟨h2, hB⟩ := Emit.Wit.fmtAppend_inj h1
          obtain ⟨h3, -⟩ := Emit.Wit.fmtAppend_inj h2
          obtain ⟨-, hA⟩ := Emit.Wit.fmtAppend_inj h3
          have hok : ok = ok' :=
            ihok ok' ((Bool.and_eq_true _ _).mp hl |>.1)
              ((Bool.and_eq_true _ _).mp hl' |>.1) hA
          have herr : err = err' :=
            iherr err' ((Bool.and_eq_true _ _).mp hl |>.2)
              ((Bool.and_eq_true _ _).mp hl' |>.2) hB
          exact by rw [hok, herr]
      | _ => wit_simp at h hl'
  | list a ih =>
      intro t' hl hl' h
      cases t' with
      | list b =>
          obtain ⟨hAB, -⟩ := Emit.Wit.fmtAppend_inj h
          obtain ⟨-, hAB⟩ := Emit.Wit.fmtAppend_inj hAB
          exact congrArg _ (ih b hl hl' hAB)
      | _ => wit_simp at h hl'
  | map k v ih =>
      intro t' hl hl' h
      cases t' with
      | map k' v' =>
          obtain ⟨h1, -⟩ := Emit.Wit.fmtAppend_inj h
          obtain ⟨h2, hV⟩ := Emit.Wit.fmtAppend_inj h1
          obtain ⟨h3, -⟩ := Emit.Wit.fmtAppend_inj h2
          obtain ⟨-, hK⟩ := Emit.Wit.fmtAppend_inj h3
          have hkk : k = k' := KeyTy.keyFmt_inj hK
          have hvv : v = v' := ih v' hl hl' hV
          exact by rw [hkk, hvv]
      | _ => wit_simp at h hl'
  | future a ih =>
      intro t' hl hl' h
      cases t' with
      | future b =>
          obtain ⟨hAB, -⟩ := Emit.Wit.fmtAppend_inj h
          obtain ⟨-, hAB⟩ := Emit.Wit.fmtAppend_inj hAB
          exact congrArg _ (ih b hl hl' hAB)
      | _ => wit_simp at h hl'
  | stream a ih =>
      intro t' hl hl' h
      cases t' with
      | stream b =>
          obtain ⟨hAB, -⟩ := Emit.Wit.fmtAppend_inj h
          obtain ⟨-, hAB⟩ := Emit.Wit.fmtAppend_inj hAB
          exact congrArg _ (ih b hl hl' hAB)
      | _ => wit_simp at h hl'
  | ty n =>
      intro t' hl hl' h
      cases t' with
      | ty n' =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact congrArg _ ((Ty.witLossless_ty_canon n hl |>.1.1.symm.trans h).trans
            (Ty.witLossless_ty_canon n' hl' |>.1.1))
      | bool =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | u8 =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | u16 =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | u32 =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | u64 =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | i8 =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | i16 =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | i32 =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | i64 =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | f32 =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | f64 =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | string =>
          simp only [Emit.Wit.tyFmt, Emit.Wit.fmtCoe_inj_eq, Emit.Wit.fmtText_inj_eq,
            Emit.Wit.fmtText_coe_inj_eq, Emit.Wit.fmtCoe_text_inj_eq] at h
          exact absurd h.symm (fun hc => Ty.witLossless_ty_not_atom _ hl hc (by rfl))
      | _ => wit_simp at h hl'

/-- Every type the universe's item signatures mention (records' fields,
    variants' payloads, funcs' params + return). -/
def Emit.Wit.universeTys : List Item → List Ty
  | [] => []
  | .record _ fields :: rest => fields.map (·.ty) ++ universeTys rest
  | .variant _ cs :: rest => cs.filterMap (·.2) ++ universeTys rest
  | .func s :: rest => s.params.map (·.2) ++ [s.ret] ++ universeTys rest
  | .resource _ :: rest => universeTys rest

/-- The func-ret corner (lossy corner 4): `delivery = stream` renders a
    `.list` return as `stream<…>` — the universe check refuses such
    funcs. -/
def Emit.Wit.funcRetOk (s : FuncSig) : Bool :=
  !(s.sem.delivery == (Delivery.stream) &&
    match s.ret with | .list _ => true | _ => false)

/-- Structural equality on the renderer's formats (Std.Format has no
    BEq; the sweep's pairs are the fragment's text/append trees). The
    sweep's semantics need no proof — the LAW comes from the lossless
    conjunct alone (the fragment lemma); this conjunct is the
    belt-and-suspenders surface check, witnessed firing by the
    Tests' collision controls. -/
def Emit.Wit.fmtEq : Std.Format → Std.Format → Bool
  | .text a, .text b => a == b
  | .append a b, .append c d => fmtEq a c && fmtEq b d
  | .nil, .nil => true
  | .line, .line => true
  | .nest i a, .nest j b => i == j && fmtEq a b
  | .group a _, .group b _ => fmtEq a b
  | .tag i a, .tag j b => i == j && fmtEq a b
  | _, _ => false

/-- The pairwise surface sweep: no two DISTINCT types in the universe
    render identically. -/
def Emit.Wit.surfaceOk? (l : List Ty) : Bool :=
  l.all fun t => l.all fun t' =>
    (t == t') || !(Emit.Wit.fmtEq (Emit.Wit.tyFmt t) (Emit.Wit.tyFmt t'))

/-- THE CHECK: every type in the fragment + no cross-type collisions in
    the rendered surface + no stream-delivery func with a `.list`
    return. Decidable; the obligation's decide-discharge runs it. -/
def Emit.Wit.witCheck (items : List Item) : Bool :=
  (universeTys items).all (·.witLossless) &&
  surfaceOk? (universeTys items) &&
  (items.all fun it => match it with | .func s => funcRetOk s | _ => true)

/-- THE LAW (the order's statement): a universe whose types all sit in
    the lossless fragment renders injectively — the per-type fragment
    lemma composes over the universe's type set. The item-name layer is
    the registry's (names unique pre-kebab; the `use`-dedup is order-
    preserving). -/
theorem Emit.Wit.wit_injective_of_lossless (items : List Item)
    (h : (universeTys items).all (·.witLossless) = true) :
    Function.Injective
      (fun t : {t // t ∈ universeTys items} => Emit.Wit.tyFmt t.val) := by
  intro a b he
  have ha := List.all_eq_true.mp h a.val a.property
  have hb := List.all_eq_true.mp h b.val b.property
  exact Subtype.ext (Ty.witFmt_inj a.val b.val ha hb he)

/-- The per-schema WIT obligation: the kit's shape at the item-universe
    payload, decidableNow-tiered — the discharge is the kernel's decide
    over `witCheck` (the same backend `SchemaObligation.discharge`'s
    decidableNow arm runs for invariant rows; here the payload is the
    item universe, not an invariant row). -/
def Emit.Wit.witObligation (items : List Item) : CodegenCore.Obligation (List Item) :=
  { label := "wit-lossless-injective"
  , tier := .decidableNow
  , payload := items
  , provenance := `SchemaLang.Emit.Wit.witObligation }

/-- The decidableNow DISCHARGE for the WIT obligation: the kernel's
    decide over `witCheck`; `none` = the loud gap (a lossy universe
    refuses — the lossy note as data, not silence). -/
def Emit.Wit.witDischarge (items : List Item) :
    Option CodegenCore.Obligation.Evidence :=
  match decide (Emit.Wit.witCheck items = true) with
  | true => some (.decided true)
  | false => none

/-- SOUNDNESS of the WIT obligation's discharge (the decidableNow
    backend's shape): a fired `.decided true` means the check passed. -/
theorem Emit.Wit.witDischarge_sound (items : List Item)
    (h : Emit.Wit.witDischarge items = some (.decided true)) :
    Emit.Wit.witCheck items = true := by
  unfold witDischarge at h
  cases hd : decide (witCheck items = true) with
  | true => exact of_decide_eq_true hd
  | false => rw [hd] at h; simp at h

/-- COMPLETENESS: a passing check discharges (the tier fires on the
    claims it can decide). -/
theorem Emit.Wit.witDischarge_of_check (items : List Item)
    (h : Emit.Wit.witCheck items = true) :
    Emit.Wit.witDischarge items = some (.decided true) := by
  unfold witDischarge
  rw [decide_eq_true h]

/-- The obligation's law: a discharged WIT obligation means the
    universe's WIT rendering is injective — soundness transported to
    the law's statement. -/
theorem Emit.Wit.witLaw (items : List Item)
    (h : Emit.Wit.witCheck items = true) :
    Function.Injective
      (fun t : {t // t ∈ universeTys items} => Emit.Wit.tyFmt t.val) :=
  wit_injective_of_lossless items
    ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h |>.1) |>.1)

end SchemaLang

/-- The WIT emitter plugin. Repo-root-relative path (the `../../` prefix)
    matches the Rust/vortex emitters — the forge byte-tie checks the SAME
    file the emitter writes. The world folds the ctx's DEMO partition
    (`GenCtx.rootItems` — the driver-derived root-namespace split): with a
    second project's registry replayed, the gateway world stays exactly
    the Demo universe (byte-identical output, same fold, same order). -/
def witEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx where
  name := "wit"
  style := .doubleSlash
  specSource := "Demo.lean"
  outputs := ["../../wit/gateway.wit"]
  run ctx := [
    { path := "../../wit/gateway.wit"
      contents := SchemaLang.Emit.Wit.worldOf "demo:gateway" "gateway"
        (ctx.rootItems `Demo) }
  ]

/-- The flags world's WIT emitter (the second project's wire lane): the
    FEATUREFLAGS partition of the same ctx, rendered by the SAME `worldOf`
    fold — one lowering, two worlds. The partition is DERIVED (the
driver's `GenCtx.rootPartitionOf` over the replayed registry — no
    hand-listed item names): a new `@[schema]` in FeatureFlags.lean joins
    `wit/flags.wit` without touching this emitter. Demo-only replays
    (the test goldens) see the empty partition = the bare world. -/
def flagsWitEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx where
  name := "flags-wit"
  style := .doubleSlash
  specSource := "FeatureFlags.lean (via GenCtx.rootPartitionOf)"
  outputs := ["../../wit/flags.wit"]
  run ctx := [
    { path := "../../wit/flags.wit"
      contents := SchemaLang.Emit.Wit.worldOf "guestlang:flags" "flags"
        (ctx.rootItems `FeatureFlags) }
  ]
