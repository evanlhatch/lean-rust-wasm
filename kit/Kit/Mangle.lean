/-
# Kit.Mangle — the ONE name-mangling surface + the post-mangle uniqueness
discipline

Identifiers arrive as registry names (dot/space/dash/underscore separated
words, camel humps split); every target gets its convention FROM THE SAME
word list. The mangling is NOT injective — kebab: `FooBar` / `foo-bar` /
`foo_bar` all mangle to `foo-bar` (camel/snake/pascal have the same
shape) — so "registry names are unique" is NOT collision-safety. The real
rule is POST-mangle uniqueness: the collision scan `collDiags` (the
checker arm) is EMPTY iff the mangled name list is nodup (the bridge
`collDiags_eq_nil_iff` — the WF-arm/relation pairing, mined from legacy
`SchemaLang.Wf.mangleCollDiags_eq_nil_iff`). A legal universe cannot emit
colliding target identifiers.

Provenance: mined from
`legacy/lean/codegen-core/CodegenCore/Emit/Core.lean` (the mangler
section + `rustIdent`) +
`legacy/lean/schema-lang/SchemaLang/Item.lean` + `Wf.lean` (the dup-scan
idiom + the collision bridge) — theorem content ported, files FRESH.

Core-only (no mathlib/Batteries).

The five questions (notes/v3/01-core.md):
- root: Crossing — the source names read into each target's identifier
  surface (the mangle lane every emitter shares).
- carrier grade: the collision diagnostics are plain first-order data;
  the WF fact — the mangled name list's nodup — is the BRIDGE's
  right-hand side, decided over concrete lists.
- spine reading: the Interpretation stage's name half — lowerings call
  ONE mangler per target; the post-mangle uniqueness check is the lane's
  WF arm.
- ladder rung: rung 1 — total string folds + a proved bridge; every
  checkable fact over concrete name lists is a `decide`.
- gate row: none yet — the Kit lane's WF consumes the bridge when the
  first mangled lane grows a gate; the KitTests pins (positive + the
  COLLIDING negative control) are the standing evidence.
-/

/-! ## The word splitter + the per-target conventions -/

namespace Kit

/-- Split a registry name into lowercase word parts: separators
    (`.` `-` `_` space) AND lower→Upper humps both split (`maxHealth` →
    [max, health]). The ONE split every convention below reads. -/
def words (s : String) : List String := Id.run do
  let mut cur : String := ""
  let mut out : List String := []
  let mut prevLower := false
  for c in s.toList do
    if c == '.' || c == '-' || c == '_' || c == ' ' then
      if cur != "" then out := out ++ [cur]
      cur := ""
      prevLower := false
    else if c.isUpper && prevLower then
      out := out ++ [cur]
      cur := c.toLower.toString
      prevLower := false
    else
      cur := cur ++ c.toLower.toString
      prevLower := !(c.isUpper)
  if cur != "" then out := out ++ [cur]
  return out

/-- `"foo"` → `"Foo"` (the word-level joiner's helper). -/
def capitalize (s : String) : String :=
  match s.toList with
  | [] => ""
  | c :: cs => String.ofList (c.toUpper :: cs)

/-- `foo_bar baz` → `fooBarBaz` (Rust fn, Lean field). -/
def camel (s : String) : String :=
  match words s with
  | [] => ""
  | w :: ws => w ++ String.join (ws.map capitalize)

/-- `foo_bar` → `FooBar` (Rust/Lean type). -/
def pascal (s : String) : String := String.join ((words s).map capitalize)

/-- `FooBar baz` → `foo_bar_baz` (Rust module, SQL table). -/
def snake (s : String) : String := String.intercalate "_" (words s)

/-- `foo_bar` → `foo-bar` (WIT identifiers are kebab-case). The WIT
    lane's convention — `SchemaCore.kebabName` delegates here. -/
def kebab (s : String) : String := String.intercalate "-" (words s)

/-- Rust keywords get a raw-identifier escape; the only mangling surprise
    that is allowed to exist. -/
def rustIdent (s : String) : String :=
  let kw := ["as", "break", "const", "continue", "crate", "else", "enum",
    "extern", "false", "fn", "for", "if", "impl", "in", "let", "loop",
    "match", "mod", "move", "mut", "pub", "ref", "return", "self", "Self",
    "static", "super", "trait", "true", "type", "unsafe", "use", "where",
    "while", "async", "await", "dyn", "box"]
  let c := camel s
  if kw.contains c then s!"r#{c}" else c

/-! ## THE post-mangle uniqueness discipline (the WF check + the bridge)

The dup-scan idiom, once: the duplicated names of a list, ONE each, plus
the lemmas the bridge reduces through. Applied to the MANGLED list, the
scan is the checker arm; its emptiness is DECIDABLY the mangled list's
nodup — the same reduction as the pre-mangle dup scan, at the mangling.
-/

/-- One collision diagnostic: the mangled image + ALL its preimages
    (the curated failure names the whole guilty set, not one pair). -/
structure MangleColl where
  /-- The mangled identifier two or more sources share. -/
  image : String
  /-- The source names mangling to `image`, in registration order. -/
  culprits : List String

/-- The duplicated names of `ns`, once each. -/
def dupNames (ns : List String) : List String :=
  (ns.filter fun n => ns.countP (· == n) > 1).eraseDups

/-- The post-mangle collision scan: one diagnostic per colliding mangled
    name, naming ALL its preimages. Empty iff the mangled name list is
    nodup (`collDiags_eq_nil_iff` — the bridge). -/
def collDiags (mangle : String → String) (ns : List String) : List MangleColl :=
  (dupNames (ns.map mangle)).map
    fun m => ⟨m, ns.filter fun n => mangle n == m⟩

/-- Nodup via the per-name multiplicity the dup scan counts. -/
theorem nodup_iff_countP_le_one {ns : List String} :
    ns.Nodup ↔ ∀ n, n ∈ ns → ns.countP (· == n) ≤ 1 := by
  constructor
  · intro hnd
    induction ns with
    | nil => intro n hn; cases hn
    | cons x xs ih =>
        rw [List.nodup_cons] at hnd
        intro n hn
        rw [List.countP_cons]
        rcases List.mem_cons.mp hn with rfl | hnxs
        · -- the head case (`x` substituted by `n`)
          have hz : xs.countP (· == n) = 0 := by
            rw [List.countP_eq_zero]
            intro b hb hbn
            exact hnd.1 (beq_iff_eq.mp hbn ▸ hb)
          rw [hz, if_pos (beq_self_eq_true n)]
          omega
        · have hxn : ¬ ((x == n) = true) := by
            intro hxx
            exact hnd.1 (beq_iff_eq.mp hxx ▸ hnxs)
          rw [if_neg hxn, Nat.add_zero]
          exact ih hnd.2 n hnxs
  · intro h
    induction ns with
    | nil => exact List.nodup_nil
    | cons x xs ih =>
        rw [List.nodup_cons]
        refine ⟨?_, ih ?_⟩
        · intro hx
          have hle := h x List.mem_cons_self
          rw [List.countP_cons, if_pos (beq_self_eq_true x)] at hle
          have hz : xs.countP (· == x) = 0 := by omega
          rw [List.countP_eq_zero] at hz
          exact hz x hx (beq_self_eq_true x)
        · intro n hn
          have hle := h n (List.mem_cons_of_mem x hn)
          rw [List.countP_cons] at hle
          by_cases hxn : (x == n) = true
          · have heq := beq_iff_eq.mp hxn
            subst heq
            rw [if_pos (beq_self_eq_true x)] at hle
            omega
          · rw [if_neg hxn, Nat.add_zero] at hle
            exact hle

/-- The dup scan is EMPTY iff the names are Nodup. -/
theorem dupNames_eq_nil_iff {ns : List String} :
    dupNames ns = [] ↔ ns.Nodup := by
  have hErase : ∀ l : List String, l.eraseDups = [] ↔ l = [] := by
    intro l
    cases l with
    | nil => simp
    | cons x xs => rw [List.eraseDups_cons]; simp
  show List.eraseDups _ = [] ↔ _
  rw [hErase, List.filter_eq_nil_iff]
  constructor
  · intro h
    refine nodup_iff_countP_le_one.mpr fun n hn => Nat.not_lt.mp fun hgt => h n hn ?_
    exact decide_eq_true hgt
  · intro hnd n hn hp
    have hgt : ns.countP (· == n) > 1 := of_decide_eq_true hp
    have hle := nodup_iff_countP_le_one.mp hnd n hn
    omega

/-- THE bridge (the mined `mangleCollDiags_eq_nil_iff`, generalized over
    the mangler): the collision scan is EMPTY iff the MANGLED name list
    has no duplicates. A legal universe cannot emit colliding target
    identifiers — the WF arm (this scan) and the relation (the nodup)
    agree by this theorem, not by convention. -/
theorem collDiags_eq_nil_iff (mangle : String → String) (ns : List String) :
    collDiags mangle ns = [] ↔ (ns.map mangle).Nodup := by
  unfold collDiags
  rw [List.map_eq_nil_iff, dupNames_eq_nil_iff]

/-- The executable WF face: the post-mangle uniqueness verdict, DERIVED
    from the diagnostic authority (one authority, two readings — they
    cannot drift). -/
def mangleWf (mangle : String → String) (ns : List String) : Bool :=
  (collDiags mangle ns).isEmpty

end Kit
