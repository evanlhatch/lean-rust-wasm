/-
# SchemaCore.Snapshot — the registry-state serialization (the universe snapshot)

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/03-bidirectional.md §7 (the snapshot is the
substrate the committed delta checks against — the breaking gate reads
THIS file's format); notes/v3/09-gates-ops.md §3-4 (the committed
baseline is the spec of record; the artifact ledger's demand-set
honesty); notes/v3/15-patterns.md #7 (the env extension as the event
log — registration = append, replay = the materialization, THE SNAPSHOT
= THE INTEGRAL); notes/v3/13-interfaces.md ("the universe snapshot"
row: this module is the ONE writer; lossless by design — the WIT view
is the lossy one, never this baseline).

## The format (canonical: the item lines, then the lane rows)

    item <name> field <fname> <tytext> field <fname> <tytext> ...
    lane <laneid> <name>

- one LINE per item (the line IS the block); lines sorted by item name
  — the CANONICAL form is the point: `print` sorts, so printing a
  reordered-but-equal registry state is byte-identical;
- THE LANES' ROWS (wave-30 A2: the snapshot covers the lanes, not just
  the schema items): after the item lines, one `lane <laneid> <name>`
  line per registered row of every OTHER lane of the ONE log
  (`Kit.Lane.laneLogExt`), sorted by (lane id, name); the schema
  lane's own rows ARE the `item` lines (the rich face over the same
  log's rows). The lane ids are dotted names (sep-free — the ONE name
  atom's discipline);
- `<tytext>` is `tyText`'s paren encoding (`option(u64)`,
  `result(u64,string)`, `bounded(42)`) — NO spaces, so the space is a
  reliable separator;
- names (`<name>`, `<fname>`, `<laneid>`) are space/newline-free
  (`nameOk` — the write-side gate, the emitter's law);
- LF line endings, every line newline-terminated (REQUIRED — the line
  terminator is a hard atom; the pre-grammar parse's tolerance of a
  missing final LF was accepted-set looseness against this header, now
  tightened), the empty file IS the empty universe.

## Riding the grammar layer (05 §1 + design-grammar-layer-v2 §8.2)

The ITEM level IS a `TextKit.Grammar` value: the flat rep-of-lines
shape (`CodeRegistry`'s template) — `rep` of `item <name> field…`
lines under the ONE `rel` codec, `snapshotGrammar` below. The derived
parser/printer own the line loop; THE SNAPSHOT LAW IS THE GENERIC
THEOREM'S INSTANCE: `parse_print` — a `nameOk` universe prints to its
canonical bytes and parses back to its canonical form —
`Grammar.run_print_fixFree` (+ the sort as the wrapper's canonical
composition). The exactness direction instantiates `Grammar.print_parse`
at `snapshotGrammar` (`print_parseG` — it speaks of `printG`, the
UNSORTED grammar bytes; the sort is outside, see the noted gap).

## THE RECURSION'S HONEST STATE (the layered composition — notes/v3/15-patterns.md #17)

The design's plan for the recursive Ty — `fix tyDepth body` with the
ctor arms as `rel`-over-`seq` spines — is UNCONSTRUCTIBLE, and the
wall is structural, not effort: the ctor-armed recursion wall (the
altE-uniform-payload `decode_encode` conflict, the restructures' level
shift, `SelfPathE`'s over-approximation) is pattern #17's three-point
statement — two honest attempts (the per-ctor arm rels of v2 §8.2; the
raw-sum restructures) both died on it. The documented layered
composition follows: the TY stays a hand-riding-
TextKit zone (its proved discipline, `parseTy` + `parseTy_tyText`),
presented to the grammar as the `tyAtom` lexeme: `print = tyText`,
`scan = parseTy` over the maximal separator-free token, GUARDED to the
canonical spelling (a well-formed but non-canonical token —
`bounded(042)` — is a refusal; the accepted-set tightening matches the
design's own `natLex` note). The item level consumes it as a leaf;
the engine's `selfE`/`fix` machinery is unexercised by this format.

## HONEST RESIDUE (the local machinery that stays)

- `parseTy` + its law family (`parseTy_tyText`, the `natText` digit
  theory, the `tyDepth` fuel bookkeeping): the ty token's scan engine
  and its round-trip law — the lexeme's `print_scan` base. The
  recursion is fuel-bounded hand recursion, honest at this layer.
- the carrier's loud refusals: the ty token's SN-coded diagnostics
  stay in its error text; the ITEM level re-keys to the converged
  `TextKit.ParseError` envelope (design v1 §4 — the layer's failures
  ride `parseCode`), rendered at `parse`'s boundary.
- `natText` (the cap's renderer) is format content — its OWN encoding,
  proved round-trip (`scanNat_natText`) — not parsing plumbing.

## The laws (honest, at this size)

- PROVED: `parse_print` — `parse (print items) = .ok (canonical items)`
  for `nameOk` registries — THE GENERIC THEOREM'S INSTANCE
  (`Grammar.run_print_fixFree`), the sort composed at the wrapper.
- PROVED: `print_parseG` — the exactness direction at the UNSORTED
  grammar value (`Grammar.print_parse`'s instance): a successful
  derived parse consumed exactly the `printG` bytes.
- NOTED, NOT PROVED: the wrapper-level canonicalization claim —
  `print (parse s) = s` for canonical `s` — needs the sort's
  permutation + stability theory on top of `print_parseG` (the legacy
  paid three failed attempts; the gate re-derives the bytes instead —
  the code-registry-check precedent). This is a header note, not a
  stub: zero `sorry`, zero `axiom`.

Mining: `legacy/lean/schema-lang/SchemaLang/Snapshot.lean` — the
FORMAT's intent (the stable line-based text encoding, the write-side
name gate, loud parse refusals, the committed universe baseline).

Core-only (imports Kit-riding SchemaCore only — the cone rule).

The five questions (notes/v3/01-core.md):
- root: Universe content — the registry's items (finite data), the
  snapshot = the integral of the registration event log (15 #7).
- carrier grade: first-order over String/List Char; the round-trip law
  is the generic theorem's instance over the closed universe.
- spine reading: the Interpretation stage's OTHER face — registry →
  baseline text; the breaking gate (the forward consumer) reads it.
- ladder rung: rung 1-2 — the item level is the engine's; the ty
  token's law is a small fuel-bounded induction.
- gate row: `gates snapshot-check` (the byte-tie over
  notes/universe.snapshot; the snapshot's ONE tie — never also
  gen-check's, one tie per artifact).
-/

import Kit.Diag
import SchemaCore.Item
import SchemaCore.Register
import TextKit.Lemmas
import TextKit.Literals
import TextKit.Grammar
import TextKit.Grammar.Check
import TextKit.Grammar.Lexemes
import TextKit.Grammar.Laws

namespace SchemaCore

open Kit

/-! ## the refusal envelope (05 §4: the failure KINDS as registry codes) -/

/-- The SN family — the snapshot lane's E-codes, allocated from the
    PERSISTED registry (`notes/code-registry.txt`, the spec of record;
    05 §4's stable-allocation rule). The constants are the family's
    declaration, the code-registry gate's coverage scan ties the
    spellings to the live rows. SN0017–SN0024 (the pre-grammar item
    loop's positional refusals) died with the loop — the item level's
    failures now ride the ParseError envelope's `parseCode`. -/
def eSN0001 : Kit.ECode := ⟨"SN0001"⟩
def eSN0002 : Kit.ECode := ⟨"SN0002"⟩
def eSN0003 : Kit.ECode := ⟨"SN0003"⟩
def eSN0004 : Kit.ECode := ⟨"SN0004"⟩
def eSN0005 : Kit.ECode := ⟨"SN0005"⟩
def eSN0006 : Kit.ECode := ⟨"SN0006"⟩
def eSN0007 : Kit.ECode := ⟨"SN0007"⟩
def eSN0008 : Kit.ECode := ⟨"SN0008"⟩
def eSN0009 : Kit.ECode := ⟨"SN0009"⟩
def eSN0010 : Kit.ECode := ⟨"SN0010"⟩
def eSN0011 : Kit.ECode := ⟨"SN0011"⟩
def eSN0012 : Kit.ECode := ⟨"SN0012"⟩
def eSN0013 : Kit.ECode := ⟨"SN0013"⟩
def eSN0014 : Kit.ECode := ⟨"SN0014"⟩
def eSN0015 : Kit.ECode := ⟨"SN0015"⟩
def eSN0016 : Kit.ECode := ⟨"SN0016"⟩
def eSN0025 : Kit.ECode := ⟨"SN0025"⟩
def eSN0026 : Kit.ECode := ⟨"SN0026"⟩
def eSN0027 : Kit.ECode := ⟨"SN0027"⟩

/-- The snapshot's refusal text, in the ONE envelope's rendering: the
    failure kind rides the registry's SN row, the text keeps the
    `snapshot:` channel prefix. The ty token's refusals are
    positional/structural (no single `got` to enumerate a valid space
    over), so the literal Diag text is the honest shape; the
    closed-world refusal (the unknown type token) constructs through
    `Kit.Diag.closedWorld` directly. -/
def snapshotDiag (code : Kit.ECode) (message : String) : String :=
  Kit.Diag.toString { code := code, message := s!"snapshot: {message}" }

/-! ## the encoding -/

/-- The name charset's parse face: everything but the two separators
    (space, LF). -/
def sepOk (c : Char) : Bool := c != ' ' && c != '\n'

/-- The write-side name gate — the ident-atom's round-trip discipline
    over the sep-free charset (nonempty, all-sepOk, sepOk head). THE
    ONE GATE: the name lexeme's `pre` IS this function, so the valueOk
    discipline and the write-side gate cannot drift. -/
def nameOk (s : String) : Bool := TextKit.identOk sepOk sepOk s

/-- Every name in the item list passes `nameOk`. -/
def namesOk (items : List Item) : Bool :=
  items.all (fun it => nameOk it.name && it.fields.all (fun f => nameOk f.name))

theorem namesOk_spec (items : List Item) (h : namesOk items) :
    ∀ x ∈ items, nameOk x.name ∧ (∀ f ∈ x.fields, nameOk f.name) := by
  intro x hx
  have h2 := List.all_eq_true.mp h x hx
  have h3 := Bool.and_eq_true_iff.mp h2
  exact ⟨h3.1, List.all_eq_true.mp h3.2⟩

/-- Insert by item name (the rows stay sorted; the registry's nodup
    makes the order total). -/
def insertItem : Item → List Item → List Item
  | it, [] => [it]
  | it, row :: rows => if it.name < row.name then it :: row :: rows
      else row :: insertItem it rows

/-- Canonical order: sorted by item name. `print` sorts; `parse` does
    not need to (the canonical form is the print's job). -/
def canonical : List Item → List Item
  | [] => []
  | it :: its => insertItem it (canonical its)

theorem insertItem_mem (y : Item) (l : List Item) (x : Item) :
    x ∈ insertItem y l ↔ x = y ∨ x ∈ l := by
  induction l with
  | nil => simp [insertItem]
  | cons z zs ih =>
      simp only [insertItem]
      split
      · simp []
      · constructor
        · intro h
          rcases List.mem_cons.mp h with hx | h
          · simp [hx]
          · rcases ih.mp h with hx | hx
            · exact Or.inl hx
            · simp [hx]
        · intro h
          rcases h with hx | h
          · simp [ih.mpr (Or.inl hx)]
          · rcases List.mem_cons.mp h with hx | hx
            · simp [hx]
            · simp [ih.mpr (Or.inr hx)]

theorem canonical_mem (l : List Item) (x : Item) :
    x ∈ canonical l ↔ x ∈ l := by
  induction l with
  | nil => simp [canonical]
  | cons y ys ih => simp [canonical, insertItem_mem y (canonical ys) x, ih]

/-- The cap's canonical decimal text. OWN renderer (not `Nat.toString`):
    its round trip through the parser is PROVED below (`scanNat_natText`)
    — core ships no `Nat.toString` round-trip lemma, and the snapshot
    law is only as strong as its weakest token. -/
def natDigit : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9' | _ => '?'

def natText (n : Nat) : String :=
  if n < 10 then String.singleton (natDigit n)
  else natText (n / 10) ++ String.singleton (natDigit (n % 10))
decreasing_by
  simp_wf
  omega

/-- The snapshot spelling's ALGEBRA (the foldTy row set — the ONE
    walk's snapshot face). The literal apps are split (`"option" ++ "("`)
    so the char-level proofs see every separator — the VALUE is
    byte-identical to the fused spelling (the legacy `Ty.toSnapshot`'s
    discipline, over the slice's universe). The map/set rows consume
    the KEY directly (`renderKeyTy` — no `Ty` re-entry, Ty.lean's
    scalar-sub-universe discipline). -/
def snapshotAlg : TyAlg String where
  bool := "bool"
  u64 := "u64"
  i64 := "i64"
  string := "string"
  option a := "option" ++ "(" ++ a ++ ")"
  list a := "list" ++ "(" ++ a ++ ")"
  result a b := "result" ++ "(" ++ a ++ "," ++ b ++ ")"
  map k v := "map" ++ "(" ++ renderKeyTy k ++ "," ++ v ++ ")"
  set k := "set" ++ "(" ++ renderKeyTy k ++ ")"
  bounded n := "bounded" ++ "(" ++ natText n ++ ")"

/-- The snapshot spelling of a `Ty` = the fold over `snapshotAlg` (the
    migration: ONE walk, the emitter's rows as data — a new `Ty` ctor
    refuses to compile until this algebra grows its row). -/
def tyText : Ty → String := foldTy snapshotAlg

/-- The fold's equations in the char-proof-facing form (each `rfl`:
    the fold's structural reduction + the algebra row — `parseTy_tyText`
    and its dependents consume THESE). -/
theorem tyText_bool : tyText .bool = "bool" := rfl
theorem tyText_u64 : tyText .u64 = "u64" := rfl
theorem tyText_i64 : tyText .i64 = "i64" := rfl
theorem tyText_string : tyText .string = "string" := rfl
theorem tyText_option (t : Ty) :
    tyText (.option t) = "option" ++ "(" ++ tyText t ++ ")" := rfl
theorem tyText_list (t : Ty) :
    tyText (.list t) = "list" ++ "(" ++ tyText t ++ ")" := rfl
theorem tyText_result (a b : Ty) :
    tyText (.result a b) = "result" ++ "(" ++ tyText a ++ "," ++ tyText b ++ ")" := rfl
theorem tyText_map (k : KeyTy) (v : Ty) :
    tyText (.map k v) = "map" ++ "(" ++ renderKeyTy k ++ "," ++ tyText v ++ ")" := rfl
theorem tyText_set (k : KeyTy) :
    tyText (.set k) = "set" ++ "(" ++ renderKeyTy k ++ ")" := rfl
theorem tyText_bounded (n : Nat) :
    tyText (.bounded n) = "bounded" ++ "(" ++ natText n ++ ")" := rfl

theorem ofList_ne_nil {L : List Char} (h : L ≠ []) : String.ofList L ≠ "" := by
  intro hcon
  have h2 := congrArg String.toList hcon
  simp [String.toList_ofList] at h2
  exact h h2

/-- The digit char's two faces agree with its value. -/
theorem natDigit_spec : ∀ m : Nat, m < 10 →
    (natDigit m).isDigit ∧ ((natDigit m).toNat - '0'.toNat) = m
  | 0, _ => ⟨rfl, rfl⟩
  | 1, _ => ⟨rfl, rfl⟩
  | 2, _ => ⟨rfl, rfl⟩
  | 3, _ => ⟨rfl, rfl⟩
  | 4, _ => ⟨rfl, rfl⟩
  | 5, _ => ⟨rfl, rfl⟩
  | 6, _ => ⟨rfl, rfl⟩
  | 7, _ => ⟨rfl, rfl⟩
  | 8, _ => ⟨rfl, rfl⟩
  | 9, _ => ⟨rfl, rfl⟩
  | n + 10, h => absurd h (by omega)

theorem all_natText (n : Nat) : (natText n).toList.all Char.isDigit := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · rw [natText.eq_1, if_pos h]
      simp [String.toList_singleton, (natDigit_spec n h).1]
    · rw [natText.eq_1, if_neg h]
      have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      simp only [String.toList_append, List.all_append]
      exact Bool.and_eq_true_iff.mpr ⟨ih (n / 10) hlt,
        by simp [String.toList_singleton,
          (natDigit_spec (n % 10) (Nat.mod_lt n (by omega))).1]⟩

theorem natText_ne (n : Nat) : (natText n).toList ≠ [] := by
  by_cases h : n < 10
  · rw [natText.eq_1, if_pos h]
    simp
  · rw [natText.eq_1, if_neg h]
    simp

theorem foldl_natText (n : Nat) :
    (natText n).toList.foldl
      (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 10
    · rw [natText.eq_1, if_pos h]
      have h0 : ('0' : Char).toNat = 48 := rfl
      have hv := (natDigit_spec n h).2
      simp only [String.toList_singleton, List.foldl_cons, List.foldl_nil]
      omega
    · rw [natText.eq_1, if_neg h]
      have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      have hv := (natDigit_spec (n % 10) (Nat.mod_lt n (by omega))).2
      have h0 : ('0' : Char).toNat = 48 := rfl
      simp only [String.toList_append, String.toList_singleton,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih (n / 10) hlt]
      omega

/-- The cap's canonical decimal text scans back to the cap — the
    bounded lane's token round trip. -/
theorem scanNat_natText (n : Nat) (r : List Char)
    (hr : r.head?.all (fun c => !c.isDigit)) :
    TextKit.scanNat ((natText n).toList ++ r) = some (n, r) := by
  have hall := all_natText n
  have htw : ((natText n).toList ++ r).takeWhile Char.isDigit
      = (natText n).toList := by
    rw [List.takeWhile_append_of_pos (List.all_eq_true.mp hall)]
    simp [(TextKit.takeDrop_head hr).1]
  have hdr : ((natText n).toList ++ r).dropWhile Char.isDigit = r := by
    rw [List.dropWhile_append_of_pos (List.all_eq_true.mp hall)]
    exact (TextKit.takeDrop_head hr).2
  simp only [TextKit.scanNat, htw, hdr]
  rw [if_neg (ofList_ne_nil (natText_ne n)), String.ofList_toList,
    foldl_natText]

/-! ### the ty text's charset facts (the tyAtom lexeme's base) -/

private theorem lit_bool_list : "bool".toList = 'b' :: "ool".toList := rfl
private theorem lit_u64_list : "u64".toList = 'u' :: "64".toList := rfl
private theorem lit_i64_list : "i64".toList = 'i' :: "64".toList := rfl
private theorem lit_string_list : "string".toList = 's' :: "tring".toList := rfl
private theorem lit_option_list : "option".toList = 'o' :: "ption".toList := rfl
private theorem lit_list_list : "list".toList = 'l' :: "ist".toList := rfl
private theorem lit_result_list : "result".toList = 'r' :: "esult".toList := rfl
private theorem lit_map_list : "map".toList = 'm' :: "ap".toList := rfl
private theorem lit_set_list : "set".toList = 's' :: "et".toList := rfl
private theorem lit_bounded_list : "bounded".toList = 'b' :: "ounded".toList := rfl

/-- A digit is sep-free (the bounded cap's chars pass the token
    charset). -/
theorem sepOk_of_isDigit (c : Char) (h : c.isDigit = true) : sepOk c = true := by
  have h1 := Char.isDigit_iff_toNat.mp h
  have h32 : ¬ (c = ' ') := by
    intro heq
    rw [heq] at h1
    simp at h1
  have h10 : ¬ (c = '\n') := by
    intro heq
    rw [heq] at h1
    simp at h1
  show (c != ' ' && c != '\n') = true
  simp [h32, h10]

/-- The ty text's head is a keyword-led token char (the tyAtom's FIRST
    face; every spelling is keyword-led). -/
theorem tyText_head (t : Ty) :
    (tyText t).toList.head?.all Char.isAlphanum = true := by
  cases t with
  | bool => rw [tyText_bool]; decide
  | u64 => rw [tyText_u64]; decide
  | i64 => rw [tyText_i64]; decide
  | string => rw [tyText_string]; decide
  | option a =>
      simp only [tyText_option, String.toList_append, lit_option_list,
        List.cons_append, List.head?_cons]
      decide
  | list a =>
      simp only [tyText_list, String.toList_append, lit_list_list,
        List.cons_append, List.head?_cons]
      decide
  | result a b =>
      simp only [tyText_result, String.toList_append, lit_result_list,
        List.cons_append, List.head?_cons]
      decide
  | map k v =>
      simp only [tyText_map, String.toList_append, lit_map_list,
        List.cons_append, List.head?_cons]
      decide
  | set k =>
      simp only [tyText_set, String.toList_append, lit_set_list,
        List.cons_append, List.head?_cons]
      decide
  | bounded n =>
      simp only [tyText_bounded, String.toList_append, lit_bounded_list,
        List.cons_append, List.head?_cons]
      decide

/-- The key rendering is a separator-free token. -/
theorem renderKeyTy_sepOk (k : KeyTy) : (renderKeyTy k).toList.all sepOk = true := by
  cases k <;> decide

/-- The ty text is a separator-free token (the tyAtom's munch face:
    the space/LF separators ALWAYS break it). -/
theorem tyText_sepOk (t : Ty) : (tyText t).toList.all sepOk = true := by
  have hdigit : ∀ n : Nat, (natText n).toList.all sepOk = true := by
    intro n
    have hd := all_natText n
    rw [List.all_eq_true] at hd ⊢
    intro c hc
    exact sepOk_of_isDigit c (hd c hc)
  induction t with
  | bool => rw [tyText_bool]; decide
  | u64 => rw [tyText_u64]; decide
  | i64 => rw [tyText_i64]; decide
  | string => rw [tyText_string]; decide
  | option a ih =>
      simp only [tyText_option, String.toList_append, List.all_append, ih]
      decide
  | list a ih =>
      simp only [tyText_list, String.toList_append, List.all_append, ih]
      decide
  | result a b iha ihb =>
      simp only [tyText_result, String.toList_append, List.all_append, iha, ihb]
      decide
  | map k v ihv =>
      simp only [tyText_map, String.toList_append, List.all_append, ihv,
        renderKeyTy_sepOk]
      decide
  | set k =>
      simp only [tyText_set, String.toList_append, List.all_append,
        renderKeyTy_sepOk]
      decide
  | bounded n =>
      simp only [tyText_bounded, String.toList_append, List.all_append, hdigit n]
      decide

/-- The ty text is never empty (the tyAtom always consumes at least
    one character). -/
theorem tyText_ne_nil (t : Ty) : (tyText t).toList ≠ [] := by
  cases t with
  | bool => rw [tyText_bool]; decide
  | u64 => rw [tyText_u64]; decide
  | i64 => rw [tyText_i64]; decide
  | string => rw [tyText_string]; decide
  | option a =>
      simp only [tyText_option, String.toList_append, lit_option_list,
        List.cons_append]
      exact List.cons_ne_nil _ _
  | list a =>
      simp only [tyText_list, String.toList_append, lit_list_list,
        List.cons_append]
      exact List.cons_ne_nil _ _
  | result a b =>
      simp only [tyText_result, String.toList_append, lit_result_list,
        List.cons_append]
      exact List.cons_ne_nil _ _
  | map k v =>
      simp only [tyText_map, String.toList_append, lit_map_list,
        List.cons_append]
      exact List.cons_ne_nil _ _
  | set k =>
      simp only [tyText_set, String.toList_append, lit_set_list,
        List.cons_append]
      exact List.cons_ne_nil _ _
  | bounded n =>
      simp only [tyText_bounded, String.toList_append, lit_bounded_list,
        List.cons_append]
      exact List.cons_ne_nil _ _

/-! ## the fuel discipline -/

/-- The ty recursion's depth measure: each `parseTy` nesting consumes
    one unit of fuel; the round-trip law's hypotheses are stated in it. -/
def tyDepth : Ty → Nat
  | .bool => 1 | .u64 => 1 | .i64 => 1 | .string => 1
  | .option t => 1 + tyDepth t
  | .list t => 1 + tyDepth t
  | .result a b => 1 + max (tyDepth a) (tyDepth b)
  | .map _k v => 1 + tyDepth v
  | .set _k => 2
  | .bounded _ => 2

theorem tyDepth_pos (t : Ty) : 1 ≤ tyDepth t := by
  -- kept a simp walk: the option/list cases leave the CHILD variable
  -- in the goal (not closed), so rung-3 decide cannot take them whole
  cases t <;> simp [tyDepth]

/-- A well-formed ty text always ends against a break char (one of the
    four the grammar puts after a ty token) or EOF. -/
def tyBreakOk : List Char → Prop :=
  fun sfx => match sfx.head? with
    | some c => c = ')' ∨ c = ',' ∨ c = ' ' ∨ c = '\n'
    | none => true

/-! The literal-toList tokens (`lparen`/`rparen`/`lcomma`/`lspace`/
`lnewline`) are TextKit.Literals' (`lit_lparen`/… — the ONE home,
shared with the WIT lane); this file cites them directly. -/

theorem headOk_break (sfx : List Char) (h : tyBreakOk sfx) :
    sfx.head?.all (fun c => !c.isAlphanum)
    ∧ sfx.head?.all (fun c => !c.isDigit) := by
  cases sfx with
  | nil => simp []
  | cons c X =>
      have hc := h
      simp only [tyBreakOk, List.head?_cons] at hc
      simp only [List.head?_cons, Option.all_some]
      rcases hc with hc | hc | hc | hc
      · simp [hc]
      · simp [hc]
      · simp [hc]
      · simp [hc]

/-- The head conditions for the ty scans' `r` sides (term lemmas —
    the `r` is inferred, so a tactic block there would meet a
    metavariable). -/
theorem headOk_lparen (X : List Char) :
    ('(' :: X).head?.all (fun c => !c.isAlphanum) := by simp

theorem headOk_lparen_d (X : List Char) :
    ('(' :: X).head?.all (fun c => !c.isDigit) := by simp

theorem headOk_rparen_d (X : List Char) :
    (')' :: X).head?.all (fun c => !c.isDigit) := by simp

/-! ## the ty token's parser (the hand-riding-TextKit zone) -/

/-- A `Ty` → `KeyTy` re-gate (the legacy `Ty.toKeyTy?` discipline: the
    key position is parsed as a ty then GATED back into the scalar
    sub-universe — a non-scalar key is unrepresentable in the type, and
    the parse refuses it loudly). -/
def keyOfTy : Ty → Option KeyTy
  | .bool => some .bool
  | .u64 => some .u64
  | .i64 => some .i64
  | .string => some .string
  | _ => none

/-- The ty token parser (fuel-bounded; the legacy `parseTy`'s shape over
    the slice's universe). Total: `0` fuel is the loud refusal; every
    recursive call consumes at least one character, so fuel = the input
    length is strictly sufficient (the caller passes exactly that).
    This is the tyAtom lexeme's scan engine — the recursion stays hand
    (the header's honest-state note). -/
def parseTy : Nat → List Char → Except String (Ty × List Char)
  | 0, _ => .error (snapshotDiag eSN0001 "parse fuel exhausted (malformed ty nesting)")
  | fuel + 1, cs =>
      -- the token scan rides TextKit: ONE maximal-prefix scan returning
      -- the token + the rest (`TextKit.takeWhile_stop` is its round-trip
      -- inversion). The scan is total, so the none arm is the monad
      -- carrier's shape, never a live path.
      match TextKit.Parser.takeWhile Char.isAlphanum cs with
      | none => .error (snapshotDiag eSN0002 "the token scan failed")
      | some (kw, rest) =>
        let one (k : Ty → Ty) : Except String (Ty × List Char) :=
          match rest with
          | '(' :: r =>
              match parseTy fuel r with
              | .ok (t, ')' :: r2) => .ok (k t, r2)
              | .ok (_, _) => .error (snapshotDiag eSN0003 "expected ')' after the ty argument")
              | .error e => .error e
          | _ => .error (snapshotDiag eSN0004 "expected '(' after the ty head")
        let two (k : Ty → Ty → Ty) : Except String (Ty × List Char) :=
          match rest with
          | '(' :: r =>
              match parseTy fuel r with
              | .ok (a, ',' :: r2) =>
                  match parseTy fuel r2 with
                  | .ok (b, ')' :: r3) => .ok (k a b, r3)
                  | .ok (_, _) => .error (snapshotDiag eSN0005 "expected ')' after the second ty argument")
                  | .error e => .error e
              | .ok (_, _) => .error (snapshotDiag eSN0006 "expected ',' between the ty arguments")
              | .error e => .error e
          | _ => .error (snapshotDiag eSN0004 "expected '(' after the ty head")
        let key (k : KeyTy → Ty → Ty) : Except String (Ty × List Char) :=
          match rest with
          | '(' :: r =>
              match parseTy fuel r with
              | .ok (kt, ',' :: r2) =>
                  match keyOfTy kt with
                  | none => .error (snapshotDiag eSN0007 "the map key is not a scalar key type")
                  | some kk =>
                      match parseTy fuel r2 with
                      | .ok (v, ')' :: r3) => .ok (k kk v, r3)
                      | .ok (_, _) => .error (snapshotDiag eSN0008 "expected ')' after the map's value type")
                      | .error e => .error e
              | .ok (_, _) => .error (snapshotDiag eSN0009 "expected ',' between the map's key and value")
              | .error e => .error e
          | _ => .error (snapshotDiag eSN0004 "expected '(' after the ty head")
        match kw with
        | "bool" => .ok (.bool, rest)
        | "u64" => .ok (.u64, rest)
        | "i64" => .ok (.i64, rest)
        | "string" => .ok (.string, rest)
        | "option" => one .option
        | "list" => one .list
        | "result" => two (fun a b => .result a b)
        | "map" => key (fun kk v => .map kk v)
        | "set" =>
            -- the scalar-key gate at the boundary (the legacy `set` arm):
            -- parse the element as a ty, re-gate into `KeyTy`
            match rest with
            | '(' :: r =>
                match parseTy fuel r with
                | .ok (kt, ')' :: r2) =>
                    match keyOfTy kt with
                    | none => .error (snapshotDiag eSN0010 "the set element is not a scalar key type")
                    | some kk => .ok (.set kk, r2)
                | .ok (_, _) => .error (snapshotDiag eSN0011 "expected ')' after the set element")
                | .error e => .error e
            | _ => .error (snapshotDiag eSN0012 "expected '(' after `set`")
        | "bounded" =>
            match rest with
            | '(' :: r =>
                match TextKit.scanNat r with
                | some (n, ')' :: r2) => .ok (.bounded n, r2)
                | some (_, _) => .error (snapshotDiag eSN0013 "expected ')' after the bounded cap")
                | none => .error (snapshotDiag eSN0014 "expected the bounded cap's digits")
            | _ => .error (snapshotDiag eSN0015 "expected '(' after `bounded`")
        | other =>
            -- the closed-world discipline: the legal space enumerated +
            -- the did-you-mean — the ONE engine (`Kit.suggestFor`) fills
            -- the envelope's `suggest` via `closedWorld`; the rendering
            -- carries the valid list + the suggestion suffix
            .error (Kit.Diag.toString (Kit.Diag.closedWorld eSN0016
              s!"snapshot: unknown type token `{other}`" .error other
              ["bool", "u64", "i64", "string", "option", "list", "result",
                "map", "set", "bounded"]))

/-- The key scalar's snapshot text scans back to the injected ty (the
    key positions parse as tys, then re-gate). -/
theorem parseTy_keyText (k : KeyTy) (fuel : Nat) (sfx : List Char)
    (h1 : 1 ≤ fuel) (h2 : tyBreakOk sfx) :
    parseTy fuel ((renderKeyTy k).toList ++ sfx) = .ok (k.toTy, sfx) := by
  have h2' := (headOk_break sfx h2).1
  cases fuel with
  | zero => omega
  | succ fuel =>
      cases k with
      | bool =>
          simp only [renderKeyTy,
            parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "bool".toList) (by decide) h2']
          simp [KeyTy.toTy]
      | u64 =>
          simp only [renderKeyTy,
            parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "u64".toList) (by decide) h2']
          simp [KeyTy.toTy]
      | i64 =>
          simp only [renderKeyTy,
            parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "i64".toList) (by decide) h2']
          simp [KeyTy.toTy]
      | string =>
          simp only [renderKeyTy,
            parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "string".toList) (by decide) h2']
          simp [KeyTy.toTy]

theorem keyOfTy_toTy (k : KeyTy) : keyOfTy k.toTy = some k := by
  cases k <;> rfl

/-- THE TY LAW: a ty's snapshot text scans back to the ty. Fuel is the
    budget the caller passes (the input length suffices — every
    recursion consumes a character). This is the tyAtom lexeme's
    `print_scan` base — the decode-after-encode direction's one home. -/
theorem parseTy_tyText (t : Ty) : ∀ (fuel : Nat) (sfx : List Char),
    tyDepth t ≤ fuel → tyBreakOk sfx →
    parseTy fuel ((tyText t).toList ++ sfx) = .ok (t, sfx) := by
  induction t with
  | bool =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          have h2' := (headOk_break sfx h2).1
          simp only [tyText_bool, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "bool".toList) (by decide) h2']
          simp
  | u64 =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          have h2' := (headOk_break sfx h2).1
          simp only [tyText_u64, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "u64".toList) (by decide) h2']
          simp
  | i64 =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          have h2' := (headOk_break sfx h2).1
          simp only [tyText_i64, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "i64".toList) (by decide) h2']
          simp
  | string =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          have h2' := (headOk_break sfx h2).1
          simp only [tyText_string, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "string".toList) (by decide) h2']
          simp
  | option t ih =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_option, String.toList_append, List.cons_append, TextKit.lit_lparen,
            TextKit.lit_rparen, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "option".toList) (by decide) (headOk_lparen _)]
          simp
          rw [ih fuel (')' :: sfx) (by omega) (by simp [tyBreakOk])]
          simp
  | list t ih =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_list, String.toList_append, List.cons_append, TextKit.lit_lparen,
            TextKit.lit_rparen, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "list".toList) (by decide) (headOk_lparen _)]
          simp
          rw [ih fuel (')' :: sfx) (by omega) (by simp [tyBreakOk])]
          simp
  | result a b iha ihb =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_result, String.toList_append, List.cons_append, TextKit.lit_lparen,
            TextKit.lit_rparen, TextKit.lit_comma, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "result".toList) (by decide) (headOk_lparen _)]
          simp
          rw [iha fuel (',' :: ((tyText b).toList ++ (')' :: sfx)))
            (by omega) (by simp [tyBreakOk])]
          simp
          rw [ihb fuel (')' :: sfx) (by omega) (by simp [tyBreakOk])]
          simp
  | map k v ihv =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_map, String.toList_append, List.cons_append, TextKit.lit_lparen,
            TextKit.lit_rparen, TextKit.lit_comma, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "map".toList) (by decide) (headOk_lparen _)]
          simp
          rw [parseTy_keyText k fuel
            (',' :: ((tyText v).toList ++ (')' :: sfx)))
            (by have := tyDepth_pos v; omega) (by simp [tyBreakOk])]
          simp
          rw [keyOfTy_toTy k]
          simp
          rw [ihv fuel (')' :: sfx) (by omega) (by simp [tyBreakOk])]
          simp
  | set k =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_set, String.toList_append, List.cons_append, TextKit.lit_lparen,
            TextKit.lit_rparen, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "set".toList) (by decide) (headOk_lparen _)]
          simp
          rw [parseTy_keyText k fuel (')' :: sfx) (by omega)
            (by simp [tyBreakOk])]
          simp
          rw [keyOfTy_toTy k]
  | bounded n =>
      intro fuel sfx h1 h2
      simp only [tyDepth] at h1
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [tyText_bounded, String.toList_append, List.cons_append, TextKit.lit_lparen,
            TextKit.lit_rparen, List.append_assoc, List.nil_append, parseTy]
          rw [TextKit.takeWhile_stop (p := Char.isAlphanum)
            (w := "bounded".toList) (by decide) (headOk_lparen _)]
          simp
          rw [scanNat_natText n (')' :: sfx) (headOk_rparen_d sfx)]
          simp

theorem renderKeyTy_pos (k : KeyTy) : 1 ≤ (renderKeyTy k).length := by
  cases k <;> simp only [renderKeyTy] <;> decide

theorem lenB : "bool".length = 4 := by decide
theorem lenU : "u64".length = 3 := by decide
theorem lenI : "i64".length = 3 := by decide
theorem lenS : "string".length = 6 := by decide
theorem lenO : "option".length = 6 := by decide
theorem lenL : "list".length = 4 := by decide
theorem lenR : "result".length = 6 := by decide
theorem lenM : "map".length = 3 := by decide
theorem lenT : "set".length = 3 := by decide
theorem lenBd : "bounded".length = 7 := by decide
theorem lenPl : "(".length = 1 := by decide
theorem lenPr : ")".length = 1 := by decide
theorem lenCm : ",".length = 1 := by decide

theorem tyDepth_le_tyText (t : Ty) : tyDepth t ≤ (tyText t).length := by
  induction t with
  | bool => simp [tyDepth, tyText_bool, lenB]
  | u64 => simp [tyDepth, tyText_u64, lenU]
  | i64 => simp [tyDepth, tyText_i64, lenI]
  | string => simp [tyDepth, tyText_string, lenS]
  | option t ih =>
      simp [tyDepth, tyText_option, String.length_append, lenPr]; omega
  | list t ih =>
      simp [tyDepth, tyText_list, String.length_append, lenPr]; omega
  | result a b iha ihb =>
      simp [tyDepth, tyText_result, String.length_append, lenPr, lenCm]
      omega
  | map k v ihv =>
      have hk := renderKeyTy_pos k
      simp only [tyDepth, tyText_map, String.length_append, lenM, lenPl, lenPr,
        lenCm]
      omega
  | set k =>
      have hk := renderKeyTy_pos k
      simp only [tyDepth, tyText_set, String.length_append, lenT, lenPl, lenPr]
      omega
  | bounded n =>
      have h1 : 1 ≤ (natText n).toList.length := by
        cases hl : (natText n).toList with
        | nil => exact absurd hl (natText_ne n)
        | cons c cs => simp
      have h2 : (natText n).length = (natText n).toList.length :=
        (String.length_toList (s := natText n)).symm
      simp only [tyDepth, tyText_bounded, String.length_append, lenBd, lenPl, lenPr]
      rw [h2]
      omega

/-! ## the item level — THE GRAMMAR (the flat rep-of-lines face) -/

open TextKit

/-! ### the lexemes

The maximal-munch boundary lemmas live in the shared kit
(`TextKit.Grammar.Lexemes`: `takeWhile_append_stop`/`dropWhile_append_stop`
+ `mem_takeWhile`) — the former local copies deleted; the one home.
-/

/-- The expect-success inversion (the lit-scan's extraction). -/
private theorem expect_some (s : String) (cs rest : List Char)
    (h : TextKit.expect s cs = some rest) : cs = s.toList ++ rest := by
  simp only [TextKit.expect, TextKit.startsWith] at h
  cases hb : s.toList.isPrefixOf cs with
  | false => simp [hb] at h
  | true =>
      simp only [hb, if_pos] at h
      obtain ⟨t, e⟩ := List.isPrefixOf_iff_prefix.mp hb
      subst e
      have hdrop : (s.toList ++ t).drop s.length = t := by
        simp [String.length_toList]
      simp only [hdrop, Option.some.injEq] at h
      rw [h]

/-- The expect-failure inversion: no literal prefix, no scan. -/
private theorem expect_none (s : String) (cs : List Char)
    (h : TextKit.expect s cs = Option.none) : s.toList.isPrefixOf cs = false := by
  simp only [TextKit.expect, TextKit.startsWith] at h
  cases hb : s.toList.isPrefixOf cs with
  | false => rfl
  | true => simp only [hb, if_pos] at h; simp at h

/-- The multi-char literal's scan: TextKit.expect (the kit's prefix
    consumer) + the loud refusal. -/
def litScan (s : String) : GParser Unit := fun cur =>
  match TextKit.expect s cur.cs with
  | Option.none => .error (ParseError.base cur.off [s])
  | Option.some rest => .ok ((), ⟨cur.off + s.length, rest⟩)

/-- The multi-char literal lexeme (the keyword faces `item `/` field `):
    prints the literal, scans exactly it, unit payload, no munch (the
    hard delimiters carry no maximal-munch boundary). Requires a
    nonempty literal (the consumes-≥1-char honesty). -/
def litLex (s : String) (hs : s.toList ≠ []) : Lexeme Unit where
  scan := litScan s
  print := fun _ => s
  pre := fun _ => true
  head := .lit s
  munch := Option.none
  scan_post := fun _ _ _ _ => rfl
  scan_exact := by
    intro cur u cur' h
    simp only [litScan] at h
    cases hex : TextKit.expect s cur.cs with
    | none => rw [hex] at h; simp at h
    | some rest =>
        rw [hex] at h
        obtain ⟨h0, hcc⟩ := Prod.mk.inj (Except.ok.inj h)
        have h1 := Cursor.mk.inj hcc
        rw [← h1.right]
        exact expect_some s cur.cs rest hex
  scan_off := by
    intro cur u cur' h
    simp only [litScan] at h
    cases hex : TextKit.expect s cur.cs with
    | none => rw [hex] at h; simp at h
    | some rest =>
        rw [hex] at h
        obtain ⟨h0, hcc⟩ := Prod.mk.inj (Except.ok.inj h)
        have h1 := Cursor.mk.inj hcc
        show cur'.off = cur.off + s.length
        rw [h1.left.symm]
  scan_head := by
    intro cur u cur' h
    cases hex : TextKit.expect s cur.cs with
    | none =>
        simp only [litScan, hex] at h
        simp at h
    | some rest =>
        show s.toList.isPrefixOf cur.cs = true
        rw [expect_some s cur.cs rest hex]
        exact TextKit.startsWith_self s rest
  head_fail := by
    intro cur h
    refine ⟨ParseError.base cur.off [s], ?_⟩
    show litScan s cur = Except.error _
    have h' : s.toList.isPrefixOf cur.cs = false := h
    simp only [litScan, TextKit.expect, TextKit.startsWith, h']
    simp
  print_scan := by
    intro k u sfx _ _
    show litScan s ⟨k, s.toList ++ sfx⟩ = .ok ((), ⟨k + s.length, sfx⟩)
    simp only [litScan, TextKit.expect, TextKit.startsWith]
    have h1 : s.length = s.toList.length := String.length_toList (s := s)
    simp [h1]
  consumes := by
    intro cur u cur' h
    simp only [litScan] at h
    cases hex : TextKit.expect s cur.cs with
    | none => rw [hex] at h; simp at h
    | some rest =>
        rw [hex] at h
        obtain ⟨h0, hcc⟩ := Prod.mk.inj (Except.ok.inj h)
        have h1 := Cursor.mk.inj hcc
        have h2 := expect_some s cur.cs rest hex
        rw [h2, List.length_append, ← h1.right]
        have hl : 0 < s.toList.length := by
          cases hsl : s.toList with
          | nil => exact absurd hsl hs
          | cons c0 cs0 => simp
        omega
  head_ne := by
    show s.toList.isPrefixOf [] = false
    cases hsl : s.toList with
    | nil => exact absurd hsl hs
    | cons c cs => simp

/-- The keyword/separator literals (the format's hard delimiters). -/
def itemAtom : Lexeme Unit := litLex "item " (by decide)
def fieldAtom : Lexeme Unit := litLex " field " (by decide)
def spAtom : Lexeme Unit := TextKit.constCharLex ' ' ()
def nlAtom : Lexeme Unit := TextKit.constCharLex '\n' ()

/-- The name lexeme: the shared ident-atom over the sep-free charset —
    its `pre` IS `nameOk` (definitionally: the write-side gate and the
    value discipline are ONE function). -/
def nameAtom : Lexeme String := TextKit.identAtom "<name>" sepOk sepOk (fun _ hc => hc)

/-- The ty token's scan: the hand `parseTy` over the maximal sep-free
    token, GUARDED to the canonical spelling (the scanned token must BE
    `tyText` of its result — a well-formed but non-canonical token, e.g.
    `bounded(042)`, is a refusal; the accepted-set tightening matches
    the design's `natLex` note). The guard is what makes `scan_exact`
    hold without a canonicality theorem: the accepted language IS the
    image of `tyText`. -/
def tyScan : GParser Ty := fun cur =>
  match parseTy (cur.cs.takeWhile sepOk).length (cur.cs.takeWhile sepOk) with
  | .error e => .error { ParseError.base cur.off [] with message := e }
  | .ok (t, _) =>
      if (tyText t).toList = cur.cs.takeWhile sepOk then
        .ok (t, ⟨cur.off + (cur.cs.takeWhile sepOk).length, cur.cs.dropWhile sepOk⟩)
      else
        .error { ParseError.base cur.off [] with
                 message := snapshotDiag eSN0025 "trailing garbage in a ty token" }

/-- The ty token's scan shape (the lexeme fields' shared extraction):
    success splits the cursor at the token boundary and passes the
    canonical guard. -/
theorem tyScan_ok {cur : Cursor} {t : Ty} {cur' : Cursor}
    (h : tyScan cur = .ok (t, cur')) :
    (tyText t).toList = cur.cs.takeWhile sepOk ∧
    cur'.cs = cur.cs.dropWhile sepOk ∧
    cur'.off = cur.off + (cur.cs.takeWhile sepOk).length := by
  simp only [tyScan] at h
  cases hp : parseTy (cur.cs.takeWhile sepOk).length (cur.cs.takeWhile sepOk) with
  | error e => rw [hp] at h; simp at h
  | ok r =>
      obtain ⟨t0, rest⟩ := r
      rw [hp] at h
      simp only [] at h
      by_cases hg : (tyText t0).toList = cur.cs.takeWhile sepOk
      · rw [if_pos hg] at h
        obtain ⟨h01, h02⟩ := Prod.mk.inj (Except.ok.inj h)
        have h1 := Cursor.mk.inj h02
        rw [show t0 = t from h01] at hg
        exact ⟨hg, h1.right.symm, h1.left.symm⟩
      · rw [if_neg hg] at h; simp at h

/-- A non-alphanum-led input never parses as a ty (the empty keyword
    arm is the refusal — the tyAtom's `head_fail` base). -/
theorem parseTy_error_of_head (fuel : Nat) (cs : List Char)
    (h : cs.head?.all (fun c => !c.isAlphanum) = true) :
    ∃ e, parseTy fuel cs = .error e := by
  cases fuel with
  | zero => exact ⟨_, rfl⟩
  | succ fuel =>
      cases cs with
      | nil => exact ⟨_, rfl⟩
      | cons c cs' =>
          have hc : Char.isAlphanum c = false := by
            have h2 := h
            simp only [List.head?_cons, Option.all_some] at h2
            simpa using h2
          simp only [parseTy]
          have htw : TextKit.Parser.takeWhile Char.isAlphanum (c :: cs')
              = (String.ofList [], c :: cs') := by
            show (some (String.ofList ((c :: cs').takeWhile Char.isAlphanum),
              (c :: cs').dropWhile Char.isAlphanum)) = _
            simp [hc]
          rw [htw]
          simp

/-- The ty token lexeme: `print = tyText` (the ONE spelling), the scan
    above, no write-side gate beyond the canonical guard (`pre` const —
    the printed bytes are `tyText`'s by construction), FIRST the
    alphanum class (every spelling is keyword-led), munch the sep-free
    class (the space/LF separators ALWAYS break the token). -/
def tyAtom : Lexeme Ty where
  scan := tyScan
  print := tyText
  pre := fun _ => true
  head := .cls Char.isAlphanum
  munch := Option.some sepOk
  scan_post := fun _ _ _ _ => rfl
  scan_exact := by
    intro cur t cur' h
    obtain ⟨hg, hcs, -⟩ := tyScan_ok h
    show cur.cs = (tyText t).toList ++ cur'.cs
    rw [hg, hcs, List.takeWhile_append_dropWhile]
  scan_off := by
    intro cur t cur' h
    obtain ⟨hg, -, hoff⟩ := tyScan_ok h
    show cur'.off = cur.off + (tyText t).length
    rw [hoff, ← String.length_toList, ← hg]
  scan_head := by
    intro cur t cur' h
    obtain ⟨hg, -, -⟩ := tyScan_ok h
    show cur.cs.head?.any Char.isAlphanum = true
    cases hcs : cur.cs with
    | nil =>
        rw [hcs] at hg
        simp only [List.takeWhile_nil] at hg
        exact absurd (String.toList_eq_nil_iff.mp hg) (by
          intro he
          have h2 := tyText_ne_nil t
          rw [he] at h2
          simp at h2)
    | cons c cs =>
        have hsep : sepOk c = true := by
          rw [hcs] at hg
          cases hsep' : sepOk c with
          | false =>
              simp only [List.takeWhile_cons, hsep'] at hg
              exact absurd (String.toList_eq_nil_iff.mp hg) (by
                intro he
                have h2 := tyText_ne_nil t
                rw [he] at h2
                simp at h2)
          | true => rfl
        have htw : (c :: cs).takeWhile sepOk = c :: cs.takeWhile sepOk := by
          simp [hsep]
        rw [hcs] at hg
        rw [htw] at hg
        rw [List.head?_cons, Option.any_some]
        have hall := tyText_head t
        rw [show (tyText t).toList.head? = some c from by rw [hg]; rfl] at hall
        simpa using hall
  head_fail := by
    intro cur h
    simp only [tyScan]
    have h2 : (cur.cs.takeWhile sepOk).head?.all (fun c => !c.isAlphanum) = true := by
      cases hcs : cur.cs with
      | nil => simp
      | cons c cs =>
          have hc : Char.isAlphanum c = false := by
            have h3 := h
            rw [hcs] at h3
            simp only [HeadSpec.matches, List.head?_cons, Option.any_some] at h3
            exact h3
          simp only [List.takeWhile_cons]
          cases hsep : sepOk c with
          | false => simp
          | true => simp [hc]
    obtain ⟨e, he⟩ := parseTy_error_of_head
      ((cur.cs.takeWhile sepOk).length) (cur.cs.takeWhile sepOk) h2
    exact ⟨{ ParseError.base cur.off [] with message := e }, by simp only [he]⟩
  print_scan := by
    intro k t sfx _ hmunch
    show tyScan ⟨k, (tyText t).toList ++ sfx⟩ = .ok (t, ⟨k + (tyText t).length, sfx⟩)
    simp only [tyScan]
    have hall : (tyText t).toList.all sepOk = true := tyText_sepOk t
    have htw : ((tyText t).toList ++ sfx).takeWhile sepOk = (tyText t).toList :=
      takeWhile_append_stop _ _ (List.all_eq_true.mp hall) hmunch
    have hdr : ((tyText t).toList ++ sfx).dropWhile sepOk = sfx :=
      dropWhile_append_stop _ _ (List.all_eq_true.mp hall) hmunch
    have hlaw := parseTy_tyText t (tyText t).toList.length []
      (tyDepth_le_tyText t) (by simp [tyBreakOk])
    rw [List.append_nil] at hlaw
    rw [htw, hdr, hlaw]
    simp
    exact (String.length_toList (s := tyText t)).symm
  consumes := by
    intro cur t cur' h
    obtain ⟨hg, hcs, -⟩ := tyScan_ok h
    have h1 : cur.cs = (tyText t).toList ++ cur'.cs := by
      rw [hg, hcs, List.takeWhile_append_dropWhile]
    rw [h1, List.length_append]
    have hl : 0 < (tyText t).toList.length := by
      cases hsl : (tyText t).toList with
      | nil => exact absurd hsl (tyText_ne_nil t)
      | cons c0 cs0 => simp
    omega
  head_ne := rfl

/-! ### the raw shapes + the codec -/

/-- One field's raw parse shape: the ` field ` marker, the name, the
    space, the ty token. -/
abbrev FieldRaw := Unit × (String × (Unit × Ty))

def fieldToRaw (f : Field) : FieldRaw := ((), (f.name, ((), f.ty)))

def fieldOfRaw : FieldRaw → Field := fun (_, (fn, (_, t))) => ⟨fn, t⟩

theorem fieldOfRaw_toRaw (f : Field) : fieldOfRaw (fieldToRaw f) = f := rfl

theorem map_fieldToRaw_fieldOfRaw (fs : List Field) :
    (fs.map fieldToRaw).map fieldOfRaw = fs := by
  induction fs with
  | nil => rfl
  | cons f rest ih => simp [fieldOfRaw_toRaw, ih]

theorem map_fieldOfRaw_fieldToRaw (fs : List FieldRaw) :
    (fs.map fieldOfRaw).map fieldToRaw = fs := by
  induction fs with
  | nil => rfl
  | cons f rest ih => simp [fieldToRaw, fieldOfRaw, ih]

/-- One line's raw parse shape: the `item ` marker, the name, the field
    run — plus the line's LF terminator (the line's SECOND component;
    the terminator is a hard atom, the header's LF discipline). -/
abbrev LineRaw := Unit × (String × List FieldRaw)

def itemToRaw (it : Item) : LineRaw := ((), (it.name, it.fields.map fieldToRaw))

def itemOfRaw : LineRaw → Item := fun (_, (nm, fs)) => ⟨nm, fs.map fieldOfRaw⟩

theorem itemOfRaw_toRaw (it : Item) : itemOfRaw (itemToRaw it) = it := by
  show ⟨it.name, (it.fields.map fieldToRaw).map fieldOfRaw⟩ = it
  rw [map_fieldToRaw_fieldOfRaw]

def linesToRaw (items : List Item) : List (LineRaw × Unit) :=
  items.map (fun it => (itemToRaw it, ()))

def itemsOfRaws : List (LineRaw × Unit) → Option (List Item)
  | [] => some []
  | (raw, ()) :: rest => (itemsOfRaws rest).map (fun its => itemOfRaw raw :: its)

/-- THE snapshot codec (the ONE `rel` node's semantic mapping): the raw
    IS the line list; decode unmaps the items. -/
def itemsCodec : Kit.Codec (List (LineRaw × Unit)) (List Item) where
  encode := linesToRaw
  decode := itemsOfRaws
  policy := fun _ => True
  decode_encode := by
    intro items
    induction items with
    | nil => rfl
    | cons it rest ih =>
        show itemsOfRaws ((itemToRaw it, ()) :: linesToRaw rest) = some (it :: rest)
        simp only [itemsOfRaws]
        rw [ih, Option.map_some, itemOfRaw_toRaw]
  decode_some_policy := fun _ _ _ => trivial

/-- The codec's left-inverse (the rel node's exact field): decode
    determines encode — the raw spelling is recovered. (Public: the
    graduation's exactness premise cites it.) -/
theorem itemsCodec_exact (raws : List (LineRaw × Unit)) (its : List Item)
    (h : itemsOfRaws raws = some its) : linesToRaw its = raws := by
  induction raws generalizing its with
  | nil =>
      have h1 : itemsOfRaws ([] : List (LineRaw × Unit)) = some [] := rfl
      rw [h1, Option.some.injEq] at h
      rw [← h]
      rfl
  | cons raw rest ih =>
      obtain ⟨raw0, u⟩ := raw
      cases u
      simp only [itemsOfRaws] at h
      cases hp : itemsOfRaws rest with
      | none => rw [hp] at h; simp at h
      | some its' =>
          rw [hp] at h
          simp only [Option.map_some, Option.some.injEq] at h
          have hraw : itemToRaw (itemOfRaw raw0) = raw0 := by
            obtain ⟨nm, fs⟩ := raw0
            cases nm
            simp only [itemToRaw, itemOfRaw, map_fieldOfRaw_fieldToRaw]
          subst h
          show ((itemToRaw (itemOfRaw raw0), ()) :: linesToRaw its')
            = (raw0, ()) :: rest
          rw [hraw, ih its' hp]

-- THE GRADUATION (15-patterns #11 at the codec grade,
-- `Kit.Codec.toIsoOfExact`): the total decode + the exactness law
-- (`itemsCodec_exact`) assemble the TRUE `Iso` — the raw line list ≅
-- the item list, both round trips.
/-- The decode's TOTALITY as data (the graduation's witness function):
    the raw line list never refuses — every line decodes (the item
    level is total: `itemOfRaw` is total) and the fold recurses. -/
def itemsOfRawsTotal : ∀ (raws : List (LineRaw × Unit)),
    {its : List Item // itemsOfRaws raws = some its}
  | [] => ⟨[], rfl⟩
  | (raw, ()) :: rest =>
      let t := itemsOfRawsTotal rest
      ⟨itemOfRaw raw :: t.1, by simp only [itemsOfRaws, t.2, Option.map_some]⟩

/-- THE GRADUATION'S VALUE: the raw line list ≅ the item list — a TRUE
    `Kit.Iso` from the snapshot codec's total decode + exactness. -/
def snapshotIso : Kit.Iso (List (LineRaw × Unit)) (List Item) :=
  itemsCodec.toIsoOfExact itemsOfRawsTotal itemsCodec_exact

/-! ### the lane-row face (wave-30 A2: the snapshot covers the lanes)

The ONE log's integral is the universe: the SCHEMA lane's rows at
their rich item face (the `item` lines), every OTHER lane's rows at
the identity face — `lane <laneid> <name>` lines. The lane-row case
is a SECTION after the item lines (two reps, no `alt` — the markers
are prefix-distinct), so the grammar-layer laws stay instances of the
same generic theorems over the extended grammar value; nothing is
re-proved by hand. -/

/-- The snapshot's universe: the ONE log's integral, routed — the
    schema lane's rows richly + every other lane's registered rows as
    `(lane id, item name)` pairs. -/
structure Universe where
  /-- The schema lane's rows, at the rich item face. -/
  items : List Item
  /-- Every other lane's rows: the lane id + the item's registered
      name (the identity face — the log's rows ARE the data). -/
  lanes : List (String × String)
  deriving Inhabited, Repr, BEq

/-- The lane-line lexeme: ` lane ` (prefix-distinct from `item ` —
    the two sections' heads are disjoint, the WF rows' prefix-freeness
    is structural). -/
def laneAtom : Lexeme Unit := litLex "lane " (by decide)

/-- One lane row's part: `lane <laneid> <name>` (both names ride the
    ONE name atom — the same sep-free ident discipline as the item
    names; the lane id's dotted spelling is sep-free). -/
def lanePartG : Grammar (Unit × (String × (Unit × String))) :=
  .seq (.atom laneAtom) (.seq (.atom nameAtom) (.seq (.atom spAtom) (.atom nameAtom)))

/-- One lane line: the lane row's part + the LF terminator. -/
def laneLineG : Grammar ((Unit × (String × (Unit × String))) × Unit) :=
  .seq lanePartG (.atom nlAtom)

/-- One lane line's raw parse shape. -/
abbrev LaneRaw := (Unit × (String × (Unit × String))) × Unit

def laneToRaw (l : String × String) : LaneRaw := (((), (l.1, ((), l.2))), ())

def laneOfRaw : LaneRaw → String × String := fun ((_, (l, (_, n))), _) => (l, n)

def laneLinesToRaw (lanes : List (String × String)) : List LaneRaw :=
  lanes.map laneToRaw

def lanesOfRaws : List LaneRaw → Option (List (String × String))
  | [] => some []
  | raw :: rest => (lanesOfRaws rest).map (fun ls => laneOfRaw raw :: ls)

theorem laneOfRaw_toRaw (l : String × String) : laneOfRaw (laneToRaw l) = l := rfl

theorem lanesOfRaws_encode (lanes : List (String × String)) :
    lanesOfRaws (laneLinesToRaw lanes) = some lanes := by
  induction lanes with
  | nil => rfl
  | cons l rest ih =>
      show lanesOfRaws (laneToRaw l :: laneLinesToRaw rest) = some (l :: rest)
      simp only [lanesOfRaws, ih, Option.map_some, laneOfRaw_toRaw]

theorem lanesOfRaws_encode_of (raws : List LaneRaw) (ls : List (String × String))
    (h : lanesOfRaws raws = some ls) : laneLinesToRaw ls = raws := by
  induction raws generalizing ls with
  | nil =>
      rw [lanesOfRaws] at h
      cases ls with
      | nil => rfl
      | cons _ _ => simp at h
  | cons raw rest ih =>
      simp only [lanesOfRaws] at h
      cases hp : lanesOfRaws rest with
      | none => rw [hp] at h; simp at h
      | some ls' =>
          rw [hp] at h
          simp only [Option.map_some, Option.some.injEq] at h
          have hraw : laneToRaw (laneOfRaw raw) = raw := by
            obtain ⟨a, b⟩ := raw
            obtain ⟨c, d⟩ := a
            obtain ⟨e, f⟩ := d
            rfl
          subst h
          show (laneToRaw (laneOfRaw raw) :: laneLinesToRaw ls') = raw :: rest
          rw [hraw, ih ls' hp]

/-- The universe codec's decode (a standalone function — the match's
    equations are what the proofs walk). -/
def universeDecode (raws : List (LineRaw × Unit)) (laneRaws : List LaneRaw) :
    Option Universe :=
  match itemsOfRaws raws with
  | none => none
  | .some its => (lanesOfRaws laneRaws).map (fun ls => { items := its, lanes := ls })

/-- THE universe codec (the ONE `rel` node at the file level): the raw
    is the two sections' line lists; decode unmaps both. -/
def universeCodec :
    Kit.Codec (List (LineRaw × Unit) × List LaneRaw) Universe where
  encode := fun u => (linesToRaw u.items, laneLinesToRaw u.lanes)
  decode := fun (raws, laneRaws) => universeDecode raws laneRaws
  policy := fun _ => True
  decode_encode := by
    intro u
    have hi : itemsOfRaws (linesToRaw u.items) = some u.items :=
      itemsCodec.decode_encode u.items
    have hl : lanesOfRaws (laneLinesToRaw u.lanes) = some u.lanes :=
      lanesOfRaws_encode u.lanes
    show universeDecode (linesToRaw u.items) (laneLinesToRaw u.lanes) = some u
    simp only [universeDecode]
    rw [hi, hl]
    rfl
  decode_some_policy := fun _ _ _ => trivial

/-- The codec's left-inverse at the file level: decode determines
    encode. -/
theorem universeCodec_exact (raws : List (LineRaw × Unit)) (laneRaws : List LaneRaw)
    (u : Universe) (h : universeDecode raws laneRaws = some u) :
    (linesToRaw u.items, laneLinesToRaw u.lanes) = (raws, laneRaws) := by
  simp only [universeDecode] at h
  cases hp : itemsOfRaws raws with
  | none =>
      rw [hp] at h
      simp at h
  | some its =>
      rw [hp] at h
      cases hlp : lanesOfRaws laneRaws with
      | none => rw [hlp] at h; simp at h
      | some ls =>
          rw [hlp] at h
          simp only [Option.map_some, Option.some.injEq] at h
          obtain ⟨hi, hl⟩ := Universe.mk.inj h
          have hitems : linesToRaw its = raws := itemsCodec_exact raws its hp
          have hh : lanesOfRaws laneRaws = some u.lanes := by rw [← hl]; exact hlp
          have hlanes : laneLinesToRaw u.lanes = laneRaws :=
            lanesOfRaws_encode_of laneRaws u.lanes hh
          show (linesToRaw u.items, laneLinesToRaw u.lanes) = (raws, laneRaws)
          rw [← hi, hitems, hlanes]

/-- The lane face's decode totality (the universe witness's second
    leg): the lane rows never refuse — every lane line decodes (the
    `laneOfRaw` unmapping is total) and the fold recurses. Same shape
    as `itemsOfRawsTotal`. -/
def lanesOfRawsTotal : ∀ (raws : List LaneRaw),
    {ls : List (String × String) // lanesOfRaws raws = some ls}
  | [] => ⟨[], rfl⟩
  | raw :: rest =>
      let t := lanesOfRawsTotal rest
      ⟨laneOfRaw raw :: t.1, by simp only [lanesOfRaws, t.2, Option.map_some]⟩

/-- THE universe codec's graduation witness (the totality as data,
    `itemsOfRawsTotal`'s shape at the file grade): both sections'
    decodes are total, so the pair never refuses. -/
def universeOfRawsTotal : ∀ (raws : List (LineRaw × Unit)) (laneRaws : List LaneRaw),
    {u : Universe // universeDecode raws laneRaws = some u} :=
  fun raws laneRaws =>
    let t := itemsOfRawsTotal raws
    let l := lanesOfRawsTotal laneRaws
    ⟨{ items := t.1, lanes := l.1 }, by
        simp only [universeDecode, t.2, l.2, Option.map_some]⟩

/-- THE GRADUATION (15-patterns #11 at the codec grade,
    `snapshotIso`'s precedent one section up): the universe codec's
    total decode (`universeOfRawsTotal`) + the exactness law
    (`universeCodec_exact`) assemble the TRUE `Iso` — the two
    sections' line lists ≅ the universe, both round trips. -/
def universeIso : Kit.Iso (List (LineRaw × Unit) × List LaneRaw) Universe :=
  universeCodec.toIsoOfExact (fun a => universeOfRawsTotal a.1 a.2)
    (fun _ _ h => universeCodec_exact _ _ _ h)

/-- One field: ` field <fname> <tytext>` (the marker atom, the name
    atom, the separating space, the ty token). -/
def fieldG : Grammar FieldRaw :=
  .seq (.atom fieldAtom) (.seq (.atom nameAtom) (.seq (.atom spAtom) (.atom tyAtom)))

/-- One item's part: `item <name>` + its field run (zero or more
    fields; the LF terminator lives at the line level). -/
def itemPartG : Grammar (Unit × (String × List FieldRaw)) :=
  .seq (.atom itemAtom) (.seq (.atom nameAtom) (.rep fieldG))

/-- One line: the item part + the LF terminator (the header's LF
    discipline: every line newline-terminated). -/
def lineG : Grammar (LineRaw × Unit) := .seq itemPartG (.atom nlAtom)

/-- THE file format as a grammar value: the flat rep-of-lines (no `fix`,
    no `self` anywhere — the ty token is the `tyAtom` leaf; the header's
    honest-state note), under the universe codec (the ONE `rel` node;
    the raw IS the two sections' line lists — the item face, then the
    lane face; wave-30 A2's lane-row coverage). -/
def snapshotGrammar : Grammar Universe :=
  .rel universeCodec (fun _ => true) (fun _ _ _ => rfl)
    (fun raw r h => universeCodec_exact raw.1 raw.2 r h)
    "snapshot" [] (.seq (.rep lineG) (.rep laneLineG))

/-- Insert by (lane id, name) — the lane section's rows stay sorted;
    the log's nodup-per-lane makes the order total per lane. The
    comparison is the EXPLICIT lexicographic pair (no Prod LT instance
    in core). -/
def laneLexLt (a b : String × String) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def insertLane (l : String × String) : List (String × String) → List (String × String)
  | [] => [l]
  | r :: rs => if laneLexLt l r then l :: r :: rs
      else r :: insertLane l rs

/-- Canonical lane order: sorted by (lane id, name). `print` sorts. -/
def canonicalLanes : List (String × String) → List (String × String)
  | [] => []
  | l :: ls => insertLane l (canonicalLanes ls)

/-- Canonical form of the universe: both sections sorted. -/
def canonicalU (u : Universe) : Universe :=
  { items := canonical u.items, lanes := canonicalLanes u.lanes }

theorem insertLane_mem (y : String × String) (l : List (String × String))
    (x : String × String) : x ∈ insertLane y l ↔ x = y ∨ x ∈ l := by
  induction l with
  | nil => simp [insertLane]
  | cons z zs ih =>
      simp only [insertLane]
      split
      · simp []
      · constructor
        · intro h
          rcases List.mem_cons.mp h with hx | h
          · simp [hx]
          · rcases ih.mp h with hx | hx
            · exact Or.inl hx
            · simp [hx]
        · intro h
          rcases h with hx | h
          · simp [ih.mpr (Or.inl hx)]
          · rcases List.mem_cons.mp h with hx | hx
            · simp [hx]
            · simp [ih.mpr (Or.inr hx)]

theorem canonicalLanes_mem (l : List (String × String)) (x : String × String) :
    x ∈ canonicalLanes l ↔ x ∈ l := by
  induction l with
  | nil => simp [canonicalLanes]
  | cons y ys ih => simp [canonicalLanes, insertLane_mem y (canonicalLanes ys) x, ih]

/-- Every lane row's two names pass `nameOk` (the lane id's dotted
    spelling is sep-free). -/
def lanesOk (lanes : List (String × String)) : Bool :=
  lanes.all (fun l => nameOk l.1 && nameOk l.2)

/-- The universe's write-side gate: every item/field name AND every
    lane row's two names are `nameOk`. -/
def universeOk (u : Universe) : Bool :=
  namesOk u.items && lanesOk u.lanes

theorem lanesOk_spec (lanes : List (String × String)) (h : lanesOk lanes) :
    ∀ x ∈ lanes, nameOk x.1 = true ∧ nameOk x.2 = true := by
  intro x hx
  have h2 := List.all_eq_true.mp h x hx
  exact Bool.and_eq_true_iff.mp h2

theorem namesOk_canonical (items : List Item) (hok : namesOk items) :
    namesOk (canonical items) = true := by
  rw [namesOk, List.all_eq_true]
  intro x hx
  obtain ⟨h1, h2⟩ := namesOk_spec items hok x ((canonical_mem items x).mp hx)
  exact Bool.and_eq_true_iff.mpr ⟨h1, List.all_eq_true.mpr h2⟩

theorem lanesOk_canonical (lanes : List (String × String)) (hok : lanesOk lanes) :
    lanesOk (canonicalLanes lanes) = true := by
  rw [lanesOk, List.all_eq_true]
  intro x hx
  obtain ⟨h1, h2⟩ := lanesOk_spec lanes hok x ((canonicalLanes_mem lanes x).mp hx)
  exact Bool.and_eq_true_iff.mpr ⟨h1, h2⟩

/-! ### the certificate + the law premises' discharge -/

/-- THE certificate discharge (06 §7's build-time check): the format's
    WF rows hand-check green (WF-REP-1: the line is non-nullable — the
    LF terminator is an atom; WF-REP-2: the field run's tail munch
    (the ty token's sep-free class) is broken by ` field`'s space head;
    WF-SEQ-1: the stop heads vs the LF literal are prefix-free;
    WF-SEQ-2: the sep-free munches are broken by the space/LF
    followers). -/
theorem snapshotCert : Grammar.Predictive snapshotGrammar :=
  Grammar.wfCheck_sound snapshotGrammar (by decide)

/-- The fix-free fold (no `fix` node anywhere — the ty token is a
    leaf). -/
theorem snapshotFixFree : Grammar.FixFree snapshotGrammar := by
  repeat constructor

/-- Law 2's coherence premise: NO `alt` node anywhere — the fold's
    branches are all trivial. -/
theorem snapshotCoherent : Grammar.altCoherent snapshotGrammar := by
  repeat constructor

/-- The grammar's value discipline IS the name discipline: `valueOk`
    holds exactly when every item/field name is `nameOk` (the name
    lexeme's write-side gate; every other field is trivially owned —
    the ty token's gate is its canonical guard, and the printed bytes
    are `tyText`'s by construction). -/
theorem valueOk_fieldG (f : Field) (h : nameOk f.name = true) :
    Grammar.valueOk fieldG (fieldToRaw f) = true := by
  have h1 : nameAtom.pre f.name = true := h
  show (fieldAtom.pre () && (nameAtom.pre f.name
      && (spAtom.pre () && tyAtom.pre f.ty))) = true
  rw [h1]
  rfl

/-- The grammar's value discipline IS the name discipline (the ITEM
    face's rows): every item/field name nameOk. -/
theorem valueOk_itemLines (items : List Item) (hok : namesOk items) :
    Grammar.valueOk (.rep lineG) (linesToRaw items) = true := by
  have hspec := namesOk_spec items hok
  show (linesToRaw items).all (fun z => Grammar.valueOk lineG z) = true
  rw [List.all_eq_true]
  intro raw hraw
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hraw
  obtain ⟨h1, h2⟩ := hspec it hit
  have hfields : Grammar.valueOk (.rep fieldG) (it.fields.map fieldToRaw) = true := by
    show (it.fields.map fieldToRaw).all (fun z => Grammar.valueOk fieldG z) = true
    rw [List.all_eq_true]
    intro z hz
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hz
    exact valueOk_fieldG f (h2 f hf)
  show Grammar.valueOk lineG ((itemToRaw it, ())) = true
  show (Grammar.valueOk itemPartG (itemToRaw it)
        && Grammar.valueOk (.atom nlAtom) ()) = true
  show (itemAtom.pre () && Grammar.valueOk
      (.seq (.atom nameAtom) (.rep fieldG)) (it.name, it.fields.map fieldToRaw)
      && Grammar.valueOk (.atom nlAtom) ()) = true
  show ((itemAtom.pre () && (nameAtom.pre it.name &&
        Grammar.valueOk (.rep fieldG) (it.fields.map fieldToRaw)))
      && Grammar.valueOk (.atom nlAtom) ()) = true
  have h1' : nameAtom.pre it.name = true := h1
  rw [h1', hfields]
  rfl

/-- One lane line's value face: both names ride the name atom, so the
    grammar's value discipline IS the name discipline here too. -/
theorem valueOk_laneLine (l : String × String) (h : nameOk l.1 = true)
    (hn : nameOk l.2 = true) :
    Grammar.valueOk laneLineG (laneToRaw l) = true := by
  show (Grammar.valueOk lanePartG ((), (l.1, ((), l.2)))
        && Grammar.valueOk (.atom nlAtom) ()) = true
  show (laneAtom.pre () && Grammar.valueOk
      (.seq (.atom nameAtom) (.seq (.atom spAtom) (.atom nameAtom)))
      (l.1, ((), l.2)) && Grammar.valueOk (.atom nlAtom) ()) = true
  show ((laneAtom.pre () && (nameAtom.pre l.1 &&
        (spAtom.pre () && nameAtom.pre l.2)))
      && Grammar.valueOk (.atom nlAtom) ()) = true
  have h1' : nameAtom.pre l.1 = true := h
  have h2' : nameAtom.pre l.2 = true := hn
  rw [h1', h2']
  rfl

/-- The grammar's value discipline IS the name discipline at the
    UNIVERSE face: the item rows' names + every lane row's two names
    (the write-side gate the law's premise carries). -/
theorem valueOk_universe (u : Universe) (hok : universeOk u = true) :
    Grammar.valueOk snapshotGrammar u = true := by
  obtain ⟨hitems, hlanes⟩ := Bool.and_eq_true_iff.mp hok
  show ((fun _ => true) u && Grammar.valueOk
      (.seq (.rep lineG) (.rep laneLineG))
      ((linesToRaw u.items, laneLinesToRaw u.lanes))) = true
  show (Grammar.valueOk (.rep lineG) (linesToRaw u.items)
      && Grammar.valueOk (.rep laneLineG) (laneLinesToRaw u.lanes)) = true
  rw [valueOk_itemLines u.items hitems]
  show (laneLinesToRaw u.lanes).all (fun z => Grammar.valueOk laneLineG z) = true
  rw [List.all_eq_true]
  intro raw hraw
  obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hraw
  obtain ⟨h1, h2⟩ := lanesOk_spec u.lanes hlanes l hlm
  exact valueOk_laneLine l h1 h2

/-! ### the derived print/parse (the entry points) -/

/-- The whole universe as snapshot text (canonical bytes: the derived
    printer over the SORTED universe — the item lines sorted by item
    name, then the lane lines sorted by (lane id, name), each line
    newline-terminated; the empty universe prints EMPTY — `parse "" =
    .ok ⟨[], []⟩` is the same zero). -/
def print (u : Universe) : String :=
  Grammar.print snapshotGrammar (canonicalU u)

/-- Parse snapshot text back to the universe. Total over String; every
    failure is LOUD (a snapshot that doesn't parse is a gate refusal,
    never a skip). The empty text is the empty universe. The failures
    re-key to the ONE envelope's rendering (the layer's `parseCode`
    Diag; the ty token's SN-coded refusals keep their spellings inside
    the message text). -/
def parse (s : String) : Except String Universe :=
  match Grammar.run snapshotGrammar s with
  | .ok u => .ok u
  | .error e => .error (TextKit.Diag.toString e.toDiag)

/-! ### the round trip — the file format's law, the generic instances -/

/-- THE SNAPSHOT LAW (the grammar layer's instance): the universe's
    snapshot text parses back to the CANONICAL form of the universe —
    `print` sorts, `parse` reads, and the round trip is exact. THE
    CONTENT IS `Grammar.run_print_fixFree`: the pre-grammar hand
    item-loop law family (`parseFields_render`, `parseItem_render`,
    `parseItems_printItems` + the length/depth fuel plumbing) died
    here. (The converse — `print (parse s) = s` for canonical `s` — is
    the canonicalization direction, NOTED in the module header, not
    proved: the sort's permutation theory on top of `print_parseG`;
    the legacy paid three failed attempts.) -/
theorem parse_print (u : Universe) (hok : universeOk u = true) :
    parse (print u) = .ok (canonicalU u) := by
  have hcanon : universeOk (canonicalU u) = true := by
    obtain ⟨hi, hl⟩ := Bool.and_eq_true_iff.mp hok
    exact Bool.and_eq_true_iff.mpr
      ⟨namesOk_canonical u.items hi, lanesOk_canonical u.lanes hl⟩
  simp only [parse, print]
  rw [Grammar.run_print_fixFree snapshotGrammar snapshotFixFree snapshotCert
    (canonicalU u) (valueOk_universe (canonicalU u) hcanon)]

/-- Law 2 (the exactness direction) at the snapshot's grammar value: a
    successful derived parse consumed EXACTLY the `printG` bytes of its
    result (+ the parsed value is value-owned — the name discipline).
    UNSORTED by design: `printG` prints the item list in ITS order; the
    wrapper's `print` sorts — the canonicalization direction stays the
    noted gap. -/
theorem print_parseG (fuel : Nat) (ys : Universe) (cur cur' : Cursor)
    (h : Grammar.parseG snapshotGrammar fuel cur = .ok (ys, cur')) :
    cur.cs = (Grammar.printG snapshotGrammar ys).toList ++ cur'.cs ∧
    cur'.off = cur.off + (Grammar.printG snapshotGrammar ys).length ∧
    Grammar.valueOk snapshotGrammar ys = true :=
  Grammar.print_parse snapshotGrammar fuel snapshotCoherent h

/-! ## the emitter row + the gate's ONE reading -/

/-- The snapshot's emitter row (15 #10): the declared output + the law.
    The artifact is a HEADER-FREE canonical data file (the
    code-registry precedent): the bytes are `print`'s canonical output —
    the gate (`gates snapshot-check`) is the artifact's ONE tie (never
    also gen-check's — one tie per artifact); the `style` field is
    unused here (no GENERATED header is prepended — the canonical bytes
    ARE the file). -/
def snapshotEmitter : Kit.Emit.Emitter Universe where
  name := "schema-snapshot"
  style := .lean
  specSource := "SchemaCore.Slice"
  outputs := ["notes/universe.snapshot"]
  run u := [{ path := "notes/universe.snapshot", contents := print u }]
  law := some fun u => universeOk u

/-- The certified write path: the snapshot is unemittable without the
    discharged naming precondition. -/
def snapshotFiles (u : Universe) (h : universeOk u = true) :
    List Kit.Emit.GeneratedFile :=
  snapshotEmitter.runCertified u h

/-- The gate's ONE reading: route the ONE log (the schema lane's rows
    to the rich item face; every OTHER lane's rows to the identity lane
    face), render the canonical bytes. Shared by the writer and the
    check — never re-encoded. -/
unsafe def snapshotOfEnv (env : Lean.Environment) :
    Lean.CoreM (Except String String) := do
  match ← getSchemas env with
  | .error e => pure (.error e)
  | .ok items =>
    let allRows := Kit.Lane.laneLog env
    let lanes := (allRows.filter (fun r => r.lane != schemaLaneId))
      |>.map (fun r => (r.lane, r.name))
    let u : Universe := { items := items, lanes := lanes }
    if h : universeOk u = true then
      match snapshotFiles u h with
      | [] => pure (.error (snapshotDiag eSN0026 "the emitter produced nothing"))
      | f :: _ => pure (.ok f.contents)
    else
      pure (.error (snapshotDiag eSN0027 "a registered name is not encodable \
        (space/newline in an item, field, or lane name) — the write-side \
        gate refuses"))

end SchemaCore

/-! ## the module's law-summary (the honest ledger)

PROVED (the generic theorems' instances): `parse_print` — the
decode-after-encode direction, for `nameOk` registries, exactly — is
`Grammar.run_print_fixFree` at `snapshotGrammar` (+ the sort composed
at the wrapper); `print_parseG` — the exactness direction at the
UNSORTED grammar value — is `Grammar.print_parse`. The pre-grammar
hand item-loop law family (`parseFields_render`, `parseItem_render`,
`parseItems_printItems`) and its fuel plumbing died: the content is
the engine's.

PROVED (the ty token's hand zone, the honest residue): `parseTy_tyText`
— every ty token's decode-after-encode — the tyAtom lexeme's
`print_scan` base, over the TextKit base (the scans ride
`TextKit.Parser.takeWhile`, `TextKit.expect`, `TextKit.scanNat`; the
inversions cite TextKit.Lemmas, no local scan-lemma copies beyond the
takeWhile boundary kit).

NOTED, NOT PROVED: the wrapper-level canonicalization direction
(`print (parse s) = s` for canonical `s`) — the sort's permutation
theory on top of `print_parseG`; the gate re-derives the bytes
instead. NO `sorry`, NO `axiom` anywhere above.
-/
