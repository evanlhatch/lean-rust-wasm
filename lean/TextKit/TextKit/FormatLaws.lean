/-
# TextKit.FormatLaws — the byte-exact rendering laws for `Std.Format`

The emitters (schema-lang's `Emit.Wit`, substrait's text lane) assemble
bytes with `Std.Format` — hard `line`s (NO `group`, so `.pretty` cannot
reflow), `nest` for block bodies, `joinSep` for comma lists. The
byte-tie pins the ACTUAL bytes (goldens regenerate + diff); this module
pins the LAWS the assembly rests on, as kernel-replayable theorems:

1. The rendering model `renderGo`/`renderFmt` — a TOTAL, provable
   renderer for the group-free hard-line fragment (nil/line/text/append/
   nest). The real `Format.pretty` renders through the PARTIAL `be`
   (Wadler) — no kernel-replayable equality with it exists (reducing
   would unfold a `partial`), so the model is the provable face of the
   byte-tie's semantics; byte-level identity with `pretty` remains the
   goldens' job (noted at each law).

2. The byte-exact laws:
   - append RENDERS as concatenation (`render_append`, its `renderGo`
     face) — and therefore rendering-level ASSOCIATIVITY for
     left/right-nested append trees (`render_assoc`);
   - the foldl-with-separator law the emitters' list folds are made of
     (`foldl_sep_render`);
   - the `nest`-under-hard-`line` shape a block body's FIRST line writes
     (`render_nest_line`).

   DEFERRED (no axiom): the `Std.Format.joinSep` WRAPPER law and the
   block-body-in-full law. Init's `joinSep` body is not exposed to the
   kernel, and its generated equation lemmas do not resolve under this
   module's scoping (compiler naming facts, not choices) — an in-kernel
   PROOF is infeasible without an axiom, which the axiom gate forbids.
   `foldl_sep_render` — the very recursion `joinSep` is DEFINED as —
   pins the byte semantics, and the TEST pins decide the concrete
   `joinSep` agreement by evaluation. A Lean with exposed eq-lemmas
   lands the wrapper laws unchanged.

3. The STRUCTURAL constructor laws (the fmt-injectivity set): append
   injectivity, text injection, the coerced-atom spellings, and the
   noConfusion families — INCLUDING `line`/`nest` vs `append`/`text`
   (equating hard-line shapes). These are the RELOCATED set that lived
   in `SchemaLang.Emit.Wit` (`fmtAppend_inj`…), statement-for-statement:
   `SchemaLang/Emit/Wit.lean` now imports this module and cites the
   theorems by their full names here — `witFmt_inj` compiles unchanged
   in statements, only the referenced home moved (pure code motion,
   byte-tie-neutral; verified by the schema-lang axiom shard's decl
   count falling by exactly the moved set).

CORE-ONLY: `Std.Format` lives in Init — zero imports.
-/

module

@[expose] public section

namespace TextKit

open Std.Format

namespace FormatLaws

/-! ## the rendering model -/

/-- `n` spaces (the byte the hard-line indent writes). Structural recursion
    (NOT `String.pushn` — that init def's body is not exposed to the
    kernel, so only this structural form reduces in proofs). -/
def spaces : Nat → String
  | 0 => ""
  | n + 1 => " " ++ spaces n

/-- The group-free hard-line renderer: `line` is a HARD newline followed
    by the current indent's spaces (the emitters' no-`group` `.pretty`
    semantics), `nest n f` raises the indent for `f`, `append`
    concatenates. `align`/`group`/`tag` (the reflow machinery the
    emitters do NOT use) render as no-ops on the model. -/
def renderGo : Nat → Std.Format → String
  | ind, .nil => ""
  | ind, .line => "\n" ++ spaces ind
  | ind, .text s => s
  | ind, .append a b => renderGo ind a ++ renderGo ind b
  | ind, .nest n f => renderGo (ind + n.toNat) f
  | _, .align _ => ""
  | ind, .group f _ => renderGo ind f
  | ind, .tag _ f => renderGo ind f

/-- Render at column 0 (the `String` boundary). -/
def renderFmt (f : Std.Format) : String := renderGo 0 f

/-! ## the byte-exact laws -/

/-- The append-at-`ind` law (the workhorse face of `render_append`). -/
theorem renderGo_append (ind : Nat) (a b : Std.Format) :
    renderGo ind (a ++ b) = renderGo ind a ++ renderGo ind b := rfl

/-- The atom laws (rfl-reducible). -/
theorem render_text (s : String) : renderFmt (Std.Format.text s) = s := rfl
theorem render_nil : renderFmt Std.Format.nil = "" := rfl

/-- `spaces 0` is empty (the structural recursion's base). -/
theorem spaces_zero : spaces 0 = "" := rfl

/-- `appending ""` is the identity (the atom algebra). -/
theorem append_empty_right (s : String) : s ++ "" = s := by
  rw [← String.toList_inj]
  rw [String.toList_append]
  simp

/-- The hard-line atom at column 0: a bare `line` renders as a newline
    (its indent is empty at column 0). -/
theorem render_line : renderFmt Std.Format.line = "\n" := rfl

/-- **Append renders as concatenation** — the byte-exact additive law. -/
theorem render_append (a b : Std.Format) : renderFmt (a ++ b) = renderFmt a ++ renderFmt b := by
  exact renderGo_append 0 a b

/-- **Rendering-level associativity**: left- and right-nested append
    trees render identical bytes (the emitters' `++`-chain normalizer). -/
theorem render_assoc (a b c : Std.Format) :
    renderFmt ((a ++ b) ++ c) = renderFmt (a ++ (b ++ c)) := by
  rw [render_append, render_append, render_append, render_append]
  exact String.append_assoc

/-- The intercalation THIS module proves laws about. Core's
    `String.intercalate` is built via a `where`-helper `go` (opaque to
    reduction), so the fold laws state `join` — the same interleaving
    semantics (the `[x]` shape has NO separator). -/
def join (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: y :: rest => x ++ sep ++ join sep (y :: rest)

/-- The two-or-more element law of `join`. -/
theorem join_two (sep : String) (x y : String) (rest : List String) :
    join sep (x :: y :: rest) = x ++ sep ++ join sep (y :: rest) := rfl

/-- The foldl-with-separator rendering law (the `joinSep` backbone): the
    foldl assembles `acc` ++ `sep` ++ each element; it renders as the
    intercalation of the rendered pieces. -/
theorem foldl_sep_render (ind : Nat) (acc sep : Std.Format) (fs : List Std.Format) :
    renderGo ind (fs.foldl (fun a f => a ++ sep ++ f) acc) =
      join (renderGo ind sep) (renderGo ind acc :: fs.map (renderGo ind)) := by
  refine List.rec (motive := fun fs => ∀ acc : Std.Format,
      renderGo ind (fs.foldl (fun a f => a ++ sep ++ f) acc) =
        join (renderGo ind sep) (renderGo ind acc :: fs.map (renderGo ind))) ?_ ?_ fs acc
  · intro acc
    rfl
  · intro h tl ih acc
    rw [List.foldl_cons]
    rw [ih (acc ++ sep ++ h)]
    -- both sides are the SAME run: the LHS's first element is the
    -- folded head `acc ++ sep ++ h`; `renderGo`/`join` split it; the
    -- residual is String-append id (case the map so `join` reduces):
    rw [renderGo_append, renderGo_append]
    cases htl : tl.map (renderGo ind) with
    | nil => simp [join, htl, String.append_assoc]
    | cons y rest => simp [join, htl, String.append_assoc]

/-- DEFERRED (no axiom): the `Std.Format.joinSep` WRAPPER law + the
    block-body-in-full law — see the module header's deferral note
    (init's `joinSep` body is kernel-opaque; the delivered
    `foldl_sep_render` is its recursion). -/
theorem joinSep_law_deferred : True := by trivial

/-- **The `nest`-under-hard-`line` law** (the `blockBody` FIRST-LINE
    shape): a block body's first `line`, nested by `n`, renders as a
    hard newline plus `n` spaces. -/
theorem render_nest_line (n : Int) (f : Std.Format) :
    renderGo 0 (Std.Format.nest n (Std.Format.line ++ f)) =
      "\n" ++ spaces n.toNat ++ renderGo n.toNat f := by
  simp [renderGo]
  rw [renderGo_append]
  exact show renderGo n.toNat (Std.Format.line ++ f)
    = "\n" ++ spaces n.toNat ++ renderGo n.toNat f from rfl

/-! ## the structural constructor laws (the fmt-injectivity set)

The RELOCATED set: statements identical to the historical
`SchemaLang.Emit.Wit` copies, which now import this module and cite
these names (witFmt_inj's proofwork by full name); see the module
header's relocation note. -/

/-- `append` is injective (a Format tree equality forces both halves). -/
theorem fmtAppend_inj {a b c d : Std.Format}
    (h : (a ++ b) = (c ++ d)) : a = c ∧ b = d :=
  Std.Format.append.injEq .. |>.mp h

/-- `append` injectivity as an equality (the simp face). -/
theorem fmtAppend_inj_eq {a b c d : Std.Format} :
    ((a ++ b) = (c ++ d)) = (a = c ∧ b = d) :=
  Std.Format.append.injEq ..

/-- text vs append: distinct constructors, no confusion. -/
theorem fmtText_append_iff {s : String} {a b : Std.Format} :
    (Std.Format.text s = (a ++ b)) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

/-- append vs text: distinct constructors, no confusion. -/
theorem fmtAppend_text_iff {s : String} {a b : Std.Format} :
    ((a ++ b) = Std.Format.text s) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

/-- `text` is injective. -/
theorem fmtText_inj_eq {s t : String} :
    (Std.Format.text s = Std.Format.text t) = (s = t) :=
  Std.Format.text.injEq ..

/-- The coerced-atom injections (the four spelling combinations the
    renderer's eq-lemmas produce). -/
theorem fmtCoe_inj_eq {s t : String} :
    (Std.format s = Std.format t) = (s = t) := by
  show (Std.Format.text s = Std.Format.text t) = (s = t)
  exact Std.Format.text.injEq ..

theorem fmtText_coe_inj_eq {s t : String} :
    (Std.Format.text s = Std.format t) = (s = t) := by
  show (Std.Format.text s = Std.Format.text t) = (s = t)
  exact Std.Format.text.injEq ..

theorem fmtCoe_text_inj_eq {s t : String} :
    (Std.format s = Std.Format.text t) = (s = t) := by
  show (Std.Format.text s = Std.Format.text t) = (s = t)
  exact Std.Format.text.injEq ..

/-! ## the hard-line shape family (the `nest`/`line` noConfusion)

Equality-refuting laws for the byte-tie's hard-line structures: a `nest`
or a `line` cannot BE an `append`/`text`/one another. -/

/-- `nest` vs append. -/
theorem fmtNest_append_iff {n : Nat} {f : Std.Format} {a b : Std.Format} :
    (Std.Format.nest n f = a ++ b) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

/-- append vs `nest`. -/
theorem fmtAppend_nest_iff {n : Nat} {f : Std.Format} {a b : Std.Format} :
    (a ++ b = Std.Format.nest n f) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

/-- `nest` vs `line`. -/
theorem fmtNest_line_iff {n : Nat} {f : Std.Format} :
    (Std.Format.nest n f = Std.Format.line) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

/-- `text` vs `line`. -/
theorem fmtText_line_iff {s : String} :
    (Std.Format.text s = Std.Format.line) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

/-- `line` vs `text`. -/
theorem fmtLine_text_iff {s : String} :
    (Std.Format.line = Std.Format.text s) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

/-- `line` vs append. -/
theorem fmtLine_append_iff {a b : Std.Format} :
    (Std.Format.line = a ++ b) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

/-- append vs `line`. -/
theorem fmtAppend_line_iff {a b : Std.Format} :
    (a ++ b = Std.Format.line) ↔ False :=
  ⟨fun h => Std.Format.noConfusion h, fun h => h.elim⟩

end FormatLaws

end TextKit

end -- @[expose] public section
