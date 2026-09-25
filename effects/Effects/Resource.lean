/-
# Effects.Resource — the resource discipline, SEPARATE from the effects

The split's resource half (notes/v3/08-capabilities.md §8, decision D7):
effects are upper bounds (set union — `Effects.Basic`); resources are
USAGE ACCOUNTING with CONTEXT SPLITTING. Union cannot enforce linearity:
`{consume h} ∪ {consume h}` is the same row (`Effects.
row_blind_to_double_spend` pins the blindness at the lattice) — the
double-spend lives in the accounting, never in the row. So the
accounting is its OWN structure here, and the two never collapse.

The discipline, honest-minimal:

- **The context** (`Ctx`): the unspent resources as a DUPLICATE-FREE
  list (`NoDup'` — my own induction-friendly invariant, zero core-lemma
  weight). The duplicate-freedom is not decoration: with a duplicated
  resource the split's spent fact is FALSE (`drop [h, h] h = [h]`), so
  the discipline REQUIRES the set-shaped context — an honest context is
  a finite set, and the handle's proof is only available against one.
- **The live handle** (`Handle`): pure evidence that `h` is unspent in
  `c` — the permission IS the proof (`h ∈ c.elems`), the ladder's
  rung-1 shape (a spent handle is unrepresentable: the proof is false,
  no handle constructs).
- **The context split** (`Handle.consume`): consumption returns the
  context WITHOUT `h`, and the SPENT FACT rides the type
  (`h ∉ rest.elems`). Every OTHER resource survives (`Ctx.kept_survive`
  — the context-splitting discipline).
- **THE double-spend pin** (`Handle.split_disallows`): after the split,
  no live handle for `h` exists — the reuse fails to TYPECHECK. The
  teeth: EffectsTests' `#guard_msgs` pin constructs a handle in a spent
  context and the elaboration refuses.
- **The counted tie** (01 §2: resources are not a root — a Change
  instance, monus): a stock of `n` permits spends by monus
  (`Kit.monusApply`, cited); spends compose (`spendCount_compose`).
  The LINEAR discipline is strictly stronger than the count: the count
  reads zero after one spend but monus TRUNCATES, never refuses
  (`monus_cannot_refuse`) — the refusal is the split's, type-level.
  The count is the value-level shadow for multi-permit stocks.

Named exclusions (each lands with its first consumer + its named law):
persistent/unlimited resources (a `Handle` with no split — trivially
the count discipline), fractional permissions (the split's
generalization), cross-thread aliasing (TraceModel territory — 01 §3),
resource-aware effect ROWS (the row stays an upper bound; the
accounting never enters `Effects.Basic` — D7).

Doctrine slots (notes/v3/01-core.md, the five questions):
- **Root**: Change (01 §2) — consumption is monus-shaped; the split is
  the LINEARITY the monus cannot carry. NOT a new root.
- **Carrier grade**: none — a proof-carrying token, not a crossing.
- **Spine reading**: none — the registry lane's resource table is the
  spine reading when it mounts.
- **Ladder rung**: rung 1 (unrepresentable — the spent handle has no
  constructor) for the split; rung 6 (small hand theorems) for the
  laws; the monus tie is CITED (`Kit.monusApply_*`), never re-proved.
- **Gate rows**: EffectsTests' axiom self-check + the double-spend
  elaboration tooth.

Core-only: no mathlib, no Batteries (the cone rule). Imports Kit.Change
(read-only — the monus cite).
-/

import Kit.Change
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only: any package may import it)

namespace Effects.Resource

/-! ## The duplicate-free context invariant -/

/-- A resource id (finite — the ids name the app's resource table). -/
abbrev Rsc := Nat

/-- My own nodup invariant (induction-friendly; the core's `List.Nodup`
    lemma surface is not needed here). -/
def NoDup' : List Rsc → Prop
  | [] => True
  | f :: rest => f ∉ rest ∧ NoDup' rest

@[nolint linter.guestlang.zeroCitation "load-bearing: the invariant's base case — consumed by `dropL_nodup` in this module + the tests' fixture contexts (EffectsTests ctx0/propSplit)"]
theorem noDup'_nil : NoDup' ([] : List Rsc) := ⟨⟩

@[nolint linter.guestlang.zeroCitation "load-bearing: the invariant's cons case — consumed by `dropL_nodup` in this module + the tests' fixture contexts (EffectsTests ctx0/propSplit)"]
theorem noDup'_cons {f : Rsc} {rest : List Rsc}
    (hf : f ∉ rest) (hnd : NoDup' rest) : NoDup' (f :: rest) := ⟨hf, hnd⟩

/-! ## The split's substrate -/

/-- The list without `h` (the split's substrate; equation-lemma-friendly,
    pattern #12). -/
def dropL : List Rsc → Rsc → List Rsc
  | [], _ => []
  | f :: rest, h => if f = h then rest else f :: dropL rest h

/-- THE spent fact: with a duplicate-free context, the spent resource
    is gone from the split. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `Ctx.spent` (the packaged spent fact the split's type rides)"]
theorem dropL_spent (c : List Rsc) (h : Rsc) (hnd : NoDup' c) :
    h ∉ dropL c h := by
  cases c with
  | nil => simp [dropL]
  | cons f rest =>
    have h1 := hnd.1
    have h2 := hnd.2
    simp only [dropL]
    split
    · next hf => rw [← hf]; exact h1
    · next hf =>
      intro hx
      cases List.mem_cons.mp hx with
      | inl he => exact hf he.symm
      | inr hm => exact dropL_spent rest h h2 hm

/-- Context splitting: every OTHER resource survives the split — the
    discipline's whole content (consume `h`, carry the rest). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `dropL_nodup` + `Ctx.kept_survive` in this module (the kept law the tests pin at data level)"]
theorem dropL_kept (c : List Rsc) (h g : Rsc) (hne : g ≠ h) (hnd : NoDup' c) :
    g ∈ dropL c h ↔ g ∈ c := by
  cases c with
  | nil => simp [dropL]
  | cons f rest =>
    have h1 := hnd.1
    have h2 := hnd.2
    simp only [dropL]
    split
    · next hf =>
      constructor
      · exact fun hx => List.mem_cons_of_mem f hx
      · intro hx
        cases List.mem_cons.mp hx with
        | inl he => exact absurd (by rw [he]; exact hf) hne
        | inr hr => exact hr
    · next hf =>
      constructor
      · intro hx
        cases List.mem_cons.mp hx with
        | inl he => rw [he]; exact List.mem_cons_self ..
        | inr hr =>
          exact List.mem_cons_of_mem f ((dropL_kept rest h g hne h2).mp hr)
      · intro hx
        cases List.mem_cons.mp hx with
        | inl he => rw [he]; exact List.mem_cons_self ..
        | inr hr =>
          exact List.mem_cons_of_mem f ((dropL_kept rest h g hne h2).mpr hr)

/-- The split preserves the invariant (the context stays a context). -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `Ctx.drop` (the split preserves the context's set shape)"]
theorem dropL_nodup (c : List Rsc) (h : Rsc) (hnd : NoDup' c) :
    NoDup' (dropL c h) := by
  cases c with
  | nil => exact noDup'_nil
  | cons f rest =>
    have h1 := hnd.1
    have h2 := hnd.2
    simp only [dropL]
    split
    · next _ => exact h2
    · next hf =>
      refine noDup'_cons ?_ (dropL_nodup rest h h2)
      intro hx
      exact h1 ((dropL_kept rest h f hf h2).mp hx)

/-! ## The context + the live handle -/

/-- A resource context: the unspent resources, DUPLICATE-FREE (the
    set-shaped discipline — see the header; a duplicated context breaks
    the spent fact, so the discipline requires this shape). -/
structure Ctx where
  /-- The unspent resources. -/
  elems : List Rsc
  /-- The set discipline. -/
  nodup : NoDup' elems

/-- The context's split: `c` without `h`. -/
def Ctx.drop (c : Ctx) (h : Rsc) : Ctx :=
  ⟨dropL c.elems h, dropL_nodup c.elems h c.nodup⟩

/-- Context splitting: every other resource survives (the kept law,
    packaged over the context). -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by EffectsTests (split_kept) + EffectsTests.Axioms (#print axioms); the kept law, packaged over the context"]
theorem Ctx.kept_survive (c : Ctx) (h g : Rsc) (hne : g ≠ h) :
    g ∈ (c.drop h).elems ↔ g ∈ c.elems :=
  dropL_kept c.elems h g hne c.nodup

/-- THE spent fact, packaged: the spent resource is gone. -/
@[nolint linter.guestlang.zeroCitation "load-bearing: consumed by `Handle.consume` (the spent fact rides the split's type)"]
theorem Ctx.spent (c : Ctx) (h : Rsc) : h ∉ (c.drop h).elems :=
  dropL_spent c.elems h c.nodup

/-- THE live handle: pure evidence that `h` is unspent in `c`. The
    permission is the proof — in a context where `h` is spent, no
    handle constructs (rung 1: the double-spend is unrepresentable). -/
structure Handle (c : Ctx) (h : Rsc) : Prop where
  /-- The resource is present in the context. -/
  live : h ∈ c.elems

/-- THE context split: consumption consumes ONCE — the returned context
    is `c` without `h`, and the spent fact rides the type. -/
def Handle.consume {c : Ctx} {h : Rsc} (_hd : Handle c h) :
    { rest : Ctx // h ∉ rest.elems } :=
  ⟨c.drop h, c.spent h⟩

/-- THE double-spend pin: after the split, NO live handle for `h`
    exists — the reuse fails to typecheck (the teeth: EffectsTests
    constructs a handle in a spent context and the elaboration
    refuses). -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by EffectsTests.Axioms (#print axioms); THE double-spend pin — the reuse fails to typecheck (the teeth's general statement)"]
theorem Handle.split_disallows {c : Ctx} {h : Rsc} (hd : Handle c h) :
    ¬ (h ∈ hd.consume.1.elems) :=
  hd.consume.2

/-! ## The counted tie (01 §2: resources are a Change instance — monus) -/

/-- The COUNTED discipline: a stock of `n` permits, spending `d` —
    monus-shaped (01 §1/§2; `Kit.monusApply` CITED, never re-encoded). -/
def spendCount : Nat → Nat → Option Nat := Kit.monusApply

/-- The counted composition law: two spends are one spend of the sum
    (the monus compose — `Kit.monusApply_compose`, cited). -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by EffectsTests (count_compose_pin) + EffectsTests.Axioms (#print axioms); the counted composition law (Kit.monusApply_compose, cited)"]
theorem spendCount_compose (s a b : Nat) :
    spendCount s (a + b)
      = (spendCount s a).bind (fun r => spendCount r b) :=
  Kit.monusApply_compose s a b

/-- THE counted discipline's honest ceiling — D7's other face: the
    count TRUNCATES, never refuses. A zero stock still "spends" (reads
    zero); the double-spend is invisible to the accounting's value
    level. The refusal exists ONLY at the split's type level
    (`Handle.split_disallows`). This is why `Effects.Basic`'s row and
    this count can NEVER be the whole discipline. -/
@[nolint linter.guestlang.zeroCitation "public API: pinned by EffectsTests (count_blind_pin) + EffectsTests.Axioms (#print axioms); D7's counted face — the count truncates, never refuses"]
theorem monus_cannot_refuse (d : Nat) : spendCount 0 d = some 0 := by
  simp [spendCount, Kit.monusApply]

-- The Prop-face projections the structures auto-generate — the
-- discipline's API (the context's set-discipline field, the handle's
-- evidence field: the permission IS the proof), never cited by name
-- outside.
attribute [nolint linter.guestlang.zeroCitation "public API: the discipline's Prop-face field — the context's set-discipline row (the spent fact is only available against a duplicate-free context) / the handle's evidence field (the permission IS the proof, rung 1); constructed by the tests' fixtures, read when the registry lane's resource table mounts"]
  Ctx.nodup Handle.live

end Effects.Resource
