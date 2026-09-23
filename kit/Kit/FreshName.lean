/-
# Kit.FreshName — the fresh-name discipline

The derive-name sanity: a proposed name is FRESH or it is a duplicate —
exactly one of the two holds (the verdict dichotomy is a theorem), and
the duplicate verdict carries the CURATED error shape: it names the
context, the rejected `proposed`, what it is, WHY it was refused
(names must be fresh — the registry rejects, there is no overwrite
path), and the did-you-mean over the taken space (the closed-world
discipline, `Kit.suggestFor` — one engine, one suffix).

Provenance: mined from
`legacy/lean/codegen-core/CodegenCore/GenKit.lean` — `freshNameVerdict`
(the pure verdict, verbatim) + `freshNameCheck` (the throwing gate).
The DELIBERATE split here: the verdict is pure data (`Option String`)
and the check face returns `Except String Unit` — Kit stays IO/elab
monad-free; a consumer in an error monad is `throwError` over the
Except's error, one line at its own layer (the legacy `MonadError`
face is exactly that mount).

Core-only. Five questions (notes/v3/01-core.md):
- root: DATA — the verdict is a value; the refusal is a String, not a
  throw.
- carrier grade: first-order over String/List — guest-thinkable.
- spine reading: as-data (consumers mount their own throwing face).
- ladder rung: rung 1 + one bridge theorem (the dichotomy) — the
  smallest honest rung for a check with a consumer.
- gate row: the axiom gate (Kit's report rows) + the test pins
  (KitTests: the curated error shapes + the negative controls).
-/

import Kit.Suggest

namespace Kit

/-! ## the fresh-name verdict -/

/-- The fresh-name VERDICT: `none` = fresh, `some msg` = the
    duplicate-decl rejection with the did-you-mean over the taken
    space (the legacy `freshNameVerdict`, verbatim). -/
def freshNameVerdict (ctx proposed what : String) (taken : List String) :
    Option String :=
  if taken.contains proposed then
    some (s!"{ctx}: `{proposed}` is already a registered {what} — "
      ++ "names must be fresh" ++ Kit.suggestSuffix proposed taken)
  else none

/-- The verdict dichotomy: the verdict is `none` EXACTLY when the
    proposed name is not taken — fresh and duplicate are mutually and
    totally exclusive (the derive-name sanity). -/
theorem freshNameVerdict_none_iff (ctx proposed what : String)
    (taken : List String) :
    (freshNameVerdict ctx proposed what taken) = none
      ↔ ¬(taken.contains proposed) := by
  unfold freshNameVerdict
  split
  · next h =>
      have h2 : proposed ∈ taken := List.contains_iff_mem.mp h
      simp [h2]
  · next h =>
      have h2 : ¬(proposed ∈ taken) := fun hm =>
        absurd (List.contains_iff_mem.mpr hm) h
      simp [h2]

/-! ## the check -/

/-- The fresh-name gate: `.ok ()` = fresh, `.error msg` = the curated
    duplicate rejection (the verdict's message, unchanged). A duplicate
    registration is a REJECTION — there is no overwrite path. -/
def freshNameCheck (ctx proposed what : String) (taken : List String) :
    Except String Unit :=
  match freshNameVerdict ctx proposed what taken with
  | none => .ok ()
  | some msg => .error msg

end Kit
