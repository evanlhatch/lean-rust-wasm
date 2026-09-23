/-
# Substrait.Decode.Inversions — the parse∘emit row inversions, generated

The extension/version line rows, inverted by `declare_inversion`
(`Substrait.Meta.Inversion`): each entry below declares the emitted row
and its resolution chain; the command generates `inv_<row>` and the
old-name corollary the axiom gate's `#print axioms` list pins.

Rows converted here:
- `inv_urnLine` — the `@<anchor>: <urn>` URN-entry row.
- `inv_declLine` — the `#<anchor> @<urnRef>: <name>` declaration row.
- `inv_versionLines` — the `=== Version X.Y.Z` header + the
  presence-conditional producer/git sub-lines (the bespoke presence split
  is the entry's `proof :=` block — the ONE non-row-shaped piece of the
  cluster).

Kept hand-written in Decode.Plan (see that module's header):
- `parseRootNames_emitted` — the Root-names row: its proof rides the
  private `splitTopLevel`/identifier lemma stack — not a row-shape twin.
- `parseType_scalar_withNull` — the scalar-type suffix core: lexCtor-
  shaped, not anchor/scan-shaped (stays private in Decode.Types).
-/

module

public import Substrait.Meta.Inversion
import Substrait.Decode.Plan

open Substrait

namespace Substrait.Decode

/- `@<anchor>: <urn>` — the URN-entry row inversion (`parse ∘ emit = id`). -/
declare_inversion inv_urnLine where
  invparse := parseUrnEntry
  invent := Emit.Text.urnLine a urn
  invbinders := (a : Nat) (urn : String)
  invresult := some { extensionUrnAnchor := a, urn := urn }
  invline := [invtok Grammar.indentUnit "  " invlit "@" invanchor a invtok Grammar.colonSpTok ": " invname urn]
  invsteps := [invreduce parseUrnEntryBody.eq_1 invscan a invexpect colonTok invfinish]
  invcor := parseUrnEntry_urnLine

/- `#<anchor> @<urnRef>: <name>` — the declaration-entry row inversion
    (the shared `Grammar.ExtKind` row, two anchors). -/
declare_inversion inv_declLine where
  invparse := parseDeclEntry k
  invent := Emit.Text.declLine u a nm
  invbinders := (k : Grammar.ExtKind) (u a : Nat) (nm : String)
  invresult := some (k.toDecl u a nm)
  invline := [invtok Grammar.indentUnit "  " invlit "#" invanchor a invlit " @" invanchor u invtok Grammar.colonSpTok ": " invname nm]
  invsteps := [invreduce parseDeclEntryBody.eq_1 invscan a invpeel " @" invreduce parseDeclEntryAt.eq_1 invscan u invexpect colonTok invfinish]
  invcor := parseDeclEntry_declLine

/- `=== Version X.Y.Z` + the producer/git sub-lines — the version-header
    row inversion (the presence split is the entry's `proof :=` block). -/
declare_inversion inv_versionLines where
  invparse := parseVersion
  invent := Emit.Text.versionLines v ++ rest
  invbinders := (v : Proto.Version) (rest : List String)
    (hboth : v.producer = "" → v.gitHash = "" → ∀ p, rest.head? = some p →
      p.startsWith Grammar.producerPfx = false ∧ p.startsWith Grammar.gitHashPfx = false)
    (hgit : v.gitHash = "" → ∀ p, rest.head? = some p →
      p.startsWith Grammar.gitHashPfx = false)
  invresult := some (v, rest)
  invline := [invpfx invnum mj invdot invnum mn invdot invnum pt]
  invsteps := [invscan mj invexpect dotTok invscan mn invexpect dotTok invscan pt invtail]
  invcor := parseVersion_versionLines
  invproof := by
    by_cases hp : prod.isEmpty <;> by_cases hg : git.isEmpty
    · rw [if_pos hp, if_pos hg]
      have hp' : prod = "" := String.isEmpty_iff.mp hp
      have hg' : git = "" := String.isEmpty_iff.mp hg
      subst hp'
      subst hg'
      simp only [List.nil_append]
      cases rest with
      | nil => simp [List.isEmpty, List.headD, List.drop]
      | cons p ps =>
        obtain ⟨hpp, hpg⟩ := hboth rfl rfl p rfl
        simp [hpp, hpg]
    · rw [if_pos hp, if_neg hg]
      have hp' : prod = "" := String.isEmpty_iff.mp hp
      subst hp'
      simp only [List.nil_append, List.singleton_append]
      simp [gitHash_ne_producerPfx, startsWith_append, dropPrefix_copy, String.length_append]
    · rw [if_neg hp, if_pos hg]
      have hg' : git = "" := String.isEmpty_iff.mp hg
      subst hg'
      simp only [List.append_nil, List.singleton_append]
      cases rest with
      | nil => simp [startsWith_append, dropPrefix_copy, String.length_append]
      | cons p ps =>
        simp [hgit rfl p rfl, startsWith_append, dropPrefix_copy, String.length_append]
    · rw [if_neg hp, if_neg hg]
      simp only [List.singleton_append]
      simp [startsWith_append, dropPrefix_copy, String.length_append]

end Substrait.Decode
