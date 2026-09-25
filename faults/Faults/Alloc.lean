/-
# Faults.Alloc — the E-code allocation from the PERSISTED registry

THE LANE'S POINT (notes/v3/05-codegen.md §4 + notes/v3/12-construction.md
§8): a fault's E-code is never hand-set and never position-derived — it
ALLOCATES from the persisted registry (`Kit.CodeRegistry` over
`notes/code-registry.txt`, the spec of record the `code-registry-check`
gate replays). The stable-allocation discipline rides the machinery: a
reordered registry changes no code, a deleted fault's row stays retired (the
tombstone), a renamed fault is a NEW fault with a NEW code (retire + fresh
allocate).

The lookup key is the fault's stable NAME, namespaced to keep the fault rows
disjoint from every other family's rows in the one code space:
`ecodeKey f = "fault." ++ f.name`. Two fault rows cannot collide (the mount
refuses duplicate names), so two faults cannot share a code — and the
allocAll fold refuses a duplicate code anyway (FT0004, decided, never
assumed).

The E-code SPELLING renders at the consumer: `"FT" ++ pad4 <allocation>`.
The spelling is DERIVED, never spelled in Lean source — the coverage tooth's
named blind spot (a concatenated code is invisible to the literal scan), with
the countermeasures in place: (1) the allocation numbers themselves live as
registry rows the gate replays; (2) the generated Rust artifact SPELLS the
codes and byte-ties through gen-check (the artifact is the pin); (3) the lane
tests pin the concrete spellings over the fixture. The lane's OWN refusal
codes are the `FT0001`–`FT0004` constants — spelled, so the tooth sees them,
live rows of the registry like every family's.

The allocation + its refusals are PURE (over a `Kit.CodeRegistry` value); the
IO face (`loadRegistry`) is the thin file read the writer exe and the gate
share. The refusals are Diag-rendered (Kit.Diag's envelope, 05 §4 — E-code +
message + the closed-world curation where a valid space exists).

Core-only (imports Kit — the cone rule).
Five questions (notes/v3/01-core.md):
- root: Crossing — the fault registry read into the ONE code space.
- carrier grade: the allocation is Except over first-order data; the
  invariants ride the persisted machinery's CheckedProp (`codeRegistryWf`).
- spine reading: the Registry → Interpretation seam: the allocation IS the
  registration's interpretation into codes.
- ladder rung: rung 1 — total folds, every verdict decided.
- gate row: code-registry-check (the family + the fault rows) +
  FaultsTests (the allocation teeth).
-/

import Kit.CodeRegistry
import Kit.Lane
import Faults.Item

namespace Faults

/-! ## the lane's own E-codes (spelled — live rows of the registry) -/

/-- FT0001 — a fault with no allocated row: the code must be allocated in
    the persisted registry first, then the derive re-run. -/
def eFT0001 : Kit.ECode := ⟨"FT0001"⟩

/-- FT0002 — the persisted registry itself is absent, malformed, or
    ill-formed (the allocation substrate's refusal). -/
def eFT0002 : Kit.ECode := ⟨"FT0002"⟩

/-- FT0003 — the derive ran over an empty registry: no `@[fault]` rows —
    nothing to allocate (the legacy's derive_fault_variant shape). -/
def eFT0003 : Kit.ECode := ⟨"FT0003"⟩

/-- FT0004 — two faults landed on the same allocated code (the
    collision-freedom tooth; decided at the allocation, never assumed). -/
def eFT0004 : Kit.ECode := ⟨"FT0004"⟩

/-! ## the spelling -/

/-- Zero-padded 4-digit decimal (the spelling's digit field; a wider code
    renders wider — the pad is a floor, never a truncation). -/
def pad4 (n : Nat) : String :=
  let s := toString n
  if s.length >= 4 then s
  else String.ofList (List.replicate (4 - s.length) '0') ++ s

/-- The fault family's E-code spelling: `FT` + the allocation, 4 digits.
    DERIVED from the allocation number (never spelled in Lean source —
    the coverage-tooth note in the module header). -/
def ecodeSpelling (n : Nat) : String := "FT" ++ pad4 n

/-- The persisted registry's row key for a fault (the fault's stable name,
    namespaced). A fault rename is a NEW key — the old row retires, the
    new name allocates fresh (the rename discipline, Kit.CodeRegistry). -/
def ecodeKey (name : String) : String := "fault." ++ name

/-! ## the allocation (pure) -/

/-- One fault's allocation: the persisted row `fault.<name>`'s code. A miss
    is the closed-world Diag (FT0001) — the valid space is the registry's
    fault rows, the did-you-mean the ONE engine's. -/
def allocOne (r : Kit.CodeRegistry) (m : FaultItem) :
    Except String (FaultItem × Nat) :=
  match r.lookup (ecodeKey m.name) with
  | some n => .ok (m, n)
  | none =>
      .error <| Kit.Diag.toString (Kit.Diag.closedWorld eFT0001
        s!"@[fault] `{m.name}`: no E-code row `{ecodeKey m.name}` in the \
          persisted registry (notes/code-registry.txt) — allocate the row \
          there first, then re-run the derive; a fault's code is never \
          hand-set"
        .error (ecodeKey m.name)
        ((r.map (·.name)).filter (fun n => n.startsWith "fault.")))

/-- All faults' allocations, in registration order. -/
def allocAll (r : Kit.CodeRegistry) (items : List FaultItem) :
    Except String (List (FaultItem × Nat)) :=
  items.foldl (fun (acc : Except String (List (FaultItem × Nat))) m =>
      match acc with
      | .error e => .error e
      | .ok ps => match allocOne r m with
        | .error e => .error e
        | .ok p => .ok (ps ++ [p]))
    (.ok [])

/-- The collision tooth: the allocated codes must be pairwise distinct.
    Empty iff nodup (Kit.dupNames' bridge, at the codes). -/
def dupCodes (ps : List (FaultItem × Nat)) : List Nat :=
  (Kit.dupNames (ps.map (fun p => toString p.2))).map (fun s => s.toNat?.getD 0)

/-- The full allocation: per-fault rows + the collision refusal (FT0004). -/
def allocAllCheck (r : Kit.CodeRegistry) (items : List FaultItem) :
    Except String (List (FaultItem × Nat)) :=
  match allocAll r items with
  | .error e => .error e
  | .ok ps =>
      let dups := dupCodes ps
      if dups.isEmpty then .ok ps
      else
        .error <| Kit.Diag.toString (Kit.Lane.usageDiag eFT0004
          s!"@[fault]: the allocation produced duplicate E-codes {dups} — \
            two faults landed on one persisted row; the mount's duplicate \
            refusal guarantees distinct keys, so this is a registry \
            invariant break (replay the gate)")

/-! ## the IO face (the ONE read the writer + the gate share) -/

/-- The persisted registry's path (repo-root-relative — the exe/gate run
    from the root; the gate's own constant is the source). -/
def registryPath : System.FilePath := "notes/code-registry.txt"

/-- Read + validate the persisted registry: parse, well-formedness gate
    (the CheckedProp's checker — an ill-formed file is a REFUSAL, never a
    silent accept). Every refusal is the FT0002 Diag. -/
def loadRegistry : IO (Except String Kit.CodeRegistry) := do
  unless ← registryPath.pathExists do
    return .error <| Kit.Diag.toString (Kit.Lane.usageDiag eFT0002
      "the persisted E-code registry is absent (notes/code-registry.txt) — \
        run `lake exe gates code-registry-check --write` to bootstrap, then \
        allocate the fault rows")
  match Kit.CodeRegistry.parse (← IO.FS.readFile registryPath) with
  | .error e =>
      return .error <| Kit.Diag.toString (Kit.Lane.usageDiag eFT0002
        s!"the persisted E-code registry failed to parse: {e}")
  | .ok r =>
      if Kit.codeRegistryWf.check r then return .ok r
      else
        return .error <| Kit.Diag.toString (Kit.Lane.usageDiag eFT0002
          "the persisted E-code registry is ill-formed — names must be \
            unique and rows sorted by code (the gate's replay is the \
            authority)")

end Faults
