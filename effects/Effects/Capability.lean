/-
# Effects.Capability — the capability valves as effect rows (D3)

The WASI capability discipline (notes/design-wave-30.md D3; 10 Phase 7's
acceptance "the WIT capability set = the join of export rows"): the
component's required capabilities are DERIVED from its world's imports —
each import interface maps to a row of the CLOSED effect atoms
(`Effects.Basic`'s eight), and the required capability set is the FOLD
JOIN of those rows over the world's import list. Never a bitflag (the
legacy `CapabilitySet`'s honest migration: the bitflags die here — the
closed lattice's sub-effect order is the valve).

The valve: the host's allowance is ITSELF a row, and a component loads
only when `Row.le required allowed` holds — the decided sub-effect order
(`Row.sub`, `sub_iff_le`) is the enforcement. DEFAULT-DENY is the empty
allowance: the empty row permits nothing (`Row.le _ []` fails for every
non-empty required row — the teeth pins below). An interface absent from
the mapping table is NOT derivable — `wasiRow` returns `none`, the
derivation returns `none`, and the load refuses (an undeclared
capability request cannot even be NAMED, let alone granted).

The shape: a component's world declares imports; the derivation is a
FOLD over that list, and the law `mem_deriveRow` says the derived row's
membership is EXACTLY the membership over the per-import rows — the set
IS the rows' join (the join discipline's law, proved). `valve_below` is
the valve's monotonicity: every recognized import's row sits below the
derived row, so an allowance admitting the derived row admits every
import's exercise. The Rust host (`crates/mandate-host`'s wasi lane)
consumes this shape: it derives the row from the component TYPE's
imports (the ground truth), checks the allowance, and refuses at LOAD —
before instantiation — with the first deficient import named.

Doctrine slots (notes/v3/01-core.md, the five questions):
- **Root**: Universe (finite data: the string→row mapping table over the
  closed atoms) — the table is CLOSED like the atoms; a new WASI
  interface is ONE row added to the table (a deliberate doctrine act),
  never a new flag.
- **Carrier grade**: the type-level annotation — the required set rides
  as an effect row (the same carrier `Effects.Basic` established), the
  allowance beside it, the valve the decided order between them.
- **Spine reading**: none yet — the rendered-table lane (the table
  emitted as a shared artifact both this proof and the Rust mirror
  read) is the named follow-up; until then the Rust mirror is pinned by
  the same fixtures its tests name, and the divergence is caught there.
- **Ladder rung**: hand theorems of the small generic kind — the fold's
  membership law and the valve's monotonicity, proved once,
  membership-level, all constructive.
- **Gate row**: the axiom sweep (the report's Effects section) +
  EffectsTests' pins. The Rust valve tests are the consumer face.

Core-only: no mathlib, no Batteries (the cone rule).
-/

import Effects.Basic

namespace Effects

/-! ## The interface table (the closed import → row mapping) -/

/-- The WASI interface-id → effect-row mapping (D3's closed table, 08
    §8's registry-derived rows): each WASI interface the component's
    world may import maps to the row of atoms its exercise demands —
    `hostIO` for every boundary crossing, plus the specific atoms
    (`clock` for the clocks' faces, `read`/`write` for the filesystem's,
    `guestCap` for the random source's nondeterminism). An interface
    ABSENT from the table is not derivable (`none`): the valve refuses —
    an unrecognized import can never be waved through by a default. The
    table covers wasi 0.3's p3-served interfaces (the `p3::add_to_linker`
    faces: cli, clocks, filesystem, random, sockets). -/
def wasiRow (id : String) : Option Row :=
  match id with
  | "wasi:cli/environment@0.3.0" => some [Effect.hostIO]
  | "wasi:cli/exit@0.3.0" => some [Effect.fail]
  | "wasi:cli/stdin@0.3.0" => some [Effect.read, Effect.hostIO]
  | "wasi:cli/stdout@0.3.0" => some [Effect.write, Effect.hostIO]
  | "wasi:cli/stderr@0.3.0" => some [Effect.write, Effect.hostIO]
  | "wasi:cli/terminal-stdin@0.3.0" => some [Effect.read, Effect.hostIO]
  | "wasi:cli/terminal-stdout@0.3.0" => some [Effect.write, Effect.hostIO]
  | "wasi:cli/terminal-stderr@0.3.0" => some [Effect.write, Effect.hostIO]
  | "wasi:clocks/monotonic-clock@0.3.0" => some [Effect.clock, Effect.hostIO]
  | "wasi:clocks/system-clock@0.3.0" => some [Effect.clock, Effect.hostIO]
  | "wasi:clocks/timezone@0.3.0" => some [Effect.clock, Effect.hostIO]
  | "wasi:filesystem/types@0.3.0" => some [Effect.read, Effect.write, Effect.hostIO]
  | "wasi:filesystem/preopens@0.3.0" => some [Effect.read, Effect.hostIO]
  | "wasi:random/random@0.3.0" => some [Effect.guestCap, Effect.hostIO]
  | "wasi:random/insecure@0.3.0" => some [Effect.guestCap, Effect.hostIO]
  | "wasi:random/insecure-seed@0.3.0" => some [Effect.guestCap, Effect.hostIO]
  | "wasi:sockets/instance-network@0.3.0" => some [Effect.hostIO]
  | "wasi:sockets/tcp@0.3.0" => some [Effect.hostIO]
  | "wasi:sockets/udp@0.3.0" => some [Effect.hostIO]
  | "wasi:sockets/ip-name-lookup@0.3.0" => some [Effect.hostIO]
  | _ => none

/-! ## The derivation: the fold join over the world's imports -/

/-- The component's required capability row: the FOLD JOIN of its
    imports' rows (the join discipline's law — the set IS the rows'
    join, `mem_deriveRow`). `none` = the valve's refusal: some import
    names no row in the closed table (an undeclared capability). -/
def deriveRow : List String → Option Row
  | [] => some []
  | id :: ids =>
    match wasiRow id with
    | none => none
    | some a => (deriveRow ids).map (fun t => Row.join a t)

/-- The empty world derives the empty row — the pure discipline. -/
theorem deriveRow_nil : deriveRow [] = some [] := rfl

/-! ## The derivation's law: the set = the rows' join (proved) -/

/-- THE D3 LAW: membership in the derived row is membership in SOME
    import's row — the capability set is exactly the join of the
    per-import rows (the join discipline over the world's import list,
    proved once, membership-level). -/
@[nolint linter.guestlang.zeroCitation "public API: THE D3 derivation law — the host's valve re-derives its shape (the Rust mirror); the rendered-table lane is the named follow-up"]
theorem mem_deriveRow (x : Effect) (ids : List String) (r : Row)
    (h : deriveRow ids = some r) :
    x ∈ r ↔ ∃ id, id ∈ ids ∧ ∃ a, wasiRow id = some a ∧ x ∈ a := by
  induction ids generalizing r with
  | nil =>
    simp only [deriveRow] at h
    cases h
    simp
  | cons id ids ih =>
    simp only [deriveRow] at h
    cases hw : wasiRow id with
    | none =>
      rw [hw] at h
      simp at h
    | some a =>
      rw [hw] at h
      cases hd : deriveRow ids with
      | none =>
        rw [hd] at h
        simp at h
      | some t =>
        rw [hd] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rw [Row.mem_join]
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact ⟨id, List.mem_cons_self, a, hw, hx⟩
          · rcases (ih t hd).mp hx with ⟨id', hmem, a', hw', hx'⟩
            exact ⟨id', List.mem_cons_of_mem _ hmem, a', hw', hx'⟩
        · intro ⟨id', hmem, a', hw', hx'⟩
          rcases List.mem_cons.mp hmem with he | hm
          · rw [he] at hw'
            have haa : a' = a := Option.some.inj (hw'.symm.trans hw)
            exact Or.inl (haa ▸ hx')
          · exact Or.inr ((ih t hd).mpr ⟨id', hm, a', hw', hx'⟩)

/-! ## The valve: the derived row's monotonicity (the load tooth) -/

/-- THE VALVE LAW: every recognized import's row sits below the world's
    derived row — an allowance admitting the derived row admits every
    import's exercise, and one NOT admitting it (the empty allowance =
    default-deny) refuses with a named deficiency. -/
@[nolint linter.guestlang.zeroCitation "public API: THE D3 valve law — the load-time refusal's justification; the Rust valve consumes its shape"]
theorem valve_below (ids : List String) (r : Row) (id : String) (a : Row)
    (hmem : id ∈ ids) (hrow : wasiRow id = some a) (h : deriveRow ids = some r) :
    Row.le a r :=
  fun e hx => (mem_deriveRow e ids r h).mpr ⟨id, hmem, a, hrow, hx⟩

/-! ## The pins (the table's rows + the valve's teeth, reduced) -/

/-- The derivation reduces: the env interface's row is the boundary
    crossing alone. -/
example : deriveRow ["wasi:cli/environment@0.3.0"] = some [Effect.hostIO] := rfl

/-- The filesystem types' face: read AND write AND the crossing. -/
example : deriveRow ["wasi:filesystem/types@0.3.0"]
    = some [Effect.read, Effect.write, Effect.hostIO] := rfl

/-- Two imports JOIN: the derived row is the union (the join
    discipline — never the max, never a flag). -/
example : deriveRow ["wasi:cli/environment@0.3.0", "wasi:clocks/monotonic-clock@0.3.0"]
    = some [Effect.clock, Effect.hostIO] := rfl

/-- An import outside the table is NOT derivable — the valve's refusal
    shape (an undeclared capability cannot be named). -/
example : deriveRow ["acme:widget/gadget@1.0.0"] = none := rfl

/-- THE DEFAULT-DENY TOOTH: the empty allowance refuses every non-empty
    required row (the closed box). -/
example : ¬ Row.le [Effect.hostIO] [] := by decide

/-- The matching allowance passes (the decided order's positive face). -/
example : Row.le [Effect.hostIO] [Effect.hostIO] := by decide

/-- THE UNDER-ALLOWANCE TOOTH: `read` beyond a hostIO-only allowance
    refuses — the valve names the deficiency. -/
example : ¬ Row.le [Effect.read, Effect.hostIO] [Effect.hostIO] := by decide

end Effects
