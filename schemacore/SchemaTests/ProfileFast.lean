/- # SchemaTests.ProfileFast — the fast slot's teeth + the hazard's
     profile law + the codegen face's pins (wave-30 E2)

The `fast` slot's consumer suite (16-surface §4.5, D38): the forfeits
are THEOREMS in SchemaCore.Profile (`fast_add_loses_identity`,
`exact_addition_never_hops`) — this suite pins their runtime faces,
the f64/2^53 hazard's BOTH-face fixture (the deterministic carrier
exact above the horizon; the fast hop inexact at the SAME operands —
the vortex compute lane's `hazard_above_f53_exact` /
`hazard_refused_not_rounded` shapes, cited as the shared discipline;
vortex is read-only here), the `fast` profile's erasure pins, and the
codegen face's text pins (Emit.Profiles — the Rust phantom
`Profiled<T, const P: u8>` / the TS branded `Profiled<T, P>`).

Negative controls are MANDATORY (15-patterns #5): the "fast is exact"
claim FAILS at the pinned horizon value; the "deterministic is the
hop" claim FAILS at the same value — the discipline is load-bearing
on both faces.
-/

import TestingKit.Harness
import SchemaCore.Profile
import SchemaCore.Emit.Profiles
import SchemaCore.Emit.Rust

namespace SchemaTests.ProfileFast

open SchemaCore TestingKit

/-- The substring check (core-only: splitOn; a nonempty pattern
    occurs iff the split leaves more than one piece). -/
def hasSubstr (s pat : String) : Bool := (s.splitOn pat).length > 1

/-! ## The fixtures -/

/-- The Money-cents carrier at a given units (the Main lane's clamp
    discipline — out-of-contract values unconstructible). -/
def mkCents (u : Nat) : Money 100 :=
  ⟨u % 2 ^ 64, Nat.mod_lt u (by decide), by decide⟩

/-- A deterministic carrier whose units sit ABOVE the f53 horizon
    (the vortex hazard's instrument's very face). -/
def aboveHorizon : Money 100 := mkCents (2 ^ 53 + 1)

/-! ## The fast lane's teeth (the runtime faces of the theorems) -/

def fastTeethSpec : Spec :=
  Spec.ofList "the fast slot: the forfeits are theorems, the teeth are live"
    (fun _ => assert ((
      -- IDENTITY LOSS (forfeit #1): above the horizon, x + 0 ≠ x —
      -- the hop loses the low bit (the vortex hazard's shape)
      ((Fast.add (f53 + 1) 0) == f53)
      -- and the sum is NOT the sum
      && (!(Fast.add (f53 + 1) 0 == f53 + 1))
      -- ASSOCIATIVITY DEATH (forfeit #2): the grouping is observable
      && ((Fast.add (Fast.add f53 1) 1) == f53)
          && ((Fast.add f53 (Fast.add 1 1)) == f53 + 2)
          && ((Fast.add (Fast.add f53 1) 1) != (Fast.add f53 (Fast.add 1 1)))
      -- BELOW the horizon the hop is honest (the speed trade's
      -- honest side — small integers survive)
      && ((Fast.add 5 7) == 12)))
      "the fast forfeits drifted")
    [ ("fast is exact", fun _ =>
        -- THE NEGATIVE CONTROL: the hop is NOT exact above the
        -- horizon — the claim dies at the pinned value
        assert ((Fast.add f53 1) == f53 + 1)
          "control fired: the f64 hop loses the low bit above 2^53 — \
            the exactness forfeit is load-bearing")
    , ("no obligation witness agrees with the hop", fun _ =>
        -- the THEOREM's runtime face: an exact addition and the hop
        -- diverge; the discharge is unconstructible
        assert ((deterministicAddition.add (f53 + 1) 0)
          == (Fast.add (f53 + 1) 0))
          "control fired: the exact sum and the hop DIVERGE — \
            exact_addition_never_hops is the type carrying the forfeit")
    , ("the erasure leaks", fun _ =>
        -- the phantom discipline covers ALL indices; the fast pins
        -- are the concrete face (the profile is compile-time-only)
        assert (((⟨(7 : UInt64)⟩ : Profiled .fast UInt64).raw : UInt64) != 7)
          "control fired: the fast profile erases to the base scalar — \
            the wire never sees the index") ]
    4 42

/-! ## The f64/2^53 hazard: BOTH faces at the SAME operands -/

def hazardSpec : Spec :=
  Spec.ofList "the f64/2^53 hazard as a profile law: the deterministic face exact above the horizon, the fast hop not"
    (fun _ => assert ((
      -- the DETERMINISTIC face: a units value ABOVE the horizon adds
      -- EXACTLY (the integer lane never routes through f64 — the
      -- profile law; Vortex.Compute's hazard_above_f53_exact is the
      -- compute lane's shape of the same discipline)
      ((aboveHorizon.raw.add? (mkCents 0).raw).map (fun c => c.units)
        == some (2 ^ 53 + 1))
      -- the overflow teeth still refuse (the capacity, not the
      -- horizon, is the deterministic face's only honesty boundary)
      && ((mkCents (2 ^ 64 - 1)).raw.add? (mkCents 1).raw == none)
      -- the FAST face at the SAME magnitude: the hop rounds (the
      -- forfeit the deterministic face never pays)
      && ((Fast.add (2 ^ 53 + 1) 0) == 2 ^ 53)
      -- the honest asymmetry: the hop is TOTAL — at the capacity it
      -- silently returns a value OUTSIDE the u64 wire domain, where
      -- the deterministic face REFUSES (the wrap-vs-refuse row)
      && ((Fast.add (2 ^ 64 - 1) 1) == 2 ^ 64)
      -- the horizon's number is the vortex instrument's (2^53 —
      -- 9007199254740992, the SAME constant both lanes name)
      && (f53 == 9007199254740992)))
      "the hazard profile law drifted")
    [ ("the deterministic face hops", fun _ =>
        -- THE NEGATIVE CONTROL: the deterministic add is NOT the
        -- hop — the exact sum above the horizon is the LAW, and the
        -- claim that it rounds is the fast face's forfeit alone
        assert (((aboveHorizon.raw.add? (mkCents 0).raw).map (fun c => c.units))
          == some (2 ^ 53))
          "control fired: the deterministic carrier's arithmetic is \
            integer arithmetic — no f64 hop, no rounding, ever")
    , ("the hop is exact at the top of the range", fun _ =>
        -- the honest asymmetry's control: the hop computes the TRUE
        -- sum here — it does not (2^53 rounds to 2^53); the
        -- deterministic face's law is the hop's forfeit
        assert ((Fast.add (2 ^ 53 + 1) 0) == 2 ^ 53 + 1)
          "control fired: the f64 hop loses the low bit at the SAME \
            operands where the deterministic face is exact — the \
            wrap-vs-refuse honesty row") ]
    4 42

/-! ## The codegen face's pins (Emit.Profiles — the phantom row) -/

-- NOTE ON THE EVIDENCE TIER: the text pins below are RUNTIME asserts
-- (the kernel splitOn over KB-size rendered text does not reduce —
-- the runtime-pin tier the emitter lanes already use). The erasure
-- itself is NOT at that tier — the model's Profiled.erase/iso pins
-- are kernel-rfl, and the generated consumers' size pin (the
-- committed profiled_erases_at_runtime test) holds the RUNTIME face
-- on the Rust side independently.

def codegenSpec : Spec :=
  Spec.ofList "the codegen face: the phantom carries the profile, the wire never sees it"
    (fun _ => assert ((
      -- the Rust face's contract rows: the const-generic PHANTOM +
      -- the transparent layout (the erasure is Rust's own
      -- guarantee) + the consumption point
      (hasSubstr SchemaCore.Emit.Profiles.profilePhantomRust
          "#[repr(transparent)]")
        && (hasSubstr SchemaCore.Emit.Profiles.profilePhantomRust
          "pub fn erase(self) -> T { self.0 }")
      -- the TS face's contract rows (the ONE brand symbol — never a
      -- second brand table; TS erases types at runtime wholesale)
      && (hasSubstr (Kit.Text.render SchemaCore.Emit.Profiles.profilePhantomTs)
          "[brand]: P")
      -- the fast tag rides the generated rendering (ONE enum, the
      -- tags are the LEAN ctor names, the tag discipline)
      && (hasSubstr SchemaCore.Emit.Rust.universeTypesRust "Fast,")
      -- the generated consumer's erasure pin rides the committed
      -- test text (the size pin IS the wire's own face)
      && (hasSubstr SchemaCore.Emit.Rust.universeTestsRust
          "fn profiled_erases_at_runtime")
      && (hasSubstr SchemaCore.Emit.Rust.universeTestsRust
          "Profile::COUNT, 3")))
      "the profile codegen face drifted")
    [ ("the phantom owns runtime bytes", fun _ =>
        -- THE NEGATIVE CONTROL: the phantom face carries NO runtime
        -- container — a field besides T would forfeit the erasure
        assert (hasSubstr SchemaCore.Emit.Profiles.profilePhantomRust
          "PhantomData")
          "control fired: the const-generic index is zero-sized BY \
            the language — a PhantomData field would be the second \
            runtime face the erasure forbids (and the face has none)")
    , ("a second brand table", fun _ =>
        assert (hasSubstr (Kit.Text.render
          SchemaCore.Emit.Profiles.profilePhantomTs) "declare const brand")
          "control fired: the TS face REUSES the ONE brand symbol — \
            a second declare would be a parallel table (the face \
            declares none)") ]
    4 42

/-- The suite's driver row. -/
def profileFastSpecs : List Spec := [fastTeethSpec, hazardSpec, codegenSpec]

end SchemaTests.ProfileFast
