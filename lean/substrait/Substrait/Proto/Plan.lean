/-
# Substrait.Proto.Plan

Wire-faithful model of Substrait's `plan.proto`: version, extension URNs,
simple extension declarations, and the top-level relations.
-/
import Substrait.Proto.Rel
import Substrait.Proto.Extensions

namespace Substrait.Proto

/-- Proto `Version` — the required `=== Version` header data. -/
structure Version where
  majorNumber : Nat
  minorNumber : Nat
  patchNumber : Nat
  producer : String := ""
  gitHash : String := ""
deriving Repr, BEq, Inhabited

/-- Convenience constructor for a plain version triple. -/
def Version.of (major minor patch : Nat) : Version :=
  { majorNumber := major, minorNumber := minor, patchNumber := patch, producer := "", gitHash := "" }

/-- True when nothing of the version header needs emitting. -/
def Version.isEmpty : Version → Bool
  | { majorNumber := 0, minorNumber := 0, patchNumber := 0, producer := "", gitHash := "" } => true
  | _ => false

/-- Proto `PlanRel` — either a bare relation or a `RelRoot` (with output names). -/
inductive PlanRel where
  | rel (r : Rel)
  | root (names : List String) (input : Rel)
  deriving Repr, BEq

/--
Proto `Plan` — the top-level container.  Mirrors `plan.proto`: version is
optional on the wire (presence-tracked), URNs and extension declarations are
lists, and `relations` is the list of top-level plan relations.
-/
structure Plan where
  version : Option Version
  extensionUrns : List SimpleExtensionUrn
  extensions : List ExtensionDeclaration
  relations : List PlanRel
deriving Repr, BEq, Inhabited

/-- The empty plan. -/
def Plan.empty : Plan :=
  { version := none, extensionUrns := [], extensions := [], relations := [] }

end Substrait.Proto
