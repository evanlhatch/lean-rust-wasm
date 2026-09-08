/-
# LeanSubstrait.Proto.Extensions

Wire-faithful model of Substrait's `extensions/extensions.proto` surface:
URN declarations and simple extension declarations (functions, types, type
variations).  Anchors are plain `Nat`s, local to a plan, as in the wire format.
-/
namespace LeanSubstrait.Proto

/-- Proto `SimpleExtensionUrn` — `{ extension_urn_anchor, urn }`. -/
structure SimpleExtensionUrn where
  extensionUrnAnchor : Nat
  urn : String
deriving Repr, BEq, Inhabited

/-- Proto `SimpleExtensionDeclaration` — one of the three mapping kinds. -/
inductive ExtensionDeclaration where
  /-- `ExtensionFunction { extension_urn_reference, function_anchor, name }`. -/
  | function (extensionUrnReference : Nat) (functionAnchor : Nat) (name : String)
  /-- `ExtensionType { extension_urn_reference, type_anchor, name }`. -/
  | extType (extensionUrnReference : Nat) (typeAnchor : Nat) (name : String)
  /-- `ExtensionTypeVariation { extension_urn_reference, type_variation_anchor, name }`. -/
  | typeVariation (extensionUrnReference : Nat) (typeVariationAnchor : Nat) (name : String)
deriving Repr, BEq, Inhabited

/-- The extension kind of a declaration, used by the emitters. -/
def ExtensionDeclaration.kind : ExtensionDeclaration → String
  | .function _ _ _ => "function"
  | .extType _ _ _  => "type"
  | .typeVariation _ _ _ => "type_variation"

end LeanSubstrait.Proto
