/-
# Demo — the native Lean structures (the authoring surface)

These are PLAIN Lean structures: `@[schema]` reflects them into the
registry at elaboration time. This module is what `forge gen` imports
(`importModules #[`Demo]`) — the SSOT for the emitted artifacts.

Authors never see `Ty`, `Item`, or the registry. Wrong field types fail
at elaboration with the boundary fragment enumerated; wrong references
fail when the referenced structure isn't reflected first (register the
referenced structure before the referencing one — v1 limitation).
-/

import SchemaLang.Meta.Reflect

@[schema]
structure User where
  id : UInt64
  name : String
  email : String
  tags : List String

@[schema]
structure OrderItem where
  id : UInt64
  qty : UInt32
  price : Float

@[schema]
structure Order where
  id : UInt64
  items : List OrderItem
  total : Float
