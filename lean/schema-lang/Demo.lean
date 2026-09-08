/-
# Demo — the authoring surface (THE source of truth)

PLAIN Lean declarations with `@[schema]` / `@[schema_fn]` /
`@[schema_resource]`. The reflection registers records, variants, func
signatures, and resources into the schema registry; every artifact (WIT
worlds, Rust types, delta types, Vortex dtypes) is generated from THIS
module. One source of truth — the hand-written `SchemaLang/Spec/Demo.lean`
data was folded in here and deleted.

Authors never see `Ty`, `Item`, or the registry. Wrong field types fail
at elaboration with the boundary fragment enumerated; wrong references
fail when the referenced type isn't registered first (register the
referenced type before the referencing one — v1 limitation).
-/

import SchemaLang.Meta.Reflect

/-! ## Records -/

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

/-! ## Variants -/

@[schema]
inductive Role where
  | admin
  | editor
  | viewer

@[schema]
inductive OrderError where
  | emptyCart
  | invalidItem (id : UInt64)
  | insufficientFunds (amount : Float)

/-! ## Async markers (WASI 0.3 at the boundary) -/

-- The Async prefix keeps the marker names from colliding with core's
-- lazy-stream `Stream`; the reifier matches the full qualified names.
namespace Async

def Future (a : Type) : Type := a

def Stream (a : Type) : Type := a

end Async

/-! ## Function signatures (the bodies are NOT part of the spec) -/

/-- u64 → option<user>. The body is a stub — the SIGNATURE is the spec;
    `_id` is the parameter's spec-name (the registered param list keeps
    the written name, underscore-silenced for the dead body). -/
@[schema_fn]
def getUser (_id : UInt64) : Option User :=
  none

/-- an order-error stream in, a user list out (async). -/
@[schema_fn]
def watchOrders (_into : OrderError) : Async.Future (List User) :=
  []

/-! ## Resources -/

/-- An opaque handle type: the schema records it as a resource. -/
@[schema_resource]
def Db : Type := Empty
