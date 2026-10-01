/- # SchemaTests.SurfaceV1 — the `table!` surface's v1 fixtures

The version chain's OLD face (the migration-proof module): `Customer`
(the ref target — its key declared first, since the forward-reference
rung refuses a keyless target) and `Account` v1 (the evolution
fixture's old face, two fields). The v2 faces live in
`SchemaTests.Surface`; the unsupported-change controls live in
`SchemaTests.SurfaceNeg` (they refuse PRE-emission, so nothing
registers — but the table names must not collide with the landed
ones, and a same-module version bump is impossible anyway: the
structure name is the table's name).

NAMESPACED, deliberately: the version chain's identity is the LAST
component of the registered name — two namespaces can carry `Account`
at v1 and v2 (the registry's rows are the versions, 15 #7). The
deriving handlers' generated names are `_root_.`-anchored (the
namespace bug the surface exposed and the same change fixes —
DeriveMeta's `tnIdent`/`tnDeclId`).

Five questions (notes/v3/01-core.md): the fixtures' own — the surface
module (SchemaCore.Surface) carries the machinery's answers.
-/

import SchemaCore

namespace SchemaTests.SurfaceV1

/-! The customer table (the ref target). -/

table! Customer where
  key: id
  id : UInt64
  name : String

/-! The account table (the evolution fixture's old face). -/

table! Account where
  key: id
  id : UInt64
  owner : String

end SchemaTests.SurfaceV1
