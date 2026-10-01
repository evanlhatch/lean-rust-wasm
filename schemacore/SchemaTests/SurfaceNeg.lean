/- # SchemaTests.SurfaceNeg — the evolution-face negative controls

The version-chain controls that need a PRIOR version of `Account`
WITHOUT the landed v2 structure name colliding: this module imports
`SchemaTests.Surface` (whose `Account` v2 is registered) and the
controls' `v3`/`v4` faces refuse PRE-emission (the analysis runs on
the clause syntax before anything is declared), so nothing registers
and the controls compose cleanly.

Five questions (notes/v3/01-core.md): the surface machinery's are in
SchemaCore.Surface; this module is part of the gate row.
-/

import SchemaCore
import SchemaTests.Surface

namespace SchemaTests.SurfaceNeg

/-- error: [SR0006] error: table! Account v3: the evolution refuses — removes field `limit` — gone data has no value-map target (the stable-id lane is the named follow-up) (got: Account) -/
#guard_msgs (error) in
table! Account v3 where
  key: id
  id : UInt64
  owner : String

/-- error: [SR0006] error: table! Account v4: the key moves from `id` to `owner` — a migrated key is a different entity set (08 §19: stable identities required) (got: owner) — valid: id -/
#guard_msgs (error) in
table! Account v4 where
  key: owner
  id : UInt64
  owner : String
  limit : UInt64

end SchemaTests.SurfaceNeg
