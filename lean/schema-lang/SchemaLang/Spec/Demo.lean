/-
# SchemaLang.Spec.Demo — the seed universe

The demo schema: the shape every emitter (WIT, Rust, OpenAPI) and the
compat diff are developed against. Plain `def : List Item` (spec-as-data
staging; attribute-first moves in with the authoring surface).

  user     — record: id, name, email, tags
  role     — variant: admin | editor | viewer
  order-error — variant: emptyCart | invalidItem(u64) | insufficientFunds(f64)
  get-user — func: u64 → option<user>
  watch-orders — func: stream<order-error> → future<...> shape (stream in, future out)
  db       — resource
-/

import SchemaLang.Item

namespace SchemaLang.Spec

open SchemaLang

def user : Item :=
  .record "user"
    [ { name := "id", ty := .u64 }
    , { name := "name", ty := .string }
    , { name := "email", ty := .string }
    , { name := "tags", ty := .list (.string) }
    ]

def role : Item :=
  .variant "role"
    [ ("admin", none), ("editor", none), ("viewer", none) ]

def orderError : Item :=
  .variant "order-error"
    [ ("empty-cart", none)
    , ("invalid-item", some .u64)
    , ("insufficient-funds", some .f64)
    ]

def getUser : Item :=
  .func { name := "get-user"
        , params := [("id", .u64)]
        , ret := .option (.ty "user") }

def watchOrders : Item :=
  .func { name := "watch-orders"
        , params := [("into", .ty "order-error")]
        , ret := .future (.list (.ty "user")) }

def db : Item := .resource "db"

/-- The demo universe. -/
def demo : List Item :=
  [ user, role, orderError, getUser, watchOrders, db ]

end SchemaLang.Spec
