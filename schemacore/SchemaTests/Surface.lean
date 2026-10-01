/- # SchemaTests.Surface — the `table!` surface's suite (wave-30 E1)

The v2 evolution + the ref/rule table + the six-word acceptance spec +
the curated-failure negative controls. The generated declarations
carry their own build-time teeth (the registration's replay, the keys
cascade's WF, the checks' scoping, the derived plan's key stability) —
those pin the LIVE lanes at each table's declaration; the spec below
pins the six-word mapping (every surface word names its machinery).

NOTE ON DOCSTRINGS: a doc comment must not directly precede a
`table!` command (after a declaration, Lean's docstring-attach rule
demands a DECLARATION command — the parse refuses). Section comments
and the generated structure's docstring carry the docs.

Five questions (notes/v3/01-core.md): the surface machinery's are in
SchemaCore.Surface; this module is the gate row (SchemaTests' surface
suite).
-/

import TestingKit.Harness
import SchemaCore
import SchemaTests.SurfaceV1

namespace SchemaTests.Surface

open SchemaCore TestingKit

/-! ## The v2 evolution (the migration lane's machinery, consumed) -/

-- `limit` added at the END with the type's default (the fill's source);
-- the key carried UNCHANGED (stable identities).
table! Account v2 where
  key: id
  id : UInt64
  owner : String
  limit : UInt64

/-! ## The ref + rule table (the keys + checks lanes, at the declaration) -/

table! Order where
  key: oid
  ref: cust : Customer
  oid : UInt64
  qty : UInt64
  rule: PositiveQty := .u64GtLit "qty" 0

/-! ## The six-word acceptance test (every surface word names its machinery) -/

def acctV1Fields : List Field :=
  [ { name := "id", ty := .u64 }, { name := "owner", ty := .string } ]

def acctV2Fields : List Field :=
  [ { name := "id", ty := .u64 }, { name := "owner", ty := .string }
  , { name := "limit", ty := .u64 } ]

def acctV1 : Item :=
  { name := "SchemaTests.SurfaceV1.Account", fields := acctV1Fields }

def acctV2 : Item :=
  { name := "SchemaTests.Surface.Account", fields := acctV2Fields }

def surfaceSpec : Spec :=
  Spec.ofList "the table! surface: every word names its machinery"
    (fun _ => do
      -- `table!`: the item level — the SAME @[schema] mount's reflection
      assert (Account.fields == acctV2Fields)
        "the table's fields snapshot drifted from the registered item"
      -- `key:` / `ref:`: the keys lane's rows (the KeyDecl mount)
      assert (Account.keyRow.record == "SchemaTests.Surface.Account" &&
              Account.keyRow.key == "id" &&
              Account.keyRow.foreign.isEmpty)
        "the key row drifted"
      assert (Order.keyRow.foreign.length == 1 &&
              Order.keyRow.foreign[0]!.field == "cust" &&
              Order.keyRow.foreign[0]!.target == "SchemaTests.SurfaceV1.Customer")
        "the ref row drifted (the target's registry name, never a string guess)"
      -- `rule:`: the check lane's row (the CheckItem mount; the generated
      -- def's name is `<table>.rule<Rule>`, the row's name `<table>-<rule>`)
      assert (Order.rulePositiveQty.schemaRef == "SchemaTests.Surface.Order" &&
              Order.rulePositiveQty.pred.reads == ["qty"])
        "the rule row drifted"
      -- `v2`: the migration lane's machinery — derived, not re-rolled
      match SchemaCore.deriveUpcaster "id" [] acctV1 acctV2 with
      | .ok p =>
          assert (p.stableKey "id") "the derived plan's key stability drifted"
      | .error r =>
          assert false s!"the derived plan drifted: {repr r}")
    [ ("the added field can host the key",
        fun _ =>
          assert (match SchemaCore.deriveUpcaster "limit" [] acctV1 acctV2 with
            | .ok _ => true | _ => false)
            "control fired: stable identities are ENFORCED — the ADDED \
              field cannot become the key (a migrated key is a different \
              entity set, 08 §19)")
    , ("the removal direction derives",
        fun _ =>
          assert (match SchemaCore.deriveUpcaster "id" [] acctV2
                    { name := "SchemaTests.SurfaceV1.Account"
                      fields := acctV1Fields } with
            | .ok _ => true | _ => false)
            "control fired: the REMOVAL refuses loudly — gone data has no \
              value-map target (no partial migration)")]
    1 42

/-! ## The negative controls (the curated failures, at the declaration; each refuses PRE-emission) -/

/-- error: [SR0001] error: table!: unknown clause `ky` — the clause list is a closed world (field lines are `name : type`) (got: ky) — valid: key:, ref:, rule:, deriving:, name : type — did you mean: key:? -/
#guard_msgs (error) in
table! Zorp where
  ky id

/-- error: [SR0003] error: table! Zorp2: the `ref:` target `Nowhere` is not a registered table with a declared key — declare the target's `table!` with its `key:` first (the forward reference rung, at authoring time) (got: Nowhere) — valid: Customer, Account, Account, Order -/
#guard_msgs (error) in
table! Zorp2 where
  key: a
  ref: g : Nowhere
  a : UInt64

/-- error: [SR0005] error: table! Zorp3: versioned declaration with no prior version in the registry — the first declaration of a name is v1 (no `v<N>` spelling); a version rides the registry's OWN event log (15 #7) (got: Zorp3) -/
#guard_msgs (error) in
table! Zorp3 v2 where
  key: a
  a : UInt64

/-- error: [SR0005] error: table! Account: `Account` is already registered — a redeclaration bumps the version (`table! Account v2 where …`); the versions ARE the registry's rows (got: Account) -/
#guard_msgs (error) in
table! Account where
  key: id
  id : UInt64
  owner : String
  limit : UInt64

end SchemaTests.Surface
