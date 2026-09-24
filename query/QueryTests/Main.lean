/-
# QueryTests — the fragment's pins, the determinacy typing, the weight-poly pins

Positive pins + the MANDATORY negative controls (15-patterns #5). The
runner is TestingKit's (`mainOfSuites`). Suites:

1. `fragment` — the worked schema's pinned evaluations: selection /
   projection / union (set semantics over Bool, bag counts over ℤ) /
   the equijoin; the spec reading (`QSat`) constructed from the
   computed weight through the bridge's forward face.
2. `weights` — the weight-polymorphism: the SAME query over Bool vs ℤ
   weights; THE ONE THEOREM's instance (`evalQ_wmap`) pinned at
   runtime with the identity and the negation maps.
3. `keyjoin` — the key-join surface: the at-most-one-per-key result is
   the TYPE (`KeyDecl.lookup?`'s Option shape); the negative controls
   (the non-unique left table hits the CONSERVATIVE `lookupAll`
   surface; a wrong ON field refuses).

Axiom self-check: `Axioms.lean` (imported below) pins `#print axioms`
over the lane's theorems — core-triple-only or the build fails.
-/

import Query
import TestingKit.Lcg
import TestingKit.Spec
import TestingKit.Harness
import QueryTests.Axioms

open Query SchemaCore TestingKit ZSet

/-! ## The worked schema (the keys lane's fixture shape) -/

/-- The Customer record: `id` is its declared primary key. -/
def custFields : List Field :=
  [{ name := "id", ty := .u64 }, { name := "name", ty := .string }]

/-- The declared key for Customer (data, the Keys lane's carrier). -/
def custKey : KeyDecl := { record := "Customer", fields := custFields, key := "id" }

/-- The Order record: `id` is its key, `cust` a foreign key to Customer. -/
def orderFields : List Field :=
  [{ name := "id", ty := .u64 }, { name := "cust", ty := .u64 },
    { name := "total", ty := .u64 }]

/-- The declared key + foreign key for Order. -/
def orderKey : KeyDecl :=
  { record := "Order", fields := orderFields, key := "id",
    foreign := [{ field := "cust", target := "Customer" }] }

def custRow (i : UInt64) (nm : String) : RowVals custFields :=
  .cons (.u64 i) (.cons (.string nm) .nil)

def orderRow (i c t : UInt64) : RowVals orderFields :=
  .cons (.u64 i) (.cons (.u64 c) (.cons (.u64 t) .nil))

def customers : List (RowVals custFields) :=
  [custRow 10 "ann", custRow 11 "bob", custRow 12 "cee"]

def orders : List (RowVals orderFields) :=
  [orderRow 1 10 200, orderRow 2 10 50, orderRow 3 11 500]

/-- The customers table with a DUPLICATE id (the negative control's
    non-unique left table). -/
def dupCustomers : List (RowVals custFields) :=
  [custRow 10 "ann", custRow 10 "impostor"]

/-! ## The queries -/

/-- Selection: the big orders (total > 100). -/
def bigOrders : Q orderFields orderFields :=
  .select (.u64GtLit "total" 100) .table

/-- Projection: orders → (cust, total) — columns 1 and 2. -/
def orderCols : Cols orderFields :=
  .cons ⟨1, by decide⟩ (.cons ⟨2, by decide⟩ .nil)

def custTotal : Q orderFields (orderCols.fields orderFields) :=
  .project orderCols .table

/-- The equijoin: orders ⋈ orders on cust = cust (the pairs sharing a
    customer, including self-pairs). -/
def sameCustJoin : Q orderFields (orderFields ++ orderFields) :=
  .join "cust" "cust" .table .table

/-- The projected row for order 1 (the computed schema: cust, total). -/
def projRow1 : RowVals (orderCols.fields orderFields) :=
  .cons (.u64 10) (.cons (.u64 200) .nil)

/-! ## Suite 1 — the fragment's pinned evaluations -/

def fragmentSpec : Spec :=
  Spec.ofList "the fragment: selection / projection / union / join, Bool + the bridge"
    (fun _ =>
      assert
        (weightW (evalQ bigOrders (tableW orders true)) (orderRow 1 10 200) = true
          && weightW (evalQ bigOrders (tableW orders true)) (orderRow 3 11 500) = true
          && weightW (evalQ bigOrders (tableW orders true)) (orderRow 2 10 50) = false
          && orderCols.fields orderFields = [{ name := "cust", ty := .u64 },
              { name := "total", ty := .u64 }]
          && weightW (evalQ custTotal (tableW orders true)) projRow1 = true
          && weightW (evalQ sameCustJoin (tableW orders true))
              (Row.append (orderRow 1 10 200) (orderRow 2 10 50)) = true
          && weightW (evalQ sameCustJoin (tableW orders true))
              (Row.append (orderRow 1 10 200) (orderRow 3 11 500)) = false
          && weightW (evalQ (.union .table .table) (tableW orders true))
              (orderRow 1 10 200) = true)
        "the fragment's Bool evaluation drifted")
    [ ("the projection keeps the dropped column (caught: it does not)",
        fun _ => assert (weightW (evalQ custTotal (tableW orders true))
          (.cons (.u64 1) (.cons (.u64 200) .nil)) = true)
          "the projection's ∃-reading was not exercised")
    , ("the selection keeps total ≤ 100 rows (caught: it restricts)",
        fun _ => assert (weightW (evalQ bigOrders (tableW orders true))
          (orderRow 2 10 50) = true)
          "the selection's restriction was not exercised") ]
    1 42

/-! ## Suite 2 — the weight-polymorphism -/

/-- The zero weight-map: the second ℤ-semiring homomorphism (the only
    two are the identity and zero — the ℤ-homomorphism fact; the
    doubling map's NEGATIVE control below is the runtime face). -/
def zeroWeightMap : WeightMap Int Int where
  map _ := wkindInt.zero
  map_zero := rfl
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl

def weightsSpec : Spec :=
  Spec.ofList "the weight-polymorphism: the same query over Bool and ℤ; evalQ_wmap"
    (fun _ =>
      assert
        (decide ((weightW (evalQ bigOrders (tableW orders true)) (orderRow 1 10 200) = true)
            ↔ (weightW (evalQ bigOrders (tableW orders 1)) (orderRow 1 10 200) ≠ 0))
          && decide ((weightW (evalQ bigOrders (tableW orders true)) (orderRow 2 10 50) = true)
            ↔ (weightW (evalQ bigOrders (tableW orders 1)) (orderRow 2 10 50) ≠ 0))
          && (toListW (wmap idWeightMap (evalQ bigOrders (tableW orders 1)))
            == toListW (evalQ bigOrders (wmap idWeightMap (tableW orders 1))))
          && (toListW (wmap zeroWeightMap (evalQ bigOrders (tableW orders 1)))
            == toListW (evalQ bigOrders (wmap zeroWeightMap (tableW orders 1)))))
        "the weight-polymorphism drifted")
    [ ("the doubling map commutes through the join (caught: mul is not preserved)",
        fun _ => assert
          (let J := evalQ sameCustJoin (tableW orders 1)
          let dj := fromListW (toListW J |>.map (fun p => (p.1, 2 * p.2)))
          let dm := fromListW (toListW (tableW orders 1) |>.map (fun p => (p.1, 2 * p.2)))
          weightW dj (Row.append (orderRow 1 10 200) (orderRow 1 10 200))
            == weightW (evalQ sameCustJoin dm)
              (Row.append (orderRow 1 10 200) (orderRow 1 10 200)))
          "the mul-homomorphism's necessity was not exercised")
    , ("the union over Bool counts bags (caught: set semantics)",
        fun _ => assert (weightW (evalQ (.union .table .table) (tableW orders true))
            (orderRow 1 10 200) = false)
          "the set semantics was not exercised") ]
    1 42

/-! ## Suite 3 — the key-join's determinacy typing -/

/-- The orders joined to their customers through the declared key
    (the ascription pins the schemas for the runtime decide). -/
def keyJoined : List (RowVals custFields × RowVals orderFields) :=
  keyJoinRows custKey "cust" customers orders

def keyjoinSpec : Spec :=
  Spec.ofList "the key-join: the at-most-one-per-key result is the type"
    (fun _ =>
      assert
        (custKey.uniqueOn customers = true
          && decide (keyJoined
            = [(custRow 10 "ann", orderRow 1 10 200),
              (custRow 10 "ann", orderRow 2 10 50),
              (custRow 11 "bob", orderRow 3 11 500)])
          && decide (keyJoined.map (·.1)
            = [custRow 10 "ann", custRow 10 "ann", custRow 11 "bob"])
          && (custKey.lookupAll customers ⟨.u64, .u64 10⟩ |>.length) == 1)
        "the key-join drifted")
    [ ("the at-most-one survives an unchecked key (caught: the conservative surface)",
        fun _ => assert (decide ((custKey.lookupAll dupCustomers ⟨.u64, .u64 10⟩ |>.length) ≤ 1))
          "the non-unique table's two-row lookupAll was not exercised")
    , ("a wrong ON field still joins (caught: the projection refuses)",
        fun _ => assert (decide ((keyJoinRows custKey "name" customers orders |>.length) == 3))
          "the missing-column refusal was not exercised") ]
    1 42

/-! ## The driver -/

def main : IO UInt32 :=
  mainOfSuites [("QueryTests", [fragmentSpec, weightsSpec, keyjoinSpec])]
