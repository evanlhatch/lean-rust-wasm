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
import SchemaLang.Migration

-- The registration-emitted instances (`instUpdatePure.<name>`) park in
-- the FRAMEWORK's namespace by construction (Reflect's command emits
-- into SchemaLang) — the packageNamespace lint's helper rule does not
-- apply to framework-emitted decls (no source-site attribute exists).
set_option linter.guestlang.packageNamespace false -- because the framework's registration command emits the instances into SchemaLang by construction; no source-site attribute exists

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

/-- Defined as `Future` itself: both are boundary markers whose bodies are
the identity BY DESIGN, so the bodies share one definition rather than two
copies (the dupDefBodies lesson — one anchor, aliases of it). -/
def Stream (a : Type) : Type := Future a

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

/-! ## Registered invariants + updates (the spec data — the emission
    lanes' registry rows)

The demo's `schema_invariant` / `schema_update` registrations live HERE
(not in Tests): they ARE spec data — the emitters read the replayed
registry (`Emit.GenCtx`), so a registration in the spec module is what
the byte-tied `invariants_generated.rs` / `updates_generated.rs`
reflect. Names are STRINGS where the registry name is kebab (`
id-positive`) — the emitted Rust carries it verbatim; a kebab word is
not a Lean ident (the string-form name is Meta.Reflect's authoring
surface for exactly this). `proved` cites a theorem name, RESOLVED at
the registration (`SchemaLang.checkCitation?` — the elaboration gate:
the theorem must live where it's cited, so `userNameLenProved` is
below, in THIS module). The `where` clause is REQUIRED (`VExpr .bool`
has no literal-true — the always-true idiom for `self_bump`). -/

-- The executable boundary check (tier: boundary-check).
schema_invariant "id-positive" for User :=
  SchemaLang.VExpr.gt (SchemaLang.VExpr.colOf "id") (SchemaLang.VExpr.lit 0)

-- The row the cited theorem pins: id 5, name "abcd" (length 4 > 3 —
-- the `name-min-length` predicate's verdict is `true`).
def userNameLenRow :
    SchemaLang.RowVals
      [⟨"id", SchemaLang.Ty.u64⟩, ⟨"name", SchemaLang.Ty.string⟩,
        ⟨"email", SchemaLang.Ty.string⟩,
        ⟨"tags", SchemaLang.Ty.list SchemaLang.Ty.string⟩] :=
  .cons (.u64 5) (.cons (.string "abcd")
    (.cons (.string "e") (.cons (.list .nil) .nil)))

-- THE CITED THEOREM (the proved tier's resolver target): the
-- `name-min-length` predicate's verdict on the pinned row, as a
-- kernel-checked `validates … = true` — the exact shape
-- `SchemaLang.checkCitation?` demands at the registration below.
theorem userNameLenProved :
    SchemaLang.validates
      (SchemaLang.VExpr.gt
        (SchemaLang.VExpr.strlen (SchemaLang.VExpr.colOf "name"))
        (SchemaLang.VExpr.lit 3))
      userNameLenRow = true := by
  unfold SchemaLang.validates
  simp only [SchemaLang.evalB, SchemaLang.evalU, SchemaLang.VExpr.colOf,
    SchemaLang.hasColHead, SchemaLang.ColPath.get,
    _root_.string_len, SchemaLang.string_len, SchemaLang.boolToU64]
  rfl

-- The proved registration: the tier is `proved` via the CITED theorem
-- name (RESOLVED at this command — a dangling or wrong-shaped citation
-- fails right here, the `Dbsp.Certs.#check_cert` gate).
schema_invariant "name-min-length" for User proved userNameLenProved :=
  SchemaLang.VExpr.gt (SchemaLang.VExpr.strlen (SchemaLang.VExpr.colOf "name")) (SchemaLang.VExpr.lit 3)

-- Linear u64 write — guard on the ORIGINAL id, write a constant.
-- reads = ["id"] (guard only), writes = ["id"], selfReading = false.
schema_update reset_id for User id := SchemaLang.VExpr.lit 0
  where SchemaLang.VExpr.gt (SchemaLang.VExpr.colOf "id") (SchemaLang.VExpr.lit 100)

-- Linear STRING write (a column copy — VExpr has no string literal, so
-- string writes are copies). reads = ["name"], writes = ["email"].
schema_update echo_email for User email := SchemaLang.VExpr.colOf "name"
  where SchemaLang.VExpr.gt (SchemaLang.VExpr.strlen (SchemaLang.VExpr.colOf "name")) (SchemaLang.VExpr.lit 3)

-- The SELF-READING classification (the enforcement ladder's input): the
-- value reads the WRITTEN column → nonlinear (the journal carries S0).
-- The guard is the always-true idiom — the `where`-required escape
-- hatch, pinned here.
schema_update self_bump for User id := SchemaLang.VExpr.colOf "id"
  where SchemaLang.VExpr.eq (SchemaLang.VExpr.lit 0) (SchemaLang.VExpr.lit 0)

/-! ## Registered migrations (6.5.2 authoring surface) -/

/-- The remedy evidence `just breaking` consumes (one row per available
    migration; the exe folds this into `Migration.verdictOf`). A real
    breaking change lands HERE — the migration def plus its soundness
    theorem (the `widenU32U64_sound` shape) — and the gate reports
    `remedied` (exit 2: apply the migration to the event log, then
    re-baseline) instead of failing. Registered but currently UNEARNED:
    the baseline has no `qty` retype, so the gate stays `clean` — the
    row is exercised in Tests. -/
def registeredMigrations : List SchemaLang.Migration :=
  [ { item := "OrderItem"
    , fields := [SchemaLang.widenU32U64 "qty"] } ]
