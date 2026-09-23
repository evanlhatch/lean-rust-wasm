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

module

public import SchemaLang.Meta.Reflect
public import SchemaLang.Meta.Derive
public import SchemaLang.Migration
public import SchemaLang.Validate
public import SchemaLang.WitnessSpec
public import Faults.Registry

@[expose] public section

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

-- The order-fault variant's Lean carrier. The SCHEMA registration is
-- the fault registry's fold below (`derive_fault_variant` — W10.1's
-- one-fault unification): the registry IS the wire variant's SSOT, so
-- there is no `@[schema]` hand-pairing here to drift from it. The
-- carrier stays a plain inductive — the compiled guest impls
-- (`GuestImpl.orderErrorValid`) match these constructors.
inductive OrderError where
  | emptyCart
  | invalidItem (id : UInt64)
  | insufficientFunds (amount : Float)

-- The fault rows — ONE declaration per failure mode (the design doc's
-- §2.2): the wire case, the fast-observe enum case, the E-code, and
-- the advice all project from the registry row. The rows live HERE
-- (not in `Faults.Spec.Demo`) because `watchOrders`' `@[schema_fn]`
-- reifies the `OrderError` reference at THIS module's elaboration —
-- the rows + the fold must precede it; the spec snapshot downstream
-- replays the extension. `meta`: the attribute's `.afterCompilation`
-- handler evaluates the compiled value — the module system's phase
-- rule demands the mark here (the plain-file spec modules got it for
-- free).
@[fault] meta def faultEmptyCart : Faults.FailureModeItem :=
  { name := "emptyCart", display := "the cart is empty"
  , category := .content, advice := "add an item before checkout"
  , payload := [] }

@[fault] meta def faultInvalidItem : Faults.FailureModeItem :=
  { name := "invalidItem", display := "invalid cart item: {id}"
  , category := .content, advice := "check cart state"
  , payload := [("id", .u64)] }

@[fault] meta def faultInsufficientFunds : Faults.FailureModeItem :=
  { name := "insufficientFunds", display := "insufficient funds: {amount}"
  , category := .content, advice := "top up the balance"
  , payload := [("amount", .f64)] }

-- THE FOLD: the rows project into the schema universe as the wire
-- variant, registered under the carrier's name. Re-running the fold
-- agrees with itself; a fault row and a registered schema variant
-- DISAGREEING on a case (name or payload) fails right here — the
-- negative control lives in FaultsTests.
derive_fault_variant OrderError

/-! ## Async markers (WASI 0.3 at the boundary) -/

-- `Async.Future`/`Async.Stream`: the ONE copy lives in
-- `SchemaLang.Meta.Reflect` (the reifier matches them by name).

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

-- DERIVED at elaboration from the registry
-- (`SchemaLang.Meta.derive_schema_fields`): User's field list + the
-- row builder (with its `list string` element helper). Not a hand
-- mirror: renaming a User field fails THIS module's elaboration.
derive_schema_fields userNameLenFields userNameLenRowOf from User

-- The row the cited theorem pins: id 5, name "abcd" (length 4 > 3 —
-- the `name-min-length` predicate's verdict is `true`). The body is
-- the derived builder applied to the record literal — the VALUES are
-- the pin, the SHAPE is derived.
def userNameLenRow : SchemaLang.RowVals userNameLenFields :=
  userNameLenRowOf ⟨5, "abcd", "e", []⟩

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
  simp only [SchemaLang.evalB, SchemaLang.evalRaw, SchemaLang.VExpr.colOf,
    SchemaLang.string_len, SchemaLang.boolToU64]
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

/-! ## The guestVerified witness registry (W9.4 — design-guest-verified §4)

The FIRST consumer of the fifth obligation tier: the User record's
v1→v2 migration segment. `SchemaLang.EventSourced` ships the identity
upcaster (its documented v1 exclusion — wire-level upcasting is the
Migration/Snapshot lane), so this segment's migrated rows ARE the
journal rows; a real retype migration lands as a remedy row above and
regenerates this witness against the NEW surface (the envelope
fingerprint changes — a stale witness is a decode-level refusal). The
claim is W9.1's chain rule: the `id-positive` invariant's mirror
(`id > 0`) holds of the initial row AND of every referenced log row.
The data rides the DERIVED field list (`userNameLenFields` — a User
field rename fails THIS module's elaboration; the spec cannot drift
from the record). The emitter (`SchemaLang.Emit.Witness`) generates +
self-checks + byte-ties the certificate; `SchemaObligation.discharge`'s
guestVerified arm consumes it. -/

/-- The initial row the chain claim certifies from (id 1 — the
    invariant holds). -/
def demoWitnessInitRow : SchemaLang.RowVals userNameLenFields :=
  userNameLenRowOf ⟨1, "ab", "a@x", []⟩

/-- The committed log segment the chain references by OFFSET (design
    §7.2: offsets, never copies — the guest already holds the log). -/
def demoWitnessLog : List (SchemaLang.RowVals userNameLenFields) :=
  [userNameLenRowOf ⟨2, "cd", "c@x", []⟩, userNameLenRowOf ⟨3, "ef", "e@x", []⟩]

/-- The obligation's registration row: replaying the segment preserves
    `id-positive` — claim + decoded context + the artifact name the
    discharge's evidence cites. -/
def demoWitnessSpecUserV1V2 : SchemaLang.WitnessSpec :=
  { label := "user-v1-v2-id-positive"
  , artifact := "witnesses/user-v1-v2-id-positive.wtn"
  , claim := .chain [⟨0⟩, ⟨1⟩] (.gt (.col "id") (.lit 0))
  , ctx := ⟨userNameLenFields, demoWitnessInitRow, demoWitnessLog⟩ }

/-- THE REGISTRY (the `registeredMigrations` precedent: spec data lives
    in the spec module; the emitter driver reads the module it already
    imports). One row per guestVerified obligation. -/
def demoWitnesses : List SchemaLang.WitnessSpec := [demoWitnessSpecUserV1V2]
