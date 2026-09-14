/-
# GuestlangStd — the compiled stdlib + the guest implementations

The std OPS (`strlen`/`strcat`) have REAL Lean bodies — they are the
differential ORACLE (the wasm side must compute the same answers). The
BACKEND never compiles these bodies: it special-cases the NAMES as
intrinsics (`$string_len` / `$string_cat` — the runtime.wat primitives
over the guest string layout `{rc@0, tag=250@4, len u32@8, bytes@16}`),
the standard compiler practice for intrinsic ops. Guest strings are
BYTE-strings: `$string_len` counts bytes, which equals Lean's
`String.length` (chars) on ASCII — the oracle rows are ASCII-only
(non-ASCII byte/char divergence is documented, v1).

`@[guest_std]` (not `@[guest]`): the std surface — String is legal
here; the strict app surface stays string-free until the type pipeline
flattens string results through the canonical ABI (greet: done).
-/

import CodegenCore.GuestGate
import Demo
import SchemaLang.Meta.Reflect
import SchemaLang.Meta.Derive
import SchemaLang.Validate
import GuestlangStd.StrOps
import LintKit.Basic

-- the ops (strlen/strcat) are declared in GuestlangStd.StrOps — the
-- root imports them; the impls below are the schema functions' bodies.

namespace GuestImpl

open GuestlangStd

/-- The `get-user` implementation: none for the sentinel id, a real
    record otherwise (strings via the std intrinsics; a two-element
    tag list — List cons cells the adapter must walk + flatten). -/
@[guest_std, schema_fn, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def getUser (id : UInt64) : Option User :=
  if id == 0 then none
  else some
    { id := id
    , name := strcat "user-" "name"
    , email := "u@guestlang.dev"
    , tags := ["alpha", "beta"] }

/-- The FIRST string through the component boundary: a `string`-returning
    export. The canonical ABI flattens a string result to (ptr, len) —
    the embedder's MAX_FLAT_RESULTS=1 convention: the adapter writes
    (bytes-ptr, byte-len) into a static return area and returns its
    pointer. Lean body = the differential oracle. -/
@[guest_std, schema_fn, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def greet (n : UInt64) : String :=
  if n > 0 then strcat "hello " "guest" else "bye"

/-- The string demo: a RUNTIME-dependent string (no constant folding —
    the branch depends on the argument), appended, then measured. The
    differential gate compares Lean's real eval against the wasm
    intrinsics: n > 0 → strlen("hello world") = 11; else 1. -/
@[guest_std, schema_fn, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def strLenDemo (n : UInt64) : UInt64 :=
  strlen (if n > 0 then strcat "hello" " world" else "!")

/-- The `watch-orders` implementation (the ASYNC schema fn): the list
    of users = the delta batch. The body = SYNC-computable (the list
    computes immediately) — the async-ness lives in the SIGNATURE (the
    canon lift's async option + the task machinery); wit-bindgen's own
    guests are the same shape. The DIFFERENTIAL ORACLE. -/
@[guest_std, schema_fn, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def watchOrders (_into : OrderError) : Async.Future (List User) :=
  [ { id := 1, name := "first", email := "1@g.dev", tags := ["a"] }
  , { id := 2, name := "second", email := "2@g.dev", tags := ["b"] } ]

/-- The STREAM's differential impl: the same data every call — the
    stream version of watch-orders' delta shape (the items flow one
    direction; the host reads until the stream closes). The delivery =
    the STREAM contract (`delivery = stream`): the world renders the
    result as `stream<u64>` — the host consumes the items
    incrementally via the async-lift's stream builtins. -/
@[guest_std, schema_fn stream] 
def watchCounts (_n : UInt64) : Async.Future (List UInt64) :=
  [ 42, 43 ]

/-- The USER-payload stream: the same records as watch-orders — the
    32-byte flat elements flow through the stream. -/
@[guest_std, schema_fn stream] 
def watchUsers (_n : UInt64) : Async.Future (List User) :=
  [ { id := 1, name := "first", email := "1@g.dev", tags := ["a"] }
  , { id := 2, name := "second", email := "2@g.dev", tags := ["b"] } ]

/-- User's schema, as the validator sees it. THE REDUCIBILITY RULE
    (`SchemaLang.Field`): `abbrev`, not `def` — instance search sees
    through reducibles only. -/
abbrev userSchema : List SchemaLang.Field :=
  [ ⟨"id", .u64⟩, ⟨"name", .string⟩, ⟨"email", .string⟩
  , ⟨"tags", .list .string⟩ ]

-- The validator's body, SCHEMA-INDEXED: `id > 0` over userSchema.
-- The field-ref is HasCol-typed — misspell it (`"iid"`) and this
-- module fails to BUILD (no instance — the elaboration error). The
-- VExpr/evalV layer (SchemaLang.Validate) is the executable spec; the
-- wasm backend compiles evalV as an ordinary target (GenMain).
-- `@[guest_std]`: the guest-mark registry — the backend's manifest fold
-- compiles every marked decl (no hand-list).
@[guest_std]
def userCheck : SchemaLang.VExpr userSchema .bool :=
  SchemaLang.VExpr.gt (SchemaLang.VExpr.colOf "id") (SchemaLang.VExpr.lit 0)

/-- The name-length condition, VExpr form: the `strlen` node over the
    name column, `> 3`. `@[guest_std]` (the WIRED compiled lane —
    SchemaLang.Validate's `evalU` strlen arm reads the boxed string's
    raw length via the runtime `$string_len`): this is a compile
    target, consumed by `userComplete`'s check. The evalV/raw readings
    AGREE on it (the schema-lang tests pin the tie + the len=3/4
    boundary flip). ASCII note: the boxed eval's length is Lean's
    `String.length` (chars) = the std `$string_len` (bytes) on ASCII —
    the StrOps v1 byte/char stance. -/
@[guest_std]
def userNameLenCheck : SchemaLang.VExpr userSchema .bool :=
  SchemaLang.VExpr.gt
    (SchemaLang.VExpr.strlen (SchemaLang.VExpr.colOf "name"))
    (SchemaLang.VExpr.lit 3)

/-- The complete-record check: the id gate AND the name-length gate in
    ONE VExpr (the conjunction compiles as the raw 0/1 MULTIPLICATION —
    `evalB`'s `.and` arm). The tags gate rides OUTSIDE the VExpr (below):
    the family has no list-length node yet. -/
@[guest_std]
def userCompleteCheck : SchemaLang.VExpr userSchema .bool :=
  SchemaLang.VExpr.and userCheck userNameLenCheck

/-- List → VList: the tags field's Value payload (the row is fully
    schema-typed — the strings ride along unopened, guest-legal).
    `@[guest_std]`: the guest-mark registry — the backend's manifest
    fold compiles every marked decl (no hand-list). -/
@[guest_std]
def toVList : List String → SchemaLang.VList .string
  | [] => .nil
  | s :: ss => .cons (.string s) (toVList ss)

/-- The record's values, in schema order — the row evalV consumes.
    `@[guest_std]`: the guest-mark registry — the backend's manifest
    fold compiles every marked decl (no hand-list). -/
@[guest_std]
def userRow (u : User) : SchemaLang.RowVals userSchema :=
  .cons (.u64 u.id)
    (.cons (.string u.name)
      (.cons (.string u.email)
        (.cons (.list (toVList u.tags)) .nil)))

-- The FIRST VALIDATOR (the record-PARAM story): a fn taking a record
-- IN. The canonical ABI hands the guest the record FLAT (7 core
-- params); the adapter reconstructs the guest User object; the impl
-- reads ONLY the id scalar (the guest-legal check: no string ops, no
-- host capabilities). The differential duel: the valid rows (id ≥ 1)
-- → 1, the INVALID row (id = 0) → 0 — the negative row is the point.
@[guest_std, schema_fn, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def userValid (u : User) : Bool :=
  SchemaLang.validates userCheck (userRow u)

/-- The u64 COUNT of a string list. Guest-legal length: core's
    `List.length` returns Nat — GMP, banned in the guest; the counter
    rides the raw u64 scalars (`sumList`'s recursion shape — the
    backend's proven list-walk target). -/
@[guest_std, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def listLenU64 : List String → UInt64
  | [] => 0
  | _ :: t => listLenU64 t + 1

-- The SECOND record validator (the pattern's RANGE: the id scalar +
-- the name STRING via the VExpr `strlen` NODE — the compiled lane is
-- wired: the raw evaluator reads the string's length through the
-- runtime `$string_len` primitive). The body = the REGISTERED form:
-- `validates` over the schema-indexed check + the tags LIST gate as
-- the hand `listLenU64` walk (the VExpr family has no list-length
-- node yet — that gate joins when the node lands; the duel cannot
-- express the empty list anyway, see GenMain's user-complete rows).
-- The `&&` shape: the conjunction compiles as the Bool cases the
-- backend already emits.
@[guest_std, schema_fn, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def userComplete (u : User) : Bool :=
  SchemaLang.validates userCompleteCheck (userRow u)
    && listLenU64 u.tags > 0

-- The VARIANT-PARAM validator (the first variant CROSSING the boundary
-- as a validator's subject): the canonical ABI flattens the variant to
-- [i32 discr, i64 joined-payload] and the adapter RE-BOXES it (the
-- watch-orders variantBox shape); the impl's match IS the payload
-- access — the tag case selects the arm, the invalid-item arm's `id`
-- rides the box's payload slot @8.
--
-- Semantics (CHOSEN + documented): a valid error REPORT is one the
-- host can act on.
-- - `emptyCart` → FALSE: an empty cart names nothing actionable — the
--   validator refuses the no-information case (the negative control's
--   discr row).
-- - `invalidItem id` → id > 0: 0 is the absent-item sentinel
--   (mirroring getUser's sentinel id).
-- - `insufficientFunds` → true, and the f64 payload is deliberately
--   UNREAD: the canonical-ABI's f64→i64 flat join + the guest's
--   boxed-Float repr make the amount's guest-side read the v1
--   exclusion (a Float compare has no binop in the backend). An
--   insufficient-funds report is always actionable, so the arm is the
--   constant true — NO Float op compiles.
@[guest_std, schema_fn, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def orderErrorValid (e : OrderError) : Bool :=
  match e with
  | .emptyCart => false
  | .invalidItem id => id > 0
  | .insufficientFunds _ => true

-- DERIVED at elaboration from the registry (`SchemaLang.Meta.derive_variant_cases`):
-- the Demo `@[schema] inductive OrderError`'s cases, kebab-cased — the
-- emitted spelling. Not a hand mirror: renaming a ctor in Demo.lean
-- fails THIS module's elaboration (the derivation throws, did-you-mean
-- included); the list cannot drift because it is not written.
derive_variant_cases orderErrorCases from OrderError

/-- The variant-row builder: the adapter's re-box — the canonical ABI's
    [i32 discr, i64 joined-payload] flattening turned back into the
    typed row (the fired tag's position + the payload at it). The f64
    payload rides the box unopened (the hand body's stance). SPEC
    LEVEL ONLY — no `@[guest_std]`: it constructs `Value` boxes the
    guest cannot compile (the `evalV` reason); the hand `match` above
    stays the compiled authority. -/
def orderErrorRow : OrderError → SchemaLang.VRow orderErrorCases
  | .emptyCart => .here ()
  | .invalidItem id => .there (.here (.u64 id))
  | .insufficientFunds amount => .there (.there (.here (.f64 amount)))

/-- The SPEC form of `orderErrorValid` (the VCase family —
    SchemaLang.Validate's Phase 3): valid = NOT empty-cart, AND NOT
    (invalid-item with a 0 payload). The insufficient-funds arm is the
    constant true (both atoms false on its row — the payload stays
    UNREAD, the f64-join exclusion). NOT `@[guest_std]` — the
    COMPILED-LANE DECISION (the strlen precedent): a raw variant
    evaluator needs the discr + joined-payload scalar level the
    backend does not emit, so this rides `evalCase` only and the hand
    body above stays the compiled authority; the schema-lang tests pin
    this EXACT shape's eval on the mirrored case list
    (`valOrderErrorCases`) and the differential duel rows are the
    end-to-end authority. -/
def orderErrorSpecValid : SchemaLang.VCase orderErrorCases .bool :=
  .and
    (.not (.isCase "empty-cart"))
    (.not
      (.and
        (.isCase "invalid-item")
        (.not (.gt (.payload "invalid-item") (.litU 0)))))

end GuestImpl
