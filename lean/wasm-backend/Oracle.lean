/-
# Oracle — the wasm differential gate's Lean-side row universe

THE single source of the oracle's rows (the generated-script era is
over): the emission loop is `OracleMain.lean` (`lake exe oracle`;
`just wasm-compile` pipes it to `target/diff.json`). The extraction makes
the gate's Lean side testable: `Tests/Main.lean` now ships a
`TestKit.DiffSpec` proving the oracle REJECTS a sabotaged row (unknown
fn, arity drift) — the corruption-negative discipline the smoke
previously enforced only Rust-side (steel-host's flipped-instruction
sabotage row).

BYTE-COMPAT INVARIANT: `rows`/`resultOf`/`jsonRow` are verbatim lifts
of the emitter's surface (the emitter's supplements — the two LCG
sweeps, the u64 boundary sweep, the validator rows — are lifted here
too, so this module's row surface IS the emitter's; `resolve` is new
(structured errors for the DiffSpec) and never changes manifest bytes).
New rows APPEND ONLY — the existing rows' bytes are the byte-tie
invariant, never spliced.

W6.3 (phase 1) added, bytes unchanged: the `Probe`/`ProbeBatch`
structure (the row universe's context-sharing made explicit — every
batch names the ONE demo-component context its probes are fired at),
and the `CompareMode`/`ErrorId`/`Outcome` comparison contract
(`resolve` now routes through `resolveOutcome` — same messages, plus
error IDENTITY as a ctor). Verified: oracle manifest sha256
b1e13749f5e25f27317f0c7b6ada65b2d6567638efd6aa59f9c6ed5e553c5d18
before AND after.

PHASE-2 NOTE (W6.3, NOT YET LANDED): the target oracle shape emits
VERDICTS, not expecteds — the replay request carries the row + its
batch context, Lean answers a judgment through `CompareMode.compare`,
and error-equivalence modes ride the wire per row (`modeOf` becomes a
real column, `.ignore`/`.identity` rows become expressible). BLOCKED
on the host replay contract: steel-host's wasm_diff still PULLS
target/diff.json and string-compares host-side; until it SENDS rows
and CONSUMES verdicts, the manifest format is byte-frozen (the hash
above) and the mode/batch structure binds Lean-side + as a Rust-side
mirror (`CompareMode` in wasm_diff.rs) only.

Ownership: this module owns the row universe + row resolution; the
script owns only the emission loop. Deliberately excluded: the component
replay itself (steel-host, Rust-side), and `just wasm-compile`'s
wasm-toolchain half (the integrating engineer runs it).
-/

import Lean
import DemoFn
import GuestlangStd
import Plausible
import TestKit
import LintKit.PackageNamespace

open TestKit

-- The oracle row surface (`rows`/`resolve`/`jsonRow`/…) is keyed by the
-- demo world's WIT export names — deliberately unprefixed.
set_option linter.guestlang.packageNamespace false -- because these decl names key the wasm differential oracle to the WIT export contract, not library API

/-- The demo inputs (deterministic — the manifest is reproducible). -/
def u64s : List UInt64 :=
  ((List.range 20).map (fun i => (i * 7 + 3) % 100)).map (fun n => n.toUInt64)

/-- One probe: a single cheap replay (fn + flat arg strings) fired at a
    shared context. The wire row IS this pair — byte-frozen. -/
abbrev Probe := String × List String

/-- A probe batch (cedar-drt's amortized probes, W6.3): ONE expensive
    context (the instantiated demo component the Rust replay builds
    once) × N cheap probes fired at it. Every batch below names the
    SAME context — the u64s grid, both LCG sweeps, the boundary sweep
    and the Gen supplement all replay against the one demo-component
    instance. The batching is the phase-2 host contract's shape (the
    replay amortizes instantiation over the batch); today it is
    structure-only — the emitted row bytes are unchanged. -/
structure ProbeBatch where
  /-- The context the batch's probes share (documentary until phase 2
      puts it on the wire). -/
  context : String
  /-- The probes fired at the context. -/
  probes : List Probe

/-- The grid batch: the fixed u64s input grid × the demo fns, plus the
    hand-pinned validator duels. -/
def gridBatch : ProbeBatch where
  context := "demo-component"
  probes :=
  (u64s.map fun a => ("double", [toString a]))
  ++ (u64s.map fun a => ("is-big", [toString a]))
  ++ (u64s.map fun a => ("adder", [toString a, toString (a + 3)]))
  ++ (u64s.map fun a => ("double-area", [toString a]))
  ++ (u64s.map fun a => ("run-paps", [toString a]))
  ++ ((List.range 20).map fun i =>
    ("total", [toString (i * 3), toString (i + 1), toString (i * 2)]))
  ++ (u64s.map fun a => ("pick", [if a % 2 == 0 then "1" else "0", toString a, toString (a + 1)]))
  ++ (u64s.map fun a => ("str-len-demo", [toString a]))
  ++ (u64s.map fun a => ("greet", [toString a]))
  ++ (u64s.map fun a => ("get-user", [toString a]))
  ++ (u64s.map fun a => ("watch-counts", [toString a]))
  ++ (u64s.map fun a => ("watch-users", [toString a]))
  -- the VALIDATOR's duel: the row args = the record's FIELD VALUES FLAT
  -- (id, name, email, tags comma-joined) — the wasm_diff arg-builder
  -- constructs the Val::Record from them. THE INVALID ROW (id = 0) is
  -- the point: the validator must REFUSE it (the negative control —
  -- Lean says false, the wasm must agree).
  ++ [("user-valid", ["0", "zero", "0@g.dev", "a"])]
  ++ (u64s.map fun a => ("user-valid", [toString a, "first", "1@g.dev", "a"]))
  -- the VARIANT validator's duel: the args = [discr, payload] — the
  -- canonical-ABI flat form (the discr = the WIT case order:
  -- empty-cart=0, invalid-item=1, insufficient-funds=2; the payload
  -- rides the joined i64 slot — u64 raw, f64 bits). The empty-cart row
  -- is the documented NEGATIVE (the validator refuses the
  -- no-information report); invalid-item(0) is the sentinel negative;
  -- the f64 arm's payload is unread (GuestImpl.orderErrorValid) — the
  -- row pins the CONSTANT arm, not a Float compare.
  ++ [("order-error-valid", ["0", "0"])]
  ++ [("order-error-valid", ["1", "0"])]
  ++ [("order-error-valid", ["1", "5"])]
  ++ [("order-error-valid", ["2", "1.5"])]
  -- the RICHER record validator's duel: the same flat-record arg form
  -- as user-valid — each gate (id, strlen, tags-count) gets its
  -- negative; the map rows are the positives. (The empty-LIST gate has
  -- no row: the flat-string convention cannot express the empty list —
  -- "" splits to [""], one element, BOTH sides agree.)
  ++ [("user-complete", ["0", "zero", "0@g.dev", "a"])]
  ++ [("user-complete", ["1", "ab", "1@g.dev", "a"])]
  ++ (u64s.map fun a => ("user-complete", [toString a, "first", "1@g.dev", "a,b"]))

/-- The manifest rows: (fn, args) pairs the differential gate replays
    (the grid batch's probes — the byte-tie surface, unchanged). -/
def rows : List Probe := gridBatch.probes

-- THE FUZZ SUPPLEMENT: a deterministic LCG drives RANDOM scalar rows —
-- the authority stays LEAN (the expected = resultOf's evals on the
-- random args); the engines must agree on inputs the fixed grid never
-- visits (the overflow wraps: UInt64 arithmetic is wrapping — the
-- random args cross the wrap boundary the grid avoids).
def fuzzRows : Nat → UInt64 → List (String × List String)
  | 0, _ => []
  | n+1, seed =>
      let s1 := lcg seed
      let s2 := lcg s1
      let s3 := lcg s2
      let s4 := lcg s3
      let row := match s1 % 7 with
        | 0 => ("double", [toString (s2 % 1000)])
        | 1 => ("is-big", [toString (s2 % 1000)])
        | 2 => ("adder", [toString (s2 % 1000), toString (s3 % 1000)])
        | 3 => ("double-area", [toString (s2 % 100)])
        | 4 => ("run-paps", [toString (s2 % 1000)])
        | 5 => ("total", [toString (s2 % 100), toString (s3 % 100), toString (s4 % 100)])
        | _ => ("pick", [if s2 % 2 == 0 then "1" else "0", toString (s3 % 100), toString (s4 % 100)])
      row :: fuzzRows n s4

/-- The fuzz supplement as a batch (same shared context). -/
def fuzzBatch (n : Nat) (seed : UInt64) : ProbeBatch :=
  ⟨"demo-component", fuzzRows n seed⟩

-- THE BOUNDARY SWEEP: the u64 fns at 0, 1, 2, 2^k and 2^k±1 (k = 31,
-- 32, 63) — the grid's mod-1000 and the LCG's small residues never
-- visit the wrap/limit surface. The adder/pick args are COMPLEMENTS
-- (a + (2^64-1-a) = 2^64-1; a=0 pins max, wrap = 0 at 2^64-1+1).
def bounds : List UInt64 :=
  [0, 1, 2, 2147483648, 4294967295, 4294967296, 9223372036854775807,
   9223372036854775808, 18446744073709551615]

def boundaryRows : List (String × List String) :=
  let maxU : UInt64 := 18446744073709551615
  (bounds.map fun a => ("double", [toString a]))
  ++ (bounds.map fun a => ("is-big", [toString a]))
  ++ (bounds.map fun a => ("adder", [toString a, toString (maxU - a)]))
  ++ (bounds.map fun a => ("double-area", [toString a]))
  ++ (bounds.map fun a => ("run-paps", [toString a]))
  ++ (bounds.map fun a => ("str-len-demo", [toString a]))
  ++ (bounds.map fun a =>
    ("pick", [if a % 2 == 0 then "1" else "0", toString a, toString (maxU - a)]))
  ++ (bounds.map fun a => ("total", [toString a, toString a, toString a]))

/-- The boundary sweep as a batch (same shared context). -/
def boundaryBatch : ProbeBatch :=
  ⟨"demo-component", boundaryRows⟩

-- THE SWEEP SUPPLEMENT: a second LCG (splitmix-style — seed, then two
-- advances per row) over the fns the first fuzz skips (str-len-demo,
-- watch-counts) plus the scalar surface — 120 rows, seed = a CONSTANT
-- (same seed → same manifest, that's what makes it a gate).
def sweepRows : Nat → UInt64 → List (String × List String)
  | 0, _ => []
  | n+1, seed =>
      let s1 := lcg seed
      let s2 := lcg s1
      let s3 := lcg s2
      let row := match s1 % 9 with
        | 0 => ("double", [toString (s2 % 1000)])
        | 1 => ("is-big", [toString (s2 % 1000)])
        | 2 => ("adder", [toString (s2 % 1000), toString (s3 % 1000)])
        | 3 => ("double-area", [toString (s2 % 100)])
        | 4 => ("run-paps", [toString (s2 % 1000)])
        | 5 => ("total", [toString (s2 % 100), toString (s3 % 100), toString (s2 % 1000)])
        | 6 => ("pick", [if s2 % 2 == 0 then "1" else "0", toString (s3 % 100), toString (s2 % 1000)])
        | 7 => ("str-len-demo", [toString (s2 % 1000)])
        | _ => ("watch-counts", [toString (s2 % 1000)])
      row :: sweepRows n s3

/-- The sweep supplement as a batch (same shared context). -/
def sweepBatch (n : Nat) (seed : UInt64) : ProbeBatch :=
  ⟨"demo-component", sweepRows n seed⟩

-- ── THE GEN SUPPLEMENT (Plausible) ───────────────────────────────────
-- Edge rows from Plausible `Gen` combinators: the nesting/shape edges
-- the grid, the LCG sweeps and the boundary sweep never visit —
-- option-of-option id sentinels, the empty tag INSIDE a non-empty list
-- ("a,,b" — the splitOn edge), strings at the 0/1/long length
-- boundaries, get-user/greet at their sentinels (0/1/max — neither
-- sweep visits greet, and get-user only rides the grid's mod-100
-- values). DETERMINISM: every draw runs through `runGenPure` (fixed
-- seed AND size — no IO, no global stdGenRef) and the driver advances
-- the seed one step per row; same seed → same manifest, which is what
-- makes it a gate. The generator picks only the fn/arg MIX; the
-- expected values stay Lean's own evals (resultOf — the authority
-- never moved). The driver filters against `preGen` (the pinned
-- universe below): no generated row duplicates an existing one.

open Plausible

/-- Deterministic pure `Gen` run (fixed seed + size — no IO; the
    schema-lang Tests' `runGenPure` pattern). -/
def runGenPure (g : Gen α) (seed : Nat) (size : Nat) : Except Plausible.GenError α :=
  (ReaderT.run (StateT.run g (ULift.up (mkStdGen seed))) ⟨size⟩).map (·.1)

/-- The id SENTINEL generator: option-of-option — the outer none is
    get-user's absent record (the `none` arm), the inner none is the
    id-0 sentinel the validators refuse. The flat surface renders both
    "0"; the two NESTS are distinct reasons a "0" row exists. The
    some (some _) arms ride the u64 boundaries the grid avoids. -/
def genNestedId : Gen (Option (Option UInt64)) := do
  let n ← Gen.chooseNat
  match n % 6 with
  | 0 => pure none
  | 1 => pure (some none)
  | 2 => pure (some (some 1))
  | 3 => pure (some (some 9223372036854775808))
  | 4 => pure (some (some 18446744073709551615))
  | _ => pure (some (some (((n / 6 + 1) * 7919 : Nat).toUInt64)))

/-- Flat render (the arg string the manifest carries). -/
def renderId : Option (Option UInt64) → String
  | none => "0"
  | some none => "0"
  | some (some v) => toString v

/-- The u64 leaf: the boundary weights (0, 1, 2^32, 2^63, max) plus a
    sized off-grid value (the 7919 multiples land between the grid's
    mod-100 and the fuzz's mod-1000 arms). -/
def genU64 : Gen String := do
  let n ← Gen.chooseNat
  match n % 6 with
  | 0 => pure "0"
  | 1 => pure "1"
  | 2 => pure "4294967296"
  | 3 => pure "9223372036854775808"
  | 4 => pure "18446744073709551615"
  | _ => pure (toString ((n / 6 + 1) * 7919))

/-- The length-boundary string: 0, 1, 3, 4 (straddling the validator's
    strlen > 3 gate — the 3/4 pair is the documented boundary flip) or
    a sized long run (the chunked-ABI edge the grid's 5-char names
    never visit). -/
def genLenStr : Gen String := do
  let n ← Gen.chooseNat
  let len : Nat :=
    match n % 5 with
    | 0 => 0
    | 1 => 1
    | 2 => 3
    | 3 => 4
    | _ => 40 + n
  pure (String.ofList (List.replicate len 'a'))

/-- The tags generator, at FULL nesting: option (list (option string)).
    The outer none = the flat convention's floor ("" → [""], one empty
    element — the documented unexpressible-empty-list limit), the inner
    none = the empty tag INSIDE a non-empty list ("a,,b" — the splitOn
    edge no existing row emits), the leaves are short runs. -/
def genTags : Gen (Option (List (Option String))) := do
  let n ← Gen.chooseNat
  if n % 4 == 0 then pure none
  else do
    let elems ← (List.range (n % 4)).mapM (fun _ => do
      let m ← Gen.chooseNat
      pure (if m % 3 == 0 then none
            else some (String.ofList (List.replicate (m % 4 + 1) 'a'))))
    pure (some elems)

/-- Flat render (the comma-join the arg-builder splits on). -/
def renderTags : Option (List (Option String)) → String
  | none => ""
  | some elems => String.intercalate "," (elems.map fun
    | none => ""
    | some s => s)

/-- The EDGE row generator: the fn arm picked by the draw, the args by
    the nested leaf generators. Total (every arm terminates, no throw)
    — the driver's Except is the Gen type's, never hit. NOT in the
    arm mix: double/is-big/double-area/run-paps/str-len-demo (the
    boundary sweep already pins those fns at 0/1/2^k/max). -/
def genEdgeRow : Gen (String × List String) := do
  let n ← Gen.chooseNat
  match n % 8 with
  | 0 => do
    let i ← genNestedId
    let name ← genLenStr
    let t ← genTags
    pure ("user-valid", [renderId i, name, "u@g.dev", renderTags t])
  | 1 => do
    let i ← genNestedId
    let name ← genLenStr
    let t ← genTags
    pure ("user-complete", [renderId i, name, "u@g.dev", renderTags t])
  | 2 => do
    let d ← Gen.elements ["0", "1", "2"] (by decide)
    let p ← genU64
    pure ("order-error-valid", [d, p])
  | 3 => pure ("get-user", [renderId (← genNestedId)])
  | 4 => pure ("greet", [renderId (← genNestedId)])
  | 5 => do
    let a ← genU64
    let b ← genU64
    pure ("adder", [a, b])
  | 6 => do
    let a ← genU64
    let b ← genU64
    let c ← genU64
    pure ("total", [a, b, c])
  | _ => do
    let b ← Gen.elements ["0", "1"] (by decide)
    let a ← genU64
    let x ← genU64
    pure ("pick", [b, a, x])

/-- The pinned batches BEFORE the Gen supplement — one context, four
    probe batches (the amortized structure: the replay instantiates
    once, fires all four). -/
def preGenBatches : List ProbeBatch :=
  [gridBatch, fuzzBatch 200 0x5EED, boundaryBatch, sweepBatch 120 0xA11CE]

/-- The pinned universe BEFORE the Gen supplement — the filter's
    reference (a generated row equal to one of these is dropped, never
    duplicated). -/
def preGen : List Probe :=
  preGenBatches.flatMap (·.probes)

/-- The Gen driver: `n` draws, each at seed `seed + k`, kept if fresh
    (not already in `acc` or the pinned universe). The count of KEPT
    rows is therefore draw-dependent — the SEED is the contract, not
    the count. -/
def genRowsInto (acc : List (String × List String)) :
    Nat → Nat → List (String × List String)
  | 0, _ => acc
  | n+1, seed =>
    let acc :=
      match runGenPure genEdgeRow seed 40 with
      | .ok row => if acc.contains row || preGen.contains row then acc else row :: acc
      | .error _ => acc
    genRowsInto acc n (seed + 1)

/-- The Gen supplement (the emitter appends this — appended, never
    spliced). -/
def genRows (n seed : Nat) : List Probe :=
  (genRowsInto [] n seed).reverse

/-- The Gen supplement as a batch (same shared context). -/
def genBatch (n seed : Nat) : ProbeBatch :=
  ⟨"demo-component", genRows n seed⟩

/-- The manifest's full replay list — the emitter's row universe, the
    Gen supplement's batch appended last. -/
def rowUniverse : List Probe :=
  (preGenBatches ++ [genBatch 130 0xBEA57]).flatMap (·.probes)

/-- The expected-result fold (Lean's semantics is the authority). "?" is
    unreachable for well-formed rows — `resolve` guards fn/arity first. -/
def resultOf (fn : String) (args : List String) : String :=
  match fn, args with
  | "double", [a] => toString (double a.toNat!.toUInt64)
  | "is-big", [a] => if isBig a.toNat!.toUInt64 then "1" else "0"
  | "adder", [a, b] => toString (adder a.toNat!.toUInt64 b.toNat!.toUInt64)
  | "double-area", [a] => toString (doubleArea a.toNat!.toUInt64)
  | "run-paps", [a] => toString (runPaps a.toNat!.toUInt64)
  | "total", [a, b, c] => toString (total a.toNat!.toUInt64 b.toNat!.toUInt64 c.toNat!.toUInt64)
  | "pick", [b, a, x] => toString (pick (b == "1") a.toNat!.toUInt64 x.toNat!.toUInt64)
  | "str-len-demo", [a] => toString (GuestImpl.strLenDemo a.toNat!.toUInt64)
  | "greet", [a] => GuestImpl.greet a.toNat!.toUInt64
  | "get-user", [a] => match GuestImpl.getUser a.toNat!.toUInt64 with
    | none => "none"
    | some u =>
      let tagS := String.intercalate "," (u.tags.map (fun t => t))
      s!"some(\{ id={u.id}, name={u.name}, email={u.email}, tags=({tagS}) })"
  -- the stream's expected = the COLLECTED list (the host reads the
  -- stream to completion; the ser form = the list's)
  | "watch-counts", [_a] => "(42,43)"
  -- the validator: the args = the FLAT field values (see the rows);
  -- the bool result = the ser convention (1/0 — ser_val's Val::Bool form)
  | "user-valid", [id, name, email, tags] =>
    if (GuestImpl.userValid { id := id.toNat!.toUInt64, name := name, email := email, tags := tags.splitOn "," }) then "1" else "0"
  -- the variant validator: the discr → the Lean ctor; the payload only
  -- READ for invalid-item (the f64 arm ignores it — see the impl)
  | "order-error-valid", [d, p] =>
    let e : OrderError :=
      match d with
      | "0" => .emptyCart
      | "1" => .invalidItem p.toNat!.toUInt64
      | _ => .insufficientFunds 1.5
    if GuestImpl.orderErrorValid e then "1" else "0"
  -- the richer record validator: the same flat-record args as user-valid
  | "user-complete", [id, name, email, tags] =>
    if (GuestImpl.userComplete { id := id.toNat!.toUInt64, name := name, email := email, tags := tags.splitOn "," }) then "1" else "0"
  | "watch-users", [_a] =>
    -- the ser_val's forms: the list = the comma-NO-space joins; the
    -- record = "{ k=v, ... }" with the comma-space joins
    let parts := (GuestImpl.watchUsers 0).map fun u =>
      let tagS := String.intercalate "," (u.tags.map (fun t => t))
      s!"\{ id={u.id}, name={u.name}, email={u.email}, tags=({tagS}) }"
    let ser := String.intercalate "," parts
    s!"({ser})"
  | _, _ => "?"

/-- The manifest's fn surface with arities (must agree with `resultOf`'s
    patterns — the DiffSpec's arity corruption pins this). -/
def arityOf : String → Option Nat
  | "double" | "is-big" | "double-area" | "run-paps"
  | "str-len-demo" | "greet" | "get-user"
  | "watch-counts" | "watch-users" => some 1
  | "adder" | "order-error-valid" => some 2
  | "total" | "pick" => some 3
  | "user-valid" | "user-complete" => some 4
  | _ => none

-- ── W6.3: error-equivalence modes + structured resolution ──────────
-- The comparison contract (cedar-drt's ErrorComparisonMode): errors
-- compare by IDENTITY (a ctor), never by rendered strings. Phase 1
-- binds the mode at `modeOf` + `CompareMode.compare`; the wire stays
-- byte-frozen (see the header's PHASE-2 NOTE).

/-- How a row's outcome is compared against the replay. -/
inductive CompareMode where
  /-- Errors waive: an error on either side passes (known-divergence
      waivers; both-sides-error = pass). -/
  | ignore
  /-- Compare error IDENTITY (the ctor) only — payloads never read,
      for errors OR values. -/
  | identity
  /-- Compare everything: identity AND payload, byte-for-byte
      (today's behavior — every row in the current universe). -/
  | full
deriving BEq, Repr

/-- The error identity an outcome can carry. Resolution failures are
    Lean-side (`resolveOutcome`); `trap` is the REPLAY side's only
    identity today (the Rust mirror — a wasmtime trap carries no
    payload the oracle may read). -/
inductive ErrorId where
  | unknownFn | arityDrift | trap
deriving BEq, Repr

/-- The identity's display form — the CTOR name, so error messages
    derived from it name the identity (the corruption pins match on
    this, never on a free-form payload). -/
instance : ToString ErrorId where
  toString
    | .unknownFn => "unknownFn"
    | .arityDrift => "arityDrift"
    | .trap => "trap"

/-- One side of a comparison: a value (rendered payload) or an error
    (identity + payload — the payload read by `.full` only). -/
structure Outcome where
  /-- The error identity (`none` = a value outcome). -/
  error : Option ErrorId
  /-- The rendered payload: the value's ser form, or the error's
      message. -/
  payload : String

/-- The mode's truth table (the Rust replay's `compare` mirrors this
    arm-for-arm; Tests pin every arm). -/
def CompareMode.compare (mode : CompareMode) (expected got : Outcome) : Bool :=
  match mode, expected.error, got.error with
  | .ignore, some _, _ => true
  | .ignore, _, some _ => true
  | .ignore, none, none => expected.payload == got.payload
  | .identity, some e, some f => e == f
  | .identity, none, none => true
  | .identity, _, _ => false
  | .full, some e, some f => e == f && expected.payload == got.payload
  | .full, none, none => expected.payload == got.payload
  | .full, _, _ => false

/-- The per-row mode binding. Every fn in today's universe is `.full`:
    the wire carries expected VALUES only — there are no error rows to
    waive or identity-compare yet (phase 2 makes this a real column). -/
def modeOf (_ : String) : CompareMode := .full

/-- Structured row resolution: unknown fn or arity drift is an error
    carrying its IDENTITY as a ctor plus the row-context message (the
    gate's corruption negatives pin both — by ctor, not by string). -/
def resolveOutcome (fn : String) (args : List String) : Outcome :=
  match arityOf fn with
  | none => { error := some .unknownFn, payload := s!"oracle row: unknown fn '{fn}'" }
  | some n =>
    if args.length != n then
      { error := some .arityDrift
      , payload := s!"oracle row: '{fn}' expects {n} args, got {args.length}" }
    else { error := none, payload := resultOf fn args }

/-- The string-surface resolver (the DiffSpec's original contract —
    byte-identical messages, now routed through `resolveOutcome`). -/
def resolve (fn : String) (args : List String) : Except String String :=
  let o := resolveOutcome fn args
  match o.error with
  | none => .ok o.payload
  | some _ => .error o.payload

/-- One manifest row as JSON (values via Lean.Json for escaping; the
    skeleton keeps the byte format — `mkObj` sorts keys, forbidden). -/
def jsonRow (fn : String) (args : List String) (expected : String) : String :=
  "{" ++ "\"fn\": " ++ (Lean.Json.str fn).compress ++ ", \"args\": [" ++
    String.intercalate "," (args.map fun a => (Lean.Json.str a).compress) ++
    "], \"expected\": " ++ (Lean.Json.str expected).compress ++ "}"
