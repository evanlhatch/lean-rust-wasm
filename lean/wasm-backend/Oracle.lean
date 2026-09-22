/-
# Oracle — the wasm differential gate's Lean-side row universe

THE single source of the oracle's rows (the generated-script era is
over): the emission loop is `OracleMain.lean` (`lake exe oracle`;
`just wasm-compile` pipes it to `artifact/diff.json`). The extraction makes
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

W9.6 (the decode lane) — the row universe GREW legitimately (the
byte-tie's documented delta): the five witness fixtures appended to
the grid batch (valid → accepted; tampered claim / tampered proof /
exhausted fuel / sabotaged bytes → refused BY THE GUEST), the
`verify-witness` sig + features rows, and the interpreted `resultOf`
arm (the same `decWitness?` + `checkWitness` the guest compiles — the
duel pins the two backends agree). The existing rows' bytes are
unchanged (append-only, the header's rule); the manifest hash above
covers the pre-W9.6 universe and is superseded by the regenerated
artifact/diff.json (`just wasm-diff-check` = the tie).

W9.x (the witness DIFFERENTIAL batch — the fuzz-gap audit's gap #1):
the row universe grew again, append-only: `witnessBatch` (33 rows,
seed 0x9EED7A11, appended AFTER the Gen supplement) sweeps the
WProp/WProof ctor space the five fixtures never tried — eqU AND gt
claims, valid + chain claims, byEval/byValidEval/steps proofs,
strlenCol + col refs, nested and/not, fuel-0, multi-label, and two
byte-tamper families (XOR flip, truncation). Expected = the
interpreted checker's verdict, unchanged authority. Tests pin the
verdict mix (14 accept / 19 refuse / 4 decode-none) as the
pinned-seed contract. Manifest delta: 779 → 812 rows, sha256
6aa479b9c15ff64867154b7cb52771c5940a9d33c6ed748ccb1bbfeecd9d5fcf →
8e15118eb4204c7db74e4101403b6a64a1473b9c7d3480893db79657e8278918.

W9.x RESOLVED (the backend repair — this header's "left red" state
superseded): the batch's predicted bug was REAL and FIXED at the
runtime/emitter, not the checked code. THREE defects, all found by the
differential duel + a WAT-level unit probe (export the internals, build
the objects, read the boxes):
1. `runtime.wat`'s `$rc_dec`: the freelist-push guard was INVERTED —
   the block returned to its class pool whenever the DECREMENTED rc
   was NONZERO (a 2→1 decrement of a shared/borrowed ref recycled a
   LIVE block) and the true 1→0 free never re-pooled. Every
   `alloc` after a shared-ref drop could alias a live object: the
   `evalWBool?` result's `some` box came back SELF-REFERENTIAL
   (payload = its own address), so every verdict compare read garbage
   — all valid/chain claims refused where the interpreted checker
   accepts. Fix: push only when the count HIT zero (`i32.eqz`).
2. The trampolines never consumed the closure: Lean's `lean_apply_N`
   decrements the closure after the call (the LCNF's `inc[ref] f`
   before a fap protects f for later uses). Without the dec, closures
   leaked (and the pass's accounting assumed the consumption).
3. The trampolines forwarded CAPTURED fields without INCing them: the
   target-wrapper decs its borrowed params, so a closure applied twice
   lost its captured field's only ref at the first application
   (use-after-free → freelist poisoning → the `alloc` fault + the
   "cannot enter component instance" wedge on the shared-instance
   gate). Fix: INC each forwarded captured field; the wrapper's dec
   consumes THAT ref, the closure keeps its own.
Repairs 2+3 together took the tampered rows from TRAP to clean
refusal. The minimal counterexample shape (a `valid` claim over a
`gt` of two lits, `byValidEval`, fuel 1) is IN the batch (rows
replayed by the isolate probe + the wasm_diff gate); the duel is
33/33 byte-agreements, every suite green. NOTE: an earlier revision
of this header quoted "minimal case" bytes
(`1,0,10,1,105,110,118,45,97,0,0,0,42,0,0,1,1`) that do NOT decode
(the payload length byte is wrong); the canonical minimal encoding is
`encWitness 1 0 ⟨"inv-a", .valid (.gt (.lit 42) (.lit 0)),
.byValidEval, 1⟩` = `1,0,14,5,105,110,118,45,97,0,0,0,42,0,0,1,1`.

W6.3 (phase 2) landed, bytes unchanged: the VERDICT layer —
`DivergenceClass`/`Divergence`/`Verdict` + `CompareMode.verdict` (the
first-divergence triple: both outcomes + the category as a CTOR +
the first payload offset), the `schemaSigs` signature table
(`arityOf` is now its lookup — same answers, pinned), the canonical
`schemaSurface` string, and the `featuresOf`/batch coverage tables.
The driver (OracleMain) gained ADDITIVE subcommands — `schema-surface`,
`coverage`, `verdict FN ARG... --observed VALUE|@trap` — the no-arg
manifest bytes are still the frozen hash above. The host side of the
debug loop is crates/oracle-runner (probe --compare verdict, explain,
all mirroring this module arm-for-arm). SCHEMA-HASH DECISION: the
manifest hash covers the manifest BYTES, so the schema hash CANNOT be
a manifest field — it lives in the verdict JSON's `schema` echo (the
surface string; consumers sha256 it) and in COVERAGE.md's header.
STILL OPEN (a later phase): the replay REQUEST carrying row + batch
context with Lean answering over the wire, and `modeOf` becoming a
real column (`.ignore`/`.identity` rows on the wire).

W6.3 follow-up, bytes unchanged: `schemaSurface`'s HOST-side consumer
landed — steel-host's `schema.rs` fails FAST on version skew at
startup, deriving the guest's surface from the component TYPE (ground
truth — the embedded-string channel was rejected: WAT can't express
custom sections, and an embedded string is a claim that can drift
from the real exports). The canonical string below is the contract;
the hash stays consumer-side (sha256 of the string).

R2 (the registry fold — resultOf's derived lane), BYTES UNCHANGED:
the finding was that `resultOf` hand-mirrored every demo fn while
`FuncSig.body` (6.5.1's declaring-constant field) sat unused — the
drift class: a new schema fn needs an oracle arm added by hand. The
repair: the SCALAR-sig arms are DERIVED at elaboration time by the
`derive_oracle_arms` command (a fold over `SchemaLang.Meta
.registeredItems` — one eval per func item whose Tys are in the
derivable surface: u64/bool params, u64/bool/string rets; the arm
CALLS the registered body — the registry row carries the WHAT, the
evaluation stays Lean's). The win pin: `scratchTriple` (registered
HERE, no arm written) resolves through the derived arm — the #guard
below the fold fails the build if the derivation breaks. The rows
whose semantics is NOT registry data stay hand-listed in
`resultOfHand` (each entry names why: the ser forms, the flat
record/variant conventions, the byte-row decode lane). `schemaSigs`
stays hand-listed too: the scratch fn must not join the SURFACE (the
Tests pin its length 16). VERIFIED: the emitted manifest is
byte-identical to the pre-fold one (sha256
8e15118eb4204c7db74e4101403b6a64a1473b9c7d3480893db79657e8278918
before AND after — the header's documented hash).

W9.6 unblocking (item 2) — `streq` intrinsic, ROWS UNCHANGED: the
backend gained the `String.decEq` lowering (`$string_eq` — one
`GuestlangStd.Intrinsic` ctor + the runtime.wat primitive + the oracle
body in StrOps.lean). The row universe here is UNCHANGED: an oracle
row replays a WORLD EXPORT (WasmGenMain's closed-world guard: every oracle
fn is a world export), and no demo export carries a string `==` — the
fns exercising `$string_eq` (the guest checker) compile only when the
W9.6 boxed-Nat decision lands and the checker decls rejoin the compile
set. The `$string_eq` duel rows ride W9.6-proper's witness fixtures
(gap 5's bytes-in wrapper export). Adding rows TODAY would also flip
the host's pinned `EXPECTED_DEMO_SURFACE` (steel-host schema.rs) and
the committed coverage matrix — the honest surface change is
W9.6-proper's, not this one.

Ownership: this module owns the row universe + row resolution; the
script owns only the emission loop. Deliberately excluded: the component
replay itself (steel-host, Rust-side), and `just wasm-compile`'s
wasm-toolchain half (the integrating engineer runs it).
-/

import Lean
import DemoFn
import GuestlangStd
import SchemaLang.Witness
import SchemaLang.WitnessCheck
import SchemaLang.Meta.Reflect -- the schema registry (the R2 fold reads it at elaboration)
import CodegenCore -- Emit.kebab: the WIT export naming the fold keys the arms by
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
  -- THE W9.6 WITNESS FIXTURES (the decode lane + checker duel): the
  -- rows' arg = the committed witness BYTES (comma-joined decimal u8s —
  -- the byte-row convention; the encoding is `Witness.encWitness 1 0`,
  -- computed by the Lean eval and PINNED here — the fixtures are
  -- constants, the oracle's authority is the resultOf eval below).
  -- valid → accepted; tampered CLAIM (43≠42), tampered PROOF (byEval
  -- 43), exhausted FUEL (0 < fuelNeed), and SABOTAGED BYTES (the label
  -- length 18→19 truncates the label — decode `none`) → all refused
  -- (the design §4 negative control: refused BY THE GUEST).
  ++ [("verify-witness", ["1,0,18,9,100,101,109,111,47,101,113,52,50,1,0,42,0,42,0,42,1"])]
  ++ [("verify-witness", ["1,0,18,9,100,101,109,111,47,101,113,52,50,1,0,42,0,43,0,42,1"])]
  ++ [("verify-witness", ["1,0,18,9,100,101,109,111,47,101,113,52,50,1,0,42,0,42,0,43,1"])]
  ++ [("verify-witness", ["1,0,18,9,100,101,109,111,47,101,113,52,50,1,0,42,0,42,0,42,0"])]
  ++ [("verify-witness", ["1,0,19,9,100,101,109,111,47,101,113,52,50,1,0,42,0,42,0,42,1"])]

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

-- ── THE WITNESS DIFFERENTIAL BATCH (the fuzz-gap audit's gap #1) ─────
-- The guest-compiled checker (`verify-witness`) was pinned at ONE
-- witness shape (an eqU claim, one label — the five fixtures above)
-- while the Lean-side checker is swept over generated witnesses: a
-- backend miscompilation of ANY untried WProp/WProof arm would have
-- been silent. This batch sweeps the ctor space: N LCG-seeded
-- witnesses (TestKit.lcg, pinned seed — failures replay
-- byte-identically), each row's arg = the witness's encoded bytes
-- (`encWitness 1 0`, the codec) and the expected = the interpreted
-- checker's verdict (resultOf's verify-witness arm: decWitness? +
-- checkWitness at the artifact's own fuel over the v1 demo's EMPTY
-- certification context — the exact shape DemoFn.verifyWitness
-- compiles). The authority never moved: expected = Lean's eval.
--
-- FAMILY MAP (row i uses family i % 11 — cycling, so the pinned count
-- 33 covers every family 3×; the VALUES ride the LCG draws):
--   0 valid + gt + byValidEval  → ACCEPT (lit-only invariant, true)
--   1 eqU + byEval              → ACCEPT (equal literals)
--   2 nested and/not            → ACCEPT (not(gt 0 v) ∧ gt v 0, v ≥ 1)
--   3 chain [] + steps []       → ACCEPT (the chain rule's empty walk —
--     the only chain shape that accepts with no log)
--   4 chain 2 steps + steps 2   → REFUSE (empty log: the offsets deref
--     none — the context-free convention the guest compiles)
--   5 strlenCol ref             → REFUSE (unresolved on the empty fields)
--   6 eqU with a col ref        → REFUSE (same, the eqU path)
--   7 wrong proof shape         → REFUSE (eqU+byValidEval /
--     valid+byEval — the LCG picks the sub-arm)
--   8 fuel 0                    → REFUSE (exhaustion IS refusal, §7.3)
--   9 TAMPERED: one XOR-flipped byte of the family-0 witness → the
--     Lean verdict pins whatever the flip yields (decode-none or a
--     semantic flip — refusal is first-class)
--   10 TAMPERED: family-1's bytes truncated one byte → decode none
--
-- Multi-label: the label supply varies the decode path's string
-- lengths (5..21 chars). The streq lowering rides the compiled closure
-- (lookupString?'s name BEq) but the pinned-empty context never
-- executes a nonempty name comparison — the duel pins the compiled
-- closure's VERDICTS, arm for arm. Non-empty chains always refuse in
-- this lane (no log on the wire); the rows still pin the guest's
-- compiled chain walk against the interpreted one.

/-- The witness batch's labels (multi-label: the decode path's string
    lengths vary — 5..21 chars). -/
def witnessLabels : List String :=
  ["inv-a", "mig-v1-v2", "step-ok", "demo/eq42", "w9-differential-batch"]

open SchemaLang.Witness in
/-- The family-`fam` witness (fam < 9 — the tamper families 9/10 build
    on families 0/1's encodings; see `witnessRowAt`). `v` is a nonzero
    u64 leaf, `s1` picks family 7's sub-arm. -/
def witnessOf (fam : Nat) (v : UInt64) (s1 : UInt64) (fuel : Nat)
    (label : String) : SchemaLang.Witness.Witness :=
  ⟨label,
   match fam with
   | 0 => .valid (.gt (.lit v) (.lit 0))
   | 1 => .eqU (.lit v) (.lit v)
   | 2 => .valid (.and (.not (.gt (.lit 0) (.lit v))) (.gt (.lit v) (.lit 0)))
   | 3 => .chain [] (.gt (.lit v) (.lit 0))
   | 4 => .chain [⟨0⟩, ⟨1⟩] (.gt (.lit v) (.lit 0))
   | 5 => .valid (.gt (.strlenCol "note") (.lit 0))
   | 6 => .eqU (.col "amount") (.lit v)
   | 7 => if (s1 % 2).toNat == 0 then .eqU (.lit v) (.lit v)
          else .valid (.gt (.lit v) (.lit 0))
   | _ => .eqU (.lit v) (.lit v),
   match fam with
   | 0 => (.byValidEval : SchemaLang.Witness.WProof)
   | 1 => (.byEval v : SchemaLang.Witness.WProof)
   | 2 => (.byValidEval : SchemaLang.Witness.WProof)
   | 3 => (.steps [] : SchemaLang.Witness.WProof)
   | 4 => (.steps [.byValidEval, .byValidEval] : SchemaLang.Witness.WProof)
   | 5 => (.byValidEval : SchemaLang.Witness.WProof)
   | 6 => (.byEval v : SchemaLang.Witness.WProof)
   | 7 => if (s1 % 2).toNat == 0 then
            (.byValidEval : SchemaLang.Witness.WProof)
          else (.byEval v : SchemaLang.Witness.WProof)
   | _ => (.byEval v : SchemaLang.Witness.WProof),
   if fam == 8 then 0 else fuel⟩

/-- One witness row: family `i % 11`, the LCG values, the arg = the
    encoded bytes comma-joined (the byte-row convention). -/
def witnessRowAt (i : Nat) (s1 s2 s3 : UInt64) : Probe :=
  let v : UInt64 := (s2 % 1000) + 1
  let fuel : Nat := (s3 % 8).toNat + 1
  let label :=
    witnessLabels[(s3 % UInt64.ofNat witnessLabels.length).toNat]?.getD "inv-a"
  let bs : List UInt8 :=
    match i % 11 with
    | 9 => -- the byte-FLIP tamper: one XORed byte of the family-0 witness
      let ok := SchemaLang.Witness.encWitness 1 0 (witnessOf 0 v s1 fuel label)
      let k := s3.toNat % ok.length
      ok.take k ++ [(ok[k]?.getD 0 ^^^ 1)] ++ ok.drop (k + 1)
    | 10 => -- the TRUNCATION tamper: family-1's bytes minus one byte
      (SchemaLang.Witness.encWitness 1 0 (witnessOf 1 v s1 fuel label)).dropLast
    | fam => SchemaLang.Witness.encWitness 1 0 (witnessOf fam v s1 fuel label)
  ("verify-witness", [String.intercalate "," (bs.map fun b => toString b.toNat)])

/-- The witness batch's rows: `n` LCG draws, each at an advanced seed,
    family = the row index mod 11 (cycling — the pinned count covers
    every family). Same seed → same rows (the fuzz sweeps' contract). -/
def witnessRows : Nat → UInt64 → List Probe
  | 0, _ => []
  | n+1, seed =>
      let s1 := lcg seed
      let s2 := lcg s1
      let s3 := lcg s2
      witnessRowAt n s1 s2 s3 :: witnessRows n s3

/-- The witness differential batch (the fuzz-gap audit's gap #1): 33
    LCG-seeded rows, 3 per ctor family (see the map at witnessRowAt).
    Seed PINNED — same seed, same bytes, failures replay
    byte-identically. -/
def witnessBatch : ProbeBatch :=
  ⟨"demo-component", witnessRows 33 0x9EED7A11⟩

/-- The manifest's full replay list — the emitter's row universe, the
    Gen supplement's batch + the witness differential batch appended
    last. -/
def rowUniverse : List Probe :=
  ((preGenBatches ++ [genBatch 130 0xBEA57, witnessBatch]).flatMap (·.probes))

/- ── R2: THE REGISTRY FOLD (resultOf's derived lane) ─────────────────
   The finding: resultOf hand-mirrored every demo fn while FuncSig.body
   (the registry's declaring-constant field, 6.5.1 — auto-filled by
   `@[schema_fn]`) sat unused. The repair: the SCALAR-sig arms are
   DERIVED from the registry at elaboration time (the fold below — the
   `derive_oracle_arms` command over `SchemaLang.Meta.registeredItems`),
   so a new
   `@[schema_fn]` demo fn joins the oracle with ZERO second site. The
   honest division of labor: the registry row carries the WHAT (name,
   Tys, the declaring constant), the evaluation stays Lean's own (the
   generated arms CALL the declared constants — no re-implementation).
   The rows whose semantics is NOT registry data stay hand-listed in
   `resultOfHand` (each with the why). The generated rows' bytes are
   pinned identical by the manifest diff (the byte-tie). -/

/-- The derived arms' flat-arg readers — the per-Ty parse the
    canonical-ABI adapter mirrors (the Layout/flatTyOf lane's oracle
    side). Byte-exact with the old hand parse (`s.toNat!.toUInt64` /
    `s == "1"`). -/
def u64Arg (args : List String) (i : Nat) : UInt64 :=
  (args.getD i "").toNat!.toUInt64

/-- See `u64Arg` (the bool convention: "1" = true — the ser form). -/
def boolArg (args : List String) (i : Nat) : Bool :=
  args.getD i "" == "1"

/-- THE WIN-PIN FIXTURE (R2): a scratch demo fn registered HERE — not in
    DemoFn — and NO resultOf arm was written for it. Its arm exists only
    because the registry fold derived it; the #guard after `resultOf`
    pins the derived verdict (build red = the derivation broke). -/
@[schema_fn]
def scratchTriple (x : UInt64) : UInt64 := x * 3 + 1

open Lean in
/-- One application step for the fold's arg chain (`foldl` helper). The
    splice rides `Unhygienic.run` — v4.33's antiquot quotations are
    monadic-only, and these run in PURE defs. -/
def armAppSplice (acc : Term) (t : Term) : Term :=
  Unhygienic.run `($acc $t)

open Lean in
/-- The fold's cons step (pure, like `armAppSplice`). -/
def armConsSplice (e acc : Term) : Term :=
  Unhygienic.run `($e :: $acc)

open Lean in
/-- The lambda wrap (the arity guard lives in the body — see the fold). -/
def armLamOf (body : Term) : Term :=
  Unhygienic.run `(fun (args : List String) => $body)

open Lean in
/-- The arm ENTRY (the WIT name keyed pair). -/
def armEntryOf (wit : String) (lam : Term) : Term :=
  Unhygienic.run `(($(quote wit), $lam))

open Lean in
/-- The per-ret render (the value → ser form; u64/bool/string — the
    derivable surface; byte-exact with the old hand arms). -/
def armRenderOf : SchemaLang.Ty → Term → Term
  | .u64, app => Unhygienic.run `(toString ($app))
  | .bool, app => Unhygienic.run `((if $app then "1" else "0"))
  | .string, app => app
  | _, _ => Unhygienic.run `((String.mk []))

open Lean in
/-- The arg-reader term per param Ty (the flat position `i`). -/
def armArgOf : SchemaLang.Ty → Nat → Term
  | .u64, i => Unhygienic.run `(u64Arg args $(quote i))
  | .bool, i => Unhygienic.run `(boolArg args $(quote i))
  | _, _ => Unhygienic.run `((String.mk []))

open Lean in
/-- The arity guard: the hand match's exact-arity patterns (drift → "?"). -/
def armGuardOf (n : Nat) (body : Term) : Term :=
  Unhygienic.run `(if args.length == $(quote n) then $body else "?")

open Lean in
/-- An ident with NO macro scope — the generated def must land at the
    ROOT name (`oracleArms`), not a hygienic alias (a quotation ident
    inside `elabCommand` is macro-scoped and would be invisible to the
    file's later commands). -/
def unscopedIdent (n : Name) : Term :=
  { raw := Syntax.ident SourceInfo.none ⟨n.toString, 0, ⟨n.toString.length⟩⟩ n [] : Term }

open Lean in
/-- The generated def's `declId` (the raw ident as a decl-id node). -/
def unscopedDeclId (n : Name) : TSyntax `Lean.Parser.Command.declId :=
  { raw := Syntax.node .none `Lean.Parser.Command.declId #[unscopedIdent n] }

open Lean Elab Command in
/-- The fold: the registry's func items → the derived `oracleArms` def
    (one eval per fn, keyed by the WIT export name — the SAME naming the
    world fold uses, `Emit.kebab body.getString!`). A fn joins iff every
    param Ty and the ret Ty are in the derivable surface (u64/bool
    params; u64/bool/string rets) — anything else (record/variant
    params, option/stream/bytes results) has no derivable arg/ser form
    and stays in `resultOfHand`. The arm's arity guard mirrors the old
    hand match's exact-arity patterns (drift → "?"). -/
def oracleArmsCmd : CommandElabM Unit := do
  let mut entries : Array Term := #[]
  for (_ln, item) in SchemaLang.Meta.registeredItems (← getEnv) do
    if let .func sig := item then
      if sig.body.isAnonymous then continue -- snapshot round trip: body reconstructed anonymous
      let wit := CodegenCore.Emit.kebab sig.body.getString!
      let mut argTerms : Array Term := #[]
      let mut derivable := true
      for i in [0:sig.params.length] do
        let ty := (sig.params[i]!).2
        match ty with
        | .u64   => argTerms := argTerms.push (armArgOf .u64 i)
        | .bool  => argTerms := argTerms.push (armArgOf .bool i)
        | _      => derivable := false
      if !derivable then continue
      let base : Term := mkIdent sig.body
      let app := argTerms.foldl armAppSplice base
      match sig.ret with
      | .u64 | .bool | .string =>
        entries := entries.push (armEntryOf wit (armLamOf (armGuardOf sig.params.length (armRenderOf sig.ret app))))
      | _ => pure ()
  let listT : Term := entries.foldr armConsSplice (mkIdent `List.nil)
  elabCommand (← `(def $(unscopedDeclId `oracleArms) : List (String × (List String → String)) := $(listT)))

open Lean Elab Command in
/-- The command wrapper: elaborating `derive_oracle_arms` re-runs the
    fold in the CURRENT environment (so a Tests module that registers
    scratch fns first can re-derive its own table). -/
syntax (name := deriveOracleArms) "derive_oracle_arms" : command

open Lean Elab Command in
@[command_elab deriveOracleArms]
def elabDeriveOracleArms : CommandElab := fun _stx => oracleArmsCmd

derive_oracle_arms

-- The HAND-LISTED remainder (R2): the rows whose semantics is NOT in
-- the registry. Each entry names why it cannot ride the fold:
--  - `get-user`/`watch-users`: the result ser form — the "some({...})"/
--    "(...)" renders are the HOST's convention (ser_val's forms), not
--    registry data (the sig's ret `option<user>`/`stream<user>` carries
--    no rendering).
--  - `watch-counts`: same ser-form reason (the stream's collected list;
--    the row pins the impl's [42, 43] through the host's render).
--  - `user-valid`/`user-complete`: the flat-RECORD arg convention — the
--    args are the record's FIELD VALUES flat (the wasm_diff arg-builder
--    reconstructs Val::Record from them), a wire convention the sig's
--    single `User` param does not carry. (`user-complete` also folds the
--    tags gate OUTSIDE the VExpr — GuestlangStd's listLenU64 body.)
--  - `order-error-valid`: the flat-VARIANT arg convention ([discr,
--    payload], the f64-payload unread) + the bool ser form.
--  - `verify-witness`: the byte-row convention (comma-joined decimal u8s)
--    + the decode lane (`decWitness?` at the artifact's own fuel over the
--    v1 empty certification context — DemoFn.verifyWitness's exact shape).
def resultOfHand (fn : String) (args : List String) : String :=
  match fn, args with
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
  -- THE W9.6 SEAM'S ORACLE (the interpreted Lean authority): decode the
  -- witness bytes (the same `decWitness?` the guest compiles), check at
  -- the artifact's own fuel over the v1 demo's empty certification
  -- context (DemoFn.verifyWitness's exact shape). The byte-row
  -- convention: comma-joined decimal u8s (see the fixture rows above).
  | "verify-witness", [bytes] =>
      let bs := (bytes.splitOn ",").map (fun s => UInt8.ofNat s.toNat!)
      match SchemaLang.Witness.decWitness? 1 bs with
      | none => "0"
      | some w =>
          if SchemaLang.WitnessCheck.checkWitness w.fuel w.claim w.proof [] .nil []
            then "1" else "0"
  | "watch-users", [_a] =>
    -- the ser_val's forms: the list = the comma-NO-space joins; the
    -- record = "{ k=v, ... }" with the comma-space joins
    let parts := (GuestImpl.watchUsers 0).map fun u =>
      let tagS := String.intercalate "," (u.tags.map (fun t => t))
      s!"\{ id={u.id}, name={u.name}, email={u.email}, tags=({tagS}) }"
    let ser := String.intercalate "," parts
    s!"({ser})"
  | _, _ => "?"

/-- The expected-result fold (Lean's semantics is the authority). "?" is
    unreachable for well-formed rows — `resolve` guards fn/arity first.
    R2: the DERIVED lane (the registry fold's `oracleArms`) answers
    first; the hand match (`resultOfHand`) is only the SER-FORM
    remainder. -/
def resultOf (fn : String) (args : List String) : String :=
  match (oracleArms.find? fun (g, _) => g == fn) with
  | some (_, eval) => eval args
  | none => resultOfHand fn args

-- THE WIN PIN (R2): `scratchTriple` was registered with NO oracle-arm
-- edit — its verdict resolves through the DERIVED arm. Build red = the
-- derivation broke.
#guard (resultOf "scratch-triple" ["5"] == "16")

/-- W6.3 phase 2: the schema surface the oracle compares against — the
    demo world's replayed-export signature table (export name × the
    manifest's FLAT-ARG arity — record/variant args ride the flat
    convention, so `user-valid` is 4). Canonical order = the row
    universe's FIRST-OCCURRENCE order (the grid batch's order) — the
    Rust replay derives the same string from any manifest by walking
    rows in order, so the schema hash compares across the boundary
    without a shared table. (`watch-orders` is exported by the world
    but not replayed — the oracle's surface is the 15 replayed fns.)
    THE single source of truth for "what's being compared": `arityOf`
    is its lookup, `schemaSurface` its canonical rendering, the
    coverage table's fn column draws from it. Behavior is
    byte-identical to the phase-1 match (Tests pin every arity + the
    unknown case). -/
def schemaSigs : List (String × Nat) :=
  [ ("double", 1), ("is-big", 1), ("adder", 2), ("double-area", 1)
  , ("run-paps", 1), ("total", 3), ("pick", 3), ("str-len-demo", 1)
  , ("greet", 1), ("get-user", 1), ("watch-counts", 1), ("watch-users", 1)
  , ("user-valid", 4), ("order-error-valid", 2), ("user-complete", 4)
  , ("verify-witness", 1) ]

/-- The manifest's fn surface with arities (must agree with `resultOf`'s
    patterns — the DiffSpec's arity corruption pins this). The lookup
    over `schemaSigs` — same answers as the phase-1 pattern match. -/
def arityOf (fn : String) : Option Nat :=
  (schemaSigs.find? (·.1 == fn)).map (·.2)

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
deriving BEq

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

/-- One manifest row as JSON, routed through the SHARED Emit builders
    (`CodegenCore.Emit.Json.obj` + `jsonStr`) — the oracle's private
    `Lean.Json` escaper is retired HERE. The two escapers agree on the
    manifest's leaves byte-for-byte (fn names, decimal args, rendered
    payloads — no quotes, backslashes, or control chars), so the
    escaping change is INVISIBLE. THE ARGS JOIN IS FROZEN (`","`, no
    space): `Json.arr` renders elements with `", "`, which would add a
    byte after every one of the manifest's 669 arg-joins — the byte-tie
    forbids that, so the args array keeps its frozen join over
    `jsonStr`-rendered elements (deviation from the arr routing,
    measured and rejected: full-arr routing drifts 669 bytes). -/
def jsonRow (fn : String) (args : List String) (expected : String) : String :=
  CodegenCore.Emit.Json.obj
    [ ("fn", CodegenCore.Emit.jsonStr fn)
    , ("args", "[" ++ String.intercalate "," (args.map CodegenCore.Emit.jsonStr) ++ "]")
    , ("expected", CodegenCore.Emit.jsonStr expected) ]

-- ── W6.3 phase 2: verdicts, not rows ───────────────────────────────
-- The comparison's answer is a JUDGMENT: pass, or the first-divergence
-- witness (observed vs expected vs the divergence CLASS — a ctor,
-- never a string). The Lean side owns the classification; the Rust
-- replay (steel-host wasm_diff, crates/oracle-runner) mirrors it
-- arm-for-arm — same discipline as the phase-1 CompareMode mirror.

/-- The divergence class. A mismatch always names ONE of these; the
    payload strings ride along as witness, never as identity. -/
inductive DivergenceClass where
  /-- Both sides values, payloads differ. -/
  | valueMismatch
  /-- Expected a value, the replay errored (today: a trap). -/
  | expectedValueGotError
  /-- Expected an error, the replay produced a value. -/
  | expectedErrorGotValue
  /-- Both sides errored, different identities. -/
  | errorIdentityMismatch
  /-- Same error identity, payloads differ (`.full` mode only —
      `.identity` never reads payloads). -/
  | errorPayloadMismatch
deriving BEq, Repr

/-- The class's display form — the CTOR name (the corruption pins match
    on this, never on a free-form payload). -/
instance : ToString DivergenceClass where
  toString
    | .valueMismatch => "valueMismatch"
    | .expectedValueGotError => "expectedValueGotError"
    | .expectedErrorGotValue => "expectedErrorGotValue"
    | .errorIdentityMismatch => "errorIdentityMismatch"
    | .errorPayloadMismatch => "errorPayloadMismatch"

/-- The first char offset at which two rendered payloads differ (`none`
    = identical). Char-wise (the ser forms are ASCII today). -/
def firstDiffAt : List Char → List Char → Nat → Option Nat
  | [], [], _ => none
  | [], _ :: _, n => some n
  | _ :: _, [], n => some n
  | a :: as, b :: bs, n => if a == b then firstDiffAt as bs (n + 1) else some n

/-- The first-divergence witness: both outcomes, the class, and the
    first payload offset where the rendered forms part (`none` when the
    payloads agree — the divergence is then in the error IDENTITY). -/
structure Divergence where
  expected : Outcome
  observed : Outcome
  category : DivergenceClass
  payloadDiffAt : Option Nat
deriving BEq

/-- The verdict: pass, or the first divergence. -/
structure Verdict where
  divergence : Option Divergence

/-- The classification of a FAILED comparison — total over the failure
    arms of every mode (`.ignore` fails only on value/value, so
    `.valueMismatch` is its only reachable class). -/
def classify (expected observed : Outcome) : DivergenceClass :=
  match expected.error, observed.error with
  | none, none => .valueMismatch
  | none, some _ => .expectedValueGotError
  | some _, none => .expectedErrorGotValue
  | some e, some f => if e == f then .errorPayloadMismatch else .errorIdentityMismatch

/-- The mode's verdict (the Bool `compare` decides pass/fail; a fail is
    classified — same truth table, richer answer). -/
def CompareMode.verdict (mode : CompareMode) (expected observed : Outcome) : Verdict :=
  if mode.compare expected observed then ⟨none⟩
  else ⟨some ⟨expected, observed, classify expected observed,
    firstDiffAt expected.payload.toList observed.payload.toList 0⟩⟩

/-- The schema surface's canonical rendering (`fn/arity`, comma-joined,
    WIT order). The SCHEMA HASH the verdicts + COVERAGE echo is sha256
    OF THIS STRING — the hashing lives in the consumers
    (oracle-runner, COVERAGE.md's header); Lean owns the canonical
    string, never the digest. -/
def schemaSurface : String :=
  String.intercalate "," (schemaSigs.map fun (f, n) => s!"{f}/{n}")

/-- One outcome as JSON (the verdict wire's leaves). -/
def jsonOutcome (o : Outcome) : String :=
  "{\"error\": " ++ (match o.error with
    | none => "null"
    | some e => (Lean.Json.str (toString e)).compress) ++
    ", \"payload\": " ++ (Lean.Json.str o.payload).compress ++ "}"

/-- The verdict as JSON — the phase-2 wire's answer shape. Additive
    echo: the schema SURFACE STRING (hash it consumer-side) so a
    verdict always names the schema it was judged under — the manifest
    hash covers the manifest bytes and stays frozen, so the echo lives
    HERE (the verdict output), not in the manifest. -/
def jsonVerdict (v : Verdict) : String :=
  match v.divergence with
  | none => "{\"ok\": true, \"schema\": " ++ (Lean.Json.str schemaSurface).compress ++ "}"
  | some d =>
    "{\"ok\": false, \"category\": " ++ (Lean.Json.str (toString d.category)).compress ++
    ", \"expected\": " ++ jsonOutcome d.expected ++
    ", \"observed\": " ++ jsonOutcome d.observed ++
    ", \"payload_diff_at\": " ++ (match d.payloadDiffAt with
      | none => "null" | some n => toString n) ++
    ", \"schema\": " ++ (Lean.Json.str schemaSurface).compress ++ "}"

-- ── W6.3 phase 2: the feature → test discipline (COVERAGE.md) ─────
-- verified-ledger's discipline: every schema feature row has a test,
-- every test names the features it exercises. The table below is the
-- single source; the driver renders COVERAGE.md from it + the row
-- universe's counts; Tests pin the discipline (every export has ≥1
-- feature, every export has ≥1 row).

/-- The schema features each export's rows exercise. The validator
    negatives are NAMED (the refusal rows are the point of those
    exports — see gridBatch's comments). -/
def featuresOf : String → List String
  | "double" => ["u64-scalar", "wrapping-arith"]
  | "is-big" => ["u64-scalar", "bool-result", "threshold-branch"]
  | "adder" => ["u64-scalar", "multi-arg", "closure-pap", "wrapping-arith"]
  | "double-area" => ["u64-scalar", "ctor-dispatch", "object-lifecycle"]
  | "pick" => ["bool-arg", "escaping-closure", "branchy-closure"]
  | "run-paps" => ["closure-pap", "closures-in-list", "multi-apply"]
  | "total" => ["u64-scalar", "multi-arg", "curried-closure", "tail-recursion"]
  | "get-user" => ["option-result", "record-result", "list-of-string", "sentinel-none"]
  | "greet" => ["string-result", "canonical-abi-return-area"]
  | "str-len-demo" => ["string-intrinsic", "runtime-dependent-branch"]
  | "watch-counts" => ["stream-u64", "async-lift"]
  | "watch-users" => ["stream-record", "async-lift"]
  | "user-valid" => ["record-arg", "validator", "negative-gate:id-zero"]
  | "user-complete" => ["record-arg", "validator", "strlen-gate", "tags-count-gate"]
  | "order-error-valid" => ["variant-arg", "validator", "negative-empty-cart", "f64-payload-arm"]
  | "verify-witness" => ["witness-decode", "guest-checker", "negative-tampered", "fuel-refusal", "witness-ctor-sweep"]
  | _ => []

/-- The batch table for COVERAGE.md: name, probe count, the feature the
    batch adds BEYOND the grid. -/
def batchTable : List (String × Nat × String) :=
  [ ("grid", gridBatch.probes.length,
     "the fixed u64s grid × all 16 exports + the pinned validator negatives + the W9.6 witness fixtures")
  , ("fuzz", (fuzzBatch 200 0x5EED).probes.length,
     "LCG-driven off-grid scalars — the engines must agree on inputs the grid never visits (wrap boundary)")
  , ("boundary", boundaryBatch.probes.length,
     "u64 limits 0/1/2/2^31/2^32±1/2^63±1/max, adder/pick complement pairs")
  , ("sweep", (sweepBatch 120 0xA11CE).probes.length,
     "second LCG over the fns the first fuzz skips (str-len-demo, watch-counts)")
  , ("gen", (genBatch 130 0xBEA57).probes.length,
     "Plausible edge rows: nested-id sentinels, the \"a,,b\" splitOn edge, length boundaries, off-grid u64 leaves")
  , ("witness", witnessBatch.probes.length,
     "the witness differential sweep (gap #1): 33 LCG-seeded witnesses across the WProp/WProof ctor space — eqU/gt claims, valid+chain claims, steps proofs, strlenCol/col refs, nested and/not, fuel-0, multi-label — plus the byte-flip and truncation tamper families; expected = the interpreted checker's verdict") ]

/-- COVERAGE.md's content (the emitter is PURE — the driver writes the
    file). GENERATED; do not hand-edit. -/
def coverageMd : String :=
  let rowCount (f : String) : Nat := (rowUniverse.filter fun (g, _) => g == f).length
  let perExport := schemaSigs.map fun (f, n) =>
    s!"| `{f}` | {n} | {rowCount f} | {String.intercalate ", " ((featuresOf f).map fun s => s!"`{s}`")} |"
  let batches := batchTable.map fun (name, count, note) =>
    s!"| `{name}` | {count} | {note} |"
  String.intercalate "\n" (
  [ "# COVERAGE — the oracle's feature → test map"
  , ""
  , "GENERATED by `lake exe oracle coverage` (lean/wasm-backend) — do not hand-edit."
  , ""
  , "Schema surface (the canonical string the verdict schema hash is sha256 of):"
  , ""
  , s!"`{schemaSurface}`"
  , ""
  , "## Per-export coverage"
  , ""
  , "| export | arity | manifest rows | schema features exercised |"
  , "| --- | --- | --- | --- |" ]
  ++ perExport ++
  [ ""
  , "## Batch coverage (one shared context, six probe batches)"
  , ""
  , "| batch | probes | adds |"
  , "| --- | --- | --- |" ]
  ++ batches ++
  [ ""
  , "## Negative controls"
  , ""
  , "- `user-valid` id=0 — the validator MUST refuse (Lean says false, the wasm must agree)"
  , "- `order-error-valid` empty-cart / invalid-item(0) — the documented variant negatives"
  , "- `user-complete` strlen(3/4) + tags-count gates — the boundary flips"
  , "- the witness fixtures' negatives (W9.6): tampered claim, tampered proof,"
  , "  exhausted fuel, sabotaged bytes — the guest checker refuses ALL"
  , "- the DiffSpec corruption rows (unknown fn, arity drift) — Lean-side rejection is observed"
  , "- steel-host's flipped-instruction sabotage — the gate demonstrably catches a wrong engine"
  , ""
  , "Discipline: every export above has ≥1 feature and ≥1 manifest row; every feature"
  , "names its export. Pinned Lean-side (Tests/Main.lean guards) — a vacuous row or an"
  , "unfeatureable export fails the build." ])
