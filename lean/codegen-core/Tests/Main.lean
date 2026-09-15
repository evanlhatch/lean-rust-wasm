/-
# CodegenCore Tests

Mangler goldens (the most common codegen bug class), header contract,
registry semantics (pure), printer spot-checks, determinism.

Run: `lake build CodegenCoreTests && .lake/build/bin/CodegenCoreTests`
-/
import CodegenCore
import TestKit
import Plausible

open CodegenCore
open CodegenCore.Emit
open TestKit
open Plausible
open Plausible.Gen

def mangleChecks : CheckResult := do
  _ ← assertEq "camel" (camel "max_health.current") "maxHealthCurrent"
  _ ← assertEq "pascal" (pascal "max_health") "MaxHealth"
  _ ← assertEq "snake" (snake "MaxHealth current") "max_health_current"
  _ ← assertEq "kebab" (kebab "maxHealth current") "max-health-current"
  _ ← assertEq "rust-kw" (rustIdent "type") "r#type"
  _ ← assertEq "rust-ok" (rustIdent "spawn_count") "spawnCount"
  .ok ()

/-! ## Mangler inverse laws (DetSpec: positives + mandatory control)

The `words` splitter lowercases everything and treats `.`/`-`/`_`/` `
as separators, so camel/snake/kebab all emit from the SAME word list:
`words (camel n) == words n` (camel re-joins with first-letter caps —
re-splitting reproduces the boundaries), `camel (snake n) == camel n`
(underscores are recognized separators), and `kebab n` is `snake n` with
all `-` for `_` (both intercalate the identical word list). Each law was
verified against `CodegenCore.Emit.words`'s fold below before being
asserted over the fixed corpus. -/
def manglerCorpus : List String :=
  ["max_health", "FooBar baz", "user.id", "total-count", "spawnCount",
   "a", "HTTP status", "mixed-hump_under-dash space"]

def manglerInverseChecks : CheckResult := do
  -- words (camel n) == words n over the corpus (n round-trippable through camel)
  for n in manglerCorpus do
    _ ← assertEq s!"words(camel {n})" (words (camel n)) (words n)
  -- camel (snake n) == camel n (snake's underscores re-split identically)
  for n in manglerCorpus do
    _ ← assertEq s!"camel(snake {n})" (camel (snake n)) (camel n)
  -- kebab n == snake n with "-" for "_" (the same word list, other glue)
  for n in manglerCorpus do
    _ ← assertEq s!"kebab {n}" (kebab n) ((snake n).replace "_" "-")
  -- capitalize pads each camel part's head; empty stays empty
  _ ← assertEq "capitalize" (capitalize "health") "Health"
  _ ← assertEq "capitalize empty" (capitalize "") ""
  -- rootRel: the "../../" prefix strips once; plain paths pass through
  _ ← assertEq "rootRel strips ../../" (rootRel "../../wit/delta.wit") "wit/delta.wit"
  _ ← assertEq "rootRel plain" (rootRel "plain/path.rs") "plain/path.rs"
  -- jsonStr: quotes and backslashes are the whole story
  _ ← assertEq "jsonStr plain" (jsonStr "/api/user") "\"/api/user\""
  _ ← assertEq "jsonStr escapes quote+backslash" (jsonStr "a\"b\\c") "\"a\\\"b\\\\c\""
  -- rustIdent: keywords r#-escaped, non-keywords camel-cased
  _ ← assertEq "rustIdent keyword" (rustIdent "type") "r#type"
  _ ← assertEq "rustIdent keyword for" (rustIdent "for") "r#for"
  _ ← assertEq "rustIdent non-keyword" (rustIdent "spawn_count") "spawnCount"
  .ok ()

/-- Deterministic suite: the mangler inverse laws (positive) + the
    sabotaged control (must FAIL — proves the positive checks bite). -/
def manglerSpec : TestKit.DetSpec :=
  { name := "mangler inverse laws"
  , check := manglerInverseChecks
  , control := assertEq "sabotage" (camel "foo_bar") "fooBarX"
  , controlName := "camel \"foo_bar\" == \"fooBarX\" (wrong suffix)" }

/-! ## Mangler property sweep (PropSpec) — pinning invariants that hold

Generator biased toward mangler-relevant characters: letters (lower + upper),
digits, and the 4 separator characters (`.`, `-`, `_`, ` `) that `words`
splits on. Length 0–12 so the edge-rich alphabet exercises all mangler paths. -/
structure Mangled where
  val : String
  deriving Repr

instance : Shrinkable Mangled where
  shrink m := (Shrinkable.shrink m.val).map (fun s => { val := s })

/-- Character pool: lowercase, uppercase, digits, and the 4 separators. -/
def manglerChar : Gen Char :=
  Gen.elements ("abcABC012._- ".toList) (by decide : 0 < ("abcABC012._- ".toList).length)

/-- Custom Arbitrary: length 0-12, each char from manglerChar. -/
instance : Arbitrary Mangled where
  arbitrary := do
    let lenGen : Gen Nat := Gen.chooseNat
    -- resize to keep len ≤ 12 so the generator stays fast but edge-rich
    let len ← Gen.resize (fun _ => 12) lenGen
    let mut cs : List Char := []
    for _ in [0:len] do
      cs := (← manglerChar) :: cs
    pure { val := String.ofList cs.reverse }

/-- Mangler invariants (all proven true by construction — see the `words` fold
    in Core.lean). Each is checked separately inside one `∀` so Plausible can
    find ANY violation regardless of which conjunct breaks.

    Invariant 1: `words s` never contains empty strings (the `if cur != ""` guard).
    Invariant 2: `snake` output has no `-`, `.`, ` ` (only `_` is the glue).
    Invariant 3: `kebab` output has no `_`, `.`, ` ` (only `-` is the glue).
    Invariant 4: `camel` output has no `_`, `-`, `.`, ` ` (no separators in output).
    Invariant 5: `pascal` output has no `_`, `-`, `.`, ` ` (same reason). -/
def manglerPropTest : TestSeq :=
  checkPlausibleIO "mangler invariants"
    (∀ (s : Mangled),
      ((words s.val).all (· ≠ "")) ∧
      ((snake s.val).all (fun c => c ≠ '-' ∧ c ≠ '.' ∧ c ≠ ' ')) ∧
      ((kebab s.val).all (fun c => c ≠ '_' ∧ c ≠ '.' ∧ c ≠ ' ')) ∧
      ((camel s.val).all (fun c => c ≠ '_' ∧ c ≠ '-' ∧ c ≠ '.' ∧ c ≠ ' ')) ∧
      ((pascal s.val).all (fun c => c ≠ '_' ∧ c ≠ '-' ∧ c ≠ '.' ∧ c ≠ ' '))
    )
    .done { numInst := 200, randomSeed := some 11 }

/-- Sabotaged negative control: "snake never contains `_`" — FALSE (snake
    joins multi-word lists with `_`). The sampler MUST catch this. -/
def manglerControl : TestSeq :=
  checkPlausibleIO "sabotage: snake never contains '_'"
    (∀ (s : Mangled), (snake s.val).all (· ≠ '_'))
    .done { numInst := 200, randomSeed := some 11 }

/-- The PropSpec pair: property passes, control is caught. -/
def manglerPropSpec : TestKit.PropSpec :=
  { name := "mangler property sweep"
  , suite := manglerPropTest
  , control := manglerControl
  , controlName := "snake output never contains '_' (must be caught)" }

def headerCheck : CheckResult :=
  let h := header .doubleSlash "codegen-core" "spec.md"
    { time := "2026-01-01T00:00Z", specSha := "abc1234", items := 3
      contentHash := 14695981039346656037 }
  -- 2 lines, dense metadata: the tool + the lean version + the time +
  -- the spec sha + the item count + the content hash + the DO-NOT-EDIT
  if h.contains "// GENERATED by codegen-core" && h.contains "DO NOT EDIT"
    && h.contains "lean-" && h.contains "2026-01-01T00:00Z"
    && h.contains "abc1234" && h.contains "3 item(s)"
    && h.contains "content hash 14695981039346656037"
  then
    -- exactly 2 header lines (the compact contract)
    let nonHeader := (h.splitOn "\n").filter (fun l => !l.isEmpty && !l.startsWith "//")
    let headerLines := (h.splitOn "\n").filter (fun l => l.startsWith "//")
    if nonHeader.isEmpty && headerLines.length == 2
    then .ok () else .error s!"header not 2 lines: {h}"
  else .error s!"header missing parts: {h}"

/-- The registry semantics, purely: append on add, concatenate on import. -/
def registryChecks : CheckResult := do
  let spec := registrySpec (α := Nat)
  let added := [1, 2, 3].foldl spec.addEntryFn ([] : List Nat)
  _ ← assertEq "addEntryFn appends" added [1, 2, 3]
  _ ← assertEq "addImportedFn concatenates in order"
    (spec.addImportedFn #[#[1], #[2, 3], #[]]) [1, 2, 3]
  -- code allocation: position-derived, prefix + running start
  let codes := allocateCodes "E" 100 ["a", "b"]
  _ ← assertEq "codes" (codes.map (·.2)) ["E100", "E101"]
  _ ← assertEq "code count" (codes.length) 2
  .ok ()

/-- Printer spot-checks on a demo module (the flatland Emit.Rust shape). -/
def emitChecks : CheckResult := do
  let items : List CodegenCore.Emit.Rust.Item :=
    [ .use_ "crate::x"
    , .struct "User" ["Clone", "Debug"]
        [{ name := "id", ty := "u64" }, { name := "name", ty := "String" }]
    , .newtype "ValidEmail" "String" ["Clone", "Debug"]
    , .fn "pub fn run() -> u32" "1"
    ]
  let out := CodegenCore.Emit.Rust.renderModule items
  -- determinism: same input, same bytes
  _ ← assertEq "deterministic" out (CodegenCore.Emit.Rust.renderModule items)
  _ ← assertEq "use" (out.contains "use crate::x;") true
  _ ← assertEq "derive line" (out.contains "#[derive(Clone, Debug)]") true
  _ ← assertEq "struct fields" (out.contains "pub id : u64,") true
  _ ← assertEq "newtype" (out.contains "pub struct ValidEmail(pub String);") true
  _ ← assertEq "no raw" (out.contains "raw") false
  .ok ()

/-! ## DidYouMean (moved here from SchemaLang — the every-error-path
    engine; wasm-backend and faults reach it core-only) -/

def didYouMeanChecks : CheckResult := do
  -- nearest-first ordering, cutoff-bounded
  _ ← assertEq "didYouMean nearest first"
    (didYouMean "usr" ["role", "user", "admin"]) ["user"]
  _ ← assertEq "didYouMean ties sort stably"
    (didYouMean "usre" ["user", "users", "roles"])
    ((didYouMean "usre" ["roles", "users", "user"]))
  -- the empty result = the closed world has no near neighbor (a NEGATIVE
  -- control: the filter is not vacuous — far strings stay out)
  _ ← assertEq "didYouMean cutoff excludes far entries"
    (didYouMean "completely-unrelated-token" ["user", "role"]) []
  .ok ()

def main : IO UInt32 := do
  let code ← mainOfChecks "CodegenCore"
    [ ("mangle", mangleChecks)
    , ("header", headerCheck)
    , ("registry", registryChecks)
    , ("emit", emitChecks)
  , ("didYouMean", didYouMeanChecks)
    ]
  if code != 0 then return code
  -- the deterministic +/− suite (TestKit.DetSpec: check must pass AND
  -- the control must fail — a vacuous control fails the gate)
  let detCode ← TestKit.runDets [manglerSpec]
  if detCode != 0 then return detCode
  -- the property sweep (PropSpec: property passes, control caught)
  TestKit.runSpecs [manglerPropSpec]
