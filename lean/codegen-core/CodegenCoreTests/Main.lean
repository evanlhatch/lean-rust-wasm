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
  _ ← assertEq "rootRel strips ../../" (rootRel "../../generated/wit/delta.wit") "generated/wit/delta.wit"
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

/-! ## GenKit — the `declare_*` generation runtime (didYouMeanSuffix /
    unknownName* / freshName*; the first clients are the macro-registered
    LintKit linters + the `@[derived]` stamp's fixture lane) -/

def genKitChecks : CheckResult := do
  -- the suffix format: the did-you-mean over the nearest candidates
  _ ← assertEq "didYouMeanSuffix appends the nearest"
    (didYouMeanSuffix "usr" ["role", "user", "admin"]) " — did you mean: user?"
  -- NEGATIVE control: nothing near = empty suffix (no empty suggestion)
  _ ← assertEq "didYouMeanSuffix empty when nothing near"
    (didYouMeanSuffix "completely-unrelated" ["user", "role"]) ""
  -- the unknown-name rejection ENUMERATES the legal space, then hints
  _ ← assertEq "unknownNameMessage enumerates the legal space"
    (unknownNameMessage "machine!" "intial" "clause" ["initial", "final"])
    "machine!: unknown clause `intial` — legal clauses: `initial`, `final` — did you mean: initial, final?"
  -- the fresh-name verdict: taken name → the rejection with did-you-mean
  _ ← assertEq "freshNameVerdict rejects a taken name (did-you-mean rides)"
    (freshNameVerdict "schema_from_template x" "user" "schema item" ["role", "user"])
    (some "schema_from_template x: `user` is already a registered schema item — \
      names must be fresh — did you mean: user?")
  -- NEGATIVE control: a fresh name passes silently
  _ ← assertEq "freshNameVerdict accepts a fresh name"
    (freshNameVerdict "ctx" "acct" "schema item" ["role", "user"]) none
  .ok ()

/-! ## Emitter.law + checkNodup (W7.9 phase 1)

The optional `law` field defaults to `none` (downstream literals unchanged);
`runCertified` is the proof-carrying lane; `checkNodup` is the decidable
one-writer audit. -/

/-- Plain emitter: no law. -/
def demoEmitterA : Emitter Unit where
  name := "demo-a"
  style := .doubleSlash
  specSource := "CodegenCore Tests"
  outputs := ["gen/a.txt"]
  run _ := []

/-- Second plain emitter, distinct output. -/
def demoEmitterB : Emitter Unit where
  name := "demo-b"
  style := .doubleSlash
  specSource := "CodegenCore Tests"
  outputs := ["gen/b.txt"]
  run _ := []

/-- Law-carrying emitter: one file per item, the law is name `Nodup`
    (the one-writer law — the CertifiedEmitter demo's shape, absorbed). -/
def demoLawEmitter : Emitter (List String) where
  name := "law-demo"
  style := .doubleSlash
  specSource := "CodegenCore Tests"
  outputs := ["gen/la.txt", "gen/lb.txt"]
  run items := items.map fun i => { path := s!"gen/{i}.txt", contents := s!"// {i}\n" }
  law := some List.Nodup

/-- The discharged certificate over concrete data (`by decide` — the
    registry-ships-the-proof pattern `checkNodup`'s docstring prescribes). -/
theorem demoLawCert : demoLawEmitter.Cert ["la", "lb"] := by
  show List.Nodup ["la", "lb"]
  decide

/-- The documented registry pattern: the one-writer audit discharged by
    `decide`, shipped beside the registry. -/
theorem demoEmitters_nodup :
    Emitter.checkNodup [demoEmitterA, demoEmitterB] = true := by decide

def emitterLawChecks : CheckResult := do
  _ ← assertEq "law defaults to none" demoEmitterA.law.isNone true
  _ ← assertEq "law some" demoLawEmitter.law.isSome true
  -- the uncertified lane still works for law-less emitters
  _ ← assertEq "runCertified (no law)"
    ((demoEmitterA.runCertified () trivial).map (·.path)) []
  -- the certified lane consumes the discharged certificate
  _ ← assertEq "runCertified (law) paths"
    ((demoLawEmitter.runCertified ["la", "lb"] demoLawCert).map (·.path))
    demoLawEmitter.outputs
  -- checkNodup: distinct outputs pass, a collision is rejected
  _ ← assertEq "checkNodup distinct"
    (Emitter.checkNodup [demoEmitterA, demoEmitterB]) true
  _ ← assertEq "checkNodup collision"
    (Emitter.checkNodup [demoEmitterA, demoEmitterA]) false
  _ ← assertEq "checkNodup empty" (Emitter.checkNodup (Spec := Unit) []) true
  .ok ()

/-! ## DataRegistry (W7.16)

Dup rejection is COMPILE-TIME: the `nodup` field's `by decide` default
fails to elaborate a duplicate-named literal, so there is no runtime
rejection path to test — the negative control is the type error. Only
positive tests ship here. -/

/-- A small concrete registry (String items are their own names). -/
def colorReg : DataRegistry String where
  items := ["red", "green", "blue"]
  nameOf := id
  -- `nodup` discharged by the `by decide` default — a dup here would not
  -- elaborate.

/-- Compile-time law consumption: the proved determinism law instantiated
    on the concrete registry — `"blue"` is THE unique item named `"blue"`. -/
theorem colorReg_lookup_unique :
    ∀ b ∈ colorReg.items, colorReg.nameOf b = "blue" → b = "blue" :=
  fun b hb hn => colorReg.lookup?_ok_unique (by rfl) b hb hn

def dataRegistryChecks : CheckResult := do
  _ ← assertEq "all" colorReg.all ["red", "green", "blue"]
  _ ← match colorReg.lookup? "green" with
    | .ok g => assertEq "lookup hit" g "green"
    | .error miss => .error s!"unexpected miss: {miss.got}"
  _ ← match colorReg.lookup? "gren" with
    | .error miss =>
      if miss.got == "gren" && miss.didYouMean.contains "green" then .ok ()
      else .error s!"bad miss payload: {miss.got} {miss.didYouMean}"
    | .ok _ => .error "expected miss for 'gren'"
  -- insertion: fresh name in, findable immediately, old items intact
  let reg2 := colorReg.insert "yellow" (by decide)
  _ ← assertEq "insert grows" reg2.all.length 4
  _ ← match reg2.lookup? "yellow" with
    | .ok y => assertEq "insert hit" y "yellow"
    | .error _ => .error "inserted item not found"
  _ ← match reg2.lookup? "red" with
    | .ok r => assertEq "old item survives" r "red"
    | .error _ => .error "old item lost after insert"
  .ok ()

/-! ## CodedRegistry (W7.4 follow-up)

A CodedRegistry extends DataRegistry with position-derived codes (`codePrefix`
+ index). The `codesNodup` default (`by decide`) ensures a literal with
colliding codes fails to elaborate — only positive checks ship here. -/

/-- A small concrete coded registry (string items are their own names). -/
def codeColorReg : CodedRegistry String where
  items := ["red", "green", "blue"]
  nameOf := id
  codePrefix := "C"
  start := 10

/-- Compile-time law: the codes-length theorem on the concrete registry. -/
theorem codeColorReg_codes_length :
    codeColorReg.codes.length = codeColorReg.items.length :=
  codeColorReg.codes_length

/-- Compile-time proof: the `codesNodup` default discharges by `decide`. -/
theorem codeColorReg_codesNodup :
    (codeColorReg.codes.map (·.2)).Nodup := by
  exact codeColorReg.codesNodup

def codedRegistryChecks : CheckResult := do
  -- codes match the codePrefix-index shape
  let expectedCodes := [("red", "C10"), ("green", "C11"), ("blue", "C12")]
  _ ← assertEq "codes match prefix+index shape"
    codeColorReg.codes expectedCodes
  -- name lookup works (inherited from DataRegistry)
  _ ← match codeColorReg.lookup? "green" with
    | .ok g => assertEq "coded lookup hit" g "green"
    | .error miss => .error s!"unexpected coded miss: {miss.got}"
  _ ← match codeColorReg.lookup? "gren" with
    | .error miss =>
      if miss.got == "gren" && miss.didYouMean.contains "green" then .ok ()
      else .error s!"bad coded miss payload: {miss.got} {miss.didYouMean}"
    | .ok _ => .error "expected miss for 'gren' in coded registry"
  -- codes-length law holds
  _ ← assertEq "coded codes.length = items.length"
    codeColorReg.codes.length codeColorReg.items.length
  -- W-iso batch piece 3: the denseness upgrade — the code space is dense
  -- (each code parses back to start + position), and positions ↔ members
  -- is an honest Iso (`membersIso`; String carries LawfulBEq so the
  -- instance fires). The full `Iso (Fin n) α` upgrade (`finIso`) needs
  -- the registry to EXHAUST α — true for enum registries, not for String.
  _ ← assertEq "codes dense" codeColorReg.denseCheck true
  _ ← assertEq "position 0 is the first member"
    ((codeColorReg.membersIso.to ⟨0, by decide⟩).val) "red"
  _ ← assertEq "first member back to position 0"
    (decide ((codeColorReg.membersIso.inv ⟨"red", by decide⟩).val = 0)) true
  .ok ()

/-! ## Validation (W7.18) — error-ACCUMULATING applicative

The accumulation contract as executable checks (the laws are compile-side:
`foldlM_ok` / `foldlM_errs_length` instantiated on concrete data below). -/

/-- Law consumption (compile-time): the ok-identity on concrete data —
    folding pure-ok addition steps IS the plain fold. -/
theorem foldlM_ok_demo :
    Validation.foldlM (fun (b a : Nat) => Validation.ok (b + a)) 0 [1, 2, 3] =
      Validation.ok (ε := String) 6 := by
  rw [Validation.foldlM_ok (g := fun (b a : Nat) => b + a)]
  rfl

/-- Law consumption (compile-time): the anti-early-exit pin — 3 failing
    steps, 3 errors reported. -/
theorem foldlM_errs_length_demo :
    (Validation.foldlM (fun (_ : Unit) (_ : Nat) => Validation.errs ["boom"])
      () [1, 2, 3]).errors?.length = 3 :=
  Validation.foldlM_errs_length "boom" () 1 [2, 3]

def validationChecks : CheckResult := do
  -- foldlM: three failures across five elements, errors in element order,
  -- the ok-steps between errors still fold (state continues from the last
  -- known accumulator)
  let step (acc : List Nat) (n : Nat) : Validation String (List Nat) :=
    if n % 2 == 0 then .ok (acc ++ [n]) else .errs [s!"E{n}"]
  _ ← assertEq "foldlM accumulates in order"
    (Validation.foldlM step [] [1, 2, 3, 4, 5])
    (Validation.errs ["E1", "E3", "E5"])
  -- the ok case: no errors, plain fold
  _ ← assertEq "foldlM all-ok"
    (Validation.foldlM (fun (b a : Nat) => Validation.ok (b + a)) 0 [1, 2, 3])
    (Validation.ok (ε := String) 6)
  -- traverse: every failure reported, element order, values discarded
  _ ← assertEq "traverse accumulates"
    (Validation.traverse
      (fun n : Nat => if n == 2 then Validation.errs [s!"bad{n}"] else Validation.ok n)
      [1, 2, 3, 2])
    (Validation.errs ["bad2", "bad2"])
  _ ← assertEq "traverse all-ok"
    (Validation.traverse (ε := String) (fun n : Nat => Validation.ok (n * 10)) [1, 2, 3])
    (Validation.ok [10, 20, 30])
  -- applicative seq: both sides' errors concatenate, function side first
  _ ← assertEq "seq concatenates"
    ((Validation.errs ["fn"] : Validation String (Nat → Nat)) <*>
      (Validation.errs ["arg"] : Validation String Nat))
    (Validation.errs ["fn", "arg"])
  _ ← assertEq "seq ok"
    ((Validation.ok (fun n : Nat => n + 1) : Validation String (Nat → Nat)) <*>
      (Validation.ok 41 : Validation String Nat))
    (Validation.ok (ε := String) 42)
  .ok ()

/-! ## Obligation (W7.1) — the checkable-fact-as-data substrate

Pins: the tier's renderings, the evidence→tier mapping (a mis-wired
discharge is detectable as data), and one toy obligation's shape. The
lane-level discharge + its negative control live in schema-lang's
tests (the invariant lane rides this substrate). -/
def obligationChecks : CheckResult := do
  _ ← assertEq "tier render" (Obligation.Tier.render .generatedCheck) "generated-check"
  _ ← assertEq "tier render proved" (Obligation.Tier.render .provedAtElab) "proved-at-elab"
  _ ← assertEq "evidence tier: cited proof"
    (Obligation.Evidence.tier (.citedProof `foo)) Obligation.Tier.provedAtElab
  _ ← assertEq "evidence tier: decided"
    (Obligation.Evidence.tier (.decided true)) .decidableNow
  _ ← assertEq "evidence tier: generated"
    (Obligation.Evidence.tier (.generatedCheck "a.rs" "f")) .generatedCheck
  _ ← assertEq "evidence tier: oracle"
    (Obligation.Evidence.tier (.oracleRow "r")) .oracleSwept
  -- W9.3: the fifth tier (design-guest-verified §3) — render + the
  -- witness evidence's tier mapping
  _ ← assertEq "tier render guest-verified"
    (Obligation.Tier.render .guestVerified) "guest-verified"
  _ ← assertEq "evidence tier: guest witness"
    (Obligation.Evidence.tier (.guestWitness "w.wtn" "lbl")) .guestVerified
  let toy : Obligation Bool :=
    { label := "one-eq-one", tier := .decidableNow, payload := true, provenance := `toy }
  _ ← assertEq "toy label" toy.label "one-eq-one"
  _ ← assertEq "toy tier" toy.tier .decidableNow
  .ok ()

/-! ## RoundTripSpec (W7.17) — toy Bool wire codec

The combinator assembles sweep + sabotage control + golden; the tests pin
that the control is CAUGHT (default sabotage bites this codec), that the
golden byte-tie detects drift, and that a non-biting sabotage (identity)
is flagged VACUOUS — the negative control cannot be omitted or defused
silently. -/

/-- Toy byte codec: Bool as one tag byte, exact decode (everything else
    rejected) — a `Kit.PartialIso` value. -/
def boolIso : PartialIso (List UInt8) Bool where
  decode
    | [0] => some false
    | [1] => some true
    | _ => none
  encode
    | false => [0]
    | true => [1]
  decode_encode := by
    intro b
    cases b <;> decide

/-- The generated suite: sweep + first-byte-increment control + golden
    samples (false → [0] decodes the +1 sabotage as `true` ≠ false;
    true → [1] corrupts to [2], rejected). -/
def boolWireSpec : RoundTripSpec Bool where
  name := "codegencore-bool-wire"
  iso := boolIso
  samples := [false, true, true]
  goldenDir := some "/tmp"

/-- W-iso batch piece 1, consumed on the toy codec: `toImageIso` upgrades
    the PartialIso to a TRUE Iso on its image; `inv_to` executed says
    re-encoding the decode of a canonical byte string reproduces the
    bytes EXACTLY (the both-ways round trip the one-ended law cannot
    give). -/
def boolImageChecks : CheckResult := do
  let img := boolIso.toImageIso
  _ ← assertEq "image decode" (img.to ⟨[1], ⟨true, rfl⟩⟩) true
  _ ← assertEq "image re-encode round trip"
    (decide (boolIso.encode (img.to ⟨[0], ⟨false, rfl⟩⟩) = [0])) true
  .ok ()

/-- The defused variant: identity "sabotage" — the control asserts the
    kit law itself, passes trivially, and `runIO` MUST flag it vacuous. -/
def boolWireVacuous : RoundTripSpec Bool where
  name := "codegencore-bool-wire-vacuous"
  iso := boolIso
  sabotage := id

def main : IO UInt32 := do
  let code ← mainOfChecks "CodegenCore"
    [ ("mangle", mangleChecks)
    , ("header", headerCheck)
    , ("registry", registryChecks)
    , ("emit", emitChecks)
  , ("didYouMean", didYouMeanChecks)
  , ("genKit", genKitChecks)
  , ("bool-image", boolImageChecks)
  , ("emitter-law", emitterLawChecks)
  , ("data-registry", dataRegistryChecks)
  , ("coded-registry", codedRegistryChecks)
  , ("validation", validationChecks)
  , ("obligation", obligationChecks)
    ]
  if code != 0 then return code
  -- the monadic gates' THROW path (over CoreM — MonadError's real
  -- instantiation): the rejection message rides verbatim, did-you-mean and all
  let env ← Lean.mkEmptyEnvironment
  let thrown ←
    try
      let (r, _) ← ((do
          freshNameCheck "ctx" "user" "item" ["user"]
          pure "NO-THROW (the gate passed a duplicate — broken)" :
          Lean.CoreM String)).toIO
        { fileName := "<genkit>", fileMap := default } { env }
      pure r
    catch e => pure (toString e)
  unless (thrown.splitOn "did you mean").length == 2 do
    IO.eprintln s!"FAIL: freshNameCheck throw path: {thrown}"
    return 1
  let fresh ←
    try
      let (r, _) ← ((do
          freshNameCheck "ctx" "acct" "item" ["user"]
          pure "fresh-passed" : Lean.CoreM String)).toIO
        { fileName := "<genkit>", fileMap := default } { env }
      pure r
    catch _ => pure "THREW (the gate rejected a fresh name — broken)"
  unless fresh == "fresh-passed" do
    IO.eprintln s!"FAIL: freshNameCheck fresh path: {fresh}"
    return 1
  -- the deterministic +/− suite (TestKit.DetSpec: check must pass AND
  -- the control must fail — a vacuous control fails the gate)
  let detCode ← TestKit.runDets [manglerSpec]
  if detCode != 0 then return detCode
  -- the property sweep (PropSpec: property passes, control caught)
  let propCode ← TestKit.runSpecs [manglerPropSpec]
  if propCode != 0 then return propCode
  -- W7.17: the assembled round-trip suite — sweep + control + golden
  let rtWrite ← boolWireSpec.runIO (update := true)
  if rtWrite != 0 then return rtWrite
  let rtMatch ← boolWireSpec.runIO
  if rtMatch != 0 then return rtMatch
  -- golden drift MUST be caught
  IO.FS.writeFile "/tmp/codegencore-bool-wire.golden" "drifted\n"
  let rtDrift ← boolWireSpec.runIO
  if rtDrift == 0 then
    IO.eprintln "FAIL: golden drift was not caught"
    return 1
  IO.println "✓ roundtrip golden drift caught"
  -- a defused (identity) sabotage MUST be flagged vacuous
  let (vacOk, vacVerdict) ← boolWireVacuous.propSpec.runIO
  IO.println vacVerdict
  if vacOk then
    IO.eprintln "FAIL: identity-sabotage control was not flagged vacuous"
    return 1
  return 0
