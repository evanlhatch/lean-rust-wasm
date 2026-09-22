/-
# Faults Tests

wellFormed (resolution), framework well-formedness (name uniqueness +
code collision-freedom via `CodedRegistry`'s `by decide` proof fields —
the elab-time negative controls are `#guard_msgs` below), allocation
count preservation (the kernel-checked obligation), guest/host
code-space disjointness (0.4), retry policy, emit determinism + pins,
the emitter audit (1.6: run ⊆ declared outputs), the knownTypes tie to
the schema universe (1.8), and the derived diag-kind block.

Run: `lake build FaultsTests && .lake/build/bin/FaultsTests`
-/
import Faults
import Faults.Emit.Registry
import CodegenCore
import SchemaLang.Meta.Reflect
import TestKit

open Faults TestKit

/-! ## Elaboration-time negative controls (the framework's rejections)

The registry's well-formedness is in the TYPE now, so the controls are
elaboration failures, not Bool checks. -/

-- Attribute-level dup rejection: `notFound` is already registered by
-- `Faults.Spec.Demo` (the extension replays imports, so the cross-module
-- duplicate is caught HERE, at this def's elaboration).
/--
error: `fault`: failure-mode name `notFound` already registered at `Faults.Spec.notFound` — names must be unique
-/
#guard_msgs (error) in
@[fault] def dupNotFound : FailureModeItem :=
  { name := "notFound", display := "d", category := .content
  , advice := "a", payload := [] }

-- The decide-default dup rejection: a coded-registry literal with a
-- duplicate name cannot discharge `nodup` — the literal fails to
-- elaborate (there is no runtime path to reject). An `example`, not a
-- `def`: the failed decide closes with a sorry, and a NAMED declaration
-- would leave a sorryAx the axiom gate rightly flags.
/-- error: Tactic `decide` proved that the proposition -/
#guard_msgs (error, substring := true) in
example : CodegenCore.CodedRegistry FailureModeItem :=
  { items := [Spec.notFound, Spec.notFound], nameOf := (·.name)
  , codePrefix := "E", start := 100 }

-- The diag-kind derive rejects a non-inductive target (a structure IS
-- an inductive, so the control uses a theorem).
/--
error: `allocate_length` is not an inductive type
-/
#guard_msgs (error) in
derive_ctor_kinds badKinds badKind from Faults.allocate_length

def registryChecks : CheckResult := do
  _ ← assertEq "demo wellFormed"
      (universeWellFormed Spec.knownTypes Spec.apiFaults.toDataRegistry) true
  -- unknown payload ref rejected (schema universe is the type authority)
  let broken : CodegenCore.DataRegistry FailureModeItem :=
    { items := [ { name := "bad", display := "d", category := .content, advice := "a"
                 , payload := [("x", .ty "nonexistent")] } ]
    , nameOf := (·.name) }
  _ ← assertEq "unknown ref rejected" (universeWellFormed Spec.knownTypes broken) false
  -- a REAL schema ref resolves (knownTypes names are the registry's)
  let referencing : CodegenCore.DataRegistry FailureModeItem :=
    { items := [ { name := "orderFailed", display := "order failed: {err}"
                 , category := .content, advice := "inspect the order error"
                 , payload := [("err", .ty "OrderError")] } ]
    , nameOf := (·.name) }
  _ ← assertEq "schema ref resolves" (universeWellFormed Spec.knownTypes referencing) true
  -- allocation preserves count (the kernel-checked obligation, executed)
  _ ← assertEq "alloc count" Spec.apiFaults.codes.length Spec.apiFaults.items.length
  .ok ()

/-- 0.4: the guest/host code spaces are disjoint BY CONSTRUCTION — the
    host start is computed from the guest registry's size, so growth can
    never collide. Plus the negative control: a hardcoded host start (the
    old E110 fiat) DOES collide once guests grow past it — if the control
    ever passes, the disjointness checks are vacuous. -/
def allocationChecks : CheckResult := do
  _ ← assertEq "guest/host codes disjoint"
      (decide ((Spec.apiFaults.codes ++ Spec.hostFaults.codes).map (·.2)).Nodup)
      true
  -- the host start is DERIVED from the guest registry's size
  _ ← assertEq "host start derived" Spec.hostFaults.start (100 + Spec.apiFaults.items.length)
  -- 15 guests push codes past the old hardcoded E110 start; the computed
  -- start still clears them
  let oversized := List.replicate 15 Spec.apiFaults.items.head!
  let bigGuestCodes := CodegenCore.allocateCodes "E" 100 oversized
  let bigHostCodes := CodegenCore.allocateCodes "E" (100 + oversized.length) Spec.hostFaults.items
  _ ← assertEq "disjoint past old E110 start"
      (decide ((bigGuestCodes ++ bigHostCodes).map (·.2)).Nodup)
      true
  -- negative control: the OLD allocation scheme collides here
  _ ← assertEq "colliding start caught (control)"
      (decide ((bigGuestCodes ++ CodegenCore.allocateCodes "E" 110 Spec.hostFaults.items).map (·.2)).Nodup)
      false
  -- W-iso batch piece 3, density half: the E-code allocation is DENSE —
  -- every code parses back to exactly `start + position` (executable
  -- check; true by construction for `allocateCodes`). The ISO half
  -- (`CodedRegistry.membersIso`/`finIso`) does NOT fire here: α =
  -- FailureModeItem is payload-carrying (the registry does not exhaust
  -- it) and its separately-derived BEq does not chain to LawfulBEq —
  -- the iso is consumed on `CodedRegistry String` in codegen-core's
  -- coded-registry checks instead.
  _ ← assertEq "guest E-codes dense" Spec.apiFaults.denseCheck true
  _ ← assertEq "host E-codes dense" Spec.hostFaults.denseCheck true
  .ok ()

def policyChecks : CheckResult := do
  -- only transient retries (flatland's observability rules as a type)
  _ ← assertEq "transient retryable" (Category.retryable .transient) true
  _ ← assertEq "content not retryable" (Category.retryable .content) false
  _ ← assertEq "invariant not retryable" (Category.retryable .invariant) false
  _ ← assertEq "fatal not retryable" (Category.retryable .fatal) false
  .ok ()

def emitChecks : CheckResult := do
  let items := Emit.Rust.faultModule "OrderError" Spec.apiFaults.codes
  let out := CodegenCore.Emit.Rust.renderModule items
  -- determinism: same input, same bytes
  _ ← assertEq "deterministic" out (CodegenCore.Emit.Rust.renderModule items)
  -- the macro + enum shape
  _ ← assertEq "macro" (out.contains "fast_observe::error!") true
  _ ← assertEq "enum" (out.contains "pub enum OrderError {") true
  -- codes from the registry, never hand-set
  _ ← assertEq "code attr" (out.contains "#[code = \"E100\", category = Content,") true
  _ ← assertEq "code attr 2" (out.contains "#[code = \"E101\", category = Content,") true
  _ ← assertEq "transient attr" (out.contains "category = Transient") true
  -- advice flows through
  _ ← assertEq "advice" (out.contains "advice = \"check cart state\"") true
  -- payload fields via schema Ty lowering
  _ ← assertEq "payload field" (out.contains "NotFound { id: u64 },") true
  -- wasm init hook (linkme unavailable on wasm)
  _ ← assertEq "init_guest" (out.contains "register_statics(OrderError::ENTRIES)") true
  -- no raw escape hatches
  _ ← assertEq "no pub pub" (out.contains "pub pub") false
  .ok ()

/-- The one-writer audit: no two faults emitters claim the same output
    path (asserted through codegen-core's shared `Emitter.checkNodup` —
    the W7.3p2 dedup shape schema-lang's Tests use; the inline
    `Faults.Emit.pathsUnique` copy was deleted), the forge job row
    covers exactly the registry's outputs (same pattern as schema-lang's
    `jobsCoverEmitters` — an emitter whose artifact forge never byte-ties
    fails here, not silently), AND every file `run` produces is a
    DECLARED output (1.6: run ⊆ outputs — `run` may not re-state paths
    `outputs` doesn't declare). Negative control: a rogue emitter whose
    `run` writes outside its declared `outputs` must FAIL the audit. -/
def emitterAuditChecks : CheckResult := do
  _ ← assertEq "emitter paths unique"
      (CodegenCore.Emit.Emitter.checkNodup Faults.Emit.emitters) true
  _ ← assertEq "jobs cover emitters" Faults.Emit.jobsCoverEmitters true
  _ ← assertEq "run ⊆ declared outputs"
      (Faults.Emit.jobs.all fun (e, spec) =>
        (e.run spec).all fun f => e.outputs.contains f.path) true
  -- the emission laws (the vortex lane's `vortexLaw` shape): both fault
  -- emitters carry the CodedRegistry's code-collision-freedom as law,
  -- discharged by the `codes_nodup` citation; the certified lane
  -- executes (`runCertified = run` by definition)
  _ ← assert (Faults.Emit.guestEmitter.law.isSome) "guest law populated"
  _ ← assert (Faults.Emit.hostEmitter.law.isSome) "host law populated"
  _ ← assertEq "guest certified run = run"
      ((Faults.Emit.guestEmitter.runCertified Spec.apiFaults
        (Faults.Emit.codesNodupLaw_discharged Spec.apiFaults)).map (·.contents))
      ((Faults.Emit.guestEmitter.run Spec.apiFaults).map (·.contents))
  _ ← assertEq "host certified run = run"
      ((Faults.Emit.hostEmitter.runCertified Spec.hostFaults
        (Faults.Emit.codesNodupLaw_discharged Spec.hostFaults)).map (·.contents))
      ((Faults.Emit.hostEmitter.run Spec.hostFaults).map (·.contents))
  let rogueEmitter : CodegenCore.Emit.Emitter Faults.Emit.FaultsSpec :=
    { Faults.Emit.guestEmitter with outputs := ["../../src/elsewhere.rs"] }
  _ ← assertEq "undeclared output caught (control)"
      ((rogueEmitter.run Spec.apiFaults).all fun f =>
        rogueEmitter.outputs.contains f.path) false
  .ok ()

open Lean SchemaLang.Meta in
/-- The schema demo universe's type names, loaded at runtime (schema-lang
    Tests' `loadDemoItems` pattern): `importModules` resolves oleans at
    RUNTIME — initialize the search path, adding this package's build dir
    AND the dependency packages' (Demo's import closure runs through
    schema-lang → substrait). A direct binary run lacks LEAN_PATH; the
    tests run from the package root. -/
unsafe def loadDemoTypeNames : IO (List String) := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.searchPathRef.modify fun sp =>
    sp ++ [ (".lake/build/lib" : System.FilePath), (".lake/build/lib/lean" : System.FilePath)
          , ("../schema-lang/.lake/build/lib/lean" : System.FilePath)
          , ("../schema-lang/.lake/build/lib" : System.FilePath)
          , ("../substrait/.lake/build/lib/lean" : System.FilePath)
          , ("../codegen-core/.lake/build/lib/lean" : System.FilePath)
          , ("../Machines/.lake/build/lib/lean" : System.FilePath)
          , ("../TestKit/.lake/build/lib/lean" : System.FilePath) ]
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[`Demo] (opts := {}) (loadExts := true)
  pure (SchemaLang.Item.typeNames ((registeredItems env).map (·.2)))

/-- 1.8: `Spec.knownTypes` hand-mirrors the schema demo universe's type
    names (the registry lives in an env extension, so a pure def cannot
    read it). This is the tie: load the ACTUAL registry and assert
    equality — edit Demo.lean without updating `knownTypes` and the
    suite goes red. Negative control: a stale knownTypes (the old kebab
    list) must FAIL the same comparison. -/
def knownTypesChecks (typeNames : List String) : CheckResult := do
  _ ← assertEq "knownTypes = schema universe" Spec.knownTypes typeNames
  _ ← assertEq "stale knownTypes caught (control)"
      (["user", "role", "order-error"] == typeNames) false
  .ok ()

/-- The error paths' did-you-mean + the schema-diag E-codes (the ONE
    E-code universe): a fault payload's unresolved type renders the
    closed-world suggestion (via `Ty.check` → `CodegenCore.didYouMean`),
    and the elaboration diagnostics resolve THEIR E-codes from the same
    allocation schedule (single lookup). The kinds list is DERIVED from
    `SchemaDiag`'s constructors at its definition site (`derive_ctor_kinds`
    in Emit/Registry.lean) — the derived-only pins here (length + E-code
    positions) are the regression controls on constructor order (a
    `SchemaDiag` edit shifts the E-code block; the byte-tie and these
    pins both go loud). Negative control: the lookup is keyed on the
    constructor kind — a sabotaged kind misses. -/
def diagCodeChecks : CheckResult := do
  -- the faults error path: did-you-mean reaches the payload diagnostics
  let broken : FailureModeItem :=
    { name := "bad", display := "d", category := .content, advice := "a"
    , payload := [("x", .ty "usr")] }
  let ds := broken.diagnose Spec.knownTypes
  _ ← assertEq "diagnose nonempty" ds.isEmpty false
  _ ← assertEq "diagnose did-you-mean" (ds.any fun d => d.contains "did you mean") true
  -- C2: the kinds list is DERIVED at its definition site
  -- (`derive_ctor_kinds schemaDiagKinds schemaDiagKind from
  -- SchemaLang.SchemaDiag` in Emit/Registry.lean — the constructor list
  -- itself, in declaration order). The 24-name hand re-list that lived
  -- here was a PROJECTION of that data — and it drifted once (the
  -- W8.2/W8.13/emitter-bug ctors landed while the stale 10-ctor pin sat
  -- unnoticed because no gate ran this exe). The pins are now
  -- derived-only: a LENGTH pin (append-only guard — a new SchemaDiag
  -- ctor without a deliberate pin update goes red), an allocation-keys
  -- tie (`allocateCodes` zips list position, so the code KEYS are the
  -- derived order), and E-code position pins at the FIRST, SECOND and
  -- LAST positions (an insert before any ctor shifts the moved ctors'
  -- codes; an append trips the length pin). The byte-tie is the
  -- comprehensive stability control on the allocation.
  _ ← assertEq "schema-diag kinds length (append-only)"
    Faults.Emit.schemaDiagKinds.length 24
  _ ← assertEq "schema-diag allocation keys = derived kind order"
    (Faults.Emit.schemaDiagCodes.map (·.1)) Faults.Emit.schemaDiagKinds
  -- the schema-diag block: allocated AFTER the fault registries (4 + 4)
  _ ← assertEq "schema-diag codes start E108"
    ((Faults.Emit.schemaDiagCodes.map (·.2)).head?.getD "") "E108"
  _ ← assertEq "schema-diag block size"
    Faults.Emit.schemaDiagCodes.length Faults.Emit.schemaDiagKinds.length
  -- the LAST ctor's code (position 23 → E131): a mid-list insert that
  -- shifts any later ctor's code goes red on this pin
  _ ← assertEq "tail ctor code E131"
    ((Faults.Emit.schemaDiagCodes.map (·.2)).getLast?.getD "") "E131"
  -- the cross-ref: single-lookup coded render
  _ ← assertEq "coded render"
    (Faults.Emit.renderDiagCoded (.dupName "user"))
    "[E109] duplicate name `user` — names must be unique"
  -- negative control: the lookup is kind-keyed — a bogus kind misses
  _ ← assertEq "kind-keyed lookup misses bogus (control)"
    (Faults.Emit.schemaDiagCodes.lookup "bogus") (none : Option String)
  .ok ()

unsafe def main : IO UInt32 := do
  let typeNames ← loadDemoTypeNames
  mainOfChecks "Faults"
    [ ("registry", registryChecks)
    , ("allocation", allocationChecks)
    , ("policy", policyChecks)
    , ("emit", emitChecks)
    , ("emitterAudit", emitterAuditChecks)
    , ("knownTypesTie", knownTypesChecks typeNames)
    , ("diagCodes", diagCodeChecks)
    ]
