/-
# Faults Tests

wellFormed (resolution + Nodup), allocation count preservation (the
kernel-checked obligation), guest/host code-space disjointness (0.4),
retry policy, emit determinism + pins, the emitter audit (1.6: run ⊆
declared outputs), and the knownTypes tie to the schema universe (1.8).

Run: `lake build FaultsTests && .lake/build/bin/FaultsTests`
-/
import Faults
import Faults.Emit.Registry
import CodegenCore
import SchemaLang.Meta.Reflect
import TestKit

open Faults TestKit

def registryChecks : CheckResult := do
  _ ← assertEq "demo wellFormed" (universeWellFormed Spec.knownTypes Spec.apiFaults) true
  -- unknown payload ref rejected (schema universe is the type authority)
  let broken : List FailureModeItem :=
    [ { name := "bad", display := "d", category := .content, advice := "a"
      , payload := [("x", .ty "nonexistent")] } ]
  _ ← assertEq "unknown ref rejected" (universeWellFormed Spec.knownTypes broken) false
  -- a REAL schema ref resolves (knownTypes names are the registry's)
  let referencing : List FailureModeItem :=
    [ { name := "orderFailed", display := "order failed: {err}"
      , category := .content, advice := "inspect the order error"
      , payload := [("err", .ty "OrderError")] } ]
  _ ← assertEq "schema ref resolves" (universeWellFormed Spec.knownTypes referencing) true
  -- dup names rejected
  _ ← assertEq "dup rejected" (namesUnique (Spec.apiFaults ++ Spec.apiFaults)) false
  -- allocation preserves count (the kernel-checked obligation, executed)
  _ ← assertEq "alloc count" (allocate Spec.apiFaults).length Spec.apiFaults.length
  .ok ()

/-- 0.4: the guest/host code spaces are disjoint BY CONSTRUCTION — the
    host start is computed from the guest registry's size, so growth can
    never collide. Plus the negative control: a hardcoded host start (the
    old E110 fiat) DOES collide once guests grow past it — if the control
    ever passes, the disjointness checks are vacuous. -/
def allocationChecks : CheckResult := do
  _ ← assertEq "guest/host codes disjoint"
      (decide ((allocate Spec.apiFaults ++ allocateHost Spec.apiFaults Spec.hostFaults).map (·.2)).Nodup)
      true
  -- 15 guests push codes past the old hardcoded E110 start; the computed
  -- start still clears them
  let oversized := List.replicate 15 Spec.apiFaults.head!
  _ ← assertEq "disjoint past old E110 start"
      (decide ((allocate oversized ++ allocateHost oversized Spec.hostFaults).map (·.2)).Nodup)
      true
  -- negative control: the OLD allocation scheme collides here
  _ ← assertEq "colliding start caught (control)"
      (decide ((allocate oversized ++ CodegenCore.allocateCodes "E" 110 Spec.hostFaults).map (·.2)).Nodup)
      false
  .ok ()

def policyChecks : CheckResult := do
  -- only transient retries (flatland's observability rules as a type)
  _ ← assertEq "transient retryable" (Category.retryable .transient) true
  _ ← assertEq "content not retryable" (Category.retryable .content) false
  _ ← assertEq "invariant not retryable" (Category.retryable .invariant) false
  _ ← assertEq "fatal not retryable" (Category.retryable .fatal) false
  .ok ()

def emitChecks : CheckResult := do
  let items := Emit.Rust.faultModule "OrderError" (allocate Spec.apiFaults)
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
    path (mirrors `SchemaLang.Emit.pathsUnique`), the forge job row
    covers exactly the registry's outputs (same pattern as schema-lang's
    `jobsCoverEmitters` — an emitter whose artifact forge never byte-ties
    fails here, not silently), AND every file `run` produces is a
    DECLARED output (1.6: run ⊆ outputs — `run` may not re-state paths
    `outputs` doesn't declare). Negative control: a rogue emitter whose
    `run` writes outside its declared `outputs` must FAIL the audit. -/
def emitterAuditChecks : CheckResult := do
  _ ← assertEq "emitter paths unique" Faults.Emit.pathsUnique true
  _ ← assertEq "jobs cover emitters" Faults.Emit.jobsCoverEmitters true
  _ ← assertEq "run ⊆ declared outputs"
      (Faults.Emit.jobs.all fun (e, spec) =>
        (e.run spec).all fun f => e.outputs.contains f.path) true
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
    allocation schedule (single lookup). Negative control: the lookup is
    keyed on the constructor kind — a sabotaged kind misses. -/
def diagCodeChecks : CheckResult := do
  -- the faults error path: did-you-mean reaches the payload diagnostics
  let broken : FailureModeItem :=
    { name := "bad", display := "d", category := .content, advice := "a"
    , payload := [("x", .ty "usr")] }
  let ds := broken.diagnose Spec.knownTypes
  _ ← assertEq "diagnose nonempty" ds.isEmpty false
  _ ← assertEq "diagnose did-you-mean" (ds.any fun d => d.contains "did you mean") true
  -- the schema-diag block: allocated AFTER the fault registries (4 + 4)
  _ ← assertEq "schema-diag codes start E108"
    ((Faults.Emit.schemaDiagCodes.map (·.2)).head?.getD "") "E108"
  _ ← assertEq "schema-diag block size"
    Faults.Emit.schemaDiagCodes.length Faults.Emit.schemaDiagKinds.length
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
