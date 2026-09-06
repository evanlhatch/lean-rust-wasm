/-
# Faults Tests

wellFormed (resolution + Nodup), allocation count preservation (the
kernel-checked obligation), retry policy, emit determinism + pins.

Run: `lake build FaultsTests && .lake/build/bin/FaultsTests`
-/
import Faults
import TestKit

open Faults TestKit

def registryChecks : CheckResult := do
  _ ← assertEq "demo wellFormed" (universeWellFormed Spec.knownTypes Spec.apiFaults) true
  -- unknown payload ref rejected (schema universe is the type authority)
  let broken : List FailureModeItem :=
    [ { name := "bad", display := "d", category := .content, advice := "a"
      , payload := [("x", .ty "nonexistent")] } ]
  _ ← assertEq "unknown ref rejected" (universeWellFormed Spec.knownTypes broken) false
  -- dup names rejected
  _ ← assertEq "dup rejected" (namesUnique (Spec.apiFaults ++ Spec.apiFaults)) false
  -- allocation preserves count (the kernel-checked obligation, executed)
  _ ← assertEq "alloc count" (allocate Spec.apiFaults).length Spec.apiFaults.length
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
  _ ← assertEq "init_guest" (out.contains "register_statics(&[OrderError::ENTRIES])") true
  -- no raw escape hatches
  _ ← assertEq "no pub pub" (out.contains "pub pub") false
  .ok ()

def main : IO UInt32 :=
  mainOfChecks "Faults"
    [ ("registry", registryChecks)
    , ("policy", policyChecks)
    , ("emit", emitChecks)
    ]
