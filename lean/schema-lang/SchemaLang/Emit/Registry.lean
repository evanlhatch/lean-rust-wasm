/-
# SchemaLang.Emit.Registry — the emitter registry (the buf plugin model)

buf's architecture: ONE parsed schema, MANY emitters, each a plugin
that consumes the descriptor and produces files. Here: the descriptor
is `GenCtx` — the project's FULL registry state (the `List Item`
universe kernel-checked, plus the invariant/update lanes — the v2
env-hook contract); an `Emitter` is a plugin with a name, a comment
style, DECLARED output paths (the one-writer audit surface), and a
pure `run` from the ctx to files.

Adding a language = one module defining an `Emitter` + one line in
`emitters`. No driver changes, no GenMain changes (the driver iterates
the registry). Outputs must be unique across the registry — the audit
test fails the build on a collision, and `forge gen --check` byte-ties
every declared path.

Two of the emitters are FORGE-DRIVER artifacts (see the section below):
the pipeline stage machine forge sequences through, and the job
manifest forge byte-ties from — the driver consumes the Lean spec
instead of a hand-copied stale table.
-/

import CodegenCore
import SchemaLang.Item
import SchemaLang.Pipeline
import SchemaLang.Emit.GenCtx
import SchemaLang.Emit.Wit
import SchemaLang.Emit.Rust
import SchemaLang.Delta
import SchemaLang.Emit.WitFixture
import SchemaLang.Emit.Invariant
import SchemaLang.Emit.Update
import SchemaLang.Emit.Machine
import SchemaLang.Emit.Typestate
import SchemaLang.Vortex.Emit
import SchemaLang.Vortex.ExtDType
import SchemaLang.Docs

namespace SchemaLang.Emit

/-! ## The forge-driver artifacts

forge (crates/forge) is the pipeline's Rust DRIVER. Two artifacts make
it consume the Lean spec instead of a hand-copied stale surface (the
JOBS table it shipped with had DRIFTED — the delta/ext-dtype artifacts
were registered here but never byte-tied there):

1. `pipelineEmitter` — the stage machine as Rust (`PipelineStage` enum +
   `step` fn), mirroring `Pipeline.pipelineTrans` — the table
   `tableStep?_eq_step?` proves IS the machine. forge steps its own
   phases through it; an illegal transition aborts the driver (the
   proved `rank_advances`/`reject_out_of_order` govern the Rust side).
2. `forgeJobsEmitter` — the job manifest (`package`, `exe`, `outputs`).
   forge reads it instead of a hand-written table — registering an
   emitter whose artifact forge never byte-ties becomes a CI failure
   (`jobsCoverEmitters`), not a silent gap.
-/

/-- One job row → the JSON object text. Takes the registry's RAW
    package-relative outputs and roots them itself (`CodegenCore.Emit.rootRel`
    — callers pass raw paths so rooting happens exactly once). Paths in
    the JSON are REPO-ROOT-relative — forge joins from the root. -/
def jobJson (package exe : String) (outputs : List String) : String :=
  "  { \"package\": " ++ CodegenCore.Emit.jsonStr package ++ ", \"exe\": " ++ CodegenCore.Emit.jsonStr exe
    ++ ", \"outputs\": [" ++ String.intercalate ", " ((outputs.map CodegenCore.Emit.rootRel).map CodegenCore.Emit.jsonStr) ++ "] }"

/-- The Rust constructor name for a pipeline event label (the enum the
    emitted `step` matches on). -/
def pipelineEventRust : pipeline.Label → String
  | .reflect => "Reflect" | .check => "Check" | .emit => "Emit"
  | .tie => "Tie" | .reset => "Reset"

/-- The Rust expression for a CONCRETE pipeline state. `failed` carries
    arbitrary strings — data can't wildcard it; `tableStep?` handles it
    structurally and so does the arm fold below (it never reaches this
    function). -/
def pipelineStateRust : PipelineState → String
  | .idle => "Idle" | .reflecting => "Reflecting" | .checked => "Checked"
  | .emitted => "Emitted" | .tied => "Tied"
  | .failed _ _ => "Failed { .. }"

/-- The pipeline machine's Rust renderings: state names as-is, event
    ctors QUALIFIED (`PipelineEvent::Check`) — the emitted `match`
    disambiguates against the bare stage names. -/
def pipelineRenderings : Machine.Renderings PipelineState pipeline.Label where
  state := pipelineStateRust
  event := fun e => "PipelineEvent::" ++ pipelineEventRust e

/-- The `step` match arms, folded by the GENERIC fold (`Machine.matchArms`)
    from the PROVED `pipelineTrans` table (not a hand copy of it): one
    arm per non-`reset` row, and — when the `reset` rows send EVERY
    concrete (non-`failed`) state to the same target, which is also the
    structural `failed` arm's target (`tableStep?`: only `reset`
    recovers from `failed`) — a single wildcard arm. The wildcard
    collapse is checked against the table by `matchArms` itself, so the
    emitted Rust stays a function of the proved data. -/
def pipelineArms : List String :=
  Machine.matchArms pipelineRenderings pipelineTrans (some .reset)
    [.idle, .reflecting, .checked, .emitted, .tied]

/-- The pipeline stage machine as Rust: the `PipelineStage` enum + the
    `step` fn, mirroring `Pipeline.pipelineTrans` (+ the structural
    `failed` arm the table can't express — data can't wildcard strings;
    the wildcard fold above covers it exactly when the table justifies
    it). Consumed by forge; the proved agreement (`tableStep?_eq_step?`)
    makes the generated Rust the machine, not a sketch of it. -/
def pipelineRust : String :=
  CodegenCore.Emit.Rust.renderModule
    ([ .comment "GENERATED from SchemaLang.Pipeline (pipelineTrans) — the forge"
    , .comment "driver's stage machine. Agreement with the Lean machine is a"
    , .comment "THEOREM there (tableStep?_eq_step?); do not edit — regenerate."
    , .raw ""
    , .raw "#[derive(Clone, Copy, Debug, PartialEq, Eq)]"
    , .enum "PipelineStage" []
        [ "Idle", "Reflecting", "Checked", "Emitted", "Tied"
        , "Failed { stage: &'static str }" ]
    , .raw ""
    , .raw "#[derive(Clone, Copy, Debug, PartialEq, Eq)]"
    , .enum "PipelineEvent" [] ["Reflect", "Check", "Emit", "Tie", "Reset"]
    , .raw ""
    , .raw "/// The machine's step: None = illegal (guard failed). `Reset` fires"
    , .raw "/// from every state (the recovery edge) — including `Failed`, which"
    , .raw "/// nothing else accepts (the error state is a resting place)."
    , .raw "pub fn step(s: PipelineStage, e: PipelineEvent) -> Option<PipelineStage> {"
    , .raw "    use PipelineStage::*;"
    , .raw "    match (s, e) {"
    ]
    ++ (pipelineArms.map CodegenCore.Emit.Rust.Item.raw)
    ++ [ .raw "        _ => None,"
    , .raw "    }"
    , .raw "}"
    , .raw ""
    , .raw "/// The happy chain: Idle -> Reflecting -> Checked -> Emitted -> Tied"
    , .raw "/// (Lean: `happy_path`, proved by rfl). Illegal = driver bug."
    , .raw "pub fn happy_path_assertions() {"
    , .raw "    use PipelineStage::*;"
    , .raw "    assert_eq!(step(Idle, PipelineEvent::Reflect), Some(Reflecting));"
    , .raw "    assert_eq!(step(Reflecting, PipelineEvent::Check), Some(Checked));"
    , .raw "    assert_eq!(step(Checked, PipelineEvent::Emit), Some(Emitted));"
    , .raw "    assert_eq!(step(Emitted, PipelineEvent::Tie), Some(Tied));"
    , .raw "    assert_eq!(step(Idle, PipelineEvent::Check), None);"
    , .raw "    assert_eq!("
    , .raw "        step(Failed { stage: \"tie\" }, PipelineEvent::Reset),"
    , .raw "        Some(Idle)"
    , .raw "    );"
    , .raw "}"
    ])

def pipelineEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "pipeline"
  style := .doubleSlash
  specSource := "SchemaLang.Pipeline (pipelineTrans + tableStep?_eq_step?)"
  outputs := ["../../src/pipeline_generated.rs"]
  run _ctx :=
    [{ path := "../../src/pipeline_generated.rs"
       contents := pipelineRust }]

/-- The core emitters (everything but the forge-jobs manifest emitter
    itself — the manifest is derived FROM this list, so the manifest
    emitter cannot be in it). Order = write order. -/
def coreEmitters : List (CodegenCore.Emit.Emitter GenCtx) :=
  [ witEmitter
  , flagsWitEmitter
  , rustEmitter
  , SchemaLang.Vortex.Emit.vortexEmitter
  , SchemaLang.Vortex.Emit.extVortexEmitter
  , deltaEmitter
  , deltaWitEmitter
  , changeSpecEmitter
  , SchemaLang.Emit.Invariant.invariantEmitter
  , SchemaLang.Emit.Update.updateEmitter
  , SchemaLang.Emit.Typestate.typestateEmitter
  , SchemaLang.Emit.Machine.orderMachineEmitter
  , pipelineEmitter
  , WitFixture.fixtureEmitter
  , WitFixture.manifestEmitter
  , SchemaLang.Docs.docsEmitter
  ]

/-- The manifest's OWN output path — the one output no core emitter
    declares (breaking the rows → registry → manifest cycle). -/
def forgeJobsOutputPath : String :=
  "../../crates/forge/src/jobs_generated.json"

/-- The forge job rows for THIS package: (exe, outputs). DERIVED from
    the core emitter registry — no hand copy. Adding an emitter to
    `coreEmitters` automatically joins byte-tie; `jobsCoverEmitters_true`
    PROVES the coverage (the old literal copy needed a TEST to catch
    drift — the derivation cannot drift). -/
def forgeJobs : List (String × List String) :=
  [("schema-gen", (coreEmitters.flatMap (·.outputs)) ++ [forgeJobsOutputPath])]

/-- The manifest CONTENT for this package's rows (no header — the driver
    prepends; no brackets — forge unions rows across packages). -/
def forgeJobsLines : List String :=
  forgeJobs.map fun (exe, outputs) => jobJson "schema-lang" exe outputs

def forgeJobsEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "forge-jobs"
  style := .hash
  specSource := "SchemaLang.Emit.Registry (forgeJobs)"
  outputs := ["../../crates/forge/src/jobs_generated.json"]
  run _ctx :=
    [{ path := "../../crates/forge/src/jobs_generated.json"
       contents := "[\n" ++ String.intercalate ",\n" forgeJobsLines ++ "\n]\n" }]

/-- The registry. Order = write order. Declared AFTER every emitter it
    names (forward references don't elaborate). -/
def emitters : List (CodegenCore.Emit.Emitter GenCtx) :=
  coreEmitters ++ [forgeJobsEmitter]

/-- Audit: no two emitters claim the same output path. -/
def pathsUnique : Bool :=
  (emitters.flatMap (·.outputs)).Nodup

/-- Consistency: the job rows cover EXACTLY the registered emitters'
    outputs (no emitter silently outside byte-tie). PROVED: the
    derivation makes this `rfl` — the coverage is no longer a test
    claim but a theorem. -/
def jobsCoverEmitters : Bool :=
  (emitters.flatMap (·.outputs)) == forgeJobs.flatMap (·.2)

theorem jobsCoverEmitters_true : jobsCoverEmitters = true := rfl

/-- 6.5.3 — the emitter self-audit rule-set: constructs NO generated
artifact may contain (checked over raw `run` output; the GENERATED banner
is the driver's prepend, owned by gen-check's byte-tie). One list, so a
new ban is one edit guarding every emitter. The committed artifacts are
clean against these today; the sweep lives in Tests ("emitter
self-audit"). -/
def emitterAuditRules : List TestKit.GateKit.AuditRule :=
  [ { name := "no-todo", pattern := "TODO"
    , why := "unfinished emission leaked into a generated artifact" }
  , { name := "no-fixme", pattern := "FIXME"
    , why := "unfinished emission leaked into a generated artifact" }
  , { name := "no-unwrap", pattern := "unwrap()"
    , why := "generated code must not panic on spec-valid input" }
  , { name := "no-dbg", pattern := "dbg!"
    , why := "debug macro leaked into a generated artifact" }
  , { name := "no-unsafe", pattern := "unsafe "
    , why := "generated code stays in the safe subset" } ]

end SchemaLang.Emit
