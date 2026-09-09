/-
# SchemaLang.Emit.Registry — the emitter registry (the buf plugin model)

buf's architecture: ONE parsed schema, MANY emitters, each a plugin
that consumes the descriptor and produces files. Here: the universe
(`List Item`, kernel-checked) is the descriptor; an `Emitter` is a
plugin with a name, a comment style, DECLARED output paths (the
one-writer audit surface), and a pure `run` from items to files.

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
import SchemaLang.Emit.Wit
import SchemaLang.Emit.Rust
import SchemaLang.Delta
import SchemaLang.Vortex.Emit
import SchemaLang.Vortex.ExtDType

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

/-- Escape a JSON string (paths + names only — quotes and backslashes
    are the whole story). -/
def jsonStr (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

/-- Package-relative output → repo-root-relative (emitters run with CWD
    = the lean package dir and declare `../..`-paths; forge joins from
    the repo root). -/
def rootRel (p : String) : String :=
  match p.dropPrefix? "../../" with | some rest => rest.toString | none => p

/-- One job row → the JSON object text (paths REPO-ROOT-relative — forge
    joins from the root). -/
def jobJson (package exe : String) (outputs : List String) : String :=
  "  { \"package\": " ++ jsonStr package ++ ", \"exe\": " ++ jsonStr exe
    ++ ", \"outputs\": [" ++ String.intercalate ", " ((outputs.map rootRel).map jsonStr) ++ "] }"

/-- The pipeline stage machine as Rust: the `PipelineStage` enum + the
    `step` fn, mirroring `Pipeline.pipelineTrans` (+ the structural
    `failed` arm the table can't express — data can't wildcard strings).
    Consumed by forge; the proved agreement (`tableStep?_eq_step?`)
    makes the generated Rust the machine, not a sketch of it. -/
def pipelineRust : String :=
  CodegenCore.Emit.Rust.renderModule
    [ .comment "GENERATED from SchemaLang.Pipeline (pipelineTrans) — the forge"
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
    , .raw "        (Idle, Reflect) => Some(Reflecting),"
    , .raw "        (Reflecting, Check) => Some(Checked),"
    , .raw "        (Checked, Emit) => Some(Emitted),"
    , .raw "        (Emitted, Tie) => Some(Tied),"
    , .raw "        (_, Reset) => Some(Idle),"
    , .raw "        _ => None,"
    , .raw "    }"
    , .raw "}"
    , .raw ""
    , .raw "/// The happy chain: Idle -> Reflecting -> Checked -> Emitted -> Tied"
    , .raw "/// (Lean: `happy_path`, proved by rfl). Illegal = driver bug."
    , .raw "pub fn happy_path_assertions() {"
    , .raw "    assert_eq!(step(Idle, PipelineEvent::Reflect), Some(Reflecting));"
    , .raw "    assert_eq!(step(Reflecting, PipelineEvent::Check), Some(Checked));"
    , .raw "    assert_eq!(step(Checked, PipelineEvent::Emit), Some(Emitted));"
    , .raw "    assert_eq!(step(Emitted, PipelineEvent::Tie), Some(Tied));"
    , .raw "    assert_eq!(step(Idle, PipelineEvent::Check), None);"
    , .raw "    assert_eq!(step(Failed { stage: \"tie\" }, PipelineEvent::Reset), Some(Idle));"
    , .raw "}"
    ]

def pipelineEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "pipeline"
  style := .doubleSlash
  specSource := "SchemaLang.Pipeline (pipelineTrans + tableStep?_eq_step?)"
  outputs := ["../../src/pipeline_generated.rs"]
  run _ :=
    [{ path := "../../src/pipeline_generated.rs"
       contents := pipelineRust }]

/-- The forge job rows for THIS package: (exe, outputs). A LITERAL copy
    of the registry's outputs, grouped under the driver exe — the cycle
    (rows → registry → manifest emitter → rows) is broken by the copy,
    and `jobsCoverEmitters` makes the copy's drift a TEST FAILURE: add an
    emitter without a job row and the suite goes red. -/
def forgeJobs : List (String × List String) :=
  [("schema-gen",
    [ "../../wit/gateway.wit"
    , "../../src/schema_generated.rs"
    , "../../src/vortex_generated.rs"
    , "../../src/ext_dtypes_generated.rs"
    , "../../src/delta_generated.rs"
    , "../../wit/delta.wit"
    , "../../src/dbsp_change_generated.rs"
    , "../../src/pipeline_generated.rs"
    , "../../crates/forge/src/jobs_generated.json"
    ])]

/-- The manifest CONTENT for this package's rows (no header — the driver
    prepends; no brackets — forge unions rows across packages). -/
def forgeJobsLines : List String :=
  forgeJobs.map fun (exe, outputs) => jobJson "schema-lang" exe outputs

def forgeJobsEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "forge-jobs"
  style := .hash
  specSource := "SchemaLang.Emit.Registry (forgeJobs)"
  outputs := ["../../crates/forge/src/jobs_generated.json"]
  run _ :=
    [{ path := "../../crates/forge/src/jobs_generated.json"
       contents := "[\n" ++ String.intercalate ",\n" forgeJobsLines ++ "\n]\n" }]

/-- The registry. Order = write order. Declared AFTER every emitter it
    names (forward references don't elaborate). -/
def emitters : List (CodegenCore.Emit.Emitter (List SchemaLang.Item)) :=
  [ witEmitter
  , rustEmitter
  , SchemaLang.Vortex.Emit.vortexEmitter
  , SchemaLang.Vortex.Emit.extVortexEmitter
  , deltaEmitter
  , deltaWitEmitter
  , changeSpecEmitter
  , pipelineEmitter
  , forgeJobsEmitter
  ]

/-- Audit: no two emitters claim the same output path. -/
def pathsUnique : Bool :=
  (emitters.flatMap (·.outputs)).Nodup

/-- Consistency: the job rows cover EXACTLY the registered emitters'
    outputs (no emitter silently outside byte-tie). -/
def jobsCoverEmitters : Bool :=
  (emitters.flatMap (·.outputs)) == forgeJobs.flatMap (·.2)

end SchemaLang.Emit
