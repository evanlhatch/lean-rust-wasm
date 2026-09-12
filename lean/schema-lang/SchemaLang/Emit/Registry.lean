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
import SchemaLang.Pipeline
import SchemaLang.Emit.Wit
import SchemaLang.Emit.Rust
import SchemaLang.Delta
import SchemaLang.Emit.WitFixture
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

/-- The `step` match arms, folded from the PROVED `pipelineTrans` table
    (not a hand copy of it): one arm per non-`reset` row, and — when the
    `reset` rows send EVERY concrete (non-`failed`) state to the same
    target, which is also the structural `failed` arm's target
    (`tableStep?`: only `reset` recovers from `failed`) — a single
    wildcard arm. The wildcard collapse is checked against the table,
    so the emitted Rust stays a function of the proved data. -/
def pipelineArms : List String :=
  let isReset := fun (e : pipeline.Label) => decide (e = .reset)
  let specific := pipelineTrans.filter (fun (e, _, _) => !isReset e)
  let resets := pipelineTrans.filter (fun (e, _, _) => isReset e)
  let armOf := fun (e : pipeline.Label) (f t : PipelineState) =>
    s!"        ({pipelineStateRust f}, PipelineEvent::{pipelineEventRust e}) => Some({pipelineStateRust t}),"
  let concrete : List PipelineState :=
    [.idle, .reflecting, .checked, .emitted, .tied]
  let resetTos := (resets.map fun (_, _, t) => t).eraseDups
  let resetFroms := resets.map fun (_, f, _) => f
  let wildcardOk :=
    match resetTos with
    | [t] => t == PipelineState.idle && concrete.all (resetFroms.contains ·)
    | _ => false
  specific.map (fun (e, f, t) => armOf e f t)
    ++ if wildcardOk then ["        (_, PipelineEvent::Reset) => Some(Idle),"]
       else resets.map fun (_, f, t) => armOf .reset f t

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
    , "../../crates/steel-host/tests/fixtures/wit_fixture_scalars.wit"
    , "../../crates/steel-host/tests/fixtures/wit_fixture_nested.wit"
    , "../../crates/steel-host/tests/fixtures/wit_fixture_variants.wit"
    , "../../crates/steel-host/tests/fixtures/wit_fixture_async.wit"
    , "../../crates/steel-host/tests/fixtures/wit_manifest.json"
    , "../../docs/api.md"
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
  , WitFixture.fixtureEmitter
  , WitFixture.manifestEmitter
  , SchemaLang.Docs.docsEmitter
  ]

/-- Audit: no two emitters claim the same output path. -/
def pathsUnique : Bool :=
  (emitters.flatMap (·.outputs)).Nodup

/-- Consistency: the job rows cover EXACTLY the registered emitters'
    outputs (no emitter silently outside byte-tie). -/
def jobsCoverEmitters : Bool :=
  (emitters.flatMap (·.outputs)) == forgeJobs.flatMap (·.2)

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
