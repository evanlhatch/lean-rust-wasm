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
`emitters`. No driver changes, no SchemaGenMain changes (the driver iterates
the registry). Outputs must be unique across the registry — the audit
test fails the build on a collision, and `forge gen --check` byte-ties
every declared path.

Two of the emitters are FORGE-DRIVER artifacts (see the section below):
the pipeline stage machine forge sequences through, and the job
manifest forge byte-ties from — the driver consumes the Lean spec
instead of a hand-copied stale table.
-/

module

public import CodegenCore
public import Machines.Core
public import SchemaLang.Item
public import SchemaLang.Pipeline
public import SchemaLang.Emit.GenCtx
public import SchemaLang.Emit.Wit
public import SchemaLang.Emit.Rust
public import SchemaLang.Emit.GenRust
public import SchemaLang.Delta
public import SchemaLang.Emit.WitFixture
public import SchemaLang.Emit.WitSweep
public import SchemaLang.Emit.Invariant
public import SchemaLang.Emit.Update
public import SchemaLang.Emit.Machine
public import SchemaLang.Emit.Circuit
public import SchemaLang.Emit.Witness
public import SchemaLang.Emit.Typestate
public import SchemaLang.Vortex.Emit
public import SchemaLang.Vortex.ExtDType
public import SchemaLang.Docs
public import SchemaLang.ModuleDocs

@[expose] public section

namespace SchemaLang.Emit

/-! ## The forge-driver artifacts

forge (crates/forge) is the pipeline's Rust DRIVER. Two artifacts make
it consume the Lean spec instead of a hand-copied stale surface (the
JOBS table it shipped with had DRIFTED — the delta/ext-dtype artifacts
were registered here but never byte-tied there):

1. `pipelineEmitter` — the stage machine as Rust (`PipelineStage` enum +
   `step` fn), mirroring `Pipeline.pipelineTrans` — the table
   `pipelineTableStep?_eq_step?` proves IS the machine. forge steps its own
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
def jobJson (package exe : String) (args : List String) (outputs : List String) : String :=
  let argsField := match args with
    | [] => []
    | _ => [("args", CodegenCore.Emit.Json.arr (args.map CodegenCore.Emit.jsonStr))]
  "  " ++ CodegenCore.Emit.Json.objPad
    ([ ("package", CodegenCore.Emit.jsonStr package)
     , ("exe", CodegenCore.Emit.jsonStr exe) ]
     ++ argsField
     ++ [ ("outputs", CodegenCore.Emit.Json.arr ((outputs.map CodegenCore.Emit.rootRel).map CodegenCore.Emit.jsonStr)) ])

/-- The Rust constructor name for a pipeline event label (the enum the
    emitted `step` matches on). -/
def pipelineEventRust : pipeline.Label → String
  | .reflect => "Reflect" | .check => "Check" | .emit => "Emit"
  | .tie => "Tie" | .reset => "Reset"

/-- The Rust rendering of a pipeline state. The `failed` arm renders
    the ENUM VARIANT DECLARATION (`Failed { stage: &'static str }` —
    the emitted enum derives from this fold via `Machine.moduleRust`);
    `failed` never renders in a match arm (the wildcard covers it), so
    the declaration form is the only rendered one. `failed` carries
    arbitrary strings — data can't wildcard it; `pipelineTableStep?`
    handles the enumerated representative. -/
def pipelineStateRust : PipelineState → String
  | .idle => "Idle" | .reflecting => "Reflecting" | .checked => "Checked"
  | .emitted => "Emitted" | .tied => "Tied"
  | .failed _ _ => "Failed { stage: &'static str }"

/-- The pipeline machine's Rust renderings: state names as-is, event
    ctors QUALIFIED (`PipelineEvent::Check`) — the emitted `match`
    disambiguates against the bare stage names. -/
def pipelineRenderings : Machine.Renderings PipelineState pipeline.Label where
  state := pipelineStateRust
  event := fun e => "PipelineEvent::" ++ pipelineEventRust e

/-- The `step` match arms, folded by the GENERIC fold (`Machine.matchArms`)
    from the PROVED `pipelineTrans` table (machine!-generated, W2.3):
    one arm per non-`reset` row, and — when the `reset` rows send EVERY
    concrete (non-`failed`) state to the same target, which is also the
    structural `failed` arm's target (`pipelineTableStep?`: only `reset`
    recovers from the enumerated `failed`) — a single wildcard arm. The
    wildcard collapse is checked against the table by `matchArms`
    itself, so the emitted Rust stays a function of the proved data.
    (Stands as the citable arms pin — Pipeline.lean's doc references
    it; `pipelineRust` routes through `Machine.moduleRust`, which
    recomputes this same fold internally over the full
    `pipelineStates` — same arms.) -/
def pipelineArms : List String :=
  Machine.matchArms pipelineRenderings pipelineTrans (some .reset)
    [.idle, .reflecting, .checked, .emitted, .tied]

/-- The pipeline stage machine as Rust: the `PipelineStage` enum + the
    `step` fn, mirroring `Pipeline.pipelineTrans` (+ the structural
    `failed` arm the table can't express — data can't wildcard strings;
    the wildcard fold covers it exactly when the table justifies
    it). Consumed by forge; the proved agreement
    (`pipelineTableStep?_eq_step?`) makes the generated Rust the
    machine, not a sketch of it.

    ROUTED THROUGH THE GENERIC FOLD (`Machine.moduleRust`) — the
    hand-rolled item list this replaced duplicated exactly the enum +
    step + assertion module the order machine emits. The pipeline's
    divergent shape is parameterized, not forked: the `Failed` variant
    joins the state enum through `pipelineStates` (the failed
    representative's rendering IS the declaration form), the arms stay
    event-QUALIFIED (`pipelineRenderings` — no event glob, so the enum
    renders bare via `pipelineEventRust`), and the doc'd step fn + the
    happy-path trace ride `stepDoc`/`assertsFn`/`extraAsserts`. The
    emitted bytes are UNCHANGED (byte-tie: the committed
    pipeline_generated.rs golden). -/
def pipelineRust : String :=
  Machine.moduleRust pipelineRenderings pipelineEventRust
    ([ .comment "GENERATED from SchemaLang.Pipeline (pipelineTrans) — the forge"
     , .comment "driver's stage machine. Agreement with the Lean machine is a"
     , .comment "THEOREM there (pipelineTableStep?_eq_step?); do not edit — regenerate." ])
    "PipelineStage" "PipelineEvent"
    pipelineTrans (some .reset) pipelineStates
    []  -- preStep: the pipeline globs NO event (the arms qualify)
    [ .raw "/// The machine's step: None = illegal (guard failed). `Reset` fires"
    , .raw "/// from every state (the recovery edge) — including `Failed`, which"
    , .raw "/// nothing else accepts (the error state is a resting place)." ]
    [ .raw "    use PipelineStage::*;" ]
    [] []  -- happy/rejects: the trace below is the hand-pinned form
    "happy_path_assertions"
    [ .raw "/// The happy chain: Idle -> Reflecting -> Checked -> Emitted -> Tied"
    , .raw "/// (Lean: `happy_path`, proved by rfl). Illegal = driver bug." ]
    [ .raw "    use PipelineStage::*;"
    , .raw "    assert_eq!(step(Idle, PipelineEvent::Reflect), Some(Reflecting));"
    , .raw "    assert_eq!(step(Reflecting, PipelineEvent::Check), Some(Checked));"
    , .raw "    assert_eq!(step(Checked, PipelineEvent::Emit), Some(Emitted));"
    , .raw "    assert_eq!(step(Emitted, PipelineEvent::Tie), Some(Tied));"
    , .raw "    assert_eq!(step(Idle, PipelineEvent::Check), None);"
    , .raw "    assert_eq!("
    , .raw "        step(Failed { stage: \"tie\" }, PipelineEvent::Reset),"
    , .raw "        Some(Idle)"
    , .raw "    );" ]

/-! ## The emission law (the vortex lane's `vortexLaw` shape) -/

/-- The pipeline emitter's law: the table the Rust folds IS the
    machine's `step?` over the enumerated state space — the
    `pipelineTableStep?_eq_step?` agreement riding the emitter (the
    `circuitLaw` precedent: ctx-independent, the machine is module
    data and `run` ignores the ctx). forge steps its driver through
    the emitted Rust; this law is why the emitted `step` is the
    machine, not a sketch of it. -/
def pipelineLaw : GenCtx → Prop := fun _ =>
  ∀ (e : pipeline.Label) (s : PipelineState), s ∈ pipelineStates →
    pipelineTableStep? e s = Machines.Machine.step? pipeline s e

/-- The discharge: the machine!-generated agreement theorem, cited. -/
theorem pipelineLaw_discharged (ctx : GenCtx) : pipelineLaw ctx :=
  fun _ _ hs => pipelineTableStep?_eq_step? _ _ hs

def pipelineEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "pipeline"
  style := .doubleSlash
  specSource := "SchemaLang.Pipeline (pipelineTrans + pipelineTableStep?_eq_step?)"
  outputs := ["../../src/pipeline_generated.rs"]
  run _ctx :=
    [{ path := "../../src/pipeline_generated.rs"
       contents := pipelineRust }]
  law := some pipelineLaw

/-- The core emitters (everything but the forge-jobs manifest emitter
    itself — the manifest is derived FROM this list, so the manifest
    emitter cannot be in it). Order = write order.

    W7.9 phase 2 sweep — the ROUTING CONTRACT: the checked bundle is
    discharged ONCE per universe, at `GenCtx.checkedItems?` (the single
    checkpoint — one `universeCheck` + `universeCheck_sound` transport,
    in GenCtx.lean). Every item-universe consumer routes through it:
    `rustEmitter` consumes the evidence-threaded checked fold
    (`schemaItemsChecked`, its `future`/`stream` arms unrepresentable);
    `genRustEmitter` reads the checkpoint's universe; the WIT/delta
    emitters are SEAM-KEPT with per-emitter justification (partition
    subsets are not `WellFormed`; kind-partition partiality is
    WF-reachable) — see each emitter's header. No emitter re-checks. -/
def coreEmitters : List (CodegenCore.Emit.Emitter GenCtx) :=
  [ witEmitter
  , flagsWitEmitter
  , rustEmitter
  , genRustEmitter
  , SchemaLang.Vortex.Emit.vortexEmitter
  , SchemaLang.Vortex.Emit.extVortexEmitter
  , deltaEmitter
  , deltaWitEmitter
  , changeSpecEmitter
  , SchemaLang.Emit.Invariant.invariantEmitter
  , SchemaLang.Emit.Update.updateEmitter
  , SchemaLang.Emit.Typestate.typestateEmitter
  , SchemaLang.Emit.Machine.orderMachineEmitter
  , SchemaLang.Emit.Circuit.circuitEmitter
  , SchemaLang.Emit.Witness.witnessEmitter
  , pipelineEmitter
  , WitFixture.fixtureEmitter
  , WitFixture.manifestEmitter
  , WitSweep.sweepFixtureEmitter
  , WitSweep.sweepManifestEmitter
  , SchemaLang.Docs.docsEmitter
  , SchemaLang.ModuleDocs.internalsEmitter
  ]

/-- The manifest's OWN output path — the one output no core emitter
    declares (breaking the rows → registry → manifest cycle). -/
def forgeJobsOutputPath : String :=
  "../../crates/forge/src/jobs_generated.json"

/-- The forge job rows for THIS package: (exe, args, outputs). DERIVED from
    the core emitter registry — no hand copy. Adding an emitter to
    `coreEmitters` automatically joins byte-tie; `jobsCoverEmitters_true`
    PROVES the coverage (the old literal copy needed a TEST to catch
    drift — the derivation cannot drift). The exe is the consolidated
    `schema` driver (W1.10) with the subcommand as the args. -/
def forgeJobs : List (String × List String × List String) :=
  [("schema", ["gen"], (coreEmitters.flatMap (·.outputs)) ++ [forgeJobsOutputPath])]

/-- The manifest CONTENT for this package's rows (no header — the driver
    prepends; no brackets — forge unions rows across packages). -/
def forgeJobsLines : List String :=
  forgeJobs.map fun (exe, args, outputs) => jobJson "schema-lang" exe args outputs

/-- The forge-jobs manifest emitter. W7.9 `Emitter.law` sweep — NO law,
    and the reason is structural: the manifest's coverage fact
    (`jobsCoverEmitters_true`, defined AFTER this emitter because the
    coverage quantifies over the registry that includes it) is
    SELF-REFERENTIAL — a law here would quantify over the very emitter
    it decorates. The coverage lives at the registry as a theorem (not
    a test claim), which is the audit the law would carry. -/
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

/- Audit: no two emitters claim the same output path — consumed from
   codegen-core (`Emitter.checkNodup emitters`; identical semantics —
   the inline `(flatMap outputs).Nodup` re-implementation this comment
   replaced was byte-for-byte the same expression, W7.3 phase 2 dedup).
   The ASSERTION lives in Tests ("emitter paths unique"). -/

/-- Consistency: the job rows cover EXACTLY the registered emitters'
    outputs (no emitter silently outside byte-tie). PROVED: the
    derivation makes this `rfl` — the coverage is no longer a test
    claim but a theorem. -/
def jobsCoverEmitters : Bool :=
  (emitters.flatMap (·.outputs)) == forgeJobs.flatMap (·.2.2)

/- The fold grew to ~50 outputs (the seeded WIT sweep joined): the
    kernel's decide needs more than the default 512 recursion steps.
    `maxRecDepth` raised for THIS proof only — the statement is
    unchanged. -/
set_option maxRecDepth 50000 in
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
