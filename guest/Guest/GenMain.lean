/-
# Guest.GenMain — the manifest discipline (the legacy WasmGenMain's port)

Owner: the gen lane (the mandate tree, `guest/Guest/GenMain.lean`).
Mined from `legacy/lean/wasm-backend/WasmGenMain.lean` (the P1 audit
item): the compile set + the world DERIVE from the registered project
surface, never a hand-maintained list.

## The discipline (what the legacy taught, re-homed)

- **The project manifest is a DECLARED value** (`Manifest` + `mandate`):
  the authoring surface declares the world's NAME and the impl MODULES —
  never a function list.
- **The compile set = the marks** (`compileSetOf`): the
  `LintKit.GuestGate` registry — a def joins when `@[guest]` /
  `@[guest_std]` checked it at elaboration — replayed from the oleans
  by the env-extension replay (`loadEnv`'s `loadExts := true`), bounded
  by the manifest's modules (the legacy `targetDeclsOf` minus the
  intrinsics fold; this tree has no std-intrinsic layer yet, so the
  fold is the raw registry + the module bound + dedup).
- **The world = the honest ABI surface** (`surfaceOf`): every marked
  decl whose type maps into the component lane's `Wit.Scalar` universe
  (`UInt64 → u64`, `Bool → bool`) becomes a world export func under the
  decl's own name (the core export's name — `Guest.lowerFuncs` exports
  it verbatim, so the world and the core module agree by construction).
  A marked decl whose type carries no honest WIT atom (e.g. a `UInt32`
  result — `Wit.Scalar` has no u32) STAYS in the compile set and rides
  the lowered module, but is EXCLUDED from the world and reported: the
  world is the honest surface of what the component actually exports
  (the legacy's kept-list discipline). The legacy's schema-registry
  export authority (`@[schema_fn]` items whose body is the target) has
  no FuncSig registry in this tree yet — the mark + the ABI map is the
  honest minimal; the registry seam lands with SchemaCore's func items.
- **The observability discipline, honest minimal**: the derived surface
  (compile set, world exports, compiled-but-unexported) is REPORTED at
  generation — not emitted as a file. The legacy's
  `observability_generated.rs` had a Rust host consumer; this tree has
  none, and a generated file with no consumer breaks the leftover rule.
  The file emitter lands with its consumer (Gates.Audit's noted row).

## Named exclusions (each with its consumer)

- **the spec/impl module split** — the legacy manifest's `spec-modules`
  (the `@[schema]` surface) has no schema-func registry to serve here;
  one impl-module list is the honest surface. The split returns with
  SchemaCore's func-item registry.
- **the closure-completion fixpoint** — the legacy's undefined-callee
  re-run (gap-4) is `Guest.Lcnf`'s named follow-up (Lower.lean header);
  the manifest fold consumes the marks' own closure only.
- **JSON manifests** — the legacy parsed `project.json`; here the
  manifest is a declared Lean VALUE (the registry discipline: the
  elaborator checks it, the tests construct siblings). A JSON reader is
  a host-authoring convenience with no consumer yet.

The five questions (notes/v3/01-core.md):

- root: Crossing — the project's registered surface (marks + types)
  read into the component lane's inputs (compile set + world).
- carrier grade: none new — the marks ride GuestGate's replayed
  extension; the world rides `Wit.World`'s typed carrier.
- spine reading: the manifest stage of the component lane — the ONE
  derivation both the writer (`componentgen`) and the tests fold.
- ladder rung: rung 1 — total folds over the replayed registry.
- gate row: none new — the driver is the component lane's writer face
  (`gates gen-check` consumes the artifacts through the committed tie).

Consumer trail: `ComponentGenMain.lean` (the writer exe), the
`ComponentTests.Gen` battery (the manifest pins + the growth teeth).
-/

import Lean
import Lean.Compiler.LCNF
import Guest.Lcnf
import Guest.Lower
import LintKit.GuestGate
import Wit.World

namespace Guest.Gen

open Lean Compiler.LCNF

/-! ## The project manifest (the declared authoring surface) -/

/-- The project manifest: the world's name + the impl modules whose
    guest marks ARE the compile surface. A DECLARED value — the
    registry discipline, not a hand list of functions. -/
structure Manifest where
  /-- The WIT world's name (the component boundary's `world <name>`). -/
  world : String
  /-- The impl modules: the `@[guest]`/`@[guest_std]`-marked defs in
      these modules' oleans are the compile set. -/
  implModules : List Lean.Name
deriving Repr, Inhabited

/-- THE mandate project's manifest — the componentgen driver's one
    authoring surface. The fixture module carries the `@[guest]`-marked
    `add64`; the world derives. -/
def mandate : Manifest :=
  { world := "guest", implModules := [`ComponentTests.Fixture] }

/-! ## The compile set (the marks, bounded by the manifest) -/

/-- The compile set: the guest-marked decls (the `LintKit.GuestGate`
    registry, replayed from the manifest's oleans), bounded to the
    manifest's modules, deduped. NO hand list: a new `@[guest]` def in
    a manifest module joins by the registration alone. -/
def compileSetOf (env : Lean.Environment) (m : Manifest) :
    Array Lean.Name :=
  let idxs : List Nat :=
    m.implModules.filterMap (fun mo => (env.getModuleIdx? mo).map (·.toNat))
  (LintKit.GuestGate.guestMarkedDecls env).filter
      (fun n =>
        match env.getModuleIdxFor? n with
        | some i => idxs.contains i.toNat
        | none => false)
    |>.eraseDups.toArray

/-! ## The world (the honest ABI surface of the compile set) -/

/-- The component ABI's WIT face of a guest type (the source-level
    twin of `Guest.Lower`'s scalar map): only the atoms `Wit.Scalar`
    carries honestly. A type outside the map refuses the EXPORT, not
    the compilation — the world is the honest surface. -/
def witTyOf? : Lean.Expr → Option Wit.Ty
  | .const `UInt64 _ => some (.atom .u64)
  | .const `Bool _ => some (.atom .bool)
  | _ => none

/-- Peel a closed forall chain: the binders' names + types, then the
    body (the result type's expr). -/
def peelForalls : Lean.Expr → List (Lean.Name × Lean.Expr) × Lean.Expr
  | .forallE n t b _ =>
      let (ps, body) := peelForalls b
      ((n, t) :: ps, body)
  | e => ([], e)

/-- One target's world func — the fold's step: the decl's OWN name
    (the core export's name; `Guest.lowerFuncs` exports it verbatim),
    the params' user names + mapped WIT types, the mapped result
    (`Unit` → no result; an unmappable type → the fn is world-excluded). -/
def worldFuncOf? (env : Lean.Environment) (n : Lean.Name) :
    Option Wit.Func :=
  match env.find? n with
  | some (.defnInfo di) =>
      let (ps, body) := peelForalls di.type
      match ps.mapM (fun (p, t) =>
          (witTyOf? t).map (fun ty => ({ name := p.toString, ty } : Wit.Field))) with
      | some params =>
          match body with
          | .const `Unit _ =>
              some { name := n.toString, params := params, result := none }
          | _ =>
              match witTyOf? body with
              | some r =>
                  some { name := n.toString, params := params, result := some r }
              | none => none
      | none => none
  | _ => none

/-- The derived surface: the world (the exports the component ABI can
    carry honestly) + the compiled-but-unexported targets (the report's
    honesty row — the legacy's "compiled but unregistered = internal"
    discipline, inverted to name WHY an export is absent). -/
structure Surface where
  world : Wit.World
  excluded : List Lean.Name
deriving Repr, Inhabited

/-- THE world derivation: the manifest's world name + every target's
    world func (first-occurrence order = the compile set's order — the
    registration order replayed from the oleans). The duplicate-name
    refusal is the runtime route of `Wit.World`'s nodup discipline
    (WIT rejects a world exporting one name twice) — the decided
    check CONSTRUCTS the proof or refuses loudly, never silently
    accepts. -/
def surfaceOf (env : Lean.Environment) (m : Manifest)
    (targets : Array Lean.Name) : Except String Surface :=
  let fs := targets.toList.filterMap (worldFuncOf? env ·)
  let excluded :=
    targets.toList.filter
      (fun n => !(fs.any fun f => f.name == n.toString))
  let items := fs.map Wit.Item.func
  let names := items.map Wit.Item.name
  if h : names.Nodup then
    let world : Wit.World :=
      { name := m.world, imports := [], exports := items, exports_nodup := h }
    .ok { world := world, excluded := excluded }
  else
    .error s!"Guest.Gen.surfaceOf: duplicate world export names: {names} \
      (the world exports each name once)"

/-! ## The host faces (the driver's IO: the replay + the LCNF re-run) -/

/-- THE REPLAY DISCIPLINE: the manifest's modules load with the env
    extensions replayed (`loadExts := true` — the guest-mark registry
    comes back populated; `compiler.reuse` disabled — Guest.Lcnf's
    standing option). The refusal is the named envelope. -/
unsafe def loadEnv (m : Manifest) : IO (Except String Lean.Environment) := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.searchPathRef.set (".lake/build/lib/lean" :: (← Lean.searchPathRef.get))
  try
    let env ← Lean.importModules (m.implModules.toArray.map ({ module := · }))
      (opts := lcnfOptions) (loadExts := true)
    return .ok env
  catch e =>
    return .error s!"Guest.Gen.loadEnv: importModules failed: {toString e}"

/-- ONE pipeline run over ALL the targets (the multi-target read —
    `Guest.Lcnf`'s discipline grown for the manifest fold): the
    collected decls feed `Guest.lowerFuncs` (the sibling call lane
    needs them in ONE list). A target that did not compile is the named
    refusal, never a crash. -/
unsafe def readTargets? (env : Lean.Environment) (targets : Array Lean.Name) :
    IO (Except String (List (Decl .impure))) :=
  runLcnf env targets "guest-gen" do
    let mut out : List (Decl .impure) := []
    for t in targets do
      match ← Lean.Compiler.LCNF.getLocalImpureDecl? t with
      | some d => out := out ++ [d]
      | none =>
          return .error
            s!"Guest.Gen.readTargets: no impure-phase LCNF decl for \
               `{t}` — the target did not compile (is it a `def`?)"
    pure (Except.ok out)

end Guest.Gen
