/-
# SchemaCore.Emit — the slice's emitter + the shared regen core

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/01-core.md §5 (an emitter IS an
interpretation: the law field is the correspondence, cited); notes/v3/
15-patterns.md #10 (the emitter spine: pure total run, outputs nodup in
the type, drivers own IO); notes/v3/12-construction.md §3.

The emitter reads the universe (`DataRegistry Item`) into ONE artifact:
a WIT record listing at `gen/schema-slice.wit`. The lowering is
`SchemaCore.renderTy` (Ty.lean — the ONE Ty→WIT fold, total over the
closed universe), graded per row there:

- LOSSLESS: bool/u64/i64/string + `option`/`list`/`result` (the
  fragment; `Ty.witLossless` is its data + the distinctness pin).
- RETRACTION-WITH-NOTE (declared loss, 13's "the WIT view is the lossy
  one" row): `map k v` → `list<tuple<K, V>>` (uniqueness/order are
  payload invariants), `set k` → `list<K>` (byte-collides with the
  plain list — pinned), `bounded cap` → `u64` (the cap is schema
  metadata WIT cannot carry — pinned).

THE SUM CASE: the item model is records-only (Item.lean's honest gap —
no variant items), so the sum shape lands via the `result` Ty FIELD
type (the `ExampleEx.status` fixture); when variant items port, the
emitter grows the `variant` decl (the mined legacy mapping,
legacy Emit/Wit.lean's `typeDecl`) and the correspondence table grows
its row.

The LAW (honest at this size): the closed-world naming precondition —
the registry's names are unique (`reg.nodup`, the DataRegistry's own
in-the-type invariant). The driver emits through `runCertified` with
that certificate: the artifact is unemittable without the discharged
law. The fields-nodup fact rides the OBLIGATION row (Item.lean), not
the emitter law — the reflection's guarantee lives in Lean's structure
discipline; carrying it as registry evidence is the row-bridge slice's
work.

`regen` is the ONE copy of the regen semantics: the `schema` driver and
the `gates gen-check` byte-tie both call it — neither re-encodes the
reading.

UPDATE (the byte-tie's theorem upgrade, 09 §2 landed): the `schema`
exe's write path now ALSO emits `SchemaCore.Goldens` (this module's
`goldensBody`) — the committed goldens' Lean-side twin: the artifact
bodies embedded as data, the THEOREMS pinning `emitter … = golden`
(kernel-discharged: `rfl` — the lanes are structural folds), and the
teeth pinning the embedded registry to the LIVE `@[schema]` state at
elaboration. The gate's regen-and-diff stays as the CI shadow; the
three channels together give emitter = committed-file.

Core-only.

The five questions (notes/v3/01-core.md):
- root: Crossing — the universe (`DataRegistry Item`) read into the
  WIT-flavored target grammar.
- carrier grade: the law is the closed-world naming precondition
  (registry nodup) — a discharged certificate through `runCertified`,
  an honest precondition rather than a round trip.
- spine reading: the Interpretation stage (01 §5) — `regen` is the ONE
  fold; the `schema` driver and `gates gen-check` both read it.
- ladder rung: total structural folds; the law rides the obligation
  backend (decidableNow) at the driver.
- gate row: gen-check (the byte-tie over gen/schema-slice.wit) + the
  axiom report (SchemaCore roots).

UPDATE (the Rust lane's landing): the regen core now drives BOTH
emitters — `SchemaCore.Emit.Rust.rustEmitter` joins `witEmitter` in
`regen`'s file list, so the writer (`schema`) and the byte-tie
(`gen-check`) cover the generated Rust crate and the differential
vectors under the same ONE-regen-semantics rule. See the Rust lane's
module header for its law/gap notes.

UPDATE (the WIT AST migration, 07 R1 step 2): `witEmitter` no longer
renders string templates — it lowers the universe into the TYPED WIT
AST (`Wit`, the target-side carrier: the nodup facts ride the type,
malformed WIT shapes are unconstructible) and calls `Wit.Render`, the
ONE renderer (total, AST → text; the text mechanics live there now).
The Ty→WIT lowering is `witTy` (below — the graded lossiness notes
stay with `renderTy` in Ty.lean; `witTy_tie` pins the two lowerings
together, so the AST route renders the graded fold's bytes exactly).
The WIT-invalid shapes (duplicate field names, duplicate record names)
are refused at the construction boundary `witCheckedOfReg` — a decided
refusal, LOUD at the regen core (`regen` refuses before any emission;
the emitter's bare `run` refusal face is the artifact's absence, which
the byte-tie catches). The artifact `gen/schema-slice.wit` is
BYTE-IDENTICAL to the pre-AST emitter's (the gen-check gate is the
proof).
-/

import Lean
import Wit
import Wit.Render
import SchemaCore.Ty
import SchemaCore.Fold
import SchemaCore.Item
import SchemaCore.Register
import SchemaCore.Emit.Rust

open Kit

namespace SchemaCore

/-! ## The WIT AST lowering (the text mechanics live in `Wit.Render`) -/

/-- The map/set KEY's scalar atom (the sub-universe's slice of the WIT
    scalars — the same route `renderKeyTy` takes at the text level;
    the tie lemma below pins the two). -/
def keyScalar : KeyTy → Wit.Scalar
  | .bool => .bool
  | .u64 => .u64
  | .i64 => .i64
  | .string => .string

/-- The key tie: the text-level key fold and the atom spelling agree.
    -/
theorem keyScalar_tie (k : KeyTy) :
    renderKeyTy k = Wit.Render.scalar (keyScalar k) := by
  cases k <;> rfl

/-- The front-merge face: adjacent literal segments fuse under the
    kernel's append reduction (list_tuple_append's base). -/
private theorem list_tuple_append (s : String) :
    "list<" ++ ("tuple<" ++ s) = "list<tuple<" ++ s := rfl

/-- The TYPED Ty→WIT lowering (07 R1 step 1: the lowering instance over
    the closed `Ty` — ONE fold, TOTAL, so exhaustiveness IS the
    change-management system). The graded correspondence rides
    `renderTy`'s rows (Ty.lean — the lossy map/set/bounded notes live
    there, cited, never re-encoded): this fold produces the AST whose
    RENDER is `renderTy`'s text, byte for byte (`witTy_tie` below).
    -/
def witTy : Ty → Wit.Ty
  | .bool => .atom .bool
  | .u64 => .atom .u64
  | .i64 => .atom .i64
  | .string => .atom .string
  | .option t => .option (witTy t)
  | .list t => .list (witTy t)
  | .result ok err => .result (witTy ok) (witTy err)
  -- the lossy rows, as AST shapes: the association-list form (the
  -- declared retraction-with-note), the plain list, the u64 cap loss
  | .map k v => .list (.tuple (.atom (keyScalar k)) (witTy v))
  | .set k => .list (.atom (keyScalar k))
  | .bounded _ => .atom .u64

/-- The literal-split face the map row's tie needs (the kernel reduces
    the front-merged literals; the trailing split needs the assoc
    rearrangement). -/
private theorem wit_map_append (S V : String) :
    ("list<" ++ (("tuple<" ++ S ++ ", " ++ V ++ ">") ++ ">"))
      = ("list<tuple<" ++ S ++ ", " ++ V ++ ">>") := by
  simp [String.append_assoc, list_tuple_append]

/-- THE TIE (the correspondence row, 07 R1 step 3): the typed
    lowering renders to the graded text fold's bytes EXACTLY — the AST
    route and the fold-agent's `witAlg` rows agree on every type, so
    the byte-tie carries over whole. Proven by the fold's OWN law
    (`foldTy_unique` — the initiality route, not a private induction):
    the render∘lowering composition commutes with `witAlg` on every
    ctor, so it IS the fold. -/
theorem witTy_tie : ∀ t : Ty, renderTy t = Wit.Render.ty (witTy t) :=
  fun t =>
    (foldTy_unique (f := fun t => Wit.Render.ty (witTy t))
      rfl rfl rfl rfl
      (fun _ => rfl)
      (fun _ => rfl)
      (fun ok err => by simp [witTy, Wit.Render.ty, witAlg, String.append_assoc])
      (fun k v => by
        show ("list<" ++ ("tuple<" ++ Wit.Render.scalar (keyScalar k) ++ ", "
            ++ Wit.Render.ty (witTy v) ++ ">") ++ ">")
          = ("list<tuple<" ++ renderKeyTy k ++ ", "
            ++ Wit.Render.ty (witTy v) ++ ">>")
        rw [keyScalar_tie]
        exact wit_map_append _ _)
      (fun k => by simp [witTy, Wit.Render.ty, witAlg, keyScalar_tie])
      (fun _ => rfl)
      t).symm

/-- One field's AST (the wire name rides as-is — the mangle lane is
    upstream's). -/
def witField (f : Field) : Wit.Field :=
  { name := f.name, ty := witTy f.ty }

/-- The map-composition face the record construction needs: mapping
    fields through `witField` preserves the name list. -/
theorem witField_names (fs : List Field) :
    (fs.map witField).map Wit.Field.name = fs.map Field.name := by
  simp [witField]

/-! ## The WIT construction boundary (the nodup discipline's runtime
     route) -/

/-- The WIT-checked registry: every item's FIELD names and the items'
    RECORD names (the wire spellings) are distinct — the facts the
    artifact needs, carried in the type (the `DataRegistry` pattern
    one level down: `Wit.Record.fields_nodup` /
    `Wit.Interface.records_nodup` are proof fields; the emitter's
    construction draws the proofs from here, so a malformed item can
    NEVER reach the renderer). The runtime constructor decides both
    facts and refuses loudly — there is no silent acceptance path. -/
structure WitCheckedReg where
  reg : DataRegistry Item
  fields_nodup : ∀ it : Item, it ∈ reg.items →
    (it.fields.map Field.name).Nodup
  wireNames_nodup : (reg.items.map (·.wireName)).Nodup

/-- The SE family — the emit lane's E-codes, allocated from the
    PERSISTED registry (`notes/code-registry.txt`, the spec of record);
    the constants are the declaration, the code-registry gate's
    coverage scan ties the spellings to the live rows. -/
def eSE0001 : Kit.ECode := ⟨"SE0001"⟩
def eSE0002 : Kit.ECode := ⟨"SE0002"⟩

/-- The emit lane's refusal, in the ONE envelope's rendering (05 §4):
    the failure kind rides the registry's SE row; the text keeps the
    channel naming. These are closed-world shape refusals over a
    registry's names (no valid space to enumerate), so the literal Diag
    is the honest shape. -/
def emitDiag (code : Kit.ECode) (message : String) : String :=
  Kit.Diag.toString { code := code, message := message }

/-- The decided constructor (the `registryOfItems` pattern): both
    nodup facts DECIDED, a duplicate name the loud `.error`. -/
def witCheckedOfReg (reg : DataRegistry Item) :
    Except String WitCheckedReg :=
  if hall : reg.items.all
      fun it => decide ((it.fields.map Field.name).Nodup) then
    if hwn : (reg.items.map (·.wireName)).Nodup then
      .ok { reg := reg
          , fields_nodup := fun it hit =>
              of_decide_eq_true (List.all_eq_true.mp hall it hit)
          , wireNames_nodup := hwn }
    else
      .error (emitDiag eSE0001
        (s!"duplicate WIT record names: {reg.items.map (·.wireName)} — "
          ++ "the WIT artifact's record names must be distinct"))
  else
    .error (emitDiag eSE0002 "duplicate field names — every item's field \
      names must be distinct for the WIT artifact (the record's nodup \
      is in the type)")

/-- The checked registry's records: the AST construction, proofs drawn
    from the carried facts (the renderer's input is well-formed BY
    CONSTRUCTION). The recursion carries the membership invariant —
    each element's field-nodup proof is drawn from the registry-level
    fact. -/
private def witRecordsGo (c : WitCheckedReg) :
    (rest : List Item) → (∀ it, it ∈ rest → it ∈ c.reg.items) → List Wit.Record
  | [], _ => []
  | it :: rest, hmem =>
      { name := it.wireName
        fields := it.fields.map witField
        fields_nodup := by
          have h := c.fields_nodup it (hmem it (List.mem_cons_self ..))
          rw [← witField_names] at h
          exact h }
      :: witRecordsGo c rest
            (fun it' hi => hmem it' (List.mem_cons_of_mem _ hi))

/-- The checked registry's records. -/
def witRecords (c : WitCheckedReg) : List Wit.Record :=
  witRecordsGo c c.reg.items (fun _ hi => hi)

/-- The records' names ARE the items' wire names, in order (the
    interface-level nodup's bridge). -/
private theorem witRecordsGo_name_map (c : WitCheckedReg) :
    ∀ (rest : List Item) (hmem : ∀ it, it ∈ rest → it ∈ c.reg.items),
      (witRecordsGo c rest hmem).map Wit.Record.name = rest.map (·.wireName)
  | [], _ => rfl
  | it :: rest, hmem => by
      simp only [witRecordsGo, List.map_cons]
      exact congrArg _ (witRecordsGo_name_map c rest
        (fun it' hi => hmem it' (List.mem_cons_of_mem _ hi)))

theorem witRecords_name_map (c : WitCheckedReg) :
    (witRecords c).map Wit.Record.name = c.reg.items.map (·.wireName) :=
  witRecordsGo_name_map c c.reg.items (fun _ hi => hi)

/-- The artifact's AST: the package + the one `items` interface, the
    records' nodup from the carried fact. -/
def witPackage (c : WitCheckedReg) : Wit.Package :=
  { id := "mandate:slice"
    interfaces :=
      [ { name := "items"
          records := witRecords c
          records_nodup := by
            rw [witRecords_name_map]
            exact c.wireNames_nodup } ] }

/-- The registry → the artifact body (pure, total; the fold over the
    universe into the WIT AST, rendered by `Wit.Render` — the ONE
    renderer). The refusal face (an unchecked registry) is the EMPTY
    body: it is unreachable through the certified lane (`regen`
    decides the check loudly before any emission) and the byte-tie
    fires on any artifact this face could hide. -/
def renderWit (reg : DataRegistry Item) : String :=
  match witCheckedOfReg reg with
  | .ok c => Wit.Render.package (witPackage c)
  | .error _ => ""

/-! ## The emitter -/

/-- The slice's ONE emitter. `outputs_nodup` is in the type (Kit.Emit);
    the law is the registry's closed-world naming invariant — the
    precondition the artifact's item names need (the correspondence
    law's NAME layer; the TYPE layer is renderTy's graded lowering +
    `Ty.witLossless`'s fragment data, pinned in SchemaTests: the
    lossless lowerings pairwise distinct, the lossy rows' collisions
    named, nothing dropped silently). -/
def witEmitter : Kit.Emit.Emitter (DataRegistry Item) where
  name := "schema-wit"
  style := .doubleSlash
  specSource := "SchemaCore.Slice"
  outputs := ["gen/schema-slice.wit"]
  run reg :=
    match witCheckedOfReg reg with
    | .ok c =>
        [{ path := "gen/schema-slice.wit",
           contents := Wit.Render.package (witPackage c) }]
    -- the refusal face: NO artifact (the absence the byte-tie
    -- catches); regen's loud decided check is the driver's route
    | .error _ => []
  law := some fun reg => (reg.items.map reg.nameOf).Nodup

/-! ## The shared regen core -/

/-- The regen result: the registry + the certified files. -/
structure Regen where
  reg : DataRegistry Item
  files : List Kit.Emit.GeneratedFile

/-- The ONE regen semantics, over a replayed environment: read the
    extension state, decide the registry's nodup (loud on duplicates),
    run the emitter through the CERTIFIED lane. Consumers: the `schema`
    exe (the writer) and `gates gen-check` (the byte-tie) — one copy,
    never two. -/
def regen (env : Lean.Environment) : Except String Regen := do
  let reg ← registryOfItems (schemaExt.getState env)
  -- the WIT construction boundary: the record-level nodup facts,
  -- decided LOUDLY before any emission (a malformed registry refuses
  -- here — never silently misrenders)
  let _witChecked ← witCheckedOfReg reg
  let files :=
    witEmitter.runCertified reg reg.nodup ++
    Emit.Rust.rustEmitter.runCertified reg reg.nodup ++
    -- the DUEL's text lane (the manifest): the vectors are the duel
    -- emitter's binaryOutputs (the writer's binary loop; the binary
    -- byte-tie's gate wiring is the named follow-up)
    Emit.Rust.duelEmitter.runCertified reg reg.nodup ++
    -- the COMMIT DUEL's text lane (the bidirectional slice's
    -- differential — the vectors ride the binary loop with the first
    -- duel's)
    commitDuelEmitter.runCertified reg reg.nodup
  return { reg := reg, files := files }

/-! ## The golden module (the byte-tie's theorem face; 09 §2) -/

/-- One char's escaped spelling inside a Lean string literal. -/
def leanEscapeChar : Char → String
  | '\n' => "\\n"
  | '\t' => "\\t"
  | '\\' => "\\\\"
  | '\"' => "\\\""
  | c => String.singleton c

/-- A quoted, escaped Lean string literal for `s`. -/
def leanStrLit (s : String) : String :=
  "\"" ++ String.join (s.toList.map leanEscapeChar) ++ "\""

/-- The `KeyTy` ctor's literal spelling. -/
def keyLeanLit : KeyTy → String
  | .bool => "bool" | .u64 => "u64" | .i64 => "i64" | .string => "string"

/-- A Lean literal for the closed `Ty` (total over the universe; the
    goldens module's `sliceItems` spelling). -/
def tyLeanLit : Ty → String
  | .bool => ".bool"
  | .u64 => ".u64"
  | .i64 => ".i64"
  | .string => ".string"
  | .option t => "(.option " ++ tyLeanLit t ++ ")"
  | .list t => "(.list " ++ tyLeanLit t ++ ")"
  | .result a b => "(.result " ++ tyLeanLit a ++ " " ++ tyLeanLit b ++ ")"
  | .map k v => "(.map ." ++ keyLeanLit k ++ " " ++ tyLeanLit v ++ ")"
  | .set k => "(.set ." ++ keyLeanLit k ++ ")"
  | .bounded n => "(.bounded " ++ toString n ++ ")"

/-- A Lean literal for one field. -/
def fieldLeanLit (f : Field) : String :=
  "{ name := " ++ leanStrLit f.name ++ ", ty := " ++ tyLeanLit f.ty ++ " }"

/-- A Lean literal for one item. -/
def itemLeanLit (it : Item) : String :=
  "{ name := " ++ leanStrLit it.name ++ ", fields := [" ++
  String.intercalate ", " (it.fields.map fieldLeanLit) ++ "] }"

/-- A Lean literal for the item list. -/
def itemsLeanLit (items : List Item) : String :=
  "[" ++ String.intercalate ", " (items.map itemLeanLit) ++ "]"

/-- A Lean literal for a string-chunk list (the rope's `Text.chunks`). -/
def chunksLeanLit (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map leanStrLit) ++ "]"

/-- THE GOLDEN MODULE's body: the regen result rendered as the
    committed goldens' Lean-side twin — the embedded artifact bodies +
    the THEOREMS (`emitter … = golden` — kernel-discharged) + the teeth
    (the pinned registry IS the live registration). Written by the
    `schema` exe next to the artifacts; one writer, one regen. The
    theorem/gate channel contract (09 §2): the theorems prove
    emitter(sliceReg) = golden module; the teeth prove sliceReg = the
    live registry; `gates gen-check` proves the committed files = the
    fresh regen — together emitter = committed file. -/
def goldensBody (reg : DataRegistry Item) : String :=
  let itemsLit := itemsLeanLit reg.items
  let witLit := leanStrLit (renderWit reg)
  let libChunksLit := chunksLeanLit (Text.chunks (Emit.Rust.libRope reg))
  let diffChunksLit := chunksLeanLit (Text.chunks Emit.Rust.differentialRope)
  "-- SchemaCore.Goldens — the committed goldens' Lean-side twin\n-- (the byte-tie upgraded to the proved-theorem channel; notes/v3/09-gates-ops.md §2). GENERATED by the `schema` exe — never hand-edit;\n-- regenerate with `just gen`.\n--\n-- The THREE channels:
-- 1. THE THEOREMS (below, kernel-discharged): the emitters' run over the
--    pinned registry IS the embedded golden — `emitter … = committed-bytes`
--    as proved data, not a diff.
-- 2. THE TEETH (`goldensTeeth`, elaboration-time): the pinned registry IS
--    the live `@[schema]` registration — a universe change without a
--    regen FAILS THE BUILD.
-- 3. THE GATE (`gates gen-check`, the CI shadow): the committed artifact
--    files ARE the fresh regen's bytes. Together: emitter = committed
--    file, by construction and by proof.
import SchemaCore
import SchemaCore.Slice\n\nopen SchemaCore Kit\n\nnamespace SchemaCore.Goldens\n\n/-- The registered items as literals — written by the same regen run\n    that writes the artifacts (the two channels agree by\n    construction). -/\ndef sliceItems : List Item := " ++ itemsLit ++ "\n\n/-- The pinned registry (the theorems' spec value). -/\ndef sliceReg : DataRegistry Item :=\n  { items := sliceItems, nameOf := fun it => it.name, nodup := by decide }\n\n/-- `gen/schema-slice.wit`'s body (the committed artifact minus its\n    2-line GENERATED header — the gate's `tieOf` stripping exactly). -/\ndef goldenWit : String := " ++ witLit ++ "\n\n/-- The lib.rs body's CHUNKS (the rope's `Text.chunks` — the same walk\n    `libRope` renders — so the join is definitional and the kernel\n    never executes it: the monolithic-literal whnf is quadratic in the\n    body and blows the elaboration budget (measured: 5min for the\n    differential alone); the chunk form is the budget-honest rung —\n    this module elaborates in ~12s, dominated by `lib_artifact`'s rope\n    crack — the note 09 §7 asks for). -/\ndef libChunks : List String := " ++ libChunksLit ++ "\n\n/-- `crates/schema-generated/src/lib.rs`'s body = the chunks joined. -/\ndef goldenLib : String := String.join libChunks\n\n/-- The differential body's chunks (`differentialRope`'s walk). -/\ndef diffChunks : List String := " ++ diffChunksLit ++ "\n\n/-- `crates/schema-generated/tests/differential.rs`'s body. -/\ndef goldenDiff : String := String.join diffChunks
\n/-! ## The theorems (the byte-tie upgraded: emitter = golden module) -/\n\nset_option maxRecDepth 100000 in\n/-- THE WIT TIE: the emitter's run over the pinned registry IS the\n    committed golden — kernel-reduced (`rfl`; the WIT lane is fully\n    structural: the typed-AST renderer + `lastName`'s fold). -/\ntheorem wit_artifact :\n    witEmitter.run sliceReg\n      = [{ path := \"gen/schema-slice.wit\", contents := goldenWit }] := rfl\n\nset_option maxRecDepth 100000 in
/-- THE RUST TIE: the second emitter's run IS the two committed Rust
    artifacts' bodies (the codec folds are structural algebras —
    `encAlg`/`decAlg` — so the kernel cracks the whole rope). The
    commit-slice consumer (tests/commit_slice.rs) is a THIRD artifact
    on its OWN emitter — its ONE tie is `gates gen-check` (the duel
    manifest's channel), never a golden rope crack.-/\ntheorem lib_artifact :\n    Emit.Rust.rustEmitter.run sliceReg\n      = [{ path := \"crates/schema-generated/src/lib.rs\", contents := goldenLib },\n         { path := \"crates/schema-generated/tests/differential.rs\",\n           contents := goldenDiff }] := rfl\n\nset_option maxRecDepth 100000 in\n/-- THE DIFFERENTIAL TIE: the differential's body is the committed\n    vector file's bytes, kernel-reduced (all-structural fold +\n    `encVal`'s dependent fold). -/\ntheorem diff_artifact :\n    Emit.Rust.renderDifferential = goldenDiff := rfl\n\n/-! ## The teeth (the live link) -/\n\n/-- BUILD-TIME TEETH: the pinned registry IS the live registration\n    (the replayed `@[schema]` state of the imported `SchemaCore.Slice`).\n    A universe change without `just gen` FAILS THE BUILD here — the\n    theorem channel stays glued to the live registry. -/\nmeta def goldensTeeth : Lean.Elab.Command.CommandElabM Unit := do\n  let env ← Lean.getEnv\n  let items := schemaExt.getState env\n  unless items == sliceItems do\n    throwError \"Goldens: the live `@[schema]` registration drifted from \\\n      the pinned sliceItems — run `just gen` and commit (the golden \\\n      module is generated; never hand-edit)\"\n\n#eval goldensTeeth\n\nend SchemaCore.Goldens\n"

end SchemaCore
