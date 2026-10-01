/-
# Guest.Component — the component emission (the world's honest seed)

Owner: the component lane (the mandate tree, `guest/Guest/Component.lean`).
Driving decisions: notes/v3/13-interfaces.md (the WIT worlds row: the
component boundary is the contract) + notes/v3/03 (the boundary
discipline: Lean owns meaning, the artifact carries it — the world is
the SSOT, the component is checked against it at generation) + the
legacy GenMain mining (the component world as the SSOT; the structured
seam: the emission consumes the typed `Wit.World` carrier, never a
string template).

## The honest fragment

The component binary is the component-model's wrapper over the guest's
compiled CORE module (`Guest.Lower`'s output): the component header
(layer 1), the embedded core module (section 1), ONE core instance
(section 2, instantiated with no args), the export-aliases per world
export func plus the canonical-ABI adapter aliases (section 6), the
component type entries (section 7: the defined types + the func
types), the `canon lift` per export (section 8), and the component
exports (section 11).

The canonical-ABI type coverage (the ABI's own flattening rules,
pinned byte-for-byte against the devenv's wasm-tools/wasmtime pair —
the versions that pin the ABI):

- `Wit.Scalar.bool` flattens to the core `i32`; `u64`/`i64` to the
  core `i64` (identity flattening — the `i64` atom rides WIT `s64`,
  the core repr is i64 either way);
- `string` flattens to the `(i32, i32)` pair — the canonical-ABI
  `(ptr, len)` discipline: the bytes live in the component's linear
  memory, UTF-8 (the engine-default encoding; the guest's INTERNAL
  string layout is the boxed-Nat lane's zone — the boundary marshals
  the UTF-8 buffer only);
- `list<T>` flattens to the same `(i32, i32)` pair;
- `tuple<A, B>` flattens to the concatenation of the fields'
  flattening (the record discipline at the func-boundary level: a
  world func's named params ARE the record's fields);
- `option<T>` / `result<ok, err>` prepend the `i32` discriminant to
  the summands' flattening;
- THE HEAP RULES (the ABI's `flatten_function_type`): params
  flattening past `MAX_FLAT_PARAMS` (16) collapse to a single `i32`
  pointer (the args area); results past `MAX_FLAT_RESULTS` (1)
  collapse to a single `i32` (the return-area pointer the callee
  writes and returns — the return area rides the linear memory).

The ADAPTER REQUIREMENT: a func whose types carry a `string`/`list`
or whose flattening goes to the heap needs the canonical-ABI adapters
in the core module — the exported linear `memory` and the
`canonical_abi_realloc` export with the ABI's
`(i32, i32, i32, i32) -> (i32)` signature. `check` refuses
(`adapterMissing`) when the world asks for adapters the module does
not carry; the canon lifts then carry the memory/realloc options. A
func the module cannot back is a named refusal, never a silent wrong
lift. (The LCNF lowering's OWN refusal for string-producing guests is
the boxed-Nat lane's named boundary, not this file's.)

## The skew discipline at generation

`check` is the generation-time refusal: every world export func must
exist in the core module BY NAME (`exportDrift`) and the module's
actual core signature must equal the canonical-ABI flattening of the
world's declared types (`sigDrift`) — now across the composite types
too. An invalid `regen` writes NOTHING (the `wasmSliceEmitter`
discipline: an invalid artifact is a generation failure, never an
artifact).

## Named exclusions (the leftover rule, each with its consumer)

- **imports** — the world's import side is data (`Wit.World.imports`),
  but the emission consumes only the exports (the host's provide-side
  imports land with the first WASI-free imported consumer).
- **interface items** — a world export iface is unrepresented in the
  binary (it needs the instance-export shape); the export-func form is
  the fragment. The carrier keeps both forms honest.
- **multi-result / named results** — unrepresentable in `Wit.Func`
  (the carrier's honest gap).
- **named record/variant TYPES in signatures** — the closed `Ty`
  grammar carries tuples (the flattening-equivalent of the honest
  small record); a NAMED record type in a func signature needs the
  `Ty` grammar's record ctor, which lands with its consumer
  (`Wit`'s header names it).
- **the string-encoding option** — the canon lifts carry the
  memory/realloc options only; UTF-8 is the engine default (pinned:
  the toolchain's own encoder elides it).
- **the component's parse-back / validator** — the binary decoder is
  the binary-decoder order's; the component's validity is pinned at
  the CONSUMER (wasmtime refuses invalid components — the host's
  `EngineRefused` + the string slice's load path) + the
  committed-byte tie (ComponentTests).

Pure module — core-friendly (no `import Lean`; imports `Wit`,
`WasmCore`, `Kit.Emit`/`Kit.Varint`/`Kit.Diag` only). The LCNF re-run
(producing the core module) lives in the driver, not here.

The five questions (notes/v3/01-core.md):
- root: Crossing — the world + the lowered module read into the
  component binary.
- carrier grade: none new — the refusals ride `Kit.Diag` (the ONE
  envelope, the GC-family E-codes); the bytes ride `Kit.Emit`'s
  binary lane.
- spine reading: the artifact stage of the component lane — the ONE
  emitter (`componentEmitter`) every component-writing driver calls;
  the skew check is the validator at generation.
- ladder rung: rung 1 — total folds over closed data; the adapter
  face refuses loudly what the module cannot back.
- gate row: `gates ownership` (the emitters' declared set — the
  orphan face) + the byte-tie pins in ComponentTests (the gen-check
  lane grows with the gate's third-spec integration, named there).
-/

import Kit.Diag
import Kit.Emit
import Kit.Varint
import LintKit.Basic  -- the nolint opt-out attribute (LintKit is core-only)
import Wit
import Wit.Render
import Wit.World
import WasmCore.Encode
import WasmCore.Module
import WasmCore.Types
import WasmCore.Validate

namespace Guest.Component

open Kit.Varint (encVarNat)

/-! ## The spec + the refusal vocabulary (the envelope discipline, 05 §4) -/

/-- The component emitter's spec: the lowered core module + the world
    it must match. -/
structure Spec where
  core : WasmCore.Module
  world : Wit.World
deriving Repr, Inhabited

/-- THE closed-world refusal vocabulary: the component emission's
    failure KINDS as ctors. Closed on purpose (15-patterns #15); the
    E-codes continue the GC family's in-file numbering (the registry
    rows are persisted in notes/code-registry.txt; the retired
    `nonScalarExport` code GC2012 stays spent — the tombstone). -/
inductive ComponentError where
  /-- The world names an export the core module does not carry. -/
  | exportDrift (name : String)
  /-- The module's export signature differs from the world's
      canonical-ABI flattening. -/
  | sigDrift (name : String) (want got : String)
  /-- The world's func needs the canonical-ABI adapters (the linear
      `memory` + the `canonical_abi_realloc` export) the core module
      does not carry (`name` = the func, `what` = the missing face). -/
  | adapterMissing (name : String) (what : String)
  /-- THE IMPORT FACE: the world names an import the core module
      does not carry (the component's import row would dangle). -/
  | importDrift (name : String)
  /-- THE IMPORT FACE: the module's import signature differs from
      the world's canonical-ABI flattening (the skew discipline's
      import face — a provision marshalled against the wrong row). -/
  | importSigDrift (name : String) (want got : String)
  /-- THE IMPORT FACE: the core module imports a function the world
      does not declare (an unprovisioned import — the instantiate
      would refuse at the host; here it refuses at generation). -/
  | importUnclaimed (mod : String) (name : String)
  /-- THE IMPORT FACE: an imported func whose types need the
      canonical-ABI adapter face — outside the import fragment (the
      named boundary; the scalar import lane is the landed face). -/
  | importAdapters (name : String)
deriving Repr, BEq, DecidableEq, Inhabited

/-! The E-code constants (the GC family's continuation; one place,
    the persisted registry is the allocation history). -/
namespace ComponentError

def ecExportDrift : Kit.ECode := ⟨"GC2013"⟩
def ecSigDrift : Kit.ECode := ⟨"GC2014"⟩
def ecAdapterMissing : Kit.ECode := ⟨"GC2015"⟩
def ecImportDrift : Kit.ECode := ⟨"GC2026"⟩
def ecImportSigDrift : Kit.ECode := ⟨"GC2027"⟩
def ecImportUnclaimed : Kit.ECode := ⟨"GC2028"⟩
def ecImportAdapters : Kit.ECode := ⟨"GC2029"⟩

end ComponentError

/-- THE diagnostic envelope: every refusal renders into the ONE Diag —
    the GC-family E-code, the payload in `got`, the named boundary in
    the valid-space slot. -/
def ComponentError.toDiag : ComponentError → Kit.Diag
  | .adapterMissing name what =>
      Kit.Diag.closedWorld ecAdapterMissing
        s!"the canonical-ABI lift of {name} needs the adapter face — \
           {what} is missing from the core module (the string/list \
           types and the heap flattening ride the linear memory + \
           realloc)"
        .error name
        ["an exported `memory`", "an exported `canonical_abi_realloc` \
           : (i32, i32, i32, i32) -> (i32)"]
  | .exportDrift name =>
      Kit.Diag.closedWorld ecExportDrift
        "the world names an export the core module does not carry — \
         the component is the world's contract, not a new surface"
        .error name
        ["a core module export matching the world's func name"]
  | .sigDrift name want got =>
      Kit.Diag.closedWorld ecSigDrift
        s!"the module's export {name} does not match the world's \
           canonical-ABI flattening — the skew discipline refuses at \
           generation"
        .error got
        [want]
  | .importDrift name =>
      Kit.Diag.closedWorld ecImportDrift
        s!"the world names an import {name} the core module does not \
           carry — the component's import row would dangle (the \
           guest's extern must carry the wasm-import resolution)"
        .error name
        ["a core module import matching the world's import func name"]
  | .importSigDrift name want got =>
      Kit.Diag.closedWorld ecImportSigDrift
        s!"the module's import {name} does not match the world's \
           canonical-ABI flattening — the skew discipline's import \
           face refuses at generation"
        .error got
        [want]
  | .importUnclaimed mod name =>
      Kit.Diag.closedWorld ecImportUnclaimed
        s!"the core module imports {mod}.{name} — the world does not \
           declare it (an unprovisioned import: the instantiate would \
           refuse at the host; here it refuses at generation)"
        .error s!"{mod}.{name}"
        ["a world import row declaring the module's import"]
  | .importAdapters name =>
      Kit.Diag.closedWorld ecImportAdapters
        s!"the imported func {name} needs the canonical-ABI adapter \
           face — outside the import fragment (the scalar import lane \
           is the landed face; the composite import lane is the named \
           follow-up)"
        .error name
        ["an imported func over the scalar types (u64/bool — no \
          string/list/heap flattening)"]

/-- The one-line rendering (the envelope's `.toString`). -/
def ComponentError.render (e : ComponentError) : String :=
  Kit.Diag.toString e.toDiag

/-! ## The canonical-ABI type encoding (the composite fragment) -/

/-- The scalar atom's component-model primitive byte (pinned against
    the devenv's wasm-tools: bool 0x7F, u64 0x77, s64 0x78, string
    0x73). The `i64` atom rides WIT `s64` (the core repr is i64
    either way). -/
def ScalarPrim : Wit.Scalar → UInt8
  | .bool => 0x7F
  | .u64 => 0x77
  | .i64 => 0x78
  | .string => 0x73

/-- A component valtype's REFERENCE in a func type: a primitive byte
    (an atom) or a defined-type index (a composite). -/
inductive TyRef where
  | prim (b : UInt8)
  | idx (n : Nat)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The reference's bytes (the primitive, or the s33 index — the
    spec's valtype index encoding; `WasmCore.sleb` is the minimal
    signed LEB, identical to the varint under 64 where every honest
    func's type count lives). -/
def TyRef.bytes : TyRef → List UInt8
  | .prim b => [b]
  | .idx n => WasmCore.sleb n

/-- The canonical-ABI flattening: the core value types a value of the
    type occupies in the linear param/result area. `string`/`list` are
    the `(i32, i32)` (ptr, len) pair; `tuple` concatenates (the record
    discipline); `option`/`result` prepend the `i32` discriminant.
    Total over the closed grammar. -/
def flatOf : Wit.Ty → List WasmCore.ValType
  | .atom .bool => [.i32]
  | .atom .u64 => [.i64]
  | .atom .i64 => [.i64]
  | .atom .string => [.i32, .i32]
  | .list _ => [.i32, .i32]
  | .tuple a b => flatOf a ++ flatOf b
  | .option t => .i32 :: flatOf t
  | .result ok err => .i32 :: (flatOf ok ++ flatOf err)
  | .resultOk ok => .i32 :: flatOf ok
  | .resultErr err => .i32 :: flatOf err
  -- the D2 handle rows: a stream/future/resource handle flattens to
  -- the ONE i32 (the waitable/handle face of the canonical ABI); the
  -- read/write event channels are the deferred half (D2's honest
  -- fragment — the guest lane's emitter never produces these rows
  -- today, SchemaCore's witTy is both-summands and scalar-headed).
  | .stream _ => [.i32]
  | .future _ => [.i32]
  | .own _ | .borrow _ => [.i32]

/-- Does the type's lift/lower touch the linear memory? True iff a
    `string` or a `list` occurs anywhere in it (their values ARE
    `(ptr, len)` into the memory); pure-scalar composites lift in
    registers. -/
def memoryNeeded : Wit.Ty → Bool
  | .atom .string => true
  | .atom _ => false
  | .list _ => true
  | .tuple a b => memoryNeeded a || memoryNeeded b
  | .option t => memoryNeeded t
  | .result ok err => memoryNeeded ok || memoryNeeded err
  | .resultOk ok => memoryNeeded ok
  | .resultErr err => memoryNeeded err
  -- the D2 handle rows: a handle never touches the linear memory
  -- (the value IS the i32 handle; see flatOf's note).
  | .stream _ => false
  | .future _ => false
  | .own _ | .borrow _ => false

/-- The component type encoding of a WIT type at base index `base`:
    the defined-type ENTRIES it contributes (inner types first —
    indices are relative to the block start, so the caller appends the
    block at `base` and every inner reference lands right) + the
    valtype REFERENCE bytes. Total over the closed grammar.
    Pinned against the devenv's wasm-tools: list 0x70, tuple 0x6F,
    option 0x6B, result 0x6A (ok-resultlist + err-resultlist). -/
def tyEncAt : Wit.Ty → Nat → List (List UInt8) × List UInt8
  | .atom s, _ => ([], [ScalarPrim s])
  | .list a, base =>
      let (es, r) := tyEncAt a base
      (es ++ [[0x70] ++ r], encVarNat (base + es.length))
  | .tuple a b, base =>
      let (ea, ra) := tyEncAt a base
      let (eb, rb) := tyEncAt b (base + ea.length)
      (ea ++ eb ++ [[0x6F] ++ encVarNat 2 ++ ra ++ rb],
        encVarNat (base + ea.length + eb.length))
  | .option a, base =>
      let (es, r) := tyEncAt a base
      (es ++ [[0x6B] ++ r], encVarNat (base + es.length))
  | .result ok err, base =>
      let (eo, ro) := tyEncAt ok base
      let (ee, re) := tyEncAt err (base + eo.length)
      (eo ++ ee ++ [[0x6A, 0x01] ++ ro ++ [0x01] ++ re],
        encVarNat (base + eo.length + ee.length))
  -- the D2 rows' one-summand result faces — NOW wasm-tools-pinned
  -- (the D6 fault lane is their first EMITTED consumer; the devenv's
  -- wasm-tools ground truth: `result = 0x6A, ok-opt (0x00 absent |
  -- 0x01 present + valtype), err-opt (the same)` — resultOk u64 =
  -- `6a 01 77 00`, resultErr u64 = `6a 00 01 77`):
  | .resultOk ok, base =>
      let (eo, ro) := tyEncAt ok base
      (eo ++ [[0x6A, 0x01] ++ ro ++ [0x00]], encVarNat (base + eo.length))
  | .resultErr err, base =>
      let (ee, re) := tyEncAt err base
      (ee ++ [[0x6A, 0x00, 0x01] ++ re], encVarNat (base + ee.length))
  -- the D2 waitable/handle rows: the component TYPE descriptors (the
  -- resource/stream/future alias machinery) are the deferred half; the
  -- arm encodes the i32 handle the canonical ABI flattens (the same
  -- face flatOf consumes). The descriptor bytes land with the
  -- resource-emitting consumer.
  | .stream _, _ => ([], [0x7F])
  | .future _, _ => ([], [0x7F])
  | .own _, _ => ([], [0x7F])
  | .borrow _, _ => ([], [0x7F])

/-- The canonical-ABI flattening limits (the ABI's constants). The
    nolint rows: semantically distinct ABI rows whose numeric values
    coincide with unrelated layout constants (the closure object's
    slots) — coincidence, not duplication. -/
@[nolint linter.guestlang.dupDefBodies "the ABI's flat-param limit is its own row — a shared numeric value with the closure layout is coincidence, not duplication"]
def MAX_FLAT_PARAMS : Nat := 16
@[nolint linter.guestlang.dupDefBodies "the ABI's flat-result limit is its own row — a shared numeric value with the RC birth count is coincidence, not duplication"]
def MAX_FLAT_RESULTS : Nat := 1

/-- The flat param count (the fields' concatenation). -/
def flatParamCount (f : Wit.Func) : Nat :=
  (f.params.map (fun p => (flatOf p.ty).length)).foldl (· + ·) 0

/-- The flat result count (0 = no result). -/
def flatResultCount (f : Wit.Func) : Nat :=
  match f.result with
  | none => 0
  | some t => (flatOf t).length

/-- Does the func's canonical-ABI lift need the adapter face? True
    when a type carries a string/list (the `(ptr, len)` values live in
    the memory) or the flattening goes to the heap (params past 16,
    results past 1). -/
def needsAdapters (f : Wit.Func) : Bool :=
  f.params.any (fun p => memoryNeeded p.ty)
    || (match f.result with | some t => memoryNeeded t | none => false)
    || flatParamCount f > MAX_FLAT_PARAMS
    || flatResultCount f > MAX_FLAT_RESULTS

/-- THE canonical-ABI flattening of a world func → the core signature
    the module's export must carry (the ABI's `flatten_function_type`,
    heap rules included). Total over the closed grammar. -/
def flatten (f : Wit.Func) : WasmCore.FuncType :=
  let ps := (f.params.map (fun p => flatOf p.ty)).foldl (· ++ ·) []
  let ps := if ps.length > MAX_FLAT_PARAMS then [.i32] else ps
  match f.result with
  | none => { params := ps, results := [] }
  | some t =>
      let rs := flatOf t
      if rs.length > MAX_FLAT_RESULTS
        then { params := ps, results := [.i32] }
        else { params := ps, results := rs }

/-- The core signature's rendering (the sigDrift message's face). -/
def renderSig (ft : WasmCore.FuncType) : String :=
  "(" ++ String.intercalate ", " (ft.params.map WasmCore.renderValType) ++ ")"
    ++ " -> (" ++ String.intercalate ", " (ft.results.map WasmCore.renderValType) ++ ")"

/-! ## The adapter face (the module side of the canonical ABI) -/

/-- The ABI realloc's signature: (original ptr, original size,
    alignment, new size) → the new ptr — all i32. -/
def reallocTy : WasmCore.FuncType :=
  { params := [.i32, .i32, .i32, .i32], results := [.i32] }

/-- The module exports its linear memory under the ABI's name. -/
def hasMemoryExport (m : WasmCore.Module) : Bool :=
  m.exports.any (fun e =>
    e.name == "memory"
      && match e.desc with | .memory _ => true | .func _ => false)

/-- The module exports `canonical_abi_realloc` as a FUNC with the
    ABI realloc's signature. -/
def hasReallocExport (m : WasmCore.Module) : Bool :=
  match m.exports.find? (fun e => e.name == "canonical_abi_realloc") with
  | some e =>
      match e.desc with
      | .func idx =>
          match m.funcs[idx]? with
          | some f => match m.types[f.tyIdx]? with
              | some t => t == reallocTy
              | none => false
          | none => false
      | .memory _ => false
  | none => false

/-! ## The skew check at generation -/

/-- The module's exported func type of a name (the export must be a
    func whose type index resolves). -/
def moduleFuncType? (m : WasmCore.Module) (name : String) :
    Option WasmCore.FuncType :=
  match m.exports.find? (fun e => e.name == name) with
  | some e =>
      match e.desc with
      | .func idx =>
          -- THE IMPORT FACE's resolution: the export's index is
          -- ABSOLUTE — `Module.funcAt` (the import-resolved externs
          -- occupy 0..k-1; a local func's index is the shifted one)
          match m.funcAt idx with
          | some f => m.types[f.tyIdx]?
          | none => none
      | .memory _ => none
  | none => none

/-- THE skew check at generation: every world export func must (1)
    exist in the core module BY NAME, (2) carry the canonical-ABI
    flattened signature exactly (the composite flattening + the heap
    rules), and (3) when its types need the adapter face, find the
    memory + realloc exports in the module. The ok value: the world's
    export funcs in order with their flattened types (the emission's
    index discipline consumes it). -/
def check (m : WasmCore.Module) (w : Wit.World) :
    Except ComponentError (List (Wit.Func × WasmCore.FuncType)) :=
  let exportFuncs :=
    w.exports.filterMap (fun i => match i with | .func f => some f | .iface _ => none)
  exportFuncs.mapM fun f =>
    let ft := flatten f
    match moduleFuncType? m f.name with
    | none => .error (.exportDrift f.name)
    | some mft =>
        if mft != ft then .error (.sigDrift f.name (renderSig ft) (renderSig mft))
        else if needsAdapters f then
          if hasMemoryExport m then
            if hasReallocExport m then .ok (f, ft)
            else .error (.adapterMissing f.name "the canonical_abi_realloc export")
          else .error (.adapterMissing f.name "the exported linear memory")
        else .ok (f, ft)

/-! ## THE IMPORT FACE's skew check at generation -/

/-- THE IMPORT FACE's skew check at generation: the world's import
    funcs against the core module's imports — (1) every world import
    func exists in the module BY NAME (the core import's name field —
    the ONE name, two faces: the WIT row + the core wire row),
    (2) the module's import signature equals the canonical-ABI
    flattening of the world's declared types (the skew discipline's
    import face), (3) the flattening needs no adapter face (the
    scalar import lane is the landed face), and (4) every core import
    is claimed by the world (an unclaimed import is the unprovisioned
    boundary — the instantiate would refuse at the host; here it
    refuses at generation, nothing written). The ok value: the
    world's import funcs in order (the emission's index discipline
    consumes it). -/
def checkImports (m : WasmCore.Module) (w : Wit.World) :
    Except ComponentError (List Wit.Func) :=
  let importFuncs := w.imports.filterMap
    (fun i => match i with | .func f => some f | .iface _ => none)
  let claimed := importFuncs.map (·.name)
  let world (name : String) : Bool := claimed.contains name
  -- (4) every core import claimed by the world
  match m.imports.filter (fun i => !world i.name) |>.head? with
  | some i => .error (.importUnclaimed i.mod i.name)
  | none =>
    importFuncs.mapM fun f =>
      let ft := flatten f
      if needsAdapters f then .error (.importAdapters f.name)
      else
        match m.imports.find? (fun i => i.name == f.name) with
        | none => .error (.importDrift f.name)
        | some imp =>
            match m.types[imp.tyIdx]? with
            | none => .error (.importDrift f.name)
            | some mft =>
                if mft != ft then
                  .error (.importSigDrift f.name (renderSig ft)
                    (renderSig mft))
                else .ok f

/-! ## The component binary encoding -/

/-- The component header: the wasm magic + version 1 LAYER 1 (the
    component encoding's `0x0d 0x00 0x01 00`). -/
def componentHeader : List UInt8 :=
  [0x00, 0x61, 0x73, 0x6D, 0x0D, 0x00, 0x01, 0x00]

/-- A section: id + length-prefixed content (the same framing as the
    core format — `WasmCore.Encode.encodeSection`'s shape). -/
def encSection (id : UInt8) (content : List UInt8) : List UInt8 :=
  id :: (encVarNat content.length ++ content)

/-- An extern name (the component export's `0x00`-prefixed string). -/
def encExternName (s : String) : List UInt8 :=
  let bs := s.toByteArray.toList
  0x00 :: (encVarNat bs.length ++ bs)

/-- A plain name (the alias's string: length-prefixed, no prefix
    byte). -/
def encPlainName (s : String) : List UInt8 :=
  let bs := s.toByteArray.toList
  encVarNat bs.length ++ bs

/-- The embedded core module section (section 1). -/
def encodeCoreModuleSection (m : WasmCore.Module) : List UInt8 :=
  encSection 0x01 (WasmCore.encodeModule m)

/-- The core instance section (section 2): ONE instance — the embedded
    module, instantiated with no args (the no-import face; the
    byte-tie's exact bytes). -/
def encodeCoreInstanceSection : List UInt8 :=
  encSection 0x02 [0x01, 0x00, 0x00, 0x00]

/-- The distinct module names, first-occurrence order (the
    instantiate args' grouping). -/
def distinctMods : List String → List String :=
  List.foldl (fun acc m => if acc.contains m then acc else acc ++ [m]) []

/-- THE IMPORT FACE's core instances (section 2, TWO entries —
    pinned against the devenv's wasm-tools): the shim instance
    (`FromExports` — one core-func export per lowered import, under
    the core import's NAME) and the guest instance (the embedded
    module instantiated with one arg per distinct module name, each
    naming the shim instance — the arg's sort byte 0x12, the
    core-instance sort; the arg name matches the core import's
    MODULE name). -/
def encodeCoreInstanceSectionImports (mods : List String)
    (coreNames : List String) : List UInt8 :=
  let shim := [0x01] ++ encVarNat coreNames.length
    ++ ((coreNames.zipIdx.map (fun p =>
          encPlainName p.1 ++ [0x00] ++ encVarNat p.2)).foldl (· ++ ·) [])
  let inst := [0x00, 0x00] ++ encVarNat mods.length
    ++ ((mods.map (fun md => encPlainName md ++ [0x12, 0x00])).foldl (· ++ ·) [])
  encSection 0x02 ([0x02] ++ shim ++ inst)

/-- One export-alias entry: core func `i`'s slot in the instance's
    export table (the world export's name selects it); `inst` = the
    guest core instance's index (0 with no imports, 1 with — the shim
    instance takes slot 0). -/
def encodeAliasEntry (inst : Nat) (name : String) : List UInt8 :=
  [0x00, 0x00, 0x01] ++ encVarNat inst ++ encPlainName name

/-- The adapter aliases (pinned against the devenv's wasm-tools): the
    realloc alias — core func index `n` (after the world's funcs) —
    and the memory alias — core memory index 0 (the sort byte 0x02;
    the funcs ride 0x00). `inst` = the guest core instance's index. -/
def encodeAdapterAliases (inst : Nat) : List UInt8 :=
  ([0x00, 0x00, 0x01] ++ encVarNat inst) ++ encPlainName "canonical_abi_realloc"
    ++ ([0x00, 0x02, 0x01] ++ encVarNat inst) ++ encPlainName "memory"

/-- The alias section (section 6): one core-func alias per world
    export func, in order (the aliased core func index = the alias's
    position + `base` — the canon-lowERED import funcs take 0..k-1
    before them), plus the adapter aliases when ANY export func needs
    them. -/
def encodeAliasSection (fs : List Wit.Func) (base : Nat) (inst : Nat) :
    List UInt8 :=
  let names := fs.map (·.name)
  let anyAdapters := fs.any needsAdapters
  let count := names.length + (if anyAdapters then 2 else 0)
  encSection 0x06 (encVarNat count
    ++ (names.map (encodeAliasEntry inst)).foldl (· ++ ·) []
    ++ (if anyAdapters then encodeAdapterAliases inst else []))

/-- The params' encoding fold: the defined-type entries in order +
    each param's full bytes (the plain name + the valtype reference)
    at its accumulated base. -/
def paramsEncGo : List Wit.Field → Nat →
    List (List UInt8) × List (List UInt8)
  | [], _ => ([], [])
  | p :: rest, base =>
      let (es, r) := tyEncAt p.ty base
      let (restEs, restBs) := paramsEncGo rest (base + es.length)
      (es ++ restEs, (encPlainName p.name ++ r) :: restBs)

/-- One func's type entries at base: the defined types (params then
    result, inner first) + the func type entry itself; the func
    type's index is `base` + the defined count. -/
def funcTyEntry (f : Wit.Func) (base : Nat) :
    List (List UInt8) × Nat :=
  let (pes, pbs) := paramsEncGo f.params base
  let resBase := base + pes.length
  let (resEs, resBytes) :=
    match f.result with
    | none => ([], [0x01, 0x00])
    | some t =>
        let (es, r) := tyEncAt t resBase
        (es, [0x00] ++ r)
  let entries := pes ++ resEs
  let entry := [0x40] ++ encVarNat f.params.length
    ++ (pbs.foldl (· ++ ·) []) ++ resBytes
  -- the func type's index: AFTER the block's defined types (the spec's
  -- valtype indices are relative to the block start, so the entry lands
  -- at base + the defined count — a `- 1` here would mis-index every
  -- lift past the first func; the single-func cases truncated to 0 and
  -- masked it, the five-func parity set did not)
  (entries ++ [entry], base + entries.length)

/-- The type section's full entry list + each func type's index (the
    canon section's operand). The defined types precede the func
    types (the pinned encoding's index discipline). -/
def funcsTyEnc : List Wit.Func → Nat → List (List UInt8) × List Nat
  | [], _ => ([], [])
  | f :: rest, base =>
      let (es, idx) := funcTyEntry f base
      let (restEs, restIdxs) := funcsTyEnc rest (base + es.length)
      (es ++ restEs, idx :: restIdxs)

/-- The canon section's lift options for one func: memory (core
    memory 0 — the adapter alias) + realloc (core func `n` — after the
    world's funcs) when the func needs the adapters; empty otherwise
    (the pure-scalar lift carries no options). UTF-8 is the engine's
    default string encoding — the option is elided (pinned). -/
def canonOpts (f : Wit.Func) (n : Nat) : List UInt8 :=
  if needsAdapters f then
    [0x03, 0x00] ++ ([0x04] ++ encVarNat n)
  else []

/-- The canon section (section 8): one `canon lift` per export func —
    the lift operand (0x00 0x00: the core-sort lift), the aliased core
    func (the position + `base` — the canon-lowERED import funcs take
    0..k-1 before them), the options (the realloc alias's core func
    index = `base` + the export count), the component func type (past
    the defined types + the import types). -/
def encodeCanonSection (fs : List Wit.Func) (tyIdxs : List Nat) (base : Nat) :
    List UInt8 :=
  let n := fs.length
  let entries := (fs.zip (List.range n)).zip tyIdxs
  encSection 0x08 (encVarNat n
    ++ (entries.map (fun p =>
          let opts := canonOpts p.1.1 (base + n)
          [0x00, 0x00] ++ encVarNat (base + p.1.2)
            ++ encVarNat (if needsAdapters p.1.1 then 2 else 0)
            ++ opts ++ encVarNat p.2)).foldl (· ++ ·) [])

/-- One component export entry: the extern name, kind func (0x01), the
    lifted func index, no ascribed type. -/
def encodeExportEntry (i : Nat) (name : String) : List UInt8 :=
  encExternName name ++ [0x01] ++ encVarNat i ++ [0x00]

/-- THE IMPORT FACE's canon-lower section (the 0x08 section's LOWER
    face): one `canon lower` per world import func — the sort byte
    0x01, the core-sort marker 0x00, the imported func's index, no
    options (the scalar import lane) — pinned against the devenv's
    wasm-tools (`01 00 00 00` for the first). -/
def encodeCanonLowerSection (n : Nat) : List UInt8 :=
  encSection 0x08 (encVarNat n
    ++ (((List.range n).map
          (fun j => [0x01, 0x00] ++ encVarNat j ++ [0x00])).foldl (· ++ ·) []))

/-- The export section (section 11): the lifted funcs, in order (the
    component func index = the position + `base` — the imported funcs
    take 0..k-1 before them). -/
def encodeExportSection (names : List String) (base : Nat) : List UInt8 :=
  encSection 0x0B (encVarNat names.length
    ++ (((List.range names.length).zip names).map
          (fun p => encodeExportEntry (base + p.1) p.2)).foldl (· ++ ·) [])

/-- THE IMPORT FACE's import section (section 0x0A): one entry per
    world import func — the extern name, kind func (0x01), the type
    index (its position — the import types open the type section).
    The import entry carries NO ascribed-type byte (the export entry's
    trailing 0x00 is the EXPORT section's shape — the pinned dump:
    `00 <len> <name> 01 00`, three fields, nothing after). -/
def encodeImportSection (fs : List Wit.Func) : List UInt8 :=
  encSection 0x0A (encVarNat fs.length
    ++ ((List.range fs.length).zip fs
          |>.map (fun p => encExternName p.2.name ++ [0x01] ++ encVarNat p.1)
          |>.foldl (· ++ ·) []))

/-- THE component emission: check the skew at generation FIRST (an
    invalid pair is a refusal, never an artifact), then the total
    binary fold. The NO-IMPORT path's sections in ascending id order
    (1, 2, 6, 7, 8, 11 — the byte-tie's exact bytes). THE IMPORT FACE
    adds: the type section (import types OPEN it — their indices are
    the import entries' operands), the import section (0x0A), the
    canon LOWERS (the import funcs cross into core), and the shim
    core instance the instantiate args name — sections 1, 7, 0x0A, 8,
    2, 6, 8, 11 (the import lane's ordering is index-correct: types
    before imports, imports before lowers, lowers before the shim
    instance, the shim before the guest instance the aliases
    consume). -/
def encodeComponent (m : WasmCore.Module) (w : Wit.World) :
    Except ComponentError (List UInt8) :=
  match check m w, checkImports m w with
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok fs, .ok ifs =>
      let names := fs.map (fun p => p.1.name)
      let coreNames := ifs.map (·.name)
      let mods := distinctMods (m.imports.map (·.mod))
      let k := ifs.length
      let (impTyEntries, _) := funcsTyEnc ifs 0
      let (tyEntries, tyIdxs) := funcsTyEnc (fs.map (·.1)) k
      .ok (componentHeader
        ++ encodeCoreModuleSection m
        -- the type section: the import types + the export types (one
        -- section; the import entries' operands are the import types'
        -- positions) — BEFORE the import section, the types' consumer
        ++ (if k = 0 then []
            else encSection 0x07 (encVarNat (impTyEntries.length + tyEntries.length)
                   ++ ((impTyEntries ++ tyEntries).foldl (· ++ ·) [])))
        ++ (if k = 0 then [] else encodeImportSection ifs)
        ++ (if k = 0 then [] else encodeCanonLowerSection k)
        ++ (if k = 0 then encodeCoreInstanceSection
            else encodeCoreInstanceSectionImports mods coreNames)
        ++ encodeAliasSection (fs.map (·.1)) k (if k = 0 then 0 else 1)
        ++ (if k = 0 then
              encSection 0x07 (encVarNat tyEntries.length
                 ++ (tyEntries.foldl (· ++ ·) []))
              else [])
        ++ encodeCanonSection (fs.map (·.1)) tyIdxs k
        ++ encodeExportSection names k)

/-! ## The artifact spine (the ONE emitter family) -/

/-- The component slice's artifact emitter: the world text
    (`Render.worldFile`'s render face) + the component bytes
    (`gen/component-slice.wasm` + the `.hdr` sidecar — the binary
    lane's discipline). The paths are LITERALS here (the one-writer
    rule: the emitter's nodup facts ride the type via `decide` over
    the concrete paths, so the emitter is declared per artifact set,
    never parameterized over runtime strings). The driver runs
    `regen` (the skew check rides it), never the raw `runBinary` — an
    unchecked pair produces no artifact. -/
def componentEmitter : Kit.Emit.Emitter Spec where
  name := "guest.component"
  style := .doubleSlash
  specSource := "Guest.Component"
  outputs := ["gen/component-slice.wit"]
  run := fun s =>
    [{ path := "gen/component-slice.wit"
     , contents := Wit.Render.worldFile "mandate:guest" s.world }]
  binaryOutputs := ["gen/component-slice.wasm", "gen/component-slice.wasm.hdr"]
  runBinary := some fun s =>
    match encodeComponent s.core s.world with
    | .ok bs =>
        [{ path := "gen/component-slice.wasm"
         , contents := ByteArray.mk bs.toArray }]
    | .error _ => []
  rev := "component-slice-r1"
  reads := [`Wit.World, `WasmCore.Encode]

/-- The STRING slice's emitter: the same emission over the string
    lane's committed artifact set (the hand-built adapter-face
    fixture `ComponentTests.StringFixture.stringModule` — the LCNF
    lowering's string refusal is the boxed-Nat lane's named
    boundary). The literal-path discipline is the scalar emitter's. -/
def stringComponentEmitter : Kit.Emit.Emitter Spec where
  name := "guest.stringComponent"
  style := .doubleSlash
  specSource := "Guest.Component"
  outputs := ["gen/component-string-slice.wit"]
  run := fun s =>
    [{ path := "gen/component-string-slice.wit"
     , contents := Wit.Render.worldFile "mandate:guest" s.world }]
  binaryOutputs := ["gen/component-string-slice.wasm", "gen/component-string-slice.wasm.hdr"]
  runBinary := some fun s =>
    match encodeComponent s.core s.world with
    | .ok bs =>
        [{ path := "gen/component-string-slice.wasm"
         , contents := ByteArray.mk bs.toArray }]
    | .error _ => []
  rev := "component-string-slice-r1"
  reads := [`Wit.World, `WasmCore.Encode]

/-- The EDGE slice's emitter: the same emission over the edgepython
    frontend's parity set (`ComponentTests.EdgeFixture.edgeSpec` —
    `Guest.EdgePython.Fe.compileModule`'s product, pure, no LCNF
    re-run; the world's five u64-scalar exports need no adapter face).
    The literal-path discipline is the scalar emitter's. The wasmtime
    consumer: `crates/mandate-host`'s edge lane (the parity points'
    typed calls — the frontend-agnosticism's runtime proof: the SAME
    harness runs the LCNF lane's and this lane's output). -/
def edgeComponentEmitter : Kit.Emit.Emitter Spec where
  name := "guest.edgeComponent"
  style := .doubleSlash
  specSource := "Guest.Component"
  outputs := ["gen/component-edge-slice.wit"]
  run := fun s =>
    [{ path := "gen/component-edge-slice.wit"
     , contents := Wit.Render.worldFile "mandate:guest" s.world }]
  binaryOutputs := ["gen/component-edge-slice.wasm", "gen/component-edge-slice.wasm.hdr"]
  runBinary := some fun s =>
    match encodeComponent s.core s.world with
    | .ok bs =>
        [{ path := "gen/component-edge-slice.wasm"
         , contents := ByteArray.mk bs.toArray }]
    | .error _ => []
  rev := "component-edge-slice-r1"
  reads := [`Wit.World, `WasmCore.Encode]

/-- The FAULT slice's emitter: the same emission over the fault lane's
    committed artifact set (the hand-built heap-return fixture
    `ComponentTests.FaultFixture.faultModule` — the D6 port's
    typed-refusal channel: `probe : func() -> result<_, u64>`, the
    flattening's heap collapse past `MAX_FLAT_RESULTS`). The
    literal-path discipline is the scalar emitter's. The wasmtime
    consumer: `crates/mandate-host`'s fault lane (the guest's `Err`
    crossing as the host's TYPED error — never a trap). -/
def faultComponentEmitter : Kit.Emit.Emitter Spec where
  name := "guest.faultComponent"
  style := .doubleSlash
  specSource := "Guest.Component"
  outputs := ["gen/component-fault-slice.wit"]
  run := fun s =>
    [{ path := "gen/component-fault-slice.wit"
     , contents := Wit.Render.worldFile "mandate:guest" s.world }]
  binaryOutputs := ["gen/component-fault-slice.wasm", "gen/component-fault-slice.wasm.hdr"]
  runBinary := some fun s =>
    match encodeComponent s.core s.world with
    | .ok bs =>
        [{ path := "gen/component-fault-slice.wasm"
         , contents := ByteArray.mk bs.toArray }]
    | .error _ => []
  rev := "component-fault-slice-r1"
  reads := [`Wit.World, `WasmCore.Encode]

/-- The WITNESS slice's emitter: the same emission over the host-gating
    lane's committed artifact set (the hand-built checker module
    `ComponentTests.WitFixture.witGateModule` — the pinned invariant's
    checker as an export: `witness-gate : func(src, dst, amount, t1,
    b1, t2, t3, b3: u64) -> result<_, u64>`, the heap-return face). The
    literal-path discipline is the scalar emitter's. The wasmtime
    consumer: `crates/mandate-host`'s witness lane (the guest-compiled
    checker GATES the host's commit — the legacy `@[invariant]`
    discipline; a refusal crosses as the host's TYPED error, never a
    trap). -/
def witComponentEmitter : Kit.Emit.Emitter Spec where
  name := "guest.witComponent"
  style := .doubleSlash
  specSource := "Guest.Component"
  outputs := ["gen/component-witness-slice.wit"]
  run := fun s =>
    [{ path := "gen/component-witness-slice.wit"
     , contents := Wit.Render.worldFile "mandate:guest" s.world }]
  binaryOutputs := ["gen/component-witness-slice.wasm", "gen/component-witness-slice.wasm.hdr"]
  runBinary := some fun s =>
    match encodeComponent s.core s.world with
    | .ok bs =>
        [{ path := "gen/component-witness-slice.wasm"
         , contents := ByteArray.mk bs.toArray }]
    | .error _ => []
  rev := "component-witness-slice-r1"
  reads := [`Wit.World, `WasmCore.Encode]

/-- The IMPORT slice's emitter: the same emission over the import
    lane's committed artifact set (the hand-built import fixture —
    `ComponentTests.ImportFixture.importSpec` — the guest's `add64`
    calling the imported `host-add`, the world's import row + the
    component's import section + the host's provision: THE IMPORT
    DISCIPLINE's full vertical). The literal-path discipline is the
    scalar emitter's. The wasmtime consumer:
    `crates/mandate-host`'s import lane (the root provision's
    `func_wrap`, the value crossing the boundary). -/
def importComponentEmitter : Kit.Emit.Emitter Spec where
  name := "guest.importComponent"
  style := .doubleSlash
  specSource := "Guest.Component"
  outputs := ["gen/component-import-slice.wit"]
  run := fun s =>
    [{ path := "gen/component-import-slice.wit"
     , contents := Wit.Render.worldFile "mandate:guest" s.world }]
  binaryOutputs := ["gen/component-import-slice.wasm",
                    "gen/component-import-slice.wasm.hdr"]
  runBinary := some fun s =>
    match encodeComponent s.core s.world with
    | .ok bs =>
        [{ path := "gen/component-import-slice.wasm"
         , contents := ByteArray.mk bs.toArray }]
    | .error _ => []
  rev := "component-import-slice-r1"
  reads := [`Wit.World, `WasmCore.Encode]

/-- THE regen — the writer's and the tests' ONE copy (the
    `WasmCore.regen` discipline): the skew check runs AT GENERATION
    (the export face AND the import face); a refusal carries the
    rendered Diag and writes NOTHING. -/
def regen (s : Spec) :
    Except String (List Kit.Emit.GeneratedFile × List Kit.Emit.BinaryFile) :=
  match check s.core s.world, checkImports s.core s.world with
  | .error e, _ => .error (ComponentError.render e)
  | _, .error e => .error (ComponentError.render e)
  | .ok _, .ok _ =>
      .ok (componentEmitter.run s, (componentEmitter.runBinary).getD (fun _ => []) s)

end Guest.Component
