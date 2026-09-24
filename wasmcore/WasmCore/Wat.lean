/-
# WasmCore.Wat — the WAT text rendering (07-extensibility R1's text face)

The typed target AST ALREADY EXISTS — wasmcore's `Instr`/`Module` are
it; this module is its text face: a total, structural fold of the
module into WAT text (the s-expression grammar the wasm toolchain
consumes). Nothing here re-declares a target universe (R1 step 2 is
satisfied by the one-AST discipline), and the op SPELLINGS are never
spelled here: every op/mem-op line rides `WasmCore.OpTable`'s `name`
field — the ONE op table's fold (07 R6: no parallel spelling table;
legacy's `opW`/`memOpW` pairs are exactly the parallel-table shape the
doctrine retires).

MINED INTENT (legacy/lean/wasm-backend/WasmBackend/Wat.lean): WAT is
never string-interpolated for STRUCTURE (the renderer folds the AST;
never a hand-built literal); the memarg's `offset`/`align` are
STRUCTURED FIELDS rendered from the data — the legacy's two clobber
bugs lived in string literals. Ported shape: line-oriented, 2 spaces
per nesting level; the structural forms (`block`/`loop`/`if_`) own
their bodies as subterms and the renderer nests accordingly (the
block discipline rendered from the AST's structure, not from a flat
list); an empty else-branch renders NO `else` — the text mirrors the
binary format's else-elision (both are the AST's `[]`).

THE ROPE (notes/v3/06-lean-rules.md §7b): the structure carrier is
`Kit.Text` — `Text.cat`/`.app` compose O(1), the ONE render walk at
the consumer boundary; leaves are the bounded per-line templates.
Never a left-nested `++` over the artifact.

THE BOUNDARY, HONESTLY (the round-trip note): there is NO WAT parse
direction here and none is planned in this lane — the wasm toolchain
(`wat2wasm` et al.) is the text consumer, and a parser would be a
second grammar over the same surface (a parallel-table risk R6
forbids, with no consumer). The honest correspondences of this
rendering are: (a) the BYTE level — `WasmCore.Encode.encodeModule` is
the codec of the SAME `Module` the renderer folds (the two faces are
two readings of one AST, not translations of each other); and (b) the
TEXT level — the golden tie below (WasmCoreTests pins the emitter's
run byte-exact). A semantic law (rendered text ↔ re-parsed module,
or rendered ↔ encoded agreement) waits for the Sem/binary-decoder
orders; until then the law field is `none` and this note is the
declared hole, never a silent gap.

THE ARTIFACT DISCIPLINE: the emitter row (`watEmitter`) declares
`gen/wasm-slice.wat` as its one output — the path is the one-writer
ledger's anchor. PLACEMENT JUDGMENT: no `.wat` artifact COMMITS yet —
`gates gen-check`'s regen is SchemaCore-bound, and a wasm regen driver
+ its gen-check row is a named follow-up (the leftover rule: no
committed artifact ahead of its writer). Until that wiring, the
byte-tie discipline is TEST-PINNED: WasmCoreTests pins
`watEmitter.run`'s output byte-exact (the same golden discipline the
Encode lane runs), which is where the tie teeth live today.

The five questions (notes/v3/01-core.md):

- **Root**: Crossing — the module (the target grammar's value) read
  into exact text bytes.
- **Carrier grade**: none here — the renderer is a total fold; the
  laws live at the consumers (the golden tie in WasmCoreTests; the
  correspondence note above names the semantic rung's wait).
- **Spine reading**: the artifact spine — `watEmitter` is a
  Kit.Emit Emitter row over `Module` (05 §2): outputs nodup in the
  type, `run` the pure total fold, the driver owns IO (unwired — the
  note above).
- **Ladder rung**: rung 1 (total structural fold); the byte-tie is
  the test-pinned regression until the gen-check row lands.
- **Gate row**: none at the gates yet (WasmCore is not in
  Gates.Packages' gated set; the gen-check wiring is the named
  follow-up) + the WasmCoreTests golden/spelling pins.

Consumer trail: rides `Kit.Text` (the rope), `Kit.Emit` (the spine),
`WasmCore.Types` + `WasmCore.Instr` + `WasmCore.OpTable` (the ONE
table's spelling facet) + `WasmCore.Module`. Core-only (the cone
rule).
-/

import Kit.Emit
import Kit.Text
import WasmCore.Types
import WasmCore.Instr
import WasmCore.OpTable
import WasmCore.Module

namespace WasmCore

open Kit (Text)

/-! ## The leaves (bounded per-line templates — the rope rule's leaf face) -/

/-- The indentation unit: 2 spaces per nesting level. -/
def indentW (n : Nat) : String := String.join (List.replicate n "  ")

/-- One line at one nesting level (the renderer's ONLY newline
    source — every line ends exactly once). -/
def lineW (ind : Nat) (s : String) : Text := .str (indentW ind ++ s ++ "\n")

/-- The WAT string literal (module/name fields — always quoted,
    escaped). Mined from legacy `Wat.strW`. -/
def strW (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |> fun t => t.replace "\"" "\\\"") ++ "\""

/-- The value types' WAT spelling (the type grammar's words — not op
    rows; the op table owns op spellings only). -/
def valTypeW : ValType → String
  | .i32 => "i32" | .i64 => "i64" | .f32 => "f32" | .f64 => "f64"
  | .funcref => "funcref" | .externref => "externref"

/-- The memarg operands, rendered from the DATA: a zero offset is
    elided (the format's default), an explicit align is spelled, the
    row's elided default (`memAlignDefault`) stays unspelled — never
    baked numbers (the legacy clobber-bug note, module header). -/
def memArgsW (offset : Nat) (align : Option Nat) : String :=
  (if offset = 0 then "" else s!" offset={offset}") ++
  (match align with | some a => s!" align={a}" | none => "")

/-! ## The instruction fold — the spellings ride the ONE op table -/

mutual
/-- ONE instruction → its text (indented). Flat forms are the
    table-folded one-liners; the structural forms nest their bodies
    (the block discipline rendered from the AST's structure). Total
    by construction — explicit arms, the fold is the size-measured
    walk `iSize` names. -/
def instrW (ind : Nat) : Instr → Text
  | .i32const n => lineW ind s!"i32.const {n}"
  | .i64const n => lineW ind s!"i64.const {n}"
  | .localget n => lineW ind s!"local.get {n}"
  | .localset n => lineW ind s!"local.set {n}"
  | .localtee n => lineW ind s!"local.tee {n}"
  | .call fn => lineW ind s!"call {fn}"
  | .mem op offset align => lineW ind s!"{memName op}{memArgsW offset align}"
  | .op o => lineW ind (opName o)
  | .br d => lineW ind s!"br {d}"
  | .brif d => lineW ind s!"br_if {d}"
  | .block body =>
      Text.cat [lineW ind "block", bodyW (ind + 1) body, lineW ind "end"]
  | .loop body =>
      Text.cat [lineW ind "loop", bodyW (ind + 1) body, lineW ind "end"]
  | .if_ thenI elseI =>
      Text.cat [lineW ind "if", bodyW (ind + 1) thenI,
        (match elseI with
        | [] => Text.nil  -- the binary's else-elision, mirrored in text
        | _ => Text.cat [lineW ind "else", bodyW (ind + 1) elseI]),
        lineW ind "end"]
  | .ret => lineW ind "return"
  | .drop => lineW ind "drop"
  | .select => lineW ind "select"
  | .unreach => lineW ind "unreachable"

/-- A body's lines: each instruction's text in order (the `end`s are
    the structural forms' OWN — a flat list carries none, exactly as
    in the binary encoding). -/
def bodyW (ind : Nat) : List Instr → Text
  | [] => Text.nil
  | i :: is => Text.app (instrW ind i) (bodyW ind is)
end

/-! ## The module fields (each rendered from its DATA) -/

/-- The params operand: `" (param i32 i64)"` — leading-space when
    present, empty when the type has none. -/
def paramListW (ps : List ValType) : String :=
  match ps with
  | [] => ""
  | _ => " (param " ++ String.intercalate " " (ps.map valTypeW) ++ ")"

/-- The results operand (same shape). -/
def resultListW (rs : List ValType) : String :=
  match rs with
  | [] => ""
  | _ => " (result " ++ String.intercalate " " (rs.map valTypeW) ++ ")"

/-- One type: `(type (func (param …) (result …)))`, operands elided
    when empty — from the FuncType's data. -/
def typeW (ind : Nat) (ft : FuncType) : Text :=
  lineW ind s!"(type (func{paramListW ft.params}{resultListW ft.results}))"

/-- One function: the type BY INDEX (the AST's reference discipline),
    one `(local T)` per declared local (beyond the type's params),
    then the body's lines, nested. -/
def funcW (ind : Nat) (f : Func) : Text :=
  Text.cat
    [ lineW ind s!"(func (type {f.tyIdx})"
    , Text.cat (f.locals.map (fun t => lineW (ind + 1) s!"(local {valTypeW t})"))
    , bodyW (ind + 1) f.body
    , lineW ind ")" ]

/-- One export: `(export "name" (func idx))` — the name through
    `strW` (quoted, escaped), the index from the data. -/
def exportW (ind : Nat) (e : Export) : Text :=
  match e.desc with
  | .func idx => lineW ind s!"(export {strW e.name} (func {idx}))"

/-- The module's fields as text: types, memory (elided at
    `memMin = 0` — the same elision the binary format makes),
    exports, functions — the fold in the binary sections' order. -/
def moduleText (m : Module) : Text :=
  Text.cat
    [ lineW 0 "(module"
    , Text.cat (m.types.map (typeW 1))
    , (if m.memMin = 0 then Text.nil else lineW 1 s!"(memory {m.memMin})")
    , Text.cat (m.exports.map (exportW 1))
    , Text.cat (m.funcs.map (funcW 1))
    , lineW 0 ")" ]

/-- THE renderer: `Module` → the WAT text. Total, pure, structural —
    the ONE render walk at this boundary (the rope rule). -/
def renderModule (m : Module) : String := Text.render (moduleText m)

/-! ## The emitter row (05 §2 — the artifact spine) -/

/-- The WAT emitter: the module → WAT artifact as a Kit.Emit Emitter
    row. `run` is the pure total fold above; the output path is the
    one-writer declaration (`gen/wasm-slice.wat` — nodup in the
    type). The LAW, honestly: `none` — the rendering is total by
    construction (the fold above) and the golden is byte-tied in
    WasmCoreTests (the test-pinned discipline, module header); a
    semantic law (rendered ↔ encoded/decoded agreement) waits for the
    Sem/binary-decoder orders. The driver wiring (the regen writer +
    the gen-check row) is the named follow-up; nothing commits ahead
    of its writer. -/
def watEmitter : Kit.Emit.Emitter Module where
  name := "wasmcore.wat"
  style := .wat
  specSource := "WasmCore.Module"
  outputs := ["gen/wasm-slice.wat"]
  rev := "wat-r1"
  run := fun m => [{ path := "gen/wasm-slice.wat", contents := renderModule m }]

end WasmCore
