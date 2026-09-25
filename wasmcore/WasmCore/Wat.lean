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
- **Gate row**: WasmCore's row in Gates.Packages' gated set (the
  per-library axiom sweep covers it; the gen-check wiring is landed)
  + the WasmCoreTests golden/spelling pins.

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

/-- One escaped character (the WAT string escape discipline: the
    backslash and the quote are backslash-escaped, every other char is
    itself). The escape is the PER-CHAR map the parser inverts
    (`WasmCore.WatParse.unescTo_escW`). -/
def escChar (c : Char) : List Char :=
  if c == '\\' then ['\\', '\\'] else if c == '"' then ['\\', '"'] else [c]

/-- The escaped character run (the per-char map; byte-identical to the
    legacy replace-then-replace spelling — each char is escaped
    independently, and neither escape's output feeds the other's
    matcher). -/
def escW : List Char → List Char
  | [] => []
  | c :: cs => escChar c ++ escW cs

/-- The WAT string literal (module/name fields — always quoted,
    escaped). Mined from legacy `Wat.strW`; re-spelled over the
    per-char `escW` map (the same bytes — the parser's round-trip
    laws consume THIS spelling's structure). -/
def strW (s : String) : String :=
  "\"" ++ String.ofList (escW s.toList) ++ "\""

/-! ## The spellings (the ONE keyword source — 07 R6's no-parallel-table
     rule at the keyword face: the emitter's templates and the WAT
     parser's tokens (`WasmCore.WatParse`) are THIS list's projections;
     a spelling drift is a compile break, never a silent re-spell. The
     OP/MEM-OP spellings ride the ONE op table's `name` field as before
     (`opName`/`memName` — never spelled here). -/

/-- The module opener. -/
def kwModule : String := "(module"
/-- The type-section line's head. -/
def kwType : String := "(type (func"
/-- The params operand. -/
def kwParam : String := " (param "
/-- The results operand. -/
def kwResult : String := " (result "
/-- The memory-section line's head. -/
def kwMemSec : String := "(memory "
/-- The table-section line's head. -/
def kwTable : String := "(table "
/-- The table line's tail (the ONE funcref table's element type). -/
def kwFuncref : String := " funcref)"
/-- The export line's head. -/
def kwExport : String := "(export "
/-- The export descriptor's words (the desc token's decode targets —
    shared with the ref operands' spellings below). -/
def kwFuncWord : String := "func"
def kwMemWord : String := "memory"
/-- The export's func-ref operand. -/
def kwFuncRef : String := " (" ++ kwFuncWord ++ " "
/-- The export's memory-ref operand. -/
def kwMemRef : String := " (" ++ kwMemWord ++ " "
/-- The func's declaration line (the type by index). -/
def kwFuncDecl : String := "(func (type "
/-- The local declaration line. -/
def kwLocal : String := "(local "
/-- The element segment's head (the active offset-0 face). -/
def kwElem : String := "(elem (i32.const 0) func"
/-- The const instructions. -/
def kwI32const : String := "i32.const"
def kwI64const : String := "i64.const"
/-- The local instructions. -/
def kwLocalget : String := "local.get"
def kwLocalset : String := "local.set"
def kwLocaltee : String := "local.tee"
/-- The call instructions. -/
def kwCall : String := "call"
def kwCallindirect : String := "call_indirect"
/-- The indirect call's type operand. -/
def kwTypeOpnd : String := " (type "
/-- The branch instructions. -/
def kwBr : String := "br"
def kwBrif : String := "br_if"
/-- The structural markers. -/
def kwBlock : String := "block"
def kwLoop : String := "loop"
def kwIf : String := "if"
def kwEnd : String := "end"
def kwElse : String := "else"
/-- The plain control words. -/
def kwReturn : String := "return"
def kwDrop : String := "drop"
def kwSelect : String := "select"
def kwUnreachable : String := "unreachable"
/-- The memarg operands (structured fields — rendered from the DATA). -/
def kwOffset : String := " offset="
def kwAlign : String := " align="

/-- The value types' WAT spelling — Types.lean's `renderValType` (the
    ONE spelling; not op rows — the op table owns op spellings only).
    The checker's diagnostics cite the same. -/
def valTypeW : ValType → String := renderValType

/-- The memarg operands, rendered from the DATA: a zero offset is
    elided (the format's default), an explicit align is spelled, the
    row's elided default (`memAlignDefault`) stays unspelled — never
    baked numbers (the legacy clobber-bug note, module header). -/
def memArgsW (offset : Nat) (align : Option Nat) : String :=
  (if offset = 0 then "" else s!"{kwOffset}{offset}") ++
  (match align with | some a => s!"{kwAlign}{a}" | none => "")

/-! ## The instruction fold — the spellings ride the ONE op table -/

mutual
/-- ONE instruction → its text (indented). Flat forms are the
    table-folded one-liners; the structural forms nest their bodies
    (the block discipline rendered from the AST's structure). Total
    by construction — explicit arms, the fold is the size-measured
    walk `iSize` names. -/
def instrW (ind : Nat) : Instr → Text
  | .i32const n => lineW ind s!"{kwI32const} {n}"
  | .i64const n => lineW ind s!"{kwI64const} {n}"
  | .localget n => lineW ind s!"{kwLocalget} {n}"
  | .localset n => lineW ind s!"{kwLocalset} {n}"
  | .localtee n => lineW ind s!"{kwLocaltee} {n}"
  | .call fn => lineW ind s!"{kwCall} {fn}"
  | .callindirect ty => lineW ind s!"{kwCallindirect}{kwTypeOpnd}{ty})"
  | .mem op offset align => lineW ind s!"{memName op}{memArgsW offset align}"
  | .op o => lineW ind (opName o)
  | .br d => lineW ind s!"{kwBr} {d}"
  | .brif d => lineW ind s!"{kwBrif} {d}"
  | .block body =>
      Text.cat [lineW ind kwBlock, bodyW (ind + 1) body, lineW ind kwEnd]
  | .loop body =>
      Text.cat [lineW ind kwLoop, bodyW (ind + 1) body, lineW ind kwEnd]
  | .if_ thenI elseI =>
      Text.cat [lineW ind kwIf, bodyW (ind + 1) thenI,
        (match elseI with
        | [] => Text.nil  -- the binary's else-elision, mirrored in text
        | _ => Text.cat [lineW ind kwElse, bodyW (ind + 1) elseI]),
        lineW ind kwEnd]
  | .ret => lineW ind kwReturn
  | .drop => lineW ind kwDrop
  | .select => lineW ind kwSelect
  | .unreach => lineW ind kwUnreachable

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
  | _ => kwParam ++ String.intercalate " " (ps.map valTypeW) ++ ")"

/-- The results operand (same shape). -/
def resultListW (rs : List ValType) : String :=
  match rs with
  | [] => ""
  | _ => kwResult ++ String.intercalate " " (rs.map valTypeW) ++ ")"

/-- One type: `(type (func (param …) (result …)))`, operands elided
    when empty — from the FuncType's data. -/
def typeW (ind : Nat) (ft : FuncType) : Text :=
  lineW ind s!"{kwType}{paramListW ft.params}{resultListW ft.results}))"

/-- One function: the type BY INDEX (the AST's reference discipline),
    one `(local T)` per declared local (beyond the type's params),
    then the body's lines, nested. -/
def funcW (ind : Nat) (f : Func) : Text :=
  Text.cat
    [ lineW ind s!"{kwFuncDecl}{f.tyIdx})"
    , Text.cat (f.locals.map (fun t => lineW (ind + 1) s!"{kwLocal}{valTypeW t})"))
    , bodyW (ind + 1) f.body
    , lineW ind ")" ]

/-- One export: `(export "name" (func idx))` or the memory arm —
    `(export "name" (memory idx))` (the canonical-ABI adapter face's
    memory export). The name through `strW` (quoted, escaped), the
    index from the data. -/
def exportW (ind : Nat) (e : Export) : Text :=
  match e.desc with
  | .func idx => lineW ind s!"{kwExport}{strW e.name}{kwFuncRef}{idx}))"
  | .memory idx => lineW ind s!"{kwExport}{strW e.name}{kwMemRef}{idx}))"

/-- One table: `(table {n} funcref)` — the size from the entries'
    length (the table's data face; the element type is funcref in
    every honest use). -/
def tableW (ind : Nat) (t : Table) : Text :=
  lineW ind s!"{kwTable}{t.init.length}{kwFuncref}"

/-- One active element segment: `(elem (i32.const 0) func i0 i1 …)` —
    the table's initialization face, the offset spelled from the DATA
    (the constant-0 face of the wire's `i32.const 0; end`). -/
def elemW (ind : Nat) (t : Table) : Text :=
  lineW ind s!"{kwElem}{t.init.foldl (fun s n => s ++ " " ++ toString n) ""})"

/-- The module's fields as text: types, memory (elided at
    `memMin = 0` — the same elision the binary format makes), tables,
    exports, element segments, functions — the fold in the binary
    sections' order. -/
def moduleText (m : Module) : Text :=
  Text.cat
    [ lineW 0 kwModule
    , Text.cat (m.types.map (typeW 1))
    , (if m.memMin = 0 then Text.nil else lineW 1 s!"{kwMemSec}{m.memMin})")
    , Text.cat (m.tables.map (tableW 1))
    , Text.cat (m.exports.map (exportW 1))
    , Text.cat ((m.tables.filter (fun t => !t.init.isEmpty)).map (elemW 1))
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
