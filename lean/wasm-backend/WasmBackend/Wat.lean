/-!
# WasmBackend.Wat — the typed WAT AST + renderer

The doctrine: WAT is never string-interpolated for STRUCTURE. The emitter
builds `Instr`/`Func`/`Module` values; this module renders them. The
offsets in the emitted instructions are structured FIELDS (Nat), fed
from `WasmBackend.Layout.offsets` (the proved canonical-ABI layout) —
the two hand-number clobber bugs this month lived in string literals.

INCREMENTAL MIGRATION: the escape hatch `Instr.raw (s : String)` renders
`s` as one verbatim WAT line. Each migrated emission site is typed; the
un-migrated sites cross the bridge as `.raw` lines. The raw-count = the
migration's progress metric (`Module.rawCount`), printed by GenMain. The
ledger of what remains raw is owned by WasmBackend.lean's header.

Rendering: `Std.Format` (the doctrine — never string interpolation for
structure). NO `group`/`fill` is used, so every `Format.line` is a HARD
break: the output is strictly line-oriented, 2 spaces per nesting level.
WAT semantics = the parse, not the bytes: the folded/nested layout the
renderer produces may differ cosmetically from older goldens.

Constructor-name map (Lean keywords force renames):
`ret` = `return`, `unreach` = `unreachable`, `if_` = `if`.
Local references: a bare digit string is an INDEX (`local.get 3` in
cabi_realloc); anything else is an id (`local.get $x`).

Ownership: wasm-backend. Imports nothing but Init (no Lean dep) —
`WasmBackend.Layout` is consumed by the ADAPTERS (WasmBackend.lean),
not by the AST.
-/

namespace WasmBackend.Wat

open Std (Format)
open Std.Format

/-! ## Instructions -/

/-- Memory load/store ops. The `offset=`/`align=` operands are
    structured fields on `Instr.mem` — never baked into strings. -/
inductive MemOp where
  | i32load8u | i32load | i64load
  | i32store | i64store | i32store8 | i64store8
  deriving Inhabited, BEq

/-- The plain (stack-machine) operations the backend emits — binops,
    comparisons, conversions. -/
inductive Op where
  | i64add | i64sub | i64mul | i64ltu | i64eq
  | i32add | i32sub | i32mul | i32and | i32xor | i32shru | i64shru
  | i32eqz | i32eq | i32ltu | i32gtu
  | i32wrapi64 | i64extendi32u
  deriving Inhabited, BEq

/-- One instruction. Structural forms (`block`/`loop`/`if_`) own their
    bodies; everything else is flat. `raw` = the escape hatch: one
    verbatim WAT line, counted by `rawCount`. -/
inductive Instr where
  | i32const (n : Nat)
  | i64const (n : Nat)
  | localget (n : String) | localset (n : String) | localtee (n : String)
  | globalget (n : String) | globalset (n : String)
  | call (fn : String)
  | returncall (fn : String)
  | callindirect (ty : String)
  | mem (op : MemOp) (offset : Nat) (align : Option Nat)
  | memcopy
  | op (o : Op)
  | br (label : String) | brif (label : String)
  | block (label : String) (body : List Instr)
  | loop (label : String) (body : List Instr)
  | if_ (res : Option String) (thenI : List Instr) (elseI : List Instr)
  | ret
  | drop
  | select
  | unreach
  | raw (s : String)
  deriving Inhabited

/-! ## Rendering -/

/-- WAT string literal (module/name fields — always quoted, escaped). -/
def strW (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |> fun t => t.replace "\"" "\\\"") ++ "\""

/-- A WAT id: bare if every char is an id char, else a quoted id
    (`$"[callback][async-lift]watch-orders"`). -/
def idW (n : String) : String :=
  let bare := !n.isEmpty && n.all fun c => Char.isAlpha c || Char.isDigit c
    || "._-!#%&'*+-/:<=>?@^_`|~".contains c
  if bare then s!"${n}" else s!"$\"{n.replace "\\" "\\\\" |>.replace "\"" "\\\""}\""

/-- Local/global reference: a bare digit string = an INDEX (`local.get 3`);
    anything else = an id. -/
def refW (n : String) : String :=
  if !n.isEmpty && n.all (Char.isDigit) then n else idW n

def memOpW : MemOp → String
  | .i32load8u => "i32.load8_u" | .i32load => "i32.load" | .i64load => "i64.load"
  | .i32store => "i32.store" | .i64store => "i64.store" | .i32store8 => "i32.store8"
  | .i64store8 => "i64.store8"

def opW : Op → String
  | .i64add => "i64.add" | .i64sub => "i64.sub" | .i64mul => "i64.mul"
  | .i64ltu => "i64.lt_u" | .i64eq => "i64.eq"
  | .i32add => "i32.add" | .i32sub => "i32.sub" | .i32mul => "i32.mul"
  | .i32and => "i32.and" | .i32xor => "i32.xor"
  | .i32shru => "i32.shr_u" | .i64shru => "i64.shr_u"
  | .i32eqz => "i32.eqz" | .i32eq => "i32.eq" | .i32ltu => "i32.lt_u" | .i32gtu => "i32.gt_u"
  | .i32wrapi64 => "i32.wrap_i64" | .i64extendi32u => "i64.extend_i32_u"

def memArgsW (offset : Nat) (align : Option Nat) : String :=
  (if offset == 0 then "" else s!" offset={offset}")
    ++ (match align with | some a => s!" align={a}" | none => "")

/-- FLAT one-line text of an instruction (the module items' inline
    operands: the globals' init, the elem's offset; also the `raw`-line
    identity). Structural forms have no flat text — the renderer nests
    them. -/
def lineOf : Instr → String
  | .i32const n => s!"i32.const {n}"
  | .i64const n => s!"i64.const {n}"
  | .localget n => s!"local.get {refW n}"
  | .localset n => s!"local.set {refW n}"
  | .localtee n => s!"local.tee {refW n}"
  | .globalget n => s!"global.get {idW n}"
  | .globalset n => s!"global.set {idW n}"
  | .call fn => s!"call {idW fn}"
  | .returncall fn => s!"return_call {idW fn}"
  | .callindirect ty => s!"call_indirect (type {idW ty})"
  | .mem op offset al => s!"{memOpW op}{memArgsW offset al}"
  | .memcopy => "memory.copy"
  | .op o => opW o
  | .br l => s!"br {idW l}"
  | .brif l => s!"br_if {idW l}"
  | .ret => "return"
  | .drop => "drop"
  | .select => "select"
  | .unreach => "unreachable"
  | .raw s => s
  | .block .. | .loop .. | .if_ .. => "«structured instr has no flat text»"

-- The renderer. NO groups → every `Format.line` = a hard newline;
-- `nest 2` = the 2-space-per-level indentation style.
mutual
def instrW : Instr → Format
  | .i32const n => text s!"i32.const {n}"
  | .i64const n => text s!"i64.const {n}"
  | .localget n => text s!"local.get {refW n}"
  | .localset n => text s!"local.set {refW n}"
  | .localtee n => text s!"local.tee {refW n}"
  | .globalget n => text s!"global.get {idW n}"
  | .globalset n => text s!"global.set {idW n}"
  | .call fn => text s!"call {idW fn}"
  | .returncall fn => text s!"return_call {idW fn}"
  | .callindirect ty => text s!"call_indirect (type {idW ty})"
  | .mem op offset al => text s!"{memOpW op}{memArgsW offset al}"
  | .memcopy => text "memory.copy"
  | .op o => text (opW o)
  | .br l => text s!"br {idW l}"
  | .brif l => text s!"br_if {idW l}"
  | .block l body =>
      text s!"block {idW l}" ++ Format.nest 2 (Format.line ++ instrsW body)
        ++ Format.line ++ text "end"
  | .loop l body =>
      text s!"loop {idW l}" ++ Format.nest 2 (Format.line ++ instrsW body)
        ++ Format.line ++ text "end"
  | .if_ res thenI elseI =>
      let rhdr := match res with | some t => s!" (result {t})" | none => ""
      text s!"if{rhdr}"
        ++ Format.nest 2 (Format.line ++ instrsW thenI)
        ++ (match elseI with
            | [] => Format.nil
            | _ => Format.line ++ text "else" ++ Format.nest 2 (Format.line ++ instrsW elseI))
        ++ Format.line ++ text "end"
  | .ret => text "return"
  | .drop => text "drop"
  | .select => text "select"
  | .unreach => text "unreachable"
  | .raw s => text s

def instrsW : List Instr → Format
  | [] => .nil
  | [i] => instrW i
  | i :: is => instrW i ++ Format.line ++ instrsW is
end

/-! ## Functions -/

structure Param where
  /-- `none` = an unnamed param (`(param i32)`). -/
  name : Option String
  ty : String
  deriving Inhabited

structure Func where
  /-- WITHOUT the `$` (the renderer adds it, quoting when needed). -/
  name : String
  params : List Param
  result : Option String
  locals : List (String × String)
  body : List Instr
  deriving Inhabited

def paramW : Param → String
  | { name := some n, ty } => s!"(param {idW n} {ty})"
  | { name := none, ty } => s!"(param {ty})"

def paramsW (ps : List Param) : String :=
  String.intercalate " " (ps.map paramW)

def funcW (f : Func) : Format :=
  let ps := paramsW f.params
  let res := match f.result with | some t => s!" (result {t})" | none => ""
  let localsF : List Format :=
    f.locals.map fun (n, t) => text s!"(local {idW n} {t})"
  let joined := (localsF ++ [instrsW f.body]).foldl (fun a b =>
    if a.isEmpty then b else a ++ Format.line ++ b) Format.nil
  text s!"(func {idW f.name}{if ps.isEmpty then "" else " " ++ ps}{res}"
    ++ Format.nest 2 (Format.line ++ joined) ++ Format.line ++ text ")"

/-! ## Module -/

/-- `(import "mod" "name" (func …))` — the task intrinsics + any future
    imports. -/
structure Import where
  module : String
  name : String
  id : Option String
  params : List Param
  result : Option String
  deriving Inhabited

structure Global where
  name : String
  ty : String
  /-- `mut` is a reserved token — `isMut` it is. -/
  isMut : Bool
  init : Instr
  deriving Inhabited

structure TypeDef where
  name : String
  params : List Param
  result : Option String
  deriving Inhabited

structure Table where
  size : Nat
  elemTy : String
  deriving Inhabited

structure Elem where
  offset : Instr
  funcs : List String
  deriving Inhabited

inductive ExportDesc where
  | func (id : String)
  | table (idx : Nat)
  | memory (idx : Nat)
  deriving Inhabited

structure Export where
  name : String
  desc : ExportDesc
  deriving Inhabited

/-- One module field. The task's Module (imports/funcs/exports/memory/
    start) = these typed constructors; `raw` = the module-level escape
    hatch (verbatim line — used for the runtime.wat splice marker, which
    GenMain replaces by exact bytes). -/
inductive Item where
  | imp (i : Import)
  | ty (t : TypeDef)
  | global (g : Global)
  | func (f : Func)
  | table (t : Table)
  | elem (e : Elem)
  | export (e : Export)
  | memory (min : Nat)
  | raw (s : String)
  deriving Inhabited

structure Module where
  /-- Reserved for the start section (unused today — documented so the
      AST is the complete surface, not just what v1 emits). -/
  start : Option String := none
  items : List Item := []
  deriving Inhabited

def importW (i : Import) : String :=
  let idp := match i.id with | some n => s!" {idW n}" | none => ""
  let ps := if i.params.isEmpty then "" else " " ++ paramsW i.params
  let res := match i.result with | some t => s!" (result {t})" | none => ""
  s!"(import {strW i.module} {strW i.name} (func{idp}{ps}{res}))"

def typeW (t : TypeDef) : String :=
  let ps := paramsW t.params
  let res := match t.result with | some r => s!" (result {r})" | none => ""
  s!"(type {idW t.name} (func{if ps.isEmpty then "" else " " ++ ps}{res}))"

def globalW (g : Global) : String :=
  let mutw := if g.isMut then "(mut " ++ g.ty ++ ")" else g.ty
  s!"(global {idW g.name} {mutw} ({lineOf g.init}))"

def exportW (e : Export) : String :=
  let d := match e.desc with
    | .func f => s!"(func {idW f})"
    | .table n => s!"(table {n})"
    | .memory n => s!"(memory {n})"
  s!"(export {strW e.name} {d})"

def itemW : Item → Format
  | .imp i => text s!"  {importW i}"
  | .ty t => text s!"  {typeW t}"
  | .global g => text s!"  {globalW g}"
  | .func f => text "  " ++ funcW f
  | .table t => text s!"  (table {t.size} {t.elemTy})"
  | .elem e => text s!"  (elem ({lineOf e.offset}) {String.intercalate " " (e.funcs.map idW)})"
  | .export e => text s!"  {exportW e}"
  | .memory n => text s!"  (memory {n})"
  | .raw s => text s

/-- THE renderer: `Module` → the WAT text. -/
def Module.render (m : Module) : String :=
  let items := m.items.map itemW
  let startF := match m.start with
    | some s => Format.line ++ text s!"  (start {idW s})"
    | none => Format.nil
  let joined := items.foldl (fun a b =>
    if a.isEmpty then b else a ++ Format.line ++ b) Format.nil
  Format.pretty (text "(module" ++ Format.line ++ joined ++ startF
    ++ Format.line ++ text ")") (width := 1 <<< 30)

/-! ## The raw-count metric -/

/-- The number of `Instr.raw` instructions in a body — the migration's
    progress metric. -/
def rawCountOf : List Instr → Nat
  | [] => 0
  | .raw _ :: is => rawCountOf is + 1
  | .block _ b :: is => rawCountOf b + rawCountOf is
  | .loop _ b :: is => rawCountOf b + rawCountOf is
  | .if_ _ t e :: is => rawCountOf t + rawCountOf e + rawCountOf is
  | _ :: is => rawCountOf is

/-- The module's total raw count (funcs' bodies + verbatim module lines,
    which are ALWAYS raw by construction). -/
def Module.rawCount (m : Module) : Nat :=
  m.items.foldl (fun n it => n +
    match it with
    | .func f => rawCountOf f.body
    | .raw _ => 1
    | _ => 0) 0

end WasmBackend.Wat
