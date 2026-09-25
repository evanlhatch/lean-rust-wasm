/-
# Wit.Render — the ONE renderer: the WIT AST → text

Owner: the Wit agent (the mandate tree, `wit/`).
Driving decisions: notes/v3/05-codegen.md §2 (the emitter spine — the
byte-tie is the correspondence evidence; the artifact of record,
`gen/schema-slice.wit`, plus the committed `schema` driver are the
format's truth, never this file's prose) + notes/v3/07 R1 (the typed
carrier makes misrendering unconstructible; the renderer is TOTAL over
it — every well-formed AST has exactly one text).

Totality is the prerequisite for everything: `render` is a total
structural fold, so a golden equality is checkable data (`WitTests`
pins the exact bytes), and the gate's regen-and-diff (`gates
gen-check`) is the CI shadow of the byte-tie.

The layout discipline (the bytes are the artifact's, verbatim):
- the package line + a blank line, then the interfaces;
- the interface's record blocks concatenated (one per item, registration
  order — the driver's fold order is the artifact's);
- the record block: 2-space indent, fields one per line at 4, trailing
  comma per field (the artifact of record's shape, empty-fields
  included: an empty record degrades to a bare blank line — the
  pre-AST emitter's shape, byte-preserved).

The world case (grown with its first consumer, `Guest.Component`):
`func`/`exportItem`/`importItem`/`world`/`worldFile` render the
`Wit.World` carrier (the component boundary's contract). The world's
PARSE-BACK is a NAMED follow-up (`Wit.World`'s header): the accepted
language below stays the world-free package text, and `worldFile`'s
image is deliberately outside it — the world artifact's tie is the
render-side byte-tie (the committed bytes vs the fresh render), not a
round-trip claim.

Core-only (imports `Wit` + `Wit.World` only — the cone rule).

The five questions (notes/v3/01-core.md):
- root: Crossing — the WIT AST read into its text (the target
  grammar's surface).
- carrier grade: none of its own — the totality + the byte-tie ARE the
  grade (a total renderer's golden equality is a theorem; the nodup
  carrier lives in `Wit`).
- spine reading: the artifact stage of the emitter spine — the ONE
  renderer every WIT-producing lane calls; drivers own IO.
- ladder rung: rung 1 — total structural folds.
- gate row: gen-check (the byte-tie over gen/schema-slice.wit).
-/

import Wit
import Wit.World

namespace Wit.Render

/-- The scalar atom's spelling (the artifact of record's — `i64`
    included; see `Wit`'s header note). -/
def scalar : Scalar → String
  | .bool => "bool"
  | .u64 => "u64"
  | .i64 => "i64"
  | .string => "string"

/-- The WIT type text: total over the closed grammar. -/
def ty : Ty → String
  | .atom s => scalar s
  | .option a => "option<" ++ ty a ++ ">"
  | .list a => "list<" ++ ty a ++ ">"
  | .result ok err => "result<" ++ ty ok ++ ", " ++ ty err ++ ">"
  | .tuple a b => "tuple<" ++ ty a ++ ", " ++ ty b ++ ">"

/-- One field line (4-space indent, trailing comma). -/
def field (f : Field) : String :=
  "    " ++ f.name ++ ": " ++ ty f.ty ++ ","

/-- The fields' continuation join: each further field rides its
    preceding newline (the explicit-fold form of `String.intercalate
    "\n"` — the intercalate's where-auxiliary is inaccessible in this
    toolchain, and the round-trip proofs consume the fold's
    equations; the VALUE is the same bytes, pinned by the golden
    tests + the gen-check byte-tie). -/
def fieldsTailJoin : List Field → String
  | [] => ""
  | f :: fs => "\n" ++ field f ++ fieldsTailJoin fs

/-- The field block: the field lines, the first without a leading
    newline (the same value as `String.intercalate "\n"` over the
    field lines). -/
def fieldsJoin : List Field → String
  | [] => ""
  | f :: fs => field f ++ fieldsTailJoin fs

/-- One record block: the fields joined one-per-line, no trailing
    blank (an empty field list degrades to a bare blank line — the
    artifact of record's empty-record shape). -/
def record (r : Record) : String :=
  "  record " ++ r.name ++ " {\n"
    ++ fieldsJoin r.fields ++ "\n  }\n"

/-- The record blocks' concatenation (one per item, registration
    order — the explicit-fold form of `String.intercalate ""`). -/
def recordsJoin : List Record → String
  | [] => ""
  | r :: rs => record r ++ recordsJoin rs

/-- One interface block (the record blocks concatenated). -/
def interface (i : Interface) : String :=
  "interface " ++ i.name ++ " {\n"
    ++ recordsJoin i.records ++ "}\n"

/-- The interface blocks' concatenation (the same fold form). -/
def interfacesJoin : List Interface → String
  | [] => ""
  | i :: is => interface i ++ interfacesJoin is

/-- The whole package text: the package line + a blank line, then the
    interfaces. Total; deterministic; the byte-tie's render face. -/
def package (p : Package) : String :=
  "package " ++ p.id ++ ";\n\n"
    ++ interfacesJoin p.interfaces

/-! ## the world case (the component boundary's text face) -/

/-- A world func's type text: `func(a: u64, b: u64) -> u64` (no
    result omits the arrow). The params ride the `name: ty` shape
    joined `, ` (NOT the record field's indented lines — a func's
    params are inline). Total over the closed grammar. -/
def funcParam (p : Field) : String :=
  p.name ++ ": " ++ ty p.ty

def func (f : Func) : String :=
  "func(" ++ String.intercalate ", " (f.params.map funcParam) ++ ")"
    ++ match f.result with
       | some t => " -> " ++ ty t
       | none => ""

/-- One EXPORT item line (2-space indent, trailing semicolon). The
    inline-func form carries the type; the interface form is
    by-name. -/
def exportItem (i : Item) : String :=
  match i with
  | .func f => "  export " ++ f.name ++ ": " ++ func f ++ ";\n"
  | .iface i => "  export " ++ i.name ++ ";\n"

/-- One IMPORT item line (the same shapes). -/
def importItem (i : Item) : String :=
  match i with
  | .func f => "  import " ++ f.name ++ ": " ++ func f ++ ";\n"
  | .iface i => "  import " ++ i.name ++ ";\n"

/-- The items' concatenation (one line each, order preserved —
    the explicit-fold form). -/
def itemsJoin (r : Item → String) : List Item → String
  | [] => ""
  | i :: is => r i ++ itemsJoin r is

/-- One world block: the imports, then the exports, then the
    closing brace. Total; deterministic; the world lane's render
    face. -/
def world (w : World) : String :=
  "world " ++ w.name ++ " {\n"
    ++ itemsJoin importItem w.imports
    ++ itemsJoin exportItem w.exports
    ++ "}\n"

/-- The world-file document: the package line + a blank line, then
    the world block. The component lane's artifact of record's
    render face (`gen/component-slice.wit`). -/
def worldFile (id : String) (w : World) : String :=
  "package " ++ id ++ ";\n\n" ++ world w

end Wit.Render
