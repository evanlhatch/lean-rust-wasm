/-
# SchemaCore.Emit.Ts — the TypeScript target (the SECOND CodeTarget row)

Owner: the codegen-target lane (the mandate tree, `schemacore/`).

THE MARGINAL-COST ROW (notes/design-forward-surface.md §1's success
metric): this module is the proof that the `Spine.CodeTarget` factoring
turned "the Rust emitter" into "the spine, parameterized". Everything
structural — the section order, the record-block join, the face
placement, the emitter row, the byte-tie — is the SPINE's; this file
carries only the target rows: the type map, the two codec-template
algs, the prelude, the universe faces, the builder face, the record
template.

THE WIRE HONESTY (the Rust lane's serde note mirrored): the schema's
CANONICAL codec is `SchemaCore.Codec`'s byte wire (the duel vectors are
its differential). THIS target's codec face is JSON — the ECOSYSTEM
INTEROP wire for TS: a missing field refuses, a wrong-typed value
refuses, `null` is `none`, the field names ride as-is. Never a second
wire spec — the wire of record stays the codec's.

THE DECLARED LOSSES (each named, none silent):
- The scalar precision note: JSON numbers carry no u64/i64 past 2^53 —
  the type aliases (`u64 = number`) keep the scalar DISTINCT at the
  type level, and the DECODE validators gate the range; the canonical
  bytes cover the full range. (The Rust lane's varint-cap note
  mirrored: different typed reason, the refusal is on both sides.)
- `bounded` renders as `u64` (the cap is schema metadata the JSON face
  cannot carry — the WIT lane's declared retraction row, mirrored; the
  decode validator gates the value at the cap it receives).
- The builder's guarantee is RUNTIME here (a `SchemaError` naming the
  never-set fields) — the typestate discipline is the RUST row's
  (TS's type system carries no set-ness index in this face's honest
  v0; the named gap). No default is ever smuggled, not even an error
  default: a never-set field refuses `build`.
- The migration lane has NO TS face yet (the Rust lane's retype gap
  mirrored — the remedy registry is Lean-side); `lanes := []`.

The five questions (notes/v3/01-core.md):
- root: Crossing — the universe (`DataRegistry Item`) read into the
  TS target grammar (interfaces + the JSON codec + the builder).
- carrier grade: the naming precondition is `DataRegistry`'s
  nodup-in-the-type (the same face the WIT/Rust lanes carry).
- spine reading: the Interpretation stage (01 §5) — a `Spine.CodeTarget`
  row over the ONE regen core (the SECOND row; the marginal-cost
  metric's measurement).
- ladder rung: total structural folds; the artifact's byte-tie is
  `gates gen-check` (the duel manifest's channel — one tie per
  artifact).
- gate row: gen-check byte-ties `gen/schema-slice.ts`; ownership +
  artifact-headers read the emitter; coverage grows the TS column.
-/

import SchemaCore.Emit.Spine
import SchemaCore.Emit.Profiles
import SchemaCore.Item
import Kit.Mangle
import Kit.Text

open Kit
open Kit.Emit

namespace SchemaCore.Emit.Ts

/-! ## The type map — the target's fold over the shared `Descr` lift -/

/-- The key universe's TS spelling (the key sub-universe's slice). -/
def keyTyTs : KeyTy → String
  | .bool => "boolean"
  | .u64 => "u64"
  | .i64 => "i64"
  | .string => "string"

/-- The description's TS text: wrappers nest, leaves delegate. The
    scalar aliases (`u64`/`i64`) keep the scalars distinct at the type
    level (the prelude's precision note). A nested PRODUCT cannot reach
    field position (the registry's rows are flat — the SD0006 refusal
    is upstream's guarantee); the arm is the honest dead branch, never
    a fabricated type. -/
def tyTsAlg : TyAlg String where
  bool := "boolean"
  u64 := "u64"
  i64 := "i64"
  string := "string"
  option _ :=
      "unknown /* unreachable: descrOfTy lifts the wrappers */"
  list _ :=
      "unknown /* unreachable: descrOfTy lifts the wrappers */"
  result ok err := "{ ok: " ++ ok ++ " } | { err: " ++ err ++ " }"
  map k v := "Array<[" ++ keyTyTs k ++ ", " ++ v ++ "]>"
  set k := "Array<" ++ keyTyTs k ++ ">"
  bounded _ := "u64"

/-- The leaf shapes' TS text = the fold (the Rust lane's `tyRustPrim`
    shape — the recursion rides `foldTy`'s structural walk, never a
    `descrOfTy` re-entry the termination check cannot see). -/
def tyTsPrim : Ty → String := foldTy tyTsAlg

/-- The description's TS text: wrappers nest, leaves delegate. A
    nested PRODUCT cannot reach field position (the registry's rows are
    flat — the SD0006 refusal is upstream's guarantee); the arm is the
    honest dead branch, never a fabricated type. -/
def tyTs : Descr → String
  | .prim t => tyTsPrim t
  | .option d => tyTs d ++ " | null"
  | .list d => "Array<" ++ tyTs d ++ ">"
  | .product _ _ =>
      "unknown /* unreachable: the registry's rows are flat (SD0006) */"

/-! ## The codec generation — the wire's TS face (JSON) -/
-- The TS string literal is `Spine.strLit` (the shared C-family escape —
-- the enforcement wave's dedupe; the field-name spellings ride as-is,
-- the mangle gap — the Rust lane's note).

/-- The KEY position's decode validators: the expression-form key fold
    (the TS face's form — the validating expression; the Rust lane's
    bind-statement form is its own). -/
def keyDecTs : KeyTyAlg (String → String) where
  bool e := "decBool(" ++ e ++ ")"
  u64 e := "decU64(" ++ e ++ ")"
  i64 e := "decI64(" ++ e ++ ")"
  string e := "decString(" ++ e ++ ")"

/-- THE ENCODE STATEMENTS = the fold: the JSON face's value model
    carries the shapes natively (a boolean is a boolean; an option is
    the value or `null`; a list is the array; a map is the pair array,
    the Rust lane's order-preserving divergence mirrored; a result is
    the tagged object) — the rows are the identity, and the wire
    discipline (the refusals) lives entirely in the DECODE face. -/
def encTsAlg : TyAlg (String → String) where
  bool := id
  u64 := id
  i64 := id
  string := id
  option _ := id
  list _ := id
  result _ _ := id
  map _ _ := id
  set _ := id
  bounded _ := id

/-- THE DECODE STATEMENTS = the fold: each row is a VALIDATING
    expression (the prelude's typed refusals — a missing field refuses,
    a wrong-typed value refuses, never a silent misparse). `e` is the
    parsed object's field expression. -/
def decTsAlg : TyAlg (String → String) where
  bool e := "decBool(" ++ e ++ ")"
  u64 e := "decU64(" ++ e ++ ")"
  i64 e := "decI64(" ++ e ++ ")"
  string e := "decString(" ++ e ++ ")"
  option a := fun e =>
      "decOption((v) => " ++ a "v" ++ ", " ++ e ++ ")"
  list a := fun e =>
      "decList((v) => " ++ a "v" ++ ", " ++ e ++ ")"
  result ok err := fun e =>
      "decResult((v) => " ++ ok "v" ++ ", (v) => " ++ err "v" ++ ", " ++ e ++ ")"
  map k v := fun e =>
      "decMap((v) => " ++ foldKeyTy keyDecTs k "v" ++ ", (v) => " ++
        v "v" ++ ", " ++ e ++ ")"
  set k := fun e =>
      "decSet((v) => " ++ foldKeyTy keyDecTs k "v" ++ ", " ++ e ++ ")"
  bounded cap := fun e =>
      "decBounded(" ++ toString cap ++ ", " ++ e ++ ")"

/-! ## The generated runtime (the helpers the codecs call) -/

/-- The TS artifact's prelude: the two-faces honesty note + the typed
    error + the validating decode helpers. `export` (a used-or-not
    helper is API, never dead code — the Rust lane's `pub` rule). -/
def tsPrelude : Text :=
  .str "// THE TWO FACES (the honesty note — the Rust lane's serde note
// mirrored): the schema's CANONICAL codec is SchemaCore.Codec's BYTE
// wire (the Lean codec; the duel vectors are its differential). THIS
// artifact is the JSON INTEROP face — a different encoding with its
// own conventions: a missing field refuses, a wrong-typed value
// refuses, `null` is `none`, the field names ride as-is. Never a
// second wire spec: the wire of record stays the codec's.
// The scalar note (the declared loss): JSON numbers carry no u64/i64
// past 2^53 — the type aliases keep the scalars distinct at the type
// level and the decode validators gate the range; the canonical bytes
// cover the full range.

/// The typed refusal — every out-of-policy shape maps to an error
/// (SchemaCore.Codec's accepted-shape policy mirrored at the JSON
/// face). Never a silent misparse.
export class SchemaError extends Error {
    constructor(message: string) {
        super(message);
        this.name = \"SchemaError\";
    }
}

export function decBool(x: unknown): boolean {
    if (typeof x !== \"boolean\") throw new SchemaError(\"expected boolean\");
    return x;
}

export function decU64(x: unknown): u64 {
    if (typeof x !== \"number\" || !Number.isInteger(x) || x < 0 || x >= 2 ** 53)
        throw new SchemaError(\"expected u64 (the 2^53 note)\");
    return x;
}

export function decI64(x: unknown): i64 {
    if (typeof x !== \"number\" || !Number.isInteger(x) || !(x >= -(2 ** 53)) || x >= 2 ** 53)
        throw new SchemaError(\"expected i64 (the 2^53 note)\");
    return x;
}

export function decString(x: unknown): string {
    if (typeof x !== \"string\") throw new SchemaError(\"expected string\");
    return x;
}

export function decOption<A>(f: (x: unknown) => A, x: unknown): A | null {
    if (x === null) return null;
    return f(x);
}

export function decList<A>(f: (x: unknown) => A, x: unknown): Array<A> {
    if (!Array.isArray(x)) throw new SchemaError(\"expected list\");
    return x.map(f);
}

export function decSet<A>(f: (x: unknown) => A, x: unknown): Array<A> {
    if (!Array.isArray(x)) throw new SchemaError(\"expected set\");
    return x.map(f);
}

export function decMap<K, V>(
    k: (x: unknown) => K, v: (x: unknown) => V, x: unknown,
): Array<[K, V]> {
    if (!Array.isArray(x)) throw new SchemaError(\"expected map (the pair array)\");
    return x.map((p) => [k(p[0]), v(p[1])]);
}

export function decResult<O, E>(
    ok: (x: unknown) => O, err: (x: unknown) => E, x: unknown,
): { ok: O } | { err: E } {
    if (typeof x !== \"object\" || x === null)
        throw new SchemaError(\"expected result\");
    if (\"ok\" in x) return { ok: ok((x as { ok: unknown }).ok) };
    if (\"err\" in x) return { err: err((x as { err: unknown }).err) };
    throw new SchemaError(\"expected result tag\");
}

export function decBounded(cap: number, x: unknown): u64 {
    if (typeof x !== \"number\" || !Number.isInteger(x) || x < 0 || x >= cap)
        throw new SchemaError(\"expected bounded < cap\");
    return x;
}"

/-! ## The closed universe's TS faces — the closed enums (string
     unions) + the branded key materials -/

/-- The closed universe's TS faces (NOT registry-dependent — the
    universe's own faces, emitted once; the Rust lane's universe block
    mirrored at the honest TS depth):

- THE CLOSED ENUMS as string unions: the tags are the LEAN ctor
  names, snake_case (the model's tag discipline). A closed enum's
  exhaustiveness rides TS's union checking (the consumer's switch
  without the default arm refuses to compile on a new tag).
- THE SCALAR ALIASES: `u64`/`i64` distinct at the type level (the
  prelude's precision note).
- THE KEY MATERIALS as branded types (the keys lane's admission gate's
  TS face — only scalars are key material; the brand is the
  construction point's marker, the honest v0 without a runtime
  try_new lane). -/
def tsUniverseTypes : Text :=
  .str "// THE CLOSED UNIVERSE'S TS FACES (the schema's closed enums + the
// scalar sub-universe + the key materials — the model's guarantees
// carried in TS's types, the Rust lane's universe block mirrored).

/// The closed Profile enum (SchemaCore.Profile — WHICH semantic a
/// scalar carries). CLOSED over the three slots: the tags are the
/// LEAN ctor names; `fast` is the hardware-float trade (its forfeits
/// are named in the model, never hidden).
export type Profile = \"plain\" | \"deterministic\" | \"fast\";

/// The closed scalar sub-universe (SchemaCore.Ty's KeyTy — the
/// map/set keys + the declared keys' admitted materials).
export type KeyTy = \"bool\" | \"u64\" | \"i64\" | \"string\";

/// The scalar aliases (the prelude's precision note).
export type u64 = number;
export type i64 = number;

/// The key MATERIALS (the keys lane's admission gate `keyOfTy`'s TS
/// face): branded scalars — the brand marks the admitted material.
declare const brand: unique symbol;
type Brand<T, B extends string> = T & { readonly [brand]: B };

export type KeyBool = Brand<boolean, \"KeyBool\">;
export type KeyU64 = Brand<u64, \"KeyU64\">;
export type KeyI64 = Brand<i64, \"KeyI64\">;
export type KeyString = Brand<string, \"KeyString\">;"

/-! ## The builder face — the API discipline's TS row -/

/-- One record's builder block (the face's TS row). The Rust lane's
    typestate builder mirrored at the honest TS depth: the chained
    setters + the `build` that REFUSES the never-set fields (a
    `SchemaError` naming them) — the RUNTIME guarantee (the typestate
    is the Rust row's; the named gap in the module header). No default
    is ever smuggled: a never-set field refuses, never a default. -/
def renderBuilderTs (item : Item) : Text :=
  let name := Kit.pascal (lastName item.name)
  let fts := item.fields.map fun f => (f.name, tyTs (Spine.descrOfTy f.ty))
  let setters := String.intercalate "\n" (fts.map fun p =>
    "    " ++ p.1 ++ "(v: " ++ p.2 ++ "): this { this.values["
      ++ Spine.strLit p.1 ++ "] = v; return this; }")
  let checks := String.intercalate "\n" (fts.map fun p =>
    "        if (this.values[" ++ Spine.strLit p.1 ++ "] === undefined) missing.push("
      ++ Spine.strLit p.1 ++ ");")
  Text.cat
    [ .str "// The builder face (the Rust lane's typestate discipline's honest\n"
    , .str "// TS row: the never-set fields REFUSE build — at runtime here, the\n"
    , .str "// named gap; no default is ever smuggled).\n"
    , .str ("export class " ++ name ++ "Builder {\n")
    , .str ("    private values: Partial<" ++ name ++ "> = {};\n\n")
    , .str setters
    , .str "\n\n"
    , .str ("    build(): " ++ name ++ " {\n")
    , .str "        const missing: string[] = [];\n"
    , .str checks
    , .str "\n        if (missing.length > 0) {\n"
    , .str "            throw new SchemaError(\n"
    , .str "                \"fields never set: \" + missing.join(\", \"));\n"
    , .str "        }\n"
    , .str ("        return this.values as " ++ name ++ ";\n")
    , .str "    }\n"
    , .str "}\n" ]

/-! ## The record template — the SPINE's facts + the faces -/

/-- One item → one TS interface + the JSON codec fns + the builder
    face (pure, total) — the SPINE's record template at this lane's
    parameters (the facts are the spine's shared walk; the face is
    placed by name). -/
def tsRenderRecord :
    Spine.RecordFacts → (String → Option Text) → Text :=
  fun facts face =>
  let name := facts.name
  let fieldDecls := facts.fields.map fun p =>
    .str ("    " ++ p.1 ++ ": " ++ p.2 ++ ";")
  let encLines := (facts.fields.zip facts.enc).map fun p =>
    .str ("        \"" ++ p.1.1 ++ "\": " ++ p.2 ++ ",")
  let decLines := (facts.fields.zip facts.dec).map fun p =>
    .str ("        " ++ p.1.1 ++ ": " ++ p.2 ++ ",")
  Text.cat
    [ .str ("export interface " ++ name ++ " {\n")
    , Text.sepBy "\n" fieldDecls
    , .str "\n}\n\n"
    , .str ("export function encode" ++ name ++ "(v: " ++ name ++ "): string {\n")
    , .str "    return JSON.stringify({\n"
    , Text.sepBy "\n" encLines
    , .str "\n    });\n"
    , .str "}\n\n"
    , .str ("export function decode" ++ name ++ "(s: string): " ++ name ++ " {\n")
    , .str "    const o = JSON.parse(s) as Record<string, unknown>;\n"
    , .str "    return {\n"
    , Text.sepBy "\n" decLines
    , .str "\n    };\n"
    , .str "}\n\n"
    , face "builder" |>.getD .nil ]

/-! ## THE CODETARGET ROW — the TypeScript target -/

/-- THE TYPESCRIPT TARGET as a `Spine.CodeTarget` row: the section
    order, the record-block join, the face placement and the emitter
    row are the SPINE's; the type map, the two algs, the prelude, the
    universe faces and the builder face are this row's. No lanes yet
    (the migration lane's TS face is the named gap). -/
def tsTarget : Spine.CodeTarget where
  name := "ts"
  style := .doubleSlash
  outputPath := "gen/schema-slice.ts"
  tyText := tyTs
  identTy := fun s => Kit.pascal (lastName s)
  encRef := fun f => "v." ++ f
  decExpr := fun f => "o[" ++ Spine.strLit f ++ "]"
  encAlg := encTsAlg
  decAlg := decTsAlg
  prelude := tsPrelude
  universeTypes := Text.cat [tsUniverseTypes, Emit.Profiles.profilePhantomTs]
  faces := [{ name := "builder", render := renderBuilderTs }]
  faceNames := ["builder"]
  renderRecord := tsRenderRecord

/-- The registry → the TS artifact body's rope (the SPINE's section
    assembly at this row). -/
def tsRope (reg : DataRegistry Item) : Text :=
  Spine.spineLibRope tsTarget reg

/-- The TypeScript lane's emitter: the SECOND CodeTarget row — the
    SPINE's emitter row at this target (the name, the style, the
    output and the run are the spine's assembly; no extra outputs).
    `outputs_nodup` is in the type; the naming invariant is the
    registry's own nodup-in-the-type (one naming world, three
    renderings). -/
def tsEmitter : Emitter (DataRegistry Item) :=
  Spine.spineEmitter tsTarget

end SchemaCore.Emit.Ts
