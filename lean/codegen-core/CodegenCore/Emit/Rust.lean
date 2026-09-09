/-
# CodegenCore.Emit.Rust — the Rust target AST and printer

Lifted from flatland's `Codegen.Emit.Rust` (lean-v3 §7.2, lean4-mlir's
skel/Raw/Tok). The three-layer discipline:

    spec item ──► CodegenCore.Emit.Rust.Item (the TargetAst: nodes carry
                  emit metadata; field order is declaration order,
                  deterministic)
              ──► Std.Format ──► text

No string interpolation for STRUCTURE: item shape is the AST; interpolation
appears only inside leaf payloads (a function body is a `String` leaf — the
boring-template concession, audited: every leaf body is emitted through
`Item` nodes and the emitter counts them).

Design decisions:
- The AST is a *faithful subset* of Rust item syntax — enough for registry
  folds (structs, enums, impls, consts, fns, use decls). It is NOT a Rust
  parser target; there is no `Raw`/`Tok` split because nothing parses Rust
  back (the byte-tie CI is the Rust-side drift guard, per the lean4-mlir
  scoping lesson: prove the round-trip where a parser exists; diff the
  text where it doesn't).
- Names arrive PRE-MANGLED from `CodegenCore.Emit` (the one mangling
  module). This AST never case-converts.
- Determinism: no HashMap iteration anywhere in emitters; folds are over
  registry `List`s in registration order.
-/

namespace CodegenCore.Emit.Rust

/-- A Rust expression leaf we emit verbatim (template-instantiated by the
    emitter, never by the spec author). -/
abbrev Body := String

/-- A struct field: name + type text. -/
structure Field where
  name : String
  ty : String
deriving Repr, Inhabited

/-- The item grammar (module-level Rust). -/
inductive Item where
  | use_ (path : String)
  | const (name : String) (ty : String) (value : Body)
  | unitStruct (name : String) (derives : List String)
  | newtype (name : String) (inner : String) (derives : List String)
  | struct (name : String) (derives : List String) (fields : List Field)
  | enum (name : String) (derives : List String) (variants : List String)
  | implDisplay (name : String) (body : Body)
  | implTrait (trait : String) (forTy : String) (assocTypes : List (String × String))
      (methods : List (String × Body))
  | fn (sig : String) (body : Body)
  | macroCall (name : String) (args : List String)
  | mod_ (name : String) (items : List Item)
  | trait_ (name : String) (methodSigs : List String)
  | comment (content : String)
  | raw (content : String)   -- escape hatch; AUDITED and counted
deriving Repr, Inhabited

open Std.Format in
/-- The printer. Two-space indent is non-negotiable (rustfmt's). -/
partial def Item.format : Item → Std.Format
  | .use_ path => f!"use {path};"
  | .const name ty value => f!"pub const {name} : {ty} = {value};"
  | .unitStruct name derives =>
    deriveLine derives ++ line ++ f!"pub struct {name};"
  | .newtype name inner derives =>
    deriveLine derives ++ line ++ f!"pub struct {name}(pub {inner});"
  | .struct name derives fields =>
    deriveLine derives ++ line ++ f!"pub struct {name}" ++
      block (fields.map fun f => f!"pub {f.name} : {f.ty},")
  | .enum name derives variants =>
    deriveLine derives ++ line ++ f!"pub enum {name}" ++
      block (variants.map fun v => f!"{v},")
  | .implDisplay name body =>
    f!"impl std::fmt::Display for {name}" ++
      block [f!"fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result" ++
        block [body]]
  | .implTrait trait forTy assocTypes methods =>
    let assocs := assocTypes.map fun (n, t) => f!"type {n} = {t};"
    let meths := methods.map fun (sig, body) => f!"fn {sig}" ++ block [body]
    f!"impl {trait} for {forTy}" ++ block (assocs ++ meths)
  | .fn sig body => f!"pub {sig}" ++ block [body]
  | .macroCall name args =>
    -- macro_rules! patterns reject a trailing comma after the last arg —
    -- intercalate, don't terminate (unlike struct fields / enum variants)
    f!"{name}!" ++ f!" \{" ++ Std.Format.nest 2 (line ++
      (Std.Format.joinSep args (f!"," ++ line))) ++ line ++ f!"}"
  | .mod_ name items =>
    f!"pub mod {name}" ++ block (items.map Item.format)
  | .trait_ name methodSigs =>
    f!"pub trait {name}" ++ block (methodSigs.map fun sig => f!"fn {sig};")
  | .comment content => f!"// {content}"
  | .raw content => content
where
  deriveLine : List String → Std.Format :=
    fun ds => if ds.isEmpty then ""
      else f!"#[derive({String.intercalate ", " ds})]"
  block : List Std.Format → Std.Format :=
    fun fs => f!" \{" ++ Std.Format.nest 2 (line ++ joinSep fs line) ++ line ++ f!"}"

/-- A whole module = items, trailing newline. Callers prepend
    `CodegenCore.Emit.header`. -/
def renderModule (items : List Item) : String :=
  (Std.Format.line.joinSep (items.map Item.format) |>.pretty) ++ "\n"

end CodegenCore.Emit.Rust
