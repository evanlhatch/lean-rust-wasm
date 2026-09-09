/-
# SchemaLang.Delta — delta-shaped contracts (the event-sourcing shape)

For each `@[schema]` RECORD, derive the change variant: the event-sourcing
shape that connects schema-lang to `Dbsp.ChangeSpec` (the change-structure
classes — patch/valid/diff/invert — D18). A table's row type gets a
companion change type:

    record user { id: u64, ... }
      ⇒ variant user-change { insert(user), update(user), remove(u64) }
        enum UserChange { Insert(User), Update(User), Remove(u64) }
        impl dbsp::Change for UserChange { ... }

Lowering decisions:
- `insert` / `update` carry the FULL record (v1 is full replacement —
  the Dbsp.ChangeSpec patch law `patch old Δ = new` with a self-contained
  delta; column-wise/positioned patches land with the faults package).
- `remove` carries the KEY field's type (the FIRST field — same key
  convention the oracle and codecs use). A record with no fields has no
  key, so it gets NO change type (`changeTy = none`).
- Only RECORDS get change types: variants/funcs/resources have no row
  identity in the store.

Non-goals (deliberate): diff generation (`Difference.diff` bodies), the
`ChangeInversion`/`Noc` instances — the emitted Rust is the CONTRACT
shape; the lawful instances are the engine's job.

Why a separate `deltaWitEmitter` (not folding the variants into
`witEmitter`): `wit/gateway.wit` is a byte-tied golden whose exact
content existing tests pin (`witChecks`); the change variants are
consumed by DBSP-side tooling, not the gateway world. A distinct
`wit/delta.wit` keeps the gateway world stable and gives the delta
artifact its own one-writer claim.
-/

import CodegenCore
import SchemaLang.Item
import SchemaLang.Emit.Wit
import SchemaLang.Emit.Rust

namespace SchemaLang

open CodegenCore.Emit (pascal kebab rustIdent snake)

/-! ## The change shape, target-neutral -/

/-- The change type's name: record `user` → `UserChange` (Pascal + suffix,
    the Rust/WIT-facing name). Non-records have no change type. -/
def Item.changeTypeName : Item → String
  | .record n _ => pascal n ++ "Change"
  | _ => ""

/-- The change variant's PAYLOAD type for a record: the record itself
    (`.ty n` — the caller wraps it in its target's variant/enum). `none`
    for non-records AND for field-less records (no key field). -/
def Item.changeTy : Item → Option Ty
  | .record n fields =>
      match fields with
      | [] => none
      | _ :: _ => some (.ty n)
  | _ => none

/-! ## WIT lowering -/

/-- The change variant as WIT text lines. The variant name and the record
    reference are kebab-mangled; `remove` carries the KEY field's WIT
    type. Empty list for non-records / key-less records. -/
def Item.changeWitDecl : Item → List String
  | .record n fields =>
      match fields.head? with
      | none => []
      | some key =>
          let ref := kebab n
          ["variant " ++ kebab n ++ "-change {"
          , "    insert(" ++ ref ++ "),"
          , "    update(" ++ ref ++ "),"
          , "    remove(" ++ SchemaLang.Emit.Wit.tyWit key.ty ++ "),"
          , "}"
          ]
  | _ => []

/-! ## Rust lowering -/

/-- The change ENUM + its `dbsp::Change` impl (the `Dbsp.Change` class
    shape: `patch` + `valid`). `insert`/`update` replace the row;
    `remove` keeps the last-seen value (the deletion is the key join's
    signal). Empty list for non-records / key-less records.

    Derives follow the Rust emitter's Eq discipline: a change enum whose
    payload record is float-free gets `Eq` (the same `hasFloat` check
    `schemaItems` uses). The full record is the payload, so the check is
    over the record's own fields. -/
def Item.changeRustItems : Item → List CodegenCore.Emit.Rust.Item
  | .record n fields =>
      match fields.head? with
      | none => []
      | some key =>
          let change := Item.changeTypeName (.record n fields)
          let full := SchemaLang.Emit.Rust.tyRust (.ty n)
          let keyTy := SchemaLang.Emit.Rust.tyRust key.ty
          let eqOk := !(fields.any (fun f => SchemaLang.Emit.Rust.hasFloat f.ty))
          let derives := if eqOk then SchemaLang.Emit.Rust.baseDerives ++ ["Eq"]
                         else SchemaLang.Emit.Rust.baseDerives
          [ .enum change derives
              [ s!"Insert({full})"
              , s!"Update({full})"
              , s!"Remove({keyTy})"
              ]
          , .comment
              s!"ChangeSpec: the Dbsp.Change shape (patch + valid) for {change}."
          , .implTrait s!"dbsp::Change<{full}>" change []
              [ ("patch(&self, base: &" ++ full ++ ") -> " ++ full
                , "match self { Self::Insert(u) | Self::Update(u) => "
                  ++ "u.clone(), Self::Remove(_) => base.clone() }")
              , ("valid(&self, base: &" ++ full ++ ") -> bool", "true")
              ]
          ]
  | _ => []

/-! ## Test emission (Stage E: certified delta impls) -/

/-- A literal Rust expression for a fresh value of a `Ty` in test
    position; `none` when no self-contained literal exists (a nested
    record payload — such records get no round-trip test). -/
def litTy? : Ty → Option String
  | .bool => some "true"
  | .u8 | .u16 | .u32 | .u64 | .i8 | .i16 | .i32 | .i64 => some "1"
  | .f32 | .f64 => some "1.0"
  | .string => some "\"a\".into()"
  | .bytes => some "vec![]"
  | .option _ => some "None"
  | .result ok _ => ("Ok(" ++ · ++ ")") <$> litTy? ok
  | .list _ => some "vec![]"
  | .future a | .stream a => litTy? a
  | .ty _ => none

/-- A record → the items of ONE patch-roundtrip test (the executable
    sibling of the ChangeSpec patch law: `Update`'s patch replaces the
    base, `Remove`'s keeps it — `valid` always). The value is built
    from per-field literals; UFCS (`dbsp::Change::patch`) keeps the
    body free of trait imports. Empty when the record has no key or a
    field has no self-contained literal.

    The attribute lines are the `raw` escape hatch — the Item grammar
    has no attribute node, and `#[test]`/`#[cfg(test)]` are the only
    two this emitter needs. -/
def Item.changeTestItems : Item → List CodegenCore.Emit.Rust.Item
  | .record n fields =>
      let lits? := fields.mapM fun f =>
        (litTy? f.ty).map fun lit => s!"{rustIdent f.name} : {lit}"
      match fields.head?, lits? with
      | some _, some lits =>
          let change := Item.changeTypeName (.record n fields)
          let full := SchemaLang.Emit.Rust.tyRust (.ty n)
          let body := String.intercalate "\n"
            [ s!"let base = {full} \{{String.intercalate ", " lits}};"
            , s!"let delta = {change}::Update(base.clone());"
            , s!"assert_eq!(dbsp::Change::patch(&delta, &base), base);"
            , s!"assert!(dbsp::Change::valid(&delta, &base));"
            ]
          [ .raw "#[test]"
          , .fn s!"fn {snake n}_change_roundtrip()" body
          ]
      | _, _ => []
  | _ => []

/-- The whole `#[cfg(test)] mod tests` — one patch-roundtrip test per
    keyed record. Empty when no record qualifies (keeps the module out
    of files with nothing to certify). -/
def Item.changeTestModule (items : List Item) :
    List CodegenCore.Emit.Rust.Item :=
  let tests := items.flatMap Item.changeTestItems
  if tests.isEmpty then []
  else [ .raw "#[cfg(test)]"
       , .mod_ "tests" (.use_ "super::*" :: tests) ]

end SchemaLang

/-! ## The emitters -/

open SchemaLang (Item)

/-- The Rust delta emitter: all change enums + ChangeSpec impls, one file. -/
def deltaEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "delta"
  style := .doubleSlash
  specSource := "Demo.lean"
  outputs := ["../../src/delta_generated.rs"]
  run items :=
    [{ path := "../../src/delta_generated.rs"
       contents :=
         CodegenCore.Emit.Rust.renderModule
           ([ .use_ "crate::dbsp"
            , .use_ "crate::schema_generated::*"
            ]
            ++ items.flatMap Item.changeRustItems
            ++ Item.changeTestModule items) }]

/-- The WIT delta emitter: all change variants, one file (see the module
    header for why this is separate from `witEmitter`). Repo-root-relative
    path like the other emitters — the forge byte-tie covers it. -/
def deltaWitEmitter : CodegenCore.Emit.Emitter (List SchemaLang.Item) where
  name := "delta-wit"
  style := .doubleSlash
  specSource := "Demo.lean"
  outputs := ["../../wit/delta.wit"]
  run items :=
    [{ path := "../../wit/delta.wit"
       contents :=
         String.join ((items.flatMap Item.changeWitDecl).map (· ++ "\n")) }]
