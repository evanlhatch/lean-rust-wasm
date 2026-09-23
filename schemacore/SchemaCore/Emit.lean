/-
# SchemaCore.Emit — the slice's emitter + the shared regen core

Owner: the SchemaCore agent (the macht tree, `schemacore/`).
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
-/

import Lean
import SchemaCore.Item
import SchemaCore.Register
import SchemaCore.Emit.Rust

open Kit

namespace SchemaCore

/-! ## The WIT-flavored rendering -/

/-- One item → one WIT record block (pure, total). -/
def renderItem (item : Item) : String :=
  let lines := item.fields.map fun f => s!"    {f.name}: {renderTy f.ty},"
  let body := String.intercalate "\n" lines
  "  record " ++ item.wireName ++ " {\n" ++ body ++ "\n  }\n"

/-- The registry → the artifact body (pure, total; the fold over the
    universe). -/
def renderWit (reg : DataRegistry Item) : String :=
  "package macht:slice;\n\ninterface items {\n" ++
  String.intercalate "" (reg.items.map renderItem) ++
  "}\n"

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
  run reg := [{ path := "gen/schema-slice.wit", contents := renderWit reg }]
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
  let files :=
    witEmitter.runCertified reg reg.nodup ++
    Emit.Rust.rustEmitter.runCertified reg reg.nodup
  return { reg := reg, files := files }

end SchemaCore
