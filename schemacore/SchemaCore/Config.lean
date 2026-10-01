/-
# SchemaCore.Config — the config face (08 §34: the configuration)

Owner: the config-face agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/08-capabilities.md §34 (a config = a
schema record + the override ORDER as data — last-wins is NOT a
semilattice — + the schema's own validation) + design-wave-30.md C4
(the override fold IS the update lane's ColPath write spine; the
sources are TextKit grammars; validation IS the check lane; the Rust
config rides the codegen spine).

The face (each piece names the discipline it REUSES — never a
parallel table):

- THE SCHEMA RECORD: `ConfigSchema` = an `Item` (the registry's record
  — the config IS a schema record) + the check rows (`Pred` over the
  item's own fields — the check lane's fragment, `CheckItem`'s
  discipline at the config granularity).
- THE OVERRIDE: a sparse write IS the update lane's `SetClause` (the
  ColPath write spine — a write to a missing or mistyped column is
  UNCONSTRUCTIBLE, the GADT index); `applySources` = the update lane's
  `applySets` fold over the prioritized sources.
- THE ORDER AS DATA: `ConfigSource` (file < env < cli) + `prioritize`
  (the stable rank sort). Last-wins is NOT a semilattice — the
  noncommutativity is STATED AND PROVED: the fold-append law (the
  honest associativity), the same-field double-write law + its
  noncommutation corollary (distinct values NEVER commute), the
  disjoint-field commutation (the update lane's kernel law), and the
  source-order witness (swapping the sources' order swaps the result).
- THE SOURCES: the raw `(key, value)` pairs lower against the schema
  (`lowerPair`/`lowerPairs`) — unknown keys refuse through the ONE
  engine's closed-world Diag (the valid space = the field names, the
  did-you-mean cannot be skipped), mistyped values refuse with the
  type named (`Fold.renderTy`'s ONE spelling). The TEXT formats are
  TextKit grammar values (`TextKit.ConfigFormat` — the file/env/CLI
  spellings with their round-trip laws); the os-delivered env halves
  ride `lowerPair` directly.
- THE VALIDATION: `validateConfig` — the check rows over the merged
  record; a violated constraint is a curated Diag (E-codes from the
  PERSISTED registry: the CF family, allocated rows 198-200).

DELIBERATE EXCLUSIONS (the leftover rule, each names its reason): no
`schema_config` elaboration command — no consumer surface yet (the
lane's data + laws + lowering are the honest minimal; the Rust
artifact FILE lands with its first emitted crate — the byte-tie bars
a writer without an artifact path, the golden pins in SchemaTests are
the face's teeth); no non-scalar source syntax (list/map/set/result
values have no consumer config — the scalar fragment + option covers
every knob that exists); no i64 source spelling (no i64 knob exists;
the parse refuses honestly rather than guessing a sign convention).

The five questions (notes/v3/01-core.md): root = the config discipline
(08 §34 — data); carrier = the GADT write path (SetClause's ColPath
index) + the persisted E-code rows; spine reading = registration-free:
the schema record IS the item model's rows, the override fold IS the
update lane's, the validation IS the check lane's — the face is the
COMPOSITION, cited, never re-rolled; ladder rung = decide/
decidableNow for every checkable fact over concrete configs (the
order laws are equalities/inequalities over the write spine); gate
row = SchemaTests' configSpec (the order-law pins + the refusal teeth
+ the negative controls) + the axiom report.

Core-only (imports SchemaCore.Update + SchemaCore.Pred + SchemaCore.
Fold + SchemaCore.Emit.Rust + Kit.Diag — the cone rule; TextKit rides
behind Kit's envelope).
-/

import SchemaCore.Update
import SchemaCore.Pred
import SchemaCore.Check
import SchemaCore.Fold
import SchemaCore.Emit.Rust
import Kit.Diag

namespace SchemaCore

/-! ## the E-codes (the CF family — the persisted registry's rows 198-200) -/

/-- The config face's E-codes — the CF family, allocated from the
    PERSISTED registry (`notes/code-registry.txt`; 05 §4's
    stable-allocation rule). One row per FAILURE KIND, never per
    site. -/
def eCF0001 : Kit.ECode := ⟨"CF0001"⟩  -- an unknown key (the closed world: the field names)

def eCF0002 : Kit.ECode := ⟨"CF0002"⟩  -- a mistyped value (the field's own type refuses)

def eCF0003 : Kit.ECode := ⟨"CF0003"⟩  -- a declared constraint is violated

/-- The config refusal's text, in the ONE envelope's rendering: the
    failure kind rides the registry's CF row, the text keeps the
    `config:` channel prefix. -/
def configDiag (code : Kit.ECode) (message : String) : Kit.Diag :=
  { code := code, message := s!"config: {message}", severity := .error }

/-! ## the config schema record -/

/-- THE CONFIG SCHEMA: a schema record (the item model's rows) + the
    record's own validation (the check rows — the check lane's `Pred`
    fragment over the item's OWN fields). -/
structure ConfigSchema where
  item : Item
  checks : List (Pred item.fields)

/-- The typed read: the u64 column's value (the knobs' face; `none`
    for a missing or non-u64 field — a refusal, never a zero). -/
def readNat (fs : List Field) (r : RowVals fs) (name : String) : Option Nat :=
  match RowVals.project? fs r name with
  | some ⟨.u64, .u64 v⟩ => some v.toNat
  | _ => none

/-! ## the scalar source fragment -/

/-- The scalar text-parse (the closed fragment the config face
    admits: bool/u64/string + option; the non-scalar Tys refuse —
    the header's named exclusion). A mistyped value is `none` — the
    refusal's curated Diag lives at the lowering (`lowerPair`). -/
def parseValue : (t : Ty) → String → Option (Value t)
  | .bool, s =>
      if s == "true" then Option.some (.bool true)
      else if s == "false" then Option.some (.bool false)
      else Option.none
  | .u64, s =>
      s.toNat?.bind fun n =>
        if n < 2 ^ 64 then Option.some (.u64 (UInt64.ofNat n)) else Option.none
  | .string, s => Option.some (.string s)
  | .option a, s =>
      if s == "none" then Option.some .none
      else (parseValue a s).map Value.some
  | _, _ => Option.none

/-- The scalar default (the record's zero face; the non-scalar Tys
    have no default — the typed-knob consumer's fallback is the
    caller's). -/
def scalarDefault : (t : Ty) → Option (Value t)
  | .bool => Option.some (.bool false)
  | .u64 => Option.some (.u64 0)
  | .i64 => Option.some (.i64 0)
  | .string => Option.some (.string "")
  | .option _ => Option.some .none
  | _ => Option.none

/-- The record's default row (`none` when any field is non-scalar —
    the honest partial: a config schema over non-scalar fields has no
    zero face yet). -/
def initialRow : (fs : List Field) → Option (RowVals fs)
  | [] => Option.some .nil
  | ⟨_, t⟩ :: gs =>
      match scalarDefault t, initialRow gs with
      | Option.some v, Option.some vs => Option.some (.cons v vs)
      | _, _ => Option.none

/-! ## the lowering (raw pairs → typed overrides, the curated refusals) -/

/-- The recursive clause lowering (the GADT's construction — the head
    case builds `.here` at the head's OWN type; the tail case lifts
    through `.there`). `all` is the WHOLE field list — the tail
    recursion shrinks `fs`, but the unknown-key refusal enumerates the
    FULL valid space (the field names) through the ONE closed-world
    constructor (`Kit.Diag.closedWorld`: got + valid + the ONE
    engine's did-you-mean — `Kit.suggestFor` fills the envelope's
    suggest slot, so the discipline cannot be skipped). -/
def lowerClause : (all : List Field) → (fs : List Field) → (key val : String) →
    Except Kit.Diag (SetClause fs)
  | all, [], key, _ =>
      .error (Kit.Diag.closedWorld eCF0001 s!"unknown key `{key}`" .error key
        (all.map (·.name)))
  | all, ⟨n', t'⟩ :: gs, key, val =>
      if n' == key then
        match parseValue t' val with
        | Option.none =>
            .error (configDiag eCF0002
              s!"`{val}` is not a {renderTy t'} (for key `{n'}`)")
        | Option.some v => .ok { field := ⟨n', t'⟩, path := .here, value := v }
      else
        (lowerClause all gs key val).map
          fun c => { field := c.field, path := ColPath.there c.path, value := c.value }

/-- THE lowering: one raw pair against the schema — the clause walk's
    own closed-world refusal (the field names are the valid space,
    `Kit.suggestFor` the did-you-mean; no post-hoc upgrade). -/
def lowerPair (fs : List Field) (key val : String) :
    Except Kit.Diag (SetClause fs) :=
  lowerClause fs fs key val

/-- The lowering of a whole source's pairs (first refusal wins — the
    source is unusable until its whole face is typed). -/
def lowerPairs (fs : List Field) (pairs : List (String × String)) :
    Except Kit.Diag (List (SetClause fs)) :=
  pairs.mapM fun p => lowerPair fs p.1 p.2

/-! ## the override ORDER as data -/

/-- The config sources (the precedence's carriers). -/
inductive ConfigSource where
  | file   -- the config file: the BASE layer
  | env    -- the environment: overrides the file
  | cli    -- the command line: overrides everything
deriving BEq, Repr

/-- The rank (file < env < cli — the discipline's ORDER as data). -/
def ConfigSource.rank : ConfigSource → Nat
  | .file => 0
  | .env => 1
  | .cli => 2

/-- One source's sparse overrides (each a typed clause — the update
    lane's write spine). -/
structure SourceOverrides (fs : List Field) where
  src : ConfigSource
  overrides : List (SetClause fs)

/-- The rank-ordered insert (STABLE: a later-delivered source at an
    equal rank goes AFTER the delivered ones — the last-wins fold
    reads the delivery order within a rank). -/
def insertSource : List (SourceOverrides fs) → SourceOverrides fs →
    List (SourceOverrides fs)
  | [], s => [s]
  | s' :: ss, s =>
      if s.src.rank < s'.src.rank then s :: s' :: ss
      else s' :: insertSource ss s

/-- The precedence discipline: the stable rank fold (file first, cli
    last — the delivery order kept within a rank). -/
def prioritize (ss : List (SourceOverrides fs)) : List (SourceOverrides fs) :=
  ss.foldl insertSource []

/-- The sources flattened in precedence order (the fold's input). -/
def flattenSources (ss : List (SourceOverrides fs)) : List (SetClause fs) :=
  (prioritize ss).map (·.overrides) |>.flatten

/-- THE OVERRIDE FOLD: the update lane's `applySets` over the
    prioritized sources — the ColPath write spine, last-wins. -/
def applySources (r : RowVals fs) (ss : List (SourceOverrides fs)) :
    RowVals fs :=
  applySets (flattenSources ss) r

/-! ## the order's laws -/

/-- THE APPEND LAW (the honest associativity): folding os2 over the
    os1-merged record = folding the CONCATENATION — grouping is free;
    the ORDER within the list is everything. -/
theorem applySets_append {fs : List Field} :
    ∀ (os1 os2 : List (SetClause fs)) (r : RowVals fs),
      applySets os2 (applySets os1 r) = applySets (os1 ++ os2) r := by
  intro os1
  induction os1 with
  | nil => intro os2 r; rfl
  | cons c cs ih =>
      intro os2 r
      show applySets os2 (applySets cs (c.path.set r c.value)) = _
      exact ih os2 (c.path.set r c.value)

/-- The same-path double write (the fold's snoc face): the LAST wins. -/
theorem ColPath.set_set_same {n : String} {t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (row : RowVals fs)
      (v₁ v₂ : Value t),
      ColPath.set p (ColPath.set p row v₁) v₂ = ColPath.set p row v₂ := by
  intro fs p
  induction p with
  | here => intro row v₁ v₂; cases row; rfl
  | there p ih =>
      intro row v₁ v₂
      cases row with
      | cons a vs =>
          simp only [ColPath.set]
          rw [ih vs v₁ v₂]

/-- The same-path write's injectivity: equal results, equal values
    (the noncommutativity's read — the write spine's GADT index makes
    the injection structural). -/
theorem ColPath.set_inj {n : String} {t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (row : RowVals fs)
      (v₁ v₂ : Value t),
      ColPath.set p row v₁ = ColPath.set p row v₂ → v₁ = v₂ := by
  intro fs p
  induction p with
  | here =>
      intro row v₁ v₂ hEq
      cases row with
      | cons a vs =>
          rw [ColPath.set, ColPath.set, RowVals.cons.injEq] at hEq
          exact hEq.1
  | there p ih =>
      intro row v₁ v₂ hEq
      cases row with
      | cons a vs =>
          rw [ColPath.set, ColPath.set, RowVals.cons.injEq] at hEq
          exact ih vs v₁ v₂ hEq.2

/-- THE NONCOMMUTATIVITY (last-wins is NOT a semilattice): two writes
    at the same field with distinct values NEVER commute — the fold's
    last-wins law reduces both orders to single writes, and the write
    spine's injectivity reads off the distinct values. -/
theorem ColPath.set_set_noncommute {n : String} {t : Ty} :
    ∀ {fs : List Field} (p : ColPath n t fs) (row : RowVals fs)
      (v₁ v₂ : Value t), v₁ ≠ v₂ →
      ColPath.set p (ColPath.set p row v₁) v₂
        ≠ ColPath.set p (ColPath.set p row v₂) v₁ := by
  intro fs p row v₁ v₂ hne hEq
  rw [ColPath.set_set_same p row v₁ v₂, ColPath.set_set_same p row v₂ v₁] at hEq
  exact hne (ColPath.set_inj p row v₂ v₁ hEq).symm

/-- THE DISJOINT COMMUTATION: two writes at DISTINCT fields commute —
    the update lane's kernel law (`ColPath.set_commute_disjoint`) at
    the clause granularity. -/
theorem setClause_comm_disjoint {fs : List Field}
    (c₁ c₂ : SetClause fs) (hne : c₁.field.name ≠ c₂.field.name)
    (r : RowVals fs) :
    c₂.path.set (c₁.path.set r c₁.value) c₂.value
      = c₁.path.set (c₂.path.set r c₂.value) c₁.value :=
  (ColPath.set_commute_disjoint c₂.path c₁.path (fun h => hne h.symm) r c₂.value c₁.value).symm

/-! ## the source-order teeth (the concrete witnesses) -/

/-- The witness schema: ONE u64 knob (the dogfood's shape). The ABBREV
    rule (06 §3): the GADT index must unfold at the fixtures' row
    literals. -/
abbrev witnessFs : List Field := [{ name := "jobs", ty := .u64 }]

/-- The default row at the witness schema. -/
def witnessRow : RowVals witnessFs := .cons (.u64 0) .nil

/-- The file-source write: jobs = 1. -/
def wFile : SetClause witnessFs :=
  { field := { name := "jobs", ty := .u64 }, path := .here, value := .u64 1 }

/-- The cli-source write: jobs = 2. -/
def wCli : SetClause witnessFs :=
  { field := { name := "jobs", ty := .u64 }, path := .here, value := .u64 2 }

/-- THE SOURCE-ORDER WITNESS: the file's value UNDER the cli's wins
    rank; swapping the VALUES across the fixed ranks swaps the result
    — the order (the ranks) is data, and the configuration is
    rank-dependent, never position-dependent (prioritize sorts BOTH
    deliveries to the same rank order — the discipline). -/
theorem sourceOrderWitness :
    applySources witnessRow [{ src := .file, overrides := [wFile] },
                             { src := .cli, overrides := [wCli] }]
      ≠ applySources witnessRow [{ src := .file, overrides := [wCli] },
                                 { src := .cli, overrides := [wFile] }] := by
  intro h
  have h1 : readNat witnessFs
      (applySources witnessRow [{ src := .file, overrides := [wFile] },
                                { src := .cli, overrides := [wCli] }]) "jobs"
    = Option.some 2 := by decide
  have h2 : readNat witnessFs
      (applySources witnessRow [{ src := .file, overrides := [wCli] },
                                { src := .cli, overrides := [wFile] }]) "jobs"
    = Option.some 1 := by decide
  rw [h] at h1
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- The last-wins read at the witness: the disciplined order's
    verdict is the CLI value (the behavior pin). -/
theorem sourceOrderCliWins :
    readNat witnessFs
      (applySources witnessRow [{ src := .file, overrides := [wFile] },
                                { src := .cli, overrides := [wCli] }]) "jobs"
      = Option.some 2 := by decide

/-! ## the validation (the check lane's rows) -/

/-- THE VALIDATION: the schema's own check rows over the merged
    record (`true` = every declared constraint holds). -/
def validateConfig (cs : ConfigSchema) (r : RowVals cs.item.fields) : Bool :=
  cs.checks.all (fun p => p.check r)

/-- The violated constraints as curated Diags (the CF0003 row; one
    per violated check — the violating CONFIG is the context). -/
def configViolations (cs : ConfigSchema) (r : RowVals cs.item.fields) :
    List Kit.Diag :=
  cs.checks.filterMap fun p =>
    if p.check r then Option.none
    else Option.some (configDiag eCF0003
      s!"a declared constraint is violated (schema `{cs.item.name}`)")

/-- The validated merge (the face's TOTAL entry: lower the three
    source layers in rank order — file, env, cli — fold, check; any
    refusal surfaces as `.error`, the curated Diag). -/
def loadConfig (cs : ConfigSchema)
    (filePairs envPairs cliPairs : List (String × String)) :
    Except Kit.Diag (RowVals cs.item.fields) :=
  match initialRow cs.item.fields with
  | none => .error (configDiag eCF0002 "the schema has no default row (a non-scalar field)")
  | some base => do
      let f ← lowerPairs cs.item.fields filePairs
      let e ← lowerPairs cs.item.fields envPairs
      let c ← lowerPairs cs.item.fields cliPairs
      let r := applySources base
        [{ src := .file, overrides := f },
         { src := .env, overrides := e },
         { src := .cli, overrides := c }]
      if validateConfig cs r then .ok r
      else .error (configDiag eCF0003
        s!"a declared constraint is violated (schema `{cs.item.name}`)")

/-! ## the Rust face (the codegen spine's config row) -/

/-- The config struct's Rust name (the item's namespace path, dots
    dropped). -/
def rustConfigName (it : Item) : String :=
  (it.name.splitOn ".").foldl (· ++ ·) "" ++ "Config"

/-- THE GENERATED RUST FACE: the config schema's struct + the
    source-merge discipline's doc (the fields in schema order, the
    types at `Emit.Rust.tyRust`'s ONE walk). The artifact FILE (the
    byte-tie's writer) lands with the first emitted crate — the face
    renders, the pins tie the bytes. -/
def rustConfigStruct (it : Item) : String :=
  "// GENERATED from " ++ it.name ++ " — SchemaCore.Config's Rust face (do not edit).\n"
    ++ "// The source-merge discipline: file (base) < env < cli, LAST-WINS —\n"
    ++ "// the override order is data (SchemaCore.Config's rank sort), never\n"
    ++ "// a semilattice join.\n"
    ++ "#[rustfmt::skip]\n"
    ++ "#[derive(Clone, Debug, PartialEq, Eq)]\n"
    ++ "pub struct " ++ rustConfigName it ++ " {\n"
    ++ String.intercalate "\n"
        (it.fields.map fun f =>
          "    pub " ++ f.name ++ ": "
            ++ Emit.Rust.tyRust (Emit.Spine.descrOfTy f.ty) ++ ",")
    ++ "\n}\n"

end SchemaCore
