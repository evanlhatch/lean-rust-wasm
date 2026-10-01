/-
# SchemaTests.Config — the config face's suite

Per the slice: positive pins + the MANDATORY negative controls
(15-patterns #5 — each sabotage's WRONG claim must fail). The module
under test is SchemaCore.Config; the text formats ride
TextKit.ConfigFormat (its own pins live in TextKitTests).

1. THE ORDER'S LAWS — the fold-append law (the honest associativity),
   last-wins, the same-field noncommutation, the disjoint
   commutation, the source-order witness (rank-dependent, never
   position-dependent).
2. THE LOWERING'S TEETH — unknown key (the closed-world valid space +
   did-you-mean), mistyped value (the type named), the end-to-end
   loadConfig over the three source layers, the check rows.
3. THE RUST FACE — the golden pin (the byte-tie at the fixture).
-/

import TestingKit.Harness
import SchemaCore
import SchemaCore.Config

namespace SchemaTests.Config
open SchemaCore TestingKit

/-! ## Fixtures -/

/-- The two-knob fixture (the dogfood's shape: one u64 knob, one
    bool switch). The abbrev rule (06 §3): the GADT index unfolds. -/
abbrev cfgFields : List Field :=
  [ { name := "jobs", ty := .u64 }
  , { name := "verbose", ty := .bool } ]

/-- The fixture item (the schema record). -/
def cfgItem : Item := { name := "Gates.Knobs", fields := cfgFields }

/-- The fixture's check rows: every knob positive (the >0 shape). -/
def cfgChecks : List (Pred cfgFields) := [Pred.u64GtLit "jobs" 0]

/-- The fixture's config schema (record + validation). -/
def cfgSchema : ConfigSchema := { item := cfgItem, checks := cfgChecks }

/-- The fixture's default row (jobs 0, verbose false — the literal
    pin of `initialRow`'s verdict at this fixture). -/
def cfgBase : RowVals cfgFields := .cons (.u64 0) (.cons (.bool false) .nil)

-- The row equality is the UPDATE LANE's `rowBeq` (SchemaCore.Update —
-- one copy; the pins compare rows through it, never a local re-roll).

/-- The verbose read (the bool knob's face — `Pred` carries only the
    u64/string projections, so the pin reads the GADT directly). -/
def readVerbose (r : RowVals cfgFields) : Option Bool :=
  match RowVals.project? cfgFields r "verbose" with
  | some ⟨.bool, .bool b⟩ => some b
  | _ => none

/-- The writes: jobs = 1 (the file face) and jobs = 2 (the cli face). -/
def wJobs1 : SetClause cfgFields :=
  { field := { name := "jobs", ty := .u64 }, path := .here, value := .u64 1 }

def wJobs2 : SetClause cfgFields :=
  { field := { name := "jobs", ty := .u64 }, path := .here, value := .u64 2 }

/-- The verbose write (the DISJOINT field — the commutation's other
    party). -/
def wVerbose : SetClause cfgFields :=
  { field := { name := "verbose", ty := .bool }, path := .there .here,
    value := .bool true }

/-! ## 1. The order's laws -/

def configLawsSpec : Spec :=
  Spec.ofList "the override order's laws: append (the honest associativity), last-wins, disjoint commutation"
    (fun _ =>
      assert ((
      -- THE APPEND LAW at the fixture: folding cli over the file-merge
      -- = folding the concatenation (grouping is free)
        (rowBeq cfgFields (applySets [wJobs2] (applySets [wJobs1] cfgBase))
          (applySets ([wJobs1] ++ [wJobs2]) cfgBase))
      -- LAST-WINS: the snoc fold reads the last write
        && (readNat cfgFields (applySets ([wJobs1] ++ [wJobs2]) cfgBase) "jobs"
              == some 2)
      -- THE NONCOMMUTATION (the negative face, positive form): the
      -- same-field distinct-value writes do NOT commute — the theorem
      -- `ColPath.set_set_noncommute` says never; the pin decides here
        && !(rowBeq cfgFields (applySets [wJobs2] (applySets [wJobs1] cfgBase))
              (applySets [wJobs1] (applySets [wJobs2] cfgBase)))
      -- THE DISJOINT COMMUTATION: the jobs write and the verbose write
      -- commute (the update lane's kernel law at the clause granularity)
        && (rowBeq cfgFields (wJobs2.path.set (wVerbose.path.set cfgBase wVerbose.value) wJobs2.value)
              (wVerbose.path.set (wJobs2.path.set cfgBase wJobs2.value) wVerbose.value))
      -- THE SOURCE-ORDER WITNESS (the theorem's concrete face): the
      -- configuration is rank-dependent, never position-dependent
        && (readNat cfgFields
              (applySources cfgBase [{ src := .file, overrides := [wJobs1] },
                                     { src := .cli, overrides := [wJobs2] }]) "jobs"
              == some 2)
        && (readNat cfgFields
              (applySources cfgBase [{ src := .file, overrides := [wJobs2] },
                                     { src := .cli, overrides := [wJobs1] }]) "jobs"
              == some 1)
      ))
      "the override order's laws drifted")
    [ ("same-field overrides commute (the semilattice lie)",
        fun _ =>
          assert (rowBeq cfgFields (applySets [wJobs2] (applySets [wJobs1] cfgBase))
            (applySets [wJobs1] (applySets [wJobs2] cfgBase)))
          "control fired: same-field distinct-value overrides NEVER commute — \
            last-wins is not a join")
    , ("the source ranks are ignored (position wins)",
        fun _ =>
          assert (readNat cfgFields
              (applySources cfgBase [{ src := .file, overrides := [wJobs2] },
                                     { src := .cli, overrides := [wJobs1] }]) "jobs"
            == some 2)
          "control fired: the CLI source must win over the file source — \
            the ranks are the order")
    , ("disjoint writes do not commute",
        fun _ =>
          assert (!(rowBeq cfgFields (wJobs2.path.set (wVerbose.path.set cfgBase wVerbose.value) wJobs2.value)
            (wVerbose.path.set (wJobs2.path.set cfgBase wJobs2.value) wVerbose.value)))
          "control fired: writes at DISTINCT fields commute — the kernel law")
    ]
    4 42

/-! ## 2. The lowering's teeth -/

/-- The unknown-key refusal's face (the closed-world constructor's
    product: code CF0001 + the field names' valid space). -/
def unknownKeyDiag? (key : String) : Option Kit.Diag :=
  match lowerPair cfgFields key "1" with
  | .error d => if d.code == eCF0001 then some d else none
  | .ok _ => none

/-- The mistyped refusal's face (CF0002, the type named). -/
def mistypedDiag? (key val : String) : Option Kit.Diag :=
  match lowerPair cfgFields key val with
  | .error d => if d.code == eCF0002 then some d else none
  | .ok _ => none

/-- The applied clause's jobs read (the lowered write's effect). -/
def appliedJobs (c : SetClause cfgFields) : Option Nat :=
  readNat cfgFields (applySets [c] cfgBase) "jobs"

def configLowerSpec : Spec :=
  Spec.ofList "the lowering: typed, curated refusals, end-to-end merge"
    (fun _ =>
      assert ((
      -- the good lowering: the clause APPLIES (jobs 8)
        (match lowerPair cfgFields "jobs" "8" with
          | .ok c => appliedJobs c == some 8
          | .error _ => false)
      -- the bool knob: "true" lowers
        && (match lowerPair cfgFields "verbose" "true" with
              | .ok _ => true | .error _ => false)
      -- the unknown key: CF0001 + the valid space (the did-you-mean
      -- engine's route — closedWorld cannot skip it)
        && ((unknownKeyDiag? "jbs").map (fun d => d.valid == cfgFields.map (·.name))
              == some true)
        && ((unknownKeyDiag? "jbs").map (fun d => d.suggest.isSome) == some true)
      -- the mistyped value: CF0002 + the type named
        && ((mistypedDiag? "verbose" "8").map (fun d =>
              d.message.contains "bool") == some true)
      -- the end-to-end merge: file base, env over it, cli over that
        && (match loadConfig cfgSchema [("jobs", "8")] [("verbose", "true")] [] with
              | .ok r => readNat cfgFields r "jobs" == some 8
                && readVerbose r == some true
              | .error _ => false)
      -- the env override wins over the file (the same key, both layers)
        && (match loadConfig cfgSchema [("jobs", "8")] [("jobs", "16")] [] with
              | .ok r => readNat cfgFields r "jobs" == some 16
              | .error _ => false)
      -- the validation: the violating config REFUSES (jobs = 0 fails
      -- the check row) — the check lane's verdict, the CF0003 row
        && (match loadConfig cfgSchema [("jobs", "0")] [] [] with
              | .error d => d.code == eCF0003
              | .ok _ => false)
      -- a VALID config passes the check rows
        && (match loadConfig cfgSchema [("jobs", "3")] [] [] with
              | .ok _ => true | .error _ => false)
      ))
      "the config lowering drifted")
    [ ("the mistyped value lowers (silent wrap)",
        fun _ =>
          assert (match lowerPair cfgFields "verbose" "8" with
            | .ok _ => true | .error _ => false)
          "control fired: a bool knob fed `8` must refuse with CF0002")
    , ("the unknown key's refusal loses the valid space",
        fun _ =>
          assert ((unknownKeyDiag? "jbs").map (fun d => d.valid.isEmpty) == some true)
          "control fired: the closed-world refusal must enumerate the \
            field names")
    , ("the violating config is accepted",
        fun _ =>
          assert (match loadConfig cfgSchema [("jobs", "0")] [] [] with
            | .ok _ => true | .error _ => false)
          "control fired: jobs = 0 violates the declared >0 check row — \
            the check lane's refusal is the tooth")
    , ("the file source beats the env source",
        fun _ =>
          assert (match loadConfig cfgSchema [("jobs", "8")] [("jobs", "16")] [] with
            | .ok r => readNat cfgFields r "jobs" == some 8
            | .error _ => false)
          "control fired: the env source overrides the file layer — \
            the precedence is file < env < cli")
    ]
    4 42

/-! ## 3. The Rust face -/

/-- THE GOLDEN PIN: the generated Rust config struct, byte-for-byte
    (the byte-tie at the fixture; the artifact FILE lands with the
    first emitted crate — this pin is the face's tie until then). -/
def expectedRustStruct : String :=
  "// GENERATED from Gates.Knobs — SchemaCore.Config's Rust face (do not edit).\n"
    ++ "// The source-merge discipline: file (base) < env < cli, LAST-WINS —\n"
    ++ "// the override order is data (SchemaCore.Config's rank sort), never\n"
    ++ "// a semilattice join.\n"
    ++ "#[rustfmt::skip]\n"
    ++ "#[derive(Clone, Debug, PartialEq, Eq)]\n"
    ++ "pub struct GatesKnobsConfig {\n"
    ++ "    pub jobs: u64,\n"
    ++ "    pub verbose: bool,\n"
    ++ "}\n"

/-- The grown sibling (one more knob — the pin's negative control's
    base). -/
def cfgItemEx : Item :=
  { name := "Gates.Knobs"
    fields := cfgFields ++ [{ name := "budget", ty := .u64 }] }

def configRustSpec : Spec :=
  Spec.ofList "the Rust config face ties the bytes at the fixture"
    (fun _ =>
      assert (rustConfigStruct cfgItem == expectedRustStruct)
      "the Rust config face drifted")
    [ ("the struct survives a schema change (the stale face)",
        fun _ =>
          assert (rustConfigStruct cfgItemEx == expectedRustStruct)
          "control fired: a grown schema must render a grown struct — \
            the face is the schema's, never a constant")
    , ("the face forgets the merge discipline's doc",
        fun _ =>
          assert (!(rustConfigStruct cfgItem).contains "LAST-WINS")
          "control fired: the merge discipline rides the artifact — \
            the order-as-data is the contract")
    ]
    4 42

/-! ## the axiom pins -/

#print axioms configLawsSpec
#print axioms configLowerSpec
#print axioms configRustSpec
end SchemaTests.Config
