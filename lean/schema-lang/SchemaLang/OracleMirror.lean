/-
# SchemaLang.OracleMirror — the oracle's comparison BOOKKEEPING, as data

The differential doctrine (notes/lean-refactor-guide.md, C4): faithful
RE-IMPLEMENTATIONS at differential boundaries stay hand-written (the
parsers/codecs/evaluators — the bug-finder); the comparison/
serialization PLUMBING around them may be GENERATED. This module is the
bookkeeping: crates/oracle-runner's mirror of the oracle's
CompareMode/ErrorId/Outcome/compare/classify/firstDiffAt/verdict/
jsonVerdict/ser_val surface, emitted to
`generated/rust/oracle_mirror_generated.rs` (oracle-runner's hand
copies are DELETED — it `#[path]`-includes the module).

WHY THE DATA LIVES HERE (schema-lang), NOT in Oracle.lean: the emitter
must register in THIS package's registry (the forge byte-tie's job —
`SchemaLang.Emit.Registry.coreEmitters`), and a `module`-declared
registry file cannot import wasm-backend's non-module roots (the
`cannot import non-module` rule). Schema-lang cannot depend on
wasm-backend — so the mirror is emitted from DATA against which
Oracle.lean PROVES agreement (below): Oracle.lean imports this module
and #guard-sweeps the tables against its own definitions (the finite
sweeps over `compareTableRows`/`classifyRows`/the display tables vs
`CompareMode.compare`/`classify`/the ToString instances). The Lean side
stays the authority; the byte-tie pins the artifact; the INDEPENDENCE
lives in the EVALUATION (the replay machinery — the arg builders, the
stream drain, ser_val's Val reads — is NOT generated; the ser-FORM
CONTRACT strings ride as data).

The sweep evaluators here operate on the DATA's string mode names (the
row table carries `"ignore"`/`"identity"`/`"full"` as strings — the
module has no oracle dependency); Oracle.lean maps its ctors to the
same names when proving the agreement.
-/

module

import Lean
public import CodegenCore -- Registry's import pattern (the umbrella; pascal/Emitter/GeneratedFile re-exported)
public import SchemaLang.Emit.GenCtx -- the emitter's spec type (the registry's GenCtx)

@[expose] public section

namespace SchemaLang.OracleMirror

/-- The CompareMode ctor NAME table — the Rust enum's variants + the
    sweep's domain. The order is the declaration order (Oracle.lean's
    sweep zips it against its ctors). -/
def compareModeNames : List String := ["ignore", "identity", "full"]

/-- The ErrorId ctor NAME table — the Rust enum + `as_str`'s arms
    (Oracle.lean pins it against the ToString instance). -/
def errorIdNames : List String := ["unknownFn", "arityDrift", "trap"]

/-- The DivergenceClass ctor NAME table — the Rust enum + `as_str`. -/
def divergenceClassNames : List String :=
  ["valueMismatch", "expectedValueGotError", "expectedErrorGotValue",
   "errorIdentityMismatch", "errorPayloadMismatch"]

-- ── the compare truth table as DATA ─────────────────────────────────

/-- One side's error pattern in a table row (`any` = the match's
    wildcard arm — the data-form of the `_` pattern). -/
inductive MirrorErrPat where | any | none | some
deriving BEq, Repr

/-- One row's outcome rule. -/
inductive MirrorCompRes where
  | pass | fail | payloadEq | idEq | idAndPayloadEq
deriving BEq, Repr

/-- One arm of `CompareMode.compare` as data: the mode (its NAME), the
    expected/got error patterns, the outcome rule. ROW ORDER = the
    match's arm order (the wildcard arm is LAST — the Rust fold's
    first-match IS the Lean match's first-arm). -/
structure MirrorCompareRow where
  mode : String
  expected : MirrorErrPat
  got : MirrorErrPat
  result : MirrorCompRes
deriving BEq, Repr

/-- THE TRUTH TABLE — the 9 arms of `CompareMode.compare`, in arm
    order. The 9-line `compare` on the Rust side is one small fold over
    this data (the P1 shape: generate the DATA, fold in Rust; the
    independence lives in the EVALUATION, not the 9-line table). -/
def compareTableRows : List MirrorCompareRow :=
  [ ⟨"ignore", .some, .any, .pass⟩
  , ⟨"ignore", .any, .some, .pass⟩
  , ⟨"ignore", .none, .none, .payloadEq⟩
  , ⟨"identity", .some, .some, .idEq⟩
  , ⟨"identity", .none, .none, .pass⟩
  , ⟨"identity", .any, .any, .fail⟩
  , ⟨"full", .some, .some, .idAndPayloadEq⟩
  , ⟨"full", .none, .none, .payloadEq⟩
  , ⟨"full", .any, .any, .fail⟩ ]

/-- The error-pattern evaluator (Oracle.lean's sweep side). -/
def mirrorPatMatch (p : MirrorErrPat) (o : Option String) : Bool :=
  match p, o with
  | .any, _ => true
  | .none, none => true
  | .some, some _ => true
  | _, _ => false

/-- One row's outcome rule evaluated over concrete outcomes (the error
    identities as NAMES — identity compares are name compares). -/
def mirrorRowResult (r : MirrorCompRes) (e g : Option String) (ep gp : String) : Bool :=
  match r with
  | .pass => true
  | .fail => false
  | .payloadEq => ep == gp
  | .idEq =>
      match e, g with | some a, some b => a == b | _, _ => false
  | .idAndPayloadEq =>
      match e, g with | some a, some b => a == b && ep == gp | _, _ => false

/-- The table as an EVALUATOR over string modes (Oracle.lean maps its
    ctors to the same names when proving the agreement): the first
    matching row in table order, then its rule. -/
def mirrorCompareByName (mode : String) (e g : Option String) (ep gp : String) : Bool :=
  match compareTableRows.find? fun row =>
    row.mode == mode && mirrorPatMatch row.expected e && mirrorPatMatch row.got g with
  | none => false
  | some row => mirrorRowResult row.result e g ep gp

-- ── the classification table as DATA ────────────────────────────────

/-- One `classify` row's outcome rule (`idDependent` = the nested
    `if e == f then errorPayloadMismatch else errorIdentityMismatch`). -/
inductive MirrorClassRes where
  | fixed (c : String)
  | idDependent
deriving BEq, Repr

/-- The `classify` arms as data (exact patterns — every error pair is
    covered, order irrelevant). The fixed class renders as the
    DivergenceClass variant of the same name. -/
def classifyRows : List (MirrorErrPat × MirrorErrPat × MirrorClassRes) :=
  [ (.none, .none, .fixed "valueMismatch")
  , (.none, .some, .fixed "expectedValueGotError")
  , (.some, .none, .fixed "expectedErrorGotValue")
  , (.some, .some, .idDependent) ]

/-- The table as an evaluator (Oracle.lean's sweep side). -/
def mirrorClassifyByName (e g : Option String) : String :=
  match classifyRows.find? fun (p, q, _) => mirrorPatMatch p e && mirrorPatMatch q g with
  | some (_, _, .fixed c) => c
  | some (_, _, .idDependent) =>
      match e, g with
      | some a, some b => if a == b then "errorPayloadMismatch" else "errorIdentityMismatch"
      | _, _ => "errorIdentityMismatch"
  | none => "errorIdentityMismatch"

-- ── the ser-form CONTRACT strings (ser_val's rendered leaves) ───────
-- The strings the wire expects (the oracle's resultOf ser forms — the
-- duels pin them end-to-end): the values are DATA here, and the emitted
-- Rust renders from them. The ARMS (the Val -> form evaluation) stay on
-- the Rust side — that is the differential's evaluation half.

/-- The Bool ser form (`"1"`/`"0"`). -/
def serFormTrue := "1"
def serFormFalse := "0"
/-- The `Option.none` ser form (`"none"`). -/
def serFormNone := "none"
/-- The `Option.some x` wrapper — `"some(" ++ x ++ ")"`. -/
def serFormSomeOpen := "some("
def serFormSomeClose := ")"
/-- The record form — `"{ " ++ fields ++ " }"` (comma-space joins). -/
def serFormRecordOpen := "{ "
def serFormRecordClose := " }"
def serFormRecordSep := ", "
/-- The field form — `k ++ "=" ++ v`. -/
def serFormEq := "="
/-- The list form — `"(" ++ items ++ ")"` (comma joins, NO space — the
    byte-tie's frozen join). -/
def serFormListOpen := "("
def serFormListClose := ")"
def serFormListSep := ","
/-- The stream form (the collected list is the value — the drain's). -/
def serFormStream := "<stream>"

-- ── the Rust renderer ───────────────────────────────────────────────

/-- The Rust variant name of a ctor display (CodegenCore's pascal — the
    mangling every other emitter's Rust types use). -/
def rustVariantOf (name : String) : String := CodegenCore.Emit.pascal name

/-- Doubling the format-STRING braces (Rust format literals escape `{`
    and `}` as `{{`/`}}`) — the ser-form delimiters derive their Rust
    literals from the constants above. -/
def doubleBraces (s : String) : String :=
  (s.replace "{" "{{").replace "}" "}}"

/-- The format literal rendering `openS ++ placeholder ++ closeS` (e.g.
    the record's `"{{ {} }}"` from `"{ "`/`" }"`). -/
def rustFormatLiteral (openS closeS : String) : String :=
  "\"" ++ doubleBraces openS ++ "{}" ++ doubleBraces closeS ++ "\""

def errPatRust : MirrorErrPat → String
  | .any => "ErrPat::Any" | .none => "ErrPat::None" | .some => "ErrPat::Some"

def compResRust : MirrorCompRes → String
  | .pass => "CompareResult::Pass"
  | .fail => "CompareResult::Fail"
  | .payloadEq => "CompareResult::PayloadEq"
  | .idEq => "CompareResult::IdEq"
  | .idAndPayloadEq => "CompareResult::IdAndPayloadEq"

/-- One `COMPARE_TABLE` row line. -/
def compareRowLine (r : MirrorCompareRow) : String :=
  "    CompareRow { mode: CompareMode::" ++ rustVariantOf r.mode
  ++ ", expected: " ++ errPatRust r.expected
  ++ ", got: " ++ errPatRust r.got
  ++ ", result: " ++ compResRust r.result ++ " },"

/-- One `CLASSIFY_TABLE` row line. -/
def classifyRowLine (p : MirrorErrPat) (q : MirrorErrPat) (r : MirrorClassRes) : String :=
  match r with
  | .fixed c =>
      "    ClassifyRow { expected: " ++ errPatRust p ++ ", got: " ++ errPatRust q
      ++ ", result: ClassifyResult::Fixed(DivergenceCategory::"
      ++ rustVariantOf c ++ ") },"
  | .idDependent =>
      "    ClassifyRow { expected: " ++ errPatRust p ++ ", got: " ++ errPatRust q
      ++ ", result: ClassifyResult::IdDependent },"

/-- The ErrorId enum text (variants + `as_str` arms — both from the
    name table). -/
def errorIdEnumLines : List String :=
  [ "/// The error identity an outcome can carry — mirrors `Oracle.ErrorId`;"
  , "/// the replay side's only identity today is `Trap` (a wasmtime trap"
  , "/// carries no payload the oracle may read). `UnknownFn`/`ArityDrift`"
  , "/// are the LEAN-side identities — constructed by the mirror's tests,"
  , "/// kept for the arm-for-arm truth table."
  , "#[allow(dead_code)]"
  , "#[derive(Clone, Copy, PartialEq, Eq, Debug)]"
  , "pub enum ErrorId {"
  ] ++ errorIdNames.map (fun n => "    " ++ rustVariantOf n ++ ",") ++
  [ "}"
  , ""
  , "impl ErrorId {"
  , "    pub fn as_str(self) -> &'static str {"
  , "        match self {"
  ] ++ errorIdNames.map (fun n =>
      "            ErrorId::" ++ rustVariantOf n ++ " => \"" ++ n ++ "\",") ++
  [ "        }"
  , "    }"
  , "}" ]

/-- The DivergenceCategory enum text. -/
def divergenceCategoryLines : List String :=
  [ "/// The divergence category — mirrors `Oracle.DivergenceClass`. A"
  , "/// mismatch always names ONE of these; the payload strings ride"
  , "/// along as witness, never as identity."
  , "#[derive(Clone, Copy, PartialEq, Eq, Debug)]"
  , "pub enum DivergenceCategory {"
  ] ++ divergenceClassNames.map (fun n => "    " ++ rustVariantOf n ++ ",") ++
  [ "}"
  , ""
  , "impl DivergenceCategory {"
  , "    pub fn as_str(self) -> &'static str {"
  , "        use DivergenceCategory::*;"
  , "        match self {"
  ] ++ divergenceClassNames.map (fun n =>
      "            " ++ rustVariantOf n ++ " => \"" ++ n ++ "\",") ++
  [ "        }"
  , "    }"
  , "}" ]

/-- The ser_val arms (the value -> ser-form evaluation; the left side
    is wasmtime's `Val` — the host's — the right side renders from the
    ser-form constants above). -/
def serValArmLines : List String :=
  [ "        Val::Bool(b) => {"
  , "            if *b { \"" ++ serFormTrue ++ "\".into() } else { \"" ++ serFormFalse ++ "\".into() }"
  , "        }"
  , "        Val::U8(n) => n.to_string(),"
  , "        Val::U16(n) => n.to_string(),"
  , "        Val::U32(n) => n.to_string(),"
  , "        Val::U64(n) => n.to_string(),"
  , "        Val::S8(n) => n.to_string(),"
  , "        Val::S16(n) => n.to_string(),"
  , "        Val::S32(n) => n.to_string(),"
  , "        Val::S64(n) => n.to_string(),"
  , "        Val::Float32(f) => f.to_string(),"
  , "        Val::Float64(f) => f.to_string(),"
  , "        Val::Char(c) => c.to_string(),"
  , "        Val::String(s) => s.clone(),"
  , "        Val::Option(None) => \"" ++ serFormNone ++ "\".into(),"
  , "        Val::Option(Some(inner)) => format!(" ++ rustFormatLiteral serFormSomeOpen serFormSomeClose ++ ", ser_val(inner)),"
  , "        Val::Record(fields) => {"
  , "            let inner: Vec<String> ="
  , "                fields.iter().map(|(k, v)| format!(\"{k}" ++ serFormEq ++ "{}\", ser_val(v))).collect();"
  , "            format!(" ++ rustFormatLiteral serFormRecordOpen serFormRecordClose ++ ", inner.join(\"" ++ serFormRecordSep ++ "\"))"
  , "        }"
  , "        Val::List(items) => {"
  , "            let inner: Vec<String> = items.iter().map(ser_val).collect();"
  , "            format!(" ++ rustFormatLiteral serFormListOpen serFormListClose ++ ", inner.join(\"" ++ serFormListSep ++ "\"))"
  , "        }"
  , "        Val::Stream(_) => \"" ++ serFormStream ++ "\".into(),"
  , "        other => format!(\"{other:?}\")," ]

/-- THE GENERATED MODULE BODY (the driver prepends the GENERATED
    header). Everything below is a function of the data above. -/
def oracleMirrorRs : String :=
  String.intercalate "\n" (
  [ "use wasmtime::component::Val;"
  , ""
  , "/// The comparison contract — GENERATED from SchemaLang.OracleMirror"
  , "/// (compareTableRows/classifyRows + the ser-form constants); the"
  , "/// agreement with the oracle's definitions is #guard-swept in"
  , "/// Oracle.lean. The mode truth table and the classification are"
  , "/// folds over DATA (COMPARE_TABLE / CLASSIFY_TABLE) in the Lean arm"
  , "/// order."
  , "///"
  , "/// How a row's outcome is compared against the replay —"
  , "/// mirrors `Oracle.CompareMode`."
  , "#[allow(dead_code)]"
  , "#[derive(Clone, Copy, PartialEq, Eq, Debug)]"
  , "pub enum CompareMode {"
  ] ++ (compareModeNames.map fun n => "    " ++ rustVariantOf n ++ ",") ++
  [ "}"
  , ""
  ] ++ errorIdEnumLines ++
  [ ""
  , "/// One side of a comparison — mirrors `Oracle.Outcome`."
  , "#[derive(Clone, PartialEq, Eq, Debug)]"
  , "pub struct Outcome {"
  , "    pub error: Option<ErrorId>,"
  , "    pub payload: String,"
  , "}"
  , ""
  , "impl Outcome {"
  , "    pub fn value(s: String) -> Self {"
  , "        Outcome { error: None, payload: s }"
  , "    }"
  , "    pub fn trap() -> Self {"
  , "        Outcome { error: Some(ErrorId::Trap), payload: String::new() }"
  , "    }"
  , "}"
  , ""
  , "/// The error-pattern of one truth-table row (the wildcard arm)."
  , "#[derive(Clone, Copy, PartialEq, Eq, Debug)]"
  , "pub enum ErrPat {"
  , "    Any,"
  , "    None,"
  , "    Some,"
  , "}"
  , ""
  , "/// The outcome rule of one truth-table row."
  , "#[derive(Clone, Copy, PartialEq, Eq, Debug)]"
  , "pub enum CompareResult {"
  , "    Pass,"
  , "    Fail,"
  , "    PayloadEq,"
  , "    IdEq,"
  , "    IdAndPayloadEq,"
  , "}"
  , ""
  , "/// One row of the compare truth table — the DATA form of one"
  , "/// `Oracle.CompareMode.compare` arm (arm ORDER preserved: the wildcard"
  , "/// row is last, so the fold's first-match is the match's first-arm)."
  , "pub struct CompareRow {"
  , "    pub mode: CompareMode,"
  , "    pub expected: ErrPat,"
  , "    pub got: ErrPat,"
  , "    pub result: CompareResult,"
  , "}"
  , ""
  , "/// The truth table as data — folded from"
  , "/// `SchemaLang.OracleMirror.compareTableRows`."
  , "pub const COMPARE_TABLE: &[CompareRow] = &["
  ] ++ compareTableRows.map compareRowLine ++
  [ "];"
  , ""
  , "fn pat_matches(p: ErrPat, o: Option<ErrorId>) -> bool {"
  , "    matches!("
  , "        (p, o),"
  , "        (ErrPat::Any, _) | (ErrPat::None, None) | (ErrPat::Some, Some(_))"
  , "    )"
  , "}"
  , ""
  , "/// The mode truth table — `Oracle.CompareMode.compare` as one small"
  , "/// fold over the DATA (the arm tuples above): the first matching row"
  , "/// in TABLE order wins, exactly the Lean match's arm order. The"
  , "/// INDEPENDENCE lives in the EVALUATION, not this table."
  , "pub fn compare(mode: CompareMode, expected: &Outcome, got: &Outcome) -> bool {"
  , "    for row in COMPARE_TABLE {"
  , "        if row.mode == mode"
  , "            && pat_matches(row.expected, expected.error)"
  , "            && pat_matches(row.got, got.error)"
  , "        {"
  , "            return match row.result {"
  , "                CompareResult::Pass => true,"
  , "                CompareResult::Fail => false,"
  , "                CompareResult::PayloadEq => expected.payload == got.payload,"
  , "                CompareResult::IdEq => match (expected.error, got.error) {"
  , "                    (Some(e), Some(f)) => e == f,"
  , "                    _ => false,"
  , "                },"
  , "                CompareResult::IdAndPayloadEq => match (expected.error, got.error) {"
  , "                    (Some(e), Some(f)) => e == f && expected.payload == got.payload,"
  , "                    _ => false,"
  , "                },"
  , "            };"
  , "        }"
  , "    }"
  , "    false"
  , "}"
  , ""
  ] ++ divergenceCategoryLines ++
  [ ""
  , "/// One classification row — the data-form of one `Oracle.classify` arm."
  , "pub struct ClassifyRow {"
  , "    pub expected: ErrPat,"
  , "    pub got: ErrPat,"
  , "    pub result: ClassifyResult,"
  , "}"
  , ""
  , "/// One classification row's outcome rule."
  , "#[derive(Clone, Copy, PartialEq, Eq, Debug)]"
  , "pub enum ClassifyResult {"
  , "    Fixed(DivergenceCategory),"
  , "    IdDependent,"
  , "}"
  , ""
  , "/// The classification table as data — folded from"
  , "/// `SchemaLang.OracleMirror.classifyRows`."
  , "pub const CLASSIFY_TABLE: &[ClassifyRow] = &["
  ] ++ classifyRows.map (fun (p, q, r) => classifyRowLine p q r) ++
  [ "];"
  , ""
  , "/// Mirrors `Oracle.classify` — the same small fold over the data."
  , "pub fn classify(expected: &Outcome, observed: &Outcome) -> DivergenceCategory {"
  , "    for row in CLASSIFY_TABLE {"
  , "        if pat_matches(row.expected, expected.error)"
  , "            && pat_matches(row.got, observed.error)"
  , "        {"
  , "            return match row.result {"
  , "                ClassifyResult::Fixed(c) => c,"
  , "                ClassifyResult::IdDependent => match (expected.error, observed.error) {"
  , "                    (Some(e), Some(f)) => {"
  , "                        if e == f {"
  , "                            DivergenceCategory::ErrorPayloadMismatch"
  , "                        } else {"
  , "                            DivergenceCategory::ErrorIdentityMismatch"
  , "                        }"
  , "                    }"
  , "                    _ => DivergenceCategory::ErrorIdentityMismatch,"
  , "                },"
  , "            };"
  , "        }"
  , "    }"
  , "    DivergenceCategory::ErrorIdentityMismatch"
  , "}"
  , ""
  , "/// The first char offset at which two rendered payloads differ."
  , "/// Mirrors `Oracle.firstDiffAt` (char-wise; the ser forms are ASCII)."
  , "pub fn first_diff_at(a: &str, b: &str) -> Option<usize> {"
  , "    let mut i = 0;"
  , "    let mut ac = a.chars();"
  , "    let mut bc = b.chars();"
  , "    loop {"
  , "        match (ac.next(), bc.next()) {"
  , "            (None, None) => return None,"
  , "            (None, Some(_)) | (Some(_), None) => return Some(i),"
  , "            (Some(x), Some(y)) if x == y => i += 1,"
  , "            (Some(_), Some(_)) => return Some(i),"
  , "        }"
  , "    }"
  , "}"
  , ""
  , "/// The first-divergence witness — mirrors `Oracle.Divergence`."
  , "pub struct Divergence {"
  , "    pub expected: Outcome,"
  , "    pub observed: Outcome,"
  , "    pub category: DivergenceCategory,"
  , "    pub payload_diff_at: Option<usize>,"
  , "}"
  , ""
  , "/// The mode's verdict — mirrors `Oracle.CompareMode.verdict`: `None`"
  , "/// = pass, `Some(d)` = the first divergence."
  , "pub fn verdict(mode: CompareMode, expected: &Outcome, observed: &Outcome) -> Option<Divergence> {"
  , "    if compare(mode, expected, observed) {"
  , "        None"
  , "    } else {"
  , "        Some(Divergence {"
  , "            expected: expected.clone(),"
  , "            observed: observed.clone(),"
  , "            category: classify(expected, observed),"
  , "            payload_diff_at: first_diff_at(&expected.payload, &observed.payload),"
  , "        })"
  , "    }"
  , "}"
  , ""
  , "fn json_str(s: &str) -> String {"
  , "    // DELIBERATE INVARIANT (audit class (a)): serde_json's string"
  , "    // serialization is infallible by construction (no pending failure"
  , "    // state) — the expect documents that, never fires."
  , "    serde_json::to_string(s).expect(\"string serializes\")"
  , "}"
  , ""
  , "/// One outcome as JSON — mirrors `Oracle.jsonOutcome`."
  , "pub fn outcome_json(o: &Outcome) -> String {"
  , "    let err = match o.error {"
  , "        None => \"null\".to_string(),"
  , "        Some(e) => json_str(e.as_str()),"
  , "    };"
  , "    format!(\"{{\\\"error\\\": {}, \\\"payload\\\": {}}}\", err, json_str(&o.payload))"
  , "}"
  , ""
  , "/// The verdict as JSON — mirrors `Oracle.jsonVerdict`'s shape"
  , "/// byte-for-byte (the schema echo = the canonical surface STRING;"
  , "/// hash it consumer-side)."
  , "pub fn verdict_json(v: Option<&Divergence>, schema_surface: &str) -> String {"
  , "    match v {"
  , "        None => format!(\"{{\\\"ok\\\": true, \\\"schema\\\": {}}}\", json_str(schema_surface)),"
  , "        Some(d) => {"
  , "            let at = match d.payload_diff_at {"
  , "                None => \"null\".to_string(),"
  , "                Some(n) => n.to_string(),"
  , "            };"
  , "            format!("
  , "                \"{{\\\"ok\\\": false, \\\"category\\\": {}, \\\"expected\\\": {}, \\\"observed\\\": {}, \\\"payload_diff_at\\\": {}, \\\"schema\\\": {}}}\","
  , "                json_str(d.category.as_str()),"
  , "                outcome_json(&d.expected),"
  , "                outcome_json(&d.observed),"
  , "                at,"
  , "                json_str(schema_surface)"
  , "            )"
  , "        }"
  , "    }"
  , "}"
  , ""
  , "/// The ser forms — the value -> payload rendering rendered from the"
  , "/// ser-form CONTRACT constants (OracleMirror.serForm*). MUST match"
  , "/// Lean's `resultOf` byte-for-byte (the differential duels pin it)."
  , "pub fn ser_val(v: &Val) -> String {"
  , "    match v {"
  ] ++ serValArmLines ++
  [ "    }"
  , "}"
  , "" ])

/-- The emitter — registered in schema-lang's coreEmitters (ONE line in
    Registry.lean; the driver's `certifiedJobs` pairing is the second,
    the run side of the same registration). The byte-tie is forge's
    (`just gen` + `forge gen --check`); this is BOOKKEEPING — the
    evaluation halves (the replay, the Val reads) are not generated. -/
def oracleMirrorEmitter : CodegenCore.Emit.Emitter SchemaLang.Emit.GenCtx :=
  { name := "oracle-mirror"
  , style := .doubleSlash
  , specSource := "SchemaLang.OracleMirror (compareTableRows/classifyRows + the ser-form constants; pinned against Oracle.lean)"
  , outputs := ["../../generated/rust/oracle_mirror_generated.rs"]
  , run := fun _ctx =>
      [{ path := "../../generated/rust/oracle_mirror_generated.rs"
         contents := oracleMirrorRs }] }

end SchemaLang.OracleMirror
