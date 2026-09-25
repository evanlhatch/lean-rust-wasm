/-
# SchemaCore.Emit.Witness — the witness lane's EMIT face

Owner: the SchemaCore agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/09-gates-ops.md (the byte-tie: ONE writer
per artifact path, the committed bytes are the spec of record);
notes/v3/15-patterns.md #10 (the emitter spine: pure total run, outputs
nodup in the type, drivers own IO); notes/v3/03-bidirectional.md §3
(the duel: the Lean checker vs the Rust checker over the SAME seeded
bytes — tested agreement, never a theorem, Kit.Duel's header). Mined:
`legacy/lean/schema-lang/SchemaLang/Emit/Witness.lean` (the seeded
registry as module data, the self-check wired into the render path,
the byte-tied Rust table) — ported FRESH over the landed substrate.

THE EMIT FACE (two artifacts, one regen):

- THE WITNESS REGISTRY (`witnessRegistryEmitter`, the text lane): the
  generated Rust table
  `crates/schema-generated/tests/witness_check/witnesses_generated.rs`
  — one row per seeded witness spec: label + version + pinned fuel +
  the certificate's wire bytes (`encWitness`). THE SELF-CHECK IS
  WIRED INTO THE RUN PATH — `renderRow` renders a row ONLY from a
  `WitnessGen.selfChecked?`-accepted certificate; a refusal panics the
  gen driver (the legacy core rule verbatim: an emitter that emits an
  unchecked witness is a bug). The law field is NOT the gate here —
  the run path's panic is louder (a law is a proof obligation at the
  driver; a panic refuses EVERY consumer, certified or not).

- THE WITNESS DUEL (`witnessDuelEmitter`, Kit.Duel's ONE body): the
  seeded witnesses' bytes + the REFUSAL vectors as the binary lane's
  files, the manifest the text lane's. The `accept` rows' value note
  pins the dual contract: decode (the version gate, append-form) AND
  checker-accept at the pinned fuel; the `refuse` rows are the
  negative controls (the tamper splices + the hand-built false-claim
  witness — the producer REFUSES to emit one, and the vector proves
  the Rust checker refuses it too). The Rust half is the handwritten
  consumer `crates/schema-generated/tests/witness_check.rs` (the duel
  is never a theorem — a divergence names the sides' observations).

THE HONEST BOUNDARY: the registry carries the CERTIFICATES; the ROW
they are checked against is the duel's shared fixture — the Lean
producer self-checked every seeded witness against the check slice's
`goodRow`, and the Rust consumer pins its twin
(`fixture_row()` in witness_check.rs). A drift between the twins
surfaces as a DUEL DIVERGENCE (one side accepts, the other refuses) —
never as a wrong acceptance on both sides, because the certificates
are sound by `Witness.checks_sound` on the Lean side and the Rust
checker is equation-order-identical (the port's discipline). The
legacy's schema-surface hash (deviation 4) is deliberately out: our
envelope's version gate + the claim's name-resolution refusals serve
at slice scale; the fingerprint lands with the first cross-schema
consumer (the leftover rule).

Ledger rows: the emitters declare `attests` (the seeded obligations)
+ `rev`; the drivers (`schema` exe / `gates gen-check`) record the
rows through `runEmitters` — the one-writer discipline's audit face.

Core-only (imports SchemaCore.Witness + WitnessGen + CheckSlice +
Kit.Duel — the cone rule).
-/

import SchemaCore.Witness
import SchemaCore.WitnessGen
import SchemaCore.CheckSlice
import Kit.Duel

namespace SchemaCore.Emit.Witness

open Kit.Duel (VectorSet Expect)
open Kit.Emit
open Kit.Varint

/-! ## The envelope -/

/-- The witness format's wire VERSION (the envelope's first field —
    bumping it is the wire-breaking change, the EnumWire discipline). -/
def witnessVersion : Nat := 1

/-! ## The seeded registry (module data — the legacy deviation-1 shape) -/

/-- One seeded witness spec: the obligation's label + the claim. The
    row is the duel's shared fixture (`seedRow` below). -/
structure WitnessSpec where
  label : String
  claim : Pred exampleCheckFields

/-- The fixture row (the check slice's `goodRow`): the Lean producer
    self-checks every seeded witness against it; the Rust consumer's
    pinned twin must agree — the duel NAMES that agreement as tested
    evidence. -/
def seedRow : RowVals exampleCheckFields := goodRow

/-- The seeded specs, in registration order: the atomic (the record
    is verified, never trusted), the conjunction+refutation compound,
    and the disjunction (the chosen side). -/
def seedSpecs : List WitnessSpec :=
  [ { label := "count-positive", claim := .u64GtLit "count" 0 }
  , { label := "count-compound"
      claim := .and (.u64GtLit "count" 0) (.not (.u64EqLit "count" 0)) }
  , { label := "count-disj"
      claim := .or (.u64EqLit "count" 0) (.u64GtLit "count" 1) } ]

/-- THE PRODUCTION STEP: generate + self-check (the producer's face;
    an unchecked witness is never emitted). -/
def produce? (spec : WitnessSpec) : Option (Witness exampleCheckFields) :=
  WitnessGen.selfChecked? spec.label spec.claim seedRow

/-- The seeded witness's bytes (the wire's kernel-reducible fold; a
    refused self-check panics — it is an emission failure, loud). -/
def seedBytes (spec : WitnessSpec) : List UInt8 :=
  match produce? spec with
  | some w => encWitness witnessVersion w
  | none => panic! s!"witness generation FAILED: `{spec.label}` — the
      self-check refused; refusing to emit"

/-! ## The registry's Rust table (the text lane) -/

/-- The JSON string literal for a label (the registry's Rust face; the
    escape covers the quote + the backslash — the fixture labels carry
    no control characters) — the JSON literal syntax's escape TABLE
    (Kit.Text's per-character policy shape; `none` = the byte-identity
    pass-through), the ONE kit walk at this table. -/
def jsonStr (s : String) : String :=
  Kit.escapeWith (fun c =>
    if c = '"' then "\\\""
    else if c = '\\' then "\\\\"
    else none) s

/-- The byte list as a Rust `&[u8]` literal's body. -/
def renderBytes (bs : List UInt8) : String :=
  String.intercalate ", " (bs.map toString)

/-- One registry row's Rust line — THE SELF-CHECK WIRED INTO THE RUN
    PATH: the row renders ONLY from a `selfChecked?`-accepted
    certificate; a refusal panics the gen driver (a failed self-check
    is an emission failure, loud — the byte-tied artifact cannot carry
    an unchecked witness). -/
def renderRow (spec : WitnessSpec) : String :=
  match produce? spec with
  | some w =>
      let bs := encWitness witnessVersion w
      "    WitnessRow { label: " ++ jsonStr w.label
        ++ ", version: " ++ toString witnessVersion ++ "u64"
        ++ ", fuel: " ++ toString w.fuel ++ "u64"
        ++ ", bytes: &[" ++ renderBytes bs ++ "] },"
  | none =>
      panic! s!"witness self-check FAILED at emission: `{spec.label}` — the
        generated certificate did not pass checkWitness at its pinned
        fuel; refusing to emit (an emitter that emits an unchecked
        witness is a bug)"

/-- The registry module's body (deterministic: registration order
    throughout). -/
def moduleItems (specs : List WitnessSpec) : String :=
  String.intercalate "\n"
    [ "// THE WITNESS REGISTRY (SchemaCore.Emit.Witness) — the witness"
    , "// lane's producer face: one row per seeded witness spec. Every"
    , "// row's certificate PASSED the Lean checker in-process at"
    , "// emission (a refused self-check panics the gen driver — this"
    , "// file cannot carry an unchecked witness). Never hand-edit —"
    , "// `just gen` regenerates."
    , ""
    , "/// One witness registry row: the obligation's label, the"
    , "/// envelope version, the pinned fuel (needed x 4), and the"
    , "/// certificate's wire bytes (SchemaCore.Witness.encWitness —"
    , "/// the version-gated append-form encoding)."
    , "pub struct WitnessRow {"
    , "    pub label: &'static str,"
    , "    pub version: u64,"
    , "    pub fuel: u64,"
    , "    pub bytes: &'static [u8],"
    , "}"
    , ""
    , "/// The registry, in registration order. The consumer flow"
    , "/// (tests/witness_check.rs): decode the envelope (the version"
    , "/// gate), decode the witness, re-check via the Rust checker at"
    , "/// the row's fuel over the pinned fixture row. Rejection = the"
    , "/// typed fault; the certificate is refused."
    , "pub static WITNESS_REGISTRY: &[WitnessRow] = &["
    ]
    ++ String.intercalate "\n" (specs.map renderRow)
    ++ "\n];\n"

/-- THE WITNESS REGISTRY EMITTER (the emit face through the ONE
    spine): the text lane, ONE declared output (the generated Rust
    table the handwritten consumer mounts as a module). -/
def witnessRegistryEmitter : Emitter Unit where
  name := "witness-registry"
  style := .doubleSlash
  specSource := "SchemaCore.Emit.Witness (seedSpecs)"
  outputs :=
    ["crates/schema-generated/tests/witness_check/witnesses_generated.rs"]
  rev := "witness-registry-v1"
  attests := seedSpecs.map (·.label)
  run _ :=
    [{ path := "crates/schema-generated/tests/witness_check/witnesses_generated.rs"
       contents := moduleItems seedSpecs }]

/-! ## The duel's vector set (Kit.Duel's convention — the binary lane) -/

/-- The duel's directory: ONE directory per duel (Kit.Duel's committed
    convention). -/
def duelDir : String := "crates/schema-generated/tests/duel-witness"

/-- The duel's vector path for one row name — Kit.Duel.vpath (the ONE
    path convention; the local restatement is deleted, the adoption
    delegate). -/
def duelPath (name : String) : String := Kit.Duel.vpath duelDir name

/-- The first seeded spec (the atomic — the refusal splices'
    substrate; the match's empty arm is dead for the literal list —
    no `Inhabited` derivation exists over the GADT-indexed claim). -/
def seedHead : WitnessSpec :=
  match seedSpecs with
  | s :: _ => s
  | [] => { label := "count-positive", claim := .u64GtLit "count" 0 }

/-- THE TAMPERED RECORD: the seeded atomic's certificate with the proof
    term's verdict FLIPPED — the checker verifies the record (the
    claim's own check), never trusts it, so the flip must refuse in
    BOTH checkers. -/
def refuseTamperedRecord : List UInt8 :=
  match produce? seedHead with
  | some w => encWitness witnessVersion { w with proof := .verdict false }
  | none => panic! "seedHead refused — the seed registry is broken"

/-- THE WRONG VERSION: the seeded certificate re-encoded at version + 1
    — the envelope gate refuses before any checking (both checkers). -/
def refuseWrongVersion : List UInt8 :=
  match produce? seedHead with
  | some w => encWitness (witnessVersion + 1) w
  | none => panic! "seedHead refused — the seed registry is broken"

/-- THE FALSE CLAIM's witness (hand-built — the producer REFUSES to
    emit one: `WitnessGen.selfChecked?_none_of_check_false`). The
    vector proves the Rust checker refuses it too: the claim
    `count = 0` is false at the fixture row, and the checker's
    acceptance would imply the claim's check. -/
def refuseFalseClaim : List UInt8 :=
  encWitness witnessVersion
    ({ label := "count-zero"
       claim := (Pred.u64EqLit "count" 0 : Pred exampleCheckFields)
       proof := .verdict true, fuel := 1 }
      : Witness exampleCheckFields)

/-- THE TRUNCATED WITNESS: the seeded certificate minus its last byte
    (a torn write's shape — the fuel varint's tail gone; the decoder
    refuses, typed, never a silent zero-parse). -/
def refuseTruncated : List UInt8 :=
  let bs := seedBytes seedHead
  bs.take (bs.length - 1)

/-- THE UNKNOWN TAG: the seeded certificate with the CLAIM's tag byte
    spliced outside the ctor image (the prefix — version + label — is
    COMPUTED, never hand-counted). -/
def refuseUnknownTag : List UInt8 :=
  let bs := seedBytes seedHead
  let pre := encVarNat witnessVersion ++ encList encChar seedHead.label.toList
  bs.take pre.length ++ [9] ++ bs.drop (pre.length + 1)

/-- THE WITNESS DUEL'S VECTOR SET (Kit.Duel's convention): the seeded
    witnesses' bytes + the refusal splices as the binary lane's files,
    the manifest the text lane's. The `accept` rows' value note pins
    the dual contract (decode AND checker-accept at the pinned fuel);
    the `refuse` rows are the negative controls. -/
def witnessDuel : VectorSet where
  dir := duelDir
  name := "witness-check"
  generator := "SchemaCore.Emit.Witness"
  style := .doubleSlash
  vectors :=
    seedSpecs.map (fun spec =>
      { path := duelPath spec.label
        contents := (seedBytes spec).toByteArray })
    ++ [ { path := duelPath "refuse_tampered_record"
           contents := refuseTamperedRecord.toByteArray }
       , { path := duelPath "refuse_wrong_version"
           contents := refuseWrongVersion.toByteArray }
       , { path := duelPath "refuse_false_claim"
           contents := refuseFalseClaim.toByteArray }
       , { path := duelPath "refuse_truncated"
           contents := refuseTruncated.toByteArray }
       , { path := duelPath "refuse_unknown_tag"
           contents := refuseUnknownTag.toByteArray } ]
  expects :=
    seedSpecs.map (fun spec =>
      (duelPath spec.label,
        .decode ("accept " ++ spec.label
          ++ " at its pinned fuel over the fixture row")))
    ++ [ (duelPath "refuse_tampered_record", .refuse)
       , (duelPath "refuse_wrong_version", .refuse)
       , (duelPath "refuse_false_claim", .refuse)
       , (duelPath "refuse_truncated", .refuse)
       , (duelPath "refuse_unknown_tag", .refuse) ]

/-- THE WITNESS DUEL EMITTER (Kit.Duel's ONE body at this lane's
    parameters — the manifest rides the text lane, the vectors the
    binary lane; the spec is Unit — a pinned-constant set). -/
def witnessDuelEmitter : Emitter Unit :=
  Kit.Duel.emitterWith witnessDuel "SchemaCore.Emit.Witness"

/-! ## The regen (the writer's and the gate's ONE copy) -/

/-- THE REGEN (Journal's shape, env-free — the seeded registry is
    module data): the REGISTRY TABLE + the duel manifest on the text
    lane, the vectors on the binary lane. ONE copy — `gates gen-check`
    byte-ties BOTH lanes against it; the `schema` exe writes it. (The
    registry does NOT ride `SchemaCore.regen`'s files list: the
    fixture's legality teeth live in `SchemaCore.CheckSlice`, whose
    replay imports the barrel — importing it from `SchemaCore.Emit`
    would be a build cycle. The gen-check compare + the audit scan
    both take this regen instead.) -/
def regen : List GeneratedFile × List BinaryFile :=
  (witnessRegistryEmitter.run () ++ witnessDuelEmitter.run (),
   witnessDuel.vectors)

end SchemaCore.Emit.Witness
