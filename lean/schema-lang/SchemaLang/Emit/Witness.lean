/-
# SchemaLang.Emit.Witness — host-side witness GENERATION + self-check (W9.4)

The fifth tier's host half (notes/design-guest-verified.md §3 "host, at
emission" + §4 step 1): from each registered `guestVerified` witness
spec (`SchemaLang.WitnessSpec`, carried as spec-module data in
`Demo.demoWitnesses`), GENERATE the certificate — the claim-matched
proof term in W9.1's calculus, the pinned fuel (`consumed × 4`, owner
decision 2 / §7.3), the envelope pair (version + the schema-surface
hash of the record's field list) — SELF-CHECK it in-process with
W9.2's checker (`selfChecked?`), and emit the byte-tied witness
registry artifact (`../../src/witnesses_generated.rs`, one row per
obligation: label + artifact name + version + surface hash + fuel +
the encoded certificate bytes).

THE CORE RULE (the order's): **an emitter that emits an unchecked
witness is a bug.** The self-check is wired INTO the run path —
`renderRow` renders a row ONLY from a `selfChecked?`-accepted
certificate; a refusal `panic!`s the gen driver (emission failure,
loud — the byte-tied artifact cannot carry an unchecked witness). The
emitter's `law` (W7.3p2's field, populated) states exactly that every
registered spec self-checks, and `witnessLaw_discharged` proves it for
the demo registry by citing `selfChecked?_of_WHolds` — generation is
COMPLETE for true claims: `WHolds` (the claim's denotation, W9.2) →
the generated certificate passes the checker at its pinned fuel. The
two directions together: the host ships only checked witnesses
(self-check), and every true registered claim ships (completeness).

## Deviations / decisions (each with its reason)

1. **`run` ignores the ctx; the spec registry is module data.** The
   `circuitEmitter` precedent ("the circuit is DATA in this module (the
   demo scale — a registry lane … is the follow-up)"). Concretely this
   module imports `Demo` for `demoWitnesses` — deliberate, because the
   spec's context rides Demo's DERIVED field list
   (`derive_schema_fields`: a User field rename fails the demo module's
   own elaboration; a hand mirror in this module could drift). The
   GenCtx lane (`invariantItemExt`'s replay shape) is the follow-up
   when a second package registers witnesses — recorded in
   `SchemaLang.WitnessSpec`'s header. Consequence: `gates gen-check`
   needs NO wiring for this artifact (the fold is ctx-independent);
   the coverage matrix baseline gains one emitter column (the owner's
   `gates coverage --write`).
2. **The artifact is a Rust static table in `src/`, not a `witnesses/`
   blob directory.** The declared-outputs discipline: one writer (this
   emitter), byte-tied like every sibling. The per-obligation
   `witnesses/<record>-v<from>-v<to>.wtn` name (design §4) is the
   row's `artifact` field — the logical name the obligation's
   `.guestWitness` evidence cites; the registry file is the physical
   artifact the host reads (W9.5's consumer flow: host looks the row
   up by label, ships `(journal bytes, row.bytes)` to the guest). The
   guest only ever sees BYTES (the W6.2 boundary rule) — the Rust
   table is host-side plumbing.
3. **Fuel accounting is exact, then quadruplicated.** W9.2's checker
   costs 1 per rule node + 1 per chain step (its deviation 2);
   `fuelConsumed` computes exactly that, `fuelPinned` multiplies by 4
   (owner decision 2: `consumed × 4` pinned in the artifact — host and
   guest agree BY CONSTRUCTION). `checkWitness_mono` (W9.2) transports
   acceptance at the consumed fuel to the pinned fuel — the headroom
   can never cause a host/guest verdict split.
4. **The envelope fingerprint is the field-list surface hash** (design
   §1: "derived from the schema fingerprint pair of the record the
   claim ranges over" — there is no pre-existing fingerprint
   machinery; the Snapshot spelling of the field list,
   `Ty.toSnapshot`-rendered and `String.hash`ed, IS the surface the
   claim resolves against). The guest's `decEnvelope?` rejects a
   witness generated against another surface before any checking.

Deliberate exclusions: the guest-side re-check + the apply-gate
(W9.5), the guest compile (W9.6), the env-extension registration lane
(above), multi-record segment batching (design §7.2's size finding
path).
-/

module

public import CodegenCore
public import SchemaLang.Emit.GenCtx
public import SchemaLang.WitnessSpec
public import SchemaLang.Snapshot
public import Demo

@[expose] public section

namespace SchemaLang.Emit.Witness

open SchemaLang.Witness (WProp WProof WStep WU64 WBoolExpr encWitness)
open SchemaLang.WitnessCheck (RowValsP evalWU64? evalWBool? checkStepProof checkSteps
  checkWitness checkWitnessArtifact WHolds checkWitness_mono)

/-! ## The envelope pair (design §1, W9.1's caller-supplied parameters) -/

/-- The witness format's wire VERSION (the envelope's first field —
    bumping it is the wire-breaking change, the EnumWire discipline). -/
def witnessVersion : Nat := 1

/-- The schema surface's canonical text: `name:ty` pairs in field
    order at the Snapshot spelling (the same `Ty.toSnapshot` the
    snapshot format pins — one spelling, two consumers). -/
def surfaceText (fs : List Field) : String :=
  String.intercalate ";" (fs.map fun f => f.name ++ ":" ++ f.ty.toSnapshot)

/-- THE SCHEMA-SURFACE HASH (deviation 4): the envelope fingerprint —
    the guest rejects a witness generated against another surface
    before any checking (`Codec.decEnvelope?_wrong_version`-adjacent:
    the fingerprint mismatch is a decode-level refusal). -/
def surfaceHash (fs : List Field) : UInt64 := String.hash (surfaceText fs)

/-! ## Generation: the proof term + the fuel -/

/-- The proof term the claim's shape demands (design §2.2's
    claim-matched grammar): `valid` ↔ `byValidEval`; `chain` ↔ one
    `byValidEval` per step (W9.2's deviation 3 — the per-step claim is
    always `.valid inv`, whose only proof ctor is `byValidEval`);
    `eqU` ↔ `byEval` at the LEFT side's computed value (the RIGHT
    side's agreement is the checker's verdict — an unequal pair fails
    the self-check below, loudly). `none` = the claim cannot be
    evaluated against the context at all (an unresolvable operand —
    the §7.1 refusal shape). -/
def proofFor : (claim : WProp) → (fs : List Field) → RowVals fs → Option WProof
  | .valid _, _, _ => some .byValidEval
  | .eqU a _, fs, row => (evalWU64? a fs row).map .byEval
  | .chain steps _, _, _ => some (.steps (.replicate steps.length .byValidEval))

/-- The fuel the checker CONSUMES on an accepting run (W9.2's
    deviation 2: one unit per rule node, plus one per chain step). -/
def fuelConsumed : WProp → Nat
  | .chain steps _ => steps.length + 1
  | _ => 1

/-- The SHIPPED fuel (owner decision 2 / design §7.3): `consumed × 4`,
    pinned in the artifact — host and guest agree by construction, and
    a legitimately expensive witness is a claim-shape finding, never a
    retry. -/
def fuelPinned (claim : WProp) : Nat := fuelConsumed claim * 4

/-- Generate the certificate for a registered spec. UNCHECKED — the
    self-check is `selfChecked?`'s, and the emitter consumes only
    `selfChecked?` (this function exists separately so the Tests'
    doctored-generator control can exhibit exactly what skipping the
    check would ship). -/
def generateWitness (spec : WitnessSpec) : Option SchemaLang.Witness.Witness :=
  (proofFor spec.claim spec.ctx.fs spec.ctx.row).map fun proof =>
    { label := spec.label
      claim := spec.claim
      proof := proof
      fuel := fuelPinned spec.claim }

/-- THE SELF-CHECK (the order's core rule): generation is complete
    only when the freshly generated certificate passes W9.2's checker
    IN-PROCESS at its own pinned fuel over the spec's decoded context.
    `none` = emission failure (the run path panics — loud). -/
def selfChecked? (spec : WitnessSpec) : Option SchemaLang.Witness.Witness :=
  match generateWitness spec with
  | none => none
  | some w =>
      if checkWitnessArtifact w spec.ctx then some w else none

/-! ## Acceptance at the consumed fuel (the completeness lemmas) -/

/-- `valid` accepts at one fuel unit when the row fold is 1. -/
theorem checkWitness_accept_valid {fs : List Field} {e : WBoolExpr}
    {row : RowVals fs} {log : List (RowVals fs)}
    (h : evalWBool? e fs row = some 1) :
    checkWitness 1 (.valid e) .byValidEval fs row log = true := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  simp only [checkWitness]
  exact beq_iff_eq.mpr h

/-- `eqU` accepts at one fuel unit when both sides evaluate to the
    proof's expected value. -/
theorem checkWitness_accept_eqU {fs : List Field} {a b : WU64} {v : UInt64}
    {row : RowVals fs} {log : List (RowVals fs)}
    (ha : evalWU64? a fs row = some v) (hb : evalWU64? b fs row = some v) :
    checkWitness 1 (.eqU a b) (.byEval v) fs row log = true := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  simp only [checkWitness, Bool.and_eq_true]
  exact ⟨beq_iff_eq.mpr ha, beq_iff_eq.mpr hb⟩

/-- The per-step walk accepts at exactly `steps.length` fuel when every
    referenced offset resolves and the invariant holds there. -/
theorem checkSteps_accept {fs : List Field} (steps : List WStep) {inv : WBoolExpr}
    {log : List (RowVals fs)}
    (h : ∀ s, s ∈ steps → ∃ r, log[s.offset]? = some r ∧ evalWBool? inv fs r = some 1) :
    checkSteps steps.length steps (.replicate steps.length .byValidEval) inv fs log = true := by
  induction steps with
  | nil => rfl
  | cons s ss ih =>
      obtain ⟨r, hget, hr⟩ := h s List.mem_cons_self
      have hstep : checkStepProof .byValidEval inv fs r = true := beq_iff_eq.mpr hr
      have htail := ih (fun s' hs' => h s' (List.mem_cons_of_mem s hs'))
      simp only [List.length_cons, List.replicate_succ, checkSteps, hget, hstep,
        Bool.true_and, htail]

/-- `chain` accepts at `steps.length + 1` fuel when the invariant holds
    of the initial row and at every referenced log row. -/
theorem checkWitness_accept_chain {fs : List Field} {steps : List WStep}
    {inv : WBoolExpr} {row : RowVals fs} {log : List (RowVals fs)}
    (hinit : evalWBool? inv fs row = some 1)
    (hsteps : ∀ s, s ∈ steps → ∃ r, log[s.offset]? = some r ∧ evalWBool? inv fs r = some 1) :
    checkWitness (steps.length + 1) (.chain steps inv)
      (.steps (.replicate steps.length .byValidEval)) fs row log = true := by
  simp only [checkWitness, List.length_replicate, beq_self_eq_true, Bool.true_and,
    Bool.and_eq_true]
  exact ⟨beq_iff_eq.mpr hinit, checkSteps_accept steps hsteps⟩

/-! ## Generation is complete for true claims (the per-ctor helpers +
    the `WHolds` dispatch) -/

/-- A true `valid` claim self-checks (consumed fuel 1, pinned 4 —
    `checkWitness_mono` covers the headroom). -/
theorem selfChecked?_valid (label artifact : String) (e : WBoolExpr) (ctx : RowValsP)
    (he : evalWBool? e ctx.fs ctx.row = some 1) :
    (selfChecked? ⟨label, artifact, .valid e, ctx⟩).isSome = true := by
  have hle : (1 : Nat) ≤ fuelPinned (.valid e) := by
    show 1 ≤ 1 * 4; decide
  have hacc : checkWitness (fuelPinned (.valid e)) (.valid e) .byValidEval
      ctx.fs ctx.row ctx.log = true :=
    checkWitness_mono hle _ _ _ _ (checkWitness_accept_valid he)
  simp [selfChecked?, generateWitness, proofFor, checkWitnessArtifact, hacc]

/-- A true `eqU` claim self-checks (the generated `byEval` carries the
    left side's value; the right side's agreement is the hypothesis). -/
theorem selfChecked?_eqU (label artifact : String) (a b : WU64) (v : UInt64)
    (ctx : RowValsP)
    (ha : evalWU64? a ctx.fs ctx.row = some v)
    (hb : evalWU64? b ctx.fs ctx.row = some v) :
    (selfChecked? ⟨label, artifact, .eqU a b, ctx⟩).isSome = true := by
  have hle : (1 : Nat) ≤ fuelPinned (.eqU a b) := by
    show 1 ≤ 1 * 4; decide
  have hacc : checkWitness (fuelPinned (.eqU a b)) (.eqU a b) (.byEval v)
      ctx.fs ctx.row ctx.log = true :=
    checkWitness_mono hle _ _ _ _ (checkWitness_accept_eqU ha hb)
  simp [selfChecked?, generateWitness, proofFor, checkWitnessArtifact, ha, hacc]

/-- A true `chain` claim self-checks (consumed `steps.length + 1`,
    pinned quadruplicated). -/
theorem selfChecked?_chain (label artifact : String) (steps : List WStep)
    (inv : WBoolExpr) (ctx : RowValsP)
    (hinit : evalWBool? inv ctx.fs ctx.row = some 1)
    (hsteps : ∀ s, s ∈ steps → ∃ r, ctx.log[s.offset]? = some r ∧
      evalWBool? inv ctx.fs r = some 1) :
    (selfChecked? ⟨label, artifact, .chain steps inv, ctx⟩).isSome = true := by
  have hle : steps.length + 1 ≤ fuelPinned (.chain steps inv) := by
    show steps.length + 1 ≤ (steps.length + 1) * 4; omega
  have hacc : checkWitness (fuelPinned (.chain steps inv)) (.chain steps inv)
      (.steps (.replicate steps.length .byValidEval)) ctx.fs ctx.row ctx.log = true :=
    checkWitness_mono hle _ _ _ _ (checkWitness_accept_chain hinit hsteps)
  simp [selfChecked?, generateWitness, proofFor, checkWitnessArtifact, hacc]

/-- GENERATION IS COMPLETE FOR TRUE CLAIMS: if the spec's claim HOLDS
    over its decoded context (W9.2's denotation), the generated
    certificate passes the checker at its pinned fuel — the host never
    fails to certify a true registered claim (the other direction —
    only checked certificates ship — is `selfChecked?` itself, and its
    soundness is W9.2's `checkWitnessArtifact_sound`). -/
theorem selfChecked?_of_WHolds (spec : WitnessSpec)
    (h : WHolds spec.claim spec.ctx.row spec.ctx.log) :
    (selfChecked? spec).isSome = true := by
  obtain ⟨label, artifact, claim, ctx⟩ := spec
  obtain ⟨fs, row, log⟩ := ctx
  dsimp only at h
  cases h
  next e he => exact selfChecked?_valid _ _ _ _ he
  next a b v ha hb => exact selfChecked?_eqU _ _ _ _ _ _ ha hb
  next steps inv hinit hsteps =>
    exact selfChecked?_chain _ _ _ _ _ hinit hsteps

/-! ## The demo registry's semantic premise + the emitter law -/

/-- The demo spec's claim HOLDS (the premise the law's discharge
    cites): `id > 0` at the initial row (id 1) and at both log rows
    (ids 2, 3 — the identity-upcast v1→v2 segment, Demo's header
    note). -/
theorem demoWitnessSpec_holds :
    WHolds demoWitnessSpecUserV1V2.claim demoWitnessSpecUserV1V2.ctx.row
      demoWitnessSpecUserV1V2.ctx.log := by
  show WHolds (.chain [⟨0⟩, ⟨1⟩] (.gt (.col "id") (.lit 0)))
    demoWitnessInitRow demoWitnessLog
  apply WHolds.chain
  · decide
  · intro s hs
    fin_cases hs
    · exact ⟨userNameLenRowOf ⟨2, "cd", "c@x", []⟩, rfl, by decide⟩
    · exact ⟨userNameLenRowOf ⟨3, "ef", "e@x", []⟩, rfl, by decide⟩

/-- The emitter's law (W7.3p2's `law` field, populated): every
    registered witness spec's generated certificate passes W9.2's
    checker at emission. Ctx-independent (the registry is module data
    — deviation 1, the `circuitLaw` precedent). -/
def witnessLaw : GenCtx → Prop := fun _ =>
  ∀ spec ∈ demoWitnesses, (selfChecked? spec).isSome = true

/-- The discharge: the demo registry's single row holds semantically
    (`demoWitnessSpec_holds`), and generation is complete for true
    claims (`selfChecked?_of_WHolds`) — no `decide` over the checker
    here, the law's proof IS the semantic argument. -/
theorem witnessLaw_discharged (ctx : GenCtx) : witnessLaw ctx := by
  intro spec hspec
  simp only [demoWitnesses, List.mem_singleton] at hspec
  subst hspec
  exact selfChecked?_of_WHolds _ demoWitnessSpec_holds

/-! ## The artifact (one row per obligation: label + encoded witness +
    fuel + the schema-surface hash) -/

/-- The registry artifact's path (repo-root-relative, the declared
    output — the one-writer discipline). -/
def witnessArtifactPath : String := "../../src/witnesses_generated.rs"

/-- The wire bytes as a Rust `&[u8]` literal's body. -/
def renderBytes (bs : List UInt8) : String :=
  String.intercalate ", " (bs.map toString)

/-- One registry row's Rust line — THE SELF-CHECK WIRED INTO THE RUN
    PATH: the row renders ONLY from a `selfChecked?`-accepted
    certificate; a refusal panics the gen driver (a failed self-check
    is an emission failure, loud — the byte-tied artifact cannot carry
    an unchecked witness). -/
def renderRow (spec : WitnessSpec) : String :=
  match selfChecked? spec with
  | some w =>
      let fp := surfaceHash spec.ctx.fs
      let bs := encWitness witnessVersion fp.toNat w
      s!"    WitnessRow \{ label: {CodegenCore.Emit.jsonStr w.label}, artifact: {CodegenCore.Emit.jsonStr spec.artifact}, "
        ++ s!"version: {witnessVersion}u64, surface_hash: {fp}u64, fuel: {w.fuel}u64, "
        ++ s!"bytes: &[{renderBytes bs}] },"
  | none =>
      panic! s!"witness self-check FAILED at emission: `{spec.label}` — the \
        generated certificate did not pass WitnessCheck.checkWitnessArtifact at \
        its pinned fuel over the spec's decoded context; refusing to emit \
        (W9.4: an emitter that emits an unchecked witness is a bug)"

/-- The full module items (deterministic: registration order
    throughout). -/
def moduleItems (specs : List WitnessSpec) : List CodegenCore.Emit.Rust.Item :=
  [ .comment "GENERATED from Demo.demoWitnesses (SchemaLang.Emit.Witness, W9.4) — the"
  , .comment "guestVerified witness registry: one row per registered guestVerified"
  , .comment "obligation. Every row's certificate PASSED W9.2's checker in-process"
  , .comment "at emission (a refused self-check panics the gen driver — this file"
  , .comment "cannot carry an unchecked witness). Do not edit — regenerate (just gen)."
  , .raw ""
  , .raw "/// One witness registry row: the obligation's label, the artifact name its"
  , .raw "/// `guestWitness` evidence names (SchemaObligation.discharge), the envelope"
  , .raw "/// version, the schema-surface hash (the envelope fingerprint — the"
  , .raw "/// field-list surface the claim was generated against), the pinned fuel"
  , .raw "/// (consumed x 4 — owner decision 2), and the certificate's wire bytes"
  , .raw "/// (SchemaLang.Witness.encWitness)."
  , .raw "pub struct WitnessRow {"
  , .raw "    pub label: &'static str,"
  , .raw "    pub artifact: &'static str,"
  , .raw "    pub version: u64,"
  , .raw "    pub surface_hash: u64,"
  , .raw "    pub fuel: u64,"
  , .raw "    pub bytes: &'static [u8],"
  , .raw "}"
  , .raw ""
  , .raw "/// The registry, in registration order. The guest's flow (design"
  , .raw "/// guest-verified §4): decode the envelope (version + fingerprint),"
  , .raw "/// decode the witness, re-check via the compiled checkWitness at the"
  , .raw "/// row's fuel over the decoded row + log segment. Rejection = the"
  , .raw "/// typed fault; the events are not applied."
  , .raw "pub static WITNESS_REGISTRY: &[WitnessRow] = &["
  ]
  ++ specs.map (fun spec => .raw (renderRow spec))
  ++ [ .raw "];" ]

/-- The emitter's pure fold (fully testable — the Tests re-run it and
    round-trip the rendered bytes through W9.1's decoder). -/
def witnessFiles (specs : List WitnessSpec) : List CodegenCore.Emit.GeneratedFile :=
  [ { path := witnessArtifactPath
      contents := CodegenCore.Emit.Rust.renderModule (moduleItems specs) } ]

/-- The witness emitter: buf-plugin shape (name/style/specSource/
    declared outputs/pure run) + the POPULATED law (`witnessLaw`,
    discharged by `witnessLaw_discharged`). `run` ignores the ctx —
    the registry is module data (deviation 1); the byte-tie pins the
    output. The parent registry wires it into
    `SchemaLang.Emit.coreEmitters`. -/
def witnessEmitter : CodegenCore.Emit.Emitter GenCtx where
  name := "witness"
  style := .doubleSlash
  specSource := "SchemaLang.Emit.Witness (Demo.demoWitnesses)"
  outputs := [witnessArtifactPath]
  run _ctx := witnessFiles demoWitnesses
  law := some witnessLaw

end SchemaLang.Emit.Witness

end -- @[expose] public section
