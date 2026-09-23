/-
# CodegenCore.RoundTrip — `RoundTripSpec`: the codec suite, assembled once

One record assembles the full round-trip discipline for a byte codec: the
decode∘encode PropSpec WITH its sabotaged control (the negative control is
built by the combinator — unconstructible to omit), plus a golden byte-tie
over fixed samples when `goldenDir` is set. Placement note: the runbook
names TestKit, but the dependency direction is codegen-core → TestKit —
a TestKit module cannot name `Kit.PartialIso` without a lake cycle, so
the combinator lives here (the kit's home). schema-lang's EnumWire is the
hand-assembled precedent; its append-form codecs are richer — consumers
adapt at the boundary (`decode bs |>.map (·.1)`).

Sabotage design: the kit law `decode (encode b) = some b` is ONE-ENDED —
it says nothing about corrupt bytes (a decoder that accepts ANY byte
string satisfies it). So the control corrupts the ENCODED BYTES and
asserts the corruption went undetected (`decode (sabotage (encode a)) ==
some a`); a wire format that detects the corruption falsifies the
assertion and the sampler catches the control. A control the sampler
cannot catch is flagged VACUOUS by `PropSpec.runIO` — that is the
enforcement. The default sabotage (`sabotageFirstByte`) increments byte 0
(empty encodings corrupt to `[1]`); override it for formats whose first
byte is uninformative, and let the vacuity flag judge the choice.
-/

module

public meta import CodegenCore.Kit
public meta import TestKit

public meta section

namespace CodegenCore

/-- The default byte sabotage: increment byte 0 (wrapping); an empty
    encoding corrupts to `[1]`. Deliberately minimal — a format that
    cannot detect a one-byte perturbation of its first byte is exactly
    the vacuity the control exists to flag. -/
def sabotageFirstByte : List UInt8 → List UInt8
  | [] => [1]
  | b :: bs => (b + 1) :: bs

/-- A round-trip suite spec over a byte codec. The wire side is
    `List UInt8` (the kit's `PartialIso A B` with `A := List UInt8`,
    `decode : List UInt8 → Option α` the plain — non-append — form).
    `samples` feeds the golden byte-tie (deterministic; the plausible
    sweep is seeded but not golden-pinned). -/
structure RoundTripSpec (α : Type) [BEq α] [Plausible.SampleableExt α] where
  /-- Display name (also the golden file's basename when `goldenDir`). -/
  name : String
  /-- The codec, as the kit's partial iso (law: `decode (encode b) = some b`). -/
  iso : PartialIso (List UInt8) α
  /-- Byte-level corruption for the negative control. -/
  sabotage : List UInt8 → List UInt8 := sabotageFirstByte
  /-- Fixed samples for the golden byte-tie (encodings pinned, one line
      each). -/
  samples : List α := []
  /-- When set, `runIO` byte-ties `samples`' encodings against
      `<dir>/<name>.golden` (`update := true` regenerates). -/
  goldenDir : Option String := none
  /-- Plausible instance count for both the sweep and the control. -/
  numInst : Nat := 256
  /-- Seed for both sweeps (deterministic suites). -/
  randomSeed : Option Nat := some 20261104

namespace RoundTripSpec

/-- The round-trip predicate (Bool form for the sweep). -/
def roundTrips {α : Type} [BEq α] [Plausible.SampleableExt α]
    (s : RoundTripSpec α) (a : α) : Bool :=
  s.iso.decode (s.iso.encode a) == some a

/-- The control predicate: the sabotaged bytes decode to the ORIGINAL
    value (i.e. the corruption went undetected). A detecting codec makes
    this false, and the sampler must find such an `a`. -/
def controlHolds {α : Type} [BEq α] [Plausible.SampleableExt α]
    (s : RoundTripSpec α) (a : α) : Bool :=
  s.iso.decode (s.sabotage (s.iso.encode a)) == some a

/-- The assembled PropSpec: sweep (must pass) + byte-sabotage control
    (must be caught). -/
def propSpec {α : Type} [BEq α] [Plausible.SampleableExt α]
    (s : RoundTripSpec α) : TestKit.PropSpec where
  name := s!"{s.name}: decode∘encode round trip"
  suite := LSpec.checkPlausibleIO s!"{s.name}: decode (encode a) == some a"
    (∀ a : α, s.roundTrips a = true) .done
    { numInst := s.numInst, randomSeed := s.randomSeed }
  control := LSpec.checkPlausibleIO
    s!"{s.name}: sabotaged bytes decode to original (must be caught)"
    (∀ a : α, s.controlHolds a = true) .done
    { numInst := s.numInst, randomSeed := s.randomSeed }
  controlName := "byte sabotage (default: first-byte increment)"

/-- The golden payload: one line per sample, the encoding's decimal byte
    list. -/
def goldenContents {α : Type} [BEq α] [Plausible.SampleableExt α]
    (s : RoundTripSpec α) : String :=
  String.intercalate "\n" (s.samples.map fun a => toString (s.iso.encode a)) ++ "\n"

/-- Run the whole suite: the PropSpec (sweep + mandatory control), then
    the golden byte-tie when `goldenDir` is set. `update := true`
    regenerates the golden (the deliberate-change path). -/
def runIO {α : Type} [BEq α] [Plausible.SampleableExt α]
    (s : RoundTripSpec α) (update : Bool := false) : IO UInt32 := do
  let code ← TestKit.runSpecs [s.propSpec]
  if code != 0 then return code
  match s.goldenDir with
  | none => return 0
  | some dir =>
    let path : System.FilePath := s!"{dir}/{s.name}.golden"
    match ← TestKit.Golden.checkAgainstGolden s.name s.goldenContents path update with
    | .ok () =>
      IO.println s!"✓ {s.name}: golden byte-tie ({s.samples.length} samples)"
      return 0
    | .error e =>
      IO.eprintln s!"× {e}"
      return 1

end RoundTripSpec

end CodegenCore
