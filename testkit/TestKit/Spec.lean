/-
# TestKit.Spec — the ONE spec structure: property + mandatory negatives

Owned by: the TestKit agent (the macht tree, `testkit/`).
Driving decisions: notes/v3/15-patterns.md #5 (the mandatory negative
control — a suite without its control doesn't CONSTRUCT) and
notes/v3/04-verification.md §1-2 (the ladder + obligations: a vacuous
sweep is a loud gap, never a silent pass).

Mined from: legacy/lean/TestKit/TestKit/PropSpec.lean (the negative
control, made structural) + Harness.lean (CheckResult — tests are data
folds, per 07's tooling). Fresh here: no LSpec `TestSeq`, no Plausible
`Gen` — the property is a pure check over the LCG tape (TestKit.Lcg),
the negatives list is a SUBTYPE so a spec with fewer than two controls
is unconstructible, and the result type is a three-constructor verdict
(pass | fail with minimal counterexample evidence | vacuous, louder
than failing).

The ladder rung for the control-count invariant: rung 3 — the
`negatives` field's proof is discharged `by decide` at listable call
sites (Spec.ofList's defaulted `h`); a non-literal site supplies the
proof (rung 6, one-line arithmetic).

The five questions (notes/v3/01-core.md):
- root: none — the discipline layer's spec shape over checkable
properties.
- carrier grade: the negatives SUBTYPE — a spec with fewer than two
controls is unconstructible (the unrepresentable grade).
- spine reading: none — every package's test exe folds it.
- ladder rung: rung 3 — the control-count proof discharges `by
decide` at listable sites (the header note above).
- gate row: none — TestKit is outside Gates.Packages' gated set; the
test exes are its consumers.
-/

module

public import TestKit.Lcg

@[expose] public section

namespace TestKit

/-- The value level of every check: `.ok ()` or `.error message`.
    Checks return data, never print — printing is the driver's job. -/
abbrev CheckResult := Except String Unit

/-- Boolean assertion with message. -/
def assert (cond : Bool) (msg : String) : CheckResult :=
  if cond then .ok () else .error msg

/-- Equality assertion with got/expected in the failure message. -/
def assertEq [BEq α] [ToString α] (name : String) (got expected : α) : CheckResult :=
  if got == expected then .ok () else .error s!"{name}: got {got}, expected {expected}"

/-- Where a failure came from: the property itself, or a named control. -/
inductive VerdictSource where
  /-- The property under test broke. -/
  | prop
  /-- A control broke unexpectedly. -/
  | control (name : String)
deriving BEq, Repr

def VerdictSource.toString : VerdictSource → String
  | .prop => "property"
  | .control c => s!"control '{c}'"

instance : ToString VerdictSource := ⟨VerdictSource.toString⟩

/-- The result of running a Spec — the closed verdict vocabulary
    (ctors, never strings; 04 §6). -/
inductive Verdict where
  /-- Every instance passed; every negative was caught. -/
  | pass (insts : Nat)
  /-- A check broke: which surface, which instance, the replay seed for
      that instance's tape (byte-identical replay, #14), and the message
      — the minimal counterexample evidence. -/
  | fail (source : VerdictSource) (inst : Nat) (replaySeed : UInt64) (msg : String)
  /-- A control was NOT caught: the sweep proves nothing. LOUDER than a
      failure — a vacuous suite passes forever while exercising nothing. -/
  | vacuous (uncaught : List String)
deriving BEq, Repr

def Verdict.toString : Verdict → String
  | .pass n => s!"pass {n}"
  | .fail src i rs m => s!"fail ({src}) at instance {i}, replay seed {rs}: {m}"
  | .vacuous un => s!"vacuous, uncaught: {un}"

instance : ToString Verdict := ⟨Verdict.toString⟩

/-- The ONE spec structure: a property sweep + its mandatory negatives.
    The `negatives` subtype makes a control-free sweep UNCONSTRUCTIBLE
    (pattern #5): fewer than two must-fail controls does not elaborate. -/
structure Spec where
  /-- Display name. -/
  name : String
  /-- The property at one drawn instance: consumes that instance's tape
      (LCG-seeded from the pin); must be `.ok` for every instance. -/
  prop : Tape → CheckResult
  /-- The must-FAIL controls — the sabotaged siblings the sweep MUST
      catch, one per coverage family. MANDATORY: at least two; absence
      is unconstructible (the subtype's proof field). -/
  negatives : { l : List (String × (Tape → CheckResult)) // 2 ≤ l.length }
  /-- The sweep width (the instance count). -/
  numInst : Nat
  /-- The pinned seed: same seed → same sweep, byte-identically (#14). -/
  seed : UInt64
  /-- The shrink strategy, as a NOTE — no engine until its first
      consumer (the leftover rule). -/
  shrinkNote : Option String := none

/-- Construct a Spec from a plain negatives list. The count proof is
    defaulted `by decide` — literal lists discharge at the call site;
    computed lists supply the arithmetic proof explicitly. -/
def Spec.ofList (name : String) (prop : Tape → CheckResult)
    (negatives : List (String × (Tape → CheckResult))) (numInst : Nat) (seed : UInt64)
    (h : 2 ≤ negatives.length := by decide)
    (shrinkNote : Option String := none) : Spec :=
  ⟨name, prop, ⟨negatives, h⟩, numInst, seed, shrinkNote⟩

end TestKit
