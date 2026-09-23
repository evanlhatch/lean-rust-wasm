/-
# TextKit.Diag — parse diagnostics: the farthest-failure lane

The `Parser` monad is a pure recognizer — its failures are `none`, with
no rest, so a failure's POSITION is not observable from the outside. This
module adds the diagnostics lane: `Diag` (the outcome), `DParser` (the
failure-instrumented recognizer — same recognition math as `Parser`, but
each failure records the LENGTH OF INPUT REMAINING at its point plus its
expected-token label), and the driver `farthestFailure` (picks the
FARTIEST failure — the minimum remaining — unioning the expected-token
sets at that point).

The instrumentation is pure and kernel-friendly: `DParser` is just

    List Char → Option (α × List Char) × List (Nat × List String)

(remaining length × expected labels), and the combinators thread the
record like a writer. `labels exp p` re-tags any failure of `p` at its
own (deepest) point with `exp` — so a consumer writes
`labels "expected ' = '" (expectD " = " …)` and `farthestFailure`
reports exactly that expectation at the consumed column.

Honesty notes (what the DELIVERABLE's sketch typed and what this lands):

- `labels (expected : String) (p : Parser α) : Parser α` — the plain-Parser
  face (`labelsM` below) CANNOT carry positions: a `Parser` is a pure
  Option function; its internal failure state is invisible. `labelsM` is
  therefore the identity on recognition (the marker), and the
  position-carrying `labels` lives on `DParser`. The consumer uses the
  `DParser` lane.
- `farthestFailure : Parser α → List Char → Diag α` — likewise delivered
  over the `DParser` lane (`farthestFailure` takes the instrumented
  parser); the plain-Parser face (`farthestFailureM`) reports `.fail 0 []`
  on a failure (the honest unknown — no position exists in the type).
- `renderDiag` takes the line number as its parameter (the caller owns
  the line; this module owns the within-line column) and renders the
  deliverable's "line N, col M: expected 'x', 'y'".
-/

module

public import TextKit.Basic

@[expose] public section

namespace TextKit

open TextKit.Parser

namespace Diag

/-! ## the outcome -/

/-- A parse outcome: the value, or the farthest failure (position +
    expected-token set). -/
inductive Diag (α : Type u) where
  | ok (a : α)
  | fail (pos : Nat) (expected : List String)
deriving Repr, Inhabited

/-! ## the failure record -/

/-- Keep, from a failure record (`(remaining, expected-labels)` entries),
    the FARTHEST point — the minimum remaining length — unioning the
    expected labels at that point. Entries with larger remaining
    (shallower failures) are dropped. -/
def best : List (Nat × List String) → List (Nat × List String)
  | [] => []
  | (n, e) :: rest =>
      match best rest with
      | [] => [(n, e)]
      | (m, es) :: tl =>
          if n < m then [(n, e)]
          else if m < n then (m, es) :: tl
          else (n, e ++ es) :: tl

/-- The merge the writer combinators use: the union of two failure records,
    reduced to the farthest point. -/
def merge (a b : List (Nat × List String)) : List (Nat × List String) := best (a ++ b)

/-! ## the instrumented lane -/

/-- The failure-instrumented recognizer: like `Parser`, but the result
    PAIRS the option with the farthest failure record seen while
    trying. -/
abbrev DParser (α : Type) : Type :=
  List Char → Option (α × List Char) × List (Nat × List String)

namespace DParser

/-- `pure` on the instrumented lane. -/
def result (a : α) : DParser α := fun cs => (some (a, cs), [])

/-- `bind` on the instrumented lane: failures thread their records; a
    successful step merges the writer of both halves. -/
def bind {α β : Type} (p : DParser α) (f : α → DParser β) : DParser β := fun cs =>
  match p cs with
  | (none, d) => (none, d)
  | (some (a, rest), d1) =>
      let (r, d2) := f a rest
      (r, Diag.merge d1 d2)

instance : Monad DParser where
  pure := DParser.result
  bind := DParser.bind

/-- Fail with an expected-token label at the CURRENT position (the
    remaining length recorded is this input's). -/
def fail (exp : String) : DParser α := fun cs => (none, [(cs.length, [exp])])

/-- Read the input as it stands (position capture). -/
def rest : DParser (List Char) := fun cs => (some (cs, cs), [])

/-- The instrumented `consumeChar`: `exp` labels its failure. -/
def consumeCharD (c : Char) (exp : String) : DParser Unit := fun cs =>
  match consumeChar c cs with
  | some (_, rest) => (some ((), rest), [])
  | none => (none, [(cs.length, [exp])])

/-- The instrumented `takeWhile`: the maximal run before `stop` (never
    fails — the run may be empty). -/
def takeWhileD (stop : Char) : DParser String := fun cs =>
  (some (String.ofList (cs.takeWhile (fun c => c != stop)),
          cs.dropWhile (fun c => c != stop)), [])

/-- **The label**: run `p`; on success, the record passes; on failure, the
    expected-token `exp` is attached at `p`'s own (deepest) failure point
    (the record `p` left), not at the wrapper's position. -/
def labels (exp : String) (p : DParser α) : DParser α := fun cs =>
  match p cs with
  | (some r, d) => (some r, d)
  | (none, d) =>
      match Diag.best d with
      | [] => (none, [(cs.length, [exp])])
      | (n, es) :: _ => (none, [(n, exp :: es)])

end DParser

/-- The plain-Parser marker: attaching an expected-token label to a plain
    `Parser`. Recognition is UNCHANGED (a `Parser`'s failure carries no
    position — see the module header); consumers that need the reported
    label use the `DParser` lane's `DParser.labels`. -/
def labelsM (expected : String) (p : Parser α) : Parser α := p

/-- **The driver**: run the instrumented parser; a success is `.ok`, a
    failure is `.fail` at the farthest point — `pos = input.length -
    remaining` is the CONSUMED length at the farthest failure — with the
    expected-token union there. -/
def farthestFailure {α : Type} (p : DParser α) (input : List Char) : Diag α :=
  match p input with
  | (some (a, _), _) => .ok a
  | (none, d) =>
      match Diag.best d with
      | [] => .fail 0 []
      | (n, es) :: _ => .fail (input.length - n) es

/-- The driver over a PLAIN parser: failures carry no position in the
    `Parser` type, so the only honest report is `.fail 0 []` here — use
    the `DParser` lane for real diagnostics. -/
def farthestFailureM {α : Type} (p : Parser α) (input : List Char) : Diag α :=
  match p input with
  | some (a, _) => .ok a
  | none => .fail 0 []

/-- The expected-set rendering, joined with `', '` between items. -/
def expectedText (es : List String) : String :=
  String.intercalate "', '" es

/-- Render a diagnostic: "line N, col M: expected 'x', 'y'" — `lineNo` is
    the CALLER's (the driver owns the line; the column is this module's
    `pos + 1`). -/
def renderDiag (lineNo : Nat) (d : Diag α) : String :=
  match d with
  | .ok _ => "ok"
  | .fail pos expected =>
      s!"line {lineNo}, col {pos + 1}: expected '{expectedText expected}'"

/-- The Diag-combinator sanity: a failure record reduces to itself. -/
theorem best_singleton (n : Nat) (e : List String) : best [(n, e)] = [(n, e)] := rfl

/-- The driver reports a success as `.ok`. -/
theorem farthestFailure_ok {α : Type} (a : α) (rest : List Char) :
    farthestFailure (fun _ => (some (a, rest), [])) ("xy".toList) = .ok a := by
  unfold farthestFailure
  rfl

end Diag

end TextKit

end -- @[expose] public section
