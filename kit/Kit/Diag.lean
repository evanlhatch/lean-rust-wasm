/-
# Kit.Diag — the ONE diagnostic envelope (notes/v3/05-codegen.md §4)

Every channel speaks it: elaboration errors, parse failures (TextKit's
`ParseError` = a Diag with position — the CONVERGENCE is a later
order; the shapes relate, they are not merged here), lint findings,
gate verdicts, obligation rows, Rust spans, the guest's thin
diagnostics. One envelope, seven fields, a closed severity universe of
five; the did-you-mean field is filled by the ONE engine
(`Kit.suggestFor` — Kit.Suggest) through the `closedWorld` constructor,
so a closed-world failure cannot skip the suggestion (the discipline
lands in the SHAPE, not in a convention).

The E-code discipline: `ECode` is an opaque constructor-wrapped String.
The PERSISTED STABLE REGISTRY (codes never derive from enumeration
position or import order; the same E-code in an elaboration error, a
gate log, a Rust span, a guest refusal) is a LATER lane — this wrapper
does not preclude it: the registry allocates `ECode`s, nothing here
cares how. No numeric codes are hardcoded here; call sites name their
code at construction.

Relation to TextKit.ParseError: a ParseError IS the positioned Diag
(`pos` plays the envelope's position slot; `expected` = `valid`;
`context : List String` = the label stack's names; `suggest` = the same
engine's fill). The convergence (ParseError riding the envelope) is a
later order — no forcing now; only this note ties them.

Provenance: HAND-MAINTAINED (the legacy's schema-lang Diag decision —
the envelope is the honest hand version; the legacy TextKit.Diag's
farthest-failure lane stays in TextKit's lane, not here). The severity
five and the field set are the doctrine's, verbatim (05 §4).

Core-only (no mathlib/Batteries). Five questions (notes/v3/01-core.md):
- root: DATA — a pure diagnostic value; the throwing/rendering faces
  are consumers, not this module.
- carrier grade: first-order over String/List/Option — guest-thinkable
  (ids-and-strings only; a guest refusal renders from the same fields).
- spine reading: as-data (rendering is a total String function).
- ladder rung: rung 1 — the discipline lives in the type + the
  `closedWorld` route; no proof family.
- gate row: the axiom gate (Kit's report rows) + the test pins
  (KitTests: the envelope pins + the rendering pins + the negative
  controls).
-/

import Kit.Suggest

namespace Kit

/-! ## ECode — the opaque code -/

/-- The E-code: an opaque constructor-wrapped String — the one code
    space for all diagnostics (elaboration, gates, Rust spans, wasm
    faults). The persisted stable registry (allocation that never
    derives from enumeration position or import order) is a LATER
    lane; this wrapper is the shape it will fill. Construct at a
    call site via `⟨"K…"⟩`; the meaning of the string lives at the
    registry, once it exists — never in the code's spelling alone. -/
structure ECode where
  /-- The wrapped code string (the registry's key, later). -/
  code : String
deriving Repr, BEq, DecidableEq, Inhabited

/-- Render an E-code inline: `[K0123]`. -/
def ECode.render (c : ECode) : String := s!"[{c.code}]"

/-! ## Label — the context frame -/

/-- One context label: the frame's `name` ("while parsing X") plus its
    optional `detail` ("inside Y"). The list in `Diag.context` reads
    outermost first (the stack, top of file to failure point). -/
structure Label where
  /-- The frame's name (WHAT the consumer was doing). -/
  name : String
  /-- The frame's detail (WHERE — optional, empty = no detail). -/
  detail : String := ""
deriving Repr, BEq, DecidableEq, Inhabited

/-- A name-only label (no detail). -/
def Label.at (name : String) : Label := { name := name }

/-- Render one label: `name` or `name (detail)` when a detail stands. -/
def Label.render (l : Label) : String :=
  if l.detail.isEmpty then l.name else s!"{l.name} ({l.detail})"

/-! ## Severity — the closed five -/

/-- The severity universe is CLOSED: exactly five — a new channel
    reuses one of these or extends this type (the compiler drives the
    extension; 15-patterns #15's discipline at the diagnostic seam). -/
inductive Severity where
  | error      -- the channel refuses
  | warning    -- the channel proceeds + reports
  | gate       -- a gate verdict row
  | obligation -- an obligation row's finding
  | info       -- informational
deriving Repr, BEq, DecidableEq, Inhabited

/-- The severity's rendering (the closed five, verbatim). -/
def Severity.render : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .gate => "gate"
  | .obligation => "obligation"
  | .info => "info"

/-! ## Diag — the envelope -/

/-- THE diagnostic envelope (05 §4, field set verbatim). Every failure
    path constructs one — a bare error string is an unfinished API. -/
structure Diag where
  /-- The E-code (the opaque code; the registry is a later lane). -/
  code : ECode
  /-- The human message (curated: names the context, the construct,
      the fix — never a raw synthesis wall). -/
  message : String
  /-- The context stack, outermost first. -/
  context : List Label := []
  /-- The rejected input, when the failure is over one (`none` for
      positional failures that carry no single got). -/
  got : Option String := none
  /-- The VALID SPACE, enumerated (the closed-world rule — errors list
      the valid moves; empty only when there is genuinely none). -/
  valid : List String := []
  /-- The did-you-mean, filled by the ONE engine (`Kit.suggestFor`)
      via `closedWorld` — never hand-guessed at a call site. -/
  suggest : Option String := none
  /-- The closed five. -/
  severity : Severity := .error
deriving Repr, BEq, DecidableEq, Inhabited

namespace Diag

/-- THE closed-world constructor: every failure over a closed world —
    the valid space is enumerable — builds its Diag HERE, so the
    valid-space enumeration and the did-you-mean (one engine, one
    suffix) cannot be skipped. Positional/gate/info failures with no
    single `got` use the literal (empty `valid`/`suggest` is then
    honest, not a skipped discipline). -/
def closedWorld (code : ECode) (message : String) (severity : Severity)
    (got : String) (valid : List String) : Diag :=
  { code := code
    message := message
    got := some got
    valid := valid
    suggest := Kit.suggestFor got valid
    severity := severity }

/-! ## the rendering -/

/-- Render the context stack: ` [a, b (d)]`; empty stack = nothing. -/
def contextText (d : Diag) : String :=
  if d.context.isEmpty then ""
  else " [" ++ String.intercalate ", " (d.context.map Label.render) ++ "]"

/-- Render the got-slot: ` (got: x)` when present. -/
def gotText (d : Diag) : String :=
  match d.got with
  | some g => s!" (got: {g})"
  | none => ""

/-- Render the valid-space enumeration: ` — valid: a, b`; empty = nothing. -/
def validText (d : Diag) : String :=
  if d.valid.isEmpty then ""
  else " — valid: " ++ String.intercalate ", " d.valid

/-- Render the suggestion: the engine's suffix verbatim (`none` = nothing). -/
def suggestText (d : Diag) : String :=
  match d.suggest with
  | some s => s
  | none => ""

/-- The one-line rendering: `[CODE] severity: message (got: x)
    [context…] — valid: … — did you mean: …` — the tail sections appear
    only when their data stands. The GUEST rendering is this same
    line, ids-only (a later lane re-keys it; nothing here precludes
    it — the fields are the data). -/
def toString (d : Diag) : String :=
  d.code.render ++ " " ++ d.severity.render ++ ": " ++ d.message
    ++ d.gotText ++ d.contextText ++ d.validText ++ d.suggestText

instance : ToString Diag := ⟨Diag.toString⟩

end Diag

end Kit
