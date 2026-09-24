/-
# Kit.Diag — the ONE diagnostic envelope's Kit-namespaced face (the shim)

Every channel speaks it: elaboration errors, parse failures (TextKit's
`ParseError` = a Diag with position — THE CONVERGED SHAPE,
`ParseError extends TextKit.Diag`), lint findings, gate verdicts,
obligation rows, Rust spans, the guest's thin diagnostics. One
envelope, seven fields, a closed severity universe of five; the
did-you-mean field is filled by the ONE engine (`Kit.suggestFor` —
which itself delegates to `TextKit.suggestFor`) through the
`closedWorld` constructor, so a closed-world failure cannot skip the
suggestion (the discipline lands in the SHAPE, not in a convention).

THE CONVERGENCE ORDER (this wave): the envelope's ONE home is
`TextKit.Diag` — the cone/build call: a `module` file cannot import a
pre-`module` file, so textkit→kit is build-impossible, while Kit's own
module files already import TextKit (the proven direction). This module
is the `Kit`-namespaced face of the envelope: the `abbrev` aliases
below resolve every `Kit`-namespaced use (`Kit.Diag`, `Kit.ECode`,
`Kit.Label`, `Kit.Severity`, and all dot notation under them — the
constructors, the fields, `.render`, `.at`, `.closedWorld`, the
rendering family — unfolds to the head constant) to the TextKit
declarations, so every Kit-side consumer (Scaffold, SchemaCore,
DemoApp, the KitTests pins) is interface-preserved. The E-code
discipline note and the field-set provenance live with the home
(`TextKit.Diag`'s header); the severity five and the field set are the
doctrine's, verbatim (05 §4).

Core-only (no mathlib/Batteries). Five questions (notes/v3/01-core.md):
answered at the home module; this shim adds nothing but the namespace.
-/

import TextKit.Diag

namespace Kit

/-- The E-code: an opaque constructor-wrapped String — the one code
    space for all diagnostics. ALIAS of `TextKit.ECode` (the home). -/
abbrev ECode := TextKit.ECode

/-- One context label: the frame's `name` plus its optional `detail`.
    ALIAS of `TextKit.Label` (the home). -/
abbrev Label := TextKit.Label

/-- The closed severity universe: exactly five. ALIAS of
    `TextKit.Severity` (the home). -/
abbrev Severity := TextKit.Severity

/-- THE diagnostic envelope (05 §4, field set verbatim). ALIAS of
    `TextKit.Diag` (the home). -/
abbrev Diag := TextKit.Diag

/-! The envelope's FUNCTION surface as real `Kit`-namespaced constants
    (dot-notation calls like `Kit.Diag.closedWorld x` resolve the name
    in the namespace, not through the abbrev — the constants must
    exist). Each delegates to the home; the behavior is the home's,
    verbatim. -/

namespace Diag

/-- THE closed-world constructor: every failure over a closed world —
    the valid space is enumerable — builds its Diag through the ONE
    engine (`TextKit.suggestFor`), so the valid-space enumeration and
    the did-you-mean cannot be skipped. DELEGATION to the home. -/
def closedWorld (code : ECode) (message : String) (severity : Severity)
    (got : String) (valid : List String) : Diag :=
  TextKit.Diag.closedWorld code message severity got valid

/-- The one-line rendering (05 §4: `[CODE] severity: message (got: x)
    [context…] — valid: … — did you mean: …`). DELEGATION to the home. -/
def toString (d : Diag) : String := TextKit.Diag.toString d

instance : ToString Diag := ⟨toString⟩

end Diag

/-- A name-only label (no detail). DELEGATION to the home. -/
def Label.at (name : String) : Label := TextKit.Label.at name

end Kit
