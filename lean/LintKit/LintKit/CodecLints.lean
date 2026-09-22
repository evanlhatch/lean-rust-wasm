/-
LintKit.CodecLints — two TEXT lints (the TextLints shape: pure
`String → Array TextFinding`, run by the driver over each linted module's
`.lean` file; no elaboration involvement), both enforcing doctrine §8's
correspondence preference:

* `linter.guestlang.unregisteredRoundtrip` — a module defining BOTH an
  encoder-side def (`enc*`/`emit*`/`render*`) AND a decoder-side def
  (`dec*`/`parse*`) must register their correspondence: a `PartialIso` /
  `RoundTripSpec` (the kit's codec vocabulary, CodegenCore.RoundTrip) in
  the file. Heuristic, deliberately: name-prefix classification at
  top-level `def` lines, one finding per file naming the first pair, the
  registration = the vocabulary tokens in the code channel. False-positive
  stance: emitters-only or parsers-only modules are silent (the rule needs
  BOTH directions); Tests files are exempt.

* `linter.guestlang.didyoumeanDiscipline` — the error-quality rule (the
  closed-world discipline: errors ENUMERATE the valid space). A line whose
  code channel raises an error naming something "unknown" with a backticked
  payload is a finding when the FILE uses none of the did-you-mean
  machinery (`didYouMean`/`didYouMeanSuffix`/`unknownNameError`/
  `unknownNameMessage` — CodegenCore.DidYouMean/GenKit). Heuristic,
  deliberately: per-line, comment-scoped (the comment/string scanner), so
  prose mentioning "unknown" is exempt and a file that already imports the
  discipline is exempt wholesale. Tests files are exempt.

Both honor the driver's per-linter overrides; deliberate current-tree
exceptions live in `roundtripAllowance`/`dymAllowance` (file-suffix keyed,
reasoned — the partialAllowance precedent; the ratchet only tightens).
-/
module

public import LintKit.TextLints

public meta section

open Lean

register_option linter.guestlang.unregisteredRoundtrip : Bool := {
  defValue := true
  descr := "text lint: a module defining both an encoder-side and a \
    decoder-side def must register the correspondence (PartialIso / \
    RoundTripSpec) in the file"
}

register_option linter.guestlang.didyoumeanDiscipline : Bool := {
  defValue := true
  descr := "text lint: an unknown-name rejection without any did-you-mean \
    machinery in the file (the closed-world error discipline)"
}

namespace LintKit

/-! ## unregisteredRoundtrip -/

/-- Encoder-side name prefixes (case-insensitive leaf prefixes). -/
def encNamePrefixes : List String := ["enc", "emit", "render"]

/-- Decoder-side name prefixes. -/
def decNamePrefixes : List String := ["dec", "parse"]

/-- Projection-style EXCLUSIONS (the first tree-wide run's false
positives, calibrated out — documented, not silent): `emitOf` is the
toString of the proto field named `emit` (a projection, not a wire
encoder); `decl*` (`declAnchor`/`declName`/`declLine`) are DECLARATION
table names, not decodes. A name starting with one of these (case-
insensitive) is classified as neither side regardless of prefix. -/
def roundtripNameExclusions : List String := ["emitof", "decl"]

private def hasIcPrefix (name : String) (ps : List String) : Bool :=
  let low := name.toLower
  !roundtripNameExclusions.any (low.startsWith ·)
    && ps.any (low.startsWith ·)

/-- Is this code line a top-level def-line? Returns the declared name. -/
private def defLineName? (code : String) : Option String :=
  let toks := code.trimAscii.toString.splitOn.filter (!·.isEmpty)
  match toks with
  | "def" :: nm :: _ => some nm
  | _ :: "def" :: nm :: _ => some nm  -- private/meta/partial/unsafe/protected def
  | _ => none

/-- Deliberate exceptions: (file-suffix, reason) — see the module header.
Ratchet down, never up. -/
def roundtripAllowance : List (String × String) := [
  ("LintKit/LintKit/CodecLints.lean",
   "this module DEFINES the lint's enc*/dec* vocabulary tables — the \
     name-shape the lint hunts is its own source"),
  ("lean/schema-lang/SchemaLang/Snapshot.lean",
   "REAL (reported 2026-09-19): render/parseTy's correspondence is proven \
     as the pre-kit agreement theorem toSnapshot_toTy, not a \
     PartialIso/RoundTripSpec registration — kit registration pending"),
]

/-- `unregisteredRoundtrip`: both directions defined, no registration. -/
def checkUnregisteredRoundtrip (file : String) (content : String) : Array TextFinding := Id.run do
  if isTestsFile file then return #[]
  if (roundtripAllowance.find? fun (s, _) => (file.splitOn s).length > 1).isSome then
    return #[]
  let mut encs : Array (Nat × String) := #[]
  let mut decs : Array (Nat × String) := #[]
  for (i, code, _comment) in splitCodeComments content do
    match defLineName? code with
    | some nm =>
        if hasIcPrefix nm encNamePrefixes then encs := encs.push (i, nm)
        if hasIcPrefix nm decNamePrefixes then decs := decs.push (i, nm)
    | none => pure ()
  if encs.isEmpty || decs.isEmpty then return #[]
  let codeText := (splitCodeComments content).foldl (fun a p => a ++ " " ++ p.2.1) ""
  let registered := ["PartialIso", "RoundTripSpec", "roundTrips", "Codec"].any
    (fun k => (codeText.splitOn k).length > 1)
  unless registered do
    return #[{ file := file, line := encs[0]!.1
               linter := `linter.guestlang.unregisteredRoundtrip
               message := s!"module defines both an encoder-side def \
                 (`{encs[0]!.2}`) and a decoder-side def (`{decs[0]!.2}`) \
                 with no PartialIso/RoundTripSpec registration in the file — \
                 codecs declare their correspondence (lean-doctrine.md §8, \
                 the correspondence preference)" }]
  return #[]

/-! ## didyoumeanDiscipline -/

/-- The did-you-mean machinery tokens: ANY occurrence in the file exempts
it (the discipline is imported — the lint hunts files that never learned
it). -/
def dymTokens : List String :=
  ["didYouMean", "did you mean", "unknownNameError", "unknownNameMessage",
   "didYouMeanSuffix"]

/-- Error-raising shapes the "unknown" payload must ride. -/
def errorTokens : List String :=
  ["throwError", "throw ", ".error", "throwThe", "s!\"", "m!\""]

/-- Deliberate exceptions: (file-suffix, reason) — see the module header.
Ratchet down, never up. Reasons prefixed REAL are true findings, reported
to the owner (2026-09-19 lint-gate run) and silenced only to keep the gate
green; the fix lands with the ratchet. -/
def dymAllowance : List (String × String) := [
  ("lean/dbsp/Dbsp/Certs.lean",
   "REAL (reported 2026-09-19): `@[cert]: unknown declaration` and \
     `unknown constant` neither enumerate the legal space nor append the \
     did-you-mean — fix: didYouMeanSuffix over the cert/decl names"),
]

/-- `didyoumeanDiscipline`: an unknown-name rejection with no did-you-mean
machinery anywhere in the file. RAW-LINE scan (the message lives in a
string literal — the comment/string scanner's code channel drops contents
by design), skipping comment-only lines; block-comment prose has an empty
code channel and is skipped. Documented approximation: a code line with a
trailing comment containing an `unknown …` + backtick payload false-positives
(accepted — heuristic gates, not a parser). -/
def checkDidyoumeanDiscipline (file : String) (content : String) : Array TextFinding := Id.run do
  if isTestsFile file then return #[]
  if (dymAllowance.find? fun (s, _) => (file.splitOn s).length > 1).isSome then
    return #[]
  -- file-level exemption: the discipline is already in use here
  if dymTokens.any (fun k => (content.splitOn k).length > 1) then return #[]
  let mut out := #[]
  for (i, code, _comment) in splitCodeComments content do
    let raw := (content.splitOn "\n").toArray[i - 1]!
    if code.trimAscii.toString.isEmpty then continue  -- comment-only line
    unless (raw.splitOn "unknown").length > 1 do continue
    unless raw.contains "`" do continue
    unless errorTokens.any (fun k => (raw.splitOn k).length > 1) do continue
    out := out.push { file := file, line := i
                      linter := `linter.guestlang.didyoumeanDiscipline
                      message := "unknown-name rejection without the \
                        did-you-mean discipline — errors enumerate the legal \
                        space and append `didYouMeanSuffix` (CodegenCore.GenKit; \
                        the closed-world rule, notes/canon.md's error-quality row)" }
  return out

end LintKit
