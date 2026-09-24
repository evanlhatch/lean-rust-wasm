/-
LintKit.CodecLints — two TEXT lints (the TextLints shape: pure
`String → String → Array TextFinding`, run by the driver over each linted
module's `.lean` file), both enforcing the correspondence preference:

* `linter.guestlang.unregisteredRoundtrip` — a file defining BOTH an
  encoder-side def (`enc*`/`emit*`/`render*`/`print*`) AND a decoder-side
  def (`dec*`/`parse*`) must register their correspondence. Registration
  = the kit's codec vocabulary in the code channel (`Kit.Correspondence`'s
  `Iso`/`Retraction`/`Codec`, the kit-grade names) OR a same-file theorem
  whose NAME names both sides (the proved correspondence law: `parse_print`,
  `decVarNat?_encVarNat_append`, `decBool?_encBool_append` — a round-trip
  law names its pair). Heuristic, deliberately: name-prefix classification
  at top-level `def` lines, one finding per file naming the first pair.
  False-positive stance: encoder-only or parser-only files are silent
  (the rule needs BOTH directions); Tests files are exempt.

* `linter.guestlang.didyoumeanDiscipline` — the error-quality rule (the
  closed-world discipline: errors ENUMERATE the valid space). A line
  whose code channel raises an error naming something "unknown" with a
  backticked payload is a finding when the FILE uses none of the
  did-you-mean machinery (`Kit.didYouMean`/`Kit.suggestSuffix` and
  siblings — Kit.Suggest is the carrier). Heuristic, deliberately:
  per-line, comment-scoped, so prose mentioning "unknown" is exempt and
  a file that already imports the discipline is exempt wholesale. Tests
  files are exempt.

Both honor the driver's per-linter overrides; deliberate current-tree
exceptions live in `roundtripAllowance`/`dymAllowance` (file-suffix
keyed, reasoned — the partialAllowance precedent; the ratchet only
tightens).
-/
module

public import LintKit.TextLints

public meta section

open Lean

register_option linter.guestlang.unregisteredRoundtrip : Bool := {
  defValue := true
  descr := "text lint: a file defining both an encoder-side and a \
    decoder-side def must register the correspondence (the Kit codec \
    vocabulary or a proved round-trip law) in the file"
}

register_option linter.guestlang.didyoumeanDiscipline : Bool := {
  defValue := true
  descr := "text lint: an unknown-name rejection without any did-you-mean \
    machinery in the file (the closed-world error discipline)"
}

namespace LintKit

/-! ## unregisteredRoundtrip -/

/-- Encoder-side name prefixes (case-insensitive leaf prefixes). `print`
joins the legacy's enc/emit/render: a printer is the text encoder. -/
def encNamePrefixes : List String := ["enc", "emit", "render", "print"]

/-- Decoder-side name prefixes. -/
def decNamePrefixes : List String := ["dec", "parse"]

/-- Projection-style EXCLUSIONS: `emitOf` is the toString of a field named
`emit`; `decl*` (`declAnchor`/`declName`/`declLine`) are DECLARATION table
names, not decodes. A name starting with one of these (case-insensitive)
is classified as neither side regardless of prefix. -/
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

/-- Deliberate exceptions: (file-suffix, reason) — the ratchet only
tightens. The first row is the lint's own source: this module DEFINES
the enc*/dec* vocabulary tables, the name-shape the lint hunts. -/
def roundtripAllowance : List (String × String) :=
  [("LintKit/CodecLints.lean",
   "this module DEFINES the lint's enc*/dec* vocabulary tables — the \
     name-shape the lint hunts is its own source")]

/-- The kit's codec vocabulary (Kit.Correspondence): a code-channel token
registers the correspondence. -/
def codecVocabTokens : List String := ["Iso", "Retraction", "Codec", "RoundTrip", "roundTrip"]

/-- A round-trip LAW registers too: a same-file theorem whose name names
both a declared encoder-side and a declared decoder-side def (the proved
correspondence — `parse_print`, `decVarNat?_encVarNat_append`). -/
def hasCorrespondenceLaw (thms : Array String) (encs decs : Array String) : Bool :=
  thms.any fun t =>
    encs.any (fun e => (t.splitOn e).length > 1)
      && decs.any (fun d => (t.splitOn d).length > 1)

/-- `unregisteredRoundtrip`: both directions defined, no registration. -/
def checkUnregisteredRoundtrip (file : String) (content : String) : Array TextFinding := Id.run do
  if isTestsFile file then return #[]
  if (roundtripAllowance.find? fun (s, _) => (file.splitOn s).length > 1).isSome then
    return #[]
  let mut encs : Array (Nat × String) := #[]
  let mut decs : Array (Nat × String) := #[]
  let mut thms : Array String := #[]
  for (i, code, _comment) in splitCodeComments content do
    let toks := code.trimAscii.toString.splitOn.filter (!·.isEmpty)
    match toks with
    | "def" :: nm :: _ | _ :: "def" :: nm :: _ =>
        if hasIcPrefix nm encNamePrefixes then encs := encs.push (i, nm)
        if hasIcPrefix nm decNamePrefixes then decs := decs.push (i, nm)
    | "theorem" :: nm :: _ | _ :: "theorem" :: nm :: _ =>
        thms := thms.push nm
    | _ => pure ()
  if encs.isEmpty || decs.isEmpty then return #[]
  let codeText := (splitCodeComments content).foldl (fun a p => a ++ " " ++ p.2.1) ""
  let registered := codecVocabTokens.any (fun k => (codeText.splitOn k).length > 1)
  let encNames := encs.map (·.2)
  let decNames := decs.map (·.2)
  let registered := registered || hasCorrespondenceLaw thms encNames decNames
  unless registered do
    return #[{ file := file, line := encs[0]!.1
               linter := `linter.guestlang.unregisteredRoundtrip
               message := s!"file defines both an encoder-side def \
                 (`{encs[0]!.2}`) and a decoder-side def (`{decs[0]!.2}`) \
                 with no codec registration in the file (the Kit.Correspondence \
                 vocabulary — `Iso`/`Retraction`/`Codec` — or a proved \
                 round-trip law naming both sides); codecs declare their \
                 correspondence (the correspondence preference)" }]
  return #[]

/-! ## didyoumeanDiscipline -/

/-- The did-you-mean machinery tokens: ANY occurrence in the file exempts
it (the discipline is imported — the lint hunts files that never learned
it; Kit.Suggest is the carrier). -/
def dymTokens : List String :=
  ["didYouMean", "did you mean", "unknownNameError", "unknownNameMessage",
   "didYouMeanSuffix", "suggestSuffix", "Kit.suggestFor"]

/-- Error-raising shapes the "unknown" payload must ride. -/
def errorTokens : List String :=
  ["throwError", "throw ", ".error", "throwThe", "s!\"", "m!\""]

/-- Deliberate exceptions: (file-suffix, reason). NONE at the fresh port
— the ratchet only tightens: a silenced site lands here with its reason,
never silently. -/
def dymAllowance : List (String × String) := []

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
                        space and append the suggestion (Kit.didYouMean / \
                        Kit.suggestSuffix; the closed-world rule)" }
  return out

end LintKit
