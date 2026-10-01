/-
# TextKit.ConfigFormat — the config sources' text formats as grammar values

Owner: the config-face agent (the mandate tree, `textkit/`).
Driving decisions: notes/v3/08-capabilities.md §34 (the configuration —
the sources are grammars) + design-wave-30.md C4 (the CLI-args +
env-vars + file grammars as TextKit grammar values).

The honest minimal (the leftover rule: a nested face needs a consumer):

- the FILE format: `key=value` rows, one per line, LF-terminated —
  the flat rep-of-lines shape (`GrammarSlice`'s template, the
  code-registry's row shape). NO comments, NO nesting, NO quoting —
  each names its exclusion: comments are a format decision the first
  real config file forces; the nested face (`[section]`) lands when a
  consumer's keys need namespacing (dotted keys are the flat escape
  at the lowering layer — the consumer maps `a.b` itself).
- the ENV format: the SAME row grammar at one row (`K=V`) — the OS
  delivers the split already (`IO.getEnv`'s halves); the grammar value
  pins the `env`(1) spelling for the round trip + the tests.
- the CLI format: `--key=value` (the dash prefix + the row).

The keys' charset: alphanumeric + `_` (the shared `identAtom`; env
conventions fit). The values' charset: everything but LF — the
boundary is charset exclusion (`\n` ends the value, `=` ends the
key). The value lexeme KEEPS the maximal-munch row (`some valChar` —
`print_scan`'s boundary is the munch's, never omitted); the
line-level tail rows stay vacuous at the format because the LF atom
is every line's LAST component (its munch is `none` — a single char
scan needs no boundary declaration), so a next line's key-led first
never collides with a munch row. The canonical print: `key=value\n` —
no padding spaces (the canonical form is the print's job; the
values' spaces are the value's own bytes — round-trip exact).

The laws (the grammar-layer laws as instances, `GrammarSlice`'s
route): the Predictive certificate rides the PROVED `wfCheck_sound`
(`decide` discharges `wfCheck`); law 1 (`run_print_fixFree` — the
parse of the print is the value) and law 2 (`print_parse` — a
successful parse consumed exactly the print) instantiate at
`fileGrammar` / `rowG`, the valueOk/tailOk premises decided at the
pins.

Core-only (imports `TextKit.Grammar*` only — the cone rule). The
typed face (schema records, the override ORDER, the Diag refusals)
lives in `SchemaCore.Config` — this module is the SOURCE FORMATS'
text layer, consumer-agnostic.
-/

import TextKit.Grammar
import TextKit.Grammar.Lexemes
import TextKit.Grammar.Check
import TextKit.Grammar.Laws

namespace TextKit.ConfigFormat

/-! ## the lexemes -/

/-- The key charset: alphanumeric + underscore (the env conventions'
    spellings fit). -/
def keyChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The value charset: everything but LF (the row boundary). -/
def valChar (c : Char) : Bool := c != '\n'

/-- The value atom's write-side gate: nonempty, all non-LF, non-LF
    head (the maximal-run round-trip discipline — `identOk` at the
    value charset). -/
def valOk (s : String) : Bool := identOk valChar valChar s

open Grammar in
/-- The key atom: the shared `identAtom` at the key charset (the
    generator rule — the ident shape is Lexemes', never re-rolled). -/
def keyAtom : Lexeme String := identAtom "key" keyChar keyChar (fun _ hc => hc)

open Grammar in
/-- The value atom: the ident shape at the value charset — the shared
    `identAtom` at `h = p = valChar` (the generator rule; the maximal
    run's boundary is the munch's, see the header). The `fail` spelling
    is the row-level refusal's label. -/
def valAtom : Lexeme String := identAtom "value" valChar valChar (fun _ hc => hc)

/-! ## the rows -/

open Grammar in
/-- The row-level pair rel: `((), v)` prints/scans as the value — the
    `=`'s unit payload discarded at the semantic mapping (the rel
    node's ONE job). -/
def pairTailCodec : Kit.Codec (Unit × String) String where
  encode := fun s => ((), s)
  decode := fun p => Option.some p.2
  policy := fun _ => True
  decode_encode := by intro s; rfl
  decode_some_policy := by intro a b _h; trivial

open Grammar in
/-- The `key=value` row (WITHOUT the newline — the env row's shape;
    the file line and the CLI flag extend it). -/
def rowG : Grammar (String × String) :=
  .seq (.atom keyAtom)
    (.rel pairTailCodec (fun _ => true) (fun _ _ _ => rfl)
      (fun raw r h => by
        cases raw with
        | mk u s =>
          cases u
          have hs : s = r := Option.some.inj h
          subst hs
          rfl)
      "pair" []
      (.seq (.atom (constCharLex '=' ())) (.atom valAtom)))

open Grammar in
/-- The FILE line: a row + the LF terminator (the line's payload pairs
    the row with the unit — the terminator's payload; the CLEAN row
    list is the file grammar's rel below). -/
def lineG : Grammar ((String × String) × Unit) :=
  .seq rowG (.atom (constCharLex '\n' ()))

/-- The line tuples' firsts — the unwrap is TOTAL (the second
    component is `Unit`, pure structure, nothing to refuse), so the
    decode is `some` of the map. The rel node is the ONLY
    payload-changing node; the exactness is the mapPairSelf law. -/
def unwrapRows : List ((String × String) × Unit) → Option (List (String × String)) :=
  fun raw => Option.some (raw.map (·.1))

/-- The wrap-unwrap law: wrapping every row then taking firsts is the
    identity (the elementwise face: every tuple's second is the unit,
    so the composite is the identity map). -/
theorem mapPairSelf : ∀ (raw : List ((String × String) × Unit)),
    ((raw.map (·.1)).map (fun p => (p, ()))) = raw := by
  intro raw
  induction raw with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | mk p u =>
          cases u
          simp only [List.map_cons, ih]

/-- The unwrap-then-wrap map is the identity on clean rows (the
    elementwise projection reduces). -/
theorem mapUnwrapId : ∀ rows : List (String × String),
    (rows.map (fun p => (p, ()))).map (·.1) = rows := by
  intro rows
  induction rows with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The unwrap codec (the rel row; the payload change is total). -/
def unwrapCodec : Kit.Codec (List ((String × String) × Unit)) (List (String × String)) where
  encode := fun rows => rows.map (fun p => (p, ()))
  decode := fun raw => Option.some (raw.map (·.1))
  policy := fun _ => True
  decode_encode := by
    intro rows
    show Option.some ((rows.map (fun p => (p, ()))).map (·.1)) = _
    rw [mapUnwrapId]
  decode_some_policy := by intro a b _h; trivial

/-- The codec's exactness: a decoded row list re-encodes to its raw
    (the mapPairSelf law at the codec's faces). -/
theorem unwrapCodec_exact : ∀ (raw : List ((String × String) × Unit))
    (r : List (String × String)), unwrapCodec.decode raw = Option.some r →
    unwrapCodec.encode r = raw := by
  intro raw r h
  have h1 : raw.map (·.1) = r := Option.some.inj h
  subst h1
  exact mapPairSelf raw

/-- The tail codec's exactness: a decoded value re-encodes to its raw
    (the unit payload's projection — the row's rel node's law). -/
theorem pairTailCodec_exact : ∀ (a : Unit × String) (b : String),
    pairTailCodec.decode a = Option.some b → pairTailCodec.encode b = a := by
  intro ⟨u, s⟩ b h
  have hs : s = b := Option.some.inj h
  cases u
  subst hs
  rfl

/-- THE GRADUATION (15-patterns #11 at the codec grade,
    `Kit.Codec.toIsoOfExact` — the registry's `registryIso` precedent):
    the row codec is a TRUE `Iso` — the decode is TOTAL (the unit
    payload's projection never refuses) + `pairTailCodec_exact` —
    `()` ≅ the value, both round trips. -/
def pairTailIso : Kit.Iso (Unit × String) String :=
  pairTailCodec.toIsoOfExact (fun a => ⟨a.2, rfl⟩) pairTailCodec_exact

/-- THE GRADUATION (15-patterns #11 at the codec grade,
    `Kit.Codec.toIsoOfExact` — the registry's `registryIso` precedent):
    the unwrap codec is a TRUE `Iso` — the decode is TOTAL (the
    second component is `Unit`, pure structure, nothing to refuse) +
    `unwrapCodec_exact` — the raw line tuples ≅ the clean row list,
    both round trips. -/
def unwrapIso : Kit.Iso (List ((String × String) × Unit)) (List (String × String)) :=
  unwrapCodec.toIsoOfExact (fun raw => ⟨raw.map (·.1), rfl⟩) unwrapCodec_exact

open Grammar in
/-- The file grammar: the rep of lines under the unwrap rel (the
    CLEAN row list is the payload; the line tuples are pure text
    structure). -/
def fileGrammar : Grammar (List (String × String)) :=
  .rel unwrapCodec (fun _ => true) (fun _ _ _ => rfl)
    (fun raw r h => unwrapCodec_exact raw r h)
    "rows" [] (.rep lineG)

open Grammar in
/-- The CLI format: `--key=value` (the dash prefix + the row; the
    payload pairs the dashes' units with the pair — the accessor is
    `.2.2`). -/
def cliG : Grammar ((Unit × Unit) × (String × String)) :=
  .seq (.seq (.atom (constCharLex '-' ())) (.atom (constCharLex '-' ()))) rowG

/-! ## the value-side gate + the certificates -/

/-- The row's write-side gate: THE grammar's own valueOk fold (the
    one gate — never a parallel table; reduces to the key's ident
    discipline + the value's). -/
def rowOk (p : String × String) : Bool := Grammar.valueOk rowG p

/-- The file's write-side gate: the file grammar's valueOk fold (the
    rows' gate, at the format's ONE definition). -/
def rowsOk (rows : List (String × String)) : Bool :=
  Grammar.valueOk fileGrammar rows

/-- THE certificate: the file grammar's predictive-parsing discharge
    (the wf rows hand-check green: the rep's body is non-nullable —
    the key atom consumes; the junction rows vacuous — every line's
    last munch is the LF atom's `none`). -/
theorem fileCert : Grammar.Predictive fileGrammar :=
  Grammar.wfCheck_sound fileGrammar (by decide)

/-- The row grammar's certificate. -/
theorem rowCert : Grammar.Predictive rowG :=
  Grammar.wfCheck_sound rowG (by decide)

/-- The CLI grammar's certificate. -/
theorem cliCert : Grammar.Predictive cliG :=
  Grammar.wfCheck_sound cliG (by decide)

/-- The fix-free fold discharges at all three (no `fix`/`self`
    anywhere — the flat formats' face). -/
theorem fileFixFree : Grammar.FixFree fileGrammar :=
  ⟨⟨trivial, ⟨trivial, trivial⟩⟩, trivial⟩
theorem rowFixFree : Grammar.FixFree rowG := ⟨trivial, ⟨trivial, trivial⟩⟩

/-- The CLI grammar's fix-free fold (the dashes' seq + the row). -/
theorem cliFixFree : Grammar.FixFree cliG :=
  ⟨⟨trivial, trivial⟩, ⟨trivial, ⟨trivial, trivial⟩⟩⟩

/-- Law 1 at the CLI grammar (the flag round trip). -/
theorem cliRunPrint (p : (Unit × Unit) × (String × String))
    (hval : Grammar.valueOk cliG p = true) :
    Grammar.run cliG (Grammar.print cliG p) = .ok p :=
  Grammar.run_print_fixFree cliG cliFixFree cliCert p hval

/-! ## the law instantiations -/

/-- Law 1 at the file grammar: a gate-passing row list prints to its
    canonical bytes and parses back EXACTLY (the run face). -/
theorem fileRunPrint (rows : List (String × String))
    (hval : rowsOk rows = true) :
    Grammar.run fileGrammar (Grammar.print fileGrammar rows) = .ok rows :=
  Grammar.run_print_fixFree fileGrammar fileFixFree fileCert rows hval

/-- Law 1 at the row grammar (the env row's face). -/
theorem rowRunPrint (p : String × String) (hval : rowOk p = true) :
    Grammar.run rowG (Grammar.print rowG p) = .ok p :=
  Grammar.run_print_fixFree rowG rowFixFree rowCert p hval

/-! ## the concrete pins -/

/-- The canonical print of a two-row file (no padding spaces — the
    canonical form is the print's job). -/
theorem filePrint_two :
    Grammar.print fileGrammar [("a", "1"), ("b", "hi")] = "a=1\nb=hi\n" := rfl

/-- The run round trip at the concrete text. -/
theorem fileRun_two :
    Grammar.run fileGrammar "a=1\nb=hi\n" = .ok [("a", "1"), ("b", "hi")] := by
  have h := fileRunPrint [("a", "1"), ("b", "hi")] (by decide)
  rw [filePrint_two] at h
  exact h

/-- The env row's round trip at a concrete env spelling. -/
theorem rowRun_env :
    Grammar.run rowG "GATES_ALL_JOBS=8" = .ok ("GATES_ALL_JOBS", "8") := by
  have h := rowRunPrint ("GATES_ALL_JOBS", "8") (by decide)
  exact h

/-- The CLI flag's parse (the payload's accessor is `.2.2`). -/
theorem cliRun_flag :
    Grammar.run cliG "--all_jobs=8" = .ok (((), ()), ("all_jobs", "8")) :=
  cliRunPrint (((), ()), ("all_jobs", "8")) (by decide)

/-- The value's charset keeps spaces (the row stays one line) — the
    parse is round-trip exact through them. -/
theorem fileRun_spaces :
    Grammar.run fileGrammar "greeting=hello world\n" = .ok [("greeting", "hello world")] := by
  have h := fileRunPrint [("greeting", "hello world")] (by decide)
  exact h

/-! ## the negative controls (the certificate's teeth) -/

/-- SABOTAGE 1 (WF-ALT-1): colliding alt heads — two key arms (the
    `GrammarSlice` sabotage face at this format's lexemes). -/
def sabAltHeads : Grammar String := .alt (.atom keyAtom) (.atom keyAtom)

theorem sabAltHeads_row :
    Grammar.wfProblems [] sabAltHeads = ["WF-ALT-1 at []"] := by decide

/-- The write-side gate's teeth: an empty value refuses (the scan's
    progress honesty), an empty key refuses, a key with a non-key
    char refuses — decided, never assumed. -/
theorem rowOk_emptyValue : rowOk ("k", "") = false := by decide

theorem rowOk_emptyKey : rowOk ("", "v") = false := by decide

theorem rowOk_spaceKey : rowOk ("k v", "1") = false := by decide

theorem rowOk_good : rowOk ("k", "1") = true := by decide

/-! ## the axiom pins (the axiom gate's replay face; the GrammarSlice
    note 4: these live HERE — the module barrier keeps them out of
    TextKitTests.Axioms) -/

#print axioms fileCert
#print axioms cliCert
#print axioms fileRunPrint
#print axioms cliRunPrint
#print axioms fileRun_two

end TextKit.ConfigFormat

