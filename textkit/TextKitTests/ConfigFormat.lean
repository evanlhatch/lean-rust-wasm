/-
# TextKitTests.ConfigFormat — the config sources' format suite

The module under test is `TextKit.ConfigFormat` (the config face's
source formats — C4). The format's laws are INSTANCES there (the
GrammarSlice route); this suite pins the instances' behavior + the
mandatory negative controls.
-/

import TestingKit.Harness
import TextKit.ConfigFormat

namespace TextKitTests.ConfigFormat

open TextKit TextKit.ConfigFormat TestingKit

/-- The parse verdict's structural equality (ParseError carries no
    BEq — the pins compare the OK face by match, never an instance). -/
def parsesTo {A : Type} [BEq A] (g : Grammar A) (text : String) (want : A) : Bool :=
  match Grammar.run g text with
  | .ok x => x == want
  | .error _ => false

def configFormatSpec : Spec :=
  Spec.ofList "the config sources' formats: rows round-trip, the certificates, the gate teeth"
    (fun _ =>
      assert ((
      -- the file's round trip (law 1's run face, at the pins)
        parsesTo fileGrammar "a=1\nb=hi\n" [("a", "1"), ("b", "hi")]
        && parsesTo fileGrammar "greeting=hello world\n" [("greeting", "hello world")]
      -- the env row's round trip (the SAME row grammar at one row)
        && parsesTo rowG "GATES_ALL_JOBS=8" ("GATES_ALL_JOBS", "8")
      -- the canonical print (no padding spaces)
        && (Grammar.print fileGrammar [("a", "1"), ("b", "hi")] == "a=1\nb=hi\n")
      -- the CLI flag: the dash prefix + the row
        && parsesTo cliG "--all_jobs=8" (((), ()), ("all_jobs", "8"))
      ))
      "the config formats drifted")
    [ ("an empty value parses (the progress lie)",
        fun _ =>
          assert (parsesTo rowG "k=" ("k", ""))
          "control fired: the value's maximal run must be NONEMPTY — the \
            progress honesty")
    , ("a space-key row parses (the charset lie)",
        fun _ =>
          assert (parsesTo rowG "k v=1" ("k v", "1"))
          "control fired: the key charset is alphanumeric + underscore — \
            `k v` is not a key")
    ]
    4 42

end TextKitTests.ConfigFormat
