/-
# Kit.Cli — the ONE exe-driver discipline (design-wave-30 C7, N6)

Every exe driver in the tree shares one shape: an argv parse → a
subcommand dispatch → a verdict/exit mapping, plus the shared flags
(`--package` shard, `--write` baseline, `--accept-drift` re-baseline).
Before this module each driver hand-rolled its own copy (gates rode the
external lean4-cli package, inspector a bare `match args`, lintkit its
own prefix walk), so the failure faces drifted: an unknown token was a
bare usage string here, a library message there — never the ONE
diagnostic envelope's curated did-you-mean.

This module is the ONE driver: the subcommand TABLE (name + summary +
run fn), the shared-flag parser (the unknown flag fails through the
closed-world `Kit.Diag.closedWorld` constructor — the did-you-mean
cannot be skipped), the help text GENERATED from the table (the table
is the one source — help cannot drift from it), and the exit-code
discipline (`Verdict`'s closed three → `UInt32`, ONE mapping).

The E-codes are the CX family, registry-allocated (`notes/
code-registry.txt`; `gates code-registry-check` replays the allocation
and its coverage tooth refuses hand-strung spellings).

Core-only (no mathlib/Batteries — the cone rule). Five questions
(notes/v3/01-core.md): root DATA — the dispatch table is the closed
subcommand universe (the closed-world error discipline over it);
carrier grade first-order over String/List; spine reading as-data (the
table drives both dispatch and help; nothing prints but the help and
the curated Diags); ladder rung: n/a (no proofs over IO); gate row:
none — the exes are how the rows run, not rows. Tests: KitTests.Cli
(the did-you-mean teeth + the help-from-table pin + the verdict map).
-/

module

public import Kit.Diag

@[expose] public section

namespace Kit.Cli

/-! ## the E-codes (the CX family — registry-allocated, 05 §4) -/

/-- an unknown subcommand (the closed world = the table's names). -/
def eCX0001 : Kit.ECode := ⟨"CX0001"⟩

/-- an unknown flag (the closed world = the command's flag spellings). -/
def eCX0002 : Kit.ECode := ⟨"CX0002"⟩

/-! ## the exit-code discipline -/

/-- The verdict's closed universe → exit codes. ONE mapping: clean = 0,
a finding (the loud miss, the review failure) = 1, the unremedied
verdict (the breaking gate's third way — the evidence is named, the run
still fails) = 2. A driver never hand-codes a number. -/
inductive Verdict where
  | ok         -- exit 0: clean / answered / report rendered
  | finding    -- exit 1: a finding, a loud miss, a curated refusal
  | unremedied -- exit 2: the three-way verdict's loud warning

/-- THE mapping (the discipline's one copy). -/
def Verdict.exit : Verdict → UInt32
  | .ok => 0
  | .finding => 1
  | .unremedied => 2

/-! ## the shared flags -/

/-- The shared flag surface every driver's handlers parse through:
the `--package=<dir>` shard, the `--write` baseline, the
`--accept-drift` re-baseline. Extra (driver-local) flags ride `extra`
as `--name` / `--name=value` rows (`has`/`val`); positionals land in
`rest` (the modules of lintkit's explicit mode). -/
structure Flags where
  /-- The shard: ONE package (`--package=<dir>`). -/
  pkg : Option String := none
  /-- The write-baseline mode. -/
  write : Bool := false
  /-- The deliberate re-baseline (the loud discipline). -/
  acceptDrift : Bool := false
  /-- The driver-local flags, name ↦ value (`""` for a bare boolean). -/
  extra : List (String × String) := []
  /-- The positional arguments (non-flag tokens). -/
  rest : List String := []

/-- A bare boolean extra flag's presence. -/
def Flags.has (f : Flags) (name : String) : Bool := f.extra.any (fun r => r.1 == name)

/-- An extra flag's value (bare flags carry `""`). -/
def Flags.val (f : Flags) (name : String) : Option String :=
  (f.extra.filter (fun r => r.1 == name)).head?.map (·.2)

/-- ALL of a repeatable extra flag's values, in order. -/
def Flags.all (f : Flags) (name : String) : List String :=
  (f.extra.filter (fun r => r.1 == name)).map (·.2)

/-- The shared spellings — the flag closed world's constant half. -/
def sharedFlags : List String := ["--package", "--write", "--accept-drift"]

/-- Match one driver-local flag token: `--name` (bare) or
`--name=value` (value = everything after the FIRST `=`). -/
def extraFlag? (a : String) (extra : List String) : Option (String × Option String) :=
  match (extra.map (fun n => ("--" ++ n, n))).find? fun (spelling, _) => a == spelling with
  | some (_, n) => some (n, none)
  | none =>
      match (extra.map (fun n => ("--" ++ n ++ "=", n))).find? fun (pfx, _) => a.startsWith pfx with
      | some (pfx, n) => some (n, some ((a.drop pfx.length).toString))
      | none => none

/-- The ONE flag parse: shared + driver-local flags, positionals in
`rest`; an unrecognized `--…` token REFUSES through the closed-world
constructor (the did-you-mean over the command's full flag spelling
set — the closed-world discipline, not a usage-string shrug). -/
def parseFlags (extra : List String) (args : List String) :
    Except Kit.Diag Flags :=
  let valid := sharedFlags ++ extra.map (fun n => "--" ++ n)
  let rec go (f : Flags) : List String → Except Kit.Diag Flags
    | [] => .ok f
    | a :: as =>
        if a == "--write" then go { f with write := true } as
        else if a == "--accept-drift" then go { f with acceptDrift := true } as
        else if a == "--package" then
          match as with
          | v :: rest => go { f with pkg := some v } rest
          | [] => .error (Kit.Diag.closedWorld eCX0002
              "the --package flag needs a value" .error "--package" valid)
        else if let some v := a.dropPrefix? "--package=" then
          go { f with pkg := some v.toString } as
        else if let some (n, v) := extraFlag? a extra then
          go { f with extra := f.extra ++ [(n, v.getD "")] } as
        else if a.startsWith "--" then
          .error (Kit.Diag.closedWorld eCX0002 "unknown flag" .error a valid)
        else go { f with rest := f.rest ++ [a] } as
  go {} args

/-! ## the subcommand table -/

/-- One subcommand row: the name (multi-word allowed, space-separated —
`ledger backward`'s shape), the summary (the help's ONLY source), the
run fn over the row's remaining arguments. -/
structure Sub where
  /-- The spelling the user types (the dispatch key). -/
  name : String
  /-- The one-line summary; the help text is GENERATED from it. -/
  summary : String
  /-- The handler over the remaining argv tokens. -/
  run : List String → IO UInt32

/-- The row's tokens (multi-word names dispatch on the token list). -/
def Sub.tokens (s : Sub) : List String := s.name.splitOn (sep := " ")

/-- The longest row whose tokens are a prefix of `toks` (longest first,
so `ledger backward` wins over `ledger`). -/
def longestMatch (subs : List Sub) (toks : List String) : Option (Sub × Nat) :=
  subs.foldl (fun best s =>
    let ts := s.tokens
    if ts.isPrefixOf toks then
      match best with
      | some (_, n) => if ts.length > n then some (s, ts.length) else best
      | none => some (s, ts.length)
    else best) none

/-- The help text, GENERATED from the table (the table is the one
source — the help cannot drift from the dispatch). -/
def help (prog : String) (about : String) (subs : List Sub) : String :=
  let pad := (subs.foldl (fun n s => max n s.name.length) 0) + 2
  "usage: lake exe " ++ prog ++ " <subcommand> [flags...]"
    ++ (if about.isEmpty then "" else "\n\n" ++ about)
    ++ "\n\nsubcommands:\n"
    ++ String.intercalate "\n" (subs.map fun s =>
        "  " ++ s.name ++ String.ofList (List.replicate (pad - s.name.length) ' ')
          ++ s.summary)
    ++ "\n"

/-- THE driver: the no-arg / `--help` faces print the GENERATED help;
a table hit hands the row its remaining args; a miss fails through the
closed-world constructor (the did-you-mean over the table's names —
the teeth). `default` is the bare-invocation face (`none` = the help;
inspector's sweep passes its report mode). -/
def run (prog : String) (about : String) (subs : List Sub)
    (default : Option (IO UInt32)) (args : List String) : IO UInt32 := do
  if args == [] then
    match default with
    | some act => act
    | none => IO.println (help prog about subs); return Verdict.ok.exit
  else if args == ["--help"] || args == ["-h"] || args == ["help"] then
    IO.println (help prog about subs)
    return Verdict.ok.exit
  else
    match longestMatch subs args with
    | some (s, n) => s.run (args.drop n)
    | none =>
        IO.eprintln (Kit.Diag.toString (Kit.Diag.closedWorld eCX0001
          (s!"unknown subcommand — the full table: lake exe {prog} --help")
          .error (args.headD "") (subs.map (·.name))))
        return Verdict.finding.exit

end Kit.Cli

end -- @[expose] public section