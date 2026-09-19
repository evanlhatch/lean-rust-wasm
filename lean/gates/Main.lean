/-
# Gates.Main — the `gates` exe: subcommand dispatch (Cli)

    lake exe gates gen-check        — the stripped byte-tie
    lake exe gates axioms [--write] [--package X] — the axiom report
                                      (sharded: one package's env per
                                      process — the lean-axioms recipe
                                      loops this; no --package = the
                                      monolithic whole-file mode)
    lake exe gates manifest-check   — lakefile ↔ manifest drift
    lake exe gates coverage [--write] [--strict] — the coverage matrix
    lake exe gates kernel-check     — the lean4lean double-check
    lake exe gates native-policy    — the native_decide grandfathering gate
    lake exe gates all [--full]     — 1–5 (+ kernel-check) in one run;
                                      --full also shells out to the
                                      Rust/wasm lane (just wasm-compile,
                                      just test) — subprocess is THEIR
                                      lane, the Lean gates stay in-process

Recipes run the exe from THIS dir (`cd lean/gates && lake exe gates …`)
— the same depth as lean/schema-lang, so the emitters' `../..`-relative
output paths and the `../<pkg>` package paths resolve unchanged.

Cli parses argv (hyphenated subcommand names via the string form of
`literalIdent`). Handlers are `unsafe` (registry replay is
`importModulesReplayed`) — the SchemaMain/LintMain pattern.
-/
import Cli
import Gates

open Cli

unsafe def runGenCheck (_p : Parsed) : IO UInt32 := Gates.GenCheck.run

unsafe def runAxioms (p : Parsed) : IO UInt32 :=
  Gates.Axioms.run (p.hasFlag "write") (p.flag? "package" |>.map (·.as! String))

unsafe def runManifestCheck (_p : Parsed) : IO UInt32 := Gates.Manifest.run

unsafe def runCoverage (p : Parsed) : IO UInt32 :=
  Gates.Coverage.run (p.hasFlag "write") (p.hasFlag "strict")

unsafe def runKernelCheck (p : Parsed) : IO UInt32 :=
  Gates.KernelCheck.run (p.flag? "package" |>.map (·.as! String))

unsafe def runNativePolicy (p : Parsed) : IO UInt32 := Gates.NativePolicy.run (p.flag? "package" |>.map (·.as! String))

/-- `just <recipe>` from the repo root (the exe runs at the root — the
    single-lake layout). -/
def shellJust (args : List String) : IO UInt32 := do
  let out ← IO.Process.output
    { cmd := "just", args := args.toArray
    , cwd := some ("." : System.FilePath) }
  IO.print out.stdout
  IO.eprint out.stderr
  return out.exitCode

unsafe def runAll (p : Parsed) : IO UInt32 := do
  for (name, step) in
    [ ("gen-check",     Gates.GenCheck.run)
    , ("axioms",        Gates.Axioms.run false none)
    , ("manifest-check", Gates.Manifest.run)
    , ("coverage",      Gates.Coverage.run false false)
    , ("native-policy", Gates.NativePolicy.run none) ] do
    IO.println s!"══ gates all: {name} ══"
    let code ← step
    if code != 0 then
      IO.eprintln s!"gates all: {name} FAILED"
      return code
  if p.hasFlag "full" then
    -- the Rust/wasm world stays subprocess-driven (just's lane too)
    for recipe in [["wasm-compile"], ["test"]] do
      IO.println s!"══ gates all --full: just {String.intercalate " " recipe} ══"
      let code ← shellJust recipe
      if code != 0 then
        IO.eprintln s!"gates all: just {String.intercalate " " recipe} FAILED"
        return code
  IO.println "gates all: clean"
  return 0

unsafe def genCheckCmd : Cmd := `[Cli|
  "gen-check" VIA runGenCheck; ["0.1.0"]
  "The byte-tie, stripped: regenerate every artifact in-process from the \
   replayed registries and compare body bytes + the embedded content hash \
   against the committed files (the header's timestamp/spec-sha are exempt \
   by the byte-tie contract). Closes the 'just gen dirties the tree' \
   weakness of forge gen --check. Never writes."
]

unsafe def axiomsCmd : Cmd := `[Cli|
  "axioms" VIA runAxioms; ["0.1.0"]
  "The global axiom report: per gated package, every declaration's kernel \
   axiom cone (CollectAxioms) checked against LintKit's allowlist \
   (consumed, not re-encoded); diffs against notes/axiom-report.md."

  FLAGS:
    write;            "Update the committed notes/axiom-report.md instead of diffing it."
    package : String; "Check ONE gated package (its Gates.Packages dir) — one \
      environment in this process, the sharded mode the lean-axioms recipe \
      loops over (the monolithic all-envs run peaks at ~26.5GB RSS). With \
      --write, rewrites only that package's `## <dir>` section of \
      notes/axiom-report.md in place; the check diffs only that section."
]

unsafe def manifestCheckCmd : Cmd := `[Cli|
  "manifest-check" VIA runManifestCheck; ["0.1.0"]
  "Every lean/*/lake-manifest.json agrees with its lakefile.toml \
   (require↔entry, rev pins, checkout HEADs). Structural + offline — see \
   Gates/Manifest.lean's header for why this is not `lake update`-based."
]

unsafe def coverageCmd : Cmd := `[Cli|
  "coverage" VIA runCoverage; ["0.1.0"]
  "The coverage matrix as data: Ty ctors x registered emitters \
   (probe-differential) x the oracle's replay surface. Diffs against \
   notes/coverage-matrix.md; fully-quiet ctors print as findings."

  FLAGS:
    write;  "Update the committed notes/coverage-matrix.md instead of diffing it."
    strict; "Fail on fully-quiet ctors (unexercised members of the closed universe)."
]

unsafe def kernelCheckCmd : Cmd := `[Cli|
  "kernel-check" VIA runKernelCheck; ["0.1.0"]
  "The lean4lean double-check: replay every gated package's modules \
   through the pure-Lean kernel (per-package `lake env lean4lean`, \
   non-fresh whole-path mode). Caveats in Gates/KernelCheck.lean's \
   header: no reduceBool (the 3 disclosed native_decide uses are outside \
   its checking), shared lineage with the C++ kernel = double-check, \
   not independence."

  FLAGS:
    package : String; "Check ONE gated package — one lean4lean env in this \
      process (the sharded mode the kernel-check recipe loops; the full \
      sweep in one process exceeds 30 minutes on this box)."
]

unsafe def nativePolicyCmd : Cmd := `[Cli|
  "native-policy" VIA runNativePolicy; ["0.1.0"]
  "The native_decide grandfathering gate (W9.7, design-guest-verified.md \
   §6.3): every decl in every gated package gets its CollectAxioms cone; \
   a `_native.native_decide.` axiom outside the grandfathered set \
   (Gates.NativePolicy.grandfatheredNative — edgepython's Parity module, \
   schema-lang's Emit/Circuit) FAILS. lean4lean cannot re-check \
   reduceBool, so a decl on that trust base is outside the independent \
   kernel's checking. Stale grandfather entries fail too."

  FLAGS:
    package : String; "Check ONE gated package — one environment in this \
      process (the sharded mode the native-policy recipe loops; the \
      full sweep in one process accumulates every package's env and \
      OOMs). The stale-entry check is scoped to the selected package."
]

unsafe def allCmd : Cmd := `[Cli|
  "all" VIA runAll; ["0.1.0"]
  "gen-check + axioms + manifest-check + coverage + native-policy in one run."

  FLAGS:
    full; "Also shell out to the Rust/wasm lane (just wasm-compile, just test)."
]

unsafe def gatesCmd : Cmd := `[Cli|
  "gates" NOOP; ["0.1.0"]
  "The Lean-side gates driver (the pipeline-as-machine row)."

  SUBCOMMANDS: genCheckCmd; axiomsCmd; manifestCheckCmd; coverageCmd; kernelCheckCmd; nativePolicyCmd; allCmd
]

unsafe def main (args : List String) : IO UInt32 :=
  gatesCmd.validate args
