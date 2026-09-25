/-
# Kit.Duel — the duel/vector harness seed (03 §3's differential level)

HOME DECISION — kit, not TestingKit: the duel is the EVIDENCE shape (03
§3: the differential/property row = "tested executions agree"; 04 §6:
a duel verdict is tested agreement, NEVER a theorem), and its
consumers are the LANES — the codec differential, the wasm execution
duel, the substrait round-trips, the vortex duels, the snapshot
Lean↔Rust — which import Kit (SchemaCore, WasmCore, the crates'
generated surfaces). A TestingKit home would drag the Lean test harness
into production (guest-relevant) lane closures. TestingKit-flavored it
stays in two named debts only: the seeded generator rides TestingKit's
LCG (pattern #14 — the ONE recurrence, imported, never hand-copied)
and the verdicts are ctors, never strings (04 §6).

THE VECTOR-SET CONVENTION: ONE DIRECTORY per duel; the vector files'
bytes plus a committed TEXT manifest naming the generator and the
expectations. The manifest rides the emitter spine (15-patterns #10)
— the text lane for the manifest, the binary lane (Kit.Emit's
`BinaryFile`) for the vectors; the duel's one-writer discipline is in
the type (the vector paths' nodup, the emitter's declared outputs).

THE CONSUMER-SIDE CONTRACT (the Rust/wasm reader's shape): read the
manifest, skip the 2-line GENERATED header, skip the `generator`
provenance row, split each row on the tab. A `decode <note>` row names a vector that MUST decode — the
decoded value re-encodes byte-identically (the differential's BOTH
directions, as crates/schema-generated/tests/differential.rs does
today over its inline arrays). A `refuse` row names a vector that
MUST be refused — a typed error, never a panic, never a silent
misparse. The vector bytes are LCG-seeded (the generator module pins
its seed; the manifest names the module) — same seed, byte-identical
replay.

EVIDENCE LEVEL (03 §3): EVERYTHING here is "tested agreement" — the
duel is a regression surface, never an authority. `agree` rows are
regressions; `diverge` rows carry the distinguishing witness (04 §8:
never a bare "behavior changed"); `refused` rows name the typed
refusal — an EXPECTED refusal is the negative control passing, an
unexpected one is the witness.

The five questions (notes/v3/01-core.md):
- root: Crossing — the duel couples two presentations through shared
  vectors + a shared verdict vocabulary.
- carrier grade: the verdict ctors + the vector paths' nodup IN THE
  TYPE (a colliding vector set fails to elaborate).
- spine reading: the evidence stage — vector sets are artifacts
  emitted through the ONE spine (the manifest's text lane + the
  vectors' binary lane); duels READ them, never re-encode.
- ladder rung: rung 1 — pure data + total folds; the agreement is
  TESTED, not proved (named here, not hidden).
- gate row: none yet — the duel rows land with the first consumer's
  gate (the differential's migration is the named follow-up); the
  KitTests pins are the standing evidence.
-/

import Kit.Emit
import TestingKit.Lcg

namespace Kit.Duel

open Kit.Emit

/-! ## The verdict vocabulary -/

/-- The divergence witness: which vector, what each side observed.
    The observations are RENDERED — the duel's sides are heterogeneous
    (a Lean value, a Rust decode, a wasm execution); the witness is
    the minimal evidence a `diverge` verdict must name. -/
structure Witness where
  /-- Which vector (the duel-relative name). `at` is a Lean keyword —
      the same trap Emit's GenMeta note honors; `loc` is the field. -/
  loc : String
  lhs : String
  rhs : String
deriving DecidableEq, Repr

/-- The duel verdict vocabulary (ctors, never strings — 04 §6).
    `agree` is TESTED agreement (a regression row), never a theorem;
    `diverge` carries the distinguishing witness; `refused` names a
    side's typed refusal (expected or not — the expectation decides). -/
inductive Verdict where
  | agree
  | diverge (witness : Witness)
  | refused (why : String)
deriving DecidableEq, Repr

/-- Render a verdict as a line — for humans; consumers pattern-match
    the ctors (TestingKit.Harness's discipline). -/
def Verdict.render : Verdict → String
  | .agree => "agree"
  | .diverge w => s!"diverge at {w.loc}: lhs {w.lhs} vs rhs {w.rhs}"
  | .refused why => s!"refused: {why}"

/-- Fold a duel's row verdicts into the duel's verdict: all-agree is
    agree; the FIRST non-agree row wins — its witness/refusal IS the
    failure evidence (the minimal-counterexample discipline). -/
def Verdict.foldRows : List Verdict → Verdict
  | [] => .agree
  | .agree :: rest => foldRows rest
  | v :: _ => v

/-! ## The vector-set convention -/

/-- The consumer-side expectation per vector (closed — a new duel kind
    extends this deliberately, the patterns-catalog rule; the wasm
    execution duel's extension is the `run`/`trap` pair). -/
inductive Expect where
  /-- MUST decode; the note pins the decoded value's identity for the
      consumer's decode-then-compare (the differential's value pin). -/
  | decode (valueNote : String)
  /-- MUST be refused — a typed refusal, never a panic, never a
      silent misparse (the tamper-vector control). -/
  | refuse
  /-- MUST execute to completion and return the PINNED result values
      (the wasm execution duel: the Lean executor's computed output,
      rendered in the duel's value vocabulary — `i64:42` per value,
      comma-joined for several). -/
  | run (result : String)
  /-- MUST trap — the typed wasm trap, in EVERY engine (an expected
      trap is the trap lane's agreement row; an unexpected one is the
      divergence witness). -/
  | trap
deriving BEq, DecidableEq, Repr

/-- Render an expectation as the manifest's second column. -/
def Expect.render : Expect → String
  | .decode note => "decode " ++ note
  | .refuse => "refuse"
  | .run r => "run " ++ r
  | .trap => "trap"

/-- One duel's vector set: ONE DIRECTORY per duel (the committed
    convention); the vectors are the binary lane's artifacts
    (`BinaryFile`), the manifest the text lane's. The vector paths'
    nodup is IN THE TYPE — a colliding vector set fails to elaborate
    (the one-writer discipline, duel-shaped). -/
structure VectorSet where
  /-- The duel's directory (repo-root-relative — ONE directory per
      duel: the manifest + the vectors live there). -/
  dir : String
  /-- The duel's name (the emitter's identity + the manifest's
      provenance row's neighbor). -/
  name : String
  /-- The generator: the Lean module whose seeded fold produced the
      bytes (the manifest's provenance row; the module pins its seed). -/
  generator : String
  /-- The vectors: repo-root-relative path + bytes. -/
  vectors : List BinaryFile
  /-- The expectation per vector path (the consumer contract's data). -/
  expects : List (String × Expect)
  /-- The manifest's header comment style: `.hash` when the manifest
      sits beside other `#`-header artifacts, `.doubleSlash` when it
      sits next to Rust code (the artifact-headers gate's shape
      contract reads THIS field through the emitter — the DRY sweep's
      consolidation: the style is the only behavioral parameter the
      duel lanes differ in). Defaults to the seed's `.hash`. -/
  style : CommentStyle := .hash
  /-- THE one-writer discipline: two vectors cannot share one path. -/
  vectors_nodup : (vectors.map (·.path)).Nodup := by decide
  /-- Two expectations cannot name one vector (contradictory rows). -/
  expects_nodup : (expects.map (·.1)).Nodup := by decide

/-- The manifest ROWS (the ONE format, stated once): the generator
    provenance row, then one row per expectation —
    `<path>\t<expectation>`. `manifestBody` is the VectorSet face of
    this; the wasm execution duel rides THIS entry point directly (its
    expectations are the executor's computed `Except` outputs — the
    VectorSet literal's proof fields do not apply to a computed list,
    so the duel's one-writer discipline rides the emitter's declared
    `binaryOutputs`/`outputs` instead). -/
def manifestRows (generator : String) (expects : List (String × Expect)) : String :=
  "generator\t" ++ generator ++ "\n" ++
  String.intercalate "\n"
    (expects.map fun (p, x) => p ++ "\t" ++ x.render) ++ "\n"

/-- The manifest body (the driver prepends the 2-line GENERATED
    header): the generator row, then one row per expectation —
    `<path>\t<expectation>`. The consumer contract is the module
    header's; these rows are its data. -/
def manifestBody (vs : VectorSet) : String :=
  manifestRows vs.generator vs.expects

/-- The shape check: every expectation names a vector in the set — a
    manifest row over an absent vector is a generator bug, and the
    check makes it a testable verdict. -/
def expectsCovered (vs : VectorSet) : Bool :=
  let paths := vs.vectors.map (·.path)
  vs.expects.all fun (p, _) => paths.contains p

/-! ## The vector-set emitter (through the ONE spine) -/

/-- The vector-set emitter, lane-parameterized (the DRY sweep's ONE
    body — the duel lanes were hand-rolling exactly this shape): the
    manifest rides the TEXT lane, the vectors the BINARY lane; the
    per-lane differences are exactly the spec type (the fold's input),
    the specSource provenance, the header style (the VectorSet's OWN
    field), and the optional emission law. The one-writer discipline
    rides the VectorSet's proof fields, never a second proof. -/
def emitterWith {Spec : Type} (vs : VectorSet) (specSource : String)
    (law : Option (Spec → Prop) := none) : Emitter Spec where
  name := s!"duel:{vs.name}"
  style := vs.style
  specSource := specSource
  outputs := [vs.dir ++ "/manifest.txt"]
  outputs_nodup := by simp
  binaryOutputs := vs.vectors.map (·.path)
  binaryOutputs_nodup := vs.vectors_nodup
  run _ := [{ path := vs.dir ++ "/manifest.txt", contents := manifestBody vs }]
  runBinary := some fun _ => vs.vectors
  law := law

/-- The vector-set emitter (the seed's pinned-constant face: spec
    `Unit`, the generator as the provenance — KitTests' driver pin). -/
def emitter (vs : VectorSet) : Emitter Unit :=
  emitterWith vs vs.generator

/-! ## The Rust consumers' shared preamble (the ONE copy) -/

/-- The Rust duel consumers' shared preamble — `const CRATE_PREFIX`
    (the generated crate's repo-root prefix; byte-identical in every
    Rust-side consumer, so it lives HERE once — the DRY sweep's string
    consolidation; gen-check's byte-tie proves the splices identical). -/
def rustCratePrefix : String :=
  "/// The generated crate's repo-root prefix (the manifest's rows are
/// repo-root-relative; the test binary's cwd is the crate root).
const CRATE_PREFIX: &str = \"crates/schema-generated/\";

"

/-- The Rust duel consumers' shared preamble — `fn crate_path` (the
    row path's re-basing; byte-identical in every consumer). -/
def rustCratePath : String :=
  "/// Re-base a manifest row's repo-root-relative path to the crate root.
fn crate_path(row_path: &str) -> &str {
    match row_path.strip_prefix(CRATE_PREFIX) {
        Some(p) => p,
        None => row_path,
    }
}

"

/-- The Rust duel consumers' shared `fn manifest_rows` (Kit.Duel's
    consumer contract: skip the 2-line GENERATED header + the
    `generator` provenance row, split each row on the tab — ONE parse
    walk). The row SHAPE is the consumer's: `rowTy` names the Vec's
    element type, `rowExpr` the produced row — the only two
    byte-differences between the lanes' copies. -/
def rustManifestRows (rowTy rowExpr : String) : String :=
  "/// Kit.Duel's consumer contract: skip the 2-line GENERATED header and
/// the `generator` provenance row, split each row on the tab.
fn manifest_rows() -> Vec<" ++ rowTy ++ "> {
    MANIFEST
        .lines()
        .skip(2)
        .filter(|line| !line.is_empty() && !line.starts_with(\"generator\\t\"))
        .map(|line| {
            let mut parts = line.split('\\t');
            let path = parts.next().expect(\"manifest row: path\").to_string();
            let expect = parts.next().expect(\"manifest row: expectation\");
            " ++ rowExpr ++ "
        })
        .collect()
}

"

/-! ## The Lean-side vector generator (the seeded discipline) -/

/-- Draw `n` LCG bytes from the tape (pattern #14: same seed, same
    bytes — a failing vector replays byte-identically from its seed).
    The generator module pins the seed; the manifest names the module. -/
def genBytes (t : TestingKit.Tape) : Nat → ByteArray × TestingKit.Tape
  | 0 => (ByteArray.empty, t)
  | n + 1 =>
    let (b, t1) := t.byte
    let (rest, t2) := genBytes t1 n
    (rest.push b.toNat.toUInt8, t2)

end Kit.Duel
