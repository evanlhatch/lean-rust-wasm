/-
# TestingKit.Golden — the golden/byte-tie helper (the stripped compare)

Owned by: the TestingKit agent (the mandate tree, `testingkit/`).
Driving decision: notes/v3/15-patterns.md #10 (the emitter spine — the
byte-tie is the emitter's correspondence law; the artifact header carries
the content hash; the tie strips only the volatile lines) +
notes/v3/09-gates-ops.md's discipline: the golden is COMMITTED, a
mismatch is drift, never a test you skip.

Mined from: legacy/lean/TestingKit/TestingKit/Golden.lean (the committed-golden
discipline). Fresh here: the compare is PURE (body bytes in, CheckResult
out — no file IO; drivers own the FS) and the volatile-header exemption +
content hash are explicit data, so the exemption itself is testable.

The compare's law: two artifacts TIE iff their bodies (the non-volatile
lines) are byte-equal; the content hash folds the body's bytes through
the LCG (the tape reader doubles as the digest) and rides the failure
message as the diff anchor.

The five questions (notes/v3/01-core.md):
- root: Crossing — the artifact-vs-golden compare (the byte-tie's
pure core).
- carrier grade: the tie law — body byte-equality with the volatile
exemption explicit + the LCG hash as the diff anchor (a Codec-shaped
equality over bodies).
- spine reading: the artifact stage's check face; drivers own the FS.
- ladder rung: rung 1 — pure total functions.
- gate row: the discipline behind gen-check (the compare itself is
pinned in TestingKitTests).
-/

module

public import TestingKit.Lcg
public import TestingKit.Spec

@[expose] public section

namespace TestingKit.Golden

/-- The volatile header prefixes exempt from the byte-tie — stamps and
    run-dependent paths that legitimately drift between runs. -/
def volatilePrefixes : List String :=
  ["-- generated:", "-- stamp:", "-- source:"]

/-- A line is volatile iff it starts with one of the exempt prefixes. -/
def isVolatile (line : String) : Bool :=
  volatilePrefixes.any (fun p => line.startsWith p)

/-- The body: the non-volatile lines — the tied bytes. -/
def bodyOf (text : String) : String :=
  String.intercalate "\n" ((text.splitOn "\n").filter (fun l => !isVolatile l))

/-- The content hash: the body's bytes folded through the LCG (the tape
    reader doubles as the digest). Same body → same hash, always. -/
def contentHash (body : String) : UInt64 :=
  body.toList.foldl (fun h c => lcg (h + (c.toNat % 256).toUInt64))
    1442695040888963407

/-- The stripped compare: body bytes must tie; volatile header lines are
    exempt. Returns `.ok` or a structured failure carrying both hashes
    (the diff anchor). -/
def cmp (emitted golden : String) : CheckResult :=
  let eb := bodyOf emitted
  let gb := bodyOf golden
  if eb == gb then .ok ()
  else .error s!"byte-tie mismatch: body bytes differ \
    (emitted hash {contentHash eb}, golden hash {contentHash gb})"

end TestingKit.Golden
