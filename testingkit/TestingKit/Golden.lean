/-
# TestingKit.Golden — the ONE text byte-tie (the stripped compare)

Owned by: the TestingKit agent (the mandate tree, `testingkit/`).
Driving decision: notes/v3/15-patterns.md #10 (the emitter spine — the
byte-tie is the emitter's correspondence law; the artifact header carries
the content hash; the tie strips only the volatile lines) +
notes/v3/09-gates-ops.md §2: the committed generated artifacts are the
spec of record; the tie binds CONTENT (the header's timestamp/sha are
exempt metadata; the embedded content hash + body bytes are the tie);
drift fails CI; regen is a deliberate commit-visible act.

THE ONE TIE — the law in one place. A generated artifact's committed
text ties iff:
1. it CARRIES the 2-line GENERATED header (the header's PRESENCE marks
   the generator's one-writer surface — a headerless text is outside
   the tie's exemption, and the artifact face refuses it),
2. the BODY (everything after the leading header block) is byte-equal
   to the fresh body, and
3. the header's content-hash line still names the fresh body's hash —
   `String.hash`, the `Kit.Emit.GenMeta.contentHash` contract every
   driver embeds. The ONE text hash: the byte-tie names no other.

The binary twin — `Kit.Emit.tieBytes` over `Kit.Emit.bytesHash` (the
LCG fold, the ONE recurrence at `TestingKit.lcg`; a binary has no
volatile region, its header rides the `.hdr` sidecar) — is the same
law's byte-valued face, adopted kit-side, never re-encoded here.

THE VOLATILE CONVENTION (the one strip): the volatile region is
EXACTLY the leading 2-line GENERATED header block — the driver
(`Kit.Emit.header`) prepends it, always two lines. The convention this
consolidation replaced — a per-line PREFIX filter
(`-- generated:`/`-- stamp:`/`-- source:`) — matched no header the
tree actually writes (an accident, not a need) and folded a SECOND text
hash (an LCG over the body's chars) beside the one the artifacts embed;
both spellings died here, and the scaffold's generator now embeds the
one hash too. The strip keys on the header's own markers (line 0
carries GENERATED + DO NOT EDIT — the artifact-headers gate's
detection face), so a bare body (a golden pin, a hand-owned seed) ties
whole.

Adoption faces (ONE definition, three consumers — never a re-encoding):
- `Kit.Emit.tieText` — the kit's artifact face; `gates gen-check`'s
  text lane compares through it (beside the binary `tieBytes`).
- `cmp` — the test-golden compare (ScaffoldTests' byte-tie rows,
  SchemaTests' golden pins): the same strip, both sides.

Module form: this file is the law's home — the TextKit.Diag/Laws
precedent (a module-form law file below every consumer; Kit imports
TestingKit, never the reverse).

Mined from: legacy/lean/TestingKit/TestingKit/Golden.lean (the
committed-golden discipline). Fresh here: the compare is PURE (text in,
verdict out — no file IO; drivers own the FS) and the strip is
structural data, so the exemption itself is testable.

The five questions (notes/v3/01-core.md):
- root: Crossing — the artifact-vs-golden compare (the byte-tie's
pure core).
- carrier grade: the tie law — the structural strip + body
byte-equality + the header naming the fresh body's `String.hash`.
- spine reading: the artifact stage's check face; drivers own the FS.
- ladder rung: rung 1 — pure total functions.
- gate row: the discipline behind gen-check (the compare itself is
pinned in TestingKitTests; ScaffoldTests' byte-tie rows consume it).
-/

module

public import TestingKit.Spec

@[expose] public section

namespace TestingKit.Golden

/-- The ONE byte-tie verdict (ctors, never strings — 04 §6). Both
    faces return it: the text tie (`tie`) and the binary twin
    (`Kit.Emit.tieBytes`). -/
inductive ByteTie where
  | tied
  | drifted (why : String)

/-- The header's own markers (line 0 of the `Kit.Emit.header` block):
    the artifact-headers gate's detection face, style-independent
    (the comment prefix varies per target; the markers do not). -/
def isHeaderLine0 (l0 : String) : Bool :=
  l0.contains "GENERATED" && l0.contains "DO NOT EDIT"

/-- THE VOLATILE CONVENTION — the one strip: the leading 2-line
    GENERATED header is the volatile metadata (clock, spec sha, item
    count); `bodyOf` returns the tied bytes (the body). A text that
    does not carry the header (a bare golden pin, a hand-owned seed)
    has NO exempt region — its bytes tie whole. -/
def bodyOf (text : String) : String :=
  let lines := text.splitOn "\n"
  match lines[0]? with
  | some l0 =>
      if isHeaderLine0 l0 then String.intercalate "\n" (lines.drop 2)
      else text
  | none => text

/-- THE ONE TEXT BYTE-TIE — the artifact face (the gate's compare).
    The committed artifact must carry the 2-line GENERATED header
    (its absence is drift, never an exemption), the body must tie
    byte-exact against the fresh body, and the header's content-hash
    line must still name the fresh body's hash (`String.hash` — the
    `Kit.Emit.GenMeta.contentHash` contract). -/
def tie (committed fresh : String) : ByteTie :=
  let lines := committed.splitOn "\n"
  match lines[0]? with
  | none => .drifted "committed file has no 2-line GENERATED header"
  | some l0 =>
      if !(isHeaderLine0 l0) then
        .drifted "committed file has no 2-line GENERATED header"
      else
        match lines[1]? with
        | none => .drifted "committed file has no 2-line GENERATED header"
        | some headerLine =>
            let committedBody := bodyOf committed
            if committedBody != fresh then
              .drifted "artifact body drifted"
            else if !(headerLine.contains (toString fresh.hash)) then
              .drifted "header content hash does not name the fresh body's hash"
            else
              .tied

/-- The test-golden face: the same ONE strip (`bodyOf`) on both sides,
    the bodies must tie. Returns `.ok` or a structured failure carrying
    both bodies' hashes (the diff anchor — the ONE text hash,
    `String.hash`). The hash-naming face is the artifact tie's (`tie`)
    — a golden-vs-emitted compare carries its own headers on both
    sides; the gate's committed-vs-fresh-body relation is `tie`'s. -/
def cmp (emitted golden : String) : CheckResult :=
  let eb := bodyOf emitted
  let gb := bodyOf golden
  if eb == gb then .ok ()
  else .error s!"byte-tie mismatch: body bytes differ \
    (emitted body hash {eb.hash}, golden body hash {gb.hash})"

end TestingKit.Golden
