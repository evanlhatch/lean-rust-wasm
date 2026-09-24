# Design — the typed bidirectional grammar layer (05 §1, execution shape)

The design of record for Phase 4's core: one `Grammar α` value drives
parser + printer + certificate + the two round-trip theorems, GENERIC —
per-format work becomes rows. This file is prescriptive: execution
agents build what is written here. Every Lean fence below is a
**sketch** (the code does not exist; the docs-check marker convention
applies — an unmarked fence would claim real decls).

Doctrine slots: 05 §1 (this implements it) · 01 §4 (the rel node rides
the kit's graded carrier) · 15 #1 (the certificate is a CheckedProp)
· 15 #2 (both laws are append-form) · 15 #12 (the layer sits on
TextKit's total GParser carrier) · 06 §6 (totality: fuel for parse,
a carried measure for print — no `partial`, no hidden wf opacity)
· 05 §4 (errors are the converged ParseError).

## 0. What does not survive contact (the honest deltas from 05 §1's sketch)

1. **`rel` rides `Kit.Codec`, not the legacy `PartialIso`** — and it
   needs TWO more fields. `PartialIso` is v3's `Codec` (renamed, policy
   field added). Contact facts: (a) parse∘print needs only
   `decode (encode x) = some x` — Codec's law exactly; (b) the
   canonicalization law needs the OTHER direction on accepted raws
   (`decode raw = some r → encode r = raw`) — not in any kit grade, so
   it is an explicit node field `exact`; (c) the printer's alternation
   choice needs a domain discriminator `owns`. `Kit.Retraction` was
   considered and REJECTED: its `inv` is total, but the real semantic
   mappings are partial (`keyOfTy : Ty → Option KeyTy`). The Codec's
   `policy` field is not used at the node level (the grammar itself is
   the accepted-byte policy; node codecs fill `policy := fun _ => True`
   — the format-level Codec row is built from the two generic theorems,
   §3.4).
2. **`tok (l : Lex Tok) (payload : Tok → Option R)` collapses.** The
   leaf is a typed `Lexeme R` bundling scan/print/laws; the payload
   prism is `rel` over an atom. One mapping discipline, not two
   (leftover rule at the node level). Node set: `atom seq alt rep opt
   label rel fix self` — 9 nodes.
3. **`rep` carries NO progress proof field.** Progress is the checker's
   computed `¬nullable body`; the generic consumption lemma (§3.3)
   supplies the proof. The grammar value stays PURE DATA (the checker
   and dsl! must fold over it — proof fields would poison both).
4. **The sketch has no recursion; the migration targets do.** The
   snapshot's `ty` and WIT's `ty` are recursive grammars
   (`option<option<…>>`). A finite grammar value needs the `fix`/`self`
   node pair. `fix` carries a payload measure + a decreases proof
   (§1.3) — the one genuinely non-mechanical point of the layer
   (print totality cannot ride the input, there is no input).
5. **`declare_inversion` as sketched is dead on arrival.** The per-node
   inversion-lemma family is REPLACED by the two generic theorems (the
   inversion IS `print_parse`). The surviving generated surface is the
   thin-wrapper family (05 §3's thin-wrapper rule: generic theorem
   first, specialization second); its generator is `declare_format`
   (§6). The name `parse_emit` becomes `Grammar.parse_print`.
6. **No lexer level** (§7).

## 1. The `Grammar α` value

Home: `kit/Kit/Grammar*.lean` (non-module files importing TextKit.* +
Kit.* — the textkit→kit direction is build-impossible, the kit→textkit
direction is the proven one, so the layer lives kit-side; TextKit stays
the pure parser substrate). Core-only, cone C0.

### 1.1 Head specs and lexemes

```lean sketch
/-- A FIRST-set entry: a literal head or a char-class head. The
    disjointness discipline over these is the certificate's decidable
    fragment (§2). -/
inductive HeadSpec where
  | lit (s : String)          -- the token's spelling is this literal
  | cls (p : Char → Bool)     -- the first char satisfies p

/-- Does a head spec match the text at this point? -/
def HeadSpec.matches : HeadSpec → List Char → Bool
  | .lit s, cs => s.toList.isPrefixOf cs
  | .cls p, cs => cs.head?.any p

/-- The typed leaf: a total scanner + its printer + the leaf laws.
    `munch` is the maximal-munch discipline as DATA: `some p` means the
    character AFTER the token must fail p (takeWhile-scanners: p is the
    scan predicate; literal keywords: p is the ident charset — the
    WIT `atomArm` discipline). Every lexeme consumes ≥ 1 char on
    success and fails on a head mismatch — the two facts the generic
    exclusion lemma stands on. -/
structure Lexeme (R : Type) where
  scan : GParser R
  print : R → String
  pre : R → Bool                      -- the write-side gate (nameOk's home)
  head : HeadSpec
  munch : Option (Char → Bool)
  scan_post : ∀ cur r cur', scan cur = .ok (r, cur') → pre r = true
  scan_exact : ∀ cur r cur', scan cur = .ok (r, cur') →
    cur.cs = (print r).toList ++ cur'.cs
  scan_head : ∀ cur r cur', scan cur = .ok (r, cur') →
    head.matches cur.cs = true
  head_fail : ∀ cur, head.matches cur.cs = false →
    ∃ e, scan cur = .error e
  print_scan : ∀ k r sfx, pre r = true →
    (munch.all fun p => sfx.head?.all (fun c => !p c)) →
    scan ⟨k, (print r).toList ++ sfx⟩ = .ok (r, ⟨k + (print r).length, sfx⟩)
  consumes : ∀ cur r cur', scan cur = .ok (r, cur') →
    cur'.cs.length < cur.cs.length
```

The standard lexeme library (`Kit/Grammar/Lexemes.lean`) lands with the
first migration and is exactly: `lit` (a bare literal), `kwLit` (literal
+ munch guard), `nameLex` (predicate munch, `pre` = the name
discipline), `natLex` (CANONICAL decimals only — leading-zero spellings
are rejected, keeping `scan_exact` true; this TIGHTENS the snapshot's
accepted bytes for `bounded(007)` — the committed artifact is
unaffected, the acceptance note is in §5), plus the text kit row the
lemmas need: `TextKit.GParser.scanWhile` (a positioned maximal-munch
scanner) with `scanWhile_stop`/`scanWhile_exact` inversions, ported
from `TextKit.takeWhile_stop`'s content (TextKit owns it; the layer is
its first consumer).

### 1.2 The inductive

```lean sketch
/-- The typed bidirectional grammar. Pure data (no proof fields — the
    certificate is computed OVER the value, not carried IN it; the one
    exception is `fix`, §1.3). -/
inductive Grammar : Type → Type where
  | atom : Lexeme R → Grammar R
  | seq  : Grammar A → Grammar B → Grammar (A × B)
  | alt  : Grammar R → Grammar R → Grammar R          -- ordered choice, one payload
  | rep  : Grammar R → Grammar (List R)
  | opt  : Grammar R → Grammar (Option R)
  | label (name : String) : Grammar R → Grammar R
  | rel  (m : Kit.Codec Raw R) (owns : R → Bool)
         (decode_owns : ∀ raw r, m.decode raw = some r → owns r = true)
         (exact : ∀ raw r, m.decode raw = some r → m.encode r = raw)
         (name : String) (valid : List String) :
         Grammar Raw → Grammar R
  | fix  (measure : R → Nat) : (body : Grammar R) →
         (∀ x y, y ∈ selfVals body x → measure y < measure x) → Grammar R
  | self : Grammar R
```

Notes on the shape:

- `alt` is SAME-PAYLOAD ordered choice. The Sum-typed alternation is
  rejected: branch-specific mappings live in `rel` INSIDE each branch
  (the ty grammar's branches are `rel boolCodec (atom (kwLit "bool"))`,
  etc.). The printer picks a branch by `valueOk` (§3.1).
- `rel` is the ONE semantic-mapping node (kit correspondence, 01 §4).
  `name`/`valid` feed the curated decode-failure error (§4); `owns` +
  `decode_owns` make the printer's branch choice and the
  parsed-values-are-owned lemma (§3.3) provable; `exact` is the
  canonicalization law's node-level content (§0.1).
- Punctuation is a DERIVED row, not a node:
  `punct l := rel unitCodec … (atom l)` with
  `unitCodec : Codec String Unit` (encode _ := the literal, decode :=
  equality gate). `keyword` prisms are the same row shape. These are
  defined ONCE in the layer.
- `self` refers to the closest enclosing `fix` (dynamic scoping, one
  binder — nested `fix` overwrites; no migration target nests).

### 1.3 The `fix` node and print totality (the non-mechanical point)

Parse recursion is input-driven: `fix` unfolds with a fuel (the
`tyP` precedent — fuel = remaining length + 1, dead arm at 0, the
guardedness certificate proves it unreachable, §2 WF-FIX).

PRINT recursion is value-driven and crosses `rel` (`encode` is an
arbitrary function), so NO generic structural/size argument exists.
Honest payment: `fix` carries `measure : R → Nat` + a proof that every
value a `self` occurrence receives is smaller, where

```lean sketch
/-- The values each `self` occurrence of `g` receives, computed by the
    same walk as the printer (structural on g — total, no fix-unfolding:
    `selfVals self x = [x]`, `selfVals (fix _ b) x = selfVals b x`). -/
def selfVals : Grammar R → R → List R
```

is a plain fold. The per-format proof is small and formulaic
(`simp [codec]; omega`-scale: the self-values are the ctor's direct
children inside `encode`'s output). This is format content, stated once
per recursive format — the generic layer cannot manufacture it and does
not pretend to.

The derived printer's totality: `printG` recurses structurally on the
grammar everywhere except `fix`, where it re-enters on the `self`-value
with the carried measure — `termination_by (sizeOf g, measure x)`
(lexicographic; 06 §6's "termination_by with an explicit measure" —
NOT kernel-opaque-wf at decision sites because no `decide` ever runs
over `printG`; if the lex measure fights the elaborator, the fallback
is the two-level walk: `printWalk` structural on the node taking the
self-handler with its `selfVals` membership proof — same obligation,
more plumbing). The design pins the OBLIGATION (measure + decreases on
`fix`); the wf-plumbing is execution.

## 2. The predictive-fragment certificate

Per 15 #1: a semantic Prop, a Bool checker, a proved soundness bridge,
completeness LOUDLY `.missing`.

### 2.1 The computed folds (pure, total, over the grammar value)

- `nullable : Grammar R → Bool` — `atom/self := false`; `opt/rep :=
  true`; `seq := ∧`; `alt := ∨`; `label/rel` := body; `fix b` :=
  `nullable b` (sound because `self` is guarded, WF-FIX below).
- `first : Grammar R → Option (List HeadSpec)` — `none` = a `self` in
  FIRST position (the guardedness failure surface); `fix b` requires
  `first b` to succeed, which IS the left-recursion/unguarded check.
- `tailMunch : Grammar R → Option (List (Char → Bool))` — the munch
  predicates exposed at the grammar's tail (`seq` takes the right's,
  falling back to the left's when the right is nullable; `alt` unions;
  `rel/label/opt/rep` pass through; `atom` is its own munch). `self`
  unfolds the enclosing fix ONCE; a second `self` hit at a
  munch-relevant tail REJECTS (unproductive right-recursion — no
  migration target needs it; this is the known conservative corner).
- `tailFirst : Grammar R → List HeadSpec` — FIRST of the nullable tail
  consumers (the law-1 suffix condition, §3.2).

### 2.2 The well-formedness conditions (the checker's rows)

At every `alt g₁ g₂`:
- **WF-ALT-1 (FIRST-prefix freedom):** every head of `first g₁` is
  disjoint from every head of `first g₂`, where disjointness is:
  lit/lit — neither is a prefix of the other; lit/cls (either side) —
  the literal's head char fails the class predicate; cls/cls — REJECT
  (conservative; char-predicate disjointness is not decidable by
  enumeration — this is the .missing completeness's main source).
- **WF-ALT-2 (no nullable left):** `nullable g₁ = false` (an earlier
  nullable branch shadows later ones under ordered choice — almost
  always a grammar bug; honestly rejected).

At every `seq g₁ g₂`:
- **WF-SEQ-1 (stop determinism):** if `nullable g₁`, then `first g₁`
  disjoint from `first g₂` (an `opt`/`rep` stops exactly where the
  continuation starts).
- **WF-SEQ-2 (munch break):** every predicate in `tailMunch g₁` is
  broken by every head of `first g₂` (lit head: the predicate fails its
  first char; cls head: reject). This is the maximal-munch FOLLOW
  discipline — the `takeWhile_stop` break conditions, made structural.

At every `rep b`:
- **WF-REP-1 (progress):** `nullable b = false`.
- **WF-REP-2 (iteration self-junction):** WF-SEQ-1/WF-SEQ-2 applied to
  `(b, b)` — the boundary between iterations obeys the same discipline
  as the boundary with the continuation.

At every `fix b`:
- **WF-FIX (guardedness):** `first b` succeeds (every `self` sits
  behind a consuming token on every path — the snapshot's
  `option(…self…)` and WIT's `option<…self…>` both pass).

`rel`/`label`/`opt` contribute no conditions (their bodies are checked
recursively).

### 2.3 The CheckedProp

```lean sketch
/-- The semantic well-formedness (the spec — stated over
    `HeadSpec.matches`, never over the checker). -/
def Predictive : Grammar R → Prop

/-- The executable shadow, with the failure-facing twin: the Diags
    name the offending junction (the enclosing `label` chain + the
    literal spellings) — 05 §4's every-failure-ships-its-Diag rule. -/
def wfCheck : Grammar R → Bool
def wfDiagnose : Grammar R → List Kit.Diag   -- wfCheck g = wfDiagnose g.isEmpty

def grammarPredictive : Kit.CheckedProp (Grammar R) where
  P := Predictive
  check := wfCheck
  sound := wfCheck_sound          -- PROVED (the bridge theorem)
  complete? := .missing           -- LOUD: cls/cls + WF-ALT-2 conservatism
```

The soundness bridge's content is the per-row head lemmas:
prefix-free literals are mutually exclusive on any extension
(`l₁` not a prefix of `l₂` and conversely ⟹ `l₁` is not a prefix of
`l₂ ++ rest`); a literal whose head fails a class predicate is never
matched by that class. Both are small hand lemmas (01 §7's rung).

The completeness honesty (05 §1: "other parsing strategies enter
through the same semantic contract"): grammars outside the fragment
hand-prove `Predictive g` directly and cite the same generic theorems —
the certificate is the decidable ROUTE to the premise, not the premise.

## 3. The derived parser, printer, and the two generic laws

### 3.1 The folds

```lean sketch
/-- The value-side precondition fold (the nameOk discipline, generic):
    atom := lex.pre; seq := both; alt := either (this is also the
    printer's branch discriminator); opt none := true; rep := all;
    rel := owns x && valueOk body (encode x); label := body;
    fix/self := body/env. -/
def valueOk : Grammar R → R → Bool

/-- Parse: structural on the grammar + the fix fuel (fuel = remaining
    length + 1 at entry; the 0 arm is the dead "fuel exhausted" error,
    WF-FIX proves it unreachable). -/
def Grammar.parse : Grammar R → Nat → GParser R

/-- Print: structural on the grammar, the fix-measure at `self`
    (§1.3). alt picks the branch by `valueOk`; rep is a foldr of ++
    (the derived printer is the byte-tied emitters' engine — 06 §7b's
    rope rule yields to the tie: the append-form law REQUIRES the
    String reading). -/
def Grammar.print : Grammar R → R → String

/-- The run entry: fuel = length + 1, offset 0, full consumption or
    the trailing-garbage error at the final offset. -/
def Grammar.run (g : Grammar R) (s : String) : Except ParseError R
```

### 3.2 Law 1 — parse∘print (append form, 15 #2)

```lean sketch
/-- The suffix condition: the suffix breaks every tail munch AND
    matches no tail-greedy FIRST head. Decidable; `tailOk g [] = true`
    always, so full-file runs need no side condition. -/
def tailOk : Grammar R → List Char → Bool

theorem Grammar.parse_print (g : Grammar R) (hp : Predictive g)
    (x : R) (hx : valueOk g x = true)
    (fuel k : Nat) (sfx : List Char)
    (hfuel : (g.print x).length + sfx.length + 1 ≤ fuel)
    (hfol : tailOk g sfx = true) :
    g.parse fuel ⟨k, (g.print x).toList ++ sfx⟩
      = .ok (x, ⟨k + (g.print x).length, sfx⟩)

/-- The corollary every format cites. -/
theorem Grammar.run_print (g : Grammar R) (hp : Predictive g)
    (x : R) (hx : valueOk g x = true) :
    g.run (g.print x) = .ok x
```

### 3.3 Law 2 — print∘parse (exactness; the canonicalization content)

```lean sketch
/-- The parse consumed EXACTLY the print of its result. NO certificate
    premise — only the leaf/rel exactness fields (the certificate buys
    law 1's greedy-stop and branch-selection correctness; this
    direction is unconditional). -/
theorem Grammar.print_parse (g : Grammar R)
    (fuel : Nat) (cur cur' : Cursor) (x : R)
    (h : g.parse fuel cur = .ok (x, cur')) :
    cur.cs = (g.print x).toList ++ cur'.cs
      ∧ cur'.off = cur.off + (g.print x).length
      ∧ valueOk g x = true

/-- Normalization, whole-file form: accepted text IS canonical
    (strict fragment). Formats with a tolerant surface compose a
    named pre-pass (WIT's stripComments) or a Kit.Normalization row
    (the snapshot's sort) — §5, per format. -/
theorem Grammar.print_run (g : Grammar R) (s : String) (x : R)
    (h : g.run s = .ok x) : g.print x = s
```

### 3.4 Proof architecture

Law 1: induction on `g`, generalizing `fuel`, the cursor, and the
`self`-environment; the `fix/self` case is an inner induction on
`fuel`. Per-node content:

- `atom`: the lexeme's `print_scan`; `hfol`/WF-SEQ-2 supply the munch
  break at each use site.
- `seq`: append-assoc + both IHs; the junction premises enter HERE
  (WF-SEQ-1 for nullable lefts, WF-SEQ-2 for munch tails).
- `alt`: the **first-exclusion lemma** — a non-nullable grammar whose
  heads all fail to match the text fails on it (induction on the node;
  the leaf case is `head_fail`; WF-ALT-1 supplies the disjointness,
  WF-ALT-2 the non-nullability) — the wrongly-ordered branch fails, so
  `orElse` reaches the branch `print` chose (`valueOk`).
- `opt`: `some` — IH; `none` — the body must fail on the suffix:
  `hfol` + first-exclusion.
- `rep`: list induction × the manyGo fuel lemmas; stop-exactness from
  WF-SEQ-1/WF-REP-2 + first-exclusion; WF-REP-1 + the **consumption
  lemma** (a successful parse of a non-nullable grammar shortens the
  input — induction on the node, leaf case `Lexeme.consumes`) keep the
  zero-progress stop dead.
- `rel`: `m.decode_encode` (+ `valueOk` via `owns`).
- `label`: success path untouched by the error mapping.
- `fix/self`: the fuel invariant `cur.cs.length + 1 ≤ fuel` is
  preserved because guardedness + the consumption lemma force ≥ 1
  consumption before each re-entry; the fuel-0 arm dies by omega.

Law 2: induction on `g` generalizing cursor/fuel/env; `fix/self` by
inner fuel induction. Per node: `atom` — `scan_exact`; `seq` — append
cancellation; `alt` — orElse-success inversion + IH; `opt/rep` —
outcome cases, rep by a manyGo inversion lemma (inner fuel induction);
`rel` — `exact`; the `valueOk` conjunct by `scan_post` (atom) and
`decode_owns` (rel). No certificate premise anywhere.

The fuel-sufficiency plumbing the snapshot pays BY HAND today
(`tyDepth_le_tyText`, `lenB`…`printItems_ge` — the whole length
family) is proved ONCE here, generically: guardedness makes each
recursion level consume ≥ 1 char, so fuel = input length + 1 always
suffices.

### 3.5 The format's correspondence row

Per migrated format, the two generic theorems specialize to a
`Kit.Codec` (decode∘encode = `run_print`; the accepted-byte policy =
the grammar's language, exact via `print_run`) — the thin-wrapper rule
(05 §3): generic theorem first, `Format.roundtrip := Grammar.run_print
formatGrammar formatCert` second.

## 4. The error discipline

Parse failures are the converged `TextKit.ParseError` (Diag envelope +
position) BY CONSTRUCTION — the derived parser is a GParser fold:

- `atom` failures: the lexeme's own error (expected-set = the lexeme's
  name/literal).
- `alt` merges via `ParseError.farther` (farthest position wins;
  same-position unions the expected-sets, order-stable) — the WIT
  tyP "deeper error wins" behavior falls out, no per-format code.
- `label name` pushes the name on the envelope's context stack and
  sets `valid := [name]` — the grammar's labels ARE the error's
  teaching surface; unlabeled grammars degrade honestly (empty valid
  at the top, farthest leaf sets below).
- `rel` decode failure: a curated error AT THE NODE'S START OFFSET —
  `message` names the node's `name`, `got` is the consumed raw text,
  `valid := the node's valid list`, `suggest` filled by the ONE engine
  (`TextKit.suggestFor`) when `valid` is non-empty (keyword prisms:
  the valid space is the keyword list — the closed-world rule, 05 §4).
- `fix` fuel-0 and `run`'s trailing-garbage: `ParseError.base` at the
  position with the honest expected-set.
- The E-code: the layer's failures ride `TextKit.parseCode` (TK1001).
  Per-format codes are allocated at migration ONLY if a consumer
  distinguishes them (leftover rule; the registry's stable-allocation
  discipline applies when one lands).
- The certificate's own failures (`wfDiagnose`) are `Kit.Diag`s
  (Validation-style accumulation, 05 §4), each naming the junction —
  these are BUILD-TIME errors (dsl!/the discharge site), never parse
  errors.

## 5. The migration plan (the three consumers)

Order: **CodeRegistry → Snapshot → Wit.Parse** — simplest shape first
(no recursion), then recursion + a sort, then the richest surface
(comments pre-pass, proof-carrying payloads). One vertical slice per
migration: grammar value + lexeme/codec rows + certificate discharge +
the entry-point swap + gates green. THE BYTE-TIE DISCIPLINE: the
committed artifacts — `notes/code-registry.txt`,
`notes/universe.snapshot`, `gen/schema-slice.wit` — MUST NOT change;
the re-deriving gates (`code-registry-check`, `snapshot-check`,
`gen-check`) stay green with ZERO re-baseline. Test-suite error-text
pins may update (they are tests, not artifacts) — each such update is
named in the migration's commit.

### 5.1 `kit/Kit/CodeRegistry.lean` (first)

Format: rows `name<TAB>code`, optional `-` tombstone, sorted by code,
LF endings. Already total over TextKit.Basic scanners with
`parse_print` proved.

Dies: the hand parse/print pair over the text face; the per-format
round-trip proof (replaced by the specialized generic theorems).
Stays: the registry MODEL untouched — `CodeRow`, `sortedCodes`/`SortedLt`,
`wfProp`/`codeRegistryWf` (the CheckedProp over parsed data is the
model's invariant, not text plumbing), `allocate`'s discipline. The
grammar: `rep` of row-grammar (alt of tombstone/live rows) — recursion-free,
so this slice validates the core before `fix/self` exists in anger.

### 5.2 `schemacore/SchemaCore/Snapshot.lean` (second)

Dies: `parseTy`/`parseFields`/`parseItem`/`parseItems` and their fuel
plumbing; the per-shape law family (`parseTy_tyText`, `parseFields_render`,
`parseItem_render`, `parseItems_printItems`); the length family
(`tyDepth_le_tyText`, `lenB`…, `printItems_ge` — subsumed by the
generic fuel sufficiency, §3.4); `natText`'s one-off home (the nat
codec becomes the layer's `natLex` row — the theorem content
`scanNat_natText` ports INTO the lexeme's `print_scan`).
Stays: `snapshotAlg` (its rows become the rel codecs' data — the ONE
walk's snapshot face is unchanged); `canonical`/`insertItem` (the sort
is FORMAT content, layered over the grammar: the grammar parses lines
in order, canonicalization composes as a `Kit.Normalization` row — the
canonicalization direction stays the noted honest gap at the FORMAT
level, unchanged by this layer); `nameOk`/`namesOk` (they become the
name lexeme's `pre` and the format's `valueOk` specialization);
`snapshotEmitter`, `snapshotOfEnv`, the gate.
Acceptance note: `natLex` rejects leading-zero caps the old `scanNat`
accepted — an accepted-set tightening, loud here, zero artifact drift.

### 5.3 `wit/Wit/Parse.lean` (third; in-flight — land the hand version's
proofs, then migrate)

Dies: the combinator chains (`atomArm`/`unaryArm`/`binaryArm`/`tyArms`/
`tyP`/`fieldsGo`/`recordsP`/`interfacesP`), the per-shape inversion
family (`*_sound`), the hand fuel discipline. `Wit.Render`'s functions
are replaced by the derived printer (the artifact pin proves the
bytes).
Stays: the `Wit` AST; `stripComments` as the NAMED pre-pass (the
grammar operates on comment-stripped text; the format-level law is
`Render.package p = stripComments s`, composed from `print_run` +
the strip's own row — comments are not grammar content); the nodup
constructions (the record/interface rel codecs DECIDE nodup and
construct the proof field — the codec's `decode` is a decider, the
grammar layer never sees the proof); the correspondence rows
(`witCodec` etc. become the §3.5 thin wrappers; `witImageIso` is
re-derived from them).
The WIT grammar exercises: `fix` (ty), `rep` (fields/records/
interfaces), the keyword-munch lexemes (`atomArm`'s post-keyword
check IS `kwLit`), the four-deep continuation dispatch (WF-SEQ-1:
`"\n    "` vs `"\n  }"` are prefix-free — the hand-rolled lookahead
becomes a certificate row).

## 6. The authoring surface: dsl! + declare_format

**dsl!** (host-only meta, `Kit/Grammar/Dsl.lean`) generates a DSL from
a grammar value — the third DSL in the tree MUST use it (07 R4); it
lands WITH its first consumer (leftover rule). Honest minimal shape:

```lean sketch
dsl! witTy for Wit.tyGrammar cert Wit.tyCertified reify Wit.tyToExpr
```

generates exactly three things:
1. a syntax rule + term elaborator: the literal's text is parsed by
   `Grammar.parse` AT ELABORATION; success reifies the value through
   the named reifier (06 §7: the tree's ONE reifier family per type —
   never a new quoter); failure throws the ParseError rendered through
   `Diag.toString` (the error discipline lands in the DSL for free);
2. an unexpander/delaborator printing the value via `Grammar.print`
   (byte-tie of the surface: printed text re-elaborates — the cert
   argument is what SELLS this, so dsl! refuses an uncertified
   grammar);
3. the `@[derived]` stamps + the curated instance-gate failure (name
   the grammar, the payload, the missing piece — never a synthesis
   wall).

Nothing more: no grammar-notation sugar in v1 (the node constructors +
the standard rows are the authoring syntax until a second consumer
proves the sugar's worth — leftover rule).

**declare_format** (the honest residue of 05 §1's `declare_inversion`,
§0.5): given the grammar + the discharged certificate, generate the
thin wrappers — `Format.parse`, `Format.print`, `Format.run_print`,
`Format.print_run`, the `Kit.Codec` row — each `@[derived]`, each a
one-line specialization. No per-node inversion lemmas are generated:
the generic theorems ARE the inversion kit for grammars.

## 7. The honest boundaries

- **The fragment excludes** (loudly, via the checker or the type):
  cls/cls head disjointness (undecidable by enumeration — conservative
  reject; `complete? := .missing` says so forever); nullable left
  branches at `alt`; unguarded `self` (left-recursion is a checker
  failure, not a divergence); unproductive right-recursive munch tails;
  whitespace/comment tolerance INSIDE the grammar (a named pre-pass —
  `stripComments` — or explicit whitespace nodes; the strict fragment's
  law 2 is exactness); longest-match ACROSS alternation (munch lives
  at leaves only); context-sensitive constructs (indentation, stateful
  lexing); backtracking-with-commit semantics (the alt is pure ordered
  choice). The wall behind the conservative corners: language
  disjointness — hence unambiguity — of general grammars is
  undecidable; the certificate is a DECIDABLE SUFFICIENT condition and
  says so in its type (`.missing`).
- **What stays hand:** the per-format `rel` codec rows (semantic
  mappings are format content — `keyOfTy`, the ty-ctor codecs, the
  nodup deciders); the per-recursive-format `fix` measure + decreases
  proof (§1.3); canonicalization beyond exactness (sorts, comment
  strips — `Kit.Normalization` rows composed per format); the
  write-side name disciplines as lexeme `pre`s (they RIDE the layer —
  `nameOk` is a `pre`, not a separate gate).
- **The lexer decision: there is NO lexer level.** The grammar's
  leaves are char-level lexemes over `List Char`; the token discipline
  (maximal munch + the break-char rule) is `Lexeme.munch` + WF-SEQ-2,
  living at the grammar level where the proofs consume it. A token
  stream would double the carrier (a second cursor, a second error
  position space) and the law families (token-level round trips under
  char-level ones) — and no consumer exists: all three migration
  targets are char-level with exactly this munch discipline. Owner of
  the token discipline: the grammar layer's lexeme library over
  TextKit's scanners (TextKit owns the char machinery; the layer owns
  the munch-as-data).
- **The boundary that must not blur** (05 §1, verbatim intent): the
  round-trip laws prove TEXTUAL agreement. The emitted artifact's
  semantics is a separate theorem (the correspondence lane) — no row
  in this design claims otherwise.

## 8. What lands (the build rows)

| Module | Content | Doctrine slot |
|---|---|---|
| `TextKit/Combinators.lean` (+Lemmas) | `GParser.scanWhile` + inversions | 15 #12 |
| `kit/Kit/Grammar.lean` | HeadSpec, Lexeme, Grammar, the folds (nullable/first/tailMunch/tailFirst/valueOk/selfVals) | 05 §1 |
| `kit/Kit/Grammar/Parse.lean` | parse (fuel) / print (measure) / run | 06 §6 |
| `kit/Kit/Grammar/Check.lean` | wfCheck/wfDiagnose + `grammarPredictive` (CheckedProp, sound, `.missing`) | 15 #1 |
| `kit/Kit/Grammar/Laws.lean` | `parse_print`, `print_parse`, the run corollaries | 15 #2 |
| `kit/Kit/Grammar/Lexemes.lean` | lit/kwLit/nameLex/natLex + punct/keyword rows | the token discipline |
| `kit/Kit/Grammar/Dsl.lean` | dsl! (host meta) — WITH its first consumer | 07 R4 |
| `kit/Kit/Grammar/Declare.lean` | declare_format (thin wrappers) | 05 §3 |

Tests (`KitTests`/the formats' suites): golden round-trips per migrated
format + the MANDATORY negative controls (15 #5): sabotaged grammars —
a prefix-colliding alt, a nullable `rep` body, an unguarded `fix`, a
munch without its break — must each fail `wfCheck` with the named
Diag. Build-time `#guard`s at the discharge sites (06 §7).
