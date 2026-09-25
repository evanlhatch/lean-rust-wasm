# Design v2 — the grammar layer, round two: from the two walls to the laws

The design of record for the grammar layer's SECOND round. Round one
(`notes/design-grammar-layer.md`, v1) built the engine and hit two
precise walls; this round STARTS from the walls. This file supersedes
v1 where they differ; v1 stays as history. Prescriptive: execution
agents build what is written here. Every Lean fence is a **sketch**
(the docs-check marker convention) — the landed decls are cited inline
and live in `textkit/TextKit/Grammar.lean`, `textkit/TextKit/Grammar/Parse.lean`,
`textkit/TextKit/Grammar/Check.lean`.

Doctrine slots: 05 §1 (this completes it) · 15 #1 (the certificate is
a CheckedProp) · 15 #2 (both laws append-form) · 15 #12 (the layer
sits on TextKit's total GParser carrier) · 06 §6 (totality: fuel for
parse, AccD over the carried measure for print) · 06 §2 (kernel walls:
no inductive+def mutual blocks — the landed scheme respects it) ·
05 §4 (errors are the converged ParseError) · the leftover rule (every
certificate row + every leaf field names its law-side consumer, §4.3).

## 0. The state of the ground (what round one landed, what parked)

**Landed, green, gated:**
- `TextKit/Grammar.lean` — the 9-node shape: the CLOSED `Grammar`
  (atom/seq/alt/rep/opt/label/rel/fix) + the OPEN family `GrammarE R A`
  (adds `selfE`), `SelfPathE` (the self-value relation), `AccD` (the
  Type-valued accessibility certificate), `Lexeme` (the typed leaf,
  7 law fields), and the computed folds (nullable/first/effFirst/guard/
  tailSelfFree/tailMunch/tailFirst/valueOkWalk/fixValueOk/tailOkE/tailOk).
- `TextKit/Grammar/Parse.lean` — the derived TOTAL parser
  (`GrammarE.parseE`/`Grammar.parseG`, fuel-driven, lex measure
  `(fuel, sizeOf g, phase)`), the derived TOTAL printer
  (`GrammarE.printWalk`/`Grammar.printFix` over `AccD.ofFuel`,
  `Grammar.printG`/`Grammar.print`), the run entry (`Grammar.run`,
  fuel = length + 1). No `partial`, no premises on print.
- `TextKit/Grammar/Check.lean` — the semantic Prop folds
  (`Grammar.Predictive`/`GrammarE.PredictiveE`), the problem walk
  (`wfProblems`/`wfDiagnose`, one Diag per failed row NAMING the row),
  and **`Grammar.wfCheck_sound` — PROVED**. The certificate survives
  round two unchanged in shape (§4).

**Parked:** `notes/grammar-laws-wip.lean.txt` — ~2900 lines of the
senior's proof content (does not compile as-is; the build task is
landing it green, not redesigning it): §0 the head/string hand lemmas
(`prefix_total`, `disj_sound`, `breaks_sound`, `matches_append`…), §1
the print-head-vs-FIRST family (`printBundleE`/`printFixBundle`/
`printBundleG` — the wall-1 kit's print half), §2 the parse duals
(`parseMonoE`/`parseConsumeE`), §3 law 2 open (`print_parse_E`), §4
the parse head/exclusion family (`parseHeadE`/`parseExcludeE`), §5 the
closed family + **law 2 closed (`Grammar.print_parse`) — done
modulo compile-fixing**, under the discovered `altCoherent` premise
(§5). **Missing from the parked file: the junction family and law 1
entirely** — the token wall hit there. §6 specifies them.

**The two walls' fates:**
- **Wall 2 (the recursion-scheme knot) — DISSOLVED, landed.** The
  Grammar.lean module header records how: the fix body lives in the
  separate open family `GrammarE R R` with `selfE : GrammarE R R` at
  EXACTLY the enclosing payload type; the parse's self-environment
  became the closed term `sb` itself (defunctionalized), so no
  polymorphic env crosses the index; print recursion rides `AccD` over
  the fix-carried measure with `SelfPathE` derivations threaded to the
  `selfE` leaves. No inductive+def mutual block, no Grammar-indexed
  sibling inductive, no polymorphic-recursive fold remains. §1
  evaluates the alternatives against this fact.
- **Wall 1 (the seq-case IH premise) — a MISSING LEMMA FAMILY, now
  specified (§6.3).** Law 1's seq case needs `tailOkE a p (print b ++
  sfx)` from `tailOkE (seq a b) (p,q) sfx` — the junction lemma. v1
  never specced the family; the parked file landed its two SUPPORT
  kits (the print-head-vs-FIRST bundle and the parse-side
  duals/exclusion) and parked before the junction itself. §6 gives the
  exact statements and the per-node proof content.

## 1. The recursion-scheme decision (wall 2): the four options, honestly

The question is moot unless an option BEATS the landed scheme, because
the landed scheme compiles, is total, and its certificate is proved.
The evaluation is therefore: what would each alternative buy, at what
cost, against the landed baseline.

**Option A — the named-reference discipline (a registry of named
grammars + a `ref name` node; acyclicity via `ZSet.Graph.Acyclic`;
laws compose per-grammar with the references' laws as hypotheses).**
REJECTED for this round. (a) The knot it would dissolve is already
dissolved — and the landed scheme IS the registry's degenerate case:
`sb` is a one-entry registry, `selfE` is the one `ref`, the unfold is
the function call `parseE sb sb fuel` / the `printFix` closure. (b) A
real name registry RE-INTRODUCES the wall-2 environment: the parse
fold would need a name → grammar association over HETEROGENEOUS
payloads (seq changes the payload index), i.e. either a homogeneous
registry (insufficient) or an indexed map with the same
index-refinement wall the knot was about. (c) Acyclicity is a SECOND
well-formedness dimension threaded through every law statement;
the fuel + the carried measure already give termination with the
certificate proving the dead arms unreachable. (d) The leftover rule:
no consumer — all three migration targets are single-binder
recursions (the snapshot's `option(…self…)`, WIT's `option<…self…>`;
CodeRegistry recursion-free). ENTRY CONDITION, written down: the first
format with mutually recursive named productions (real WIT's named
type references across records) lands the registry as an EXTENSION —
per-name grammar rows, each law stated with the referenced names' laws
as hypotheses, the acyclicity certificate riding `Graph.Acyclic` — and
this design's per-lemma architecture carries over unchanged (the
one-binder `sb` generalizes to the acyclic walk's current node).

**Option B — the non-indexed syntax + the semantic layer (Grammar as a
plain inductive, no payload index; typing recovered at the
interpretation).** REJECTED. What it buys: simpler folds (no
polymorphic recursion). What it costs the laws' strength: the parse
produces a value-TREE; law 1 (`parse (print x) = ok x`) needs the
interpretation to succeed on printed trees — a new premise family
(print∘interpret agreement) strictly harder than the current
`valueOk`; law 2's exactness would quantify over raw trees with a
partial interpret — the statement WEAKENS exactly where the formats
consume it (they want `Ty`-level round trips, not tree-level); the
printer's branch choice loses its typed discriminator. And the wall
this option dodges no longer exists: the landed folds' polymorphic
recursion compiles via the equation compiler's dependent motive
(Grammar.lean's header note: "the folds compile and the equations are
`rfl`").

**Option C — the fuel/height engine discipline (fuel = input length +
1; termination via the consumption lemma).** KEPT — it is the landed
discipline. Round two's refinement is the fuel ACCOUNTING inside
law 1: the flat `n + 1 ≤ fuel` invariant does not survive the `selfE`
crossing (the crossing decrements fuel on the SAME input — off by one
at equality). The answer is the guard-aware slack (§6.1): the premise
is `n + guardSlack g ≤ fuel` with `guardSlack g := if guardE g then 1
else 2`; guardedness (WF-FIX ⟹ `guardE body = true` via the parked
`firstE_some_guardE`) makes each crossing spend exactly the unit of
slack the guarded prefix's consumption bought — the parked header's
"node-local" phrase, formalized. This is where the proofs land: the
slack propagation is a per-node table (§6.5), each row a two-line
omega over the guard fold's definition.

**Option D — V1-without-fix (the non-recursive fragment first).**
INSUFFICIENT alone (the three targets are recursive — v1 §0.4) and
unneeded as scaffolding: the engine landed WITH `fix`. Its content
survives as the LANDING ORDER: the proof-of-life slice (§7) exercises
the recursive discipline on the smallest possible format before any
migration touches a byte-tied artifact.

**Decision: the landed GrammarE scheme stands.** Round two is the
laws' completion, not a re-design.

## 2. The Grammar's exact shape (pinned — the landed form + one delta)

The node set and the folds are PINNED as landed (see §0's file list;
the module headers carry the design notes). The deltas from v1 that
round one already paid, recorded so the next reader doesn't re-derive
them:

1. **`tailOk` is VALUE-DEPENDENT** (v1 §3.2 sketched `tailOk g sfx`
   value-free — wrong at `alt`: only the PRINTED branch's tail
   condition holds of the value). The landed `GrammarE.tailOkE`/
   `Grammar.tailOk` follow the printer's own discriminator (the
   `fixValueOk` closure), so branch agreement is by construction.
   Law 1's premise is `tailOk g x sfx = true`; §6.6 proves
   `tailOk g x [] = true` unconditionally, so whole-file runs keep
   v1's side-condition-free corollary.
2. **WF-OPT joined the row list** (Check.lean's header): an `opt`
   with a nullable body mis-parses `none`; law 1's none-case exclusion
   stands on it.
3. **WF-FIX is the triple** `firstE body ≠ none ∧ nullableE body =
   false ∧ tailSelfFreeE body = true` — the consumption lemma's
   premise, the guardedness, and the junction's once-unfold corner
   respectively.
4. **`Grammar : Type → Type 1`** (probe-verified against the landed
   toolchain). Consequence for 15 #1's packaging: `Kit.CheckedProp`'s
   field is `α : Type`, so `CheckedProp (Grammar R)` does not
   typecheck as v1 sketched. The fix: generalize `Kit.CheckedProp` to
   `CheckedProp.{u} (α : Type u)` — mechanical, backward-compatible
   (every current consumer instantiates `u := 0`), KitTests re-pins —
   then land `grammarPredictive` (§4.2). Fallback if the bump fights:
   ship the bare quadruple (P := Predictive, check := wfCheck, sound
   := wfCheck_sound, complete? := the .missing note in prose) and cite
   15 #1's SHAPE in the header — the discipline is the mandatory
   soundness + the loud completeness choice, not the structure literal.
5. **ONE engine delta this round: `Lexeme.head_ne : head.matches [] =
   false`** joins the leaf's law fields. Content: the tailOk-nil lemma
   (§6.6) needs every effective-first head to fail the empty text; the
   stop conjuncts (`optE none`, `repE`) quantify exactly those heads.
   For `cls` heads the field is `rfl`; for `lit s` it is `s ≠ ""` —
   an empty-literal lexeme is useless anyway (it matches every
   continuation, so no WF row would ever pass it against a sibling).
   Alternative considered and rejected: a computed WF-HEAD certificate
   row — the leaf is where the other seven laws live; the failure
   belongs at lexeme construction, not grammar check. Every library
   lexeme (§7, §8) discharges it by `rfl`/`simp`.

## 3. The derived parser and printer (landed; the totality discipline)

Pinned as landed; the discipline summary for the law proofs' sake:

- **Parse** (`parseE`/`parseG`/`parseManyE`/`parseManyG`): fuel +
  structural, lex measure `(fuel, sizeOf g, phase)`; `selfE` spends
  one fuel re-entering `sb`; the repetition engine spends one per
  iteration and has a zero-progress stop arm (dead for checked
  grammars — WF-REP-1 + `parseConsumeE`); the `selfE` fuel-0 arm is
  the dead "recursion limit" error (unreachable under the slack
  invariant, §6.5). Equation lemmas are the proofs' rewrite surface;
  the compiled code is what tests run (06 §2's wf-opacity rule is not
  triggered — the folds are structural, not `termination_by`-wf at the
  `decide` sites… the ONE explicit-measure site is the parse measure
  itself; no `decide` runs over it — certificate checks reduce the
  WF folds, never the parser).
- **Print** (`printWalk`/`printFixGo`/`printFix`/`printG`/`print`):
  total, premise-free; the `selfE` re-entry rides `AccD` CONSTRUCTED
  from the measure itself (`AccD.ofFuel m x (m x + 1)`); the walk
  threads `SelfPathE` derivations so the handler pays the carried
  decrease proof. The irrelevance lemmas (`printFixGo_irrel`,
  `fixValueOkGo_irrel`) + the one-step unfolds (`printFix_unfold`,
  `fixValueOk_unfold`) are the laws' entry points.
- **Run**: fuel = length + 1, offset 0, full-consumption-or-error.

## 4. The certificate (landed; `wfCheck_sound` survives)

### 4.1 The rows (pinned)

WF-ALT-1 (effective-first prefix freedom), WF-ALT-2 (no nullable
left), WF-SEQ-1 (tail-first stop determinism), WF-SEQ-2 (tail-munch
break), WF-REP-1 (progress), WF-REP-2 (the iteration self-junction),
WF-OPT (the body non-nullable), WF-FIX (the triple, §2.3). Decidable
shadows: `HeadSpec.disj` (lit/lit prefix-freedom; lit/cls head-char
check with the nonempty side condition; cls/cls conservative reject),
`HeadSpec.breaks` (nonempty literal head char fails the munch
predicate; cls reject).

### 4.2 The packaging

```lean sketch
/-- The CheckedProp row (15 #1), once `Kit.CheckedProp` is
    universe-polymorphic (§2.4). Sound PROVED; completeness LOUDLY
    .missing (cls/cls + the conservative corners — forever). -/
def Grammar.grammarPredictive : Kit.CheckedProp (Grammar R) where
  P := Grammar.Predictive
  check := Grammar.wfCheck
  sound := Grammar.wfCheck_sound
  complete? := .missing
```

Grammars outside the decidable fragment hand-prove `Predictive g` and
cite the same laws — the certificate is the decidable ROUTE to the
premise, never the premise (05 §1's contract).

### 4.3 The row→consumer table (the wall-1 lesson, made structural)

Wall 1 was a row family (`WF-SEQ-1/2`) whose LAW-SIDE consumer was
never specced. The leftover rule applied to the certificate: every row
names its consumer lemma; every leaf field likewise. A future row
without a row in this table is a design failure at review, not at
proof time.

| Row / field | Content | The consuming lemma |
|---|---|---|
| WF-ALT-1 | branch heads mutually exclusive | `parse_print_E` alt case (wrong-branch exclusion: `printBundle*` head + `disj_symm` + `parseExcludeE`) |
| WF-ALT-2 | no nullable left | the same (exclusion needs non-nullability) |
| WF-SEQ-1 | tail-stop heads disj continuation firsts | `junctionE` (the heads-fail conjuncts, §6.3) |
| WF-SEQ-2 | tail munches broken by continuation firsts | `junctionE` (the `atomE`/munch conjuncts) |
| WF-REP-1 | rep body non-nullable | `parseManyE_print` (the progress `if` is always true; the fuel invariant; per-element nonempty prints) |
| WF-REP-2 | the (a, a) self-junction rows | `parseManyE_print`'s per-element `junctionE a a` (§6.4) |
| WF-OPT | opt body non-nullable | `parse_print_E` opt-none case (`parseExcludeE`) |
| WF-FIX.first | `firstE body ≠ none` | `firstE_some_guardE` → the slack accounting; `effFirstE_bodyFirsts` |
| WF-FIX.nonnull | `nullableE body = false` | `parseConsumeE`'s `hn` (consumption across `selfE`) |
| WF-FIX.tailselffree | `tailSelfFreeE body` | `tailOkE_tok_irrel` (the selfE tail bridge), `bodyTailMunch_isSome`, `tailOk_nil` |
| `Lexeme.scan_exact`/`scan_off` | leaf exactness | `print_parse` (law 2) |
| `Lexeme.scan_post` | scanned values pass `pre` | law 2's `valueOk` conjunct |
| `Lexeme.scan_head` | success starts at the head | `parseHeadE`, `printBundle*` |
| `Lexeme.head_fail` | head mismatch ⟹ failure | `parseExcludeE` |
| `Lexeme.print_scan` | the print re-scans | `parse_print_E` atom case |
| `Lexeme.consumes` | success consumes ≥ 1 | `parseConsumeE` |
| `Lexeme.head_ne` (§2.5) | the head fails `[]` | `tailOk_nil` |
| `rel`'s `decode_owns`/`exact` | owned + canonical raws | law 2's rel case |
| `Kit.Codec.decode_encode` | `decode (encode x) = some x` | law 1's rel case |

## 5. Law 2 — print∘parse (the landed shape + the discovered premise)

The parked file's §3/§5c ARE the proof content; round two lands them
compiling. The statement (closed level):

```lean sketch
/-- THE exactness law (design §3.3): a successful parse consumed
    EXACTLY the print of its result. Premises: the branch-coherence
    fold ONLY — the round-one discovery: v1's "unconditional" claim
    is FALSE (two rel-branches whose codecs decode different spellings
    INTO the same value are first-disjoint, accepted, and
    exactness-false). `altCoherent` is semantic, not decidable; the
    migration targets discharge it by ctor discrimination (below). -/
theorem Grammar.print_parse {A : Type} :
    ∀ (g : Grammar A) (fuel : Nat), altCoherent g →
      ∀ {x : A} {cur cur' : Cursor},
      parseG g fuel cur = .ok (x, cur') →
      cur.cs = (printG g x).toList ++ cur'.cs ∧
      cur'.off = cur.off + (printG g x).length ∧
      valueOk g x = true
```

The `altCoherent` fold (parked §3): at each `alt a b`, the left-owning
values never satisfy the right branch (`∀ x, valueOk a x = true →
valueOk b x = false`), recursively. The discharge kit the formats
consume:

```lean sketch
/-- The ctor-discriminated coherence (the targets' shape): two
    rel-branches with disjoint `owns` are coherent. The format proves
    owns-disjointness by the AST's no-confusion; the valueOk-rel
    equation (`owns x && …`) does the rest. -/
theorem Grammar.altCoherent_alt_rel_rel … :
    (∀ x, owns₁ x = true → owns₂ x = false) →
    altCoherent (rel c₁ owns₁ … sub₁) → altCoherent (rel c₂ owns₂ … sub₂) →
    altCoherent (alt (rel c₁ owns₁ … sub₁) (rel c₂ owns₂ … sub₂))
```

The whole-file corollary (the canonicalization content, strict
fragment): `Grammar.print_run : g.run s = .ok x → g.print x = s` —
from `print_parse` + the run entry's full-consumption match. Formats
with a tolerant surface compose a named pre-pass (WIT's
`stripComments`) or a `Kit.Normalization` row (the snapshot's sort) —
unchanged from v1 §5.

## 6. Law 1 — parse∘print (the completion; the wall-1 resolution)

### 6.1 The statements

```lean sketch
/-- The guard-aware fuel slack: an UNGUARDED node (a `selfE` reachable
    without consumption) needs one extra unit; guarded nodes ride the
    input bound. WF-FIX makes every reachable re-entry guarded
    (`firstE_some_guardE`). -/
def GrammarE.guardSlack (g : GrammarE R A) : Nat := if guardE g then 1 else 2

/-- THE law, open level. STRONG induction on `fuel`, INNER structural
    induction on `g` (the parked law-2 architecture); the `selfE` case
    consumes the fuel-IH at `sb`. `tokStar` is the once-unfold closure
    `Grammar.tailOk`'s fix arm uses — the open statement takes it
    CONCRETELY (the open law is internal machinery; the closed law is
    the surface). -/
theorem GrammarE.parse_print_E {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x)
    (hpred : PredictiveE sb sb) (hn : sb.nullableE = false)
    (hf : sb.firstE ≠ none) (htf : sb.tailSelfFreeE = true) :
    ∀ (fuel : Nat) {A : Type} (g : GrammarE R A) (x : A) (k : Nat) (sfx : List Char),
    PredictiveE sb g →
    valueOkWalk g x (fun y _ => Grammar.fixValueOk m sb dec y) = true →
    tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) g x sfx = true →
    ((printWalk g x (fun y _ => Grammar.fixValueOk m sb dec y)
        (fun y _ => printFix m sb dec y)).toList ++ sfx).length
      + guardSlack g ≤ fuel →
    parseE sb g fuel ⟨k, (printWalk g x _ _).toList ++ sfx⟩
      = .ok (x, ⟨k + (printWalk g x _ _).length, sfx⟩)

/-- THE law, closed level (15 #2's append form). Strong induction on
    `fuel` generalizing `g` (mirroring the parked closed law 2); the
    fix arm delegates to `parse_print_E`. The slack is 1 at this
    level: `predictive_guard : Predictive g → guard g = true` (the fix
    case via `firstE_some_guardE`; fix-free grammars structurally). -/
theorem Grammar.parse_print (g : Grammar R) (hp : Predictive g)
    (x : R) (hx : valueOk g x = true)
    (fuel k : Nat) (sfx : List Char)
    (hfuel : ((g.print x).toList ++ sfx).length + 1 ≤ fuel)
    (hfol : tailOk g x sfx = true) :
    g.parse fuel ⟨k, (g.print x).toList ++ sfx⟩
      = .ok (x, ⟨k + (g.print x).length, sfx⟩)

/-- The corollary every format cites (05 §3's thin-wrapper rule). -/
theorem Grammar.run_print (g : Grammar R) (hp : Predictive g)
    (x : R) (hx : valueOk g x = true) :
    g.run (g.print x) = .ok x
```

### 6.2 The §0 additions (small hand lemmas, 01 §7's rung)

Beyond the parked §0 (`prefix_total`, `matches_append`, `disj_sound`,
`breaks_sound`, the `String` nonempty/append family):

- `HeadSpec.disj_symm : h1.disj h2 = h2.disj h1` — case bash (lit/lit
  prefix-or symmetric; lit/cls both directions the same conjuncts;
  cls/cls both false). Its semantic face:
  `SemDisj` symmetric — the junction's and the alt case's direction
  flip (the row gives `disj s1 s2`; the text exhibits `s2` matching;
  the conclusion needs `s1` failing).
- `GrammarE.firstE_head_ne` / the closed twin: under the lexemes'
  `head_ne` (§2.5), every head in `firstE g` fails `[]` (induction;
  the `none` cases vacuous). Corollaries: `bodyFirsts` heads fail
  `[]`; `effFirstE fs g` heads fail `[]` when `fs`'s do.
- `GrammarE.tailMunchE_isSome`: `(tm).isSome → (tailMunchE tm g).isSome`
  (plain induction — atoms are always `some`, the combinators
  preserve); and `bodyTailMunch_isSome : tailSelfFreeE sb = true →
  (bodyTailMunch sb).isSome` (the tail-consulted positions are
  self-free, so the `none` seed is never read). The junction's
  membership restrictions stand on these (a `getD []` quantification
  is vacuous unless the fold is known `some`).

### 6.3 THE JUNCTION FAMILY (the wall-1 lemma set, specified)

The seq-case need: law 1 at `seqE a b` parses `a` over
`printWalk a p ++ (printWalk b q ++ sfx)`; the IH wants
`tailOkE … a p (printWalk b q ++ sfx)`; the hypothesis gives
`tailOkE … b q sfx` (+, when `nullableE b`, `tailOkE … a p sfx`). The
junction lemma bridges: the certificate's (a, b) rows + b's value
discipline + the tail fold at `sfx` YIELD the tail fold for `a` at
the shifted suffix.

```lean sketch
/-- THE junction lemma, open level. Induction on `a` (the LEFT
    grammar; `b` is fixed). The two row premises are EXPLICIT
    quantified facts (not the `PredictiveE` bundle) so the induction
    can re-derive sub-junction rows from the outer row by
    list-membership restriction. `HSJ` is the `selfE`-leaf interface —
    the exact `printBundleE`/`printFixBundle` pattern (the HSB
    parameter): the open lemma is tok-agnostic; `junctionEG` pays it. -/
theorem GrammarE.junctionE {R : Type} (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x)
    (hn : sb.nullableE = false) (hf : sb.firstE ≠ none)
    (htf : sb.tailSelfFreeE = true) :
    {A B : Type} → (a : GrammarE R A) → (b : GrammarE R B) →
    (x : A) → (y : B) → (sfx : List Char) →
    PredictiveE sb a → PredictiveE sb b →
    (rowTF : ∀ s1 ∈ tailFirstE (bodyFirsts sb) (bodyTailFirsts sb) a,
      ∀ s2 ∈ effFirstE (bodyFirsts sb) b, HeadSpec.disj s1 s2 = true) →
    (rowTM : ∀ p ∈ (tailMunchE (bodyTailMunch sb) a).getD [],
      ∀ s2 ∈ effFirstE (bodyFirsts sb) b, s2.breaks p = true) →
    valueOkWalk b y (fun y _ => Grammar.fixValueOk m sb dec y) = true →
    tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) b y sfx = true →
    (HSJ : ∀ y' (path : SelfPathE a x y'),
      tokStar m sb dec y' ((printWalk b y _ _).toList ++ sfx) = true) →
    tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) a x
      ((printWalk b y _ _).toList ++ sfx) = true

/-- The fix-level junction instance: `junctionE` AT `a := sb`, the
    HSJ discharged by `AccD` recursion over the carried measure —
    each `selfE` leaf's value is measure-smaller (`dec`), so its own
    body-junction is the IH. EXACTLY `printFixBundle`'s shape
    (parked §1), one more AccD instance. The `fixValueOk` premise
    feeds the IH at the self-values (via `fixValueOk_unfold` +
    `valueOkWalk_selfE`). -/
theorem Grammar.junctionEG (m : R → Nat) (sb : GrammarE R R)
    (dec : ∀ x y, SelfPathE sb x y → m y < m x)
    (hpred : PredictiveE sb sb) (hn : sb.nullableE = false)
    (hf : sb.firstE ≠ none) (htf : sb.tailSelfFreeE = true) :
    ∀ x (acc : AccD m x), Grammar.fixValueOk m sb dec x = true →
    ∀ {B : Type} (b : GrammarE R B) (y : B) (sfx : List Char),
    PredictiveE sb b → [the (sb, b) row pair] →
    valueOkWalk b y _ = true → tailOkE … (tokStar m sb dec) b y sfx = true →
    tailOkE m sb dec (bodyFirsts sb) (tokStar m sb dec) sb x
      ((printWalk b y _ _).toList ++ sfx) = true

/-- The closed junction (law 1's closed seq case + the formats'
    face). Induction on the closed `a`; the fix arm unfolds
    `Grammar.tailOk`'s fix equation — the closed folds' fix arms ARE
    the once-unfold E-values with exactly the E-row parameters
    (the bridges are `rfl`-family, the `effFirst_fix` shape) — and
    delegates to `junctionEG`. No `selfE` case: closed grammars have
    none outside `fix`. -/
theorem Grammar.junctionG :
    {A B : Type} → (a : Grammar A) → (b : Grammar B) →
    Predictive a → Predictive b →
    (∀ s1 ∈ tailFirst a, ∀ s2 ∈ effFirst b, HeadSpec.disj s1 s2 = true) →
    (∀ p ∈ (tailMunch a).getD [], ∀ s2 ∈ effFirst b, s2.breaks p = true) →
    ∀ (x : A) (y : B) (sfx : List Char),
    valueOk a x = true → valueOk b y = true →
    tailOk b y sfx = true →
    tailOk a x ((printG b y).toList ++ sfx) = true
```

The `junctionE` per-node content (write `sfx'` for
`(printWalk b y _ _).toList ++ sfx`; every case splits on
`printWalk b y = ""` — EMPTY: `sfx' = sfx` definitionally, the
hypothesis's own `a`-side conjuncts close the goal; NONEMPTY: the
parked `printBundleE`'s head conjunct exhibits `h2 ∈ effFirstE … b`
matching `sfx'`, and the rows + `disj_symm`/`breaks_sound` transfer):

- **`atomE L`**: goal = the munch break at `sfx'.head?`. Empty: the
  hypothesis (the atom arm of the outer `tailOkE (seqE …)` — via the
  caller's tailOk; inside junctionE it is the `nullableE b` fallback
  conjunct… precisely: the caller supplies the a-side adequacy at
  `sfx` whenever `printWalk b y = ""` — see the note below). Nonempty:
  `rowTM` at `p ∈ L.munch.toList` (the atom's tail munch is exactly
  `some L.munch.toList`; the row's `getD` is real by
  `tailMunchE_isSome`) gives `h2.breaks p`; `breaks_sound` closes.
- **`seqE a₁ a₂`**: goal's first conjunct is the IH on `a₂` — rows
  restrict (`tailFirstE a₂ ⊆ tailFirstE (seqE a₁ a₂)` definitionally;
  the munch side via `tailMunchE_isSome` on both halves). The
  `nullableE a₂` second conjunct is the IH on `a₁` — the restriction
  uses the nullability: `tailFirstE a₁ ⊆ tailFirstE (seqE a₁ a₂)`
  exactly when `nullableE a₂` (the fold's `if` — and the `if`'s
  condition IS the case hypothesis).
- **`altE a₁ a₂`**: the branch discriminator (`valueOkWalk a₁ x …`)
  is THE SAME in hypothesis and goal — branch agreement definitional.
  Printed-left: IH `a₁`. Printed-right: IH `a₂` for the main conjunct;
  the `nullableE a₂` sub-conjunct (`effFirstE fs a₁` all fail `sfx'`):
  empty — the hypothesis's own conjunct; nonempty — `tailFirstE
  (altE a₁ a₂) ⊇ effFirstE fs a₁` under `nullableE a₂` (the fold's
  third clause), `rowTF` + `disj_symm`.
- **`repE a₁`**: conjunct 1 (`effFirstE fs a₁` all fail `sfx'`): empty —
  the hypothesis's first conjunct; nonempty — `tailFirstE (repE a₁) ⊇
  effFirstE fs a₁` + `rowTF` + `disj_symm`. Conjunct 2: per-element
  IH `a₁` (rows: `tailMunchE (repE a₁) = tailMunchE a₁`;
  `tailFirstE a₁ ⊆ tailFirstE (repE a₁)`).
- **`optE`**: `some z` — IH `a₁`. `none` — the heads-fail conjunct as
  in `repE`'s conjunct 1 (`tailFirstE (optE a₁) ⊇ effFirstE fs a₁`).
- **`labelE`/`relE`**: IH (`relE` shifts the a-side value across
  `m.encode`; the b-side premises are untouched).
- **`selfE`**: `HSJ x (.selfP x)`.

The caller-side note (the seq case's empty-print reading): law 1's
seq hypothesis `tailOkE (seqE a b) (p,q) sfx` unfolds to
`tailOkE b q sfx && (nullableE b → tailOkE a p sfx)` — when
`printWalk b q = ""`, `nullableE b = true` is NOT derivable from
emptiness (a non-nullable grammar never prints empty — the parked
bundle's first conjunct — but emptiness does not imply nullability);
the junction's empty branch does not NEED it: `sfx' = sfx`, and the
goal `tailOkE a p sfx'` … — CAREFUL: the goal is `tailOkE a p sfx'`
with `sfx' = sfx`, and the hypothesis gives `tailOkE a p sfx` ONLY
under `nullableE b`. Two sub-cases repair this: if `nullableE b =
true`, the hypothesis's second conjunct fires and the empty branch is
the hypothesis directly; if `nullableE b = false`, the parked bundle's
first conjunct gives `printWalk b q ≠ ""` — the empty branch is
VACUOUS. So the junction carries `nullableE b = true → tailOkE … a p
sfx = true` as an additional hypothesis (the caller's exact second
conjunct), and case-splits on `nullableE b` BEFORE the empty/nonempty
split. This is the one non-obvious plumbing point of the family —
write it into the lemma's hypothesis list, not into a proof comment.

### 6.4 The repetition engine lemma (inside `parse_print_E`'s repE case)

A LOCAL induction on the engine fuel, exactly the parked law-2's repE
shape — including the `f + 1 = F ∨ f + 1 < F` split (at equality the
body parse fact comes from the structural `a`-IH; below it, from the
outer fuel-IH). Statement (local `have`, quantified over the engine
fuel `f`, the remaining list, the cursor):

```lean sketch
have parseManyE_print : ∀ f ys c, c.cs.length + guardSlack a ≤ f →
    c.cs = (printList ys (fun z hz => printWalk a z _ _)).toList ++ sfx →
    (∀ z hz, valueOkWalk a z _ = true) →
    (∀ z hz, tailOkE … a z ((printList (ys.dropAfter z) _).toList ++ sfx) = true) →
    ((effFirstE (bodyFirsts sb) a).all (fun h => !h.matches sfx)) = true →
    parseManyE sb a f c = .ok (ys, ⟨c.off + (printList ys _).length, sfx⟩)
```

- The per-element shifted tailOk premise is produced ONCE at the
  call site by list induction with `junctionE a a` per step — THIS is
  what WF-REP-2 exists for (the certificate's self-junction rows are
  exactly the `(a, a)` row pair the junction consumes).
- The engine invariant is `n + guardSlack a ≤ f` (NOT `f + 1`): the
  engine at `f' + 1` calls the body at fuel `f' + 1` (needs
  `n + slack ≤ f' + 1` — the invariant exactly), progress
  (`parseConsumeE` + WF-REP-1) gives `n' ≤ n - 1` for the recursive
  call at `f'` (needs `n' + slack ≤ f'` ✓ by omega).
- The stop: with `ys` exhausted the body parse on `sfx` fails —
  `parseExcludeE` (WF-REP-1's non-nullability + the heads-fail
  premise, the `tailOkE (repE a)` first conjunct) — the engine
  returns `([], c)`; the offsets/values assemble by the parked
  family (`printList`/`allWalk` congruence lemmas).
- The `f = 0` arm: with `ys` nonempty the invariant is contradictory
  (each element print is nonempty — the parked bundle's first
  conjunct under WF-REP-1 — so `n ≥ 1` against `n + slack ≤ 0`); with
  `ys = []` the engine's `[]` return is already the goal. Fuel
  exhaustion therefore never corrupts the result — the v1 §3.4
  "fuel-sufficiency paid once, generically" claim, made precise.

### 6.5 `parse_print_E` per-node (the case table)

Induction: strong on `fuel` (the parked law-2's `Nat.strongRecOn`
shape), inner structural on `g`. Write `n` for the input length
`((printWalk g x _ _).toList ++ sfx).length`; the fuel premise is
`n + guardSlack g ≤ fuel`.

| Case | The parse step | The premises consumed | The slack propagation |
|---|---|---|---|
| `atomE L` | `L.print_scan` | `valueOkWalk` (= `L.pre x`), `tailOkE` (= the munch break at `sfx`) | none needed |
| `seqE a b` | parse `a` (IH), then `b` (IH); assemble by append-assoc | `junctionE a b` for a's shifted tailOk (§6.3, with the caller-side note); the b tailOk from the hypothesis | a: `guardSlack a ≤ guardSlack (seqE a b)` (guardE false propagates left-to-right); b: if `guardSlack b = 2 ∧ guardSlack (seqE) = 1` then `guardE b = false ∧ nullableE a = false` (the guard fold's def) so a consumed ≥ 1 (`parseConsumeE` + `hn`) and `n₁ + 2 ≤ n + 1 ≤ fuel` |
| `altE a b` | left printed: IH, orElse short-circuits. right printed: `a` FAILS, then IH b | the failure: WF-ALT-2 (`nullableE a = false`) + `parseExcludeE`; the heads-fail: `printBundle*`'s head of the b-print (nonempty — WF-ALT-2 is about `a`; `b`'s emptiness sub-case: `sfx' = sfx` and the VALUE-DEPENDENT `tailOkE` alt clause's own `effFirstE fs a`-fail conjunct — §2.1's delta pays here) + WF-ALT-1 + `disj_symm` | branches: `guardE (altE) = guardE a && guardE b` — each branch's slack ≤ the alt's |
| `repE a` | `parseManyE_print` (§6.4) | WF-REP-1/2 | `guardE (repE a) = guardE a` — the engine invariant at `F` is the case premise |
| `optE a` | `some`: IH. `none`: the body FAILS on `sfx`, return `none` at the same cursor | WF-OPT (`nullableE a = false`) + `parseExcludeE` (heads-fail from the `tailOkE` opt-none conjunct) | `guardE (optE a) = guardE a` |
| `labelE n a` | IH (the error map is success-transparent) | — | guardE delegates |
| `relE m …` | IH at `m.encode x`, then `m.decode (m.encode x) = some x` | `Kit.Codec.decode_encode`; the tailOk/valueOk pass through `encode` definitionally | guardE delegates |
| `selfE` | the fuel-IH at `sb` | premise transfer: `printFix_unfold` (the length is unchanged), `fixValueOk_unfold` (the valueOk), `tailOkE_tok_irrel htf` (the tailOk: `tokStar x sfx` IS `tailOkE …(fun _ _ => false)… sb x sfx`, rewritten to the `tokStar` version) | `guardSlack selfE = 2` gives `n + 2 ≤ f + 1`, i.e. `n + 1 ≤ f`; `sb` is guarded (`firstE_some_guardE hf`), so the fuel-IH's premise is `n + 1 ≤ f` — EXACTLY met. The dead fuel-0 arm: the premise is `n + 2 ≤ 0`, omega-false |

### 6.6 The closed law and the run corollary

`Grammar.parse_print`: strong fuel induction generalizing `g`; the
non-fix cases mirror §6.5 through the closed family (parked §5's
`printBundleG`/`parseExcludeG`/`parseConsumeG` + §6.3's `junctionG`);
the fix case delegates to `parse_print_E` (the premises are the
`Predictive` fix row's fields; `guardSlack`-1 via
`predictive_guard`).

`Grammar.run_print`: `parse_print` at `sfx := []`, fuel `= length + 1`,
then the run entry's full-consumption match. The side condition is
discharged by:

```lean sketch
/-- The empty suffix is always an adequate tail. The `optE none` /
    `repE` stop conjuncts need every effective-first head to fail
    `[]` — the `head_ne` family (§6.2). The fix arm: `tokStar` at `[]`
    is the body's own `tailOkE … []` with the DEAD tok — `tailSelfFreeE`
    makes the tok irrelevant (`tailOkE_tok_irrel` against the trivial
    `fun _ _ => true`), so the open lemma applies with no AccD
    recursion. -/
theorem Grammar.tailOk_nil (g : Grammar R) (x : R) : tailOk g x [] = true
```

## 7. The proof-of-life slice (lands FIRST)

The smallest end-to-end exercise of the full discipline — one tiny
RECURSIVE format through grammar → certificate → both laws → run
round-trips → negative controls — BEFORE any byte-tied migration.
Home: `TextKitTests` (a fixture, not a format; no artifact pins).

- **The format**: `PTree := leaf | node PTree`; the text: `"x" | "("
  PTree ")"`. The grammar:

```lean sketch
/-- The slice grammar: ONE binder, one self, two rel arms over a
    punct/atom spine. Exercises: fix (the AccD printer + the fuel
    parser), alt (the branch exclusion), seq WITH a selfE left of a
    literal (the junction against `")"` — real junction content),
    rel (the codec rows), the certificate's WF-FIX/WF-ALT-1 rows. -/
def ptreeGrammar : Grammar PTree :=
  .fix PTree.depth
    (.altE (.relE leafCodec … (.atomE xLex))
           (.relE nodeCodec … (.seqE (punctE "(") (.seqE .selfE (punctE ")")))))
    ptreeDecreases
```

  with `PTree.depth` the carried measure and `ptreeDecreases` the
  `SelfPathE`-inversion + `simp [leafCodec, nodeCodec]; omega`-scale
  decreases proof (the self-values are the ctor's direct children
  inside `encode`'s output — §8.2's per-format pattern, at minimal
  size).
- **The lexeme rows the slice forces** (the leftover rule at the
  library level): `TextKit/Grammar/Lexemes.lean` lands with EXACTLY
  `lit` (a bare literal lexeme) + the derived `punct`/`punctE` rows
  (the `unitCodec` pattern, v1 §1.2) + the unit/ctor codecs the arms
  need. `kwLit`/`nameLex`/`natLex` land with their migrations (§8) —
  never ahead.
- **The certificate discharge**: `wfCheck ptreeGrammar = true` at the
  discharge site (06 §7's build-time `#guard`; the folds are
  structural, so `decide` reduces — if the kernel balks, the
  specialized reduction lemma per 06 §2, never a silent
  `native_decide` outside the axiom gate's disclosed list).
  Hand-checks the fixture SHOULD pass (the review's arithmetic):
  WF-ALT-1: `lit "x"` vs `lit "("` prefix-free ✓; WF-FIX: firstE =
  `[x, (]` ≠ none, body non-nullable, tail-self-free (the selfE is
  left of the non-nullable `")"`) ✓; the WF-SEQ rows are vacuous
  (empty tailMunches, empty tailFirsts at the literal junctions) ✓.
- **The pins**: `run (print t) = .ok t` on a depth-3 value battery
  (the tests run the COMPILED parser); `print (run s) = s` on the
  accepted texts; the law instantiations type-check
  (`PTree.run_print := Grammar.run_print ptreeGrammar (wfCheck_sound
  …) …`, `PTree.print_run := …`); the `altCoherent` discharge is
  `altCoherent_alt_rel_rel` + `PTree.node.noConfusion`-scale
  owns-disjointness; TextKitTests.Axioms pins `#print axioms` of both
  law instantiations (core triple only).
- **The negative controls** (15 #5, the certificate's teeth — each a
  sabotaged sibling grammar failing `wfCheck` with the NAMED row):
  unguarded body (`selfE` in first position) → `WF-FIX`; colliding
  alt heads (two `"("` branches) → `WF-ALT-1`; a nullable left branch
  → `WF-ALT-2`; a nullable `rep` body → `WF-REP-1`; a seq whose left
  tail-munch survives the right's head (a `takeWhile`-class lexeme
  against a same-class continuation — forces the one `munch`-carrying
  test lexeme) → `WF-SEQ-2`; a nullable `opt` body → `WF-OPT`. Plus
  the law-level control: a grammar with coherent-false rel branches
  (two codecs decoding different spellings into one value) passes
  `wfCheck` yet its `print_parse` instance does not typecheck — the
  premise's teeth, pinned as a `guard_msgs` elaboration failure or a
  comment-documented non-instance (the honest negative for a
  Prop premise).

## 8. The migration plan (the three formats; the byte-ties hold)

THE BYTE-TIE DISCIPLINE (unchanged from v1 §5): the committed
artifacts — `notes/code-registry.txt`, `notes/universe.snapshot`,
`gen/schema-slice.wit` — MUST NOT change; `code-registry-check`,
`snapshot-check`, `gen-check` stay green with ZERO re-baseline. Test
error-text pins may update (tests, not artifacts) — each named in its
migration commit. Order: CodeRegistry → Snapshot → Wit.Parse (the
slice §7 retires v1's "validate the core before fix exists" motive;
the order is now by BYTE-TIE risk alone). One vertical slice per
migration: grammar value + lexeme/codec rows + certificate discharge +
the `altCoherent` discharge + the entry-point swap + gates green.
Per-format NEW content beyond v1 §5 (the round-two rows): the fix
measure + decreases (recursive formats), the coherence discharge.

### 8.1 `kit/Kit/CodeRegistry.lean` (first; recursion-free)

As v1 §5.1. Grammar: `rep` of the row grammar (alt tombstone/live),
`label`ed for the Diags. Dies/stays as v1. No fix, no coherence
premise of note (the row alt's branches are `owns`-disjoint by the
`-` head — actually first-DISJOINT, and the coherence is the
kit-level `altCoherent_alt_rel_rel` or a direct two-line fold proof).
`declare_format` lands HERE with its first consumer (the thin
wrappers: `CodeRegistry.parse/print/run_print/print_run` + the
`Kit.Codec` row, each `@[derived]`, each a one-line specialization).

### 8.2 `schemacore/SchemaCore/Snapshot.lean` (second; recursion + a sort)

As v1 §5.2, plus the recursion rows: the ty grammar is
`fix tyDepth body …` with `body` the alt of the seven arms
(bool/u64/i64/string atoms; option/list/result/map/set as
`rel`-over-`seq` spines with `selfE` payloads); the decreases proof:
`SelfPathE` inversion reaches only direct ctor children of
`encode`'s output — `simp [the arm codecs]; omega`. Coherence: the
seven arms' `owns` are the Ty ctor discriminators — pairwise
disjoint by no-confusion, discharged through
`altCoherent_alt_rel_rel` (six iterated instances). The old law
family (`parseTy_tyText`…), the fuel plumbing, and the length family
DIE (the generic theorems + the §6.4 fuel invariant subsume them);
`natText`'s theorem content ports INTO `natLex.print_scan` (the
lexeme's law field, not a free theorem). The acceptance note stands:
`natLex` rejects leading-zero caps the old `scanNat` accepted —
accepted-set tightening, zero artifact drift.

### 8.3 `wit/Wit/Parse.lean` (third; the richest surface)

As v1 §5.3: `stripComments` stays the NAMED pre-pass (the format law
is `Render.package p = stripComments s`, composed from `print_run` +
the strip's own row); the nodup deciders live in the rel codecs'
`decode`. The ty grammar exercises the full row set: `fix` (measure
= the Ty depth), `rep` (fields/records/interfaces), the keyword
lexemes (`kwLit` IS the `atomArm` discipline — the post-keyword munch
guard), the four-deep continuation dispatch as WF-SEQ-1 rows
(`"\n    "` vs `"\n  }"` prefix-freedom — decidable, discharged by
`wfCheck`, replacing the hand-rolled lookahead). Coherence: the eight
ty arms' ctor discriminators, as §8.2. `Wit.Render`'s functions are
replaced by the derived printer — the artifact pin proves the bytes.

## 9. The honest boundaries

- **One binder, no mutual recursion.** The `fix`/`selfE` pair is
  single-binder dynamic scoping (nested `fix` would need `GrammarE`'s
  `fixE`/`embedE` — deliberately absent, the leftover rule). The
  registry (option A) enters with the first mutually recursive
  consumer, on the written entry condition (§1).
- **The decidable fragment's conservative corners** (unchanged from
  v1 §7, now with the landed rows): cls/cls head disjointness
  (rejected; `complete? := .missing` forever); nullable left branches;
  unguarded/left-recursive `selfE`; tail-self-deep bodies
  (`tailSelfFreeE` rejects grammars whose TAIL folds would need a
  second unfold — no target needs it). The wall behind them:
  language disjointness of general grammars is undecidable; the
  certificate is a decidable SUFFICIENT condition and says so in its
  type.
- **`altCoherent` is a semantic premise, not a checkable row** (the
  round-one discovery): codec equality on values is undecidable in
  general; the targets discharge it by ctor discrimination (§5's
  kit). A format whose branches genuinely overlap in value space is
  OUTSIDE law 2 — loudly, at the premise.
- **What stays hand** (unchanged): the per-format `rel` codec rows
  (semantic mappings are format content); the per-recursive-format
  measure + decreases proof; canonicalization beyond exactness
  (sorts, comment strips — `Kit.Normalization` rows composed per
  format); the write-side name disciplines as lexeme `pre`s.
- **No lexer level** (unchanged, v1 §7): char-level lexemes +
  munch-as-data + WF-SEQ-2; no token stream, no second cursor space.
- **The boundary that must not blur** (05 §1, verbatim intent): the
  round-trip laws prove TEXTUAL agreement. The emitted artifact's
  semantics is a separate theorem (the correspondence lane).

## 10. What lands (the build rows, in dependency order)

| # | Module / change | Content | Doctrine slot |
|---|---|---|---|
| 1 | `Kit/CheckedProp.lean` | universe-polymorphic `CheckedProp.{u}` (§2.4) + KitTests re-pin | 15 #1 |
| 2 | `TextKit/Grammar.lean` | `Lexeme.head_ne` field (§2.5) + the two lexeme constructions' discharge | the leaf discipline |
| 3 | `TextKit/Grammar/Laws.lean` (NEW, non-module like its siblings) | the parked file LANDED GREEN: §0 lemmas + `disj_symm`, the print-bundle family, the parse duals, law 2 open+closed under `altCoherent` | 15 #2 |
| 4 | Laws.lean (cont.) | §6.2's folds-lemmas + the JUNCTION family (`junctionE`/`junctionEG`/`junctionG`) + `parse_print_E`/`parse_print`/`run_print` + `tailOk_nil` + `predictive_guard` + the `altCoherent` discharge kit | 15 #2 · 06 §6 |
| 5 | `TextKit/Grammar.lean` or Check.lean | `grammarPredictive` (§4.2) | 15 #1 |
| 6 | `TextKit/Grammar/Lexemes.lean` (NEW) | `lit` + `punct`/`punctE` + the slice's codecs (§7); `kwLit`/`nameLex`/`natLex` with their migrations (§8) | the token discipline |
| 7 | `TextKitTests` | THE PROOF-OF-LIFE SLICE (§7): the ptree fixture end-to-end + the negative controls + the axiom pins | 15 #5 |
| 8 | The migrations (§8 order) | per format: grammar + rows + discharges + entry swap + `declare_format` (first consumer: CodeRegistry) + gates green | 05 §3 |

Rows 1–7 are this round's core; row 8's migrations are the consumers
that prove the layer (05 §5's acceptance gate: a new text format = a
Grammar value + golden rows). `dsl!` stays deferred to its first DSL
consumer (07 R4; none of the three migrations is a DSL surface).

Verification per row: `just build` after every declaration (the
mandate's compile-after-every-declaration rule); `just gates` green at
each row boundary; NEVER a re-baseline mid-order (the axiom-report
drift rule) — the laws land on the core triple alone, pinned by
TextKitTests.Axioms.
