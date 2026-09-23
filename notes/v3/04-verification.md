# 04 — Verification: the ladder, obligations, certificates, observers

## 1. The proof ladder (the location of correctness)

Apply to every invariant; the highest working rung wins; lower rungs
carry a written reason:

1. **Unrepresentable** — the illegal state has no constructor (indexed
   types, dependent payloads, Fin-indexed codes).
2. **No-instance** — legality by instance search (a misspelled field is
   a missing instance = an elaboration error).
3. **Defaulted proof field** — `p : P := by decide` inside the
   structure: construction discharges the invariant.
4. **Generated theorem** — the deriving/family! machinery emits the
   proof from a table.
5. **Disclosed native_decide** — heavy decidable judgments in the
   kernel; the disclosure is itself a gate row.
6. **Hand theorem** — relational content the type system can't compute
   (fixpoints, perturbations) — written ONCE at the structure, cited
   everywhere after. A small generic handwritten lemma that retires a
   thousand generated ground proofs is the PREFERRED foundation — the
   ladder ranks the location of correctness, never the count of
   handwritten proofs.

A hand theorem below rung 4 without a written reason is a review
failure; an invariant checked only by a test is a violation.

## 2. Obligations (the checkable-fact substrate)

One shape: label + computed tier + payload + provenance + evidence.
The tier set is CLOSED; the evidence kinds are CLOSED:

```lean
inductive Tier where
  | provedAtElab | decidableNow | generatedCheck | oracleSwept | guestVerified
inductive Evidence where
  | citedProof (thm : Name) | decided (result : Bool)
  | generatedCheck (artifact fn : String) | oracleRow (ref : String)
  | witnessRef (…)
```

A row whose evidence's tier mismatches its obligation's tier fails
construction — armed-but-unfired is unrepresentable for registered rows.
An obligation with no discharge path is a LOUD gap (a value), never a
comment. The backends (decideEvidence/decideDischarge) live once in the
kit; lanes instantiate.

## 3. Certificates: untrusted search, small verified checker

The strongest architecture, adopted wholesale: an untrusted producer
(analyzer, optimizer, planner, search) generates a candidate + a
certificate; a small verified checker validates. Applications: solver
certificates, reachability certificates, inductive-invariant discovery,
optimization rewrite traces, translation validation, refinement
witnesses, abstract-interpretation results.

**The rule (the corrected R11): no duplicate semantic authority.**
Generated evidence is allowed — independently checked against the
authoritative declaration. Generation describes origin, not logical
strength; a generated proof term checked by the kernel is not less
trustworthy than a handwritten one. What stays forbidden: a verification
ARTIFACT as a second authority (a certificate file nobody re-checks).

## 4. The observer parameter

"Same behavior" is meaningless without naming the observer. Every
equivalence/refinement claim carries one:

```lean
structure Observer where
  see : Execution → Observation

-- the standard hierarchy:
apiObs        -- return values + public errors
auditObs      -- + committed events
perfObs       -- + resource costs
securityObs p -- what principal p can see
```

Instrumentation preserves API semantics without pretending logs are
unchanged; cache correctness ignores hits, preserves outputs; retry
correctness hides attempts, keeps visible charges; compiler correctness
states exactly whether traps/divergence/errors are in the observation.
The duel, the witness lane, and the skew checks all name their observer.

## 5. Feasibility (spec sanity)

An inconsistent contract holds vacuously and proves nothing:
`requires balance < 0 ∧ balance ≥ 0` admits every implementation. Every
spec layer answers the feasibility obligations: an admissible initial
state exists; the operation has valid inputs; the assumptions permit an
environment; the implementation can make required progress; the
generator reaches its intended cases. Finite fragments decide; larger
fragments accept witnesses or explicit impossibility proofs. Emptiness
is sometimes intentional — then it's DECLARED, never mistaken for
success. The spec-sanity report is a gate row.

## 6. The kernel sweep + the trust axes

The pure-Lean kernel (lean4lean) replays the gated libraries every run.
Its blind spots are documented, not silent: structure-field defaults,
`example`s, files outside the gated roots get no replay. A re-baseline
that changes content is a deliberate act (`--write --accept-drift`),
never a quiet write.

Trust has FOUR axes — keep them distinct; a claim's trust dependencies
are computed from its evidence chain:

| Axis | Values |
|---|---|
| evidence strength | universal proof / bounded proof / sampled test |
| production method | handwritten / derived / solver-produced |
| checker (the trusted base) | the kernel / native evaluation / compiled verifier |
| assumptions | environment fairness, hash assumptions, handler contracts |

`oracleSwept` means tested agreement (a regression), never a universal
theorem over unbounded inputs. The verdict vocabulary is ctors, never
strings; bounded exploration answers proved/refuted/unknown-with-reason.

## 7. The portable verifier, stated honestly

An artifact shipping data + witness + the compiled checker is portable
VERIFICATION, not automatic security: an attacker could ship an
"always-accept" checker. The consumer pins the checker's identity
(a real digest — not a bare UInt64) and the claim's semantics. Two
embedders agreeing proves tested portability, not checker soundness or
compiler correctness — the doc says which.

## 8. The acceptance shape of a correctness claim

A claim lands with: its highest ladder rung, its evidence (cited /
decided / disclosed / generated-and-checked), its E-code, its observer,
its feasibility note where vacuity is possible, its Spec rows (positive
+ negative + the vacuity tripwire), its duel rows where a semantics is
involved, and its 07 recipe entry. Claims are obligations; obligations
are data; the gates run the data (09).
