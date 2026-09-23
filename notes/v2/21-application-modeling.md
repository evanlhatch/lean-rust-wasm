# 21 — Application modeling: effects completed + the tabular layer + trust

The roots hold (20). This doc strengthens the INSTANCES: (a) the effect
kernel gains failure + linearity axes (one closed extension), (b) the
tabular/data layer gains the classic DB semantics (certified rewrites,
windows, indexed tables, the TVL reference), and (c) one conceptual
primitive is added: the TRUST DOMAIN (who attests, and how much we trust
them — as data).

## 1. The effect kernel completed (extend 12 §1; closed extension)

```lean
inductive Effect where
  | read   (name : String)
  | write  (name : String)
  | guestCap (c : Capability)
  | fail   (k : ErrorKind)     -- NEW: a fault this fn may raise (E-code kinds)
  | consume (r : ResourceId)   -- NEW: linear/affine — use exactly once (oneshot, stream, handle)
  | clock                     -- NEW: reads the world (FuncSem.volatile in the lattice)
  | hostIO
  | observe                   -- NEW: emits spans (observability as a read-capability)

-- the ERROR ROW: which faults a fn may raise, closed over the E-code universe
def raisesOf (sig : FuncSig) : List ErrorKind   -- derived from the ret type/registry
-- compose = union (read+write=fail-union, etc.); the boundary gate checks:
--   a call site may only observe failures its callee DECLARED (04 §4).
```

- `raises` closes the effects↔faults loop: the error channel is part of
  "what may happen"; the duel replays the declared surface; a fn that can
  raise an undeclared kind is an elaboration error (the E-code registry is
  the closed kind set).
- `consume` makes "use a one-shot twice" / "reopen a stream" unrepresentable
  at the boundary (the mpsc/oneshot/session machinery are its semantics).
- Wire/guest/decide layers consume the canonical rep, never the theory
  objects (09 §2).

## 2. The tabular layer (instance library over the roots)

The relational algebra already exists (dbsp.Relational: union/map/filter/
product/join/groupBy/intersect/difference over Z-sets, all proved). The
missing pieces:

```lean
-- 2.1 CERTIFIED REWRITES (the optimizer license)
-- each rule is an `equiv` theorem over the proven denotation:
theorem join_assoc   : equiv (Q1 ⋈ Q2) ⋈ Q3   ... (the associativity/license)
theorem filter_push  : filter p (join a b) = join (filter p a) b   (with the
                     -- predicate-safety condition = a Statement)
-- the optimizer = a rewrite SEQUENCE with a certificate; optimized plans are
-- provably semantics-preserving (the Calcite/TiDB formalization, as an
-- instance of the Change/TraceModel theory).

-- 2.2 WINDOW/ORDER semantics (the honest, order-aware fragment)
structure Window (order : keys) where ...
-- rank/lag over ordered partitions; order-dependence is NAMED (the
-- non-incrementalizable fragment is stated, using the ordering lane) —
-- never a silent assumption.

-- 2.3 INDEXED canonical tables (the data-structure side)
-- the KeyTy total order (17 product #1 canonical form) + RANGE-QUERY
-- semantics: access by key-range is a DEFINED operation (not just the
-- algebraic operators) — the "index" is a canonical rep, the query is a
-- fold over it.

-- 2.4 THE TVL REFERENCE (SQL three-valued logic)
-- nullable filters/aggregates: ONE reference reading for the data plane —
-- "keep/drop/unknown" is a fixpoint of the duel, and the compiled
-- evaluators compare against it. We have the nullability machinery; make it
-- the canonical reference (duel rows cite it).
```

## 3. Transactions as an instance (NOT a new root)

```lean
structure Transaction where
  batch : List Update       -- applied atomically (the batch law)
  commit : Unit → State     -- the batch application (proved atomic by applySeq laws)
  rollback : State → State  -- ChangeInversion (proved: revert restores)
-- atomicity = the batch law; rollback = invert — both ALREADY proved;
-- the transaction's certificate is CITED, never re-proved.
```

## 4. The trust domain (the conceptual primitive)

Every obligation/claim/artifact carries its trust-domain; the TCB table is
the set of domains a claim depends on; "is this trustworthy" is a QUERY.

```lean
inductive TrustDomain where
  | kernelProved   -- the C++ kernel independently rechecked (lean4lean)
  | decide         -- decided in the kernel
  | nativeDecide   -- disclosed trust base (gate row)
  | generated      -- family!/deriving emitted
  | guestVerified  -- the guest re-checks in-sandbox (the tier WE have)
  | oracleSwept    -- differential coverage, regression not proof

structure Attestation where
  claim    : Statement
  domain   : TrustDomain
  evidence : Obligation.Evidence
  tcb      : List TrustDomain     -- the honesty set this claim's truth depends on
```

- The E-code universe keys the attestations (04 §4).
- "Do we trust this artifact's claim?" = resolve its domain chain against
  the TCB — data, not judgment; the guestVerified tier is the domain that's
  genuinely ours.

## 5. Acceptance

1. A guest fn's `raises` row matches what its duel rows exercise; an
   undeclared fault in a call path is an elaboration error.
2. A one-shot boundary consumed twice fails construction (the `consume`
   axis); a stream's closure is affine.
3. Two equivalent join plans differ only by certified rewrites — the
   optimizer's output cites the license theorem; a rewrite without its
   citation is a review finding.
4. A transaction's commit/rollback certificate cites the batch + inversion
   laws (no new proofs); the TVL filter semantics agree with the duel rows.
5. Every obligation carries its trust-domain; the TCB table is the audit
   surface — the gates and the inspector list "this claim rests on:
   kernelProved + decide", computably.

## Guard rules

- The effect kernel extension is CLOSED (new axes are additive enum cases,
  not open strings); wire/guest layers consume canonical reps.
- Certified rewrites apply only where the license theorem covers the shape —
  an unlicensed rewrite is a finding, never a silent optimization.
- Indexed access and windows are DEFINED semantics, not heuristics; the
  non-incrementalizable fragment of windows is stated (ordering lane).
- Trust domains are closed; the TCB is data; exotic domains need a gate row.
