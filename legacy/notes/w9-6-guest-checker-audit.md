# W9.6 — the guest checker compile: audit record (STOP with the gap list)

Date: 2026-09-17. Order: notes/design-guest-verified.md W9.6 ("the
checker compiles to wasm"). Outcome: **the design-doc's step-4 exit —
the backend cannot compile the checker yet; this file IS the precise
gap report.** Nothing was shrunk, excluded, or hand-listed to force it
through (the order's recipe note governs: report, don't shrink).

## What was audited and how

`SchemaLang.WitnessCheck`'s guest-marked decls (`lookupU64?`,
`lookupString?`, `evalWU64?`, `evalWBool?`, `checkStepProof`,
`checkSteps`, `checkWitness`, `checkWitnessArtifact`, `verifyWitness`
— all `@[guest_std]`, W9.2) were run through the wasm-backend's
compiler line: the marks ride the manifest fold's import closure
(`GuestlangStd → Demo → SchemaLang.WitnessSpec → SchemaLang.WitnessCheck`),
so adding nothing, `lake exe wasm-gen` already pulls them into
`targetDeclsOf`. The LCNF re-run's final decls were dumped (the
GenMain x-ray) and the emission attempted.

**Observed:** `lake exe wasm-gen` currently FAILS for the whole demo
pipeline — `uncaught exception: WasmBackend: unsupported construct:
Perceus reset/reuse/isShared` — because the checker's decls are in the
compile set. This means `just wasm-compile` has been red since the
W9.2 marks landed (not a gate row, so `just gates` stayed green on
stale `target/` artifacts; the byte-tied surfaces — `demo-world.wit`,
`src/observability_generated.rs` — are unaffected).

**Observed:** the elaboration-time gate (`@[guest_std]`, the
LintKit.GuestBan check) PASSES the whole closure — the linter surface
(match-only Nat, String BEq, `string_len`) is in. The gap is entirely
between the linter's surface and the BACKEND's lowering capability.

## The gap list (each observed in the LCNF x-ray, not inferred)

1. **Nat is unlowerable (the fundamental gap).** The checker's fuel
   model is `Nat` (the design doc's §2.3 "match-only Nat — fuel
   decrement is legal"). The backend throws on `Nat.lit` ("GMP —
   banned in the guest") and has no lowering for the LCNF the Nat
   matches produce:
   - `checkWitness`: `let zero := 0` (Nat.lit from the `0` fuel
     pattern), `Nat.decEq` (the fuel-zero test), `Nat.sub` + the
     succ-guard join point (the `fuel + 1` pattern), `Nat.decEq` again
     for the `steps.length == ps.length` gate.
   - `checkSteps`: the same fuel-pattern surface (`Nat.lit`,
     `Nat.decEq`, `Nat.sub`) plus `List.get?Internal._redArg` (the
     `log[s.offset]?` walk) and `List.lengthTR._redArg` /
     `List.length` — core-List helper decls the re-run generates
     in-process but the manifest fold's namespace filter excludes from
     the compile set (they would emit as undefined wasm calls).
   - `WStep.offset : Nat` (the wire's journal offsets) compounds this
     at any export boundary.
   A fix is a BACKEND FEATURE: a boxed-Nat object model (tag + i64
   payload) with `Nat.lit`/`decEq`/`beq`/`sub` lowerings, plus
   compiling (or intrinsics-mapping) the `_redArg` List helpers. Not a
   tweak — a runtime-model decision (the guest ban's "fixed-width
   integers" stance needs a documented exception for match-only Nat).

2. **Perceus `reset`/`reuse`/`isShared` are unlowered.** Observed in
   `lookupString?` (the `some`-rebox of the string payload),
   `evalWU64?` (the `.map string_len` arm), `evalWBool?` (the
   gt/eq/and/not arms reusing a dead `Option.some` scrutinee). They
   arrive as join points WITH ARGS (`jp resetjp.13 _x.14 isShared.15`,
   `goto reusejp.18 reuseFailAlloc.20`) — the backend's `.jp` emission
   currently IGNORES jp arguments, so this needs both a conservative
   reset/reuse/isShared lowering (e.g. `isShared → true` forces the
   fresh-alloc path) AND real join-point-with-args emission. Note:
   `compiler.reuse := false` (ConfigOptions) disables the INSERTION
   pass in the re-run — a one-line pipeline option that removes this
   gap for good once the others close.

3. **`String.decEq` has no lowering.** `lookupU64?`/`lookupString?`
   compare field names (`f.name == n`) — the linter calls String BEq
   std-legal; the backend emits `call String.decEq` — an undefined
   wasm function. Fix: a `streq` intrinsic (one ctor in the closed
   `GuestlangStd.Intrinsic` universe + a `$string_eq` runtime.wat
   primitive over the guest string layout + an oracle body) — the
   StrOps header documents exactly this recipe.

4. **Specialization products are excluded from the compile set.**
   `Option.instBEq.beq._at_.SchemaLang.WitnessCheck.checkStepProof.spec_0`
   (the spec pass's `Option (…)= some 1` comparison) is generated
   in-process but named by its SOURCE TYPE, so the fold's
   under-target-namespace filter drops it → undefined call. Fix:
   include every local impure decl in the emission set (the re-run's
   local decls ARE the targets' closure — the namespace heuristic is
   the bug).

5. **The wire-decode lane is host-only today (the boundary blocker).**
   Even with 1–4 fixed, the end-to-end ("the host hands the guest
   witness BYTES") needs the guest to run `decWitness?` — whose
   closure is `decVarNat` (`b.toNat - 128 + 128 * p.1`: Nat
   arithmetic), `decChar?`/`Char.ofNat`, `decString?`/`String.ofList`
   — all outside the guest runtime (no boxed-Nat, no Char ops, no
   bytes→String primitive in the `Intrinsic` universe). Until the
   backend grows these, a guest checker export can only take
   pre-flattened WIT-native arguments (the canonical ABI's own
   decoding), not the committed witness wire format.

Also observed: `verifyWitness : Witness → RowValsP → Bool` cannot be a
world export at ANY fixing of the above — `Witness`/`RowValsP` are not
`Ty`-representable (the `worldExportsOf` fold only exports
`@[schema_fn]` items). The design-doc's export shape is a
bytes-in/verdict-out wrapper whose guest body contains the decode lane
(gap 5) — the seam's signature is fine for the Lean side, but the WIT
surface needs its own wrapper def.

## What landed in this order

- `lean/wasm-backend/GenMain.lean`: the `UNSUPPORTED-LCNF` diagnostic
  (`reportUnsupportedLCNF` + `ctorNameOf`) — every wasm-gen run now
  names each target decl whose final LCNF carries a construct the
  backend cannot lower (Perceus reset/reuse/isShared, Nat literals,
  unknown-callee faps), with the code path to it, BEFORE the emitter
  throws. Today it prints:
  - `SchemaLang.WitnessCheck.evalWU64? @/case/let/let/case/let/jpK: isShared`
  - `SchemaLang.WitnessCheck.evalWBool? @/case/let/let/case/let/jpK: isShared`
  - `SchemaLang.WitnessCheck.checkWitness @: nat-lit`
- No other file touched: `project.json`, `WasmBackend.lean`, the
  committed artifacts — all verified unchanged.
- wasm-backend build + `lake test` green (the `× identity control`
  verdict line is the deliberate vacuous-control misbehavior the
  driver requires; exit 0).

## The differential test (VERIFY step) — not runnable

The guest-compiled checker does not exist (gaps above), so the
guest≡interpreted verdict duel over the witness fixtures cannot run.
The design doc's W9.6 done-when ("runs under wasmtime AND wasmi
agreeing with the interpreted run") stays open until the backend wave
lands.

## Follow-ups (the unblocking order)

1. Backend: join-point-with-args emission + conservative
   reset/reuse/isShared lowering (or pin `compiler.reuse := false` in
   the re-run).
2. Backend: `streq` intrinsic (closed-universe ctor + runtime
   primitive + oracle body).
3. Backend: include the spec-generated decls in the compile set
   (drop the namespace heuristic).
4. Backend: the boxed-Nat decision (match-only-Nat model or a
   documented calculus restriction per design §7.4 — loudly either
   way).
5. Then W9.6 proper: the bytes-in wrapper export, the oracle duel rows
   over the witness fixtures, the steel-host end-to-end (valid
   accepted / tampered refused BY THE GUEST).
