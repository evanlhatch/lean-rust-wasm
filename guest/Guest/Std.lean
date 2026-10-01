/-
# Guest.Std — the guest std library (the guest-compilable implementations)

The guest's std surface (mined from `legacy/lean/std/GuestlangStd.lean`
+ `StrOps.lean` — the INTENT fresh over this tree's guest lane): the
implementations the guest compiler compiles + the guest-compat
discipline (pattern #13 — every compiled decl carries `@[guest_std]`,
the elaboration-time ban gate). The dual face per function:

- the NATIVE oracle — the real Lean body (the differential duel's
  authority);
- the COMPILED lane — the name in the guest-mark registry (the
  backend's compile roots) and, for the bodies already in the guest's
  fragment, a lowering target (the end-to-end in GuestStdTests).

Umbrella (one import point; root-module imports are NOT re-exported —
the WasmCore.lean discipline):

- `GuestStd.StrOps` — the string intrinsics: the ONE closed universe
  + the oracle wrappers (`strlen`/`strcat`/`streq`/`strof`).
- `GuestStd.ListOps` — the guest-fragment list/numeric utilities
  (`listLenU64`/`sumU64`) + their spec theorems.

The five questions (notes/v3/01-core.md): answered per submodule; the
umbrella is the import point and answers none.
-/

module

public import Guest.Std.StrOps
public import Guest.Std.ListOps


@[expose] public section