/-
# Ledger spec — the authoring surface (THE source of truth)

DO-NOT-DELETE header: every attribute here has a role in the codegen
pipeline. This module is the SSOT — the WIT world, the Rust types, the
observe spans, and the fault surfaces are all generated from the
registrations BELOW (the `schema-gen` driver replays them from the
oleans). Delete an attribute and the artifact loses the surface
silently; the byte-tie gate catches it only after the fact.

Attribute roles:

- `@[schema]` on a structure/inductive → registers a record/variant in
  the schema registry. Fields must live in the CLOSED boundary universe
  (`Ty`): UInt64/String/List/Option/… — anything else fails at
  elaboration with the fragment enumerated. The generated Rust/WIT type
  is derived from the field list; renaming a field IS a breaking change
  (`just breaking` gates it).
- `@[schema_fn]` on a def → registers a func SIGNATURE. The body is a
  STUB — the signature is the spec (`_id` is the parameter's spec-name,
  underscore-silenced for the dead body). The real body lives in the
  impl module (LedgerFn.lean). Optional semantic args: `@[schema_fn
  strict]` / `volatile` / `stream` (the FuncSem axes).
- `@[schema_resource]` on an opaque def → an opaque handle type (not
  used in this minimal skeleton; see schema-lang/Demo.lean).

Registration order matters (v1 limitation): the referenced type must be
registered before the referencing declaration — keep the record above
the functions that mention it.
-/

import SchemaLang
import Machines

/-! ## Records -/

@[schema]
structure Ledger where
  id : UInt64
  label : String
  balance : UInt64
  owner : String

/-! ## Function signatures (the bodies are NOT part of the spec) -/

/-- u64 → option<ledger>. The body is a stub — the SIGNATURE is the spec. -/
@[schema_fn]
def ledger_get (_id : UInt64) : Option Ledger :=
  none

/-- THE INVARIANT (the validator): an account is well-formed when its
    id is nonzero and its label is nonempty. The compiled copy runs at
    the host's boundary BEFORE any processing (the load_component.rs
    pattern). -/
@[schema_fn]
def ledger_valid (_a : Ledger) : Bool :=
  true

/-- The DEPOSIT: the balance grows by the amount. UInt64 arithmetic is
    wrapping — the overflow = the caller's concern (the spec-level cap
    = the invariant's story, not the arithmetic's). -/
@[schema_fn]
def deposit (balance amount : UInt64) : UInt64 :=
  0

/-! ## The event-sourced dogfood (W5.1 phase 2)

`Account`/`Entry` carry the full `@[event_sourced]` assembly: the delta
variant (`Account.Event` = insert/update/remove over the first-field
key), the journal codec (`esEncodeJournal`/`esDecodeJournal?` + the
proved round trip), replay (`replay` = the I operator), the identity
upcaster hook, and the `RewindableMachine` (`esMachine` — firing =
patching by the recorded delta; reversal = the inverse delta). The
model layer (posting, derived balances, conservation) is `LedgerES`. -/

/-- An account. The event log over `Account.Event` IS the account
table's history: posting = appending a delta, the table = replay,
reversal = the inverse delta (the journal's rewind). -/
@[schema, event_sourced]
structure Account where
  id : UInt64
  label : String
  balance : Int64
deriving BEq, Repr, DecidableEq

/-- A posting entry: moves `amount` from account `src` to account
    `dst` (the double-entry leg pair in ONE row — the journal entry).
    Entry logs are insert-only by convention (an entry is never edited;
    a reversal is a compensating entry). -/
@[schema, event_sourced]
structure Entry where
  id : UInt64
  src : UInt64
  dst : UInt64
  amount : Int64
deriving BEq, Repr, DecidableEq
