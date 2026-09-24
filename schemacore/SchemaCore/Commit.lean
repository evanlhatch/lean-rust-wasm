/-
# SchemaCore.Commit — the propose→check→commit discipline (as DATA)

Owner: the bidirectional-slice agent (the mandate tree, `schemacore/`).
Driving decisions: notes/v3/03-bidirectional.md §3 (the practical
default: Rust proposes, the checker validates, the commit applies —
the delta applies against the SAME snapshot/version; the commit
refuses a stale snapshot), §7 (the trichotomy: a COMMAND is requested
intent — it can fail or no-op; a DELTA is the accepted net change; the
event is the journal's business, `Event.lean`'s lane), §8 (the
violation query checks the proposal; empty permits commit).

THE DISCIPLINE, HONEST FIRST CUT:

- `Proposal` — the command's delta as DATA: the base snapshot VERSION
  (the proposal is computed against a NAMED snapshot — 03 §3's
  race-honesty) + the transfer's fields;
- `Proposal.deltas` — the command's lowering to the shared delta
  carrier (`Update.RowDelta`, ONE variant, no second table): the
  transfer-row INSERT into the ledger + the two keyed account UPDATES
  read off the SNAPSHOT (a missing endpoint contributes NO account
  delta — the insert still fires, so the foreign-key query catches it;
  a self-transfer's two updates collapse to net zero through the keyed
  applicator);
- `checkDelta` — THE VIOLATION QUERY over the POST-STATE (the delta
  applied to the whole db): the honest first cut. The
  change-proportional face — the violation relation updated
  incrementally, `ΔV = V(B+ΔB) − V(B)`, proved equal to full
  recomputation ONCE at the circuit theory (`incrementalize_ok`) — is
  the dbsp-circuit wave's content: NAMED here, never faked;
- `checkVerdict` — the verdict: `.accept` or `.refuse` with the
  violations AS DATA;
- `Proposal.commit` — the transactional adapter: refuses a STALE
  snapshot (base ≠ version, `commit_stale`), refuses an INVALID
  proposal (the violations ride the error), otherwise applies the
  accepted delta and bumps the version. A refused proposal produces NO
  state change — structural, never a flag.

THE SOUNDNESS (CheckerSoundness, 03 §3): `check_sound` — an ACCEPTED
proposal's post-state satisfies the state invariant (`Valid`, via
`Violate.valid_iff`); `commit_ok_valid` — a COMMITTED snapshot's
database satisfies it. Both directions of the acceptance bridge ride
the violation lane's theorem; nothing here re-proves it.

Deliberate exclusions (the leftover rule): the runtime-checked-
transition level (the guest-compiled checker + its trust story) is the
wasm wave's content — THIS slice's evidence level is the DIFFERENTIAL
(03 §3's table), landed as the `commitDuel` vector set below, whose
Rust consumer re-proposes the deltas and agrees verdict-for-verdict;
concurrent commit arbitration (CAS/recheck/proven commutativity) — the
single-threaded snapshot-version discipline is the honest first cut;
batch proposals — the first batch consumer lands them.

The five questions (notes/v3/01-core.md): root = Change (01 §2) at the
transaction boundary — command → delta → commit, the trichotomy's
operational face; carrier = the proposal as data + the verdict ctors
(never strings, 04 §6) + the violations as rows (02 §1); spine reading
= none — the discipline rides Violate's queries and Update's
`applyRowDelta`; ladder rung = the soundness theorems are the small
hand kind over `valid_iff` (the bridge is CITED, not re-proved); gate
row = SchemaTests' commitSpec + the axiom report.

Core-only (imports SchemaCore.Violate + SchemaCore.Codec + Kit.Duel —
the cone rule; the duel rides the ONE Kit, the vectors' bytes are
`encVal`'s, never a second encoding).
-/

import SchemaCore.Violate
import SchemaCore.Codec
import Kit.Duel

namespace SchemaCore

open Kit

/-! ## The snapshot + the proposal (the command's delta, as data) -/

/-- THE SNAPSHOT: the database under a named version. The version is
    the race-honesty carrier (03 §3): a proposal checks against the
    version it was computed from, and the commit REFUSES a stale one. -/
structure DbSnap where
  /-- The snapshot version (monotone; bumped by every commit). -/
  version : Nat
  /-- The database. -/
  db : Db

/-- THE PROPOSAL (the command's delta): the base snapshot version the
    proposal was computed against + the transfer's fields. This is the
    data a handwritten Rust command proposes (the differential's
    vectors ARE these, on `SchemaCore.Codec`'s wire). -/
structure Proposal where
  /-- The base snapshot version (the staleness check's face). -/
  base : Nat
  /-- The ledger row's key. -/
  tid : UInt64
  /-- The source account. -/
  src : UInt64
  /-- The destination account. -/
  dst : UInt64
  /-- The amount. -/
  amount : UInt64

/-- The proposal's amount as a balance DELTA (the signed reading; the
    u64→i64 widening is the fixture's honest arithmetic). -/
def Proposal.amt (p : Proposal) : Int64 := Int64.ofInt (p.amount.toNat : Int)

/-- The transfer row the proposal inserts into the ledger (the command
    is RECORDED even when the accounts move — the audit face). -/
def transferRow (p : Proposal) : RowVals transferFields :=
  .cons (.u64 p.tid)
    (.cons (.u64 p.src) (.cons (.u64 p.dst) (.cons (.u64 p.amount) .nil)))

/-! ## The delta carrier (Update.RowDelta — ONE variant, no second table) -/

/-- THE DELTAS: a proposal's table effects as signed-bag entries over
    each table's OWN key — the shared `RowDelta` carrier specialized
    to both tables of the fixture. -/
structure Deltas where
  /-- The account-table entries (keyed on `id`). -/
  accounts : List (RowDelta accountFields)
  /-- The ledger entries (keyed on `tid`). -/
  transfers : List (RowDelta transferFields)

/-- THE KEYED APPLICATION: each table's entries fold through the
    update lane's `applyRowDelta` (the keyed applicator — insert
    appends, update replaces the rows sharing the key image, remove
    drops them). -/
def applyDeltas (db : Db) (d : Deltas) : Db where
  accounts := d.accounts.foldl (fun acc d => applyRowDelta "id" d acc) db.accounts
  transfers := d.transfers.foldl (fun acc d => applyRowDelta "tid" d acc)
    db.transfers

/-- THE COMMAND'S LOWERING (request → proposed delta): the ledger
    insert ALWAYS fires (the intent is recorded — a missing endpoint
    then REFUSES through the foreign-key query, never silently
    no-ops); the two account updates fire only when the snapshot has
    the endpoint row. A self-transfer's two updates share one key: the
    keyed applicator's last-wins leaves the balance unchanged (the net
    zero the command MEANS). -/
def Proposal.deltas (db : Db) (p : Proposal) : Deltas where
  accounts :=
    ((db.accounts.find? (fun r => accId r == p.src)).map
      (fun r => RowDelta.update (withBal r (accBal r - p.amt)))).toList ++
    ((db.accounts.find? (fun r => accId r == p.dst)).map
      (fun r => RowDelta.update (withBal r (accBal r + p.amt)))).toList
  transfers := [RowDelta.insert (transferRow p)]

/-- THE POST-STATE: the proposed delta applied (the state the check
    speaks about — 03 §8: check the post-state). -/
def postDb (db : Db) (p : Proposal) : Db := applyDeltas db (p.deltas db)

/-! ## The check + the verdict -/

/-- THE CHECK (03 §8's honest first cut): the violation query over the
    POST-STATE — full recomputation at this size. The change-
    proportional face (the violation relation maintained incrementally
    under the delta) is the dbsp-circuit wave's `incrementalize_ok`:
    named in the module header, not faked here. -/
def checkDelta (db : Db) (p : Proposal) : List Violation :=
  violations (postDb db p)

/-- THE VERDICT: accept, or refuse with the violations AS DATA (ctors,
    never strings — 04 §6; the violating rows ARE the refusal's
    payload, 02 §1). -/
inductive Verdict where
  /-- The post-state is valid — the proposal may commit. -/
  | accept
  /-- The post-state violates — the payload names the rows. -/
  | refuse (vs : List Violation)

/-- The verdict from the check (the empty-violations discipline). -/
def checkVerdict (db : Db) (p : Proposal) : Verdict :=
  match checkDelta db p with
  | [] => .accept
  | vs => .refuse vs

/-- THE CHECK'S LAW: the verdict accepts iff the violation query is
    empty (the verdict is the query's decision, nothing added). -/
theorem checkVerdict_accept_iff (db : Db) (p : Proposal) :
    checkVerdict db p = .accept ↔ checkDelta db p = [] := by
  unfold checkVerdict
  cases hq : checkDelta db p with
  | nil => simp
  | cons v vs => simp

/-- THE CHECKER SOUNDNESS (03 §3): an ACCEPTED proposal's post-state
    satisfies the state invariant — the acceptance bridge rides
    `valid_iff`, never a re-proof. -/
theorem check_sound (db : Db) (p : Proposal)
    (h : checkVerdict db p = .accept) : Valid (postDb db p) :=
  (valid_iff _).mpr ((checkVerdict_accept_iff db p).mp h)

/-! ## The transactional adapter -/

/-- THE COMMIT ERROR: stale snapshot, or invalid proposal with the
    violations as the payload (the refusal names its reason — 04 §8). -/
inductive CommitError where
  /-- The proposal's base version is not the snapshot's. -/
  | stale (base got : Nat)
  /-- The post-state violates — the violations ride the error. -/
  | invalid (vs : List Violation)

/-- THE COMMIT (the transactional adapter, honest first cut): the
    stale snapshot REFUSES (03 §3's race-honesty — the commit applies
    the accepted delta against the SAME snapshot/version); the invalid
    proposal REFUSES with its violations; the accepted proposal
    applies and bumps the version. -/
def Proposal.commit (s : DbSnap) (p : Proposal) : Except CommitError DbSnap :=
  if p.base = s.version then
    match checkVerdict s.db p with
    | .accept => .ok { version := s.version + 1, db := postDb s.db p }
    | .refuse vs => .error (.invalid vs)
  else .error (.stale p.base s.version)

/-- The commit's stale equation. -/
theorem commit_eq_of_stale (s : DbSnap) (p : Proposal)
    (h : p.base ≠ s.version) :
    p.commit s = .error (.stale p.base s.version) := by
  unfold Proposal.commit
  rw [if_neg h]

/-- The commit's accept equation. -/
theorem commit_eq_of_accept (s : DbSnap) (p : Proposal)
    (h : p.base = s.version) (hok : checkVerdict s.db p = .accept) :
    p.commit s = .ok ⟨s.version + 1, postDb s.db p⟩ := by
  unfold Proposal.commit
  rw [if_pos h, hok]

/-- The commit's refuse equation. -/
theorem commit_eq_of_refuse (s : DbSnap) (p : Proposal)
    (h : p.base = s.version) (l : List Violation)
    (hv : checkVerdict s.db p = .refuse l) :
    p.commit s = .error (.invalid l) := by
  unfold Proposal.commit
  rw [if_pos h, hv]

/-- THE COMMIT'S SOUNDNESS: a COMMITTED snapshot's database satisfies
    the state invariant — the adapter applies only accepted proposals
    (the equation lemmas above make the three paths decidable), and
    acceptance is sound by `check_sound`. -/
theorem commit_ok_valid (s : DbSnap) (p : Proposal) (s' : DbSnap)
    (h : p.commit s = .ok s') : Valid s'.db := by
  by_cases hbase : p.base = s.version
  · cases hcheck : checkDelta s.db p with
    | nil =>
        rw [commit_eq_of_accept s p hbase
          ((checkVerdict_accept_iff s.db p).mpr hcheck)] at h
        injection h with hEq
        subst hEq
        exact (valid_iff _).mpr hcheck
    | cons v vs =>
        have hv : checkVerdict s.db p = .refuse (v :: vs) := by
          unfold checkVerdict
          rw [hcheck]
        rw [commit_eq_of_refuse s p hbase (v :: vs) hv] at h
        exact absurd h (by simp)
  · rw [commit_eq_of_stale s p hbase] at h
    exact absurd h (by simp)

/-- THE STALE REFUSAL (03 §3's race-honesty face): a proposal computed
    against a stale version NEVER commits — whatever its content. -/
theorem commit_stale (s : DbSnap) (p : Proposal) (h : p.base ≠ s.version) :
    p.commit s = .error (.stale p.base s.version) :=
  commit_eq_of_stale s p h

/-! ## The fixture (the worked example's state) -/

/-- The accounts: alice (id 1, balance 100) + bob (id 2, balance 50). -/
def fixtureAccounts : List (RowVals accountFields) :=
  [ .cons (.u64 1) (.cons (.string "alice") (.cons (.i64 100) .nil))
  , .cons (.u64 2) (.cons (.string "bob") (.cons (.i64 50) .nil)) ]

/-- The fixture's snapshot: version 1, an empty ledger. -/
def fixtureSnap : DbSnap := ⟨1, { accounts := fixtureAccounts, transfers := [] }⟩

/-! ## The duel (03 §3's differential level — the slice's evidence) -/

/-- The duel's proposals (the commands the handwritten Rust side
    re-proposes): the legal transfer, the overdraft, the dangling
    endpoint, the stale snapshot. One per face of the slice. -/
def duelProposals : List (String × Proposal) :=
  [ ("p8",  { base := 1, tid := 8, src := 1, dst := 2, amount := 30 })
  , ("p9",  { base := 1, tid := 9, src := 2, dst := 1, amount := 500 })
  , ("p10", { base := 1, tid := 10, src := 9, dst := 1, amount := 5 })
  , ("p11", { base := 0, tid := 11, src := 1, dst := 2, amount := 5 }) ]

/-- The duel's directory (Kit.Duel's ONE-directory-per-duel rule). -/
def commitDuelDir : String := "crates/schema-generated/tests/duel-commit"

/-- A proposal's vector path. -/
def commitDuelPath (name : String) : String :=
  commitDuelDir ++ "/" ++ name ++ ".bin"

/-- A proposal's wire bytes (SchemaCore.Codec's `encVal` — the ONE
    encoding; the vector bytes are these, never re-encoded). -/
def proposalBytes (p : Proposal) : List UInt8 :=
  encVal .u64 (.u64 (p.base.toUInt64)) ++ encVal .u64 (.u64 p.tid)
    ++ encVal .u64 (.u64 p.src) ++ encVal .u64 (.u64 p.dst)
    ++ encVal .u64 (.u64 p.amount)

/-- The duel's expectation per proposal — COMPUTED BY THE CHECKER (the
    Lean commit IS the golden: an accept row rides `decode accept`, a
    refusal rides `refuse` — Kit.Duel's closed vocabulary). -/
def expectOf (p : Proposal) : Kit.Duel.Expect :=
  match p.commit fixtureSnap with
  | .ok _ => Kit.Duel.Expect.decode "accept"
  | .error _ => Kit.Duel.Expect.refuse

/-- THE COMMIT DUEL's vector set: the four proposals' wire bytes + the
    checker-computed expectations. The Rust consumer re-proposes each
    delta (the handwritten command) and must agree verdict-for-verdict
    — the differential level, tested agreement, never a theorem. -/
def commitDuel : Kit.Duel.VectorSet where
  dir := commitDuelDir
  name := "commit-slice"
  generator := "SchemaCore.Commit"
  vectors := duelProposals.map (fun np =>
    { path := commitDuelPath np.1
      contents := (proposalBytes np.2).toByteArray })
  expects := duelProposals.map (fun np =>
    (commitDuelPath np.1, expectOf np.2))

/-- The duel's emitter (the manifest rides the TEXT lane, the vectors
    the BINARY lane — the existing duel emitter's shape, a second
    directory). -/
def commitDuelEmitter : Kit.Emit.Emitter (DataRegistry Item) where
  name := s!"duel:{commitDuel.name}"
  style := .doubleSlash
  specSource := "SchemaCore.Slice"
  outputs := [commitDuel.dir ++ "/manifest.txt"]
  binaryOutputs := commitDuel.vectors.map (·.path)
  binaryOutputs_nodup := commitDuel.vectors_nodup
  run _ :=
    [ { path := commitDuel.dir ++ "/manifest.txt"
      , contents := Kit.Duel.manifestBody commitDuel } ]
  runBinary := some fun _ => commitDuel.vectors
  law := some fun reg => (reg.items.map reg.nameOf).Nodup

/-! ## The Rust consumer (the handwritten command + the duel's other side) -/

/-- THE RUST CONSUMER (the duel's other side): the handwritten command
    (`propose_transfer` — a Rust-side transfer between two accounts,
    PROPOSED on the wire) + the fixture mirror + the violation
    queries' mirror + the transactional adapter's mirror + the duel
    loop (re-propose byte-identically, agree verdict-for-verdict) +
    the negative controls (the stale refusal names STALENESS; the
    overdraft refusal carries the violating row; a tampered vector
    misses the proposal). GENERATED bytes (the emitter owns the file —
    never hand-edit), but the SHAPE is 03 §3's: Rust keeps the
    algorithmic freedom, the checker's verdict is the authority. The
    evidence level is the DIFFERENTIAL — tested agreement, named in
    the module header; the runtime-checked transition is the wasm
    wave's content. -/
def commitSliceRust : String :=
  "//! GENERATED commit-slice consumer (SchemaCore.Commit's duel —
//! notes/v3/03 section 3's DIFFERENTIAL level). The duel directory
//! tests/duel-commit/ carries the proposal vectors plus manifest.txt
//! (the generator row + one `<path>\t<expectation>` row per vector),
//! all emitted by SchemaCore.Commit's duel emitter and committed
//! through the byte-tie — never hand-written, never hand-edited.
//!
//! THE SLICE (03 section 9): the handwritten command proposes a
//! delta; the violation queries check the post-state; the
//! transactional adapter commits against the SAME snapshot version.
//! This test is the Rust half: it re-proposes each committed delta
//! byte-identically and must agree verdict-for-verdict with the
//! Lean-side golden. Tested agreement — never a theorem; the
//! runtime-checked transition is the wasm wave's content.

use schema_generated::{dec_u64, enc_varint};

/// The duel manifest, compile-time pinned to the committed artifact.
const MANIFEST: &str = include_str!(\"duel-commit/manifest.txt\");

/// The generated crate's repo-root prefix (the manifest's rows are
/// repo-root-relative; the test binary's cwd is the crate root).
const CRATE_PREFIX: &str = \"crates/schema-generated/\";

/// Kit.Duel's consumer contract: skip the 2-line GENERATED header and
/// the `generator` provenance row, split each row on the tab.
fn manifest_rows() -> Vec<(String, Option<String>)> {
    MANIFEST
        .lines()
        .skip(2)
        .filter(|line| !line.is_empty() && !line.starts_with(\"generator\t\"))
        .map(|line| {
            let mut parts = line.split('\\t');
            let path = parts.next().expect(\"manifest row: path\").to_string();
            let expect = parts.next().expect(\"manifest row: expectation\");
            (path, expect.strip_prefix(\"decode \").map(str::to_string))
        })
        .collect()
}

/// Re-base a manifest row's repo-root-relative path to the crate root.
fn crate_path(row_path: &str) -> &str {
    match row_path.strip_prefix(CRATE_PREFIX) {
        Some(p) => p,
        None => row_path,
    }
}

/// The fixture mirror (SchemaCore.Commit's fixtureSnap): version 1,
/// two accounts, an empty ledger.
#[derive(Clone)]
struct Account {
    id: u64,
    balance: i64,
}

fn fixture() -> (u64, Vec<Account>, Vec<(u64, u64, u64, u64)>) {
    (
        1,
        vec![Account { id: 1, balance: 100 }, Account { id: 2, balance: 50 }],
        vec![],
    )
}

/// THE HANDWRITTEN COMMAND (03 section 3): a Rust-side transfer
/// between two accounts, PROPOSED on the wire (base, tid, src, dst,
/// amount — five canonical varints, the generated encoder's).
fn propose_transfer(base: u64, tid: u64, src: u64, dst: u64, amount: u64) -> Vec<u8> {
    let mut out = Vec::new();
    enc_varint(base, &mut out);
    enc_varint(tid, &mut out);
    enc_varint(src, &mut out);
    enc_varint(dst, &mut out);
    enc_varint(amount, &mut out);
    out
}

/// Decode a proposal off the wire (five varints; a truncated or
/// non-canonical vector is a typed None, never a panic).
fn dec_proposal(bs: &[u8]) -> Option<(u64, u64, u64, u64, u64)> {
    let mut rest: &[u8] = bs;
    let base = dec_u64(&mut rest).ok()?;
    let tid = dec_u64(&mut rest).ok()?;
    let src = dec_u64(&mut rest).ok()?;
    let dst = dec_u64(&mut rest).ok()?;
    let amount = dec_u64(&mut rest).ok()?;
    Some((base, tid, src, dst, amount))
}

/// The violation queries' mirror over the POST-STATE (the honest
/// first cut: full recomputation — the change-proportional face is
/// the dbsp-circuit wave's `incrementalize_ok`, named not faked).
fn violations(accounts: &[Account], transfers: &[(u64, u64, u64, u64)]) -> Vec<String> {
    let ids: Vec<u64> = accounts.iter().map(|a| a.id).collect();
    let mut out: Vec<String> = Vec::new();
    for id in &ids {
        if ids.iter().filter(|k| **k == *id).count() > 1 {
            out.push(format!(\"duplicate account id {}\", id));
        }
    }
    for a in accounts {
        if a.balance < 0 {
            out.push(format!(\"negative balance: id {} balance {}\", a.id, a.balance));
        }
    }
    for (tid, src, dst, _amount) in transfers {
        if !ids.contains(src) {
            out.push(format!(\"unresolved src: tid {}\", tid));
        }
        if !ids.contains(dst) {
            out.push(format!(\"unresolved dst: tid {}\", tid));
        }
    }
    out
}

/// The transactional adapter's mirror: the stale snapshot refuses
/// FIRST (03 section 3's race-honesty); the proposed delta applies to
/// a WORKING COPY (external effects never occur before authorization);
/// the violation query over the post-state decides; empty permits the
/// commit (apply + bump the version).
fn commit(
    version: &mut u64,
    accounts: &mut Vec<Account>,
    transfers: &mut Vec<(u64, u64, u64, u64)>,
    base: u64,
    tid: u64,
    src: u64,
    dst: u64,
    amount: u64,
) -> Result<(), String> {
    if base != *version {
        return Err(format!(\"stale {} vs {}\", base, *version));
    }
    let mut accounts2 = accounts.clone();
    let mut transfers2 = transfers.clone();
    transfers2.push((tid, src, dst, amount));
    let amt = amount as i64;
    for a in accounts2.iter_mut() {
        if a.id == src {
            a.balance -= amt;
        }
        if a.id == dst && src != dst {
            a.balance += amt;
        }
    }
    let vs = violations(&accounts2, &transfers2);
    if vs.is_empty() {
        *accounts = accounts2;
        *transfers = transfers2;
        *version += 1;
        Ok(())
    } else {
        Err(format!(\"invalid: {:?}\", vs))
    }
}

/// THE DUEL: every vector is re-proposed byte-identically (one wire,
/// two sides) and the adapter's verdict must match the manifest's
/// expectation. The duel must exercise BOTH verdicts.
#[test]
fn commit_duel() {
    let mut saw_accept = false;
    let mut saw_refuse = false;
    for (path, note) in manifest_rows() {
        let bytes = std::fs::read(crate_path(&path)).expect(\"duel vector file present\");
        let (base, tid, src, dst, amount) = dec_proposal(&bytes)
            .unwrap_or_else(|| panic!(\"proposal {} does not decode\", path));
        assert_eq!(
            propose_transfer(base, tid, src, dst, amount),
            bytes,
            \"propose drift at {}\",
            path
        );
        let (mut version, mut accounts, mut transfers) = fixture();
        let verdict = match commit(&mut version, &mut accounts, &mut transfers, base, tid, src, dst, amount) {
            Ok(()) => \"accept\",
            Err(_) => \"refuse\",
        };
        match &note {
            Some(n) if n == \"accept\" => {
                assert_eq!(verdict, \"accept\", \"{}: expected accept\", path);
                saw_accept = true;
            }
            None => {
                assert_eq!(verdict, \"refuse\", \"{}: expected refuse\", path);
                saw_refuse = true;
            }
            Some(n) => panic!(\"{}: unknown expectation {}\", path, n),
        }
    }
    assert!(saw_accept && saw_refuse, \"the duel must exercise both verdicts\");
}

/// THE NEGATIVE CONTROL (the stale face): the stale vector's refusal
/// names STALENESS — a stale commit refuses on the VERSION, never on
/// the content.
#[test]
fn stale_refusal_names_staleness() {
    let mut found = false;
    for (path, note) in manifest_rows() {
        if note.is_some() {
            continue;
        }
        let bytes = std::fs::read(crate_path(&path)).expect(\"duel vector file present\");
        let (base, tid, src, dst, amount) = dec_proposal(&bytes)
            .unwrap_or_else(|| panic!(\"proposal {} does not decode\", path));
        let (mut version, mut accounts, mut transfers) = fixture();
        if base != version {
            found = true;
            match commit(&mut version, &mut accounts, &mut transfers, base, tid, src, dst, amount) {
                Err(e) => assert!(
                    e.starts_with(\"stale\"),
                    \"{}: wrong refusal reason: {}\",
                    path,
                    e
                ),
                Ok(()) => panic!(\"{}: a stale proposal committed\", path),
            }
        }
    }
    assert!(found, \"the duel carries no stale vector\");
}

/// THE NEGATIVE CONTROL (the refuse-with-rows face): an invalid
/// proposal's refusal carries the VIOLATING ROW as data (the payload
/// names the negative balance or the unresolved endpoint — 02's
/// discipline, never a bare false).
#[test]
fn invalid_refusal_carries_the_violating_row() {
    let mut found = false;
    for (path, note) in manifest_rows() {
        if note.is_some() {
            continue;
        }
        let bytes = std::fs::read(crate_path(&path)).expect(\"duel vector file present\");
        let (base, tid, src, dst, amount) = dec_proposal(&bytes)
            .unwrap_or_else(|| panic!(\"proposal {} does not decode\", path));
        let (mut version, mut accounts, mut transfers) = fixture();
        if base == version {
            match commit(&mut version, &mut accounts, &mut transfers, base, tid, src, dst, amount) {
                Err(e) => {
                    if e.starts_with(\"invalid\") {
                        found = true;
                        assert!(
                            e.contains(\"negative balance\") || e.contains(\"unresolved\"),
                            \"{}: the refusal lost the row: {}\",
                            path,
                            e
                        );
                    }
                }
                Ok(()) => {}
            }
        }
    }
    assert!(found, \"the duel carries no invalid vector\");
}

/// THE NEGATIVE CONTROL (the differential's tooth): a tampered vector
/// MISSES the proposal — the flipped bytes either refuse to decode or
/// re-propose differently (a differential that cannot see a flip
/// proves nothing).
#[test]
fn tampered_vector_misses_the_proposal() {
    let mut exercised = false;
    for (path, note) in manifest_rows() {
        if note.is_none() {
            continue;
        }
        let orig = std::fs::read(crate_path(&path)).expect(\"duel vector file present\");
        let mut bytes = orig.clone();
        let last = bytes.len() - 1;
        bytes[last] ^= 0x01;
        match dec_proposal(&bytes) {
            None => exercised = true, // the flip broke the varint — the typed refusal IS the pass
            Some((base, tid, src, dst, amount)) => {
                exercised = true;
                assert_ne!(
                    propose_transfer(base, tid, src, dst, amount),
                    orig,
                    \"{}: tampered bytes re-proposed the committed vector\",
                    path
                );
            }
        }
    }
    assert!(exercised, \"the duel carries no accept vector to tamper\");
}
"

end SchemaCore
