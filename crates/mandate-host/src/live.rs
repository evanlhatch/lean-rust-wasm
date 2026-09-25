//! The LIVE propose/check/commit loop — notes/v3/03-bidirectional.md
//! §3's practical default, running against the host:
//!
//! > Rust computes `request + snapshot → proposed delta + response`;
//! > the checker validates `snapshot + request + proposal →
//! > accept/refuse`; the commit applies the accepted delta against the
//! > SAME snapshot/version.
//!
//! THE CHECKER'S EVIDENCE LEVEL — the honest cut, named: the ideal is
//! the guest-compiled checker exported from the component. THE GUEST
//! CANNOT COMPILE IT: the checker (`SchemaCore.Violate.violations`)
//! runs over the GADT-indexed `RowVals` rows with `List.filter`
//! closures, `String` columns, and `List.count` — every one outside
//! the guest compiler's landed fragment (scalar lets / binops /
//! returns / Bool-cases; closures, strings, and record types are
//! NAMED refusals in `Guest.Lower`). So the checker stays LEAN-side as
//! the reference: the committed commit-duel vectors
//! (`crates/schema-generated/tests/duel-commit/`, emitted by
//! `SchemaCore.Commit.commitDuel` with the expectations COMPUTED BY
//! `Proposal.commit`) are the Lean checker's pinned verdicts, and THIS
//! side's mirror checker is duel-bound to them verdict-for-verdict
//! (`run_commit_duel`). The evidence level is 03 §3's DIFFERENTIAL —
//! tested agreement, never a theorem; the runtime-checked transition
//! is the wasm wave's content. The component lane keeps what the
//! guest CAN compile (the slice's `answer` — `component.rs`).
//!
//! THE LOOP (per proposal):
//! 1. PROPOSE — the handwritten command: a transfer computed against
//!    the CURRENT snapshot version (`Live::propose`; the version is
//!    the race-honesty carrier);
//! 2. CHECK — the mirror of `Proposal.deltas` + `checkDelta`: the
//!    delta applied to a WORKING COPY (external effects never occur
//!    before authorization), the violation queries over the POST-state
//!    (full recomputation — the change-proportional face is the
//!    dbsp-circuit wave's `incrementalize_ok`, named not faked);
//! 3. COMMIT — the mirror of `Proposal.commit`: a stale base REFUSES
//!    on the version (before any content look); a violated post-state
//!    REFUSES with the violating rows AS DATA (02 §1) and produces NO
//!    state change and NO journal entry (structural, never a flag);
//!    an accepted commit applies + bumps the version and records the
//!    ledger row through the journal (`mandate-delta` — the effect
//!    written BEFORE the in-memory state moves, so memory never runs
//!    ahead of the durable log).
//!
//! THE JOURNAL'S SCOPE — honest first cut: the delta log is
//! single-table (the Lean journal model's granularity), so it records
//! the TRANSFER LEDGER — the command's recorded intent (Lean's own
//! face: "the ledger insert ALWAYS fires — the audit face"); the
//! account movements are DERIVED by replaying the ledger against the
//! fixture on open (reopen reconstructs the full live state; the
//! reopen-equivalence tooth pins it). An account-table journal is the
//! named follow-up, not faked here.
//!
//! THE MIRROR'S ONE KNOWN DRIFT — pinned, not hidden: Lean's
//! `Proposal.deltas` header claims a self-transfer "collapses to net
//! zero", but the COMMITTED CODE computes both account updates from
//! the snapshot and applies them last-wins through `applyRowDelta` —
//! evaluated (`postDb fixtureSnap`, src=dst=1, amount=10): balances
//! `[110, 50]`, NOT net zero. The mirror follows the CODE (the spec of
//! record); the self-transfer tooth pins the same value Lean computes.
//! No duel vector exercises self-transfer, so the committed duel
//! cannot see this face — flagged to the slice owner.
//!
//! ERROR DISCIPLINE (12 §8): a refusal (stale/violated) is a TYPED
//! VERDICT, not an error — the discipline working is the expected
//! path; `HostError` is reserved for genuine faults (I/O, the journal,
//! a journaled row that lost its schema).

use std::path::{Path, PathBuf};

use mandate_delta::{Delta, Field, Row, Schema, Ty, Value};

use crate::artifact::{bytes_hash, sidecar_hash};
use crate::duel::RowVerdict;
use crate::{HostError, Journal};

/// The ledger journal's schema: the transfer row, keyed on `tid` (the
/// fixture's `transferFields` + `transferDecl`'s key, at the journal's
/// scalar arms).
fn ledger_schema() -> Schema {
    Schema::build(
        vec![
            Field { name: "tid".into(), ty: Ty::U64 },
            Field { name: "src".into(), ty: Ty::U64 },
            Field { name: "dst".into(), ty: Ty::U64 },
            Field { name: "amount".into(), ty: Ty::U64 },
        ],
        "tid",
    )
    .unwrap_or_else(|e| panic!("the ledger schema is well-formed: {e}"))
}

/// An account (the fixture's `accountFields`: id/owner/balance —
/// balance SIGNED, the overdraft face representable).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Account {
    /// The primary key.
    pub id: u64,
    /// The owner.
    pub owner: String,
    /// The balance (signed).
    pub balance: i64,
}

/// A ledger row (the fixture's `transferFields`: tid/src/dst/amount).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transfer {
    /// The primary key.
    pub tid: u64,
    /// The source account.
    pub src: u64,
    /// The destination account.
    pub dst: u64,
    /// The amount.
    pub amount: u64,
}

/// THE PROPOSAL (the command's delta, as data): the base snapshot
/// version + the transfer's fields — the handwritten Rust command's
/// shape, mirroring `SchemaCore.Proposal`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Proposal {
    /// The base snapshot version (the staleness check's face).
    pub base: u64,
    /// The ledger row's key.
    pub tid: u64,
    /// The source account.
    pub src: u64,
    /// The destination account.
    pub dst: u64,
    /// The amount.
    pub amount: u64,
}

/// THE VIOLATION DATA (02 §1): the failed check's payload carries the
/// offending key image or the offending ROW, never a bare `false` —
/// the mirror of `SchemaCore.Violation`'s four ctors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViolationRow {
    /// An account id occurring more than once.
    DuplicateId(u64),
    /// An account row whose balance is negative — the row's image.
    NegativeBalance { id: u64, balance: i64 },
    /// A transfer row whose `src` does not resolve — the row's image.
    UnresolvedSrc { tid: u64, src: u64 },
    /// A transfer row whose `dst` does not resolve — the row's image.
    UnresolvedDst { tid: u64, dst: u64 },
}

impl ViolationRow {
    /// The violation's rendering (mirrors `Violation.render`'s
    /// vocabulary; diagnostics + test pins, NOT byte-tied).
    #[must_use]
    pub fn render(&self) -> String {
        match self {
            Self::DuplicateId(k) => format!("duplicate account id {k}"),
            Self::NegativeBalance { id, balance } => {
                format!("negative balance: id {id} balance {balance}")
            }
            Self::UnresolvedSrc { tid, src } => format!("unresolved src: tid {tid} src {src}"),
            Self::UnresolvedDst { tid, dst } => format!("unresolved dst: tid {tid} dst {dst}"),
        }
    }
}

/// THE VERDICT (ctors, never strings — 04 §6): the commit's three
/// faces. `Committed` carries the new version; `Stale` names BOTH
/// versions (the race witness); `Violated` carries the rows AS DATA.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LiveVerdict {
    /// The post-state is valid — the delta applied, the version
    /// bumped, the ledger row journaled.
    Committed { version: u64 },
    /// The proposal's base is not the snapshot's version — refused on
    /// the VERSION, whatever the content.
    Stale { base: u64, got: u64 },
    /// The post-state violates — the payload names the rows.
    Violated(Vec<ViolationRow>),
}

/// THE LIVE STATE: the snapshot version + the two tables + the
/// journal beside. The invariant: the in-memory state is exactly the
/// journal's replay over the fixture (the reopen tooth pins it).
#[derive(Debug)]
pub struct Live {
    /// The snapshot version (monotone; bumped by every commit).
    version: u64,
    /// The account table.
    accounts: Vec<Account>,
    /// The transfer ledger.
    transfers: Vec<Transfer>,
    /// The journal (the ledger's durable face).
    journal: Journal,
}

/// The account row a delta update CARRIES: computed from the
/// SNAPSHOT row (`withBal r (accBal r ∓ amt)` — Lean reads the
/// pre-delta row, never the intermediate), applied last-wins.
fn with_bal(r: &Account, d: i64) -> Account {
    Account { id: r.id, owner: r.owner.clone(), balance: r.balance + d }
}

/// ONE keyed update's fold step (the mirror of `applyRowDelta`'s
/// `update` arm): every row sharing the update's key image is
/// replaced by the carried row, the rest pass through.
fn apply_one(accounts: &[Account], r: &Account) -> Vec<Account> {
    accounts
        .iter()
        .map(|a| if a.id == r.id { r.clone() } else { a.clone() })
        .collect()
}

/// ONE transfer's table effect over the accounts (the mirror of
/// `Proposal.deltas`' account face + `applyRowDelta`'s keyed fold):
/// the src update and the dst update are each computed from the
/// PRE-transfer rows (the snapshot, never the intermediate), then
/// folded in order by keyed replacement — a self-transfer's second
/// update last-wins over the first (the pinned drift; see the module
/// header).
fn apply_transfer(accounts: &[Account], t: &Transfer) -> Vec<Account> {
    let amt = t.amount as i64;
    let r1 = accounts.iter().find(|a| a.id == t.src).map(|r| with_bal(r, -amt));
    let r2 = accounts.iter().find(|a| a.id == t.dst).map(|r| with_bal(r, amt));
    let mut out = accounts.to_vec();
    if let Some(r) = r1 {
        out = apply_one(&out, &r);
    }
    if let Some(r) = r2 {
        out = apply_one(&out, &r);
    }
    out
}

/// A ledger `Row` → its `Transfer` image (`None` = the row lost its
/// own schema — a typed refusal, never a panic or a silent skip).
fn row_to_transfer(r: &Row) -> Option<Transfer> {
    let vs = r.values();
    match vs {
        [Value::U64(tid), Value::U64(src), Value::U64(dst), Value::U64(amount)] => {
            Some(Transfer { tid: *tid, src: *src, dst: *dst, amount: *amount })
        }
        _ => None,
    }
}

/// A `Transfer` → its journal `Row` (the ledger schema's field order).
fn transfer_to_row(t: &Transfer) -> Row {
    let schema = ledger_schema();
    Row::build(
        &schema,
        vec![
            Value::U64(t.tid),
            Value::U64(t.src),
            Value::U64(t.dst),
            Value::U64(t.amount),
        ],
    )
    .unwrap_or_else(|e| panic!("the ledger row matches its own schema: {e}"))
}

/// THE VIOLATION QUERIES (the mirror of `Violate.violations`, in
/// query order: duplicate ids per occurrence, negative balances,
/// dangling src, dangling dst) over any (accounts, transfers) pair —
/// the free face the check runs over the POST-state working copy.
fn violations_over(accounts: &[Account], transfers: &[Transfer]) -> Vec<ViolationRow> {
    let ids: Vec<u64> = accounts.iter().map(|a| a.id).collect();
    let mut out = Vec::new();
    for k in &ids {
        if ids.iter().filter(|x| *x == k).count() > 1 {
            out.push(ViolationRow::DuplicateId(*k));
        }
    }
    for a in accounts {
        if a.balance < 0 {
            out.push(ViolationRow::NegativeBalance { id: a.id, balance: a.balance });
        }
    }
    for t in transfers {
        if !ids.contains(&t.src) {
            out.push(ViolationRow::UnresolvedSrc { tid: t.tid, src: t.src });
        }
    }
    for t in transfers {
        if !ids.contains(&t.dst) {
            out.push(ViolationRow::UnresolvedDst { tid: t.tid, dst: t.dst });
        }
    }
    out
}

impl Live {
    /// Opens the live state at `journal_path`: the journal's replay
    /// restores the ledger, the account movements derive from it (the
    /// fixture balances folded through each accepted transfer), and
    /// the version is the fixture's 1 + one bump per accepted commit
    /// (each accepted commit inserts exactly one ledger row — the
    /// derivation the reopen tooth pins).
    ///
    /// # Errors
    /// The journal failed to open (I/O, a corrupt COMPLETE frame), or
    /// a journaled row lost its schema.
    pub fn open(journal_path: &Path) -> Result<Self, HostError> {
        let journal = Journal::open(journal_path, ledger_schema())?;
        let mut transfers = Vec::new();
        for r in journal.state().rows() {
            let t = row_to_transfer(r)
                .ok_or_else(|| HostError::LiveState("a journaled ledger row lost its schema".into()))?;
            transfers.push(t);
        }
        // The fixture (Commit.fixtureSnap's accounts) replayed forward.
        let mut accounts = vec![
            Account { id: 1, owner: "alice".into(), balance: 100 },
            Account { id: 2, owner: "bob".into(), balance: 50 },
        ];
        for t in &transfers {
            accounts = apply_transfer(&accounts, t);
        }
        let version = 1 + journal.len();
        Ok(Self { version, accounts, transfers, journal })
    }

    /// THE HANDWRITTEN COMMAND: propose a transfer against the CURRENT
    /// snapshot (the base is the race-honesty carrier — 03 §3). Rust
    /// keeps the algorithmic freedom; the checker owns the verdict.
    #[must_use]
    pub fn propose(&self, tid: u64, src: u64, dst: u64, amount: u64) -> Proposal {
        Proposal { base: self.version, tid, src, dst, amount }
    }

    /// The violation queries over THIS state (the mirror of
    /// `Violate.violations`, in query order).
    #[must_use]
    pub fn violations(&self) -> Vec<ViolationRow> {
        violations_over(&self.accounts, &self.transfers)
    }

    /// THE CHECK (03 §8's honest first cut): the violation queries
    /// over the POST-state — the delta applied to a WORKING COPY
    /// (this state is never touched by a check; external effects
    /// never occur before authorization). Full recomputation — the
    /// change-proportional face is the dbsp-circuit wave's
    /// `incrementalize_ok`, named not faked.
    #[must_use]
    pub fn check(&self, p: &Proposal) -> Vec<ViolationRow> {
        let (accounts, transfers) = self.post_state(p);
        violations_over(&accounts, &transfers)
    }

    /// The POST-STATE (the working copy): the transfer insert ALWAYS
    /// fires (the intent recorded — the audit face); the two account
    /// updates fire only when the snapshot has the endpoint row; a
    /// self-transfer's two updates last-wins (the pinned drift).
    fn post_state(&self, p: &Proposal) -> (Vec<Account>, Vec<Transfer>) {
        let mut accounts = self.accounts.clone();
        accounts = apply_transfer(&accounts, &Transfer {
            tid: p.tid, src: p.src, dst: p.dst, amount: p.amount,
        });
        let mut transfers = self.transfers.clone();
        transfers.push(Transfer {
            tid: p.tid, src: p.src, dst: p.dst, amount: p.amount,
        });
        (accounts, transfers)
    }

    /// THE COMMIT (the transactional adapter, live): stale refuses
    /// FIRST (on the version, before any content look); a violated
    /// post-state refuses with the rows and produces NO state change
    /// and NO journal entry; an accepted commit journals the ledger
    /// row (the authorized effect — written BEFORE the in-memory
    /// state moves) and bumps the version.
    ///
    /// # Errors
    /// Only genuine faults (the journal's I/O); a refusal is a typed
    /// [`LiveVerdict`], never an error.
    pub fn commit(&mut self, p: &Proposal) -> Result<LiveVerdict, HostError> {
        if p.base != self.version {
            return Ok(LiveVerdict::Stale { base: p.base, got: self.version });
        }
        let vs = self.check(p);
        if !vs.is_empty() {
            return Ok(LiveVerdict::Violated(vs));
        }
        let t = Transfer { tid: p.tid, src: p.src, dst: p.dst, amount: p.amount };
        // The effect seam: append + fsync before the call returns; a
        // fault here leaves the in-memory state UNCHANGED (memory
        // never runs ahead of the durable log).
        self.journal.record(Delta::Insert(transfer_to_row(&t)))?;
        let (accounts, transfers) = self.post_state(p);
        self.accounts = accounts;
        self.transfers = transfers;
        self.version += 1;
        Ok(LiveVerdict::Committed { version: self.version })
    }

    /// The snapshot version (the race-honesty carrier's current face).
    #[must_use]
    pub fn version(&self) -> u64 {
        self.version
    }

    /// The account table (the replay-derived state).
    #[must_use]
    pub fn accounts(&self) -> &[Account] {
        &self.accounts
    }

    /// The transfer ledger.
    #[must_use]
    pub fn transfers(&self) -> &[Transfer] {
        &self.transfers
    }
}

/// The repo root (the commit-duel vectors are repo-root-relative —
/// the committed convention, next to the generated crate).
#[must_use]
pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The commit duel's manifest path (inside the generated crate's
/// tests — the duel emitter's ONE directory).
fn commit_duel_dir(root: &Path) -> PathBuf {
    root.join("crates/schema-generated/tests/duel-commit")
}

/// The committed manifest's expectation (Kit.Duel's decode vocabulary,
/// at the commit duel's two arms).
#[derive(Debug, Clone, PartialEq, Eq)]
enum CommitExpect {
    /// The Lean checker ACCEPTED the proposal (computed at generation).
    Accept,
    /// The Lean checker REFUSED it.
    Refuse,
}

impl CommitExpect {
    /// Parses the manifest's second column. `None` = unknown
    /// vocabulary — the caller refuses (never a guess).
    fn parse(s: &str) -> Option<Self> {
        match s {
            "decode accept" => Some(Self::Accept),
            "refuse" => Some(Self::Refuse),
            _ => None,
        }
    }
}

/// One commit-duel row's outcome (the verdict vocabulary is THE ONE
/// `RowVerdict` — the wasm duel's, never a second one).
#[derive(Debug, Clone)]
pub struct CommitDuelRow {
    /// The vector path (repo-root-relative).
    pub path: String,
    /// The verdict.
    pub verdict: RowVerdict,
}

/// The commit duel's report: the Lean generator's provenance + every
/// row's verdict. TESTED AGREEMENT (03 §3's differential level) —
/// never a theorem; the rendering says so.
#[derive(Debug, Clone)]
pub struct CommitDuelReport {
    /// The manifest's generator row.
    pub generator: String,
    /// The rows, manifest order.
    pub rows: Vec<CommitDuelRow>,
}

impl CommitDuelReport {
    /// THE duel verdict: all-agree folds to agree; the FIRST
    /// non-agree row is the failure evidence (the
    /// minimal-counterexample discipline).
    #[must_use]
    pub fn verdict(&self) -> RowVerdict {
        for r in &self.rows {
            match &r.verdict {
                RowVerdict::Agree => continue,
                v @ (RowVerdict::Diverge { .. } | RowVerdict::Refused { .. }) => {
                    let mut w = v.clone();
                    if let RowVerdict::Diverge { loc, .. } = &mut w {
                        *loc = r.path.clone();
                    }
                    return w;
                }
            }
        }
        RowVerdict::Agree
    }

    /// The honest rendering (the tier sentence is part of the report).
    #[must_use]
    pub fn render(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!(
            "commit duel (generator {}): TESTED AGREEMENT — the \
             differential level (notes/v3/03 section 3), never a theorem\n",
            self.generator
        ));
        for r in &self.rows {
            out.push_str(&format!("  {}: {}\n", r.path, r.verdict.render()));
        }
        out
    }
}

/// Decodes one proposal off the wire (five canonical varints — the
/// GENERATED decoder's, never a hand-mirrored one). `None` = the
/// vector does not decode (a tampered vector's typed face).
fn dec_proposal(bs: &[u8]) -> Option<Proposal> {
    let mut rest: &[u8] = bs;
    let base = schema_generated::dec_u64(&mut rest).ok()?;
    let tid = schema_generated::dec_u64(&mut rest).ok()?;
    let src = schema_generated::dec_u64(&mut rest).ok()?;
    let dst = schema_generated::dec_u64(&mut rest).ok()?;
    let amount = schema_generated::dec_u64(&mut rest).ok()?;
    if !rest.is_empty() {
        return None;
    }
    Some(Proposal { base, tid, src, dst, amount })
}

/// Runs ONE duel row: hash-tie the vector to its sidecar, decode, run
/// the LIVE loop over a FRESH fixture (an empty journal in scratch),
/// compare the live verdict with the Lean-computed expectation.
fn run_commit_row(root: &Path, path: &str, expect: &CommitExpect) -> Result<RowVerdict, HostError> {
    if !path.starts_with("crates/") {
        return Err(HostError::DuelManifest(format!(
            "{path}: the vector path is not repo-root-relative under crates/"
        )));
    }
    let vp = root.join(path);
    let bytes = std::fs::read(&vp)
        .map_err(|source| HostError::Io { what: "commit-duel vector", source })?;
    let sidecar = std::fs::read_to_string(PathBuf::from(format!("{}.hdr", vp.display())))
        .map_err(|source| HostError::Io { what: "commit-duel vector sidecar", source })?;
    let declared = sidecar_hash(&sidecar).ok_or(
        HostError::SidecarMalformed("the commit-duel vector's sidecar names no content hash"),
    )?;
    let computed = bytes_hash(&bytes);
    if computed != declared {
        return Ok(RowVerdict::Refused {
            why: format!("sidecar hash mismatch: declared {declared}, computed {computed}"),
        });
    }
    let p = match dec_proposal(&bytes) {
        Some(p) => p,
        None => {
            return Ok(RowVerdict::Refused {
                why: "the vector does not decode as five varints".to_string(),
            });
        }
    };
    // The live loop over a fresh fixture: an empty scratch journal →
    // the fixture snapshot (version 1, alice 100 / bob 50, no ledger).
    let scratch = std::env::temp_dir().join(format!(
        "mandate-host-duel-{}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0),
        path.replace(['/', '\\'], "_"),
    ));
    std::fs::create_dir_all(&scratch)
        .map_err(|source| HostError::Io { what: "duel scratch dir", source })?;
    let live = Live::open(&scratch.join("journal.bin"))?;
    let verdict = live.commit(&p)?;
    std::fs::remove_dir_all(&scratch)
        .map_err(|source| HostError::Io { what: "duel scratch cleanup", source })?;
    Ok(match (expect, &verdict) {
        (CommitExpect::Accept, LiveVerdict::Committed { .. }) => RowVerdict::Agree,
        (CommitExpect::Refuse, LiveVerdict::Stale { .. } | LiveVerdict::Violated(_)) => {
            RowVerdict::Agree
        }
        (CommitExpect::Accept, other) => RowVerdict::Diverge {
            loc: path.to_string(),
            lhs: "accept".to_string(),
            rhs: verdict_render(other),
        },
        (CommitExpect::Refuse, other) => RowVerdict::Diverge {
            loc: path.to_string(),
            lhs: "refuse".to_string(),
            rhs: verdict_render(other),
        },
    })
}

/// The verdict's one-line face for the divergence witness.
fn verdict_render(v: &LiveVerdict) -> String {
    match v {
        LiveVerdict::Committed { version } => format!("committed (version {version})"),
        LiveVerdict::Stale { base, got } => format!("stale: base {base} vs {got}"),
        LiveVerdict::Violated(vs) => {
            format!("violated: {:?}", vs.iter().map(ViolationRow::render).collect::<Vec<_>>())
        }
    }
}

/// Runs the commit duel: reads the committed manifest, ties + decodes
/// each vector, runs the LIVE loop, compares verdict-for-verdict with
/// the Lean checker's committed expectations. The discipline that
/// binds the live mirror to the Lean checker (03 §3's differential
/// level — the checker cannot itself compile to the guest's fragment).
///
/// # Errors
/// The manifest is malformed, a vector is unreadable, or the live
/// loop hit a genuine fault (I/O / journal).
pub fn run_commit_duel(root: &Path) -> Result<CommitDuelReport, HostError> {
    let manifest = std::fs::read_to_string(commit_duel_dir(root).join("manifest.txt"))
        .map_err(|source| HostError::Io { what: "commit-duel manifest", source })?;
    let mut generator: Option<String> = None;
    let mut rows = Vec::new();
    for line in manifest.lines().filter(|l| !l.is_empty()) {
        // The 2-line GENERATED header (skipped; the headers gate owns
        // the audit).
        if line.starts_with("//") {
            continue;
        }
        let mut parts = line.split('\t');
        let keyword = parts.next().unwrap_or_default();
        if keyword == "generator" {
            generator = Some(
                parts
                    .next()
                    .ok_or_else(|| {
                        HostError::DuelManifest("the generator row names no module".into())
                    })?
                    .to_string(),
            );
            continue;
        }
        let expect = parts
            .next()
            .and_then(CommitExpect::parse)
            .ok_or_else(|| HostError::DuelManifest(format!("{keyword}: unknown expectation")))?;
        if parts.next().is_some() {
            return Err(HostError::DuelManifest(format!("{keyword}: extra columns")));
        }
        rows.push(CommitDuelRow {
            path: keyword.to_string(),
            verdict: run_commit_row(root, keyword, &expect)?,
        });
    }
    let generator = generator
        .ok_or_else(|| HostError::DuelManifest("no generator row".to_string()))?;
    if rows.is_empty() {
        return Err(HostError::DuelManifest("no expectation rows".to_string()));
    }
    Ok(CommitDuelReport { generator, rows })
}
