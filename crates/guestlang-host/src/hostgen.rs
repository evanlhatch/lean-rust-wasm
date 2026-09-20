//! HOST-SIDE GENERATION (W8.11): the host PRODUCES its binding contract
//! from the committed universe (the byte-tied
//! `lean/schema-lang/goldens/universe.snapshot`) and validates it
//! against the compiled-in expectation — instead of only consuming
//! hand-copied constants.
//!
//! MECHANISM (runbook W8.11's conservative default — validation, no new
//! codegen path): the snapshot is PARSED here (a faithful Rust port of
//! `SchemaLang.Snapshot.parse` — the Lean module is the format's ONLY
//! other encoder/decoder), and the parsed universe is PROJECTED to the
//! two artifacts the host consumes:
//!
//! 1. the canonical schema-surface string (`fn/arity`, comma-joined —
//!    the oracle's flat-arg convention, mirrored from
//!    [`crate::schema`]), checked against
//!    [`crate::schema::EXPECTED_DEMO_SURFACE`];
//! 2. the schema's type/func declarations (records, variants, cases,
//!    field/param/ret TYPES), checked against what `bindgen!` actually
//!    consumed (`wit/gateway.wit`, resolved with wit-parser in
//!    `tests/hostgen_byte_tie.rs` — the type-level byte-tie moved into
//!    the host).
//!
//! This closes the gap the fault-injection suite recorded
//! (`tests/fault_injection.rs` header: "the snapshot's only consumer is
//! a test-side line parser … no runtime failure mode exists to pin") —
//! a corrupt or drifted snapshot now has a structured, fail-fast host
//! failure mode ([`HostgenError`]).
//!
//! DESIGN DECISION — why not byte-render `wit/gateway.wit` here: a
//! Rust re-implementation of the Lean WIT emitter would be a SECOND
//! writer for that artifact path (the architecture's one-writer rule)
//! and would couple the host to the emitter's formatting. The
//! structural projection keeps the Lean emitter the sole writer while
//! the host still DERIVES its contract from the committed universe.
//!
//! FOLLOW-UP (the ambitious half of W8.11, noted not built): drive the
//! Lean emitters IN-PROCESS via `crates/lean-ffi` (the verified-ledger
//! study's C-shim pattern: only codec bytes cross the boundary) — the
//! host would then run the real emitters rather than project from the
//! snapshot. The snapshot projection is the dependency-free v1.
//!
//! Losslessness: parse stores every name VERBATIM (the format's own
//! spelling, the Lean authority's law — `parse ∘ render = id`), with NO
//! case normalization: the snapshot writer never kebab-cases, so a
//! parser that did would be a second, LOSSY codec. The WIT wire
//! spelling (`order-item`) is the PROJECTION layer's job — see
//! [`Universe::surface_entries`], the one place this module kebabs.
//! Regression pins: `tests/snapshot_differential.rs` (the Lean↔Rust
//! differential over generated fixtures) + the `ty()`/CRLF laws in
//! this module's tests.

use std::fmt;

use crate::schema;

/// Maximum `parse_ty_at` nesting depth (the Lean parser's fuel, made
/// structural): each recursive call consumes at least one character, so
/// real types never come close; a corrupted snapshot with pathological
/// nesting fails LOUD instead of blowing the stack.
const MAX_TY_DEPTH: usize = 64;

/// Kebab-case a registry name (`OrderError` → `order-error`,
/// `getUser` → `get-user`). Mirrors the emitter's wire spelling: an
/// uppercase char after the first becomes `-` + lowercase.
pub fn kebab(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() && i > 0 {
            out.push('-');
        }
        out.push(c.to_ascii_lowercase());
    }
    out
}

/// A snapshot type — the Rust twin of `Ty.toSnapshot`'s paren encoding
/// (`option(u64)`, `list(ty(User))`, `result(string,ty(User))`, …).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    /// `bool`
    Bool,
    /// `u8`
    U8,
    /// `u16`
    U16,
    /// `u32`
    U32,
    /// `u64`
    U64,
    /// `i8`
    I8,
    /// `i16`
    I16,
    /// `i32`
    I32,
    /// `i64`
    I64,
    /// `f32`
    F32,
    /// `f64`
    F64,
    /// `string`
    String,
    /// `bytes`
    Bytes,
    /// `option(…)`
    Option(Box<Ty>),
    /// `result(ok,err)`
    Result(Box<Ty>, Box<Ty>),
    /// `list(…)`
    List(Box<Ty>),
    /// `map(key,value)` — key is a scalar key type
    Map(Box<Ty>, Box<Ty>),
    /// `set(key)` — element is a scalar key type
    Set(Box<Ty>),
    /// `future(…)` — the async marker: the emitter renders a future
    /// return as `async func` over the UNWRAPPED payload
    Future(Box<Ty>),
    /// `stream(…)`
    Stream(Box<Ty>),
    /// `tensor(dims…;elem)` — dims ride `;`-separated before the element
    Tensor(Vec<u64>, Box<Ty>),
    /// `ty(<name>)` — a named ref into the same universe, VERBATIM
    /// (parse is lossless; the writer never kebab-cases)
    Named(String),
}

/// Is this a scalar KEY type (`KeyTy` — map keys / set elements; no
/// floats, no composites)? The parse-side gate twin of
/// `Ty.toKeyTy?`.
#[must_use]
fn is_key_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::String
    )
}

/// The optional per-func semantics line (`sem <nullsem> <determinism>
/// [stream]`) — written only when non-default, so `None` = the
/// defaults.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncSem {
    /// `strict | propagate | custom`
    pub null_sem: String,
    /// `pure | stable | volatile`
    pub determinism: String,
    /// The optional 4th token (`stream`); absent = `once` (default).
    pub stream: bool,
}

/// One universe item — record / variant / func / resource, members in
/// registry order, names VERBATIM (parse is lossless; the kebab WIT
/// spelling is the projection layer's).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    /// `record <name>` + `field` lines
    Record {
        /// record name, verbatim
        name: String,
        /// fields in order: (name, type)
        fields: Vec<(String, Ty)>,
    },
    /// `variant <name>` + `case` lines
    Variant {
        /// variant name, verbatim
        name: String,
        /// cases in order: (name, payload type — `None` = bare)
        cases: Vec<(String, Option<Ty>)>,
    },
    /// `func <name>` + `param`/`ret` (+ optional `sem`) lines
    Func {
        /// func name, verbatim
        name: String,
        /// params in order: (name, type)
        params: Vec<(String, Ty)>,
        /// the return type (`future(…)` = the async marker)
        ret: Ty,
        /// non-default semantics, when the snapshot carried a `sem` line
        sem: Option<FuncSem>,
    },
    /// `resource <name>`
    Resource {
        /// resource name, verbatim
        name: String,
    },
}

/// A structured snapshot parse failure: the offending line number
/// (1-based, over the RAW file — blank lines count) and what the
/// parser wanted. Loud over silent, always: a snapshot that doesn't
/// parse is a gate failure, never a skip.
#[derive(Debug, Clone)]
pub struct ParseError {
    /// 1-based raw-file line number
    pub line: usize,
    /// the specific corruption class
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "snapshot: line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for ParseError {}

/// Parse one type token (the `<ty>` grammar — no spaces, fuel/depth
/// bounded, loud on trailing garbage).
fn parse_ty_text(s: &str) -> Result<Ty, String> {
    let (ty, rest) = parse_ty_at(s.as_bytes(), 0)?;
    if rest.is_empty() {
        Ok(ty)
    } else {
        Err(format!(
            "snapshot: trailing garbage `{}`",
            String::from_utf8_lossy(rest)
        ))
    }
}

/// Parse a type AT a byte offset; returns the type and the unconsumed
/// rest (the Lean parser's `(Ty × List Char)` discipline).
fn parse_ty_at(cs: &[u8], depth: usize) -> Result<(Ty, &[u8]), String> {
    if depth > MAX_TY_DEPTH {
        return Err("snapshot: parse depth exceeded (malformed nesting)".to_string());
    }
    let kw_len = cs
        .iter()
        .position(|b| !b.is_ascii_alphanumeric())
        .unwrap_or(cs.len());
    let kw = std::str::from_utf8(&cs[..kw_len])
        .map_err(|_| "snapshot: invalid UTF-8 in type token".to_string())?;
    let rest = &cs[kw_len..];

    /// One-arg constructor (`option(…)`, `list(…)`, `future(…)`,
    /// `stream(…)`): `(` type `)`.
    fn arg1<'a>(
        kw: &str,
        rest: &'a [u8],
        depth: usize,
        wrap: fn(Box<Ty>) -> Ty,
    ) -> Result<(Ty, &'a [u8]), String> {
        match rest.first() {
            Some(b'(') => {
                let (t, r) = parse_ty_at(&rest[1..], depth + 1)?;
                match r.first() {
                    Some(b')') => Ok((wrap(Box::new(t)), &r[1..])),
                    _ => Err(format!("snapshot: expected ')' after `{kw}(`")),
                }
            }
            _ => Err(format!("snapshot: expected '(' after `{kw}`")),
        }
    }

    match kw {
        "bool" => Ok((Ty::Bool, rest)),
        "u8" => Ok((Ty::U8, rest)),
        "u16" => Ok((Ty::U16, rest)),
        "u32" => Ok((Ty::U32, rest)),
        "u64" => Ok((Ty::U64, rest)),
        "i8" => Ok((Ty::I8, rest)),
        "i16" => Ok((Ty::I16, rest)),
        "i32" => Ok((Ty::I32, rest)),
        "i64" => Ok((Ty::I64, rest)),
        "f32" => Ok((Ty::F32, rest)),
        "f64" => Ok((Ty::F64, rest)),
        "string" => Ok((Ty::String, rest)),
        "bytes" => Ok((Ty::Bytes, rest)),
        "option" => arg1(kw, rest, depth, Ty::Option),
        "list" => arg1(kw, rest, depth, Ty::List),
        "future" => arg1(kw, rest, depth, Ty::Future),
        "stream" => arg1(kw, rest, depth, Ty::Stream),
        "set" => {
            // the key GATE: the element must be a scalar key type
            match rest.first() {
                Some(b'(') => {
                    let (t, r) = parse_ty_at(&rest[1..], depth + 1)?;
                    if !is_key_ty(&t) {
                        return Err("snapshot: set element is not a scalar key type".to_string());
                    }
                    match r.first() {
                        Some(b')') => Ok((Ty::Set(Box::new(t)), &r[1..])),
                        _ => Err("snapshot: expected ')' after `set(…`".to_string()),
                    }
                }
                _ => Err("snapshot: expected '(' after `set`".to_string()),
            }
        }
        "map" => {
            // map(key,value): the key GATE applies, then the comma
            match rest.first() {
                Some(b'(') => {
                    let (kt, r) = parse_ty_at(&rest[1..], depth + 1)?;
                    if !is_key_ty(&kt) {
                        return Err("snapshot: map key is not a scalar key type".to_string());
                    }
                    match r.first() {
                        Some(b',') => {
                            let (vt, r) = parse_ty_at(&r[1..], depth + 1)?;
                            match r.first() {
                                Some(b')') => Ok((Ty::Map(Box::new(kt), Box::new(vt)), &r[1..])),
                                _ => {
                                    Err("snapshot: expected ')' after map's value type".to_string())
                                }
                            }
                        }
                        _ => {
                            Err("snapshot: expected ',' between map's key and value types"
                                .to_string())
                        }
                    }
                }
                _ => Err("snapshot: expected '(' after `map`".to_string()),
            }
        }
        "result" => match rest.first() {
            Some(b'(') => {
                let (ok, r) = parse_ty_at(&rest[1..], depth + 1)?;
                match r.first() {
                    Some(b',') => {
                        let (err, r) = parse_ty_at(&r[1..], depth + 1)?;
                        match r.first() {
                            Some(b')') => Ok((Ty::Result(Box::new(ok), Box::new(err)), &r[1..])),
                            _ => Err("snapshot: expected ')' after result's err type".to_string()),
                        }
                    }
                    _ => Err("snapshot: expected ',' between result's types".to_string()),
                }
            }
            _ => Err("snapshot: expected '(' after `result`".to_string()),
        },
        "ty" => match rest.first() {
            Some(b'(') => {
                let end = rest[1..]
                    .iter()
                    .position(|b| *b == b')')
                    .ok_or("snapshot: expected ')' after ty ref")?;
                let name = std::str::from_utf8(&rest[1..1 + end])
                    .map_err(|_| "snapshot: invalid UTF-8 in ty ref")?;
                if name.is_empty() {
                    return Err("snapshot: empty ty ref".to_string());
                }
                Ok((Ty::Named(name.to_string()), &rest[1 + end + 1..]))
            }
            _ => Err("snapshot: expected '(' after `ty`".to_string()),
        },
        "tensor" => {
            // `tensor(` (dim ';')* elem ')' — nat atoms first, each
            // consumed WITH its ';'; zero dims = `tensor(;elem)`
            match rest.first() {
                Some(b'(') => {
                    let mut dims = Vec::new();
                    let mut r = &rest[1..];
                    loop {
                        let d_end = r
                            .iter()
                            .position(|b| !b.is_ascii_digit())
                            .unwrap_or(r.len());
                        if d_end == 0 {
                            break; // no more dims
                        }
                        let dim = std::str::from_utf8(&r[..d_end])
                            .map_err(|_| "snapshot: invalid UTF-8 in tensor dim")?
                            .parse::<u64>()
                            .map_err(|e| format!("snapshot: bad tensor dim: {e}"))?;
                        dims.push(dim);
                        match r[d_end..].first() {
                            Some(b';') => r = &r[d_end + 1..],
                            _ => return Err("snapshot: expected ';' after tensor dim".to_string()),
                        }
                    }
                    let (elem, r) = parse_ty_at(r, depth + 1)?;
                    match r.first() {
                        Some(b')') => Ok((Ty::Tensor(dims, Box::new(elem)), &r[1..])),
                        _ => Err("snapshot: expected ')' after tensor".to_string()),
                    }
                }
                _ => Err("snapshot: expected '(' after `tensor`".to_string()),
            }
        }
        other => Err(format!("snapshot: unknown type token `{other}`")),
    }
}

/// The partially-accumulated open item (member lists in arrival order;
/// closed in reverse to restore registry order — the Lean fold's
/// discipline).
enum Open {
    Record {
        name: String,
        fields: Vec<(String, Ty)>,
    },
    Variant {
        name: String,
        cases: Vec<(String, Option<Ty>)>,
    },
    Func {
        name: String,
        params: Vec<(String, Ty)>,
        ret: Option<Ty>,
        sem: Option<FuncSem>,
    },
    Resource(String),
}

impl Open {
    /// Close the open item. Members were APPENDED in arrival order
    /// (the Lean fold PREPENDS then reverses — same result); a func
    /// without `ret` is malformed — the writer always emits one.
    fn close(self) -> Result<Item, String> {
        match self {
            Open::Record { name, fields } => Ok(Item::Record { name, fields }),
            Open::Variant { name, cases } => Ok(Item::Variant { name, cases }),
            Open::Func {
                name,
                params,
                ret,
                sem,
            } => match ret {
                Some(ret) => Ok(Item::Func {
                    name,
                    params,
                    ret,
                    sem,
                }),
                None => Err(format!("snapshot: func `{name}` has no `ret` line")),
            },
            Open::Resource(name) => Ok(Item::Resource { name }),
        }
    }
}

/// Validate one `sem` line's tokens against the closed sets
/// (`NullSem.ofToken?` / `Determinism.ofToken?` twins).
fn parse_sem(tokens: &[&str]) -> Result<FuncSem, String> {
    const NULL_SEMS: [&str; 3] = ["strict", "propagate", "custom"];
    const DETERMINISMS: [&str; 3] = ["pure", "stable", "volatile"];
    let ns = tokens[1];
    let ds = tokens[2];
    if !NULL_SEMS.contains(&ns) {
        return Err(format!(
            "snapshot: unknown nullSem token `{ns}` — valid: strict, propagate, custom"
        ));
    }
    if !DETERMINISMS.contains(&ds) {
        return Err(format!(
            "snapshot: unknown determinism token `{ds}` — valid: pure, stable, volatile"
        ));
    }
    Ok(FuncSem {
        null_sem: ns.to_string(),
        determinism: ds.to_string(),
        stream: tokens.len() == 4 && tokens[3] == "stream",
    })
}

/// Parse snapshot text back to a universe (the faithful port of
/// `SchemaLang.Snapshot.parse`: line-based, first error sticks, blank
/// lines skipped, names VERBATIM — parse is lossless on both sides).
/// LF-only, like the Lean authority: the writer never emits `\r`, so a
/// `\r` sticks to its line's last token and fails loud (unrecognized
/// line / trailing garbage) — `split('\n')`, NOT `lines()` (which
/// silently strips `\r`; the CRLF drift's fix).
///
/// # Errors
/// A [`ParseError`] naming the 1-based line and corruption class for
/// ANY malformed input — never a silent skip.
pub fn parse_snapshot(text: &str) -> Result<Vec<Item>, ParseError> {
    let mut done: Vec<Item> = Vec::new();
    let mut cur: Option<Open> = None;
    let mut last_line: usize = 0;

    for (idx, line) in text.split('\n').enumerate() {
        let n = idx + 1;
        if line.is_empty() {
            continue;
        }
        last_line = n;
        // close the open item (if any) and start the new one
        let restart = |done: &mut Vec<Item>, cur: &mut Option<Open>, o: Open| {
            if let Some(open) = cur.take() {
                done.push(open.close().map_err(|e| (n, e))?);
            }
            *cur = Some(o);
            Ok(())
        };
        let tokens: Vec<&str> = line.split(' ').collect();
        let err = |message: &str| ParseError {
            line: n,
            message: message.to_string(),
        };
        match tokens.as_slice() {
            ["record", name] => {
                restart(
                    &mut done,
                    &mut cur,
                    Open::Record {
                        name: name.to_string(),
                        fields: Vec::new(),
                    },
                )
                .map_err(|e: (usize, String)| err(&e.1))?;
            }
            ["variant", name] => {
                restart(
                    &mut done,
                    &mut cur,
                    Open::Variant {
                        name: name.to_string(),
                        cases: Vec::new(),
                    },
                )
                .map_err(|e: (usize, String)| err(&e.1))?;
            }
            ["func", name] => {
                restart(
                    &mut done,
                    &mut cur,
                    Open::Func {
                        name: name.to_string(),
                        params: Vec::new(),
                        ret: None,
                        sem: None,
                    },
                )
                .map_err(|e: (usize, String)| err(&e.1))?;
            }
            ["resource", name] => {
                restart(&mut done, &mut cur, Open::Resource(name.to_string()))
                    .map_err(|e: (usize, String)| err(&e.1))?;
            }
            ["field", name, ty_text] => match &mut cur {
                Some(Open::Record { fields, .. }) => {
                    let t = parse_ty_text(ty_text).map_err(|e| err(&e))?;
                    fields.push((name.to_string(), t));
                }
                _ => return Err(err("snapshot: `field` outside a record")),
            },
            ["case", name] => match &mut cur {
                Some(Open::Variant { cases, .. }) => {
                    cases.push((name.to_string(), None));
                }
                _ => return Err(err("snapshot: `case` outside a variant")),
            },
            ["case", name, ty_text] => match &mut cur {
                Some(Open::Variant { cases, .. }) => {
                    let t = parse_ty_text(ty_text).map_err(|e| err(&e))?;
                    cases.push((name.to_string(), Some(t)));
                }
                _ => return Err(err("snapshot: `case` outside a variant")),
            },
            ["param", name, ty_text] => match &mut cur {
                Some(Open::Func { params, ret, .. }) if ret.is_none() => {
                    let t = parse_ty_text(ty_text).map_err(|e| err(&e))?;
                    params.push((name.to_string(), t));
                }
                Some(Open::Func { .. }) => {
                    return Err(err("snapshot: `param` after `ret`"));
                }
                _ => return Err(err("snapshot: `param` outside a func")),
            },
            ["ret", ty_text] => match &mut cur {
                Some(Open::Func { ret, .. }) if ret.is_none() => {
                    *ret = Some(parse_ty_text(ty_text).map_err(|e| err(&e))?);
                }
                Some(Open::Func { .. }) => {
                    return Err(err("snapshot: duplicate `ret`"));
                }
                _ => return Err(err("snapshot: `ret` outside a func")),
            },
            ["sem", _, _, "stream"] | ["sem", _, _] => match &mut cur {
                Some(Open::Func { ret, sem, .. }) if ret.is_some() && sem.is_none() => {
                    *sem = Some(parse_sem(&tokens).map_err(|e| err(&e))?);
                }
                Some(Open::Func { sem, .. }) if sem.is_some() => {
                    return Err(err("snapshot: duplicate `sem`"));
                }
                Some(Open::Func { .. }) => {
                    return Err(err("snapshot: `sem` before `ret`"));
                }
                _ => return Err(err("snapshot: `sem` outside a func")),
            },
            _ => {
                return Err(err(&format!("snapshot: unrecognized line `{line}`")));
            }
        }
    }
    if let Some(open) = cur.take() {
        let item = open.close().map_err(|e| ParseError {
            line: last_line,
            message: e,
        })?;
        done.push(item);
    }
    Ok(done)
}

/// A parsed universe: the committed snapshot's items in registry
/// order, names VERBATIM (parse is lossless).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Universe {
    items: Vec<Item>,
}

impl Universe {
    /// Wrap parsed items.
    #[must_use]
    pub const fn new(items: Vec<Item>) -> Self {
        Self { items }
    }

    /// The items, registry order.
    #[must_use]
    pub fn items(&self) -> &[Item] {
        &self.items
    }

    /// Find an item by its VERBATIM (snapshot-spelling) name.
    #[must_use]
    pub fn find(&self, name: &str) -> Option<&Item> {
        self.items.iter().find(|it| match it {
            Item::Record { name: n, .. }
            | Item::Variant { name: n, .. }
            | Item::Func { name: n, .. }
            | Item::Resource { name: n } => n == name,
        })
    }

    /// The oracle's flat-arg arity of a type: a record arg rides the
    /// boundary as its FIELD VALUES FLAT, a variant arg as
    /// `[discr, payload]`, everything else one slot. Twin of
    /// `schema::flat_arity` on the component-type side.
    ///
    /// # Errors
    /// A `ty()` ref that doesn't resolve in this universe (a corrupt
    /// snapshot) is loud.
    pub fn flat_arity(&self, ty: &Ty) -> Result<usize, String> {
        match ty {
            Ty::Named(n) => match self.find(n) {
                Some(Item::Record { fields, .. }) => Ok(fields.len()),
                Some(Item::Variant { .. }) => Ok(2),
                Some(Item::Resource { .. } | Item::Func { .. }) => Ok(1),
                None => Err(format!(
                    "hostgen: named type `{n}` not found in the universe"
                )),
            },
            _ => Ok(1),
        }
    }

    /// PRODUCE the schema-derived surface entries: `(kebab fn name,
    /// flat arity)` per func, in registry order (the oracle's
    /// first-occurrence order). This is the host GENERATING its side
    /// of the surface contract from the committed universe — and the
    /// ONE place this module kebab-cases: the WIT wire spelling is the
    /// PROJECTION's convention, never the parser's (parse is lossless;
    /// the kebab-at-parse drift's fix).
    ///
    /// # Errors
    /// A param type referencing an unknown item (corrupt snapshot).
    pub fn surface_entries(&self) -> Result<Vec<(String, usize)>, String> {
        let mut out = Vec::new();
        for item in &self.items {
            if let Item::Func { name, params, .. } = item {
                let mut arity = 0usize;
                for (_, pt) in params {
                    arity += self.flat_arity(pt)?;
                }
                out.push((kebab(name), arity));
            }
        }
        Ok(out)
    }
}

/// Render ordered pairs back to the canonical surface string
/// (`fn/arity`, comma-joined).
#[must_use]
pub fn render_surface(entries: &[(String, usize)]) -> String {
    entries
        .iter()
        .map(|(f, n)| format!("{f}/{n}"))
        .collect::<Vec<_>>()
        .join(",")
}

/// The refusal: the snapshot-generated surface diverged from the
/// host's committed expectation, with both renderings + the first
/// difference named.
#[derive(Debug, Clone)]
pub struct ContractSkew {
    /// the host's committed expectation (canonical string)
    pub expected: String,
    /// the snapshot-generated surface (canonical string)
    pub actual: String,
    /// the first difference, named
    pub detail: String,
}

impl fmt::Display for ContractSkew {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "hostgen contract skew: refusing — the universe.snapshot's generated surface \
             diverges from the host's committed expectation\n  \
             expected sha256:{} ({})\n  \
             snapshot sha256:{} ({})\n  \
             first difference: {}",
            schema::schema_hash(&self.expected),
            self.expected,
            schema::schema_hash(&self.actual),
            self.actual,
            self.detail,
        )
    }
}

impl std::error::Error for ContractSkew {}

/// The happy-path report: which schema fns the contract covers, and
/// which are out of contract (extra guest exports — the host never
/// calls them; `schema.rs` guards the reverse direction).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractCoverage {
    /// schema fns present in the contract with matching arity
    pub covered: Vec<(String, usize)>,
    /// schema fns absent from the contract (legitimate: out of
    /// contract, e.g. `watch-orders`)
    pub out_of_contract: Vec<(String, usize)>,
}

/// Check the snapshot-generated surface against the host's committed
/// expectation: every generated entry that appears in the contract
/// must match arity; a mismatch or a VACUOUS validation (zero
/// coverage — a snapshot/expectation pair that agrees by accident)
/// is a skew.
///
/// # Errors
/// [`ContractSkew`] with both renderings + the first difference.
pub fn check_contract(
    entries: &[(String, usize)],
    expected: &str,
) -> Result<ContractCoverage, ContractSkew> {
    let contract = schema::parse_surface(expected);
    let skew = |detail: String| ContractSkew {
        expected: expected.to_string(),
        actual: render_surface(entries),
        detail,
    };
    let mut covered = Vec::new();
    let mut out_of_contract = Vec::new();
    for (f, n) in entries {
        match contract.iter().find(|(g, _)| g == f) {
            None => out_of_contract.push((f.clone(), *n)),
            Some((_, m)) if m != n => {
                return Err(skew(format!(
                    "`{f}` — snapshot arity {n}, contract arity {m}"
                )));
            }
            Some(_) => covered.push((f.clone(), *n)),
        }
    }
    if covered.is_empty() {
        return Err(skew(
            "the snapshot's schema surface covers none of the contract fns — \
             vacuous validation refused"
                .to_string(),
        ));
    }
    Ok(ContractCoverage {
        covered,
        out_of_contract,
    })
}

/// The hostgen failure domain: parse (corruption), surface resolution
/// (unresolved ref), or contract skew (drift).
#[derive(Debug, Clone)]
pub enum HostgenError {
    /// the snapshot didn't parse
    Parse(ParseError),
    /// the snapshot parsed but referenced an unknown item
    Surface(String),
    /// the generated surface diverged from the expectation
    Skew(ContractSkew),
}

impl fmt::Display for HostgenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(e) => write!(f, "{e}"),
            Self::Surface(e) => write!(f, "{e}"),
            Self::Skew(s) => write!(f, "{s}"),
        }
    }
}

impl std::error::Error for HostgenError {}

impl From<ParseError> for HostgenError {
    fn from(e: ParseError) -> Self {
        Self::Parse(e)
    }
}

impl From<String> for HostgenError {
    fn from(e: String) -> Self {
        Self::Surface(e)
    }
}

impl From<ContractSkew> for HostgenError {
    fn from(e: ContractSkew) -> Self {
        Self::Skew(e)
    }
}

/// THE STARTUP GATE: parse the committed universe snapshot, generate
/// the schema surface from it, and validate against the host's
/// committed expectation. A drifted or corrupt snapshot fails FAST,
/// with the corruption class or the first surface difference named —
/// the byte-tie moved into the host.
///
/// # Errors
/// [`HostgenError`] — parse corruption, unresolved surface refs, or
/// contract skew (arity mismatch / vacuous coverage).
pub fn validate_committed(
    snapshot_text: &str,
    expected_surface: &str,
) -> Result<ContractCoverage, HostgenError> {
    let items = parse_snapshot(snapshot_text)?;
    let universe = Universe::new(items);
    let entries = universe.surface_entries()?;
    Ok(check_contract(&entries, expected_surface)?)
}

#[cfg(test)]
#[allow(clippy::panic, reason = "tests: fail loud, fail clear")]
mod tests {
    use super::*;

    /// A minimal universe covering every Ty shape the format carries.
    const ALL_TYS: &[(&str, &str)] = &[
        ("bool", "bool"),
        ("u8", "u8"),
        ("u16", "u16"),
        ("u32", "u32"),
        ("u64", "u64"),
        ("i8", "i8"),
        ("i16", "i16"),
        ("i32", "i32"),
        ("i64", "i64"),
        ("f32", "f32"),
        ("f64", "f64"),
        ("string", "string"),
        ("bytes", "bytes"),
        ("option(u64)", "option"),
        ("result(u64,string)", "result"),
        ("list(string)", "list"),
        ("map(string,u64)", "map"),
        ("set(string)", "set"),
        ("future(u64)", "future"),
        ("stream(u64)", "stream"),
        ("tensor(2;3;u64)", "tensor"),
        ("tensor(u64)", "tensor-zero-dims"),
        ("ty(Foo)", "named"),
    ];

    #[test]
    fn every_ty_shape_parses() {
        for (text, label) in ALL_TYS {
            let parsed = parse_ty_text(text);
            assert!(parsed.is_ok(), "{label}: {parsed:?}");
        }
        // spot-check the recursive shapes structurally
        assert_eq!(
            parse_ty_text("list(ty(User))").ok(),
            Some(Ty::List(Box::new(Ty::Named("User".to_string()))))
        );
        assert_eq!(
            parse_ty_text("result(u64,string)").ok(),
            Some(Ty::Result(Box::new(Ty::U64), Box::new(Ty::String)))
        );
        assert_eq!(
            parse_ty_text("tensor(u64)").ok(),
            Some(Ty::Tensor(vec![], Box::new(Ty::U64)))
        );
    }

    #[test]
    fn key_gate_rejects_non_scalar_keys() {
        assert!(parse_ty_text("set(f64)").is_err());
        assert!(parse_ty_text("map(f64,u64)").is_err());
        assert!(parse_ty_text("map(string,u64)").is_ok());
    }

    #[test]
    fn malformed_types_are_loud() {
        assert!(parse_ty_text("option(u64").is_err());
        assert!(parse_ty_text("option").is_err());
        assert!(parse_ty_text("u64x").is_err(), "unknown token");
        assert!(parse_ty_text("u64,u64").is_err(), "trailing garbage");
        assert!(parse_ty_text("ty()").is_err(), "empty ty ref");
    }

    #[test]
    fn deep_nesting_fails_loud_not_fatal() {
        let mut s = String::from("u64");
        for _ in 0..200 {
            s = format!("option({s})");
        }
        assert!(parse_ty_text(&s).is_err());
    }

    #[test]
    fn parse_is_lossless_verbatim_names() {
        // the kebab-at-parse drift's pin: names survive VERBATIM (the
        // kebab WIT spelling is `surface_entries`' projection, never
        // the parser's)
        let items = parse_snapshot(
            "record OrderItem\nfield unitPrice ty(User)\n\
             func getUser\nparam orderId u64\nret option(ty(OrderItem))\n",
        )
        .unwrap_or_else(|e| panic!("verbatim round trip: {e}"));
        assert_eq!(
            items,
            vec![
                Item::Record {
                    name: "OrderItem".to_string(),
                    fields: vec![("unitPrice".to_string(), Ty::Named("User".to_string()))],
                },
                Item::Func {
                    name: "getUser".to_string(),
                    params: vec![("orderId".to_string(), Ty::U64)],
                    ret: Ty::Option(Box::new(Ty::Named("OrderItem".to_string()))),
                    sem: None,
                },
            ],
        );
    }

    #[test]
    fn crlf_is_corruption_not_whitespace() {
        // the CRLF drift's pin: `lines()` used to silently strip `\r`;
        // the writer never emits it, so CRLF is corruption — both this
        // parser and the Lean authority reject it, loudly (the `\r`
        // lands on its line's LAST token: an unrecognized line on the
        // header, trailing garbage on a type token — either class is
        // the loud rejection the pin asserts)
        let err = parse_snapshot("record User\r\nfield id u64\r\n")
            .err()
            .unwrap_or_else(|| panic!("CRLF must fail"));
        let msg = err.to_string();
        assert!(
            msg.contains("unrecognized line") || msg.contains("trailing garbage"),
            "{msg}"
        );
        assert!(msg.contains("snapshot: line"), "line number named: {msg}");
    }
}
