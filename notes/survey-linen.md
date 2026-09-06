# Survey: typednotes/linen — 2026-09 (subagent, source-level read)

## Verdict: SKIP (no dependency). STEAL-PATTERNS: 2 one-file ideas.

Linen = Haskell-ecosystem port for Lean 4 (740 modules, Apache-2.0,
toolchain v4.33.1): freer effects over OpenUnion, full profunctor
lenses, byte-strings/JSON/YAML/INI, typed DataFrame + CSV,
SQLite/DuckDB/Postgres/Redis clients, HTTP/TLS/QUIC stack, PDF/image
codecs, Conduit-style streaming.

## Overlap with schema-lang: essentially none

- No Ty universe, no item model, no wellFormed/EqAns/compat machinery,
  no row polymorphism or type-level field lookup. Closest thing is a
  runtime PostgREST SchemaCache (a DB catalog, not a schema language).
- Not duplicative of Batteries either (it overlaps Batteries' territory
  more than ours; it's a parallel stdlib, not a modeling layer).

## Steal-patterns (implement, don't depend)

1. **Proven codec round-trips**: `encode : α → Value` /
   `decode : Value → Option α` with the round-trip theorem PROVEN
   (their JSON module). Our JSON Schema / codec emitters adopt the
   same law shape (mirrors Codegen.ExtMetadata's decode∘encode = id).
2. **outParam two-param-class idiom** (their `Ixed`/`At`): the Lean-
   native substitute for Haskell type families — directly relevant to
   the planned schema-indexed `HasCol`-style field resolution.

## Dependency calculus (why not)

740 modules of single-maintainer churn ("instances deferred to a later
batch" per doc comments), vendored C FFI (OpenSSL/libpq/SQLite) we
don't need, zero borrowed machinery for schema-lang. QUIC/HTTP3 are
Haskell-port transports — our wire story is WIT + wRPC/quinn on the
Rust side, not a Lean HTTP stack.
