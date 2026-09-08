# Vendored protobuf schemas

This directory is the vendored (not submoduled) protobuf schema subset that the
`LeanSubstrait.ProtoGen` wire codec is generated from.

## Upstream

### `substrait/`

- Source: `substrait-io/substrait` (https://github.com/substrait-io/substrait)
- Vendored commit: `6706015ffdb19345fef399ef8238e3e6269cb380`
  (`feat(protos)!: support expression in window aggregate bounds (#1105)`,
  Tue Aug 18 13:16:15 2026 -0700)
- Files copied from `proto/substrait/` of that commit:
  - `algebra.proto`
  - `extended_expression.proto`
  - `extensions/extensions.proto`
  - `plan.proto`
  - `type.proto`

### `google/protobuf/`

Well-known types imported by the Substrait schemas above.  These are frozen
upstream Google protobuf definitions, copied from the include tree of the
protoc shipped by the devenv (protobuf 35.1):

- `any.proto`   — imported by `substrait/algebra.proto` and
  `substrait/extensions/extensions.proto`.
- `empty.proto` — imported by `substrait/type.proto`.

Vendoring them makes codegen self-contained: `protoc` needs no system `include`
path beyond this directory.

## Regeneration

Generated Lean lives in `../LeanSubstrait/ProtoGen/` (GENERATED — DO NOT EDIT).
To regenerate:

```bash
# Build the protoc-gen-lean4 plugin (needs the LeanSubstrait dev shell).
lake build Plugin   # in the Lean-zh/protobuf checkout

protoc \
  --plugin=protoc-gen-lean4=<path-to-plugin> \
  --lean4_out=<LeanSubstrait>/LeanSubstrait/ProtoGen \
  --lean4_opt=lean4_prefix=LeanSubstrait.ProtoGen \
  --proto_path=<LeanSubstrait>/protos \
  substrait/plan.proto substrait/algebra.proto substrait/type.proto \
  substrait/extensions/extensions.proto substrait/extended_expression.proto \
  google/protobuf/any.proto google/protobuf/empty.proto
```
