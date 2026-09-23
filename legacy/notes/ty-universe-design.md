# SchemaLang.Ty — design notes

Moved out of `lean/schema-lang/SchemaLang/Ty.lean` by the debloat pass
(2026-09). The module keeps contracts, laws, and trap notes; this file
holds the design essays.

## The four-addresses axis (TOOLKIT Part 1)

- (a) data: `Ty` is a first-order inductive — emitters fold it, the
  oracle reads it, it serializes.
- (b) type-level: `Value : Ty → Type` — a value payload INDEXED by the
  type (a `.bool` value cannot carry a string). This is the bridge that
  gives schema-typed validators and test-vector generation for free;
  Lean forbids Σ/nested-inductive under GADT params, so nothing needs
  the wrapper (flatland's AnyExpr lesson — no heterogeneous lists yet).
- (c) proposition: `Ty.wellFormed` over a universe of known names.
- (d) instance: `EqAns` — DIRECTED, proof-carrying equality (`.yes h` /
  `.no`, no `Decidable` instance needed for open terms; the flatland
  Typed/Schema pattern).

## Tensor layout layer (not built — no consumer yet)

When a tensor first crosses the WASM memory boundary (a tensor field in
a record = addressed offsets, not the self-describing wire lists the
codec uses), the blueprint is flatland's `Flatland/Flatland/Tensor.lean`:

- `CoordsOf` — typed coordinates `Fin d₀ × Fin d₁ × …`
- `flatIdxT` — the total row-major offset, the bound carried by types
  (the same telescope as `Layout.go_pairwise`)
- `dot_inj` — the write-safety theorem (scatter through a view cannot
  alias)

The ingress-validates-once bridge (`Coords.ofList?` + `flatIdxT_ofList`)
is the pattern the codec's shape gate already mirrors at the value
level.

For the WIRE FORMAT of tensor DATA (bytes, not values): NumPy's `.npy`
(header + raw row-major bytes) is the proven shape — see also
leanprover/TensorLib (the NumPy engine model: unitStrides/startIndex
zero-copy views, `Dtype.itemsize`, the LOrd NaN-excluded Float32
order) — an engineering reference, not a dependency (its shapes are
runtime data; ours are indices).
