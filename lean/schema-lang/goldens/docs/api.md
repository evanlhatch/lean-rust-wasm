# demo:gateway — API reference
Generated from the schema-lang universe (`Demo.lean`); types are
WIT-rendered — the same spelling the emitted `wit/gateway.wit`
uses. DO NOT EDIT: regenerate with `just gen`.

## Records

### `user`

| Field | Type |
| --- | --- |
| `id` | `u64` |
| `name` | `string` |
| `email` | `string` |
| `tags` | `list<string>` |

### `order-item`

| Field | Type |
| --- | --- |
| `id` | `u64` |
| `qty` | `u32` |
| `price` | `f64` |

### `order`

| Field | Type |
| --- | --- |
| `id` | `u64` |
| `items` | `list<order-item>` |
| `total` | `f64` |

## Variants

### `role`

| Case | Payload |
| --- | --- |
| `admin` | — |
| `editor` | — |
| `viewer` | — |

### `order-error`

| Case | Payload |
| --- | --- |
| `empty-cart` | — |
| `invalid-item` | `u64` |
| `insufficient-funds` | `f64` |

## Functions

### `get-user`

```wit
get-user: func(id: u64) -> option<user>;
```

null: `propagate` · determinism: `pure` · delivery: `once`

### `watch-orders`

```wit
watch-orders: async func(into: order-error) -> list<user>;
```

null: `propagate` · determinism: `pure` · delivery: `once`

## Resources

### `db`

Opaque handle — its methods are `func` items whose first parameter references it.
