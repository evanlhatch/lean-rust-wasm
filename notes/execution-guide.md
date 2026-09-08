# Execution Guide: Closing the Loop

The pipeline from `@[schema]` to a running WASM component with typed host
bindings, generated faults, and certified delta impls. Each stage is
independently demoable. Stages are dependency-ordered — do them in order.

## Source of truth

The SSOT is `lean/schema-lang/Demo.lean` — plain Lean structures with
`@[schema]`. Everything downstream is generated from the reflection.
Right now there are TWO sources (`Demo.lean` structures + `Spec/Demo.lean`
hand-lists) — Stage A collapses them.

## Build/test commands (always use these)

```bash
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0/bin

# Lean: build all packages
devenv shell --profile wasm -- bash -c 'just lean-build'

# Lean: run schema-lang tests (includes golden byte-tie)
cd lean/schema-lang
LEAN_PATH="$PWD/.lake/build/lib/lean:$PWD/.lake/packages/plausible/.lake/build/lib/lean:$PWD/.lake/packages/LSpec/.lake/build/lib/lean:$PWD/../codegen-core/.lake/build/lib/lean:$PWD/../substrait/.lake/build/lib/lean:$PWD/../TestKit/.lake/build/lib/lean:$PWD/../Machines/.lake/build/lib/lean" PATH="$TC:$PATH" ./.lake/build/bin/SchemaLangTests

# Codegen: regenerate artifacts
LEAN_PATH="$PWD/.lake/build/lib/lean" PATH="$TC:$PATH" $TC/lake exe schema-gen

# Rust: check the host crate
cd /home/evan/lean-rust-wasm
devenv shell --profile wasm -- bash -c 'cargo check -p lean-rust-wasm'

# Rust: build + test steel-host
devenv shell --profile wasm -- bash -c 'cargo test -p steel-host'

# Full gates
devenv shell --profile wasm -- bash -c 'just gates'
```

## Stage A: Unify the spec surface (blocks everything)

**Goal**: ONE source of truth. `Demo.lean` (native structures) is the SSOT;
the hand-written `Spec/Demo.lean` data becomes generated.

**Current state**:
- `lean/schema-lang/Demo.lean` — 3 structures (`User`, `OrderItem`, `Order`) with `@[schema]`
- `lean/schema-lang/SchemaLang/Spec/Demo.lean` — hand-written `List Item` data (items + funcs + resources + failure modes)
- `lean/schema-lang/SchemaLang/Meta/Reflect.lean` — reflects STRUCTURES only (not inductives)

**Do**:
1. Extend `Meta/Reflect.lean` to reflect **inductives** (variants):
   - `Lean.isInductive env declName` (not `isStructure`)
   - Get constructors via `getStructureCtor` or the inductive's `ctors`
   - Each constructor's args → the variant's payload types
   - Register as `Item.variant`
2. Extend to reflect **funcs**: a `@[schema_fn]` attribute on `def`s — read the type via `whnf`, extract params/ret, register as `Item.func`
3. Delete `Spec/Demo.lean` — the hand-written data is replaced by the reflection
4. Move the test fixtures (the `broken`/`dup`/`fwd` universes used in resolution tests) into the test file itself (they're test data, not spec)
5. The `FailureModeItem` registry (in `faults/Spec/Demo.lean`) stays — it's a separate concern (error codes, not types)

**Done when**: `lake build` green, `SchemaLangTests` green, `schema-gen` emits the same artifacts as before (byte-tie against the existing goldens).

## Stage B: Typed host bindings from WIT

**Goal**: The Rust host calls guest functions through the component model with TYPED arguments (not untyped `Val` marshalling).

**Current state**: `steel-host` calls via `instance.get_typed_func` on the raw component — works but untyped. `wit-bindgen` is installed in the wasm profile but not used.

**Do**:
1. Add `wit-bindgen = "0.42"` (or whatever version is in the nix profile) to `steel-host`'s dev-dependencies (or use the `wasmtime::component::bindgen!` macro)
2. Generate host-side bindings from `wit/gateway.wit`:
   ```rust
   // In steel-host/src/bindings.rs
   wasmtime::component::bindgen!({
       path: "../wit/gateway.wit",
       world: "gateway",
       async: true,
   });
   ```
3. This generates a `Gateway` trait + `GatewayPre`/`Gateway` structs — the typed host API
4. In the test: instantiate the guest through the typed bindings, call `get-user(id)` — the args and return are TYPED (not `Val`)
5. The generated code references the schema types (User etc.) — connect them to `schema_generated.rs`

**Done when**: the steel-host test calls `add(1,2)` through TYPED bindings (not raw `Val`), and `get-user` returns a structured `User` (not a blob).

## Stage C: Generated host faults

**Goal**: The host's error codes (E110-E113) come from the SAME Lean registry as the guest's (E100-E103). One code allocator across the stack.

**Current state**: `steel-host/src/valves.rs` (or wherever) hardcodes the host fault codes. The faults emitter generates `OrderError` for the GUEST but not the HOST faults.

**Do**:
1. The faults registry (`lean/faults/Faults/Spec/Demo.lean`) has the guest faults (E100-E103). ADD host-side faults (E110+: engine error, missing export, fuel exhausted, timeout).
2. The faults emitter generates TWO modules: the guest's `OrderError` (already done) and the HOST's `HostFault`. Same registry, same allocation.
3. Replace the hardcoded E110-E113 in steel-host with the generated types.
4. The host's `HostFault` uses `fast_observe::error!` with the same `#[code]`/`#[category]`/`#[advice]` attributes.

**Done when**: `lookup_error("E110")` resolves from BOTH the host and guest sides. The E-code means the same thing across the boundary.

## Stage D: Guest exports from schema funcs

**Goal**: The guest's exported functions come from the schema's `func` items, not hand-written `#[no_mangle]`.

**Current state**: `guest-demo/src/lib.rs` has hand-written `#[no_mangle]` exports. The schema's `func` items (if any) aren't reflected.

**Do**:
1. Extend `Meta/Reflect.lean` to reflect **functions**: `@[schema_fn]` attribute on `def`s — read the type, extract params/ret
2. The emitter generates a guest-side stub module: `pub mod guest_exports { pub fn get_user(id: u64) -> Option<User> { ... } }`
3. The WIT world includes the func exports (it already does via `gateway-exports`)
4. The guest-demo imports the generated stub and implements the handlers

**Done when**: the guest's exports match the schema's func items, and the host calls them through the component model.

## Stage E: Certified delta impls

**Goal**: The `ChangeSpec` laws (patch/invert/diff_correct) as EXECUTABLE Rust tests.

**Current state**: `src/delta_generated.rs` generates the `UserChange` enum + a `dbsp::Change` impl — but the impl body is a leaf string with no proof.

**Do**:
1. The delta emitter generates `#[cfg(test)]` tests:
   ```rust
   #[test]
   fn change_roundtrip() {
       let user = User { id: 1, name: "a".into(), email: "b".into(), tags: vec![] };
       let delta = UserChange::Update(user.clone());
       assert_eq!(delta.patch(&user), user);  // diff_correct
   }
   ```
2. The tests are GENERATED from the schema — every record gets a round-trip test
3. These are the executable siblings of the Lean `ChangeSpec` theorems

**Done when**: `cargo test` in the host crate proves the change laws on concrete values.

## Stage F: Rust round-trip gate

**Goal**: The Rust side can parse the WIT back — the echo of `Decode.lean`'s inversion.

**Do**:
1. In forge (or a test), use `wit-parser` (the Rust crate) to parse `wit/gateway.wit`
2. Verify: the parsed interface matches the schema items (field names, types)
3. This is the Rust-side echo of the Lean `Decode` module's `parse ∘ emit = id`

**Done when**: a forge test parses the WIT and asserts the schema matches.

## Stage G: The end-to-end demo

**Goal**: One command that closes the loop.

**Do**:
1. Add a `just demo` recipe:
   ```just
   demo: gen wasm-guest
       # host loads the component, calls add(1,2) through typed bindings
       cargo test -p steel-host
   ```
2. This is the "edit Lean → get a working component" loop, closed.

## Rules (binding)

- Zero `sorry`/`axiom` in Lean code. `just lean-axioms` enforces.
- All artifacts byte-tied. `just gen-check` enforces.
- One writer per artifact path.
- The SSOT is `Demo.lean` (native Lean structures). Everything else is generated.
- Build after every declaration. Compile errors compound.
- Never trust your own report — run the gate.
