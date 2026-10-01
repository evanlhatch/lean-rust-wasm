# LLVM-Backend Spike — honest results

Date: 2026-10-05/06. Spike artifacts: `/tmp/llvm-spike/` (nothing in-tree except
this note). Prior session landed Q1 (toolchain) and most of Q2 (bitcode face);
this session ran the remaining questions to ground.

## Q1 — Can the toolchain build with -DLLVM=ON here? **LANDED**

- **No prebuilt LLVM-enabled Lean exists**: the devenv's nix Lean 4.30.0
  (`/nix/store/l5cvm64lwqnripwik8vqvp8xkmdfb2ik-lean4-4.30.0`) has `lean --bc`
  in `--help` but `lean --features` → `[]`. Upstream v4.30.0 release assets
  (checked via GitHub API) contain no LLVM-enabled artifact. So: source build
  is the only route.
- **Hard pin**: `lean-src/src/CMakeLists.txt` requires `llvm-config` major
  version **exactly 19** (fatal error otherwise). The devenv only ships
  LLVM 21.1.8; LLVM 19.1.7 was realized from the nix cache
  (`nix-store -r .../llvm-19.1.7.drv` → substitutes, ~1 min, no source build).
- **Build cost**: full stage0+stage1 source build is ~2× C++ passes; halved by
  `-DSTAGE1_PREV_STAGE=<nix lean 4.30.0>` (boot stage1 from the prebuilt nix
  Lean). Stage1 then built clean in ~11 min on 16 cores (4625 build steps),
  compiling `library/llvm.cpp` against LLVM 19 without error.
- **Result**: `/tmp/llvm-spike/build/stage1/bin/lean --features` → `[LLVM]`.

## Q2 — The bitcode face (`lean --bc`) **LANDED**

- `lean --bc=test2.bc test2.lean` emits a real 82 KB bitcode module;
  `llvm-dis` (LLVM 19) disassembles it cleanly. Plain `def`s get full scalar
  bodies (`define dllexport i64 @l_pipeline(i64)`, `@l_add64(i64,i64)`) plus
  boxed entry wrappers (`l_pipeline___boxed`) and the whole `lean.h.bc`
  runtime interface inlined into the module.
- **Test-module design gotcha (cost one session to find)**: `@[extern "x"]`
  marks a def as *implemented elsewhere* — the backend emits only `declare`,
  never a body. A spike module built from `@[extern]` defs links but resolves
  nothing. Plain defs are what the LLVM backend compiles; `@[extern]` is only
  the FFI seam (used here for `opaque rustMul10 : UInt64 → UInt64`).
- One blocker found and fixed earlier: with `-DSTAGE1_PREV_STAGE=<nix lean>`,
  `lean.h.bc` is *copied from the prev stage* and the nix Lean's bitcode was
  produced by clang 21 → LLVM-19 parse error
  (`Unknown attribute kind (102) (Producer: 'LLVM21.1.8' Reader: 'LLVM 19.1.7')`).
  Fix: regenerate via `make runtime_bc LEAN_CC=<clang-19>`. **The
  Lean↔clang version must match exactly on both faces** — key operational rule.

## Q3 — Cross-language LTO (the point) **LANDED — inlining materializes, end-to-end run passes, with one operational caveat**

Producers and the version-match rule:
- Lean producer: LLVM **19.1.7** (spike toolchain). Rust producer: nix
  `rust-nightly-1.100.0-nightly-2026-09-06` → `rustc --version --verbose` says
  **LLVM 23.1.1** (also present in store: 1.99.0 nightlies on LLVM 22.1.8/23.1.0).
- Rule confirmed the hard way: LLVM 19 tools **cannot read** LLVM-23 bitcode
  (`llvm-dis-19 rust.bc` → `Unknown attribute kind (102) (Producer:
  'LLVM23.1.1-rust' Reader: 'LLVM 19.1.7')`). So **the linker's LLVM must be ≥
  every producer's**: a clang-19/lld-19 final link is impossible with any
  current nix rustc. The workable final linker is **rust-lld 23** (shipped
  inside the rustc sysroot: `lib/rustlib/aarch64-unknown-linux-gnu/bin/rust-lld`),
  which reads both the LLVM-19 Lean bitcode and the LLVM-23 Rust bitcode.

The experiment (`/tmp/llvm-spike/lto/`):
- `lib.rs`: `#![no_std]` `#[no_mangle] pub extern "C" fn rust_mul10(x: u64)
  -> u64 { x.wrapping_mul(10) }` → `rustc --emit=llvm-bc -O -C
  codegen-units=1` → `rust.bc` (body: `mul i64 %x, 10`).
- `test2.lean`: plain `def pipeline (x : UInt64) : UInt64 := add64 (rustMul10
  x) 1` → `lean --bc=lean.bc` → `l_pipeline` calls `@rust_mul10` then
  `@lean_uint64_add`.
- Link: `rust-lld -flavor gnu -shared -O2 lean.bc rust.bc libleanshared.so` →
  links clean, symbols `l_pipeline`, `rust_mul10` both present.

**Two honest negatives on the way to the positive:**
1. **Target-feature attribute mismatch blocks cross-language inlining.** lld's
   LTO ran the inliner on `l_pipeline` but declined every edge. Root cause:
   rustc stamps `"target-features"="+v8a,+outline-atomics"` on its functions;
   the Lean LLVM backend stamps none (`attributes #0 = { "probe-stack"=
   "inline-asm" }`), and LLVM's inliner requires callee features ⊆ caller
   features. Adding the matching `"target-features"` string to the Lean
   module's attribute group (one-line patch to the disassembled IR, reassemble
   with llvm-as-23) made intra-module inlining work (`lean_uint64_add`
   inlined, `+1` folded to `add x0, x0, #1`). Any adoption must either teach
   Lean's backend to emit target features or normalize attributes at link
   time — otherwise the two producers' IR silently refuses to fuse.
2. **lld's stock mixed LTO still did not import Rust→Lean.** Even with
   features aligned, `l_pipeline` kept `bl rust_mul10@plt` under `-O2`/
   `--lto-O2`/`-O3 --lto-O3`. Running the identical optimizer manually —
   `llvm-link-23 lean23.bc rust.bc` then `opt-23 -O2` — **does** inline.

**The positive — cross-language inlining materializes.** After `opt -O2` on
the linked module, the Rust body is inlined at the Lean call site and fused
with the Lean arithmetic:

```
define dllexport range(i64 1, 0) i64 @l_pipeline(i64 %0) local_unnamed_addr #0 {
entry:
  %_0.i = mul i64 %0, 10        ; ← Rust rust_mul10, inlined
  %1 = or disjoint i64 %_0.i, 1 ; ← Lean add64(+1), folded
  ret i64 %1
}
```

**End-to-end run**: that optimized module linked to `liblto.so`, a C main
calling `l_pipeline(5)` against it + `libleanshared` prints
**`pipeline(5) = 51`** — one binary, Lean and Rust code fused by LLVM LTO.

## Q4 — Lean bitcode → wasm32-unknown-unknown **LANDED (codegen); runtime port is the honest gap**

- The spike's LLVM 19 has the wasm backends registered (`llc --version` →
  `wasm32`, `wasm64`), and `llc-19 -mtriple=wasm32-unknown-unknown
  -filetype=obj test2.bc` emits a valid 34 KB wasm object (feature warnings
  only: `+fp-armv8/+neon/+outline-atomics` are host attrs, ignored). So the
  Lean-produced bitcode **codesgens** to wasm32 with zero Lean-side changes.
- `rust-lld -flavor wasm --allow-undefined --no-entry` links that object
  mechanically (the toolchain path runs end to end).
- **The gap**: a *runnable* wasm Lean module needs the Lean runtime compiled
  to wasm32 — `lean_dec_ref`/RC, the mimalloc allocator face
  (`mi_malloc_small`/`mi_free`, declared in the emitted IR), GC/IO and a libc
  face (wasi or wasm32-unknown-unknown's minimal libc). `libleanshared.so` is
  ELF-only. That is a real porting project (runtime C deps → wasm), not a
  linking flag. Unmeasured whether mimalloc's wasm story suffices; pthreads
  and the I/O layer are known-open. Until then the tree's proved
  Lean→wasm route (guest compiler, wasm runtime already shipped) stays the
  only complete wasm story.

## Q5 — Debug-info face **NEGATIVE**

- `llvm-dis test2.bc` contains **zero** `DICompileUnit`/`DISubprogram`/
  `!dbg`/`!llvm.dbg.cu` records — the Lean LLVM backend emits no DWARF
  metadata at all (same for `lean.h.ll`). Same for the Rust side's own
  `rust.bc` at `-O` (no debuginfo requested; `rustc -g` would add it, but the
  Lean side has nothing to match). So line-level mixed debugging through the
  LLVM route is currently **not available**; symbol-level (nm/objdump on
  `l_*` names) is all you get. The tree's proved route (Lean→wasm + source
  maps tooling) is strictly ahead on debuggability too.

## Q6 — The duel (LLVM route vs the tree's proved route) **DESIGN NOTE — not run**

Same source, two routes, wasmtime as judge:

```
  A (proved, in-tree):  Lean source → Lean guest compiler → wasm
                        → wasm runtime w/ Lean RC built-in → wasmtime
  B (this spike):       Lean source → lean --bc (LLVM 19) → llc/wasm-ld
                        (+ Rust LTO at the seam) → wasm
                        → needs Lean runtime ported to wasm32 → wasmtime
```

- Route A exists and is exercised by the tree's gates; its cost model (guest
  compiler in the wasm payload, Lean RC in the runtime) is known.
- Route B was shown to codegen the same source's bitcode to wasm32 (Q4), and
  its one unique card is the Q3 result: **Rust code fusing into Lean code at
  the IR level**, which A cannot do (A links Rust only across the wasm ABI).
- A fair duel would hold the runtime constant (B borrows A's wasm runtime)
  and measure: payload size, cold-start, the `pipeline`-shaped hot loop with
  and without the Rust inline. Honest status: not set up — the runtime-port
  gap in Q4 means B has no runnable wasm module to race yet, so any duel
  result today would measure the stub, not the route. Defer until/unless the
  runtime port happens.

## Adoption verdict

**Not adopted — and the spike says why honestly.** What the LLVM route would
buy this tree: (a) cross-language IR-level fusion with Rust (proven, Q3) and
(b) native codegen without the interpreter layer. What it costs, all
evidenced here:

1. **Toolchain fork forever**: Lean hard-pins LLVM major 19; our LLVM-19 Lean
   must be built from source and re-pinned on every Lean upgrade (upstream
   edits the CMake pin, never loosens it).
2. **A three-way exact-version lattice**: Lean↔19, lean.h.bc must be
   regenerated with clang-19, and the final linker must be ≥ every producer
   (rustc is already at LLVM 23; clang-19 cannot link Rust's output at all).
   Today that lattice resolves only via rust-lld-23 — a linker nobody in the
   tree currently drives.
3. **The attribute wall**: the two producers emit incompatible target-feature
   attributes and silently refuse to inline; adoption needs an attribute
   normalization step that upstream Lean does not ship.
4. **No debug info at all** from the Lean backend (Q5), vs the proved route's
   tooling story.
5. **The wasm route B is incomplete** without porting the Lean runtime
   (mimalloc/RC/libc face) to wasm32 — the same runtime the proved route
   already ships.
6. **`just gates` cost**: an llvm-19 toolchain row, a lean.h.bc regeneration
   step, and a version-lattice check, all to serve a fusion feature nothing
   in the current note set asks for.

The honest one-liner: the LLVM backend is a real, working compiler path with
one genuinely unique capability (Rust↔Lean IR fusion, now demonstrated), but
every step of its supply chain is a version-locked, self-maintained fork that
the proved Lean→wasm route does not pay. Revisit only if a workload demands
native-code fusion of Lean and Rust and tolerates the fork.

## Verification commands

```
export PATH=/tmp/llvm-spike/build/stage1/bin:/tmp/llvm-spike/llvm19/bin:$PATH
export LEAN_PATH=/tmp/llvm-spike/build/stage1/lib/lean
cd /tmp/llvm-spike/bc
lean --bc=test2.bc test2.lean && llvm-dis test2.bc -o test2.ll

cd /tmp/llvm-spike/lto
NT=/nix/store/xj662y7bgwi6jnk2sjl27plgjlqbxxfy-rust-nightly-1.100.0-nightly-2026-09-06-1.100.0-nightly-2026-09-06/lib/rustlib/aarch64-unknown-linux-gnu/bin
# attributes fix: lean23.ll has "target-features" added to group #0 (see Q3.1)
$NT/llvm-link -S lean23.bc rust.bc -o combined.ll
$NT/opt -passes='default<O2>' combined.ll -o opt.bc
$NT/rust-lld -flavor gnu -shared -o liblto.so opt.bc \
  /tmp/llvm-spike/build/stage1/lib/lean/libleanshared.so -soname liblto.so
/tmp/llvm-spike/ccbin/clang main.c -o run ./liblto.so \
  -Wl,-rpath,/tmp/llvm-spike/lto -L/tmp/llvm-spike/build/stage1/lib/lean \
  -lleanshared -Wl,-rpath,/tmp/llvm-spike/build/stage1/lib/lean
./run   # → pipeline(5) = 51

# wasm codegen face (Q4):
llc -mtriple=wasm32-unknown-unknown -filetype=obj /tmp/llvm-spike/bc/test2.bc -o lean.wasm.o
```
