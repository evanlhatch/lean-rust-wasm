# WasmBackend — design notes

Moved out of `lean/wasm-backend/WasmBackend.lean` by the debloat pass.
The module keeps contracts, ABI facts, and validator-trap notes; this
file holds the how-we-got-here essays.

## The async-lift recipe (§async-lift)

Cracked via the minimal-module bisection against wasmparser 0.257's
`check_asyncness`. Requirements:

(a) the WIT function must be declared `async func` (the component func
type's async flag — a SYNC-marked fn = the `async canonical option
requires an async function type` error);
(b) the core module IMPORTS the task intrinsics: the per-fn
`[export]$root`/`[export]<iface-key>` `[task-return]<fn>` (the flat
results — the list = (ptr, len)) + `$root`'s [waitable-set-poll/new/
drop], [waitable-join], [context-get-0/set-0] + `[export]$root`
[task-cancel] (NO params);
(c) the core exports: memory, `__indirect_function_table`,
cabi_realloc, `[async-lift]<key>#<fn>` (the params = the flat form;
the result = i32 = the task handle-ish 0) +
`[callback][async-lift]<key>#<fn>` ((i32,i32,i32)->i32);
(d) the callee DELIVERS results by CALLING task-return(flat-results)
then returning 0 (the sync-computable body = done at the first poll;
the callback = the constant Exit=0).

The fused-adapter `type mismatch` seen earlier = the missing
task-return import+call. Emission is LIVE: the callback +
interface-qualified exports are emitted (verified against the
wit-bindgen 0.61 reference).
