/-
# GuestlangStd — the compiled stdlib + the guest implementations

The std OPS (`strlen`/`strcat`) have REAL Lean bodies — they are the
differential ORACLE (the wasm side must compute the same answers). The
BACKEND never compiles these bodies: it special-cases the NAMES as
intrinsics (`$string_len` / `$string_cat` — the runtime.wat primitives
over the guest string layout `{rc@0, tag=250@4, len u32@8, bytes@16}`),
the standard compiler practice for intrinsic ops. Guest strings are
BYTE-strings: `$string_len` counts bytes, which equals Lean's
`String.length` (chars) on ASCII — the oracle rows are ASCII-only
(non-ASCII byte/char divergence is documented, v1).

`@[guest_std]` (not `@[guest]`): the std surface — String is legal
here; the strict app surface stays string-free until the type pipeline
flattens string results through the canonical ABI (greet: done).
-/

import CodegenCore.GuestGate
import Demo
import GuestlangStd.StrOps
import LintKit.Basic

-- the ops (strlen/strcat) are declared in GuestlangStd.StrOps — the
-- root imports them; the impls below are the schema functions' bodies.

namespace GuestImpl

open GuestlangStd

/-- The `get-user` implementation: none for the sentinel id, a real
    record otherwise (strings via the std intrinsics; a two-element
    tag list — List cons cells the adapter must walk + flatten). -/
@[guest_std, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def getUserImpl (id : UInt64) : Option User :=
  if id == 0 then none
  else some
    { id := id
    , name := strcat "user-" "name"
    , email := "u@guestlang.dev"
    , tags := ["alpha", "beta"] }

/-- The FIRST string through the component boundary: a `string`-returning
    export. The canonical ABI flattens a string result to (ptr, len) —
    the embedder's MAX_FLAT_RESULTS=1 convention: the adapter writes
    (bytes-ptr, byte-len) into a static return area and returns its
    pointer. Lean body = the differential oracle. -/
@[guest_std, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def greet (n : UInt64) : String :=
  if n > 0 then strcat "hello " "guest" else "bye"

/-- The string demo: a RUNTIME-dependent string (no constant folding —
    the branch depends on the argument), appended, then measured. The
    differential gate compares Lean's real eval against the wasm
    intrinsics: n > 0 → strlen("hello world") = 11; else 1. -/
@[guest_std, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def strLenDemo (n : UInt64) : UInt64 :=
  strlen (if n > 0 then strcat "hello" " world" else "!")

/-- The `watch-orders` implementation (the ASYNC schema fn): the list
    of users = the delta batch. The body = SYNC-computable (the list
    computes immediately) — the async-ness lives in the SIGNATURE (the
    canon lift's async option + the task machinery); wit-bindgen's own
    guests are the same shape. The DIFFERENTIAL ORACLE. -/
@[guest_std, nolint linter.guestlang.packageNamespace "guest-impl surface: the backend maps these BY NAME as the demo world's function impls — the namespace is the contract"]
def watchOrdersImpl (_into : OrderError) : List User :=
  [ { id := 1, name := "first", email := "1@g.dev", tags := ["a"] }
  , { id := 2, name := "second", email := "2@g.dev", tags := ["b"] } ]

end GuestImpl
