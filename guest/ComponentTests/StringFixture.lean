/-
# ComponentTests.StringFixture — the canonical-ABI string lane's fixture

The component lane's SECOND fixture: the string world + the core
module that backs it through the canonical-ABI adapter face. The
SCALAR fixture (`Fixture.add64`) is the LCNF-compiled guest; the
string fixture is HAND-BUILT at the core-module level, on purpose:

- the string lift's boundary is the ABI's `(ptr, len)` pair into the
  component's linear memory (UTF-8) — the EMITTER's discipline
  (`Guest.Component`), pinned here byte-for-byte;
- the guest's INTERNAL string layout (the boxed-Nat lane's zone) does
  not enter this fixture: the core func receives `(i32, i32)` and
  answers the byte length — the boundary's honest minimal;
- the adapter face: the module exports the linear `memory` (one page)
  and `canonical_abi_realloc`. The realloc body is the SINGLE-CALL
  stub (the fixed base 1024) — the honest minimal for a fixture whose
  one string-lowering per call fits the page; the runtime
  bump-allocator lane is the guest runtime's (the boxed-Nat lane's
  zone). The ENGINE's side of the string round trip rides the host
  tests' WAT components (a real bump allocator there).

The five questions (notes/v3/01-core.md): the fixture is data (the
test lane's Universe face) — the answers live at the consumers
(`Guest.Component.check`/`encodeComponent`, ComponentTests.Main).
-/

import Wit
import Wit.World
import WasmCore.Instr
import WasmCore.Module
import WasmCore.Types

open WasmCore

namespace ComponentTests.StringFixture

/-- THE string world: `length : func(s: string) -> u64` — the
    canonical-ABI `(ptr, len)` param + the scalar result. -/
def lengthWorld : Wit.World :=
  { name := "guest"
  , imports := []
  , exports :=
      [.func { name := "length"
             , params := [{ name := "s", ty := .atom .string }]
             , result := some (.atom .u64) }] }

/-- THE string fixture's core module: the adapter face (the exported
    one-page memory + the ABI realloc) + the `length` core func —
    `(i32, i32) -> (i64)`, the `(ptr, len)` pair answered by the byte
    length (`i64.extend_i32_u` of the len). -/
def stringModule : WasmCore.Module :=
  { types := [⟨[.i32, .i32, .i32, .i32], [.i32]⟩    -- the ABI realloc
            , ⟨[.i32, .i32], [.i64]⟩]               -- length
  , funcs := [ { tyIdx := 0, locals := [], body := [.i32const 1024] }
             , { tyIdx := 1, locals := [], body := [.localget 1, .op .i64extendi32u] } ]
  , exports := [ { name := "canonical_abi_realloc", desc := .func 0 }
               , { name := "length", desc := .func 1 }
               , { name := "memory", desc := .memory 0 } ]
  , memMin := 1 }

/-- THE string fixture without the memory export (the adapter
    refusal's shape — the world needs the linear memory). -/
def stringModuleNoMemory : WasmCore.Module :=
  { stringModule with
      exports := stringModule.exports.filter
        (fun e => e.name != "memory") }

/-- THE string fixture without the realloc export (the adapter
    refusal's shape — the world needs the realloc for the string
    lowering). -/
def stringModuleNoRealloc : WasmCore.Module :=
  { stringModule with
      exports := stringModule.exports.filter
        (fun e => e.name != "canonical_abi_realloc") }

/-- THE string fixture with the WRONG realloc signature (the adapter
    refusal's shape — the ABI realloc is
    `(i32, i32, i32, i32) -> (i32)`). -/
def stringModuleBadRealloc : WasmCore.Module :=
  { stringModule with
      types := [⟨[.i32, .i32], [.i32]⟩, ⟨[.i32, .i32], [.i64]⟩] }

/-- THE string fixture with the WRONG length signature (the sig
    drift's shape — the module answers the ptr, not the (ptr, len)
    pair). -/
def stringModuleWrongSig : WasmCore.Module :=
  { stringModule with
      types := [⟨[.i32, .i32, .i32, .i32], [.i32]⟩, ⟨[.i32], [.i64]⟩] }

end ComponentTests.StringFixture
