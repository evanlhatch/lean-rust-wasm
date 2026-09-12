/-
# Oracle — the wasm differential gate's Lean-side row universe

Extracted from `target/oracle.lean` (which stays the manifest EMITTER —
`just wasm-compile` runs it and byte-ties nothing: the manifest is
regenerated with the WAT so it can never go stale). The extraction makes
the gate's Lean side testable: `Tests/Main.lean` now ships a
`TestKit.DiffSpec` proving the oracle REJECTS a sabotaged row (unknown
fn, arity drift) — the corruption-negative discipline the smoke
previously enforced only Rust-side (steel-host's flipped-instruction
sabotage row).

BYTE-COMPAT INVARIANT: `rows`/`resultOf`/`jsonRow` are verbatim lifts;
`resolve` is new (structured errors for the DiffSpec) and never changes
manifest bytes — verified by byte-diffing the emitter's output
pre/post extraction.

Ownership: this module owns the row universe + row resolution; the
script owns only the emission loop. Deliberately excluded: the component
replay itself (steel-host, Rust-side).
-/

import Lean
import DemoFn
import GuestlangStd
import LintKit.PackageNamespace

-- The oracle row surface (`rows`/`resolve`/`jsonRow`/…) is keyed by the
-- demo world's WIT export names — deliberately unprefixed.
set_option linter.guestlang.packageNamespace false -- because these decl names key the wasm differential oracle to the WIT export contract, not library API

/-- The demo inputs (deterministic — the manifest is reproducible). -/
def u64s : List UInt64 :=
  ((List.range 20).map (fun i => (i * 7 + 3) % 100)).map (fun n => n.toUInt64)

/-- The manifest rows: (fn, args) pairs the differential gate replays. -/
def rows : List (String × List String) :=
  (u64s.map fun a => ("double", [toString a]))
  ++ (u64s.map fun a => ("is-big", [toString a]))
  ++ (u64s.map fun a => ("adder", [toString a, toString (a + 3)]))
  ++ (u64s.map fun a => ("double-area", [toString a]))
  ++ (u64s.map fun a => ("run-paps", [toString a]))
  ++ ((List.range 20).map fun i =>
    ("total", [toString (i * 3), toString (i + 1), toString (i * 2)]))
  ++ (u64s.map fun a => ("pick", [if a % 2 == 0 then "1" else "0", toString a, toString (a + 1)]))
  ++ (u64s.map fun a => ("str-len-demo", [toString a]))
  ++ (u64s.map fun a => ("greet", [toString a]))
  ++ (u64s.map fun a => ("get-user", [toString a]))

/-- The expected-result fold (Lean's semantics is the authority). "?" is
    unreachable for well-formed rows — `resolve` guards fn/arity first. -/
def resultOf (fn : String) (args : List String) : String :=
  match fn, args with
  | "double", [a] => toString (double a.toNat!.toUInt64)
  | "is-big", [a] => if isBig a.toNat!.toUInt64 then "1" else "0"
  | "adder", [a, b] => toString (adder a.toNat!.toUInt64 b.toNat!.toUInt64)
  | "double-area", [a] => toString (doubleArea a.toNat!.toUInt64)
  | "run-paps", [a] => toString (runPaps a.toNat!.toUInt64)
  | "total", [a, b, c] => toString (total a.toNat!.toUInt64 b.toNat!.toUInt64 c.toNat!.toUInt64)
  | "pick", [b, a, x] => toString (pick (b == "1") a.toNat!.toUInt64 x.toNat!.toUInt64)
  | "str-len-demo", [a] => toString (GuestImpl.strLenDemo a.toNat!.toUInt64)
  | "greet", [a] => GuestImpl.greet a.toNat!.toUInt64
  | "get-user", [a] => match GuestImpl.getUser a.toNat!.toUInt64 with
    | none => "none"
    | some u =>
      let tagS := String.intercalate "," (u.tags.map (fun t => t))
      s!"some(\{ id={u.id}, name={u.name}, email={u.email}, tags=({tagS}) })"
  | _, _ => "?"

/-- The manifest's fn surface with arities (must agree with `resultOf`'s
    patterns — the DiffSpec's arity corruption pins this). -/
def arityOf : String → Option Nat
  | "double" | "is-big" | "double-area" | "run-paps"
  | "str-len-demo" | "greet" | "get-user" => some 1
  | "adder" => some 2
  | "total" | "pick" => some 3
  | _ => none

/-- Structured row resolution: unknown fn or arity drift is an error
    NAMING the row context (the gate's corruption negatives pin this). -/
def resolve (fn : String) (args : List String) : Except String String :=
  match arityOf fn with
  | none => .error s!"oracle row: unknown fn '{fn}'"
  | some n =>
    if args.length != n then
      .error s!"oracle row: '{fn}' expects {n} args, got {args.length}"
    else .ok (resultOf fn args)

/-- One manifest row as JSON (values via Lean.Json for escaping; the
    skeleton keeps the byte format — `mkObj` sorts keys, forbidden). -/
def jsonRow (fn : String) (args : List String) (expected : String) : String :=
  "{" ++ "\"fn\": " ++ (Lean.Json.str fn).compress ++ ", \"args\": [" ++
    String.intercalate "," (args.map fun a => (Lean.Json.str a).compress) ++
    "], \"expected\": " ++ (Lean.Json.str expected).compress ++ "}"
