/-
Scratch probe (deleted before landing): the pipeline's first-class
application shape — what impure LCNF `applyTwice` produces.
-/
import Guest
import Lean

open Lean Compiler.LCNF

unsafe def main : IO UInt32 := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.searchPathRef.set (".lake/build/lib/lean" :: (← Lean.searchPathRef.get))
  let env ← Lean.importModules #[{ module := `GuestTests.Fixture }]
    (opts := Guest.lcnfOptions) (loadExts := true)
  let pad (ind : Nat) : String := String.join (List.replicate ind " ")
  let dbgArg : Arg .impure → String
    | .fvar f => "fvar(" ++ f.name.toString ++ ")"
    | .erased => "erased"
    | .type .. => "type"
  let litS : LitValue → String
    | .nat v => "nat " ++ toString v | .str _ => "str" | .uint8 v => "u8 " ++ toString v.toNat
    | .uint16 v => "u16 " ++ toString v.toNat | .uint32 v => "u32 " ++ toString v.toNat
    | .uint64 v => "u64 " ++ toString v.toNat | .usize v => "usize " ++ toString v.toNat
  let argsS (args : Array (Arg .impure)) : String :=
    "[" ++ String.intercalate ", " (args.toList.map dbgArg) ++ "]"
  let dbgLetVal : LetValue .impure → String
    | .lit l => "lit (" ++ litS l ++ ")"
    | .erased => "erased"
    | .fvar f args => "fvar " ++ f.name.toString ++ " " ++ argsS args
    | .fap fn args => "fap " ++ toString fn ++ " " ++ argsS args
    | .ctor info args => "ctor " ++ toString info.name ++ " cidx=" ++ toString info.cidx ++ " " ++ argsS args
    | .pap fn args => "pap " ++ toString fn ++ " " ++ argsS args
    | .proj _ i f _ => "proj " ++ toString i ++ " " ++ f.name.toString
    | .uproj i f _ => "uproj " ++ toString i ++ " " ++ f.name.toString
    | .sproj n off f _ => "sproj " ++ toString n ++ " " ++ toString off ++ " " ++ f.name.toString
    | .oproj i f _ => "oproj " ++ toString i ++ " " ++ f.name.toString
    | .box ty f .. => "box " ++ toString ty ++ " " ++ f.name.toString
    | .unbox f .. => "unbox " ++ f.name.toString
    | .reset .. => "reset"
    | .reuse .. => "reuse"
    | .isShared .. => "isShared"
    | .const fn _us args .. => "const " ++ toString fn ++ " " ++ argsS args
  let rec dbgCode : Code .impure → Nat → String
    | .let d k, ind =>
        pad ind ++ "let " ++ d.fvarId.name.toString ++ " of " ++ toString d.type
          ++ " = " ++ dbgLetVal d.value ++ dbgCode k ind
    | .jp fd k, ind =>
        pad ind ++ "jp " ++ fd.fvarId.name.toString ++ " ["
          ++ String.intercalate ", " (fd.params.toList.map (fun p => p.fvarId.name.toString ++ " of " ++ toString p.type)) ++ "]"
          ++ dbgCode fd.value (ind + 2) ++ dbgCode k ind
    | .cases c, ind =>
        pad ind ++ "cases " ++ c.discr.name.toString ++ " on " ++ toString c.typeName
          ++ c.alts.toList.foldl (fun acc a => match a with
            | .ctorAlt info cd => acc ++ " [" ++ toString info.name ++ " cidx=" ++ toString info.cidx ++ "]" ++ dbgCode cd (ind + 2)
            | .default cd => acc ++ " [default]" ++ dbgCode cd (ind + 2)
            | .alt .. => acc) ""
    | .return f, ind => pad ind ++ "return " ++ f.name.toString
    | .jmp f args, ind => pad ind ++ "jmp " ++ f.name.toString ++ " " ++ argsS args
    | .unreach _, ind => pad ind ++ "unreach"
    | .fun .., _ => "fun"
    | .oset .., _ => "oset"
    | .uset .., _ => "uset"
    | .sset .., _ => "sset"
    | .setTag .., _ => "setTag"
    | .inc f n chk pers k _, ind => pad ind ++ "inc " ++ f.name.toString ++ " n=" ++ toString n ++ dbgCode k ind
    | .dec f n chk pers objs k _, ind => pad ind ++ "dec " ++ f.name.toString ++ " n=" ++ toString n ++ " objs=" ++ toString objs.isSome ++ dbgCode k ind
    | .del f k _, ind => pad ind ++ "del " ++ f.name.toString ++ dbgCode k ind
  let showDecl (name : Lean.Name) : IO Unit := do
    match ← Guest.readDecl? env name with
    | .error e => IO.println (name.toString ++ ": ERROR " ++ e)
    | .ok d =>
      IO.println ("=== " ++ name.toString)
      IO.println ("  type: " ++ toString d.type)
      IO.println ("  params: " ++ String.intercalate ", " (d.params.toList.map (fun p => p.fvarId.name.toString ++ " of " ++ toString p.type)))
      let body := match d.value with | .code c => dbgCode c 2 | .extern .. => "extern"
      IO.println body
  showDecl `GuestTests.applyTwice
  showDecl `GuestTests.twiceAdd5
  showDecl `GuestTests.useFn
  showDecl `GuestTests.tripleMain
  showDecl `GuestTests.mkTriple
  for trial in [`GuestTests.mkTriple._lam_1, `GuestTests.mkTriple._lam_1._boxed,
      `GuestTests.mkTriple._closed_0._lam_1, `GuestTests.mkTriple._lam_0,
      `GuestTests.mkTriple._closed_0] do
    match ← Guest.readDecl? env trial with
    | .error _ => IO.println ("-- absent: " ++ trial.toString)
    | .ok d =>
        IO.println ("--- FOUND " ++ d.name.toString)
        IO.println ("  type: " ++ toString d.type)
        IO.println ("  params: " ++ String.intercalate ", " (d.params.toList.map (fun p => p.fvarId.name.toString ++ " of " ++ toString p.type)))
        let body := match d.value with | .code c => dbgCode c 2 | .extern .. => "extern"
        IO.println body
  showDecl `GuestTests.useFnBig
  showDecl `GuestTests.bigMain
  return 0
