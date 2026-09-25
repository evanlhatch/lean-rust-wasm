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
  let dbgLetVal : LetValue .impure → String
    | .lit (.uint64 v) => "lit u64 " ++ toString v.toNat
    | .lit (.nat v) => "lit nat " ++ toString v
    | .lit _ => "lit ?"
    | .erased => "erased"
    | .fvar f args => "fvar " ++ f.name.toString ++ " [" ++ String.intercalate ", " (args.toList.map dbgArg) ++ "]"
    | .fap fn args => "fap " ++ toString fn ++ " [" ++ String.intercalate ", " (args.toList.map dbgArg) ++ "]"
    | .ctor info _ => "ctor " ++ toString info.name ++ " cidx=" ++ toString info.cidx
    | .pap fn args => "pap " ++ toString fn ++ " [" ++ String.intercalate ", " (args.toList.map dbgArg) ++ "]"
    | .sproj n off f _ => "sproj " ++ toString n ++ " " ++ toString off ++ " " ++ f.name.toString
    | .oproj i f _ => "oproj " ++ toString i ++ " " ++ f.name.toString
    | .box ty f .. => "box " ++ toString ty ++ " " ++ f.name.toString
    | .unbox f .. => "unbox " ++ f.name.toString
    | .proj _ i f _ => "proj " ++ toString i ++ " " ++ f.name.toString
    | .uproj i f _ => "uproj " ++ toString i ++ " " ++ f.name.toString
    | .reset .. => "reset"
    | .reuse .. => "reuse"
    | .isShared .. => "isShared"
    | .const fn _us args .. => "const " ++ toString fn ++ " [" ++ String.intercalate ", " (args.toList.map dbgArg) ++ "]"
  let rec dbgCode : Code .impure → Nat → String
    | .let d k, ind =>
        pad ind ++ "let " ++ d.fvarId.name.toString ++ " of " ++ toString d.type
          ++ " = " ++ dbgLetVal d.value ++ dbgCode k ind
    | .jp fd k, ind =>
        pad ind ++ "jp " ++ fd.fvarId.name.toString ++ dbgCode fd.value (ind + 2) ++ dbgCode k ind
    | .cases c, ind =>
        pad ind ++ "cases " ++ c.discr.name.toString ++ " on " ++ toString c.typeName
          ++ c.alts.toList.foldl (fun acc a => match a with
            | .ctorAlt info cd => acc ++ " [" ++ toString info.name ++ " cidx=" ++ toString info.cidx ++ "]" ++ dbgCode cd (ind + 2)
            | .default cd => acc ++ " [default]" ++ dbgCode cd (ind + 2)
            | .alt .. => acc) ""
    | .return f, ind => pad ind ++ "return " ++ f.name.toString
    | .jmp f _args, ind => pad ind ++ "jmp " ++ f.name.toString
    | .unreach _, ind => pad ind ++ "unreach"
    | .fun .., _ => "fun"
    | .oset .., _ => "oset" | .uset .., _ => "uset" | .sset .., _ => "sset"
    | .setTag .., _ => "setTag"
    | .inc f n _ _ k _, ind => pad ind ++ "inc " ++ f.name.toString ++ " n=" ++ toString n ++ dbgCode k ind
    | .dec f n _ _ objs k _, ind => pad ind ++ "dec " ++ f.name.toString ++ " n=" ++ toString n ++ " objs=" ++ toString objs.isSome ++ dbgCode k ind
    | .del f k _, ind => pad ind ++ "del " ++ f.name.toString ++ dbgCode k ind
  match ← Guest.readFamily? env `GuestTests.bigMain
      [`GuestTests.bigMain._closed_0, `GuestTests.mkTriple._boxed, `GuestTests.mkTriple] with
  | .ok ds =>
      for d in ds do
        IO.println ("=== " ++ d.name.toString)
        IO.println ("  type: " ++ toString d.type)
        IO.println ("  params: " ++ String.intercalate ", " (d.params.toList.map (fun p => p.fvarId.name.toString ++ " of " ++ toString p.type)))
        let body := match d.value with | .code c => dbgCode c 2 | .extern .. => "extern"
        IO.println body
  | .error e => IO.println s!"family error: {e}"
  return 0
