import Lean
import Lean.Compiler.LCNF
import CodegenCore
import SchemaLang
import SchemaLang.Meta.Reflect
import WasmBackend
import GuestlangStd.StrOps

open Lean

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let mods : Array Lean.Name := #[`DemoFn, `GuestlangStd, `SchemaLang.WitnessCheck]
  let env ← Lean.importModules (mods.map ({ module := · }))
    (opts := (default : Lean.Options).setBool `compiler.reuse false) (loadExts := true)
  let ctx : Core.Context := { fileName := "<probe>", fileMap := default
                              options := (default : Lean.Options).setBool `compiler.reuse false }
  let state : Core.State := { env := env }
  let act : CoreM Unit := do
    let targets := #[
      `SchemaLang.Witness.decWitness?, `SchemaLang.Witness.decWitnessPayload?,
      `SchemaLang.Witness.decWProp?, `SchemaLang.Witness.decWBoolExpr?,
      `SchemaLang.Witness.decWBoolExprF?, `SchemaLang.Witness.decWProof?,
      `SchemaLang.Witness.decWProofF?, `SchemaLang.Witness.decWU64?,
      `SchemaLang.Witness.decWStep?,
      `SchemaLang.Witness.WU64Tag.ofNat?, `SchemaLang.Witness.WBoolExprTag.ofNat?,
      `SchemaLang.Witness.WPropTag.ofNat?, `SchemaLang.Witness.WProofTag.ofNat?,
      `SchemaLang.Codec.decVarNat, `SchemaLang.Codec.decNat?, `SchemaLang.Codec.decEnum?,
      `SchemaLang.Codec.decBytes?, `SchemaLang.Codec.decList?, `SchemaLang.Codec.decManyBind?,
      `SchemaLang.Codec.decChar?, `SchemaLang.Codec.decString?, `SchemaLang.Codec.decU64?,
      `SchemaLang.Codec.decEnvelope?]
    Lean.Compiler.LCNF.main targets {}
    let all ← Lean.Compiler.LCNF.getLocalImpureDecls
    for n in all do
      let ns := toString n
      if ns.contains "decW" || ns.contains "decWitness" || ns.contains "decVarNat"
          || ns.contains "decNat" || ns.contains "decEnum" || ns.contains "decBytes"
          || ns.contains "decList" || ns.contains "decMany" || ns.contains "decChar"
          || ns.contains "decString" || ns.contains "decU64" || ns.contains "decEnvelope"
          || ns.contains "ofNat" || ns.contains "spec_" then
        if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
          let fmt ← Lean.Compiler.LCNF.ppDecl' d .impure
          IO.println s!"--- {n}\n{fmt}"
  let (_, _) ← act.toIO ctx state
  pure ()
