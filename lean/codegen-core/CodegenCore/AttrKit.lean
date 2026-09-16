/-
# CodegenCore.AttrKit — `register_check_attribute`: the BOILERPLATE macro
-/

import Lean

open Lean
open Lean.Elab
open Lean.Elab.Command

/-- `register_check_attribute name : "descr" := handler` → the full
    `initialize registerBuiltinAttribute { … }` block. -/
elab "register_check_attribute " name:term " : " descr:str " := " handler:term : command => do
  let cmd := (← `( initialize (registerBuiltinAttribute {
    name := $name
    descr := $descr
    applicationTime := .afterCompilation
    add := $handler
  }) )).raw
  elabCommand cmd