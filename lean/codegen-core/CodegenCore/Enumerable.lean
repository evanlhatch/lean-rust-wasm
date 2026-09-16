/-
# CodegenCore.Enumerable — `Enumerable α`: exhaustive witness list

Doctrine §6 ("boilerplate families are generated, not written"): any
closed enum that needs an `all : List α` plus the completeness proof
`∀ x, x ∈ all` gets it from `deriving Enumerable` (nullary-constructor
inductives only — the handler gate enforces this).

Generated shape (for `inductive Color where | red | green | blue`):

    def Color.all : List Color := [.red, .green, .blue]

    instance : Enumerable Color where
      all := Color.all
      complete := fun x => by
        cases x <;> decide

The handler defines the `all` def THEN the instance (so the instance
references the def, keeping the binder chain simple).
-/

module

public import Lean

@[expose] public section

open Lean Elab Command
open Lean.Elab.Deriving
open Lean.Parser.Term

namespace CodegenCore

/-- `Enumerable α` — an exhaustive witness list (every `x : α` appears
    at least once in `all`). -/
class Enumerable (α : Type) where
  all : List α
  complete : ∀ x : α, x ∈ all

namespace Enumerable

/-- Generate `def <Name>.all : List <Name> := [ctor₁, …, ctorₙ]`. -/
def mkAllDef (indVal : InductiveVal) : TermElabM Syntax := do
  let ctorTerms : Array Term := (indVal.ctors.map fun c => (mkCIdent c : Term)).toArray
  let allList : Term ← `([$ctorTerms,*])
  let allName := indVal.name ++ `all
  `(def $(mkIdent allName) : List $(mkCIdent indVal.name) := $allList:term)

/-- Generate the `Enumerable` instance referencing `all`. -/
def mkInstance (indVal : InductiveVal) : TermElabM Syntax := do
  let allName := indVal.name ++ `all
  let completeProof : Term ← `(fun x => by
    have : x ∈ $(mkCIdent allName) := by
      cases x <;> decide
    exact this)
  `(instance : Enumerable $(mkCIdent indVal.name) where
    all := $(mkCIdent allName)
    complete := $completeProof:term)

/-- Deriving handler for `Enumerable` — applies only to enum types
    (nullary constructors, no params/indices, not recursive). -/
def mkHandler (declNames : Array Name) : CommandElabM Bool := do
  unless (← declNames.allM (fun n => isInductive n)) do
    return false
  for declName in declNames do
    withoutExposeFromCtors declName do
      unless (← isEnumType declName) do
        throwError "`Enumerable` can only be derived for enum types (nullary constructors only)"
      let indVal ← getConstInfoInduct declName
      let defCmd ← liftTermElabM <| mkAllDef indVal
      elabCommand defCmd
      let instCmd ← liftTermElabM <| mkInstance indVal
      elabCommand instCmd
  return true

initialize
  registerDerivingHandler ``CodegenCore.Enumerable mkHandler

end Enumerable
end CodegenCore