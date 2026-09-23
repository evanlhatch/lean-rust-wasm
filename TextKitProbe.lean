import TextKit.Basic

namespace TextKit

inductive Grammar : Type where
  | tok : String → Grammar
  | scanTo : String → Grammar
  | seq : List Grammar → Grammar
  | alt : List Grammar → Grammar
  | rep : Grammar → Grammar
  | named : String → Grammar
  deriving BEq, Inhabited

def firstSet : Grammar → List Char
  | .tok s => s.toList.head? (n := ' ')
  | _ => []

def nonemptyFS (g : Grammar) : Bool := !(firstSet g).isEmpty

theorem nonemptyFS_iff (g : Grammar) : nonemptyFS g = true ↔ firstSet g ≠ [] := by
  simp [nonemptyFS, List.isEmpty_eq_false_iff]

#check nonemptyFS_iff.mpr
#check List.isEmpty_eq_false_iff
