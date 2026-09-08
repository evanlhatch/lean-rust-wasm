import Substrait.Decode
import Substrait.Emit.Text

open Substrait.Decode.Text
open Substrait

-- omega repro
example (c : Char) (fv : c.isDigit = true) : False := by
  have hv : c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val := by
    have hA1 : c.val ≥ 'A'.val := by native_decide
    have hA2 : c.val ≤ 'Z'.val := by native_decide
    exact ⟨hA1, hA2⟩
  have hd : c.val ≥ '0'.val ∧ c.val ≤ '9'.val := by
    unfold Char.isDigit at fv
    rw [Bool.and_eq_true] at fv
    simpa using fv
  rcases hv with ⟨hv1, hv2⟩
  rcases hd with ⟨hd1, hd2⟩
  have hA : 'A'.val = 65 := by native_decide
  have hZ : 'Z'.val = 90 := by native_decide
  have h0 : '0'.val = 48 := by native_decide
  have h9 : '9'.val = 57 := by native_decide
  rw [hA] at hv1
  rw [hZ] at hv2
  rw [h0] at hd1
  rw [h9] at hd2
  omega

-- ite text reduction repro
example (b : Bool) : ((if b then "true" else "false").toList = 'f' :: 'a' :: 'l' :: 's' :: 'e' :: []) := by
  cases b <;> simp

-- rw with hred
example : (if false = true then "true" else "false") = "false" := by native_decide
example : (if true = true then "true" else "false") = "true" := by native_decide
