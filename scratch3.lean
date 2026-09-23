example (a b c : Nat) (h : 1 + max a b ≤ c + 1) : b ≤ c := by omega
example (a b c : Nat) (h : max a b ≤ c) : a ≤ c := by omega
