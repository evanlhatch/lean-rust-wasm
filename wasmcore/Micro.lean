public import Kit.Varint


@[expose] public section
theorem intNat {p : Int} (h : 0 ≤ p) : ∃ n : Nat, p = n ∧ p.toNat = n :=
  ⟨p.toNat, (Int.toNat_of_nonneg h).symm, rfl⟩

theorem toNat_cast (n : Nat) : ((n : Int).toNat) = n := rfl

theorem u8toNat (n : Nat) : n.toUInt8.toNat = n % 256 := rfl

theorem contByte_big (p : Int) (h1 : 0 ≤ p) (h2 : p < 128) :
    ¬(((p + 128 : Int).toNat.toUInt8).toNat < 128) := by
  obtain ⟨n, hn, hnt⟩ := intNat h1
  have hn128 : n < 128 := by omega
  rw [hn]
  trace_state
  rw [show ((↑n + 128 : Int).toNat = n + 128) from rfl]
  trace_state
  rw [u8toNat]
  omega

end -- public section

