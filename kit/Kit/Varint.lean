/-
# Kit.Varint — the ONE LEB128 varint (the shared byte primitive)

The unsigned LEB128 encode/decode pair expressed through the kit's
`Kit.Codec` (the wire grade, 01-core §4) with pattern #2's append-form
law (`decVarNat? (encVarNat n ++ rest) = some (n, rest)`) proved and
stated as the composition discipline — `Codec.decode_encode` is that
law with the empty suffix, and the accepted-byte POLICY is the exact
image: the decoder is the canonical (minimal) one, so non-minimal LEB
encodings are the declared outside-of-policy surface, not folklore.
(wasm's spec grammar is more permissive; tightening lands with the
binary decoder order if a consumer needs it.)

HOME: C0 (the kit) because the varint is a general byte primitive, not
wasm-specific — the byte-for-byte twin lived in `WasmCore.Encode` and
`SchemaCore.Codec` (sibling C1 cores the cone rule separates), and both
now consume this module. The content is the WasmCore copy verbatim
(renamed to the neutral `encVarNat`/`decVarNat?` — the names the twin
already used); the proofs ported unchanged.

Totality evidence: every encoder is structural — folds/maps/flatMaps
over lists, and `encVarNat` recurses on an explicit fuel that strictly
decreases (each continuation step divides by ≥ 2), with the fuel
discharged by the round-trip theorem itself.

The five questions (notes/v3/01-core.md):

- **Root**: Crossing (the wire) — bytes are the target grammar, the
  naturals the source.
- **Carrier grade**: Kit.Codec (decode∘encode = id + the explicit
  accepted-byte policy); the append-form law (15-patterns #2) is the
  stated composition discipline on top.
- **Spine reading**: n/a — this is the shared atom, not an
  interpretation of a universe.
- **Ladder rung**: the round-trip law is a hand theorem with named
  content (the canonical-decoder agreement).
- **Gate row**: none directly — the consumers' test suites (the
  SchemaTests codec suite + the WasmCoreTests LEB128 sweep) are the
  standing evidence, plus the KitTests axiom pin.

Core-only (imports Kit.Correspondence only — the cone rule).
-/

import Kit.Correspondence

namespace Kit.Varint

/-! ## LEB128 — the unsigned pair (the codec) -/

/-- Unsigned LEB128, on an explicit fuel (structural — every
    continuation step divides by 128, so the fuel strictly decreases;
    `encVarNat` spends `n + 1`, always enough: the value drops below
    128 in at most `n` steps). -/
def encVarNatGo : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => if n < 128 then [n.toUInt8]
      else (128 + n % 128).toUInt8 :: encVarNatGo k (n / 128)

/-- The encoder: fuel `n + 1` suffices (each non-final step has a
    value ≥ 128, whose quotient is strictly smaller). -/
def encVarNat (n : Nat) : List UInt8 := encVarNatGo (n + 1) n

/-- The decoder: canonical (minimal) encodings only — a continuation
    group whose remainder value is 0 is the declared non-canonical
    shape and refuses. Returns the value + the unconsumed suffix.
    Truncated input (a dangling continuation bit) refuses. -/
def decVarNat? : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
      if b.toNat < 128 then some (b.toNat, rest)
      else
        match decVarNat? rest with
        | none => none
        | some (v, tail) =>
            if v = 0 then none else some (b.toNat % 128 + 128 * v, tail)

theorem encVarNatGo_dec_append : ∀ (k n : Nat) (rest : List UInt8),
    n < 128 ^ k → decVarNat? (encVarNatGo (k + 1) n ++ rest) = some (n, rest) := by
  intro k
  induction k with
  | zero =>
    intro n rest h
    have h0 : n = 0 := by omega
    subst h0
    simp [encVarNatGo, decVarNat?]
  | succ k ih =>
    intro n rest h
    rcases Nat.lt_or_ge n 128 with hlt | hge
    · have h256 : n < 256 := by omega
      simp only [encVarNatGo, if_pos hlt, decVarNat?,
        UInt8.toNat_ofNat_of_lt' h256, List.singleton_append]
    · have hdiv : n / 128 < 128 ^ k := by omega
      have hpos : 0 < n / 128 := by omega
      have h256 : (128 + n % 128) < 256 := by omega
      have hbyte : ((128 + n % 128 : Nat).toUInt8).toNat = 128 + n % 128 :=
        UInt8.toNat_ofNat_of_lt' h256
      rw [encVarNatGo, if_neg (by omega : ¬(n < 128)), List.cons_append, decVarNat?,
        if_neg (show ¬((128 + n % 128 : Nat).toUInt8).toNat < 128 from by rw [hbyte]; omega)]
      simp only [ih (n / 128) rest hdiv, if_neg (by omega : ¬(n / 128 = 0)), hbyte]
      have hval : (128 + n % 128) % 128 + 128 * (n / 128) = n := by omega
      simp only [hval]

/-- Fuel monotonicity (the discharge for `encVarNat_cons`). -/
theorem encVarNatGo_mono : ∀ (k₂ k₁ x : Nat), x + 1 ≤ k₁ → k₁ ≤ k₂ →
    encVarNatGo k₁ x = encVarNatGo k₂ x := by
  intro k₂
  induction k₂ with
  | zero => intro k₁ x h1 _; omega
  | succ k₂ ih =>
    intro k₁ x h1 h2
    match k₁ with
    | 0 => omega
    | k₁ + 1 =>
      show encVarNatGo (k₁ + 1) x = encVarNatGo (k₂ + 1) x
      simp only [encVarNatGo]
      by_cases hx : x < 128
      · simp only [if_pos hx]
      · have hle : x / 128 + 1 ≤ k₁ := by omega
        simp only [if_neg hx]
        rw [ih k₁ (x / 128) hle (by omega)]

/-- The multi-group shape of the encoding. -/
theorem encVarNat_cons : ∀ (n : Nat), 128 ≤ n →
    encVarNat n = (128 + n % 128).toUInt8 :: encVarNat (n / 128) := by
  intro n hge
  show encVarNatGo (n + 1) n = _
  rw [encVarNatGo, if_neg (by omega : ¬(n < 128)), encVarNat]
  rw [← encVarNatGo_mono n (n / 128 + 1) (n / 128) (by omega) (by omega)]

/-- PATTERN #2 — the append-form codec law: encoding plus any suffix
    decodes to the value and the suffix, exactly. -/
theorem decVarNat?_encVarNat_append : ∀ (n : Nat) (rest : List UInt8),
    decVarNat? (encVarNat n ++ rest) = some (n, rest) := by
  intro n rest
  exact encVarNatGo_dec_append n n rest (Nat.lt_pow_self (by decide))

/-- The exact-image theorem: everything the decoder accepts IS an
    encoder output plus its suffix — the accepted-byte policy is
    exactly the encoder's image (the `Codec` policy field's content). -/
theorem decVarNat?_encVarNat_eq : ∀ (a : List UInt8) (n : Nat) (rest : List UInt8),
    decVarNat? a = some (n, rest) → a = encVarNat n ++ rest := by
  intro a
  induction a with
  | nil => intro n rest h; simp [decVarNat?] at h
  | cons b a' ih =>
    intro n rest h
    rw [decVarNat?] at h
    by_cases hlt : b.toNat < 128
    · rw [if_pos hlt] at h
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      rw [encVarNat, encVarNatGo, if_pos hlt]
      congr 1
      exact UInt8.ofNat_toNat.symm
    · rw [if_neg hlt] at h
      cases hd : decVarNat? a' with
      | none => simp only [hd] at h; simp at h
      | some p =>
        obtain ⟨v, tail⟩ := p
        simp only [hd] at h
        by_cases hv : v = 0
        · rw [if_pos hv] at h; simp at h
        · rw [if_neg hv] at h
          obtain ⟨rfl, rfl⟩ := Option.some.inj h
          have hn128 : 128 ≤ b.toNat % 128 + 128 * v := by omega
          have h1 : (b.toNat % 128 + 128 * v) % 128 = b.toNat % 128 := by omega
          have h2 : (b.toNat % 128 + 128 * v) / 128 = v := by omega
          have h256 : b.toNat < 256 := UInt8.toNat_lt_size b
          have hbyte : (128 + b.toNat % 128).toUInt8 = b := by
            rw [show (128 + b.toNat % 128) = b.toNat from by omega]
            exact UInt8.ofNat_toNat
          rw [encVarNat_cons _ hn128, h2, h1, List.cons_append, ← ih v rest hd, hbyte]

/-- THE LEB128 codec (the kit's wire grade, 01-core §4): encode/decode
    pair + the exact-image policy + both law fields. The append-form
    law (pattern #2) is `decVarNat?_encVarNat_append` —
    `decode_encode` is that law with the empty suffix. -/
def varintCodec : Kit.Codec (List UInt8) Nat where
  encode := encVarNat
  decode := fun bytes => (decVarNat? bytes).map (fun p => p.1)
  policy bytes := ∃ n rest, bytes = encVarNat n ++ rest
  decode_encode n := by
    have h := decVarNat?_encVarNat_append n []
    rw [List.append_nil (encVarNat n)] at h
    show (decVarNat? (encVarNat n)).map (fun p => p.1) = some n
    rw [h]
    rfl
  decode_some_policy bytes b h := by
    cases hd : decVarNat? bytes with
    | none => rw [hd] at h; simp at h
    | some p =>
      obtain ⟨x, rest⟩ := p
      rw [hd] at h
      simp only [Option.map_some] at h
      have hx : x = b := Option.some.inj h
      subst hx
      exact ⟨x, rest, decVarNat?_encVarNat_eq bytes x rest hd⟩

end Kit.Varint
