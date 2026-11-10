/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Elementary.SpecialValues.FundamentalGaussSum

/-!
# `kroneckerChar D` is the Kronecker symbol `(D/·)`

For a fundamental discriminant `D` and an odd natural number `n`,
`χ_D(n) = J(D | n)` (`NTKB.kroneckerChar_apply_odd`), where `J` is Mathlib's Jacobi symbol. So
`NTKB.kroneckerChar D` agrees with the Kronecker symbol `(D/n)` at every odd `n`; it is a character
modulo `|D|`, hence determined by these values (every residue class prime to `|D|` contains odd
numbers). The proof is quadratic reciprocity with its supplements (`J(-1|n) = χ_{-4}(n)`,
`J(2|n) = χ_8(n)`).
-/

noncomputable section

open Complex

namespace NTKB

/-- Reciprocity for an odd integer `k` and an odd natural number `n`:
`J(k | n) = J(n | |k|)` if `k ≡ 1 (mod 4)` and `J(k | n) = χ_{-4}(n) J(n | |k|)` if `k ≡ 3 (mod 4)`. -/
theorem jacobiSym_int_eq_of_odd {k : ℤ} (hk : k % 2 = 1) {n : ℕ} (hn : Odd n) :
    jacobiSym k n = (if k % 4 = 1 then 1 else ZMod.χ₄ (n : ZMod 4)) * jacobiSym n k.natAbs := by
  have ha : Odd k.natAbs := Nat.odd_iff.mpr (by omega)
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hrec := jacobiSym.quadratic_reciprocity' ha hn
  rw [qrSign.neg_one_pow hn ha] at hrec
  have hχ := ZMod.χ₄_eq_neg_one_pow hn2
  have hχsq : ZMod.χ₄ (n : ZMod 4) * ZMod.χ₄ (n : ZMod 4) = 1 := by
    rw [hχ, ← pow_add, ← two_mul, pow_mul]; norm_num
  rcases le_or_gt 0 k with hpos | hneg
  · -- `k = |k|`
    have hkabs : k = (k.natAbs : ℤ) := by omega
    conv_lhs => rw [hkabs]
    rw [hrec]
    by_cases h1 : k % 4 = 1
    · rw [if_pos h1, one_mul]
      have : Even (n / 2 * (k.natAbs / 2)) := by
        rw [Nat.even_mul]; right; rw [Nat.even_iff]; omega
      rw [this.neg_one_pow, one_mul]
    · rw [if_neg h1]
      have : (-1 : ℤ) ^ (n / 2 * (k.natAbs / 2)) = (-1) ^ (n / 2) := by
        rw [pow_mul]
        have hodd : Odd (k.natAbs / 2) := by rw [Nat.odd_iff]; omega
        rcases neg_one_pow_eq_or ℤ (n / 2) with h | h <;> rw [h]
        · exact one_pow _
        · exact hodd.neg_one_pow
      rw [this, ← hχ]
  · -- `k = -|k|`
    have hkabs : k = -1 * (k.natAbs : ℤ) := by omega
    conv_lhs => rw [hkabs]
    rw [jacobiSym.mul_left, jacobiSym.at_neg_one hn, hrec]
    by_cases h1 : k % 4 = 1
    · rw [if_pos h1, one_mul]
      have : (-1 : ℤ) ^ (n / 2 * (k.natAbs / 2)) = (-1) ^ (n / 2) := by
        rw [pow_mul]
        have hodd : Odd (k.natAbs / 2) := by rw [Nat.odd_iff]; omega
        rcases neg_one_pow_eq_or ℤ (n / 2) with h | h <;> rw [h]
        · exact one_pow _
        · exact hodd.neg_one_pow
      rw [this, ← hχ, ← mul_assoc, hχsq, one_mul]
    · rw [if_neg h1]
      have : Even (n / 2 * (k.natAbs / 2)) := by
        rw [Nat.even_mul]; right; rw [Nat.even_iff]; omega
      rw [this.neg_one_pow, one_mul]

/-- `J(z | m)` through `jacobiChar` at the residue of a natural number. -/
private theorem jacobiChar_natCast {m : ℕ} [NeZero m] (n : ℕ) :
    jacobiChar m (n : ZMod m) = (jacobiSym n m : ℂ) := by
  rw [← jacobiChar_intCast]; simp

/-- For odd `n`, `χ_8(n)^3 = χ_8(n)`. -/
private theorem chi8_pow_three {n : ℕ} (hn : n % 2 = 1) :
    ZMod.χ₈ (n : ZMod 8) ^ 3 = ZMod.χ₈ (n : ZMod 8) := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega)]
  split_ifs <;> norm_num

/-- **`χ_D(n) = J(D | n)` for every odd `n`**: `kroneckerChar D` is the Kronecker symbol. -/
theorem kroneckerChar_apply_odd {D : ℤ} (hD : IsFundamentalDiscriminant D) [NeZero D.natAbs]
    {n : ℕ} (hn : Odd n) :
    kroneckerChar D (n : ZMod D.natAbs) = (jacobiSym D n : ℂ) := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  rcases hD with ⟨h1, -⟩ | ⟨h0, h23, -⟩
  · rw [kroneckerChar, if_pos (by omega), jacobiChar_natCast,
      jacobiSym_int_eq_of_odd (by omega) hn, if_pos h1, one_mul]
  rcases h23 with h2 | h3
  · -- `D = 8k`
    have h16 : D % 16 = 8 := by omega
    set k := D / 8 with hk
    have : NeZero k.natAbs := ⟨by omega⟩
    have hN : D.natAbs = 8 * k.natAbs := natAbs_eq_eight_mul (by omega)
    have hm : Odd k.natAbs := Nat.odd_iff.mpr (by omega)
    have hcop : Nat.Coprime 8 k.natAbs := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hm)
    have hJD : jacobiSym D n = ZMod.χ₈ (n : ZMod 8) * jacobiSym k n := by
      conv_lhs => rw [show D = 2 ^ 3 * k by omega]
      rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two hn, chi8_pow_three hn2]
    rw [hJD, jacobiSym_int_eq_of_odd (by omega) hn]
    by_cases hk1 : k % 4 = 1
    · rw [kroneckerChar, if_neg (by omega), dif_neg (by omega), dif_pos h16, if_pos hk1,
        changeLevel_mul_changeLevel_apply hN hcop, ZMod.cast_natCast ⟨k.natAbs, hN⟩,
        ZMod.cast_natCast ⟨8, by rw [hN, mul_comm]⟩, jacobiChar_natCast, if_pos hk1, one_mul]
      push_cast
      rfl
    · rw [kroneckerChar, if_neg (by omega), dif_neg (by omega), dif_pos h16, if_neg hk1,
        changeLevel_mul_changeLevel_apply hN hcop, ZMod.cast_natCast ⟨k.natAbs, hN⟩,
        ZMod.cast_natCast ⟨8, by rw [hN, mul_comm]⟩, jacobiChar_natCast, if_neg hk1]
      have hc : chi8' (n : ZMod 8) =
          (ZMod.χ₄ (n : ZMod 4) : ℂ) * (ZMod.χ₈ (n : ZMod 8) : ℂ) := by
        rw [chi8', MulChar.ringHomComp_apply, ZMod.χ₈'_eq_χ₄_mul_χ₈,
          ZMod.cast_natCast (by norm_num : 4 ∣ 8), map_mul]
        rfl
      rw [hc]
      push_cast
      ring
  · -- `D = 4k`, `k ≡ 3 (mod 4)`
    have h8 : D % 8 = 4 := by omega
    set k := D / 4 with hk
    have : NeZero k.natAbs := ⟨by omega⟩
    have hN : D.natAbs = 4 * k.natAbs := natAbs_eq_four_mul (by omega)
    have hm : Odd k.natAbs := Nat.odd_iff.mpr (by omega)
    have hcop : Nat.Coprime 4 k.natAbs := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
    have hJD : jacobiSym D n = jacobiSym k n := by
      conv_lhs => rw [show D = 4 * k by omega]
      rw [jacobiSym.mul_left, jacobiSym.at_four hn, one_mul]
    rw [hJD, jacobiSym_int_eq_of_odd (by omega) hn, if_neg (by omega), kroneckerChar,
      if_neg (by omega), dif_pos h8, changeLevel_mul_changeLevel_apply hN hcop,
      ZMod.cast_natCast ⟨k.natAbs, hN⟩, ZMod.cast_natCast ⟨4, by rw [hN, mul_comm]⟩,
      jacobiChar_natCast]
    push_cast
    rfl

end NTKB
