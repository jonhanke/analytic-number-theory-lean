/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Ch1to6.LOneLog
import NTKB.Analytic.Davenport.Ch1to6.LOneOdd

/-!
# Davenport, Chapters 1 and 6: `L(1, χ)` for a real even character

* §6, p. 50, formula (18): for a fundamental discriminant `d > 1` and `χ = (d/·)`,
  `L(1, χ) = -(1/√d) ∑_{m=1}^{d-1} χ(m) log sin(πm/d)`.
* §1, p. 9, formula (9): for a prime `q ≡ 1 (mod 4)`,
  `L(1) = -(1/√q) ∑_{m=1}^{q-1} (m/q) log(2 sin(πm/q))`.

Both come from `NTKB.Davenport.LFunction_one_eq_neg_sum_log` with `τ(χ) = √N`
(Gauss's sum) and `-log(1 - e(m/N)) = -log(2 sin(πm/N)) + i(π/2 - πm/N)`; the imaginary part and
the terms `log 2` cancel because `χ` is even and `∑ χ(m) = 0`.
-/

noncomputable section

open Complex Finset DirichletCharacter
open scoped Real

namespace NTKB.Davenport

variable {N : ℕ} [NeZero N]

/-- `e(m/N) = e^{i θ}` with `θ = 2πm/N`. -/
theorem stdAddChar_natCast_eq_cexp (m : ℕ) :
    (ZMod.stdAddChar (m : ZMod N) : ℂ) = cexp ((2 * π * m / N : ℝ) * I) := by
  have h := ZMod.stdAddChar_coe (N := N) (m : ℤ)
  rw [Int.cast_natCast] at h
  rw [h]
  congr 1
  push_cast
  ring

/-- For `0 < m < N`: `log(1 - e(m/N)) = log(2 sin(πm/N)) + i(πm/N - π/2)`. -/
theorem log_one_sub_stdAddChar {m : ℕ} (hm : m ∈ Ico 1 N) :
    log (1 - ZMod.stdAddChar (m : ZMod N)) =
      (Real.log (2 * Real.sin (π * m / N)) : ℂ) + ((π * m / N - π / 2 : ℝ) : ℂ) * I := by
  rw [mem_Ico] at hm
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
  have hmN : (m : ℝ) < N := by exact_mod_cast hm.2
  have h0 : 0 < 2 * π * m / N := by positivity
  have h2 : 2 * π * m / N < 2 * π := by
    rw [div_lt_iff₀ hN]; nlinarith [Real.pi_pos]
  have := neg_log_one_sub_exp h0 h2
  rw [stdAddChar_natCast_eq_cexp]
  have e1 : 2 * π * m / N / 2 = π * m / N := by ring
  rw [e1] at this
  have := congrArg Neg.neg this
  rw [neg_neg] at this
  rw [this]
  push_cast
  ring

omit [NeZero N] in
/-- For an even character, `∑_{m=1}^{N-1} χ(m) m = (N/2) ∑_{m=1}^{N-1} χ(m)`. -/
theorem two_mul_sum_mul_of_even {χ : DirichletCharacter ℂ N} (heven : χ.Even) :
    2 * ∑ m ∈ Ico 1 N, χ m * (m : ℂ) = N * ∑ m ∈ Ico 1 N, χ m := by
  have hrefl : ∑ m ∈ Ico 1 N, χ m * (m : ℂ) = ∑ m ∈ Ico 1 N, χ m * ((N : ℂ) - m) := by
    refine Finset.sum_nbij' (fun m ↦ N - m) (fun m ↦ N - m) ?_ ?_ ?_ ?_ ?_
    · intro m hm; simp only [mem_Ico] at hm ⊢; omega
    · intro m hm; simp only [mem_Ico] at hm ⊢; omega
    · intro m hm; simp only [mem_Ico] at hm; omega
    · intro m hm; simp only [mem_Ico] at hm; omega
    · intro m hm
      simp only [mem_Ico] at hm
      have hle : m ≤ N := hm.2.le
      rw [Nat.cast_sub hle, Nat.cast_sub hle, ZMod.natCast_self, zero_sub]
      have : χ (-(m : ZMod N)) = χ m := by
        rw [neg_eq_neg_one_mul, map_mul, heven, one_mul]
      rw [this]
      ring
  rw [two_mul]
  nth_rewrite 2 [hrefl]
  rw [← sum_add_distrib, mul_sum]
  exact sum_congr rfl fun m _ ↦ by ring

/-- `∑_{m=1}^{N-1} χ(m) = 0` for `χ ≠ 1`, `N ≠ 1`. -/
theorem sum_Ico_char_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hN : N ≠ 1) :
    ∑ m ∈ Ico 1 N, χ m = 0 := by
  have h := MulChar.sum_eq_zero_of_ne_one hχ
  have h2 : ∑ a : ZMod N, χ a = ∑ m ∈ range N, χ (m : ZMod N) := by
    rw [← NTKB.sum_val_eq_sum_range (fun m : ℕ ↦ χ (m : ZMod N))]
    simp only [ZMod.natCast_zmod_val]
  rw [h2, range_eq_Ico, sum_eq_sum_Ico_succ_bot (NeZero.pos N), Nat.cast_zero, χ.map_zero' hN,
    zero_add] at h
  exact h

/-- `L(1, χ)` for a real even primitive character with `τ(χ) = √N`:
`L(1, χ) = -(1/√N) ∑_{m=1}^{N-1} χ(m) log(2 sin(πm/N))`. -/
theorem LFunction_one_of_even_real {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (heven : χ.Even) (hreal : χ⁻¹ = χ)
    (hτ : gaussSum χ ZMod.stdAddChar = (√N : ℂ)) :
    LFunction χ 1 = -((√N : ℝ) : ℂ)⁻¹ *
      ∑ m ∈ Ico 1 N, χ m * (Real.log (2 * Real.sin (π * m / N)) : ℂ) := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    have h := hχ
    rw [IsPrimitive, DirichletCharacter.conductor_one] at h
    exact hN h.symm
  rw [LFunction_one_eq_neg_sum_log hχ hN, hreal, hτ]
  congr 1
  have hsum := sum_Ico_char_eq_zero hχ1 hN
  have hmul := two_mul_sum_mul_of_even heven
  rw [hsum, mul_zero] at hmul
  rw [sum_congr rfl fun m hm ↦ by rw [log_one_sub_stdAddChar hm]]
  simp only [mul_add, sum_add_distrib]
  have him : ∑ m ∈ Ico 1 N, χ m * (((π * m / N - π / 2 : ℝ) : ℂ) * I) = 0 := by
    have : ∑ m ∈ Ico 1 N, χ m * (((π * m / N - π / 2 : ℝ) : ℂ) * I) =
        (π / N * I) * ∑ m ∈ Ico 1 N, χ m * (m : ℂ) - (π / 2 * I) * ∑ m ∈ Ico 1 N, χ m := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun m _ ↦ ?_
      push_cast; ring
    rw [this, hsum, mul_zero, sub_zero]
    have : ∑ m ∈ Ico 1 N, χ m * (m : ℂ) = 0 := by
      have := hmul; simpa using this
    rw [this, mul_zero]
  rw [him, add_zero]

/-- `log(2 sin(πm/N)) = log 2 + log sin(πm/N)` for `0 < m < N`. -/
theorem log_two_mul_sin {m : ℕ} (hm : m ∈ Ico 1 N) :
    Real.log (2 * Real.sin (π * m / N)) = Real.log 2 + Real.log (Real.sin (π * m / N)) := by
  rw [mem_Ico] at hm
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
  have hmN : (m : ℝ) < N := by exact_mod_cast hm.2
  have hs : 0 < Real.sin (π * m / N) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hN]; nlinarith [Real.pi_pos]
  exact Real.log_mul (by norm_num) hs.ne'

/-- The version of `LFunction_one_of_even_real` with `log sin` (the terms `log 2` cancel). -/
theorem LFunction_one_of_even_real' {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) (heven : χ.Even) (hreal : χ⁻¹ = χ)
    (hτ : gaussSum χ ZMod.stdAddChar = (√N : ℂ)) :
    LFunction χ 1 = -((√N : ℝ) : ℂ)⁻¹ *
      ∑ m ∈ Ico 1 N, χ m * (Real.log (Real.sin (π * m / N)) : ℂ) := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    have h := hχ
    rw [IsPrimitive, DirichletCharacter.conductor_one] at h
    exact hN h.symm
  rw [LFunction_one_of_even_real hχ hN heven hreal hτ]
  congr 1
  rw [sum_congr rfl fun m hm ↦ by rw [log_two_mul_sin hm]]
  simp only [ofReal_add, mul_add, sum_add_distrib, ← sum_mul, sum_Ico_char_eq_zero hχ1 hN,
    zero_mul, zero_add]

/-- **Davenport §6, pp. 50–51, formula (18).** For a fundamental discriminant `d > 1` and
`χ = (d/·)`: `L(1, χ) = -(1/√d) ∑_{m=1}^{d-1} χ(m) log sin(πm/d)`. -/
@[kb "davenport1980" "Ch 6, pp. 50-51, (18)"]
theorem LFunction_one_kroneckerChar_of_pos {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hpos : 1 < D) [NeZero D.natAbs] :
    LFunction (kroneckerChar D) 1 = -((√(D : ℝ) : ℝ) : ℂ)⁻¹ *
      ∑ m ∈ Ico 1 D.natAbs, kroneckerChar D m * (Real.log (Real.sin (π * m / D)) : ℂ) := by
  have hDN : ((D.natAbs : ℕ) : ℝ) = (D : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast (by omega : 0 < D))]
  have hN1 : D.natAbs ≠ 1 := by omega
  have heven : (kroneckerChar D).Even := by
    rw [DirichletCharacter.Even, kroneckerChar_neg_one hD, if_pos (by omega)]
  have hτ : gaussSum (kroneckerChar D) ZMod.stdAddChar = (√(D.natAbs : ℝ) : ℂ) := by
    rw [gaussSum_kroneckerChar hD, if_pos (by omega), hDN]
  rw [LFunction_one_of_even_real' (kroneckerChar_isPrimitive hD) hN1 heven
    (kroneckerChar_inv hD) hτ, hDN]

/-- **Davenport §1, p. 9, formula (9).** For a prime `q ≡ 1 (mod 4)`:
`L(1) = -(1/√q) ∑_{m=1}^{q-1} (m/q) log(2 sin(πm/q))`. -/
@[kb "davenport1980" "Ch 1, p. 9, (9)"]
theorem LFunction_one_legendreChar_of_one_mod_four {q : ℕ} [Fact q.Prime] (hq : q % 4 = 1) :
    LFunction (legendreChar q) 1 = -((√(q : ℝ) : ℝ) : ℂ)⁻¹ *
      ∑ m ∈ Ico 1 q, (legendreSym q m : ℂ) * (Real.log (2 * Real.sin (π * m / q)) : ℂ) := by
  have hq2 : q ≠ 2 := by omega
  have hq1 : q ≠ 1 := (Fact.out : q.Prime).one_lt.ne'
  have hprim : (legendreChar q).IsPrimitive := by
    rw [← jacobiChar_prime]; exact isPrimitive_jacobiChar_prime q hq2
  have heven : (legendreChar q).Even := by
    rw [DirichletCharacter.Even, legendreChar_apply, quadraticChar_neg_one, ZMod.card,
      ZMod.χ₄_nat_one_mod_four hq]
    · simp
    · rw [ZMod.ringChar_zmod_n]; exact hq2
  have hτ : gaussSum (legendreChar q) ZMod.stdAddChar = (√(q : ℝ) : ℂ) := by
    rw [gaussSum_legendreChar q hq2, if_pos hq]
  rw [LFunction_one_of_even_real hprim hq1 heven legendreChar_isQuadratic.inv hτ]
  simp_rw [legendreChar_natCast]

end NTKB.Davenport
