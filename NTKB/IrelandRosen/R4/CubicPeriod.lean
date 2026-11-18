/-
Ireland–Rosen, Chapter 9, §12 (Lemma 1, Lemma 2 and its Corollary): the cubic Gauss period
`G = ∑_{t mod p} e^{2πi t³/p}` for a prime `p ≡ 1 (mod 3)` is real, equals `g(χ) + g(χ̄)` for a
cubic character `χ`, and is a root of `x³ - 3px - Ap` where `4p = A² + 27B²`, `A ≡ 1 (mod 3)`.
-/
import NTKB.IrelandRosen.R2.ZetaCubicCurve
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace NTKB.IrelandRosen

/-- The cubic Gauss period `G = ∑_{t mod p} e^{2πi t³/p}`. -/
noncomputable def cubicPeriod (p : ℕ) [NeZero p] : ℂ := ∑ t : ZMod p, ZMod.stdAddChar (t ^ 3)

variable {p : ℕ} [Fact p.Prime]

/-- `G` is real (it equals `∑ cos (2π t³/p)`). -/
theorem cubicPeriod_im (_hp : p % 3 = 1) : (cubicPeriod p).im = 0 := by
  have h : starRingEnd ℂ (cubicPeriod p) = cubicPeriod p := by
    unfold cubicPeriod
    rw [map_sum]
    rw [← Equiv.sum_comp (Equiv.neg (ZMod p))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← AddChar.map_neg_eq_conj]
    simp [Odd.neg_pow (by decide : Odd 3)]
  exact Complex.conj_eq_iff_im.mp h

/-- **Ireland–Rosen, Chapter 9, §12, Lemma 1.** -/
@[kb "irelandrosen1990" "Ch. 9, §12, Lemma 1, p. 143"]
theorem cubicPeriod_eq (hp : p % 3 = 1) {χ : MulChar (ZMod p) ℂ} (hχ : orderOf χ = 3) :
    cubicPeriod p = gaussSum χ ZMod.stdAddChar + gaussSum χ⁻¹ ZMod.stdAddChar := by
  have h3 : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  have h1 := cubic_ne_one hχ
  have hψ1 : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := fun h =>
    (ZMod.isPrimitive_stdAddChar p) one_ne_zero (by ext x; simp [h])
  have hfib : cubicPeriod p = ∑ a : ZMod p, (numSolPow 3 a : ℂ) * ZMod.stdAddChar a := by
    unfold cubicPeriod
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (ZMod p)) (fun t : ZMod p => t ^ 3)]
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold numSolPow
    rw [Finset.sum_congr rfl (g := fun _ => (ZMod.stdAddChar a : ℂ))]
    · simp only [Finset.sum_const, nsmul_eq_mul]
      congr
    · intro t ht
      rw [(Finset.mem_filter.mp ht).2]
  rw [hfib]
  simp_rw [numSolPow_eq_sum_range h3 hχ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, add_mul, Finset.sum_add_distrib, cubic_sq_eq_inv hχ]
  have hz : ∑ a : ZMod p, bookChar (1 : MulChar (ZMod p) ℂ) a * ZMod.stdAddChar a = 0 := by
    simp [bookChar_one, AddChar.sum_eq_zero_of_ne_one hψ1]
  have e : ∀ ψ : MulChar (ZMod p) ℂ, ψ ≠ 1 →
      ∑ a : ZMod p, bookChar ψ a * ZMod.stdAddChar a = gaussSum ψ ZMod.stdAddChar := by
    intro ψ hψ
    unfold gaussSum
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [bookChar_of_ne_one hψ]
  rw [hz, zero_add, e χ h1, e χ⁻¹ (inv_ne_one.mpr h1)]

/-- **Ireland–Rosen, Chapter 9, §12, Lemma 2.** If `J(χ, χ) = a + bω` then
`G³ - 3pG - (2a - b)p = 0`. (The book takes `χ = χ_π` with `J(χ_π, χ_π) = π = a + bω`; here `χ`
is any cubic character and `a + bω := J(χ, χ)`.) -/
@[kb "irelandrosen1990" "Ch. 9, §12, Lemma 2, p. 143"]
theorem cubicPeriod_cubic_eq (hp : p % 3 = 1) {χ : MulChar (ZMod p) ℂ} (hχ : orderOf χ = 3)
    {a b : ℤ} (hJ : multiJacobiSum ![χ, χ] = a + b * omega3) :
    cubicPeriod p ^ 3 - 3 * p * cubicPeriod p - (2 * a - b) * p = 0 := by
  have h1 := cubic_ne_one hχ
  have hψ := ZMod.isPrimitive_stdAddChar p
  have hχ' : orderOf χ⁻¹ = 3 := by rw [orderOf_inv]; exact hχ
  have g1 := gaussSum_cube hχ hψ
  have g2 := gaussSum_cube hχ' hψ
  rw [multiJacobiSum_pair_inv_inv, ZMod.card] at g2
  rw [ZMod.card] at g1
  have hinv := gaussSum_mul_gaussSum_inv h1 hψ
  rw [cubic_apply_neg_one hχ, one_mul, ZMod.card] at hinv
  have hsum : multiJacobiSum ![χ, χ] + starRingEnd ℂ (multiJacobiSum ![χ, χ]) = 2 * a - b := by
    rw [Complex.add_conj]
    have := re_add_mul_omega3 a b
    rw [← hJ] at this
    exact_mod_cast this
  rw [cubicPeriod_eq hp hχ, ← hsum]
  set g := gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)
  set g' := gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)
  linear_combination g1 + g2 + 3 * (g + g') * hinv

/-- **Ireland–Rosen, Chapter 9, §12, Corollary to Lemma 2.** `G` is a real root of
`x³ - 3px - Ap` where `4p = A² + 27B²`, `A ≡ 1 (mod 3)`. -/
@[kb "irelandrosen1990" "Ch. 9, §12, Corollary, p. 143"]
theorem exists_cubicPeriod_root (hp : p % 3 = 1) :
    ∃ A B : ℤ, 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2 ∧ A ≡ 1 [ZMOD 3] ∧
      (cubicPeriod p).im = 0 ∧ cubicPeriod p ^ 3 - 3 * p * cubicPeriod p - A * p = 0 := by
  have h3 : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := exists_orderOf_eq h3
  obtain ⟨a, b, hJ, -, -, -⟩ := cubic_jacobiSum_eq h3 hχ
  obtain ⟨A, B, hre, h, hA⟩ := cubic_four_mul_card_eq h3 hχ
  rw [ZMod.card] at h
  refine ⟨A, B, h, hA, cubicPeriod_im hp, ?_⟩
  have := cubicPeriod_cubic_eq hp hχ hJ
  have hA' : (A : ℂ) = 2 * a - b := by
    have h2 := re_add_mul_omega3 a b
    rw [← hJ] at h2
    rw [hre] at h2
    exact_mod_cast h2
  rw [hA']
  exact this

end NTKB.IrelandRosen
