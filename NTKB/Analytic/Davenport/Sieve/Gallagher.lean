/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import NTKB.Attr

/-!
# Gallagher's lemma and Parseval for trigonometric polynomials
(Davenport, Multiplicative Number Theory, ch. 27, pp. 156–157)

* `norm_le_integral_norm_add_integral_norm_deriv`: if `f` is `C¹` on `[0,1]` then for
  `x ∈ [0,1]`, `|f x| ≤ ∫₀¹ |f| + ∫₀¹ |f'|`.
* `integral_norm_sum_exp_sq`: `∫₀¹ |∑ a_n e(nα)|² dα = ∑ |a_n|²`.
-/

namespace NTKB.Davenport

open Finset Real

lemma gallagher_ibp_aux {f f' : ℝ → ℂ} (hf : ∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivAt f (f' u) u)
    (hf' : ContinuousOn f' (Set.Icc 0 1)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (c : ℝ) :
    ∫ t in a..b, ((t : ℂ) - c) * f' t =
      ((b : ℂ) - c) * f b - ((a : ℂ) - c) * f a - ∫ t in a..b, f t := by
  have hsub : Set.uIcc a b ⊆ Set.Icc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc ha hb
  have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := fun t : ℝ => (t : ℂ) - c) (u' := fun _ => (1 : ℂ)) (v := f) (v' := f')
    (fun x _ => by
      have h := (hasDerivAt_id x).ofReal_comp
      simpa using h.sub_const (c : ℂ))
    (fun x hx => hf x (hsub hx))
    intervalIntegrable_const
    ((hf'.mono hsub).intervalIntegrable)
  simpa using this

/-- **Gallagher's lemma**: if `f` has a continuous derivative on `[0, 1]`, then for `0 ≤ x ≤ 1`,
`|f(x)| ≤ ∫₀¹ |f(u)| du + ∫₀¹ |f'(u)| du`. -/
@[kb "davenport1980" "Ch 27, p. 156"]
theorem norm_le_integral_norm_add_integral_norm_deriv {f : ℝ → ℂ} {f' : ℝ → ℂ}
    (hf : ∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivAt f (f' u) u) (hf' : ContinuousOn f' (Set.Icc 0 1))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ‖f x‖ ≤ (∫ u in (0:ℝ)..1, ‖f u‖) + ∫ u in (0:ℝ)..1, ‖f' u‖ := by
  obtain ⟨hx0, hx1⟩ := hx
  have hfc : ContinuousOn f (Set.Icc 0 1) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hfi : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b ha hab hb
    apply ContinuousOn.intervalIntegrable
    refine hfc.mono ?_
    rw [Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc ha hb
  have hgi : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun u => ‖f' u‖) MeasureTheory.volume a b := by
    intro a b ha hab hb
    apply ContinuousOn.intervalIntegrable
    refine (hf'.norm).mono ?_
    rw [Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc ha hb
  have h1 := gallagher_ibp_aux hf hf' (le_refl 0) hx0 hx1 0
  have h2 := gallagher_ibp_aux hf hf' hx0 hx1 (le_refl 1) 1
  have hadd : (∫ t in (0:ℝ)..x, f t) + ∫ t in x..1, f t = ∫ t in (0:ℝ)..1, f t :=
    intervalIntegral.integral_add_adjacent_intervals (hfi 0 x (le_refl _) hx0 hx1)
      (hfi x 1 hx0 hx1 (le_refl _))
  have hgadd : (∫ t in (0:ℝ)..x, ‖f' t‖) + ∫ t in x..1, ‖f' t‖ = ∫ t in (0:ℝ)..1, ‖f' t‖ :=
    intervalIntegral.integral_add_adjacent_intervals (hgi 0 x (le_refl _) hx0 hx1)
      (hgi x 1 hx0 hx1 (le_refl _))
  have key : f x = (∫ t in (0:ℝ)..1, f t) + (∫ t in (0:ℝ)..x, ((t : ℂ) - ((0:ℝ):ℂ)) * f' t)
      + ∫ t in x..1, ((t : ℂ) - ((1:ℝ):ℂ)) * f' t := by
    rw [h1, h2, ← hadd]
    push_cast
    ring
  have b1 : ‖∫ t in (0:ℝ)..x, ((t : ℂ) - ((0:ℝ):ℂ)) * f' t‖ ≤ ∫ t in (0:ℝ)..x, ‖f' t‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le hx0 _ (hgi 0 x (le_refl _) hx0 hx1)
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have : |t| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    simp only [norm_mul, Complex.ofReal_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) this
  have b2 : ‖∫ t in x..1, ((t : ℂ) - ((1:ℝ):ℂ)) * f' t‖ ≤ ∫ t in x..1, ‖f' t‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le hx1 _ (hgi x 1 hx0 hx1 (le_refl _))
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have : |t - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have e : ((t : ℂ) - ((1:ℝ):ℂ)) = ((t - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, e, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) this
  have b0 : ‖∫ t in (0:ℝ)..1, f t‖ ≤ ∫ t in (0:ℝ)..1, ‖f t‖ :=
    intervalIntegral.norm_integral_le_integral_norm zero_le_one
  calc ‖f x‖ ≤ ‖∫ t in (0:ℝ)..1, f t‖ + ‖∫ t in (0:ℝ)..x, ((t : ℂ) - ((0:ℝ):ℂ)) * f' t‖
        + ‖∫ t in x..1, ((t : ℂ) - ((1:ℝ):ℂ)) * f' t‖ := by
        rw [key]
        exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ _ := by linarith

lemma gallagher_integral_exp_int (k : ℤ) :
    ∫ α in (0:ℝ)..1, Complex.exp (2 * π * Complex.I * (k : ℂ) * α) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hc : (2 * π * Complex.I * (k : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hk']
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * (k : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I k]; congr 1; ring
    simp [hk, h1]

lemma gallagher_exp_mul_conj_exp (m n : ℤ) (α : ℝ) :
    Complex.exp (2 * π * Complex.I * (m * α)) *
      (starRingEnd ℂ) (Complex.exp (2 * π * Complex.I * (n * α))) =
    Complex.exp (2 * π * Complex.I * (((m - n : ℤ) : ℂ)) * α) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  push_cast
  ring

/-- **Parseval for trigonometric polynomials**: `∫₀¹ |∑_{n ∈ s} a_n e(nα)|² dα = ∑_{n ∈ s} |a_n|²`
for a finite set `s` of integers, `e(x) = exp(2πix)`. -/
@[kb "davenport1980" "Ch 27, p. 157"]
theorem integral_norm_sum_exp_sq (s : Finset ℤ) (a : ℤ → ℂ) :
    ∫ α in (0:ℝ)..1, ‖∑ n ∈ s, a n * Complex.exp (2 * π * Complex.I * (n * α))‖ ^ 2 =
      ∑ n ∈ s, ‖a n‖ ^ 2 := by
  apply Complex.ofReal_injective
  have hpt : ∀ α : ℝ, (((‖∑ n ∈ s, a n * Complex.exp (2 * π * Complex.I * (n * α))‖ ^ 2 : ℝ)) : ℂ)
      = ∑ m ∈ s, ∑ n ∈ s, a m * (starRingEnd ℂ) (a n) *
          Complex.exp (2 * π * Complex.I * (((m - n : ℤ) : ℂ)) * α) := by
    intro α
    simp only [Complex.ofReal_pow]
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
    have e := gallagher_exp_mul_conj_exp m n α
    rw [map_mul]
    linear_combination (a m * (starRingEnd ℂ) (a n)) * e
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul, gallagher_integral_exp_int]
      simp [sub_eq_zero, hm]
      rw [Complex.mul_conj']
    · intro n _
      apply Continuous.intervalIntegrable
      fun_prop
  · intro m _
    apply Continuous.intervalIntegrable
    fun_prop

end NTKB.Davenport
