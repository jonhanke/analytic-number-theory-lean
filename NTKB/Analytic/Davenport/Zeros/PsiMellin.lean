/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PNT
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# `-ζ'/ζ(s) = s/(s - 1) + s ∫_1^∞ (ψ(x) - x) x^{-s-1} dx`

**Davenport, Ch. 18, p. 113 (row 18-12)**, for `σ > 1`, by partial summation (Mathlib's
`LSeries_eq_mul_integral_of_nonneg`) and `∫_1^∞ x^{-s} dx = 1/(s - 1)`.
-/

open Filter Topology Complex Set MeasureTheory Asymptotics
open scoped Real ArithmeticFunction.vonMangoldt LSeries.notation

namespace NTKB

/-- `∑_{1 ≤ k ≤ ⌊t⌋} Λ(k) = ψ(t)`. -/
lemma sum_Icc_vonMangoldt_eq_psi (t : ℝ) :
    ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, Λ k = Chebyshev.psi t := by
  rw [Chebyshev.psi]
  rfl

/-- `t ↦ ψ(t) t^{-(s+1)}` is integrable on `(1, ∞)` for `σ > 1`. -/
lemma integrableOn_psi_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  set C := Real.log 4 + 4
  have hC : 0 ≤ C := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  have hg : IntegrableOn (fun t : ℝ ↦ C * t ^ (-s.re)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul C
  refine hg.mono' ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp
        Chebyshev.psi_mono.measurable).aestronglyMeasurable
    · refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
      exact ((Complex.continuous_ofReal.continuousAt (x := t)).cpow continuousAt_const
        (Or.inl (by simpa using ht0))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg t),
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have h1 := Chebyshev.psi_le_const_mul_self ht0.le
    have e : t ^ (-(s + 1)).re = t ^ (-s.re) / t := by
      simp only [neg_re, add_re, one_re]
      rw [show -(s.re + 1) = -s.re - 1 by ring, Real.rpow_sub ht0, Real.rpow_one]
    rw [e]
    calc Chebyshev.psi t * (t ^ (-s.re) / t) ≤ (C * t) * (t ^ (-s.re) / t) := by
          gcongr
      _ = C * t ^ (-s.re) := by field_simp

/-- **Davenport, Ch. 18, p. 113 (row 18-12)**: for `σ > 1`,
`-ζ'(s)/ζ(s) = s/(s - 1) + s ∫_1^∞ (ψ(x) - x) x^{-s-1} dx`. -/
@[kb "davenport1980" "Ch 18, p. 113"]
theorem Davenport.neg_logDeriv_riemannZeta_eq_integral {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      s / (s - 1) + s * ∫ t in Ioi (1 : ℝ), ((Chebyshev.psi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hs1 : s - 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h; simp at this; linarith
  -- partial summation
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, Λ k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n ↦ ?_)
    have h := Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) n.cast_nonneg
    rw [← sum_Icc_vonMangoldt_eq_psi, Nat.floor_natCast] at h
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ ↦
      ArithmeticFunction.vonMangoldt_nonneg), Real.rpow_one, abs_of_nonneg n.cast_nonneg]
    exact h
  have hL := LSeries_eq_mul_integral_of_nonneg (fun n ↦ Λ n) zero_le_one hs hO
    (fun n ↦ ArithmeticFunction.vonMangoldt_nonneg)
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  have hL' : L ↗Λ s = LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) s := rfl
  rw [hL', hL]
  -- split the integral
  have hψ : ∀ t : ℝ, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ((Λ k : ℝ) : ℂ)) = (Chebyshev.psi t : ℂ) := by
    intro t; rw [← sum_Icc_vonMangoldt_eq_psi]; push_cast; rfl
  simp_rw [hψ]
  have hI1 := integrableOn_psi_mul_cpow hs
  have hI2 : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) one_pos
  have hI2' : IntegrableOn (fun t : ℝ ↦ (t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    refine hI2.congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (lt_trans one_pos ht).ne'
    show (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1))
    rw [show -s = 1 + -(s + 1) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]
  have hsplit : ∫ t in Ioi (1 : ℝ), ((Chebyshev.psi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1))) -
        ∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← integral_sub hI1 hI2']
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    push_cast; ring
  have hint : ∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = 1 / (s - 1) := by
    have h1 : ∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (lt_trans one_pos ht).ne'
      rw [show -s = 1 + -(s + 1) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]
    rw [h1, integral_Ioi_cpow_of_lt (by simp; linarith) one_pos]
    simp only [Complex.ofReal_one, Complex.one_cpow]
    have : -s + 1 ≠ 0 := fun h ↦ hs1 (by linear_combination -h)
    field_simp
    ring
  rw [hsplit, hint]
  field_simp
  ring

end NTKB
