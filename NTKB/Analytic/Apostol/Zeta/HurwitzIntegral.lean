/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import NTKB.Analytic.Apostol.Zeta.HurwitzEuler

/-!
# The integral representation of `Γ(s) ζ(s, a)` (Apostol, Theorem 12.2)

For `σ > 1` and `0 < a ≤ 1`: `Γ(s) ζ(s, a) = ∫_0^∞ x^{s-1} e^{-ax}/(1 - e^{-x}) dx`.
Proof as in Apostol: `∫_0^∞ e^{-(n+a)x} x^{s-1} dx = Γ(s) (n+a)^{-s}`, sum over `n ≥ 0` (the
interchange of sum and integral is justified by absolute convergence).
-/

open Complex Filter Topology Finset MeasureTheory Set HurwitzZeta

namespace NTKB.Apostol

/-- `x^{s-1} e^{-rx}` is integrable on `(0, ∞)` for `σ > 0`, `r > 0`. -/
lemma integrableOn_cpow_mul_exp_neg {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) * cexp (-((r : ℂ) * x))) (Ioi 0) := by
  have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re - 1) (p := 1) (b := r)
    (by linarith) one_pos hr
  refine hreal.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ (by fun_prop)
    refine ContinuousOn.cpow_const (by fun_prop) fun x hx ↦ ofReal_mem_slitPlane.2 hx
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx ↦ ?_)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, Real.rpow_one]
    simp only [sub_re, one_re]
    rw [show -((r : ℂ) * x) = ((-(r * x) : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
    simp

lemma integral_norm_cpow_mul_exp_neg {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    ∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (s - 1) * cexp (-((r : ℂ) * x))‖ =
      (1 / r) ^ s.re * Real.Gamma s.re := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  simp only [sub_re, one_re]
  rw [show -((r : ℂ) * x) = ((-(r * x) : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]

/-- **Apostol, Theorem 12.2**: for `σ > 1`, `0 < a ≤ 1`,
`Γ(s) ζ(s, a) = ∫_0^∞ x^{s-1} e^{-ax}/(1 - e^{-x}) dx`. -/
@[kb "apostol1976" "Thm 12.2, p. 251"]
theorem apostol_thm_12_2 {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Gamma s * hurwitzZeta a s =
      ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
        ((Real.exp (-(a * x)) / (1 - Real.exp (-x)) : ℝ) : ℂ) := by
  have hs0 : 0 < s.re := by linarith
  set F : ℕ → ℝ → ℂ := fun n x ↦ (x : ℂ) ^ (s - 1) * cexp (-(((n + a : ℝ) : ℂ) * x))
  have hint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := fun n ↦
    integrableOn_cpow_mul_exp_neg hs0 (by positivity)
  have hnorm : ∀ n : ℕ, ∫ x in Ioi 0, ‖F n x‖ = Real.Gamma s.re * ((0 + n + a : ℝ)) ^ (-s.re) := by
    intro n
    rw [integral_norm_cpow_mul_exp_neg hs0 (by positivity), one_div,
      Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), zero_add, mul_comm]
  have hsum : Summable fun n : ℕ ↦ ∫ x in Ioi 0, ‖F n x‖ := by
    simp_rw [hnorm]
    exact (summable_shift_rpow ha0 0 (by linarith)).mul_left _
  have key := integral_tsum_of_summable_integral_norm hint hsum
  -- the integrals
  have hval : ∀ n : ℕ, ∫ x in Ioi 0, F n x = Gamma s * (1 / ((n : ℂ) + a) ^ s) := by
    intro n
    have hr : (0 : ℝ) < n + a := by positivity
    rw [integral_cpow_mul_exp_neg_mul_Ioi hs0 hr, mul_comm]
    congr 1
    have h1 : ((1 / (n + a : ℝ) : ℝ) : ℂ) ^ s * (((n + a : ℝ) : ℂ)) ^ s = 1 := by
      rw [← mul_cpow_ofReal_nonneg (by positivity) hr.le, ← ofReal_mul, one_div,
        inv_mul_cancel₀ hr.ne', ofReal_one, one_cpow]
    have h2 : (((n + a : ℝ)) : ℂ) ^ s ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; push_cast; intro h; exact absurd h.1 (by exact_mod_cast hr.ne')
    push_cast at h1 h2 ⊢
    rw [eq_div_iff h2, h1]
  have hz := (hasSum_hurwitzZeta_of_one_lt_re ⟨ha0.le, ha1⟩ hs).tsum_eq
  rw [← hz, ← tsum_mul_left]
  simp_rw [← hval]
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  simp only [F]
  rw [tsum_mul_left]
  congr 1
  -- the geometric series
  have hq : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by simpa using hx)
  have hg := hasSum_geometric_of_lt_one (Real.exp_pos (-x)).le hq
  have hg' := (hg.mul_left (Real.exp (-(a * x)))).map ofRealCLM ofRealCLM.continuous
  rw [div_eq_mul_inv, show (((Real.exp (-(a * x)) * (1 - Real.exp (-x))⁻¹ : ℝ)) : ℂ) =
    ofRealCLM (Real.exp (-(a * x)) * (1 - Real.exp (-x))⁻¹) from rfl, ← hg'.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp only [Function.comp, ofRealCLM_apply]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  push_cast
  congr 1
  ring

end NTKB.Apostol
