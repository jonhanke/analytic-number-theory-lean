/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PrimeCounting
import NTKB.Analytic.Davenport.Zeros.PNTConditional

/-!
# `π(x) = li x + O(√x log x)` under the Riemann hypothesis

**Davenport, Ch. 18, p. 113 (row 18-9).** From von Koch's `ψ(x) = x + O(√x log² x)` (18-8) by the
same partial summation as for 18-6.
-/

open Filter Topology Set MeasureTheory
open scoped Real Interval

namespace NTKB

/-- **Davenport, Ch. 18, p. 113 (row 18-9)**: under the Riemann hypothesis,
`|π(x) - li x| ≤ K √x log x` for `x ≥ 2`. -/
@[kb "davenport1980" "Ch 18, p. 113"]
theorem Davenport.primeCounting_sub_logIntegral_le_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x| ≤ K * √x * Real.log x := by
  obtain ⟨C, hC, hψ⟩ := Davenport.psi_sub_self_le_of_riemannHypothesis hRH
  set L2 := Real.log 2 with hL2def
  have hL2 : 2 / 3 < L2 := log_two_gt_two_thirds
  have hL2' : L2 < 1 := by have := Real.log_two_lt_d9; linarith
  -- `|θ(t) - t| ≤ (C + 3) √t log² t`
  have hθ : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| ≤ (C + 3) * √t * Real.log t ^ 2 := by
    intro t ht
    have h1 := hψ t ht
    have h2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := t) (by linarith)
    have hlt : L2 ≤ Real.log t := Real.log_le_log two_pos ht
    have hs : t ^ (1 / 2 : ℝ) = √t := (Real.sqrt_eq_rpow t).symm
    rw [hs] at h1
    have hst : 0 ≤ √t := Real.sqrt_nonneg t
    have h3 : 2 * √t * Real.log t ≤ 3 * √t * Real.log t ^ 2 := by
      have : 2 ≤ 3 * Real.log t := by linarith
      have h0 : 0 ≤ √t * Real.log t := mul_nonneg hst (by linarith)
      nlinarith
    calc |Chebyshev.theta t - t| ≤ |Chebyshev.psi t - t| + |Chebyshev.psi t - Chebyshev.theta t| := by
          have := abs_sub_le (Chebyshev.theta t) (Chebyshev.psi t) t
          rw [abs_sub_comm (Chebyshev.theta t) (Chebyshev.psi t)] at this
          linarith
      _ ≤ C * √t * Real.log t ^ 2 + 3 * √t * Real.log t ^ 2 := by linarith
      _ = (C + 3) * √t * Real.log t ^ 2 := by ring
  refine ⟨5 * (C + 3) + 10, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : L2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hlx0 : 0 < Real.log x := by linarith
  have hsx0 : 0 < √x := Real.sqrt_pos.mpr hx0
  have hsx1 : 1 ≤ √x := Real.one_le_sqrt.mpr (by linarith)
  -- the identity (as for 18-6)
  have hπ := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  have hli := logIntegral_eq hx
  have hI1 : IntervalIntegrable (fun t ↦ Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hI2 : IntervalIntegrable (fun t : ℝ ↦ 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hdiff : (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
      ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 =
      ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_sub hI1 hI2]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    field_simp
  have hid : (Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x =
      (Chebyshev.theta x - x) / Real.log x + 2 / L2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
    rw [hπ, hli, ← hdiff, sub_div]; ring
  rw [hid]
  -- the integral: the integrand is at most `(C + 3) t^{-1/2}`
  have hpt : ∀ t ∈ Ioc (2 : ℝ) x, ‖(Chebyshev.theta t - t) / (t * Real.log t ^ 2)‖ ≤
      (C + 3) * t ^ (-(1 / 2) : ℝ) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hden : 0 < t * Real.log t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have hrt : t ^ (-(1 / 2) : ℝ) * t = √t := by
      have := Real.rpow_add ht0 (-(1 / 2) : ℝ) 1
      rw [Real.rpow_one] at this
      rw [← this, Real.sqrt_eq_rpow]; norm_num
    have e : (C + 3) * t ^ (-(1 / 2) : ℝ) * (t * Real.log t ^ 2) =
        (C + 3) * (t ^ (-(1 / 2) : ℝ) * t) * Real.log t ^ 2 := by ring
    rw [e, hrt]
    exact hθ t ht.1.le
  have hgint : IntervalIntegrable (fun t : ℝ ↦ (C + 3) * t ^ (-(1 / 2) : ℝ)) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl ht0))).continuousWithinAt
  have hI := intervalIntegral.norm_integral_le_of_norm_le hx (Eventually.of_forall hpt) hgint
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    at hI
  have hsx : x ^ (-(1 / 2) + 1 : ℝ) = √x := by rw [Real.sqrt_eq_rpow]; norm_num
  rw [hsx] at hI
  have h2 : (0 : ℝ) ≤ 2 ^ (-(1 / 2) + 1 : ℝ) := by positivity
  have hb3 : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      2 * (C + 3) * √x := by
    refine hI.trans ?_
    have : (√x - 2 ^ (-(1 / 2) + 1 : ℝ)) / (-(1 / 2) + 1) ≤ 2 * √x := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    calc (C + 3) * ((√x - 2 ^ (-(1 / 2) + 1 : ℝ)) / (-(1 / 2) + 1)) ≤ (C + 3) * (2 * √x) := by
          gcongr
      _ = 2 * (C + 3) * √x := by ring
  -- the first term
  have hb1 : |(Chebyshev.theta x - x) / Real.log x| ≤ (C + 3) * √x * Real.log x := by
    rw [abs_div, abs_of_pos hlx0, div_le_iff₀ hlx0]
    have := hθ x hx
    calc |Chebyshev.theta x - x| ≤ (C + 3) * √x * Real.log x ^ 2 := this
      _ = (C + 3) * √x * Real.log x * Real.log x := by ring
  have hb2 : |2 / L2| ≤ 3 := by
    rw [abs_of_pos (by positivity)]; rw [div_le_iff₀ (by linarith)]; linarith
  -- assemble, with `√x ≤ √x log x / L2` and `1 ≤ √x log x / L2`
  have hW : √x ≤ 2 * (√x * Real.log x) := by
    have : 1 / 2 ≤ Real.log x := by linarith
    nlinarith
  have hW1 : 1 ≤ 2 * (√x * Real.log x) := by nlinarith
  calc |(Chebyshev.theta x - x) / Real.log x + 2 / L2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)|
      ≤ |(Chebyshev.theta x - x) / Real.log x| + |2 / L2| +
          |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (C + 3) * √x * Real.log x + 3 + 2 * (C + 3) * √x := add_le_add (add_le_add hb1 hb2) hb3
    _ ≤ (5 * (C + 3) + 10) * √x * Real.log x := by
        have hC3 : 0 ≤ C + 3 := by linarith
        have h1 := mul_le_mul_of_nonneg_left hW (by positivity : (0 : ℝ) ≤ 2 * (C + 3))
        have e : (5 * (C + 3) + 10) * √x * Real.log x =
            5 * (C + 3) * (√x * Real.log x) + 10 * (√x * Real.log x) := by ring
        rw [e]
        have e2 : (C + 3) * √x * Real.log x = (C + 3) * (√x * Real.log x) := by ring
        rw [e2]
        have e3 : 2 * (C + 3) * √x = 2 * (C + 3) * √x := rfl
        nlinarith

end NTKB
