/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PrimeCounting
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.InvLog

/-!
# `π₁(x) = ∑_{n ≤ x} Λ(n)/log n`

**Davenport, Ch. 18, p. 112 (rows 18-4, 18-5).** By partial summation,
`π₁(x) = ψ(x)/log x + ∫_2^x ψ(t)/(t log² t) dt` for `x ≥ 2`, and hence (with 18-1)
`π₁(x) = li x + O(x exp(-c √log x))`.
-/

open Filter Topology Set MeasureTheory
open scoped Real Interval ArithmeticFunction.vonMangoldt

namespace NTKB

/-- Davenport's `π₁(x) = ∑_{n ≤ x} Λ(n)/log n` (the prime powers `p^k` counted with weight `1/k`). -/
noncomputable def primeCountingOne (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n / Real.log n

/-- **Davenport, Ch. 18, p. 112 (row 18-4)**: `π₁(x) = ψ(x)/log x + ∫_2^x ψ(t)/(t log² t) dt`. -/
@[kb "davenport1980" "Ch 18, p. 112"]
theorem Davenport.primeCountingOne_eq {x : ℝ} (hx : 2 ≤ x) :
    primeCountingOne x = Chebyshev.psi x / Real.log x +
      ∫ t in (2 : ℝ)..x, Chebyshev.psi t / (t * Real.log t ^ 2) := by
  unfold primeCountingOne
  have hd : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ (fun t : ℝ ↦ (Real.log t)⁻¹) t := by
    intro z ⟨hz, _⟩
    have : z ≠ 0 := by linarith
    have : Real.log z ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  have hi : IntegrableOn (deriv (fun t : ℝ ↦ (Real.log t)⁻¹)) (Set.Icc 2 x) := by
    refine ContinuousOn.integrableOn_Icc fun z ⟨hz, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have : z ≠ 0 := by linarith
    have : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop
  have key := sum_mul_eq_sub_integral_mul₁ (c := fun n : ℕ ↦ Λ n)
    (f := fun t : ℝ ↦ (Real.log t)⁻¹) (by simp) (by simp) x hd hi
  have e1 : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n / Real.log n =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * Λ n := by
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [div_eq_mul_inv, mul_comm]
  rw [e1, key, ← intervalIntegral.integral_of_le hx, ← Chebyshev.psi_eq_sum_Icc]
  have int_deriv :
      ∫ u in (2 : ℝ)..x, deriv (fun t : ℝ ↦ (Real.log t)⁻¹) u *
        ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, Λ k =
      ∫ u in (2 : ℝ)..x, -(Chebyshev.psi u / (u * Real.log u ^ 2)) := by
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [uIcc_of_le hx] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    rw [Real.deriv_inv_log_apply, ← Chebyshev.psi_eq_sum_Icc]
    field_simp
  rw [int_deriv, intervalIntegral.integral_neg]
  ring

/-- `t ↦ ψ(t)/(t log² t)` is integrable on `[2, x]`. -/
lemma intervalIntegrable_psi_div {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ Chebyshev.psi t / (t * Real.log t ^ 2)) volume 2 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  have h1 : IntegrableOn (fun t ↦ Chebyshev.psi t) (Icc 2 x) volume :=
    (Chebyshev.psi_mono.monotoneOn _).integrableOn_isCompact isCompact_Icc
  have h2 : ContinuousOn (fun t : ℝ ↦ 1 / (t * Real.log t ^ 2)) (Icc 2 x) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1]))
    have hd : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 hl
    have hc : ContinuousAt (fun t : ℝ ↦ t * Real.log t ^ 2) t :=
      continuousAt_id.mul ((Real.continuousAt_log ht0).pow 2)
    exact (continuousAt_const.div hc hd).continuousWithinAt
  exact (h1.mul_continuousOn h2 isCompact_Icc).congr_fun (fun t _ ↦ by simp [div_eq_mul_inv])
    measurableSet_Icc

/-- **Davenport, Ch. 18, p. 112 (row 18-5)**: `π₁(x) = li x + O(x exp(-c √log x))`. -/
@[kb "davenport1980" "Ch 18, p. 112"]
theorem Davenport.primeCountingOne_sub_logIntegral_le :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
      |primeCountingOne x - logIntegral x| ≤ K * x * Real.exp (-(c * √(Real.log x))) := by
  obtain ⟨c₀, B, hc₀, hB, hψ⟩ := Davenport.psi_sub_self_le
  set c := min c₀ 1 with hcdef
  have hc : 0 < c := lt_min hc₀ one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  have hψ' : ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.psi t - t| ≤ B * t * Real.exp (-(c * √(Real.log t))) + 2 * √t * Real.log t := by
    intro t ht
    have h1 := hψ t ht
    have h2 : Real.exp (-(c₀ * √(Real.log t))) ≤ Real.exp (-(c * √(Real.log t))) := by
      apply Real.exp_le_exp.mpr
      have := Real.sqrt_nonneg (Real.log t)
      have : c * √(Real.log t) ≤ c₀ * √(Real.log t) := by gcongr; exact min_le_left _ _
      linarith
    have h3 : 0 ≤ 2 * √t * Real.log t := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ t); positivity
    have h4 : B * t * Real.exp (-(c₀ * √(Real.log t))) ≤ B * t * Real.exp (-(c * √(Real.log t))) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  refine ⟨c / 2, 20 * B + 200, by positivity, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  set L2 := Real.log 2 with hL2def
  have hL2 : 2 / 3 < L2 := log_two_gt_two_thirds
  have hL2' : L2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlx : L2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hlx0 : 0 < Real.log x := by linarith
  set E := Real.exp (-(c / 2 * √(Real.log x))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- the identity
  have hπ := Davenport.primeCountingOne_eq hx
  have hli := logIntegral_eq hx
  have hI1 := intervalIntegrable_psi_div hx
  have hI2 : IntervalIntegrable (fun t : ℝ ↦ 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hdiff : (∫ t in (2 : ℝ)..x, Chebyshev.psi t / (t * Real.log t ^ 2)) -
      ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 =
      ∫ t in (2 : ℝ)..x, (Chebyshev.psi t - t) / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_sub hI1 hI2]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    field_simp
  have hid : primeCountingOne x - logIntegral x =
      (Chebyshev.psi x - x) / Real.log x + 2 / L2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.psi t - t) / (t * Real.log t ^ 2) := by
    rw [hπ, hli, ← hdiff, sub_div]; ring
  rw [hid]
  -- the bounds, as for `π(x)`
  have hcE : Real.exp (-(c * √(Real.log x))) ≤ E := by
    apply Real.exp_le_exp.mpr
    have := Real.sqrt_nonneg (Real.log x)
    nlinarith
  have haE : Real.exp (-(c * √(Real.log x / 2))) ≤ E := by
    apply Real.exp_le_exp.mpr
    have h1 : √(Real.log x) / 2 ≤ √(Real.log x / 2) := by
      rw [Real.le_sqrt (by positivity) (by positivity), div_pow, Real.sq_sqrt hlx0.le]
      nlinarith
    nlinarith
  have hsl := sqrt_mul_log_le (c := c / 2) (by positivity) (by linarith) (x := x) (by linarith)
  rw [← hE] at hsl
  have h1E := one_le_mul_exp_neg_sqrt_log (c := c / 2) (by positivity) (by linarith) hx
  rw [← hE] at h1E
  have hxE : 0 ≤ x * E := by positivity
  have b1 : |(Chebyshev.psi x - x) / Real.log x| ≤ (B + 12) / L2 * (x * E) := by
    rw [abs_div, abs_of_pos hlx0, div_le_iff₀ hlx0]
    have h := hψ' x hx
    have h2 : B * x * Real.exp (-(c * √(Real.log x))) ≤ B * (x * E) := by
      calc B * x * Real.exp (-(c * √(Real.log x))) ≤ B * x * E := by gcongr
        _ = B * (x * E) := by ring
    have h3 : (B + 12) * (x * E) ≤ (B + 12) / L2 * (x * E) * Real.log x := by
      have e : (B + 12) / L2 * (x * E) * Real.log x = (B + 12) * (x * E) * (Real.log x / L2) := by
        ring
      rw [e]
      have h1 : 1 ≤ Real.log x / L2 := by rw [le_div_iff₀ (by linarith)]; linarith
      have h0 : 0 ≤ (B + 12) * (x * E) := by positivity
      have := mul_le_mul_of_nonneg_left h1 h0
      linarith
    linarith
  have b3 := norm_integral_theta_sub_le hc hB hψ' hx
  have hL2sq : 4 / 9 ≤ L2 ^ 2 := by nlinarith
  have b3' : |∫ t in (2 : ℝ)..x, (Chebyshev.psi t - t) / (t * Real.log t ^ 2)| ≤
      (B / L2 ^ 2 * 7 + 4 / L2 * 6 / L2) * (x * E) := by
    refine b3.trans ?_
    have hB0 : 0 ≤ B / L2 ^ 2 := by positivity
    have h1 : Real.exp (-(c * √(Real.log x / 2))) * x + √x * Real.log x ≤ 7 * (x * E) := by
      have : Real.exp (-(c * √(Real.log x / 2))) * x ≤ E * x := by gcongr
      nlinarith
    have hsx : √x ≤ √x * Real.log x / L2 := by
      rw [le_div_iff₀ (by linarith)]
      have := Real.sqrt_nonneg x
      nlinarith
    have h2 : 4 / L2 * √x ≤ 4 / L2 * 6 / L2 * (x * E) := by
      have : 0 ≤ 4 / L2 := by positivity
      calc 4 / L2 * √x ≤ 4 / L2 * (√x * Real.log x / L2) := by gcongr
        _ ≤ 4 / L2 * (6 * (x * E) / L2) := by gcongr
        _ = 4 / L2 * 6 / L2 * (x * E) := by ring
    calc B / L2 ^ 2 * (Real.exp (-(c * √(Real.log x / 2))) * x + √x * Real.log x) +
          4 / L2 * √x ≤ B / L2 ^ 2 * (7 * (x * E)) + 4 / L2 * 6 / L2 * (x * E) := by gcongr
      _ = (B / L2 ^ 2 * 7 + 4 / L2 * 6 / L2) * (x * E) := by ring
  have hi1 : 1 / L2 ≤ 3 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hi2 : 1 / L2 ^ 2 ≤ 9 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
  have c1 : (B + 12) / L2 ≤ (B + 12) * (3 / 2) := by
    rw [div_eq_mul_one_div]; gcongr
  have c2 : B / L2 ^ 2 * 7 + 4 / L2 * 6 / L2 ≤ B * (9 / 4) * 7 + 24 * (9 / 4) := by
    have e : 4 / L2 * 6 / L2 = 24 * (1 / L2 ^ 2) := by field_simp; ring
    rw [e, div_eq_mul_one_div B]
    gcongr
  have c3 : 2 / L2 ≤ 3 * (x * E) := by
    have : 2 / L2 ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  calc |(Chebyshev.psi x - x) / Real.log x + 2 / L2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.psi t - t) / (t * Real.log t ^ 2)|
      ≤ |(Chebyshev.psi x - x) / Real.log x| + |2 / L2| +
          |∫ t in (2 : ℝ)..x, (Chebyshev.psi t - t) / (t * Real.log t ^ 2)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (B + 12) * (3 / 2) * (x * E) + 3 * (x * E) + (B * (9 / 4) * 7 + 24 * (9 / 4)) * (x * E) := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / L2)]
        gcongr ?_ + ?_ + ?_
        all_goals first
          | exact b1.trans (by gcongr)
          | exact b3'.trans (by gcongr)
    _ ≤ (20 * B + 200) * x * E := by
        have : 0 ≤ B * (x * E) := by positivity
        have e : (20 * B + 200) * x * E = 20 * (B * (x * E)) + 200 * (x * E) := by ring
        rw [e]
        nlinarith

end NTKB
