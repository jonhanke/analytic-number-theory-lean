/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PNT

/-!
# `π(x) = li x + O(x exp(-c √log x))`

**Davenport, Ch. 18, pp. 112-113 (rows 18-4, 18-5, 18-6).** From `ψ(x) = x + O(x exp(-c√log x))`
(18-1): `θ(x) = ψ(x) + O(√x log x)`, and partial summation
`π(x) = θ(x)/log x + ∫_2^x θ(t)/(t log² t) dt` (Mathlib,
`Chebyshev.primeCounting_eq_theta_div_log_add_integral`); with
`li x = ∫_2^x dt/log t = x/log x - 2/log 2 + ∫_2^x dt/log² t` this gives the prime number theorem
with de la Vallée Poussin's error term. (Davenport passes through `π₁(x) = ∑ Λ(n)/log n`; we pass
through `θ`, which is equivalent: both differ from `ψ`, resp. `π`, by `O(√x log x)`.)
-/

open Filter Topology Set MeasureTheory
open scoped Real Interval

namespace NTKB

/-- The logarithmic integral `li x = ∫_2^x dt / log t` (Davenport's normalization, Ch. 18). -/
noncomputable def logIntegral (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

lemma continuousOn_one_div_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ ↦ 1 / Real.log t) [[a, b]] := by
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  exact (continuousAt_const.div (Real.continuousAt_log ht0) hl).continuousWithinAt

/-- Integration by parts: `li x = x/log x - 2/log 2 + ∫_2^x dt/log² t`. -/
lemma logIntegral_eq {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x = x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hd : ∀ t ∈ [[(2 : ℝ), x]], HasDerivAt (fun t : ℝ ↦ t / Real.log t)
      (1 / Real.log t - 1 / Real.log t ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have := (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hl
    convert this using 1
    field_simp
  have hi1 : IntervalIntegrable (fun t : ℝ ↦ 1 / Real.log t) volume 2 x :=
    (continuousOn_one_div_log (by norm_num) hx).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ 1 / Real.log t ^ 2) volume 2 x := by
    have := Chebyshev.intervalIntegrable_one_div_log_sq (a := 2) (b := x) (by norm_num)
      (by linarith)
    exact this
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2] at hFTC
  unfold logIntegral
  linarith

/-- `√x log x ≤ 6 x exp(-c √log x)` for `0 < c ≤ 1/2`, `x ≥ 1`. -/
lemma sqrt_mul_log_le {c x : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2) (hx : 1 ≤ x) :
    √x * Real.log x ≤ 6 * (x * Real.exp (-(c * √(Real.log x)))) := by
  have hx0 : 0 < x := by linarith
  set v := Real.log x with hv
  have hv0 : 0 ≤ v := Real.log_nonneg hx
  have hxv : x = Real.exp v := (Real.exp_log hx0).symm
  have hsx : √x = Real.exp (v / 2) := by
    rw [hxv, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le,
      ← Real.exp_add]; ring_nf
  have hs := Real.sqrt_nonneg v
  have hs2 := Real.sq_sqrt hv0
  -- `c √v ≤ (1 + v)/4`
  have h1 : c * √v ≤ (1 + v) / 4 := by
    nlinarith [sq_nonneg (√v - 1), mul_le_mul_of_nonneg_right hc1 hs]
  -- `v ≤ 4 e^{v/4}`
  have h2 : v ≤ 4 * Real.exp (v / 4) := by
    have := Real.add_one_le_exp (v / 4); linarith
  have h3 : Real.exp (1 / 4) ≤ 1.5 := by
    have := Real.exp_bound' (x := 1 / 4) (by norm_num) (by norm_num) (n := 2) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  rw [hsx, hxv]
  -- `e^{v/2} v ≤ 4 e^{v/4} e^{v/2} = 4 e^{1/4} e^{v} e^{-(1+v)/4} ≤ 6 e^{v} e^{-c√v}`
  have h4 : Real.exp (v / 2) * v ≤ Real.exp (v / 2) * (4 * Real.exp (v / 4)) := by gcongr
  have h5 : Real.exp (v / 2) * (4 * Real.exp (v / 4)) =
      4 * Real.exp (1 / 4) * (Real.exp v * Real.exp (-((1 + v) / 4))) := by
    calc Real.exp (v / 2) * (4 * Real.exp (v / 4)) = 4 * Real.exp (v / 2 + v / 4) := by
          rw [Real.exp_add]; ring
      _ = 4 * Real.exp (1 / 4 + (v + -((1 + v) / 4))) := by congr 2; ring
      _ = _ := by rw [Real.exp_add, Real.exp_add]; ring
  have h6 : Real.exp v * Real.exp (-((1 + v) / 4)) ≤ Real.exp v * Real.exp (-(c * √v)) := by
    gcongr
  have h7 : 0 ≤ Real.exp v * Real.exp (-(c * √v)) := by positivity
  rw [h5] at h4
  have h8 : 4 * Real.exp (1 / 4) * (Real.exp v * Real.exp (-((1 + v) / 4))) ≤
      4 * Real.exp (1 / 4) * (Real.exp v * Real.exp (-(c * √v))) := by
    gcongr
  nlinarith

/-- `1 ≤ x exp(-c √log x)` for `0 < c ≤ 1/2`, `x ≥ 2`. -/
lemma one_le_mul_exp_neg_sqrt_log {c x : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2) (hx : 2 ≤ x) :
    1 ≤ x * Real.exp (-(c * √(Real.log x))) := by
  have hx0 : 0 < x := by linarith
  have hv : 2 / 3 < Real.log x := log_two_gt_two_thirds.trans_le (Real.log_le_log two_pos hx)
  have hs := Real.sqrt_nonneg (Real.log x)
  have hs2 := Real.sq_sqrt (show 0 ≤ Real.log x by linarith)
  have h : c * √(Real.log x) ≤ Real.log x := by nlinarith
  calc (1 : ℝ) ≤ Real.exp (Real.log x - c * √(Real.log x)) := Real.one_le_exp (by linarith)
    _ = x * Real.exp (-(c * √(Real.log x))) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hx0]

/-- `|θ(t) - t| ≤ B t exp(-c √log t) + 2 √t log t` for `t ≥ 2`, with `0 < c ≤ 1`. -/
lemma theta_sub_self_le :
    ∃ c B : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < B ∧ ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.theta t - t| ≤ B * t * Real.exp (-(c * √(Real.log t))) + 2 * √t * Real.log t := by
  obtain ⟨c, C, hc, hC, h⟩ := Davenport.psi_sub_self_le
  refine ⟨min c 1, C, lt_min hc one_pos, min_le_right _ _, hC, fun t ht ↦ ?_⟩
  have h1 := h t ht
  have h2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := t) (by linarith)
  have h3 : Real.exp (-(c * √(Real.log t))) ≤ Real.exp (-(min c 1 * √(Real.log t))) := by
    apply Real.exp_le_exp.mpr
    have := Real.sqrt_nonneg (Real.log t)
    have : min c 1 * √(Real.log t) ≤ c * √(Real.log t) := by gcongr; exact min_le_left _ _
    linarith
  have h4 : C * t * Real.exp (-(c * √(Real.log t))) ≤ C * t * Real.exp (-(min c 1 * √(Real.log t))) := by
    have : 0 ≤ C * t := by positivity
    exact mul_le_mul_of_nonneg_left h3 this
  calc |Chebyshev.theta t - t| ≤ |Chebyshev.psi t - t| + |Chebyshev.psi t - Chebyshev.theta t| := by
        have := abs_sub_le (Chebyshev.theta t) (Chebyshev.psi t) t
        rw [abs_sub_comm (Chebyshev.theta t) (Chebyshev.psi t)] at this
        linarith
    _ ≤ _ := by linarith

/-- `exp(-c √log t) ≤ exp(-c √(log x / 2)) + √x / t` for `2 ≤ t ≤ x`. -/
lemma exp_neg_sqrt_log_le_split {c t x : ℝ} (hc : 0 < c) (ht : 2 ≤ t) (htx : t ≤ x) :
    Real.exp (-(c * √(Real.log t))) ≤ Real.exp (-(c * √(Real.log x / 2))) + √x / t := by
  have ht0 : 0 < t := by linarith
  rcases le_or_gt (√x) t with h | h
  · have hl : Real.log x / 2 ≤ Real.log t := by
      have h1 : Real.log (√x) ≤ Real.log t := Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) h
      rwa [Real.log_sqrt (by linarith)] at h1
    have : Real.exp (-(c * √(Real.log t))) ≤ Real.exp (-(c * √(Real.log x / 2))) := by
      apply Real.exp_le_exp.mpr
      have := Real.sqrt_le_sqrt hl
      nlinarith
    have : 0 ≤ √x / t := by positivity
    linarith
  · have h1 : Real.exp (-(c * √(Real.log t))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have := Real.sqrt_nonneg (Real.log t)
      nlinarith
    have h2 : 1 ≤ √x / t := by rw [le_div_iff₀ ht0]; linarith
    have := Real.exp_pos (-(c * √(Real.log x / 2)))
    linarith

/-- The integral `∫_2^x (F(t) - t)/(t log² t) dt` (`F = θ` or `ψ`), given `|θ(t) - t| ≤ B t e^{-c√log t} + 2√t log t`. -/
lemma norm_integral_theta_sub_le {F : ℝ → ℝ} {c B : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hθ : ∀ t : ℝ, 2 ≤ t →
      |F t - t| ≤ B * t * Real.exp (-(c * √(Real.log t))) + 2 * √t * Real.log t)
    {x : ℝ} (hx : 2 ≤ x) :
    |∫ t in (2 : ℝ)..x, (F t - t) / (t * Real.log t ^ 2)| ≤
      B / Real.log 2 ^ 2 * (Real.exp (-(c * √(Real.log x / 2))) * x + √x * Real.log x) +
        4 / Real.log 2 * √x := by
  set L2 := Real.log 2
  have hL2 : 2 / 3 < L2 := log_two_gt_two_thirds
  set a := Real.exp (-(c * √(Real.log x / 2)))
  have ha0 : 0 < a := Real.exp_pos _
  set g : ℝ → ℝ := fun t ↦ B / L2 ^ 2 * (a + √x * t⁻¹) + 2 / L2 * t ^ (-(1 / 2) : ℝ)
  have hpt : ∀ t ∈ Ioc (2 : ℝ) x,
      ‖(F t - t) / (t * Real.log t ^ 2)‖ ≤ g t := by
    intro t ht
    have ht2 : 2 ≤ t := ht.1.le
    have ht0 : 0 < t := by linarith
    have hlt : L2 ≤ Real.log t := Real.log_le_log two_pos ht2
    have hlt0 : 0 < Real.log t := by linarith
    have hden : 0 < t * Real.log t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have h1 := hθ t ht2
    have hsplit := exp_neg_sqrt_log_le_split hc ht2 ht.2
    have hst : √t * √t = t := Real.mul_self_sqrt ht0.le
    have hst0 : 0 < √t := Real.sqrt_pos.mpr ht0
    have hrp : t ^ (-(1 / 2) : ℝ) * √t = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]; norm_num
    -- the two parts
    have p1 : B * t * Real.exp (-(c * √(Real.log t))) ≤
        B / L2 ^ 2 * (a + √x * t⁻¹) * (t * Real.log t ^ 2) := by
      have e1 : B / L2 ^ 2 * (a + √x * t⁻¹) * (t * Real.log t ^ 2) =
          B * t * (a + √x / t) * (Real.log t ^ 2 / L2 ^ 2) := by
        field_simp
      rw [e1]
      have hq : 1 ≤ Real.log t ^ 2 / L2 ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have hBt : 0 ≤ B * t := by positivity
      calc B * t * Real.exp (-(c * √(Real.log t))) ≤ B * t * (a + √x / t) := by gcongr
        _ = B * t * (a + √x / t) * 1 := by ring
        _ ≤ B * t * (a + √x / t) * (Real.log t ^ 2 / L2 ^ 2) := by
            gcongr
    have p2 : 2 * √t * Real.log t ≤ 2 / L2 * t ^ (-(1 / 2) : ℝ) * (t * Real.log t ^ 2) := by
      have hrt : t ^ (-(1 / 2) : ℝ) * t = √t := by
        have := Real.rpow_add ht0 (-(1 / 2) : ℝ) 1
        rw [Real.rpow_one] at this
        rw [← this, Real.sqrt_eq_rpow]; norm_num
      have e2 : 2 / L2 * t ^ (-(1 / 2) : ℝ) * (t * Real.log t ^ 2) =
          2 * √t * Real.log t * (Real.log t / L2) := by
        calc 2 / L2 * t ^ (-(1 / 2) : ℝ) * (t * Real.log t ^ 2)
            = 2 / L2 * (t ^ (-(1 / 2) : ℝ) * t) * Real.log t ^ 2 := by ring
          _ = 2 * √t * Real.log t * (Real.log t / L2) := by rw [hrt]; ring
      rw [e2]
      have hq : 1 ≤ Real.log t / L2 := by rw [le_div_iff₀ (by positivity)]; linarith
      have : 0 ≤ 2 * √t * Real.log t := by positivity
      nlinarith
    have : g t * (t * Real.log t ^ 2) = B / L2 ^ 2 * (a + √x * t⁻¹) * (t * Real.log t ^ 2) +
        2 / L2 * t ^ (-(1 / 2) : ℝ) * (t * Real.log t ^ 2) := by simp only [g]; ring
    rw [this]
    linarith
  have hgint : IntervalIntegrable g volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    refine ContinuousAt.continuousWithinAt ?_
    simp only [g]
    exact (continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul
      (continuousAt_inv₀ ht0)))).add (continuousAt_const.mul
        (Real.continuousAt_rpow_const _ _ (Or.inl ht0)))
  have hI := intervalIntegral.norm_integral_le_of_norm_le hx (Eventually.of_forall hpt) hgint
  rw [Real.norm_eq_abs] at hI
  refine hI.trans ?_
  -- compute `∫ g`
  have hx0 : 0 < x := by linarith
  have i1 : IntervalIntegrable (fun t : ℝ ↦ B / L2 ^ 2 * (a + √x * t⁻¹)) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul
      (continuousAt_inv₀ ht0)))).continuousWithinAt
  have i2 : IntervalIntegrable (fun t : ℝ ↦ 2 / L2 * t ^ (-(1 / 2) : ℝ)) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl ht0))).continuousWithinAt
  have i3 : IntervalIntegrable (fun t : ℝ ↦ √x * t⁻¹) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (continuousAt_inv₀ ht0)).continuousWithinAt
  have hg : ∫ t in (2 : ℝ)..x, g t = B / L2 ^ 2 * ((x - 2) * a + √x * Real.log (x / 2)) +
      2 / L2 * ((x ^ (1 / 2 : ℝ) - 2 ^ (1 / 2 : ℝ)) / (1 / 2)) := by
    simp only [g]
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const i3,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_inv_of_pos two_pos hx0, integral_rpow (Or.inl (by norm_num))]
    norm_num
  rw [hg]
  have hlog : Real.log (x / 2) ≤ Real.log x := Real.log_le_log (by positivity) (by linarith)
  have hsx : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm
  have h2 : (0 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) := by positivity
  have hBL : 0 ≤ B / L2 ^ 2 := by positivity
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hlx : 0 ≤ Real.log (x / 2) := Real.log_nonneg (by rw [le_div_iff₀ two_pos]; linarith)
  have hha : (x - 2) * a + √x * Real.log (x / 2) ≤ a * x + √x * Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hs0]
  refine add_le_add (mul_le_mul_of_nonneg_left hha hBL) ?_
  · rw [hsx]
    have : (√x - 2 ^ (1 / 2 : ℝ)) / (1 / 2) ≤ 2 * √x := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    calc 2 / L2 * ((√x - 2 ^ (1 / 2 : ℝ)) / (1 / 2)) ≤ 2 / L2 * (2 * √x) := by gcongr
      _ = 4 / L2 * √x := by ring

/-- **Davenport, Ch. 18, p. 113 (rows 18-5, 18-6)**: the prime number theorem with
de la Vallée Poussin's error term, `π(x) = li x + O(x exp(-c √log x))`: there are `c, K > 0`
with `|π(x) - li x| ≤ K x exp(-c √log x)` for all `x ≥ 2`. -/
@[kb "davenport1980" "Ch 18, p. 113"]
theorem Davenport.primeCounting_sub_logIntegral_le :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ x : ℝ, 2 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x| ≤ K * x * Real.exp (-(c * √(Real.log x))) := by
  obtain ⟨c, B, hc, hc1, hB, hθ⟩ := theta_sub_self_le
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
  -- the three bounds
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
  have hsx : √x ≤ √x * Real.log x / L2 := by
    rw [le_div_iff₀ (by linarith)]
    have := Real.sqrt_nonneg x
    nlinarith
  -- `|θ(x) - x| / log x`
  have b1 : |(Chebyshev.theta x - x) / Real.log x| ≤ (B + 12) / L2 * (x * E) := by
    rw [abs_div, abs_of_pos hlx0, div_le_iff₀ hlx0]
    have h := hθ x hx
    have h2 : B * x * Real.exp (-(c * √(Real.log x))) ≤ B * (x * E) := by
      calc B * x * Real.exp (-(c * √(Real.log x))) = B * x * Real.exp (-(c * √(Real.log x))) := rfl
        _ ≤ B * x * E := by gcongr
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
  -- the integral
  have b3 := norm_integral_theta_sub_le hc hB hθ hx
  have hL2sq : 4 / 9 ≤ L2 ^ 2 := by nlinarith
  have b3' : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      (B / L2 ^ 2 * 7 + 4 / L2 * 6 / L2) * (x * E) := by
    refine b3.trans ?_
    have hB0 : 0 ≤ B / L2 ^ 2 := by positivity
    have h1 : Real.exp (-(c * √(Real.log x / 2))) * x + √x * Real.log x ≤ 7 * (x * E) := by
      have : Real.exp (-(c * √(Real.log x / 2))) * x ≤ E * x := by gcongr
      nlinarith
    have h2 : 4 / L2 * √x ≤ 4 / L2 * 6 / L2 * (x * E) := by
      have : 0 ≤ 4 / L2 := by positivity
      calc 4 / L2 * √x ≤ 4 / L2 * (√x * Real.log x / L2) := by gcongr
        _ ≤ 4 / L2 * (6 * (x * E) / L2) := by gcongr
        _ = 4 / L2 * 6 / L2 * (x * E) := by ring
    calc B / L2 ^ 2 * (Real.exp (-(c * √(Real.log x / 2))) * x + √x * Real.log x) +
          4 / L2 * √x ≤ B / L2 ^ 2 * (7 * (x * E)) + 4 / L2 * 6 / L2 * (x * E) := by gcongr
      _ = (B / L2 ^ 2 * 7 + 4 / L2 * 6 / L2) * (x * E) := by ring
  -- constants: `1/L2 ≤ 3/2`, `1/L2² ≤ 9/4`
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
  calc |(Chebyshev.theta x - x) / Real.log x + 2 / L2 +
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)|
      ≤ |(Chebyshev.theta x - x) / Real.log x| + |2 / L2| +
          |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| :=
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
