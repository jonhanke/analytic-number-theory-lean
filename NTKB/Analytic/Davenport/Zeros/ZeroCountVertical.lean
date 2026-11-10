/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ZeroCountArg
import NTKB.Analytic.Davenport.Zeros.DigammaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The vertical side for `N(T)`

**Davenport, Ch. 15, p. 98.** On the line `σ = 2`,
`∫_0^T Re ξ'/ξ(2 + iy) dy = (T/2) log(T/2π) - T/2 + O(log T)` for `T ≥ 2`
(`Davenport.integral_re_logDeriv_riemannXi_two`). This is the change of argument of
`s(s - 1) π^{-s/2} Γ(s/2) ζ(s)` along `2 → 2 + iT` (Davenport's computation via Stirling's
formula), up to the horizontal piece treated separately:

* `ζ'/ζ(2 + iy) = -∑ Λ(n) n^{-2-iy}`, and integrating termwise each term contributes at most
  `2/n²`, so `∫_0^T ζ'/ζ(2 + iy) dy = O(1)` (Davenport: `arg ζ(2 + iT) = O(1)`);
* `∫_0^T Re 1/(1 + iy) dy = arctan T`;
* `∫_0^T Re ψ(2 + iy/2) dy = ∫_0^T log |2 + iy/2| dy + O(log T)` by
  `abs_re_digamma_sub_log_le`, and the last integral is computed exactly.
-/

open Filter Topology Complex Set MeasureTheory LSeries
open scoped Real Interval ArithmeticFunction.vonMangoldt LSeries.notation

namespace NTKB

/-- `Λ(n) n^{-s} = Λ(n) e^{-s log n}` (both sides vanish at `n = 0`). -/
lemma term_vonMangoldt_eq (s : ℂ) (n : ℕ) :
    term (fun n ↦ (Λ n : ℂ)) s n = (Λ n : ℂ) * Complex.exp (-(s * Real.log n)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn', ← Complex.ofReal_natCast,
    ← Complex.ofReal_log n.cast_nonneg, Complex.exp_neg, div_eq_mul_inv, mul_comm s]

lemma norm_term_vonMangoldt_two_add (y : ℝ) (n : ℕ) :
    ‖term (fun n ↦ (Λ n : ℂ)) (2 + y * I) n‖ = Λ n * Real.exp (-(2 * Real.log n)) := by
  rw [term_vonMangoldt_eq, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  congr 2
  simp only [neg_re, mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat]
  ring

/-- `‖∫_0^T Λ(n) n^{-2-iy} dy‖ ≤ 2/n²`. -/
lemma norm_integral_term_vonMangoldt_le (T : ℝ) (n : ℕ) :
    ‖∫ y in (0 : ℝ)..T, term (fun n ↦ (Λ n : ℂ)) (2 + y * I) n‖ ≤ 2 / (n : ℝ) ^ 2 := by
  rcases lt_or_ge n 2 with hn | hn
  · have hΛ : Λ n = 0 := by
      interval_cases n
      · simp
      · simp
    simp only [term_vonMangoldt_eq, hΛ, Complex.ofReal_zero, zero_mul,
      intervalIntegral.integral_zero, norm_zero]
    positivity
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  set Lg := Real.log n with hL
  have hL0 : 0 < Lg := Real.log_pos hn1
  have hLc : (Lg : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hIL : (I * (Lg : ℂ)) ≠ 0 := mul_ne_zero I_ne_zero hLc
  set G : ℝ → ℂ := fun y ↦ Complex.exp (-(((2 : ℂ) + y * I) * Lg)) / (-(I * Lg)) with hG
  have hd : ∀ y : ℝ, HasDerivAt G (Complex.exp (-(((2 : ℂ) + y * I) * Lg))) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℂ ↦ -(((2 : ℂ) + z * I) * Lg)) (-(I * Lg)) (y : ℂ) := by
      have := ((hasDerivAt_id (y : ℂ)).mul_const (-(I * (Lg : ℂ)))).add_const (-(2 * (Lg : ℂ)))
      convert this using 1
      · funext z; simp only [id]; ring
      · simp
    have h2 := (h1.cexp.div_const (-(I * Lg))).comp_ofReal
    convert h2 using 1
    field_simp
  have hcont : Continuous fun y : ℝ ↦ Complex.exp (-(((2 : ℂ) + y * I) * Lg)) := by fun_prop
  have hint : ∫ y in (0 : ℝ)..T, term (fun n ↦ (Λ n : ℂ)) (2 + y * I) n =
      (Λ n : ℂ) * (G T - G 0) := by
    simp only [term_vonMangoldt_eq]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hd y) (hcont.intervalIntegrable _ _)]
  have hGn : ∀ y : ℝ, ‖G y‖ = Real.exp (-(2 * Lg)) / Lg := by
    intro y
    rw [hG]
    simp only
    rw [norm_div, Complex.norm_exp, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg hL0.le]
    congr 2
    simp
  have hΛ : Λ n ≤ Lg := ArithmeticFunction.vonMangoldt_le_log
  have hexp : Real.exp (-(2 * Lg)) = 1 / (n : ℝ) ^ 2 := by
    rw [Real.exp_neg, hL, show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by
      rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), one_div]
  rw [hint, norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc Λ n * ‖G T - G 0‖ ≤ Λ n * (‖G T‖ + ‖G 0‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) ArithmeticFunction.vonMangoldt_nonneg
    _ = Λ n / Lg * (2 * Real.exp (-(2 * Lg))) := by rw [hGn, hGn]; ring
    _ ≤ 1 * (2 * Real.exp (-(2 * Lg))) := by
        gcongr
        rw [div_le_one hL0]; exact hΛ
    _ = 2 / (n : ℝ) ^ 2 := by rw [hexp]; ring

/-- **`∫_0^T ζ'/ζ(2 + iy) dy = O(1)`**. -/
lemma exists_norm_integral_logDeriv_riemannZeta_two_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ‖∫ y in (0 : ℝ)..T, deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I)‖ ≤ C := by
  have hg : Summable fun n : ℕ ↦ 2 / (n : ℝ) ^ 2 := by
    have := (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2
    exact this.congr fun n ↦ by ring
  refine ⟨∑' n : ℕ, 2 / (n : ℝ) ^ 2, tsum_nonneg fun n ↦ by positivity, fun T hT ↦ ?_⟩
  have hre : ∀ y : ℝ, 1 < ((2 : ℂ) + y * I).re := fun y ↦ by norm_num
  set F : ℕ → ℝ → ℂ := fun n y ↦ term (fun n ↦ (Λ n : ℂ)) (2 + y * I) n with hF
  set b : ℕ → ℝ → ℝ := fun n _ ↦ Λ n * Real.exp (-(2 * Real.log n)) with hb
  have hbs : Summable fun n ↦ Λ n * Real.exp (-(2 * Real.log n)) := by
    have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt (hre 0))
    rw [LSeriesSummable, ← summable_norm_iff] at h
    refine h.congr fun n ↦ ?_
    rw [norm_term_vonMangoldt_two_add]
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := T) (F := F) (f := fun y ↦ L (fun n ↦ (Λ n : ℂ)) (2 + y * I)) b
    (fun n ↦ by
      refine (Continuous.aestronglyMeasurable ?_)
      simp only [hF, term_vonMangoldt_eq]
      fun_prop)
    (fun n ↦ Eventually.of_forall fun y _ ↦ by rw [hF, norm_term_vonMangoldt_two_add])
    (Eventually.of_forall fun y _ ↦ hbs)
    (by simp only [hb]; exact intervalIntegrable_const)
    (Eventually.of_forall fun y _ ↦
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (hre y)).LSeriesHasSum)
  have heq : ∫ y in (0 : ℝ)..T, deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I) =
      -∫ y in (0 : ℝ)..T, L (fun n ↦ (Λ n : ℂ)) (2 + y * I) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (hre y), neg_div, neg_neg]
  rw [heq, norm_neg, ← hsum.tsum_eq]
  exact tsum_of_norm_bounded hg.hasSum fun n ↦ norm_integral_term_vonMangoldt_le T n

/-- `Re ξ'/ξ(2 + iy) = Re ζ'/ζ(2 + iy) + 1/(1 + y²) - ½ log π + ½ Re ψ(2 + iy/2)`. -/
lemma re_logDeriv_riemannXi_two_add (y : ℝ) :
    (logDeriv riemannXi (2 + y * I)).re =
      (deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I)).re + 1 / (1 + y ^ 2) -
        Real.log π / 2 + (Complex.digamma (2 + (y / 2 : ℝ) * I)).re / 2 := by
  set s : ℂ := 2 + y * I with hs
  have hsre : s.re = 2 := by simp [s]
  have hs1 : s ≠ 1 := fun h ↦ by have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hhalf : s / 2 + 1 = 2 + (y / 2 : ℝ) * I := by rw [hs]; push_cast; ring
  have hΓ : ∀ m : ℕ, s / 2 + 1 ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    rw [hhalf] at this
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; norm_num)
  have h := logDeriv_riemannZeta_eq_xi hs1 hΓ hz
  have hf : logDeriv riemannXi s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
      Complex.log π / 2 + Complex.digamma (s / 2 + 1) / 2 := by
    rw [h]; ring
  rw [hf, hhalf]
  have h1 : s - 1 = ((1 : ℝ) : ℂ) + y * I := by rw [hs]; push_cast; ring
  rw [h1, one_div_ofReal_add_mul_I (by positivity)]
  rw [← Complex.ofReal_log Real.pi_pos.le]
  simp only [add_re, sub_re, div_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul,
    sub_zero, re_ofNat, im_ofNat, normSq_ofNat]
  ring

lemma continuous_re_logDeriv_riemannZeta_two :
    Continuous fun y : ℝ ↦ (deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I)).re := by
  refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun y ↦ ?_)
  have hre : 1 < ((2 : ℂ) + y * I).re := by norm_num
  have hs1 : (2 : ℂ) + y * I ≠ 1 := fun h ↦ by rw [h] at hre; simp at hre
  have han := analyticAt_riemannZeta hs1
  have hc : ContinuousAt (fun s ↦ deriv riemannZeta s / riemannZeta s) ((2 : ℂ) + y * I) :=
    han.deriv.continuousAt.div han.continuousAt (riemannZeta_ne_zero_of_one_lt_re hre)
  exact ContinuousAt.comp (g := fun s ↦ deriv riemannZeta s / riemannZeta s)
    (f := fun y : ℝ ↦ (2 : ℂ) + y * I) hc (by fun_prop)

lemma continuous_re_digamma_two :
    Continuous fun y : ℝ ↦ (Complex.digamma (2 + (y / 2 : ℝ) * I)).re := by
  refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun y ↦ ?_)
  have hre : 0 < ((2 : ℂ) + (y / 2 : ℝ) * I).re := by simp
  exact ContinuousAt.comp (g := Complex.digamma) (f := fun y : ℝ ↦ (2 : ℂ) + (y / 2 : ℝ) * I)
    (continuousAt_digamma_of_re_pos hre) (by fun_prop)

/-- `∫_0^T log(4 + y²/4) dy = T log(4 + T²/4) - 2T + 8 arctan(T/4)`. -/
lemma integral_log_four_add_sq (T : ℝ) :
    ∫ y in (0 : ℝ)..T, Real.log (4 + y ^ 2 / 4) =
      T * Real.log (4 + T ^ 2 / 4) - 2 * T + 8 * Real.arctan (T / 4) := by
  have hpos : ∀ y : ℝ, 0 < 4 + y ^ 2 / 4 := fun y ↦ by positivity
  have hd : ∀ y : ℝ, HasDerivAt (fun y ↦ y * Real.log (4 + y ^ 2 / 4) - 2 * y +
      8 * Real.arctan (y / 4)) (Real.log (4 + y ^ 2 / 4)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ ↦ 4 + y ^ 2 / 4) (2 * y / 4) y := by
      have := ((hasDerivAt_pow 2 y).div_const 4).const_add 4
      simpa using this
    have h2 := h1.log (hpos y).ne'
    have h3 := (hasDerivAt_id y).mul h2
    have h4 := (Real.hasDerivAt_arctan (y / 4)).comp y ((hasDerivAt_id y).div_const 4)
    have h5 := (h3.sub ((hasDerivAt_id y).const_mul 2)).add (h4.const_mul 8)
    convert h5 using 1
    · funext y; simp [Function.comp]
    · simp only [id, one_mul, mul_one]
      have hy : (4 + y ^ 2 / 4) ≠ 0 := (hpos y).ne'
      have hy' : (1 + (y / 4) ^ 2) ≠ 0 := by positivity
      field_simp
      ring
  have hc : Continuous fun y : ℝ ↦ Real.log (4 + y ^ 2 / 4) :=
    Continuous.log (by fun_prop) fun y ↦ (hpos y).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hd y) (hc.intervalIntegrable _ _)]
  simp

/-- `log |2 + iy/2| = ½ log(4 + y²/4)`. -/
lemma log_norm_two_add (y : ℝ) :
    Real.log ‖(2 : ℂ) + (y / 2 : ℝ) * I‖ = Real.log (4 + y ^ 2 / 4) / 2 := by
  have h : ‖(2 : ℂ) + (y / 2 : ℝ) * I‖ = Real.sqrt (4 + y ^ 2 / 4) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  rw [h, Real.log_sqrt (by positivity)]

lemma continuousOn_four_div_two_add {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun y : ℝ ↦ 4 / (2 + y)) [[(0 : ℝ), T]] := by
  intro y hy
  rw [uIcc_of_le hT] at hy
  have h0 : (2 : ℝ) + y ≠ 0 := (by linarith [hy.1] : (0 : ℝ) < 2 + y).ne'
  exact (continuousAt_const.div (continuousAt_const.add (continuousAt_id' y)) h0).continuousWithinAt

/-- `∫_0^T 4/(2 + y) dy = 4 log((2 + T)/2)`. -/
lemma integral_four_div_two_add {T : ℝ} (hT : 0 ≤ T) :
    ∫ y in (0 : ℝ)..T, 4 / (2 + y) = 4 * Real.log ((2 + T) / 2) := by
  have hd : ∀ y ∈ [[(0 : ℝ), T]], HasDerivAt (fun y ↦ 4 * Real.log (2 + y)) (4 / (2 + y)) y := by
    intro y hy
    rw [uIcc_of_le hT] at hy
    have h0 : (2 : ℝ) + y ≠ 0 := (by linarith [hy.1] : (0 : ℝ) < 2 + y).ne'
    have h := ((hasDerivAt_id' y).const_add 2).log h0
    convert h.const_mul 4 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_four_div_two_add hT).intervalIntegrable),
    Real.log_div (by linarith) (by norm_num)]
  simp
  ring

/-- **Davenport, Ch. 15, p. 98**: `∫_0^T Re ξ'/ξ(2 + iy) dy = (T/2) log(T/2π) - T/2 + O(log T)`
for `T ≥ 2`. -/
@[kb "davenport1980" "Ch 15, p. 98"]
theorem Davenport.integral_re_logDeriv_riemannXi_two :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 2 ≤ T →
      |(∫ y in (0 : ℝ)..T, (logDeriv riemannXi (2 + y * I)).re) -
        (T / 2 * Real.log (T / (2 * π)) - T / 2)| ≤ A * Real.log T := by
  obtain ⟨C, hC, hZ⟩ := exists_norm_integral_logDeriv_riemannZeta_two_le
  refine ⟨(C + 3 * π / 2 + 2) / Real.log 2 + 2, by positivity, fun T hT ↦ ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the pieces
  set Z := ∫ y in (0 : ℝ)..T, (deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I)).re
  set Ψ := ∫ y in (0 : ℝ)..T, (Complex.digamma (2 + (y / 2 : ℝ) * I)).re
  have hc1 := continuous_re_logDeriv_riemannZeta_two
  have hc2 : Continuous fun y : ℝ ↦ 1 / (1 + y ^ 2) :=
    Continuous.div continuous_const (continuous_const.add (continuous_pow 2)) fun y ↦
      (by positivity : (0 : ℝ) < 1 + y ^ 2).ne'
  have hc3 := continuous_re_digamma_two
  have hsplit : ∫ y in (0 : ℝ)..T, (logDeriv riemannXi (2 + y * I)).re =
      Z + Real.arctan T - T * (Real.log π / 2) + Ψ / 2 := by
    simp only [re_logDeriv_riemannXi_two_add]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_add,
      integral_one_div_one_add_sq, intervalIntegral.integral_div, intervalIntegral.integral_const]
    · simp [Z, Ψ]; ring
    all_goals first
      | exact (hc1.add hc2).intervalIntegrable _ _
      | exact hc1.intervalIntegrable _ _
      | exact hc2.intervalIntegrable _ _
      | exact intervalIntegrable_const
      | exact ((hc1.add hc2).sub continuous_const).intervalIntegrable _ _
      | exact (hc3.div_const 2).intervalIntegrable _ _
  -- `ζ'/ζ`
  have hZb : |Z| ≤ C := by
    have h := hZ T hT0
    have : Z = (∫ y in (0 : ℝ)..T, deriv riemannZeta (2 + y * I) / riemannZeta (2 + y * I)).re := by
      rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm]
      · rfl
      exact (continuous_iff_continuousAt.mpr fun y ↦ by
          have hre : 1 < ((2 : ℂ) + y * I).re := by norm_num
          have hs1 : (2 : ℂ) + y * I ≠ 1 := fun h ↦ by rw [h] at hre; simp at hre
          have han := analyticAt_riemannZeta hs1
          exact ContinuousAt.comp (g := fun s ↦ deriv riemannZeta s / riemannZeta s)
            (f := fun y : ℝ ↦ (2 : ℂ) + y * I) (han.deriv.continuousAt.div han.continuousAt
            (riemannZeta_ne_zero_of_one_lt_re hre)) (by fun_prop)).intervalIntegrable (μ := volume) 0 T
    rw [this]
    exact (Complex.abs_re_le_norm _).trans h
  -- the digamma part
  have hlogc : Continuous fun y : ℝ ↦ Real.log (4 + y ^ 2 / 4) :=
    Continuous.log (by fun_prop) fun y ↦ by positivity
  have hΨ : |Ψ - (∫ y in (0 : ℝ)..T, Real.log (4 + y ^ 2 / 4)) / 2| ≤
      4 * Real.log ((2 + T) / 2) := by
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_sub
      (hc3.intervalIntegrable _ _) ((hlogc.div_const 2).intervalIntegrable _ _),
      ← integral_four_div_two_add hT0, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hT0 (Eventually.of_forall fun y hy ↦ ?_)
      ((continuousOn_four_div_two_add hT0).intervalIntegrable)
    · have hy0 : 0 ≤ y := hy.1.le
      rw [← log_norm_two_add, Real.norm_eq_abs]
      have h := abs_re_digamma_sub_log_le (w := 2 + (y / 2 : ℝ) * I) (by simp)
      have him : ((2 : ℂ) + (y / 2 : ℝ) * I).im = y / 2 := by simp
      rw [him, abs_of_nonneg (show (0 : ℝ) ≤ y / 2 by linarith)] at h
      refine h.trans (le_of_eq ?_)
      field_simp
      ring
  have hD : |(∫ y in (0 : ℝ)..T, Real.log (4 + y ^ 2 / 4)) / 4 -
      (T / 2 * Real.log (T / 2) - T / 2)| ≤ 2 + π := by
    rw [integral_log_four_add_sq]
    have hT2 : 0 < T ^ 2 / 4 := by positivity
    have e : Real.log (4 + T ^ 2 / 4) = 2 * Real.log (T / 2) + Real.log (1 + 16 / T ^ 2) := by
      rw [show (4 : ℝ) + T ^ 2 / 4 = (T / 2) ^ 2 * (1 + 16 / T ^ 2) by field_simp; ring,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    have hl0 : 0 ≤ Real.log (1 + 16 / T ^ 2) := Real.log_nonneg (by
      have : 0 ≤ 16 / T ^ 2 := by positivity
      linarith)
    have hl1 : Real.log (1 + 16 / T ^ 2) ≤ 16 / T ^ 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 16 / T ^ 2 by positivity); linarith
    have hl2 : T * Real.log (1 + 16 / T ^ 2) ≤ 8 := by
      calc T * Real.log (1 + 16 / T ^ 2) ≤ T * (16 / T ^ 2) := by gcongr
        _ = 16 / T := by field_simp
        _ ≤ 8 := by rw [div_le_iff₀ (by linarith)]; linarith
    have ha := Real.arctan_lt_pi_div_two (T / 4)
    have hb := Real.neg_pi_div_two_lt_arctan (T / 4)
    rw [e, abs_le]
    constructor <;> nlinarith [mul_nonneg hT0 hl0]
  -- assemble
  have hπ : Real.log (T / (2 * π)) = Real.log (T / 2) - Real.log π := by
    rw [show T / (2 * π) = (T / 2) / π by ring, Real.log_div (by positivity) Real.pi_pos.ne']
  have hat := Real.arctan_lt_pi_div_two T
  have hat' := Real.neg_pi_div_two_lt_arctan T
  have hlogT2 : Real.log ((2 + T) / 2) ≤ Real.log T :=
    Real.log_le_log (by positivity) (by linarith)
  rw [hsplit, hπ]
  have hfinal : |Z + Real.arctan T - T * (Real.log π / 2) + Ψ / 2 -
      (T / 2 * (Real.log (T / 2) - Real.log π) - T / 2)| ≤
      C + π / 2 + 2 * Real.log ((2 + T) / 2) + (2 + π) := by
    rw [abs_le] at hZb hΨ hD ⊢
    constructor <;> nlinarith
  refine hfinal.trans ?_
  have h1 : C + π / 2 + (2 + π) ≤ (C + 3 * π / 2 + 2) / Real.log 2 * Real.log T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    have : 0 ≤ C + 3 * π / 2 + 2 := by positivity
    nlinarith [Real.log_two_lt_d9]
  nlinarith

end NTKB
