/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroCountArg
import NTKB.Analytic.Davenport.Zeros.ZeroCountVertical
import NTKB.Analytic.Davenport.Zeros.LLocal

/-!
# The vertical side for `N(T, χ)`

**Davenport, Ch. 16, p. 101.** For `χ` primitive mod `q > 1` and `T ≥ 2`,
`∫_{-T}^T Re ξ'/ξ(3/2 + iy, χ) dy = T log(qT/2π) - T + O(log T)` with an absolute constant
(`Davenport.integral_re_logDeriv_dirichletXi`). As for `ζ`:
`ξ'/ξ(s, χ) = L'/L(s, χ) + ½ log(q/π) + ½ ψ((s + a)/2)`; the `L'/L` part integrates to `O(1)`
(termwise), and `Re ψ(w) = log |w| + O(1/(1 + |Im w|))` for `Re w ≥ 1/2`
(`abs_re_digamma_sub_log_le_half`, from the case `Re w ≥ 2` and `ψ(w + 1) = ψ(w) + 1/w`).
-/

open Filter Topology Complex Set MeasureTheory LSeries DirichletCharacter
open scoped Real Interval ArithmeticFunction.vonMangoldt LSeries.notation

namespace NTKB

/-- **Stirling's formula for `Re ψ`, `Re w ≥ 1/2`**: `|Re ψ(w) - log |w|| ≤ 18/(1 + |Im w|)`. -/
theorem abs_re_digamma_sub_log_le_half {w : ℂ} (hw : 1 / 2 ≤ w.re) :
    |(Complex.digamma w).re - Real.log ‖w‖| ≤ 18 / (1 + |w.im|) := by
  have hw0 : w ≠ 0 := fun h ↦ by rw [h] at hw; simp at hw; linarith
  have hw1 : w + 1 ≠ 0 := fun h ↦ by have := congrArg Complex.re h; simp at this; linarith
  have hpole : ∀ m : ℕ, w ≠ -m := fun m h ↦ by
    have := congrArg Complex.re h; simp at this; linarith [m.cast_nonneg (α := ℝ)]
  have hpole1 : ∀ m : ℕ, w + 1 ≠ -m := fun m h ↦ by
    have := congrArg Complex.re h; simp at this; linarith [m.cast_nonneg (α := ℝ)]
  have hψ : Complex.digamma (w + 2) = Complex.digamma w + 1 / w + 1 / (w + 1) := by
    rw [show w + 2 = (w + 1) + 1 by ring, Complex.digamma_apply_add_one _ hpole1,
      Complex.digamma_apply_add_one _ hpole]
    simp only [one_div]
  have h2 := abs_re_digamma_sub_log_le (w := w + 2) (by simp; linarith)
  have him : (w + 2).im = w.im := by simp
  rw [him] at h2
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hn2 : ‖w‖ ≤ ‖w + 2‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith
  have hn1 : ‖w‖ ≤ ‖w + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp; nlinarith
  have hlog : |Real.log ‖w + 2‖ - Real.log ‖w‖| ≤ 2 / ‖w‖ := by
    rw [← Real.log_div (by linarith) hn.ne']
    have h1 : 1 ≤ ‖w + 2‖ / ‖w‖ := by rw [le_div_iff₀ hn]; linarith
    rw [abs_of_nonneg (Real.log_nonneg h1)]
    have := Real.log_le_sub_one_of_pos (show 0 < ‖w + 2‖ / ‖w‖ by positivity)
    have h3 : ‖w + 2‖ / ‖w‖ - 1 ≤ 2 / ‖w‖ := by
      rw [div_sub_one hn.ne', div_le_div_iff_of_pos_right hn]
      have := norm_add_le w 2
      simp at this; linarith
    linarith
  have hinv : ‖1 / w + 1 / (w + 1)‖ ≤ 2 / ‖w‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, norm_one]
    have : 1 / ‖w + 1‖ ≤ 1 / ‖w‖ := one_div_le_one_div_of_le hn hn1
    linarith [show 1 / ‖w‖ + 1 / ‖w‖ = 2 / ‖w‖ by ring]
  have hwlow : (1 + |w.im|) / 4 ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w
    have := Complex.re_le_norm w
    linarith
  have hw4 : 2 / ‖w‖ ≤ 8 / (1 + |w.im|) := by
    rw [div_le_div_iff₀ hn (by positivity)]; linarith
  have hre : (Complex.digamma w).re =
      (Complex.digamma (w + 2)).re - (1 / w + 1 / (w + 1)).re := by
    rw [hψ]; simp only [add_re]; ring
  have hre' := Complex.abs_re_le_norm (1 / w + 1 / (w + 1))
  rw [hre]
  have e : (Complex.digamma (w + 2)).re - (1 / w + 1 / (w + 1)).re - Real.log ‖w‖ =
      ((Complex.digamma (w + 2)).re - Real.log ‖w + 2‖) + (Real.log ‖w + 2‖ - Real.log ‖w‖) -
        (1 / w + 1 / (w + 1)).re := by ring
  rw [e]
  have h18 : 2 / (1 + |w.im|) + 8 / (1 + |w.im|) + 8 / (1 + |w.im|) = 18 / (1 + |w.im|) := by ring
  calc _ ≤ |(Complex.digamma (w + 2)).re - Real.log ‖w + 2‖| +
        |Real.log ‖w + 2‖ - Real.log ‖w‖| + |(1 / w + 1 / (w + 1)).re| := by
        have k1 := abs_sub ((Complex.digamma (w + 2)).re - Real.log ‖w + 2‖ +
          (Real.log ‖w + 2‖ - Real.log ‖w‖)) (1 / w + 1 / (w + 1)).re
        have k2 := abs_add_le ((Complex.digamma (w + 2)).re - Real.log ‖w + 2‖)
          (Real.log ‖w + 2‖ - Real.log ‖w‖)
        linarith
    _ ≤ 2 / (1 + |w.im|) + 8 / (1 + |w.im|) + 8 / (1 + |w.im|) := by
        gcongr
        · exact hlog.trans hw4
        · exact hre'.trans (hinv.trans hw4)
    _ = 18 / (1 + |w.im|) := h18

/-- `∫_a^b log(c² + y²/4) dy` in closed form. -/
lemma integral_log_sq_add_sq {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    ∫ y in a..b, Real.log (c ^ 2 + y ^ 2 / 4) =
      (b * Real.log (c ^ 2 + b ^ 2 / 4) - 2 * b + 4 * c * Real.arctan (b / (2 * c))) -
        (a * Real.log (c ^ 2 + a ^ 2 / 4) - 2 * a + 4 * c * Real.arctan (a / (2 * c))) := by
  have hpos : ∀ y : ℝ, 0 < c ^ 2 + y ^ 2 / 4 := fun y ↦ by positivity
  have hd : ∀ y : ℝ, HasDerivAt (fun y ↦ y * Real.log (c ^ 2 + y ^ 2 / 4) - 2 * y +
      4 * c * Real.arctan (y / (2 * c))) (Real.log (c ^ 2 + y ^ 2 / 4)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ ↦ c ^ 2 + y ^ 2 / 4) (2 * y / 4) y := by
      have := ((hasDerivAt_pow 2 y).div_const 4).const_add (c ^ 2)
      simpa using this
    have h2 := h1.log (hpos y).ne'
    have h4' : HasDerivAt (fun y : ℝ ↦ y / (2 * c)) (1 / (2 * c)) y := by
      simpa using (hasDerivAt_id' y).div_const (2 * c)
    have h4 := h4'.arctan
    have h3' : HasDerivAt (fun y : ℝ ↦ y * Real.log (c ^ 2 + y ^ 2 / 4))
        (1 * Real.log (c ^ 2 + y ^ 2 / 4) + y * (2 * y / 4 / (c ^ 2 + y ^ 2 / 4))) y :=
      (hasDerivAt_id' y).mul h2
    have h5 := (h3'.sub ((hasDerivAt_id' y).const_mul 2)).add (h4.const_mul (4 * c))
    refine h5.congr_deriv ?_
    simp only [one_mul, mul_one]
    have hD := hpos y
    have hc0 : c ≠ 0 := hc.ne'
    have e1 : 1 + (y / (2 * c)) ^ 2 = (c ^ 2 + y ^ 2 / 4) / c ^ 2 := by field_simp; ring
    rw [e1]
    have e2 : 4 * c * (1 / ((c ^ 2 + y ^ 2 / 4) / c ^ 2) * (1 / (2 * c))) =
        2 * c ^ 2 / (c ^ 2 + y ^ 2 / 4) := by field_simp; ring
    have e3 : y * (2 * y / 4 / (c ^ 2 + y ^ 2 / 4)) = y ^ 2 / 2 / (c ^ 2 + y ^ 2 / 4) := by ring
    have e4 : y ^ 2 / 2 / (c ^ 2 + y ^ 2 / 4) + 2 * c ^ 2 / (c ^ 2 + y ^ 2 / 4) = 2 := by
      rw [← add_div, div_eq_iff hD.ne']; ring
    linear_combination e2 + e3 + e4
  have hcont : Continuous fun y : ℝ ↦ Real.log (c ^ 2 + y ^ 2 / 4) :=
    Continuous.log (by fun_prop) fun y ↦ (hpos y).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hd y) (hcont.intervalIntegrable _ _)]

/-- `χ(n) Λ(n) n^{-s} = χ(n) Λ(n) e^{-s log n}`. -/
lemma term_twist_vonMangoldt_eq' {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) :
    term (↗χ * ↗Λ) s n = χ n * (Λ n : ℂ) * Complex.exp (-(s * Real.log n)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn]
  simp only [Pi.mul_apply]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn', ← Complex.ofReal_natCast,
    ← Complex.ofReal_log n.cast_nonneg, Complex.exp_neg, div_eq_mul_inv, mul_comm s]

/-- `‖∫_a^b χ(n) Λ(n) n^{-3/2-iy} dy‖ ≤ 2 n^{-3/2}`. -/
lemma norm_integral_term_twist_le {N : ℕ} (χ : DirichletCharacter ℂ N) (a b : ℝ) (n : ℕ) :
    ‖∫ y in a..b, term (↗χ * ↗Λ) (3 / 2 + y * I) n‖ ≤ 2 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  rcases lt_or_ge n 2 with hn | hn
  · have hΛ : Λ n = 0 := by
      interval_cases n
      · simp
      · simp
    simp only [term_twist_vonMangoldt_eq', hΛ, Complex.ofReal_zero, mul_zero, zero_mul,
      intervalIntegral.integral_zero, norm_zero]
    positivity
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  set Lg := Real.log n with hL
  have hL0 : 0 < Lg := Real.log_pos hn1
  have hLc : (Lg : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  set G : ℝ → ℂ := fun y ↦ Complex.exp (-(((3 / 2 : ℂ) + y * I) * Lg)) / (-(I * Lg)) with hG
  have hd : ∀ y : ℝ, HasDerivAt G (Complex.exp (-(((3 / 2 : ℂ) + y * I) * Lg))) y := by
    intro y
    have h1 : HasDerivAt (fun z : ℂ ↦ -(((3 / 2 : ℂ) + z * I) * Lg)) (-(I * Lg)) (y : ℂ) := by
      have := ((hasDerivAt_id (y : ℂ)).mul_const (-(I * (Lg : ℂ)))).add_const (-(3 / 2 * (Lg : ℂ)))
      convert this using 1
      · funext z; simp only [id]; ring
      · simp
    have h2 := (h1.cexp.div_const (-(I * Lg))).comp_ofReal
    convert h2 using 1
    field_simp
  have hcont : Continuous fun y : ℝ ↦ Complex.exp (-(((3 / 2 : ℂ) + y * I) * Lg)) := by fun_prop
  have hint : ∫ y in a..b, term (↗χ * ↗Λ) (3 / 2 + y * I) n = χ n * (Λ n : ℂ) * (G b - G a) := by
    simp only [term_twist_vonMangoldt_eq']
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hd y) (hcont.intervalIntegrable _ _)]
  have hGn : ∀ y : ℝ, ‖G y‖ = Real.exp (-(3 / 2 * Lg)) / Lg := by
    intro y
    rw [hG]
    simp only
    rw [norm_div, Complex.norm_exp, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg hL0.le]
    congr 2
    simp
  have hΛ : Λ n ≤ Lg := ArithmeticFunction.vonMangoldt_le_log
  have hexp : Real.exp (-(3 / 2 * Lg)) = 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos (by positivity), ← hL, one_div, ← Real.exp_neg]
    ring_nf
  have hχn : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
  rw [hint, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  calc ‖χ n‖ * Λ n * ‖G b - G a‖ ≤ 1 * Λ n * (‖G b‖ + ‖G a‖) := by
        gcongr; exact norm_sub_le _ _
    _ = Λ n / Lg * (2 * Real.exp (-(3 / 2 * Lg))) := by rw [hGn, hGn]; ring
    _ ≤ 1 * (2 * Real.exp (-(3 / 2 * Lg))) := by
        gcongr
        rw [div_le_one hL0]; exact hΛ
    _ = 2 / (n : ℝ) ^ (3 / 2 : ℝ) := by rw [hexp]; ring

/-- **`∫_a^b L'/L(3/2 + iy, χ) dy = O(1)`**, uniformly in `χ`, `a`, `b`. -/
lemma exists_norm_integral_logDeriv_LFunction_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a b : ℝ),
      ‖∫ y in a..b, deriv (LFunction χ) (3 / 2 + y * I) / LFunction χ (3 / 2 + y * I)‖ ≤ C := by
  have hg : Summable fun n : ℕ ↦ 2 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    have := (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2
    exact this.congr fun n ↦ by ring
  refine ⟨∑' n : ℕ, 2 / (n : ℝ) ^ (3 / 2 : ℝ), tsum_nonneg fun n ↦ by positivity,
    fun {N} _ χ a b ↦ ?_⟩
  have hre : ∀ y : ℝ, 1 < ((3 / 2 : ℂ) + y * I).re := fun y ↦ by norm_num
  set F : ℕ → ℝ → ℂ := fun n y ↦ term (↗χ * ↗Λ) (3 / 2 + y * I) n with hF
  set bd : ℕ → ℝ → ℝ := fun n _ ↦ ‖term (↗χ * ↗Λ) ((3 / 2 : ℝ) : ℂ) n‖ with hbd
  have hnorm : ∀ n (y : ℝ), ‖F n y‖ = bd n y := by
    intro n y
    simp only [hF, hbd]
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    norm_num
  have hbs : Summable fun n ↦ ‖term (↗χ * ↗Λ) ((3 / 2 : ℝ) : ℂ) n‖ := by
    have h := LSeriesSummable_twist_vonMangoldt χ (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)
    rw [LSeriesSummable, ← summable_norm_iff] at h
    exact h
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := a) (b := b) (F := F) (f := fun y ↦ L (↗χ * ↗Λ) (3 / 2 + y * I)) bd
    (fun n ↦ by
      refine (Continuous.aestronglyMeasurable ?_)
      simp only [hF, term_twist_vonMangoldt_eq']
      fun_prop)
    (fun n ↦ Eventually.of_forall fun y _ ↦ (hnorm n y).le)
    (Eventually.of_forall fun y _ ↦ hbs)
    (by simp only [hbd]; exact intervalIntegrable_const)
    (Eventually.of_forall fun y _ ↦
      (LSeriesSummable_twist_vonMangoldt χ (hre y)).LSeriesHasSum)
  have heq : ∫ y in a..b, deriv (LFunction χ) (3 / 2 + y * I) / LFunction χ (3 / 2 + y * I) =
      -∫ y in a..b, L (↗χ * ↗Λ) (3 / 2 + y * I) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ ↦ ?_
    rw [← neg_logDeriv_LFunction_eq_LSeries χ (hre y), neg_div, neg_neg]
  rw [heq, norm_neg, ← hsum.tsum_eq]
  exact tsum_of_norm_bounded hg.hasSum fun n ↦ norm_integral_term_twist_le χ a b n

variable {N : ℕ} [NeZero N]

/-- `ξ'/ξ(s, χ) = L'/L(s, χ) + ½ log q - ½ log π + ½ ψ((s + a)/2)`. -/
lemma logDeriv_dirichletXi_eq {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (hs : ∀ m : ℕ, s + dirichletParity χ ≠ -(2 * m)) (hL : LFunction χ s ≠ 0)
    (hξ : dirichletXi χ s ≠ 0) :
    logDeriv (dirichletXi χ) s = deriv (LFunction χ) s / LFunction χ s + Complex.log N / 2 -
      Complex.log π / 2 + Complex.digamma ((s + dirichletParity χ) / 2) / 2 := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  obtain ⟨A, B, hH⟩ := Davenport.dirichletXi_hadamard hχ hN
  have h1 := logDeriv_eq_of_hadamard (differentiable_dirichletXi hχ1)
    (dirichletXi_zero_ne_zero hχ hN) (Davenport.entireOrder_dirichletXi_le_one hχ hN) hH hξ
  have h2 := Davenport.logDeriv_LFunction hχ hN hH hs hL
  have hψ : deriv Complex.Gamma ((s + dirichletParity χ) / 2) /
      (2 * Complex.Gamma ((s + dirichletParity χ) / 2)) =
        Complex.digamma ((s + dirichletParity χ) / 2) / 2 := by
    rw [Complex.digamma_def, logDeriv_apply]; ring
  rw [hψ] at h2
  rw [h1, h2]; ring

lemma intervalIntegral_inv_two_add_abs {T : ℝ} (hT : 0 ≤ T) :
    ∫ y in (-T)..T, 36 / (2 + |y|) = 72 * Real.log ((2 + T) / 2) := by
  have hc : Continuous fun y : ℝ ↦ 36 / (2 + |y|) :=
    continuous_const.div (continuous_const.add continuous_abs) fun y ↦
      (by positivity : (0 : ℝ) < 2 + |y|).ne'
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-T) 0)
    (hc.intervalIntegrable 0 T)]
  have h1 : ∫ y in (-T)..0, 36 / (2 + |y|) = ∫ y in (0 : ℝ)..T, 36 / (2 + |y|) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := T) (fun y : ℝ ↦ 36 / (2 + |y|))
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  have h2 : ∫ y in (0 : ℝ)..T, 36 / (2 + |y|) = 9 * ∫ y in (0 : ℝ)..T, 4 / (2 + y) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    rw [uIcc_of_le hT] at hy
    rw [abs_of_nonneg hy.1]; ring
  rw [h1, h2, integral_four_div_two_add hT]; ring

/-- **Davenport, Ch. 16, p. 101**: for primitive `χ` mod `q > 1` and `T ≥ 2`,
`|∫_{-T}^T Re ξ'/ξ(3/2 + iy, χ) dy - (T log(qT/2π) - T)| ≤ A log T`, `A` absolute. -/
@[kb "davenport1980" "Ch 16, p. 101"]
theorem Davenport.integral_re_logDeriv_dirichletXi :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ T : ℝ, 2 ≤ T →
      |(∫ y in (-T)..T, (logDeriv (dirichletXi χ) (3 / 2 + y * I)).re) -
        (T * Real.log (N * T / (2 * π)) - T)| ≤ A * Real.log T := by
  obtain ⟨C, hC, hZ⟩ := exists_norm_integral_logDeriv_LFunction_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨36 + (C + 6) / Real.log 2, by positivity, fun {N} _ {χ} hχ hN T hT ↦ ?_⟩
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hT0 : 0 ≤ T := by linarith
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  set a := (dirichletParity χ).re with ha
  have ha0 : 0 ≤ a := dirichletParity_re_nonneg χ
  have ha1 : a ≤ 1 := dirichletParity_re_le_one χ
  set c : ℝ := (3 / 2 + a) / 2 with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 5 / 4 := by rw [hc]; linarith
  have hw : ∀ y : ℝ, (3 / 2 + y * I + dirichletParity χ) / 2 = (c : ℂ) + ((y / 2 : ℝ) : ℂ) * I := by
    intro y
    apply Complex.ext <;> simp [hc, ha, dirichletParity_im]
  -- pointwise formula
  have hpt : ∀ y : ℝ, (logDeriv (dirichletXi χ) (3 / 2 + y * I)).re =
      (deriv (LFunction χ) (3 / 2 + y * I) / LFunction χ (3 / 2 + y * I)).re +
        Real.log N / 2 - Real.log π / 2 +
          (Complex.digamma ((c : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2 := by
    intro y
    have hre : (3 / 2 + y * I : ℂ).re = 3 / 2 := by simp
    have hs : ∀ m : ℕ, (3 / 2 + y * I : ℂ) + dirichletParity χ ≠ -(2 * m) := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      linarith [m.cast_nonneg (α := ℝ)]
    have hL := LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (s := 3 / 2 + y * I)
      (by rw [hre]; norm_num)
    have hξ := dirichletXi_ne_zero_of_one_le_re hχ1 hN (s := 3 / 2 + y * I)
      (by rw [hre]; norm_num)
    rw [logDeriv_dirichletXi_eq hχ hN hs hL hξ, hw, ← Complex.ofReal_natCast,
      ← Complex.ofReal_log (Nat.cast_nonneg N), ← Complex.ofReal_log Real.pi_pos.le]
    simp only [add_re, sub_re, div_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat, normSq_ofNat,
      mul_zero, zero_div]
    ring
  -- continuity
  have hcL : Continuous fun y : ℝ ↦
      deriv (LFunction χ) (3 / 2 + y * I) / LFunction χ (3 / 2 + y * I) := by
    refine continuous_iff_continuousAt.mpr fun y ↦ ?_
    have hre : 1 ≤ ((3 / 2 : ℂ) + y * I).re := by norm_num
    have han := (differentiable_LFunction hχ1).analyticAt ((3 / 2 : ℂ) + y * I)
    exact ContinuousAt.comp (g := fun s ↦ deriv (LFunction χ) s / LFunction χ s)
      (f := fun y : ℝ ↦ (3 / 2 : ℂ) + y * I) (han.deriv.continuousAt.div han.continuousAt
        (LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hre)) (by fun_prop)
  have hc1' : Continuous fun y : ℝ ↦
      (deriv (LFunction χ) (3 / 2 + y * I) / LFunction χ (3 / 2 + y * I)).re :=
    Complex.continuous_re.comp hcL
  have hc3 : Continuous fun y : ℝ ↦ (Complex.digamma ((c : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re := by
    refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun y ↦ ?_)
    have hre : 0 < ((c : ℂ) + ((y / 2 : ℝ) : ℂ) * I).re := by simp [hc0]
    exact ContinuousAt.comp (g := Complex.digamma)
      (f := fun y : ℝ ↦ (c : ℂ) + ((y / 2 : ℝ) : ℂ) * I)
      (continuousAt_digamma_of_re_pos hre) (by fun_prop)
  set Z := ∫ y in (-T)..T,
    (deriv (LFunction χ) (3 / 2 + y * I) / LFunction χ (3 / 2 + y * I)).re with hZdef
  set Ψ := ∫ y in (-T)..T, (Complex.digamma ((c : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re with hΨdef
  have hsplit : ∫ y in (-T)..T, (logDeriv (dirichletXi χ) (3 / 2 + y * I)).re =
      Z + 2 * T * (Real.log N / 2 - Real.log π / 2) + Ψ / 2 := by
    set K : ℝ := Real.log N / 2 - Real.log π / 2 with hK
    have e : ∀ y : ℝ, (logDeriv (dirichletXi χ) (3 / 2 + y * I)).re =
        ((deriv (LFunction χ) (3 / 2 + y * I) / LFunction χ (3 / 2 + y * I)).re + K) +
          (Complex.digamma ((c : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2 := by
      intro y; rw [hpt, hK]; ring
    simp only [e]
    rw [intervalIntegral.integral_add
        (f := fun y : ℝ ↦ (deriv (LFunction χ) (3 / 2 + y * I) / LFunction χ (3 / 2 + y * I)).re + K)
        (g := fun y : ℝ ↦ (Complex.digamma ((c : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re / 2)
        ((hc1'.add continuous_const).intervalIntegrable _ _)
        ((hc3.div_const 2).intervalIntegrable _ _),
      intervalIntegral.integral_add
        (f := fun y : ℝ ↦ (deriv (LFunction χ) (3 / 2 + y * I) / LFunction χ (3 / 2 + y * I)).re)
        (g := fun _ ↦ K) (hc1'.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_div, smul_eq_mul]
    ring
  -- `L'/L`
  have hZb : |Z| ≤ C := by
    have h := hZ χ (-T) T
    have : Z = (∫ y in (-T)..T,
        deriv (LFunction χ) (3 / 2 + y * I) / LFunction χ (3 / 2 + y * I)).re := by
      rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm]
      · rfl
      exact hcL.intervalIntegrable (μ := volume) (-T) T
    rw [this]
    exact (Complex.abs_re_le_norm _).trans h
  -- the digamma part
  have hlogc : Continuous fun y : ℝ ↦ Real.log (c ^ 2 + y ^ 2 / 4) :=
    Continuous.log (by fun_prop) fun y ↦ (by positivity : (0 : ℝ) < c ^ 2 + y ^ 2 / 4).ne'
  have hlogw : ∀ y : ℝ, Real.log ‖(c : ℂ) + ((y / 2 : ℝ) : ℂ) * I‖ =
      Real.log (c ^ 2 + y ^ 2 / 4) / 2 := by
    intro y
    have h : ‖(c : ℂ) + ((y / 2 : ℝ) : ℂ) * I‖ = Real.sqrt (c ^ 2 + y ^ 2 / 4) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      congr 1
      simp
      ring
    rw [h, Real.log_sqrt (by positivity)]
  have hΨ : |Ψ - (∫ y in (-T)..T, Real.log (c ^ 2 + y ^ 2 / 4)) / 2| ≤
      72 * Real.log ((2 + T) / 2) := by
    rw [← intervalIntegral.integral_div, hΨdef, ← intervalIntegral.integral_sub
      (hc3.intervalIntegrable _ _) ((hlogc.div_const 2).intervalIntegrable _ _),
      ← intervalIntegral_inv_two_add_abs hT0, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun y _ ↦ ?_)
      ((continuous_const.div (continuous_const.add continuous_abs) fun y ↦
        (by positivity : (0 : ℝ) < 2 + |y|).ne').intervalIntegrable _ _)
    rw [← hlogw, Real.norm_eq_abs]
    have h := abs_re_digamma_sub_log_le_half (w := (c : ℂ) + ((y / 2 : ℝ) : ℂ) * I)
      (by simp; linarith)
    have him : ((c : ℂ) + ((y / 2 : ℝ) : ℂ) * I).im = y / 2 := by simp
    rw [him, abs_div, abs_two] at h
    refine h.trans (le_of_eq ?_)
    field_simp
    ring
  have hD : |(∫ y in (-T)..T, Real.log (c ^ 2 + y ^ 2 / 4)) / 4 -
      (T / 2 * (2 * Real.log (T / 2)) - T)| ≤ 6 := by
    rw [integral_log_sq_add_sq hc0]
    have hT2 : 0 < T := by linarith
    have hodd : Real.arctan (-T / (2 * c)) = -Real.arctan (T / (2 * c)) := by
      rw [neg_div, Real.arctan_neg]
    rw [hodd]
    have e : Real.log (c ^ 2 + T ^ 2 / 4) =
        2 * Real.log (T / 2) + Real.log (1 + 4 * c ^ 2 / T ^ 2) := by
      rw [show c ^ 2 + T ^ 2 / 4 = (T / 2) ^ 2 * (1 + 4 * c ^ 2 / T ^ 2) by field_simp; ring,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    have e' : Real.log (c ^ 2 + (-T) ^ 2 / 4) = Real.log (c ^ 2 + T ^ 2 / 4) := by ring_nf
    rw [e', e]
    have hl0 : 0 ≤ Real.log (1 + 4 * c ^ 2 / T ^ 2) := Real.log_nonneg (by
      have : 0 ≤ 4 * c ^ 2 / T ^ 2 := by positivity
      linarith)
    have hl1 : Real.log (1 + 4 * c ^ 2 / T ^ 2) ≤ 4 * c ^ 2 / T ^ 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 4 * c ^ 2 / T ^ 2 by positivity)
      linarith
    have hl2 : T * Real.log (1 + 4 * c ^ 2 / T ^ 2) ≤ 4 := by
      calc T * Real.log (1 + 4 * c ^ 2 / T ^ 2) ≤ T * (4 * c ^ 2 / T ^ 2) := by gcongr
        _ = 4 * c ^ 2 / T := by field_simp
        _ ≤ 4 := by
            rw [div_le_iff₀ hT2]
            nlinarith
    have ha1' := Real.arctan_lt_pi_div_two (T / (2 * c))
    have hb1' := Real.neg_pi_div_two_lt_arctan (T / (2 * c))
    have hπ := Real.pi_lt_d2
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hT0 hl0]
  -- assemble
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlog : Real.log (N * T / (2 * π)) = Real.log N + Real.log (T / 2) - Real.log π := by
    rw [show (N : ℝ) * T / (2 * π) = N * (T / 2) / π by ring,
      Real.log_div (by positivity) Real.pi_pos.ne', Real.log_mul hN0.ne' (by positivity)]
  have hlogT2 : Real.log ((2 + T) / 2) ≤ Real.log T :=
    Real.log_le_log (by positivity) (by linarith)
  rw [hsplit, hlog]
  have hfin : |Z + 2 * T * (Real.log N / 2 - Real.log π / 2) + Ψ / 2 -
      (T * (Real.log N + Real.log (T / 2) - Real.log π) - T)| ≤
        C + 36 * Real.log ((2 + T) / 2) + 6 := by
    rw [abs_le] at hZb hΨ hD ⊢
    constructor <;> nlinarith
  refine hfin.trans ?_
  have h1 : C + 6 ≤ (C + 6) / Real.log 2 * Real.log T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith
  nlinarith

end NTKB
