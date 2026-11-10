/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import NTKB.Analytic.Davenport.Zeros.ZetaLocal

/-!
# Auxiliary facts for the explicit formula

**Davenport, Ch. 17.**

* (row 17-3) `ζ'(0)/ζ(0) = log 2π`;
* `‖ζ'/ζ(s)‖ ≤ -ζ'/ζ(σ₀)` for `σ ≥ σ₀ > 1`;
* `|tan z| ≤ 2` when `|Im z| ≥ 1` or `Re z ∈ πℤ`;
* (row 17-11, Davenport's (8)) for `σ ≤ -1`, `t ≠ 0`, and `|t| ≥ 1` or `σ` an odd integer:
  `|ζ'/ζ(s)| ≤ A log(|s| + 2)`, from the functional equation in logarithmic-derivative form
  (Mathlib's `logDeriv_riemannZeta_one_sub`). These are the parts of the left half-plane used in
  the explicit formula (the horizontal lines `t = ±T`, `T ≥ 2`, and the lines `σ = -U`, `U` odd).
-/

open Filter Topology Complex Set DirichletCharacter LSeries
open scoped Real LSeries.notation ArithmeticFunction.vonMangoldt

namespace NTKB

/-- **Davenport, Ch. 17, p. 104 (row 17-3)**: `ζ'(0)/ζ(0) = log 2π`. -/
@[kb "davenport1980" "Ch 17, p. 104"]
theorem Davenport.logDeriv_riemannZeta_zero :
    deriv riemannZeta 0 / riemannZeta 0 = Complex.log (2 * π) := by
  rw [deriv_riemannZeta_zero, riemannZeta_zero]
  field_simp

/-- `|ζ'/ζ(s)| ≤ -ζ'/ζ(σ₀)` for `Re s ≥ σ₀ > 1`. -/
lemma norm_logDeriv_riemannZeta_le_of_le {s : ℂ} {σ₀ : ℝ} (h1 : 1 < σ₀) (hs : σ₀ ≤ s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ -(deriv riemannZeta σ₀ / riemannZeta σ₀).re := by
  have hs1 : 1 < s.re := by linarith
  have h1' : 1 < ((σ₀ : ℝ) : ℂ).re := by simpa using h1
  have e := neg_logDeriv_LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) hs1
  have e0 := neg_logDeriv_LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) h1'
  rw [LFunction_modOne_eq] at e e0
  have s0 := Complex.reCLM.hasSum (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ 1) h1').LSeriesHasSum
  have hsre : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
  have hb : ∀ n, ‖term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) s n‖ ≤
      Complex.reCLM (term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) ((σ₀ : ℝ) : ℂ) n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have t0 := term_twist_vonMangoldt_eq (1 : DirichletCharacter ℂ 1) σ₀ 0 hn
    simp only [Complex.ofReal_zero, zero_mul, add_zero, neg_zero, Complex.exp_zero,
      mul_one] at t0
    have t1 := term_twist_vonMangoldt_eq (1 : DirichletCharacter ℂ 1) s.re s.im hn
    rw [← hsre] at t1
    rw [Complex.reCLM_apply, t0, t1, MulChar.one_apply (isUnit_of_subsingleton _)]
    have he : ‖Complex.exp (-(s.im * Real.log n) * I)‖ = 1 := by
      rw [show -((s.im : ℂ) * (Real.log n : ℝ)) * I = ((-(s.im * Real.log n)) : ℝ) * I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hc : 0 ≤ Λ n * (n : ℝ) ^ (-s.re) := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg n.cast_nonneg _)
    rw [norm_mul, norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg hc]
    simp only [one_mul, Complex.ofReal_re, norm_one]
    exact mul_le_mul_of_nonneg_left hpow ArithmeticFunction.vonMangoldt_nonneg
  have := tsum_of_norm_bounded s0 hb
  rw [← LSeries, ← e] at this
  rw [← e0, neg_div, norm_neg, Complex.reCLM_apply, neg_div, Complex.neg_re] at this
  exact this

/-- `|sin(x + iy)|² = sin² x + sinh² y` and `|cos(x + iy)|² = cos² x + sinh² y`. -/
lemma normSq_sin_cos (x y : ℝ) :
    Complex.normSq (Complex.sin (x + y * I)) = Real.sin x ^ 2 + Real.sinh y ^ 2 ∧
      Complex.normSq (Complex.cos (x + y * I)) = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sin_add_mul_I, Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  have hc := Real.cosh_sq y
  constructor
  · rw [Complex.normSq_apply]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, I_im, mul_one,
      zero_mul, add_im, mul_im, zero_add, sub_self]
    nlinarith [Real.sin_sq_add_cos_sq x]
  · rw [Complex.normSq_apply]
    simp only [sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, I_im, mul_one,
      zero_mul, sub_im, mul_im, zero_add, sub_self]
    nlinarith [Real.sin_sq_add_cos_sq x]

/-- `|tan z| ≤ 2` when `|Im z| ≥ 1` or `cos(Re z) = ±1`. -/
lemma norm_tan_le_two {z : ℂ} (h : 1 ≤ |z.im| ∨ Real.cos z.re ^ 2 = 1) : ‖Complex.tan z‖ ≤ 2 := by
  obtain ⟨hs, hc⟩ := normSq_sin_cos z.re z.im
  rw [Complex.re_add_im] at hs hc
  have hsin := Real.sin_sq_add_cos_sq z.re
  have hS : 0 ≤ Real.sinh z.im ^ 2 := sq_nonneg _
  have key : Complex.normSq (Complex.sin z) ≤ 4 * Complex.normSq (Complex.cos z) ∧
      0 < Complex.normSq (Complex.cos z) := by
    rcases h with h | h
    · have h2 : 3 / 4 ≤ Real.sinh 1 := by
        rw [Real.sinh_eq]
        have := Real.exp_one_gt_d9
        have h3 : Real.exp (-1) ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
        linarith
      have h4 : Real.sinh 1 ≤ |Real.sinh z.im| := by
        rcases le_or_gt 0 z.im with hy | hy
        · rw [abs_of_nonneg hy] at h
          rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr hy)]
          exact Real.sinh_le_sinh.mpr h
        · rw [abs_of_neg hy] at h
          rw [abs_of_neg (Real.sinh_neg_iff.mpr hy), ← Real.sinh_neg]
          exact Real.sinh_le_sinh.mpr h
      have h1 : 9 / 16 ≤ Real.sinh z.im ^ 2 := by
        have := mul_le_mul h4 h4 (by linarith) (abs_nonneg _)
        rw [abs_mul_abs_self] at this; nlinarith
      constructor <;> nlinarith [sq_nonneg (Real.cos z.re)]
    · constructor <;> nlinarith
  have hcos : Complex.cos z ≠ 0 := fun h0 ↦ by
    rw [h0, Complex.normSq_zero] at key; exact lt_irrefl _ key.2
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  rw [div_le_iff₀ (norm_pos_iff.mpr hcos)]
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Complex.sq_norm, Complex.sq_norm]
  linarith [key.1]

/-- **Davenport, Ch. 17, p. 108, (8) (row 17-11)**: there is `A` such that
`|ζ'/ζ(s)| ≤ A log(|s| + 2)` for `σ ≤ -1`, `t ≠ 0`, when `|t| ≥ 1` or `σ` is an odd negative
integer (these sets stay at distance `≥ 1/2` from the trivial zeros `-2, -4, …`). -/
@[kb "davenport1980" "Ch 17, p. 108"]
theorem Davenport.norm_logDeriv_riemannZeta_left_le :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, s.re ≤ -1 → s.im ≠ 0 → (1 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -(2 * k + 1)) →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ A * Real.log (‖s‖ + 2) := by
  have hC := zetaLogDerivTwo_nonneg
  have hπ := Real.pi_gt_three
  have hlog2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith)
  refine ⟨zetaLogDerivTwo + Real.log (2 * π) + 4 + π + 2, by positivity, fun s hσ ht hcase ↦ ?_⟩
  set w := 1 - s with hw
  have hwre : w.re = 1 - s.re := by simp [w]
  have hwim : w.im = -s.im := by simp [w]
  have hwZ : ∀ n : ℤ, w ≠ n := fun n h ↦ ht (by
    have := congrArg Complex.im h; rw [hwim] at this; simpa using this)
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hwre]; linarith)
  have hfe := logDeriv_riemannZeta_one_sub hwZ hzw
  rw [show 1 - w = s by simp [w]] at hfe
  have hs : deriv riemannZeta s / riemannZeta s = -logDeriv riemannZeta w + Complex.log (2 * π) -
      Complex.digamma w + π / 2 * Complex.tan (π * w / 2) := by
    rw [← logDeriv_apply]; linear_combination hfe
  rw [hs]
  -- the four bounds
  have b1 : ‖logDeriv riemannZeta w‖ ≤ zetaLogDerivTwo := by
    rw [logDeriv_apply]
    have := norm_logDeriv_riemannZeta_le_of_le (s := w) (σ₀ := 2) (by norm_num)
      (by rw [hwre]; linarith)
    simpa [zetaLogDerivTwo] using this
  have b2 : ‖Complex.log (2 * π)‖ = Real.log (2 * π) := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_of_nonneg hlog2π]
  have hw1 : 1 ≤ ‖w‖ := by have := Complex.re_le_norm w; linarith
  have b3 := norm_digamma_le (by rw [hwre]; linarith) hw1
  have b4 : ‖(π : ℂ) / 2 * Complex.tan (π * w / 2)‖ ≤ π := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_two]
    have ht2 : ‖Complex.tan (π * w / 2)‖ ≤ 2 := by
      apply norm_tan_le_two
      rcases hcase with h1 | ⟨k, hk⟩
      · left
        have : (π * w / 2 : ℂ).im = π * w.im / 2 := by simp
        rw [this, hwim, abs_div, abs_mul, abs_neg, abs_of_pos Real.pi_pos, abs_two]
        nlinarith
      · right
        have : (π * w / 2 : ℂ).re = (k + 1) * π := by
          simp only [mul_div_assoc]
          rw [Complex.re_ofReal_mul]
          simp [hwre, hk]; ring
        rw [this, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
          Real.cos_nat_mul_pi]
        rw [← pow_mul, mul_comm, pow_mul]; simp
    calc π / 2 * ‖Complex.tan (π * w / 2)‖ ≤ π / 2 * 2 := by gcongr
      _ = π := by ring
  have hwn : ‖w‖ ≤ ‖s‖ + 1 := by
    have := norm_sub_le (1 : ℂ) s; rw [norm_one] at this; simp only [w]; linarith
  have hlw : Real.log (‖w‖ + 1) ≤ Real.log (‖s‖ + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hL : 1 ≤ Real.log (‖s‖ + 2) := by
    have h3 : (3 : ℝ) ≤ ‖s‖ + 2 := by
      have := Complex.abs_re_le_norm s
      rw [abs_of_neg (by linarith)] at this; linarith
    have : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith [Real.log_le_log (by norm_num) h3]
  calc ‖-logDeriv riemannZeta w + Complex.log (2 * π) - Complex.digamma w +
        π / 2 * Complex.tan (π * w / 2)‖
      ≤ ‖logDeriv riemannZeta w‖ + ‖Complex.log (2 * π)‖ + ‖Complex.digamma w‖ +
          ‖(π : ℂ) / 2 * Complex.tan (π * w / 2)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        rw [norm_neg]
    _ ≤ zetaLogDerivTwo + Real.log (2 * π) + (4 + 2 * Real.log (‖s‖ + 2)) + π := by
        rw [b2]; linarith
    _ ≤ (zetaLogDerivTwo + Real.log (2 * π) + 4 + π + 2) * Real.log (‖s‖ + 2) := by
        nlinarith

end NTKB
