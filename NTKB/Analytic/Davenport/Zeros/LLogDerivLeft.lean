/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroCountVertical
import NTKB.Analytic.Davenport.Zeros.ExplicitAux

/-!
# `L'/L(s, χ)` in the half-plane `σ ≤ -1`

**Davenport, Ch. 19, p. 116 (row 19-5).** For `χ` primitive mod `q > 1` and `σ ≤ -1` away from
the trivial zeros, `L'/L(s, χ) = O(log(q|s|))` (`Davenport.norm_logDeriv_LFunction_left_le`). As
in Davenport, this comes from the functional equation, here in the form
`ξ'/ξ(1 - s, χ) = -ξ'/ξ(s, χ̄)`:
`L'/L(s, χ) = -L'/L(1 - s, χ̄) - log(q/π) - ½ ψ((1 - s + a)/2) - ½ ψ(1 - (s + a)/2)
  + (π/2) cot(π(s + a)/2)`,
with the reflection formula for `ψ`. As for `ζ` (17-11), "away from the trivial zeros" is taken
to mean `|t| ≥ 1` or `σ + a` an odd negative integer (midway between two trivial zeros
`-a - 2m`): these are the parts of the half-plane used in contour arguments.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

/-- `|cot z| ≤ 2` when `|Im z| ≥ 1` or `sin(Re z) = ±1`. -/
lemma norm_cot_le_two {z : ℂ} (h : 1 ≤ |z.im| ∨ Real.sin z.re ^ 2 = 1) : ‖Complex.cot z‖ ≤ 2 := by
  obtain ⟨hs, hc⟩ := normSq_sin_cos z.re z.im
  rw [Complex.re_add_im] at hs hc
  have hsin := Real.sin_sq_add_cos_sq z.re
  have hS : 0 ≤ Real.sinh z.im ^ 2 := sq_nonneg _
  have key : Complex.normSq (Complex.cos z) ≤ 4 * Complex.normSq (Complex.sin z) ∧
      0 < Complex.normSq (Complex.sin z) := by
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
      constructor <;> nlinarith [sq_nonneg (Real.sin z.re)]
    · constructor <;> nlinarith
  have hsin0 : Complex.sin z ≠ 0 := fun h0 ↦ by
    rw [h0, Complex.normSq_zero] at key; exact lt_irrefl _ key.2
  rw [Complex.cot_eq_cos_div_sin, norm_div]
  rw [div_le_iff₀ (norm_pos_iff.mpr hsin0)]
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Complex.sq_norm, Complex.sq_norm]
  linarith [key.1]

lemma norm_logDeriv_LFunction_le_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 2 ≤ s.re) : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ zetaLogDerivTwo := by
  refine (norm_logDeriv_LFunction_le χ (by linarith)).trans ?_
  have h := norm_logDeriv_riemannZeta_le_of_le (s := (s.re : ℂ)) (σ₀ := 2) (by norm_num)
    (by simpa using hs)
  have h2 : -(deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)).re ≤
      ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  simp only [zetaLogDerivTwo]
  linarith

variable {N : ℕ} [NeZero N]

/-- **Davenport, Ch. 19, p. 116 (row 19-5)**: there is an absolute `A` such that for `χ`
primitive mod `q > 1` and `σ ≤ -1` with `|t| ≥ 1` or `σ + a` an odd negative integer,
`|L'/L(s, χ)| ≤ A (log q + log(|s| + 2))`. -/
@[kb "davenport1980" "Ch 19, p. 116"]
theorem Davenport.norm_logDeriv_LFunction_left_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ s : ℂ, s.re ≤ -1 →
      (1 ≤ |s.im| ∨ ∃ k : ℕ, s.re + (dirichletParity χ).re = -(2 * k + 1)) →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ A * (Real.log N + Real.log (‖s‖ + 2)) := by
  have hC := zetaLogDerivTwo_nonneg
  have hπ3 := Real.pi_gt_three
  refine ⟨zetaLogDerivTwo + 10 + 2 * π, by positivity, fun {N} _ {χ} hχ hN s hσ hcase ↦ ?_⟩
  have hχ1 := ne_one_of_isPrimitive hχ hN
  have hχ1' : χ⁻¹ ≠ 1 := fun h ↦ hχ1 (inv_eq_one.mp h)
  set a := dirichletParity χ with ha
  have ha0 : 0 ≤ a.re := dirichletParity_re_nonneg χ
  have ha1 : a.re ≤ 1 := dirichletParity_re_le_one χ
  have hai : a.im = 0 := dirichletParity_im χ
  have hainv : dirichletParity χ⁻¹ = a := dirichletParity_inv χ
  have hanorm : ‖a‖ ≤ 1 := by
    have hare : a = ((a.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hai])
    rw [hare, Complex.norm_real, Real.norm_of_nonneg ha0]; exact ha1
  set w := (s + a) / 2 with hw
  have hwre : w.re = (s.re + a.re) / 2 := by simp [w]
  have hwim : w.im = s.im / 2 := by simp [w, hai]
  have hwZ : ∀ n : ℤ, w ≠ n := by
    intro n h
    rcases hcase with h1 | ⟨k, hk⟩
    · have := congrArg Complex.im h
      rw [hwim] at this; simp at this
      rw [show s.im = 0 by linarith] at h1; norm_num at h1
    · have := congrArg Complex.re h
      rw [hwre, hk] at this; simp at this
      have h2 : (2 * n + 2 * k + 1 : ℝ) = 0 := by linarith
      have h3 : (2 * n + 2 * k + 1 : ℤ) = 0 := by exact_mod_cast h2
      omega
  have hpar : ∀ m : ℕ, s + a ≠ -(2 * m) := fun m h ↦ hwZ (-m) (by
    rw [hw, h]; push_cast; ring)
  have h1s : 1 ≤ (1 - s).re := by simp; linarith
  have hξ : dirichletXi χ s ≠ 0 := by
    rw [show s = 1 - (1 - s) by ring, dirichletXi_one_sub hχ]
    exact mul_ne_zero (rootNumber_ne_zero hχ) (dirichletXi_ne_zero_of_one_le_re hχ1' hN h1s)
  have hG : Gammaℝ (s + a) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff, not_exists]; exact hpar
  have hL : LFunction χ s ≠ 0 := by
    intro e; apply hξ
    rw [dirichletXi_eq_mul_LFunction χ hN hG, e, mul_zero]
  have e1 := logDeriv_dirichletXi_eq hχ hN hpar hL hξ
  rw [← ha, ← hw] at e1
  have e2 := logDeriv_dirichletXi_one_sub hχ hN (1 - s)
  rw [show 1 - (1 - s) = s by ring] at e2
  have hpar' : ∀ m : ℕ, (1 - s) + dirichletParity χ⁻¹ ≠ -(2 * m) := by
    intro m h
    have := congrArg Complex.re h
    rw [hainv] at this
    simp at this
    linarith [m.cast_nonneg (α := ℝ)]
  have hL' := LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχ1') h1s
  have hξ' := dirichletXi_ne_zero_of_one_le_re hχ1' hN h1s
  have e3 := logDeriv_dirichletXi_eq hχ.inv hN hpar' hL' hξ'
  rw [hainv] at e3
  have e4 := Complex.digamma_one_sub hwZ
  have hform : deriv (LFunction χ) s / LFunction χ s =
      -(deriv (LFunction χ⁻¹) (1 - s) / LFunction χ⁻¹ (1 - s)) - Complex.log N +
        Complex.log π - Complex.digamma ((1 - s + a) / 2) / 2 -
          Complex.digamma (1 - w) / 2 + (π / 2) * Complex.cot (π * w) := by
    rw [e4]
    linear_combination -e1 + e2 - e3
  rw [hform]
  -- the bounds
  have hs1 : 1 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s; rw [abs_of_neg (by linarith)] at this; linarith
  have hL1 : 1 ≤ Real.log (‖s‖ + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have b1 : ‖deriv (LFunction χ⁻¹) (1 - s) / LFunction χ⁻¹ (1 - s)‖ ≤ zetaLogDerivTwo :=
    norm_logDeriv_LFunction_le_two χ⁻¹ (by simp; linarith)
  have b2 : ‖Complex.log N‖ = Real.log N := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg N), Complex.norm_real,
      Real.norm_of_nonneg hlogN]
  have b3 : ‖Complex.log π‖ ≤ 2 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_of_nonneg
      (Real.log_nonneg (by linarith))]
    rw [Real.log_le_iff_le_exp Real.pi_pos]
    have h := Real.exp_one_gt_d9
    have e2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have hee : 7 < Real.exp 2 := by rw [e2']; nlinarith
    have := Real.pi_lt_d2
    linarith
  have hu : ‖(1 - s + a) / 2‖ ≤ ‖s‖ + 1 := by
    have h1 := norm_add_le (1 - s) a
    have h2 := norm_sub_le (1 : ℂ) s
    have h3 : ‖a‖ ≤ 1 := hanorm
    rw [norm_div, Complex.norm_ofNat, norm_one] at *
    linarith
  have hu1 : 1 ≤ ‖(1 - s + a) / 2‖ := by
    have := Complex.re_le_norm ((1 - s + a) / 2)
    have hre : ((1 - s + a) / 2).re = (1 - s.re + a.re) / 2 := by simp
    rw [hre] at this; linarith
  have b4 := norm_digamma_le (w := (1 - s + a) / 2) (by simp; linarith) hu1
  have hv : ‖1 - w‖ ≤ ‖s‖ + 1 := by
    have h1 := norm_sub_le (1 : ℂ) w
    have h2 : ‖w‖ ≤ (‖s‖ + 1) / 2 := by
      have := norm_add_le s a
      have h3 : ‖a‖ ≤ 1 := hanorm
      rw [hw, norm_div, Complex.norm_ofNat]; linarith
    rw [norm_one] at h1; linarith
  have hv1 : 1 ≤ ‖1 - w‖ := by
    have := Complex.re_le_norm (1 - w)
    have hre : (1 - w).re = 1 - (s.re + a.re) / 2 := by simp [hwre]
    rw [hre] at this; linarith
  have b5 := norm_digamma_le (w := 1 - w) (by simp [hwre]; linarith) hv1
  have b6 : ‖(π / 2 : ℂ) * Complex.cot (π * w)‖ ≤ π := by
    rw [norm_mul, show (π / 2 : ℂ) = ((π / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    have hc : ‖Complex.cot (π * w)‖ ≤ 2 := by
      apply norm_cot_le_two
      rcases hcase with h1 | ⟨k, hk⟩
      · left
        have : ((π : ℂ) * w).im = π * (s.im / 2) := by
          rw [Complex.im_ofReal_mul, hwim]
        rw [this, abs_mul, abs_of_pos Real.pi_pos, abs_div, abs_two]
        nlinarith
      · right
        have : ((π : ℂ) * w).re = -((2 * k + 1) * π / 2) := by
          rw [Complex.re_ofReal_mul, hwre, hk]; ring
        rw [this, Real.sin_neg, neg_sq]
        have hcos : Real.cos ((2 * k + 1) * π / 2) = 0 := by
          rw [Real.cos_eq_zero_iff]; exact ⟨k, by push_cast; ring⟩
        have := Real.sin_sq_add_cos_sq ((2 * k + 1) * π / 2)
        rw [hcos] at this; linarith
    nlinarith
  have hlu : Real.log (‖(1 - s + a) / 2‖ + 1) ≤ Real.log (‖s‖ + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlv : Real.log (‖1 - w‖ + 1) ≤ Real.log (‖s‖ + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsum : ‖-(deriv (LFunction χ⁻¹) (1 - s) / LFunction χ⁻¹ (1 - s)) - Complex.log N +
        Complex.log π - Complex.digamma ((1 - s + a) / 2) / 2 -
          Complex.digamma (1 - w) / 2 + (π / 2) * Complex.cot (π * w)‖ ≤
      zetaLogDerivTwo + Real.log N + 2 + (4 + 2 * Real.log (‖s‖ + 2)) / 2 +
        (4 + 2 * Real.log (‖s‖ + 2)) / 2 + π := by
    have k1 := norm_add_le (-(deriv (LFunction χ⁻¹) (1 - s) / LFunction χ⁻¹ (1 - s)) -
      Complex.log N + Complex.log π - Complex.digamma ((1 - s + a) / 2) / 2 -
        Complex.digamma (1 - w) / 2) ((π / 2) * Complex.cot (π * w))
    have k2 := norm_sub_le (-(deriv (LFunction χ⁻¹) (1 - s) / LFunction χ⁻¹ (1 - s)) -
      Complex.log N + Complex.log π - Complex.digamma ((1 - s + a) / 2) / 2)
        (Complex.digamma (1 - w) / 2)
    have k3 := norm_sub_le (-(deriv (LFunction χ⁻¹) (1 - s) / LFunction χ⁻¹ (1 - s)) -
      Complex.log N + Complex.log π) (Complex.digamma ((1 - s + a) / 2) / 2)
    have k4 := norm_add_le (-(deriv (LFunction χ⁻¹) (1 - s) / LFunction χ⁻¹ (1 - s)) -
      Complex.log N) (Complex.log π)
    have k5 := norm_sub_le (-(deriv (LFunction χ⁻¹) (1 - s) / LFunction χ⁻¹ (1 - s)))
      (Complex.log N)
    rw [norm_neg] at k5
    have d1 : ‖Complex.digamma ((1 - s + a) / 2) / 2‖ ≤ (4 + 2 * Real.log (‖s‖ + 2)) / 2 := by
      rw [norm_div, Complex.norm_ofNat]; linarith
    have d2 : ‖Complex.digamma (1 - w) / 2‖ ≤ (4 + 2 * Real.log (‖s‖ + 2)) / 2 := by
      rw [norm_div, Complex.norm_ofNat]; linarith
    linarith
  refine hsum.trans ?_
  nlinarith

end NTKB
