/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitAux
import NTKB.Analytic.Davenport.Zeros.LLogDerivLeft

/-!
# `ζ'/ζ` and `L'/L` in the left half-plane, outside discs about the trivial zeros

**Davenport, Ch. 17, p. 108, (8) (row 17-11).** `ζ'/ζ(s) = O(log 2|s|)` for `σ ≤ -1`, outside the discs
of radius `1/2` about the trivial zeros `-2, -4, …`.

**Davenport, Ch. 19, p. 116 (row 19-5).** For `χ` primitive mod `q > 1`, `L'/L(s, χ) = O(log q|s|)` for
`σ ≤ -1`, outside the discs of radius `1/2` about the trivial zeros `-a, -a - 2, -a - 4, …`.

Both from the unsymmetric functional equation in logarithmic-derivative form, as in
`NTKB.Davenport.norm_logDeriv_riemannZeta_left_le` and `NTKB.Davenport.norm_logDeriv_LFunction_left_le`
(which cover `|t| ≥ 1` and the lines `σ + a = -(2k + 1)`); the new ingredient is the bound for
`cot(πz/2)` (resp. `tan`) at distance `≥ 1/2` from its poles, and continuity on the real axis.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB


/-- `|cot(π z)| ≤ 10` when `z` stays at distance `≥ 1/4` from every integer. -/
lemma norm_cot_pi_le_ten {z : ℂ} (h : ∀ n : ℤ, 1 / 4 ≤ ‖z - n‖) :
    ‖Complex.cot (π * z)‖ ≤ 10 := by
  have hz : (π * z : ℂ) = ((π * z.re : ℝ) : ℂ) + ((π * z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  obtain ⟨hs, hc⟩ := normSq_sin_cos (π * z.re) (π * z.im)
  rw [← hz] at hs hc
  have hsin := Real.sin_sq_add_cos_sq (π * z.re)
  have hS := sq_nonneg (Real.sinh (π * z.im))
  have hπ := Real.pi_gt_three
  have key : Complex.normSq (Complex.cos (π * z)) ≤ 100 * Complex.normSq (Complex.sin (π * z)) ∧
      0 < Complex.normSq (Complex.sin (π * z)) := by
    rw [hs, hc]
    by_cases hy : 3 / 8 ≤ |π * z.im|
    · have h4 : 3 / 8 ≤ |Real.sinh (π * z.im)| := by
        rcases le_or_gt 0 (π * z.im) with hy0 | hy0
        · rw [abs_of_nonneg hy0] at hy
          rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr hy0)]
          exact hy.trans (Real.self_le_sinh_iff.mpr hy0)
        · rw [abs_of_neg hy0] at hy
          rw [abs_of_neg (Real.sinh_neg_iff.mpr hy0), ← Real.sinh_neg]
          exact hy.trans (Real.self_le_sinh_iff.mpr (by linarith))
      have h1 : 9 / 64 ≤ Real.sinh (π * z.im) ^ 2 := by
        have := mul_le_mul h4 h4 (by norm_num) (abs_nonneg _)
        rw [abs_mul_abs_self] at this; nlinarith
      constructor <;> nlinarith [sq_nonneg (Real.cos (π * z.re)), sq_nonneg (Real.sin (π * z.re))]
    · push Not at hy
      have him : z.im ^ 2 < 1 / 64 := by
        have : |π * z.im| = π * |z.im| := by rw [abs_mul, abs_of_pos Real.pi_pos]
        rw [this] at hy
        have h2 : |z.im| < 1 / 8 := by nlinarith [abs_nonneg z.im]
        nlinarith [sq_abs z.im, abs_nonneg z.im]
      set e := z.re - round z.re with he
      have he1 : |e| ≤ 1 / 2 := abs_sub_round z.re
      have h14 := h (round z.re)
      have hnorm : ‖z - (round z.re : ℤ)‖ ^ 2 = e ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp [he]; ring
      have he2 : 1 / 5 ≤ |e| := by
        by_contra hc'
        push Not at hc'
        nlinarith [sq_abs e, abs_nonneg e]
      have hsq : Real.sin (π * z.re) ^ 2 = Real.sin (π * |e|) ^ 2 := by
        have h1 : π * z.re = π * e + (round z.re : ℤ) * π := by rw [he]; ring
        have hsg : ((-1 : ℝ) ^ round z.re) ^ 2 = 1 := by
          rcases Int.even_or_odd (round z.re) with h0 | h0
          · rw [h0.neg_one_zpow]; norm_num
          · rw [h0.neg_one_zpow]; norm_num
        rw [h1, Real.sin_add_int_mul_pi, mul_pow, hsg, one_mul]
        rcases le_or_gt 0 e with h0 | h0
        · rw [abs_of_nonneg h0]
        · rw [abs_of_neg h0, mul_neg, Real.sin_neg, neg_sq]
      have hj := Real.mul_le_sin (x := π * |e|) (by positivity) (by nlinarith)
      have hj2 : 2 / 5 ≤ Real.sin (π * |e|) := by
        have : 2 / π * (π * |e|) = 2 * |e| := by field_simp
        rw [this] at hj; linarith
      have hj3 : 4 / 25 ≤ Real.sin (π * z.re) ^ 2 := by rw [hsq]; nlinarith
      constructor <;> nlinarith [sq_nonneg (Real.cos (π * z.re))]
  have hsin0 : Complex.sin (π * z) ≠ 0 := fun h0 ↦ by
    rw [h0, Complex.normSq_zero] at key; exact lt_irrefl _ key.2
  rw [Complex.cot_eq_cos_div_sin, norm_div]
  rw [div_le_iff₀ (norm_pos_iff.mpr hsin0)]
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Complex.sq_norm, Complex.sq_norm]
  linarith [key.1]

lemma tan_pi_one_sub_div_two (s : ℂ) :
    Complex.tan (π * (1 - s) / 2) = Complex.cot (π * (s / 2)) := by
  rw [show (π : ℂ) * (1 - s) / 2 = π / 2 - π * (s / 2) by ring, Complex.tan_eq_sin_div_cos,
    Complex.sin_pi_div_two_sub, Complex.cos_pi_div_two_sub, Complex.cot_eq_cos_div_sin]

lemma disc_half_zeta {s : ℂ} (hσ : s.re ≤ -1) (hd : ∀ m : ℕ, 1 / 2 ≤ ‖s + 2 * ((m : ℂ) + 1)‖)
    (n : ℤ) : 1 / 4 ≤ ‖s / 2 - n‖ := by
  rcases le_or_gt 0 n with hn | hn
  · have := Complex.abs_re_le_norm (s / 2 - n)
    have h2 : (s / 2 - n).re = s.re / 2 - n := by simp
    rw [h2, abs_of_neg (by have : (0 : ℝ) ≤ n := by exact_mod_cast hn
                           linarith)] at this
    have : (0 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
    have := hd m
    have e : s / 2 - n = (s + 2 * ((m : ℂ) + 1)) / 2 := by rw [hm]; push_cast; ring
    rw [e, norm_div, Complex.norm_ofNat]; linarith

/-- The case `Im s ≠ 0` of (17-11). -/
lemma zeta_left_aux :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, s.re ≤ -1 → s.im ≠ 0 → (∀ n : ℤ, 1 / 4 ≤ ‖s / 2 - n‖) →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ A * Real.log (‖s‖ + 2) := by
  have hC := zetaLogDerivTwo_nonneg
  have hπ := Real.pi_gt_three
  have hlog2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith)
  refine ⟨zetaLogDerivTwo + Real.log (2 * π) + 4 + 5 * π + 2, by positivity,
    fun s hσ ht hcase ↦ ?_⟩
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
  have b4 : ‖(π : ℂ) / 2 * Complex.tan (π * w / 2)‖ ≤ 5 * π := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Complex.norm_two]
    have ht2 : ‖Complex.tan (π * w / 2)‖ ≤ 10 := by
      rw [hw, tan_pi_one_sub_div_two]
      exact norm_cot_pi_le_ten hcase
    calc π / 2 * ‖Complex.tan (π * w / 2)‖ ≤ π / 2 * 10 := by gcongr
      _ = 5 * π := by ring
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
    _ ≤ zetaLogDerivTwo + Real.log (2 * π) + (4 + 2 * Real.log (‖s‖ + 2)) + 5 * π := by
        rw [b2]; linarith
    _ ≤ (zetaLogDerivTwo + Real.log (2 * π) + 4 + 5 * π + 2) * Real.log (‖s‖ + 2) := by
        nlinarith

lemma zeta_ne_zero_of_disc {s : ℂ} (hσ : s.re ≤ -1)
    (hd : ∀ m : ℕ, 1 / 2 ≤ ‖s + 2 * ((m : ℂ) + 1)‖) : riemannZeta s ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos (by linarith)).mp h
  have := hd n
  rw [hn] at this
  simp at this
  linarith

lemma continuousAt_deriv_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    ContinuousAt (deriv riemannZeta) s := by
  have han : AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun t ht ↦ (differentiableAt_riemannZeta ht).differentiableWithinAt) isOpen_compl_singleton
  exact (han.deriv s hs).continuousAt

/-- **Davenport, Ch. 17, p. 108, (8) (row 17-11)**: there is `A` with `|ζ'/ζ(s)| ≤ A log(|s| + 2)`
for every `s` with `σ ≤ -1` and `|s + 2m| ≥ 1/2` for every `m ≥ 1`. -/
@[kb "davenport1980" "Ch 17, p. 108"]
theorem Davenport.norm_logDeriv_riemannZeta_left_disc_le :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, s.re ≤ -1 → (∀ m : ℕ, 1 / 2 ≤ ‖s + 2 * ((m : ℂ) + 1)‖) →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ A * Real.log (‖s‖ + 2) := by
  obtain ⟨A, hA, hAs⟩ := zeta_left_aux
  refine ⟨A, hA, fun s hσ hd ↦ ?_⟩
  by_cases him : s.im = 0
  · have hs1 : s ≠ 1 := fun h ↦ by rw [h] at hσ; simp at hσ; linarith
    have hz := zeta_ne_zero_of_disc hσ hd
    set u : ℕ → ℂ := fun k ↦ s + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I with hu_def
    have hu : Tendsto u atTop (𝓝 s) := by
      have h0 : Tendsto (fun k : ℕ ↦ ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 0) := by
        have := ((Complex.continuous_ofReal.tendsto 0).comp
          tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
        simpa using this
      rw [show (𝓝 s) = 𝓝 (s + 0) by simp]; exact tendsto_const_nhds.add h0
    have hf : ContinuousAt (fun t ↦ ‖deriv riemannZeta t / riemannZeta t‖) s :=
      ((continuousAt_deriv_riemannZeta hs1).div
        (differentiableAt_riemannZeta hs1).continuousAt hz).norm
    have hg : ContinuousAt (fun t : ℂ ↦ A * Real.log (‖t‖ + 2)) s :=
      continuousAt_const.mul (ContinuousAt.log (by fun_prop) (by positivity))
    refine le_of_tendsto_of_tendsto (hf.tendsto.comp hu) (hg.tendsto.comp hu)
      (Eventually.of_forall fun k ↦ ?_)
    have hure : (u k).re = s.re := by simp [hu_def]
    have huim : (u k).im ≠ 0 := by
      simp [hu_def, him]
      have : (k : ℝ) + 1 ≠ 0 := by positivity
      exact ⟨this, by exact_mod_cast Nat.succ_ne_zero k⟩
    have hd' : ∀ m : ℕ, 1 / 2 ≤ ‖u k + 2 * ((m : ℂ) + 1)‖ := by
      intro m
      have e : s + 2 * ((m : ℂ) + 1) = (((s + 2 * ((m : ℂ) + 1)).re : ℝ) : ℂ) :=
        Complex.ext (by simp) (by simp [him])
      have h1 := hd m
      rw [e, Complex.norm_real, Real.norm_eq_abs] at h1
      refine h1.trans ?_
      have := Complex.abs_re_le_norm (u k + 2 * ((m : ℂ) + 1))
      refine le_trans (le_of_eq ?_) this
      simp [hure]
    exact hAs (u k) (by rw [hure]; exact hσ) huim (disc_half_zeta (by rw [hure]; exact hσ) hd')
  · exact hAs s hσ him (disc_half_zeta hσ hd)

/-- **Davenport, Ch. 19, p. 116 (row 19-5)**: there is an absolute `A` such that for `χ` primitive
mod `q > 1` and every `s` with `σ ≤ -1` and `|s + a + 2m| ≥ 1/2` for every `m ≥ 0`
(`a = 0` or `1` the parity of `χ`), `|L'/L(s, χ)| ≤ A (log q + log(|s| + 2))`. -/
@[kb "davenport1980" "Ch 19, p. 116"]
theorem Davenport.norm_logDeriv_LFunction_left_disc_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ s : ℂ, s.re ≤ -1 → (∀ m : ℕ, 1 / 2 ≤ ‖s + dirichletParity χ + 2 * (m : ℂ)‖) →
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
        A * (Real.log N + Real.log (‖s‖ + 2)) := by
  have hC := zetaLogDerivTwo_nonneg
  have hπ3 := Real.pi_gt_three
  refine ⟨zetaLogDerivTwo + 10 + 5 * π, by positivity, fun {N} _ {χ} hχ hN s hσ hd ↦ ?_⟩
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
  have hdisc : ∀ n : ℤ, 1 / 4 ≤ ‖w - n‖ := by
    intro n
    rcases le_or_gt 1 n with hn | hn
    · have h1 := Complex.abs_re_le_norm (w - n)
      have h2 : (w - n).re = (s.re + a.re) / 2 - n := by simp [hwre]
      have h3 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [h2, abs_of_neg (by linarith)] at h1
      linarith
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
      have h1 := hd m
      have e : w - n = (s + a + 2 * (m : ℂ)) / 2 := by rw [hw, hm]; push_cast; ring
      rw [e, norm_div, Complex.norm_ofNat]; linarith
  have hwZ : ∀ n : ℤ, w ≠ n := fun n h ↦ by
    have := hdisc n; rw [h, sub_self, norm_zero] at this; norm_num at this
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
  have b6 : ‖(π / 2 : ℂ) * Complex.cot (π * w)‖ ≤ 5 * π := by
    rw [norm_mul, show (π / 2 : ℂ) = ((π / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    have hc : ‖Complex.cot (π * w)‖ ≤ 10 := norm_cot_pi_le_ten hdisc
    nlinarith [Real.pi_pos]
  have hlu : Real.log (‖(1 - s + a) / 2‖ + 1) ≤ Real.log (‖s‖ + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlv : Real.log (‖1 - w‖ + 1) ≤ Real.log (‖s‖ + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsum : ‖-(deriv (LFunction χ⁻¹) (1 - s) / LFunction χ⁻¹ (1 - s)) - Complex.log N +
        Complex.log π - Complex.digamma ((1 - s + a) / 2) / 2 -
          Complex.digamma (1 - w) / 2 + (π / 2) * Complex.cot (π * w)‖ ≤
      zetaLogDerivTwo + Real.log N + 2 + (4 + 2 * Real.log (‖s‖ + 2)) / 2 +
        (4 + 2 * Real.log (‖s‖ + 2)) / 2 + 5 * π := by
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
