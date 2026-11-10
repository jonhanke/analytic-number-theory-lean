/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitPrime

/-!
# Bounds for `-ζ'/ζ(s) x^s/s` on the sides of the rectangle

**Davenport, Ch. 17, pp. 108-109.** On the horizontal sides `t = ±T` (with `T` at distance
`≥ δ` from every ordinate) and on the left side `σ = -U` (`U` an odd integer) of the rectangle
with corners `-U ± iT`, `c ± iT`.
-/

open Filter Topology Complex Set MeasureTheory
open scoped Real Interval

namespace NTKB

lemma riemannZeta_ne_zero_of {s : ℂ} (hs1 : s ≠ 1) (hρ : ∀ ρ : ZeroIndex riemannXi, ρ.val ≠ s)
    (htriv : ∀ m : ℕ, s ≠ -(2 * ((m : ℂ) + 1))) : riemannZeta s ≠ 0 := fun hz ↦ by
  rcases riemannZeta_eq_zero_cases hz hs1 with ⟨m, hm⟩ | ⟨ρ, hρ'⟩
  · exact htriv m hm
  · exact hρ ρ hρ'

lemma continuousAt_explicitIntegrand {x : ℝ} (hx : 0 < x) {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0)
    (hz : riemannZeta s ≠ 0) : ContinuousAt (explicitIntegrand x) s := by
  have han := analyticAt_riemannZeta hs1
  exact (((han.deriv.differentiableAt.div han.differentiableAt hz).neg).mul
    (differentiableAt_perronKernel hx hs0)).continuousAt

/-- On a horizontal line `t = h` with `|h| ≥ 1`, avoiding the ordinates: `F` is continuous. -/
lemma continuous_explicitIntegrand_horiz {x : ℝ} (hx : 0 < x) {h : ℝ} (hh : 1 ≤ |h|)
    (hgood : ∀ ρ : ZeroIndex riemannXi, ρ.val.im ≠ h) :
    Continuous fun σ : ℝ ↦ explicitIntegrand x (σ + h * I) := by
  have hne : ∀ σ : ℝ, ((σ : ℂ) + h * I).im = h := fun σ ↦ by simp
  have hh0 : h ≠ 0 := fun h0 ↦ by rw [h0, abs_zero] at hh; norm_num at hh
  refine continuous_iff_continuousAt.mpr fun σ ↦ ?_
  refine ContinuousAt.comp (g := explicitIntegrand x) ?_
    (Complex.continuous_ofReal.add continuous_const).continuousAt
  have hs1 : (σ : ℂ) + h * I ≠ 1 := fun e ↦ hh0 (by simpa [hne] using congrArg Complex.im e)
  have hs0 : (σ : ℂ) + h * I ≠ 0 := fun e ↦ hh0 (by simpa [hne] using congrArg Complex.im e)
  refine continuousAt_explicitIntegrand hx hs1 hs0 (riemannZeta_ne_zero_of hs1 ?_ ?_)
  · intro ρ e; exact hgood ρ (by rw [e, hne])
  · intro m e; apply hh0; simpa using congrArg Complex.im e

/-- On the vertical line `σ = -(2K+1)`, `F` is continuous. -/
lemma continuous_explicitIntegrand_left {x : ℝ} (hx : 0 < x) (K : ℕ) :
    Continuous fun y : ℝ ↦ explicitIntegrand x (((-(2 * K + 1) : ℝ) : ℂ) + y * I) := by
  have hre : ∀ y : ℝ, ((((-(2 * K + 1) : ℝ) : ℂ) + y * I)).re = -(2 * K + 1) := fun y ↦ by simp
  have hK : (0 : ℝ) ≤ K := K.cast_nonneg
  refine continuous_iff_continuousAt.mpr fun y ↦ ?_
  refine ContinuousAt.comp (g := explicitIntegrand x) ?_
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  set s : ℂ := ((-(2 * K + 1) : ℝ) : ℂ) + y * I
  have hs1 : s ≠ 1 := fun e ↦ by have := congrArg Complex.re e; rw [hre] at this; simp at this; linarith
  have hs0 : s ≠ 0 := fun e ↦ by have := congrArg Complex.re e; rw [hre] at this; simp at this; linarith
  refine continuousAt_explicitIntegrand hx hs1 hs0 (riemannZeta_ne_zero_of hs1 ?_ ?_)
  · intro ρ e
    have := (riemannXi_zero_mem ρ).2.1
    rw [e, hre] at this; linarith
  · intro m e
    have := congrArg Complex.re e
    rw [hre] at this
    simp at this
    -- `2K + 1 = 2(m + 1)` is impossible
    have h2 : (2 * K + 1 : ℤ) = 2 * (m + 1) := by exact_mod_cast (by linarith : (2 * K + 1 : ℝ) = 2 * (m + 1))
    omega

/-- **Davenport, Ch. 17, p. 108 (from 17-10)**: on a horizontal line `t = h`, `|h| ≥ 2`,
`-1 ≤ σ ≤ 2`, at distance `≥ δ` from all ordinates, `|F(σ + ih)| ≤ A log(|h| + 2) x^σ / (δ |h|)`. -/
lemma norm_explicitIntegrand_horiz_near :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 < x → ∀ σ h δ : ℝ, -1 ≤ σ → σ ≤ 2 → 2 ≤ |h| → 0 < δ → δ ≤ 1 →
      (∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - h|) →
      ‖explicitIntegrand x (σ + h * I)‖ ≤ A * Real.log (|h| + 2) / δ * (x ^ σ / |h|) := by
  obtain ⟨A, hA, hb⟩ := Davenport.norm_logDeriv_riemannZeta_good_line
  refine ⟨A, hA, fun x hx σ h δ hσ1 hσ2 hh hδ hδ1 hgood ↦ ?_⟩
  have hh0 : h ≠ 0 := fun h0 ↦ by rw [h0, abs_zero] at hh; norm_num at hh
  have hre : ((σ : ℂ) + h * I).re = σ := by simp
  have him : ((σ : ℂ) + h * I).im = h := by simp
  have h1 := hb (σ + h * I) (by rw [hre]; exact hσ1) (by rw [hre]; exact hσ2) (by rw [him]; exact hh)
    δ hδ hδ1 (by rw [him]; exact hgood)
  rw [him] at h1
  rw [explicitIntegrand, norm_mul, norm_neg]
  exact mul_le_mul h1 (norm_perronKernel_le_horiz hx σ h hh0) (norm_nonneg _)
    (by have := Real.log_nonneg (by linarith [abs_nonneg h] : (1 : ℝ) ≤ |h| + 2); positivity)

/-- **Davenport, Ch. 17, p. 108 (from 17-11)**: for `σ ≤ -1`, `t ≠ 0`, and `|t| ≥ 1` or `σ` an odd
negative integer: `|F(s)| ≤ A log(|σ| + |t| + 2) |x^s/s|`. -/
lemma norm_explicitIntegrand_left :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 < x → ∀ s : ℂ, s.re ≤ -1 → s.im ≠ 0 →
      (1 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -(2 * k + 1)) →
      ‖explicitIntegrand x s‖ ≤ A * Real.log (|s.re| + |s.im| + 2) * ‖perronKernel x s‖ := by
  obtain ⟨A, hA, hb⟩ := Davenport.norm_logDeriv_riemannZeta_left_le
  refine ⟨A, hA, fun x hx s hσ ht hcase ↦ ?_⟩
  rw [explicitIntegrand, norm_mul, norm_neg]
  refine mul_le_mul_of_nonneg_right ((hb s hσ ht hcase).trans ?_) (norm_nonneg _)
  refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hA.le
  linarith [Complex.norm_le_abs_re_add_abs_im s]

/-- `log(a + b) ≤ log a + b` for `a ≥ 1`, `b ≥ 0`. -/
lemma log_add_le_log_add {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) : Real.log (a + b) ≤ Real.log a + b := by
  have ha0 : 0 < a := by linarith
  rw [show a + b = a * (1 + b / a) by field_simp, Real.log_mul ha0.ne' (by positivity)]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + b / a by positivity)
  have h2 : b / a ≤ b := div_le_self hb ha
  linarith

/-- `u ≤ 3 x^{u/2}` for `u ≥ 0`, `x ≥ 2`. -/
lemma le_three_mul_rpow_half {x u : ℝ} (hx : 2 ≤ x) (hu : 0 ≤ u) : u ≤ 3 * x ^ (u / 2) := by
  have hl2 := log_two_gt_two_thirds
  have h1 : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  rw [Real.rpow_def_of_pos (by linarith)]
  have h2 := Real.add_one_le_exp (Real.log x * (u / 2))
  have h3 : u / 3 ≤ Real.log x * (u / 2) := by nlinarith
  linarith

/-- `x^σ ≤ x^{σ/2}` and `|σ| x^σ ≤ 3 x^{σ/2}` for `σ ≤ 0`, `x ≥ 2`. -/
lemma rpow_le_rpow_half {x σ : ℝ} (hx : 2 ≤ x) (hσ : σ ≤ 0) : x ^ σ ≤ x ^ (σ / 2) :=
  Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

lemma abs_mul_rpow_le {x σ : ℝ} (hx : 2 ≤ x) (hσ : σ ≤ 0) : |σ| * x ^ σ ≤ 3 * x ^ (σ / 2) := by
  have hx0 : 0 < x := by linarith
  have h1 := le_three_mul_rpow_half hx (abs_nonneg σ)
  rw [abs_of_nonpos hσ] at h1 ⊢
  calc -σ * x ^ σ ≤ 3 * x ^ (-σ / 2) * x ^ σ := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 3 * x ^ (σ / 2) := by
      rw [mul_assoc, ← Real.rpow_add hx0]; ring_nf

/-- `∫_a^b x^{σ/2} dσ ≤ 2 x^{b/2} / log x` for `x > 1`. -/
lemma integral_rpow_half_le {x : ℝ} (hx : 1 < x) (a b : ℝ) :
    ∫ σ : ℝ in a..b, x ^ (σ / 2) ≤ 2 * x ^ (b / 2) / Real.log x := by
  have hx0 : 0 < x := by linarith
  set y := x ^ (1 / 2 : ℝ) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : 1 < y := Real.one_lt_rpow hx (by norm_num)
  have hfun : (fun σ : ℝ ↦ x ^ (σ / 2)) = fun σ ↦ y ^ σ := by
    funext σ; rw [hy, ← Real.rpow_mul hx0.le]; ring_nf
  have hlog : Real.log y = Real.log x / 2 := by
    rw [hy, Real.log_rpow hx0]; ring
  have hlx : 0 < Real.log x := Real.log_pos hx
  rw [hfun, integral_rpow_const hy0 hy1.ne' a b, hlog]
  have : y ^ b = x ^ (b / 2) := by rw [hy, ← Real.rpow_mul hx0.le]; ring_nf
  rw [this, div_div_eq_mul_div]
  have : 0 ≤ y ^ a := by positivity
  apply div_le_div_of_nonneg_right _ hlx.le
  nlinarith

/-- **Davenport, Ch. 17, p. 109**: the horizontal sides. There is `B` such that for `x ≥ 2`,
`1 < c ≤ 2`, `U ≥ 1`, `|h| ≥ 2` and `h` at distance `≥ δ` from all ordinates,
`|∫_{-U}^{c} F(σ + ih) dσ| ≤ B x^c log(|h| + 2) / (δ |h| log x)`. -/
lemma norm_integral_explicitIntegrand_horiz :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 2 ≤ x → ∀ c h δ U : ℝ, 1 < c → c ≤ 2 → 1 ≤ U → 2 ≤ |h| →
      0 < δ → δ ≤ 1 → (∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - h|) →
      ‖∫ σ : ℝ in -U..c, explicitIntegrand x (σ + h * I)‖ ≤
        B * x ^ c * Real.log (|h| + 2) / (δ * |h| * Real.log x) := by
  obtain ⟨A₁, hA₁, h₁⟩ := norm_explicitIntegrand_horiz_near
  obtain ⟨A₂, hA₂, h₂⟩ := norm_explicitIntegrand_left
  refine ⟨A₁ + 8 * A₂, by positivity, fun x hx c h δ U hc1 hc2 hU hh hδ hδ1 hgood ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hh0 : 0 < |h| := by linarith
  have hL1 : 1 ≤ Real.log (|h| + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hcont := continuous_explicitIntegrand_horiz (h := h) hx0 (by linarith) fun ρ e ↦ by
    have := hgood ρ; rw [e, sub_self, abs_zero] at this; linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := -1) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  refine (norm_add_le _ _).trans ?_
  set L := Real.log (|h| + 2)
  -- the part `-U ≤ σ ≤ -1`
  have hfar : ‖∫ σ : ℝ in -U..(-1), explicitIntegrand x (σ + h * I)‖ ≤
      8 * A₂ * L / (|h| * Real.log x) := by
    have hle : ∀ σ ∈ Ioc (-U) (-1), ‖explicitIntegrand x (σ + h * I)‖ ≤
        A₂ * (L + 3) / |h| * x ^ (σ / 2) := by
      intro σ hσ
      have hσ1 : σ ≤ -1 := hσ.2
      have hre : ((σ : ℂ) + h * I).re = σ := by simp
      have him : ((σ : ℂ) + h * I).im = h := by simp
      have e := h₂ x hx0 (σ + h * I) (by rw [hre]; exact hσ1) (by rw [him]; exact abs_pos.mp hh0)
        (Or.inl (by rw [him]; linarith))
      rw [hre, him] at e
      have hk := norm_perronKernel_le_horiz hx0 σ h (abs_pos.mp hh0)
      have hlog : Real.log (|σ| + |h| + 2) ≤ L + |σ| := by
        have := log_add_le_log_add (a := |h| + 2) (b := |σ|) (by linarith) (abs_nonneg _)
        rw [show |h| + 2 + |σ| = |σ| + |h| + 2 by ring] at this
        exact this
      have h3 := abs_mul_rpow_le hx (by linarith : σ ≤ 0)
      have h4 := rpow_le_rpow_half hx (by linarith : σ ≤ 0)
      have hxσ : 0 ≤ x ^ σ := by positivity
      have hL0 : 0 ≤ L := by linarith
      calc ‖explicitIntegrand x (σ + h * I)‖
          ≤ A₂ * Real.log (|σ| + |h| + 2) * ‖perronKernel x (σ + h * I)‖ := e
        _ ≤ A₂ * (L + |σ|) * (x ^ σ / |h|) := by gcongr
        _ = A₂ / |h| * (L * x ^ σ + |σ| * x ^ σ) := by field_simp
        _ ≤ A₂ / |h| * (L * x ^ (σ / 2) + 3 * x ^ (σ / 2)) := by gcongr
        _ = A₂ * (L + 3) / |h| * x ^ (σ / 2) := by field_simp
    have hint := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -U ≤ -1)
      (Eventually.of_forall fun σ hσ ↦ hle σ hσ)
      (Continuous.intervalIntegrable (μ := volume) (u := fun σ : ℝ ↦ A₂ * (L + 3) / |h| * x ^ (σ / 2))
        (continuous_const.mul ((Real.continuous_const_rpow hx0.ne').comp
          (continuous_id.div_const 2))) _ _)
    refine hint.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hI := integral_rpow_half_le hx1 (-U) (-1)
    have hxh : x ^ ((-1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
    have hI' : ∫ σ : ℝ in -U..(-1), x ^ (σ / 2) ≤ 2 / Real.log x :=
      hI.trans (div_le_div_of_nonneg_right (by linarith) hlx.le)
    calc A₂ * (L + 3) / |h| * ∫ σ : ℝ in -U..(-1), x ^ (σ / 2)
        ≤ A₂ * (L + 3) / |h| * (2 / Real.log x) := by gcongr
      _ ≤ A₂ * (4 * L) / |h| * (2 / Real.log x) := by gcongr; linarith
      _ = 8 * A₂ * L / (|h| * Real.log x) := by field_simp; ring
  -- the part `-1 ≤ σ ≤ c`
  have hnear : ‖∫ σ : ℝ in (-1)..c, explicitIntegrand x (σ + h * I)‖ ≤
      A₁ * L / (δ * |h|) * (x ^ c / Real.log x) := by
    have hle : ∀ σ ∈ Ioc (-1) c, ‖explicitIntegrand x (σ + h * I)‖ ≤ A₁ * L / (δ * |h|) * x ^ σ := by
      intro σ hσ
      have := h₁ x hx0 σ h δ hσ.1.le (by linarith [hσ.2]) hh hδ hδ1 hgood
      calc _ ≤ _ := this
        _ = A₁ * L / (δ * |h|) * x ^ σ := by
          rw [show Real.log (|h| + 2) = L from rfl]; field_simp
    have hint := intervalIntegral.norm_integral_le_of_norm_le (by linarith : (-1 : ℝ) ≤ c)
      (Eventually.of_forall fun σ hσ ↦ hle σ hσ)
      (Continuous.intervalIntegrable (μ := volume) (u := fun σ : ℝ ↦ A₁ * L / (δ * |h|) * x ^ σ)
        (continuous_const.mul (Real.continuous_const_rpow hx0.ne')) _ _)
    refine hint.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_rpow_const hx0 hx1.ne']
    gcongr
    have : 0 ≤ x ^ (-1 : ℝ) := by positivity
    linarith
  have hxc : 1 ≤ x ^ c := Real.one_le_rpow hx1.le (by linarith)
  have hL0 : 0 ≤ L := by linarith
  calc _ ≤ 8 * A₂ * L / (|h| * Real.log x) + A₁ * L / (δ * |h|) * (x ^ c / Real.log x) :=
        add_le_add hfar hnear
    _ ≤ 8 * A₂ * x ^ c * L / (δ * |h| * Real.log x) +
        A₁ * x ^ c * L / (δ * |h| * Real.log x) := by
        gcongr ?_ + ?_
        · rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : 8 * A₂ * L * (δ * |h| * Real.log x) ≤ 8 * A₂ * L * (|h| * Real.log x) := by
            gcongr; nlinarith
          have h2 : 8 * A₂ * L * (|h| * Real.log x) ≤ 8 * A₂ * x ^ c * L * (|h| * Real.log x) := by
            have : 0 ≤ 8 * A₂ * L * (|h| * Real.log x) := by positivity
            nlinarith
          linarith
        · apply le_of_eq; field_simp
    _ = (A₁ + 8 * A₂) * x ^ c * L / (δ * |h| * Real.log x) := by ring

/-- **Davenport, Ch. 17, p. 109**: the left side `σ = -U`, `U = 2K + 1`:
`|∫_{-T}^{T} F(-U + iy) dy| ≤ 2T · A log(U + T + 2) x^{-U}/U`. -/
lemma norm_integral_explicitIntegrand_left :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 < x → ∀ K : ℕ, ∀ T : ℝ, 0 ≤ T →
      ‖∫ y : ℝ in -T..T, explicitIntegrand x (((-(2 * K + 1) : ℝ) : ℂ) + y * I)‖ ≤
        2 * T * (A * Real.log (2 * K + 1 + T + 2) * (x ^ (-(2 * K + 1) : ℝ) / (2 * K + 1))) := by
  obtain ⟨A, hA, hb⟩ := norm_explicitIntegrand_left
  refine ⟨A, hA, fun x hx K T hT ↦ ?_⟩
  have hK : (0 : ℝ) ≤ K := K.cast_nonneg
  have hae : ∀ᵐ y : ℝ, y ∈ Ioc (-T) T →
      ‖explicitIntegrand x (((-(2 * K + 1) : ℝ) : ℂ) + y * I)‖ ≤
        A * Real.log (2 * K + 1 + T + 2) * (x ^ (-(2 * K + 1) : ℝ) / (2 * K + 1)) := by
    have h0 : ∀ᵐ y : ℝ, y ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h0] with y hy0 hy
    set s : ℂ := ((-(2 * K + 1) : ℝ) : ℂ) + y * I
    have hre : s.re = -(2 * K + 1) := by simp [s]
    have him : s.im = y := by simp [s]
    have e := hb x hx s (by rw [hre]; linarith) (by rw [him]; exact hy0)
      (Or.inr ⟨K, by rw [hre]⟩)
    rw [hre, him] at e
    have hk := norm_perronKernel_le_vert hx (-(2 * K + 1)) y (by linarith)
    rw [abs_of_neg (by linarith : -(2 * (K : ℝ) + 1) < 0), neg_neg] at hk
    rw [abs_of_neg (by linarith : -(2 * (K : ℝ) + 1) < 0), neg_neg] at e
    have hy' : |y| ≤ T := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    refine e.trans ?_
    gcongr
    all_goals first
      | exact Real.log_nonneg (by linarith [abs_nonneg y])
      | linarith [abs_nonneg y]
      | exact hk
      | exact mul_nonneg hA.le (Real.log_nonneg (by linarith))
  have := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T) hae
    intervalIntegrable_const
  rw [intervalIntegral.integral_const, smul_eq_mul, show T - -T = 2 * T by ring] at this
  exact this

end NTKB
