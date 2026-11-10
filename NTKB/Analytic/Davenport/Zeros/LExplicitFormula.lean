/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LGoodHeight
import NTKB.Analytic.Davenport.Zeros.ExplicitBounds

/-!
# The explicit formula for `J(x, T, χ)`

**Davenport, Ch. 19, pp. 116-117.** For primitive `χ` mod `q > 1`, `x ≥ 2`, `1 < c ≤ 2`, `T ≥ 2`
at distance `≥ δ` from the ordinates `±γ`:
`J(x, T, χ) = r₀ - ∑_{|γ|<T} x^ρ/ρ + O(x^c log(q(T + 2))/(δ T log x) + T x^{-1/2} log(q(T + 2)))`,
where `r₀` is the residue at `0` (`LContourMain.residueZeroL`). The second error term comes from
the left side `σ = -1/2` of the contour (Davenport moves it to `-∞` instead).
-/

open Filter Topology Complex Set DirichletCharacter MeasureTheory
open scoped Real Interval

namespace NTKB

variable {N : ℕ} [NeZero N]

/-- `L(s, χ) ≠ 0` and `s ≠ 0` on the boundary of the rectangle `[-1/2, c] × [-T, T]`. -/
lemma LFunction_ne_zero_on_boundary {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {c T : ℝ} (hc : 1 < c) (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) {s : ℂ}
    (hs : OnRectBoundary (((-1 / 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I) ((c : ℂ) + (T : ℂ) * I) s) :
    s ≠ 0 ∧ LFunction χ s ≠ 0 := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  obtain ⟨h1, h2⟩ := hs
  rw [mem_reProdIm] at h1
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at h1 h2
  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at h1
  rw [mem_reProdIm, min_eq_left (by linarith), max_eq_right (by linarith),
    min_eq_left (by linarith), max_eq_right (by linarith)] at h2
  -- a boundary point: `σ = -1/2`, `σ = c` or `|t| = T`
  have hcase : s.re = -1 / 2 ∨ s.re = c ∨ |s.im| = T := by
    by_contra hne
    push Not at hne
    apply h2
    refine ⟨⟨lt_of_le_of_ne h1.1.1 (Ne.symm hne.1), lt_of_le_of_ne h1.1.2 hne.2.1⟩, ?_⟩
    have : |s.im| < T := lt_of_le_of_ne (abs_le.mpr ⟨h1.2.1, h1.2.2⟩) hne.2.2
    exact abs_lt.mp this
  rcases hcase with hre | hre | him
  · refine ⟨fun h ↦ by rw [h] at hre; norm_num at hre, ?_⟩
    exact LFunction_ne_zero_of_re_nonpos hχ hN (ne_trivial_of_re_eq χ hre) (by rw [hre]; norm_num)
  · refine ⟨fun h ↦ by rw [h] at hre; simp at hre; linarith, ?_⟩
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by rw [hre]; linarith)
  · have hs0 : s ≠ 0 := fun h ↦ by rw [h] at him; simp at him; linarith
    refine ⟨hs0, fun hz ↦ ?_⟩
    rcases le_or_gt s.re 0 with hre | hre
    · refine LFunction_ne_zero_of_re_nonpos hχ hN (fun n hn ↦ ?_) hre hz
      have := congrArg Complex.im hn
      simp [dirichletParity_im] at this
      rw [this] at him; simp at him; linarith
    · obtain ⟨ρ, hρ⟩ := exists_zeroIndex_dirichletXi hχ hN hz hre
      exact hTz ρ (by rw [hρ]; exact him)

/-- The rectangle integral of `F(s, χ)` itself. -/
theorem Davenport.rectIntegral_explicitIntegrandL {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hN : N ≠ 1) {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 < T)
    (hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T) :
    rectIntegral (explicitIntegrandL χ x) (((-1 / 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        ((c : ℂ) + (T : ℂ) * I) =
      2 * π * I * (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hN T, perronKernel x ρ.val) := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  rw [← Davenport.rectIntegral_explicitIntegrandL' hχ hN hx hc hT hTz]
  by_cases ha : dirichletParity χ = 1
  · have e : explicitIntegrandL' χ x = explicitIntegrandL χ x :=
      funext fun s ↦ by simp only [explicitIntegrandL', ha, if_true]
    rw [e]
  · have e : explicitIntegrandL' χ x = fun s ↦ explicitIntegrandL χ x s + 1 / (s - 0) ^ 2 :=
      funext fun s ↦ by simp only [explicitIntegrandL', ha, if_false]
    have hb := fun s hs ↦ LFunction_ne_zero_on_boundary hχ hN hc hT hTz (s := s) hs
    have hF : RectIntegrable (explicitIntegrandL χ x) (((-1 / 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        ((c : ℂ) + (T : ℂ) * I) := rectIntegrable_of_continuousAt fun s hs ↦
      (differentiableAt_explicitIntegrandL hχ1 hx (hb s hs).1 (hb s hs).2).continuousAt
    have hG : RectIntegrable (fun s : ℂ ↦ 1 / (s - 0) ^ 2) (((-1 / 2 : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I)
        ((c : ℂ) + (T : ℂ) * I) := rectIntegrable_of_continuousAt fun s hs ↦ by
      have := (hb s hs).1
      simp only [sub_zero, one_div]
      exact (continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 this)
    rw [e, rectIntegral_add hF hG, rectIntegral_inv_sq fun s hs ↦ (hb s hs).1, add_zero]

/-- Continuity of `F(s, χ)` on a horizontal line `t = h ≠ 0` avoiding the ordinates. -/
lemma continuous_explicitIntegrandL_horiz {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hN : N ≠ 1) {x : ℝ} (hx : 0 < x) {h : ℝ} (hh : h ≠ 0)
    (hgood : ∀ ρ : ZeroIndex (dirichletXi χ), ρ.val.im ≠ h) :
    Continuous fun σ : ℝ ↦ explicitIntegrandL χ x (σ + h * I) := by
  have hχ1 := ne_one_of_isPrimitive hχ hN
  refine continuous_iff_continuousAt.mpr fun σ ↦ ?_
  refine ContinuousAt.comp (g := explicitIntegrandL χ x) ?_
    (Complex.continuous_ofReal.add continuous_const).continuousAt
  have him : ((σ : ℂ) + h * I).im = h := by simp
  have hs0 : (σ : ℂ) + h * I ≠ 0 := fun e ↦ hh (by simpa [him] using congrArg Complex.im e)
  refine (differentiableAt_explicitIntegrandL hχ1 hx hs0 fun hz ↦ ?_).continuousAt
  rcases le_or_gt ((σ : ℂ) + h * I).re 0 with hre | hre
  · refine LFunction_ne_zero_of_re_nonpos hχ hN (fun n hn ↦ ?_) hre hz
    have := congrArg Complex.im hn
    simp [dirichletParity_im] at this
    exact hh this
  · obtain ⟨ρ, hρ⟩ := exists_zeroIndex_dirichletXi hχ hN hz hre
    exact hgood ρ (by rw [hρ, him])

/-- **The horizontal sides** (Davenport, Ch. 19, p. 117): for `x ≥ 2`, `1 < c ≤ 2`, `|h| ≥ 2` at
distance `≥ δ` from the ordinates, `|∫_{-1/2}^{c} F(σ + ih, χ) dσ| ≤ A (log q + log(|h| + 2))
x^c / (δ |h| log x)`. -/
lemma norm_integral_explicitIntegrandL_horiz :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ x : ℝ, 2 ≤ x → ∀ c h δ : ℝ, 1 < c → c ≤ 2 → 2 ≤ |h| → 0 < δ → δ ≤ 1 →
      (∀ ρ : ZeroIndex (dirichletXi χ), δ ≤ |ρ.val.im - h|) →
      ‖∫ σ : ℝ in (-1 / 2)..c, explicitIntegrandL χ x (σ + h * I)‖ ≤
        A * (Real.log N + Real.log (|h| + 2)) * x ^ c / (δ * |h| * Real.log x) := by
  obtain ⟨A, hA, hb⟩ := Davenport.norm_logDeriv_LFunction_good_line
  refine ⟨A, hA, ?_⟩
  intro N _ χ hχ hN x hx c h δ hc1 hc2 hh hδ hδ1 hgood
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hh0 : h ≠ 0 := fun h0 ↦ by rw [h0, abs_zero] at hh; norm_num at hh
  have hhp : 0 < |h| := by linarith
  set Lg := Real.log N + Real.log (|h| + 2)
  have hLg : 0 ≤ Lg := by
    have := Real.log_natCast_nonneg N
    have := Real.log_nonneg (by linarith [abs_nonneg h] : (1 : ℝ) ≤ |h| + 2); linarith
  have hle : ∀ σ ∈ Ioc (-1 / 2 : ℝ) c, ‖explicitIntegrandL χ x (σ + h * I)‖ ≤
      A * Lg / (δ * |h|) * x ^ σ := by
    intro σ hσ
    have hre : ((σ : ℂ) + h * I).re = σ := by simp
    have him : ((σ : ℂ) + h * I).im = h := by simp
    have h1 := (hb hχ hN (σ + h * I) (by rw [hre]; linarith [hσ.1]) (by rw [hre]; linarith [hσ.2])
      (by rw [him]; exact hh) δ hδ hδ1 (by rw [him]; exact hgood)).2
    rw [him] at h1
    rw [explicitIntegrandL, norm_mul, norm_neg]
    calc ‖deriv (LFunction χ) (σ + h * I) / LFunction χ (σ + h * I)‖ *
          ‖perronKernel x (σ + h * I)‖ ≤ A * Lg / δ * (x ^ σ / |h|) :=
          mul_le_mul h1 (norm_perronKernel_le_horiz hx0 σ h hh0) (norm_nonneg _) (by positivity)
      _ = A * Lg / (δ * |h|) * x ^ σ := by field_simp
  have hint := intervalIntegral.norm_integral_le_of_norm_le (by linarith : (-1 / 2 : ℝ) ≤ c)
    (Eventually.of_forall fun σ hσ ↦ hle σ hσ)
    (Continuous.intervalIntegrable (μ := volume) (u := fun σ : ℝ ↦ A * Lg / (δ * |h|) * x ^ σ)
      (continuous_const.mul (Real.continuous_const_rpow hx0.ne')) _ _)
  refine hint.trans ?_
  rw [intervalIntegral.integral_const_mul, integral_rpow_const hx0 hx1.ne']
  have : 0 ≤ x ^ (-1 / 2 : ℝ) := by positivity
  calc A * Lg / (δ * |h|) * ((x ^ c - x ^ (-1 / 2 : ℝ)) / Real.log x)
      ≤ A * Lg / (δ * |h|) * (x ^ c / Real.log x) := by
        gcongr; linarith
    _ = A * Lg * x ^ c / (δ * |h| * Real.log x) := by field_simp

/-- **The left side** `σ = -1/2`: `|∫_{-T}^{T} F(-1/2 + iy, χ) dy| ≤ 2T · 2A (log q + log(T + 2))
x^{-1/2}`. -/
lemma norm_integral_explicitIntegrandL_left :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ x : ℝ, 0 < x → ∀ T : ℝ, 0 ≤ T →
      ‖∫ y : ℝ in -T..T, explicitIntegrandL χ x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
        2 * T * (2 * A * (Real.log N + Real.log (T + 2)) * x ^ (-1 / 2 : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := Davenport.norm_logDeriv_LFunction_left
  refine ⟨A, hA, ?_⟩
  intro N _ χ hχ hN x hx T hT
  have hlN := Real.log_natCast_nonneg N
  have hpt : ∀ y ∈ Ι (-T) T, ‖explicitIntegrandL χ x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      2 * A * (Real.log N + Real.log (T + 2)) * x ^ (-1 / 2 : ℝ) := by
    intro y hy
    rw [uIoc_of_le (by linarith)] at hy
    set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I
    have hre : s.re = -1 / 2 := by simp [s]
    have him : s.im = y := by simp [s]
    have h1 := (hb hχ hN s hre).2
    rw [him] at h1
    have hyT : |y| ≤ T := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    have hlog : Real.log (|y| + 2) ≤ Real.log (T + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hk : ‖perronKernel x s‖ ≤ x ^ (-1 / 2 : ℝ) / (1 / 2) := by
      rw [norm_perronKernel hx, hre]
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      have := Complex.abs_re_le_norm s
      rw [hre] at this; norm_num at this; linarith
    rw [explicitIntegrandL, norm_mul, norm_neg]
    calc ‖deriv (LFunction χ) s / LFunction χ s‖ * ‖perronKernel x s‖
        ≤ A * (Real.log N + Real.log (T + 2)) * (x ^ (-1 / 2 : ℝ) / (1 / 2)) := by
          have hLT : 0 ≤ Real.log N + Real.log (T + 2) := by
            have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2); linarith
          refine mul_le_mul (h1.trans ?_) hk (norm_nonneg _) (by positivity)
          gcongr
      _ = 2 * A * (Real.log N + Real.log (T + 2)) * x ^ (-1 / 2 : ℝ) := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T) hpt
  rw [show T - -T = 2 * T by ring, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * T)] at this
  linarith

/-- **Davenport, Ch. 19, pp. 116-117**: for primitive `χ` mod `q > 1`, `x ≥ 2`, `1 < c ≤ 2`,
`T ≥ 2` at distance `≥ δ` from all `±γ`,
`|J(x, T, χ) - (r₀ - ∑_{|γ|<T} x^ρ/ρ)| ≤ B (log q + log(T + 2)) (x^c/(δ T log x) + T x^{-1/2})`. -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.norm_explicitJL_sub_main_le :
    ∃ B : ℝ, 0 < B ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
      (hN : N ≠ 1), ∀ x : ℝ, 2 ≤ x → ∀ c T δ : ℝ, 1 < c → c ≤ 2 → 2 ≤ T → 0 < δ → δ ≤ 1 →
      (∀ ρ : ZeroIndex (dirichletXi χ), δ ≤ |ρ.val.im - T| ∧ δ ≤ |ρ.val.im + T|) →
      ‖explicitJL χ x c T - (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hN T, perronKernel x ρ.val)‖ ≤
        B * (Real.log N + Real.log (T + 2)) *
          (x ^ c / (δ * T * Real.log x) + T * x ^ (-1 / 2 : ℝ)) := by
  obtain ⟨A₁, hA₁, hH⟩ := norm_integral_explicitIntegrandL_horiz
  obtain ⟨A₂, hA₂, hL⟩ := norm_integral_explicitIntegrandL_left
  refine ⟨A₁ + 2 * A₂, by positivity, ?_⟩
  intro N _ χ hχ hN x hx c T δ hc1 hc2 hT hδ hδ1 hgood
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hT0 : 0 < T := by linarith
  have hπ := Real.pi_pos
  have hTz : ∀ ρ : ZeroIndex (dirichletXi χ), |ρ.val.im| ≠ T := by
    intro ρ e
    rcases abs_eq hT0.le |>.mp e with e' | e'
    · have := (hgood ρ).1; rw [e', sub_self, abs_zero] at this; linarith
    · have := (hgood ρ).2; rw [e', neg_add_cancel, abs_zero] at this; linarith
  set R := residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hN T, perronKernel x ρ.val with hR
  have hrect := Davenport.rectIntegral_explicitIntegrandL hχ hN hx0 hc1 hT0 hTz
  unfold rectIntegral at hrect
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at hrect
  have hJ : (∫ y : ℝ in -T..T, explicitIntegrandL χ x (c + y * I)) = 2 * π * explicitJL χ x c T := by
    have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [explicitJL, ← mul_assoc, mul_one_div_cancel h2π, one_mul]
  rw [hJ] at hrect
  have hTa : 2 ≤ |T| := by rw [abs_of_pos hT0]; exact hT
  have hTb : 2 ≤ |-T| := by rw [abs_neg]; exact hTa
  have hgb : ∀ ρ : ZeroIndex (dirichletXi χ), δ ≤ |ρ.val.im - -T| := fun ρ ↦ by
    rw [sub_neg_eq_add]; exact (hgood ρ).2
  have hbot := hH hχ hN x hx c (-T) δ hc1 hc2 hTb hδ hδ1 hgb
  have htop := hH hχ hN x hx c T δ hc1 hc2 hTa hδ hδ1 (fun ρ ↦ (hgood ρ).1)
  rw [abs_neg, abs_of_pos hT0] at hbot
  rw [abs_of_pos hT0] at htop
  have hlft := hL hχ hN x hx0 T hT0.le
  generalize (∫ σ : ℝ in (-1 / 2)..c, explicitIntegrandL χ x (σ + (-T : ℝ) * I)) = bot
    at hrect hbot
  generalize (∫ σ : ℝ in (-1 / 2)..c, explicitIntegrandL χ x (σ + T * I)) = top at hrect htop
  generalize (∫ y : ℝ in -T..T, explicitIntegrandL χ x (((-1 / 2 : ℝ) : ℂ) + y * I)) = lft
    at hrect hlft
  have hid : (2 * π * I) * (explicitJL χ x c T - R) = top - bot + I * lft := by
    rw [hR]; linear_combination hrect
  have hn : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg hπ.le, mul_one]
  set Lg := Real.log N + Real.log (T + 2)
  have hLg : 0 ≤ Lg := by
    have := Real.log_natCast_nonneg N
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2); linarith
  set H := A₁ * Lg * x ^ c / (δ * T * Real.log x)
  have hsum : ‖top - bot + I * lft‖ ≤ 2 * H + 2 * T * (2 * A₂ * Lg * x ^ (-1 / 2 : ℝ)) := by
    calc ‖top - bot + I * lft‖ ≤ ‖top‖ + ‖bot‖ + ‖I * lft‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ H + H + 2 * T * (2 * A₂ * Lg * x ^ (-1 / 2 : ℝ)) := by
          rw [norm_mul, Complex.norm_I, one_mul]
          exact add_le_add (add_le_add htop hbot) hlft
      _ = _ := by ring
  have h3 : 2 * π * ‖explicitJL χ x c T - R‖ ≤ 2 * H + 2 * T * (2 * A₂ * Lg * x ^ (-1 / 2 : ℝ)) := by
    rw [← hn, ← norm_mul, hid]; exact hsum
  have hπ3 := Real.pi_gt_three
  have hH0 : 0 ≤ H := by positivity
  have hT2 : 0 ≤ T * x ^ (-1 / 2 : ℝ) := by positivity
  have hfin : ‖explicitJL χ x c T - R‖ ≤ H + 2 * A₂ * Lg * (T * x ^ (-1 / 2 : ℝ)) := by
    have h4 : 2 * π * ‖explicitJL χ x c T - R‖ ≥ 6 * ‖explicitJL χ x c T - R‖ := by
      have := norm_nonneg (explicitJL χ x c T - R); nlinarith
    have e : 2 * T * (2 * A₂ * Lg * x ^ (-1 / 2 : ℝ)) = 4 * (A₂ * Lg * (T * x ^ (-1 / 2 : ℝ))) := by
      ring
    have h5 : 0 ≤ A₂ * Lg * (T * x ^ (-1 / 2 : ℝ)) := by positivity
    nlinarith
  refine hfin.trans ?_
  set X := x ^ c / (δ * T * Real.log x)
  set Y := T * x ^ (-1 / 2 : ℝ)
  have hX : 0 ≤ X := by positivity
  have hHX : H = A₁ * Lg * X := by simp only [H, X]; ring
  rw [hHX]
  have h1 : A₁ * Lg * X ≤ (A₁ + 2 * A₂) * Lg * X := by
    have : 0 ≤ 2 * A₂ * Lg * X := by positivity
    nlinarith
  have h2 : 2 * A₂ * Lg * Y ≤ (A₁ + 2 * A₂) * Lg * Y := by
    have : 0 ≤ A₁ * Lg * Y := by positivity
    nlinarith
  have e : (A₁ + 2 * A₂) * Lg * (X + Y) = (A₁ + 2 * A₂) * Lg * X + (A₁ + 2 * A₂) * Lg * Y := by
    ring
  rw [e]
  linarith

end NTKB
