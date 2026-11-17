/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitReal

/-!
# The explicit formula for `ψ₀(x)` at real `1 < x < 2`

**Davenport, Ch. 17, p. 104 (row 17-2).** For real `1 < x < 2` the formula
`ψ₀(x) = x - ∑_ρ x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})` (with `ψ₀(x) = 0`) is proved here for each
fixed `x`, so every constant may depend on `x`. The proof of `Davenport.tendsto_explicitMain_real` is
repeated with `log 2` replaced by `log x` or `log(2/x)`: the Perron part has no prime power `n ≤ x`
except none at all, so `ψ₀(x) = 0` and every term is a "far" term, and in the bound for the
horizontal sides the inequality `u ≤ 3 x^{u/2}` is replaced by `u ≤ (2/log x) x^{u/2}`.
-/

open Filter Topology Complex Set MeasureTheory
open scoped Real Interval

namespace NTKB

/-- `ψ₀(x) = 0` for `1 ≤ x < 2`. -/
lemma psi0R_of_lt_two {x : ℝ} (hx : 1 ≤ x) (hx2 : x < 2) : psi0R x = 0 := by
  have h : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast hx, by push_cast; linarith⟩
  unfold psi0R
  rw [h]
  simp [Finset.sum_range_succ]

/-- For `1 < x < 2`, the Perron part: `|ψ₀(x) - J(x, T)| ≤ C / T`. -/
lemma norm_psi0R_sub_explicitJ_le_small {x : ℝ} (hx : 1 < x) (hx2 : x < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      ‖(psi0R x : ℂ) - explicitJ x (perronAbscissa x) T‖ ≤ C / T := by
  have hπ := Real.pi_pos
  have hx0 : 0 < x := by linarith
  have hc1 := one_lt_perronAbscissa (x := x) hx.le
  have hxc := rpow_perronAbscissa_le (x := x) hx.le
  set c := perronAbscissa x with hcdef
  have hc0 : 0 < c := by linarith
  have hℓ : 0 < Real.log (2 / x) := Real.log_pos (by rw [one_lt_div hx0]; exact hx2)
  set ℓ := Real.log (2 / x) with hℓdef
  have hS := hasSum_vonMangoldt_rpow hc1
  set S := -(deriv riemannZeta c / riemannZeta c).re with hSdef
  have hS0 : 0 ≤ S := hS.nonneg fun n ↦ mul_nonneg
    ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg n.cast_nonneg _)
  refine ⟨3 * x * S / (π * ℓ) + 1, by positivity, fun T hT ↦ ?_⟩
  have hd := Davenport.hasSum_explicitJ (x := x) T hx0 hc1
  rw [psi0R_of_lt_two hx.le hx2, Complex.ofReal_zero, zero_sub, norm_neg, ← hd.tsum_eq]
  have hG := hS.mul_left (3 * x / (π * T * ℓ))
  refine (tsum_of_norm_bounded hG fun n ↦ ?_).trans ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    by_cases hn : 2 ≤ n
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      set y : ℝ := x / n with hy
      have hy0 : 0 < y := div_pos hx0 hn0
      have hy1 : y < 1 := by rw [hy, div_lt_one hn0]; linarith
      have hb := norm_perronIntegral_lt_one_log hy0 hy1 hc0 hT
      have hlog : ℓ ≤ |Real.log y| := by
        rw [abs_of_neg (Real.log_neg hy0 hy1)]
        have e : Real.log y = -Real.log (n / x) := by
          rw [hy, ← Real.log_inv, inv_div]
        rw [e, neg_neg]
        exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hn2 hx0.le)
      have hyc : y ^ c = x ^ c * (n : ℝ) ^ (-c) := by
        rw [hy, Real.div_rpow hx0.le hn0.le, Real.rpow_neg hn0.le, div_eq_mul_inv]
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have e1 : y ^ c / (π * T * |Real.log y|) ≤ y ^ c / (π * T * ℓ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      have e2 : y ^ c / (π * T * ℓ) ≤ 3 * x / (π * T * ℓ) * (n : ℝ) ^ (-c) := by
        rw [hyc, div_mul_eq_mul_div]
        gcongr
      calc ArithmeticFunction.vonMangoldt n * ‖perronIntegral y c T‖ ≤
            ArithmeticFunction.vonMangoldt n * (3 * x / (π * T * ℓ) * (n : ℝ) ^ (-c)) :=
            mul_le_mul_of_nonneg_left (hb.trans (e1.trans e2)) hΛ
        _ = _ := by ring
    · have h0 : ArithmeticFunction.vonMangoldt n = 0 := by
        have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp
      rw [h0, zero_mul, zero_mul, mul_zero]
  · have e : 3 * x / (π * T * ℓ) * S = 3 * x * S / (π * ℓ) / T := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hT.le

/-- `u ≤ (2/log x) x^{u/2}` for `u ≥ 0`, `x > 1`. -/
lemma le_rpow_half_small {x u : ℝ} (hx : 1 < x) (_hu : 0 ≤ u) :
    u ≤ 2 / Real.log x * x ^ (u / 2) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_def_of_pos (by linarith), div_mul_eq_mul_div, le_div_iff₀ hl]
  have h2 := Real.add_one_le_exp (Real.log x * (u / 2))
  nlinarith

/-- `|σ| x^σ ≤ (2/log x) x^{σ/2}` for `σ ≤ 0`, `x > 1`. -/
lemma abs_mul_rpow_le_small {x σ : ℝ} (hx : 1 < x) (hσ : σ ≤ 0) :
    |σ| * x ^ σ ≤ 2 / Real.log x * x ^ (σ / 2) := by
  have hx0 : 0 < x := by linarith
  have h1 := le_rpow_half_small hx (abs_nonneg σ)
  rw [abs_of_nonpos hσ] at h1 ⊢
  calc -σ * x ^ σ ≤ 2 / Real.log x * x ^ (-σ / 2) * x ^ σ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 2 / Real.log x * x ^ (σ / 2) := by
      rw [mul_assoc, ← Real.rpow_add hx0]; ring_nf

/-- **Davenport, Ch. 17, p. 109**: the horizontal sides, for `x > 1` (the constant depends on `x`). -/
lemma norm_integral_explicitIntegrand_horiz_small {x : ℝ} (hx : 1 < x) :
    ∃ B : ℝ, 0 < B ∧ ∀ c h δ U : ℝ, 1 < c → c ≤ 2 → 1 ≤ U → 2 ≤ |h| →
      0 < δ → δ ≤ 1 → (∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - h|) →
      ‖∫ σ : ℝ in -U..c, explicitIntegrand x (σ + h * I)‖ ≤
        B * x ^ c * Real.log (|h| + 2) / (δ * |h| * Real.log x) := by
  obtain ⟨A₁, hA₁, h₁⟩ := norm_explicitIntegrand_horiz_near
  obtain ⟨A₂, hA₂, h₂⟩ := norm_explicitIntegrand_left
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  obtain ⟨K₂, hK₂, hK₂def⟩ : ∃ K₂ : ℝ, 0 < K₂ ∧ K₂ = 2 * A₂ * (1 + 2 / Real.log x) :=
    ⟨_, by positivity, rfl⟩
  refine ⟨A₁ + K₂, by positivity, fun c h δ U hc1 hc2 hU hh hδ hδ1 hgood ↦ ?_⟩
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
      K₂ * L / (|h| * Real.log x) := by
    have hle : ∀ σ ∈ Ioc (-U) (-1), ‖explicitIntegrand x (σ + h * I)‖ ≤
        A₂ * (L + 2 / Real.log x) / |h| * x ^ (σ / 2) := by
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
      have h3 := abs_mul_rpow_le_small hx (by linarith : σ ≤ 0)
      have h4 : x ^ σ ≤ x ^ (σ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
      have hxσ : 0 ≤ x ^ σ := by positivity
      have hL0 : 0 ≤ L := by linarith
      calc ‖explicitIntegrand x (σ + h * I)‖
          ≤ A₂ * Real.log (|σ| + |h| + 2) * ‖perronKernel x (σ + h * I)‖ := e
        _ ≤ A₂ * (L + |σ|) * (x ^ σ / |h|) := by gcongr
        _ = A₂ / |h| * (L * x ^ σ + |σ| * x ^ σ) := by field_simp
        _ ≤ A₂ / |h| * (L * x ^ (σ / 2) + 2 / Real.log x * x ^ (σ / 2)) := by gcongr
        _ = A₂ * (L + 2 / Real.log x) / |h| * x ^ (σ / 2) := by ring
    have hint := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -U ≤ -1)
      (Eventually.of_forall fun σ hσ ↦ hle σ hσ)
      (Continuous.intervalIntegrable (μ := volume)
        (u := fun σ : ℝ ↦ A₂ * (L + 2 / Real.log x) / |h| * x ^ (σ / 2))
        (continuous_const.mul ((Real.continuous_const_rpow hx0.ne').comp
          (continuous_id.div_const 2))) _ _)
    refine hint.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hI := integral_rpow_half_le hx (-U) (-1)
    have hxh : x ^ ((-1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
    have hI' : ∫ σ : ℝ in -U..(-1), x ^ (σ / 2) ≤ 2 / Real.log x :=
      hI.trans (div_le_div_of_nonneg_right (by linarith) hlx.le)
    have hk2 : 0 ≤ 2 / Real.log x := by positivity
    have hLk : L + 2 / Real.log x ≤ (1 + 2 / Real.log x) * L := by nlinarith
    calc A₂ * (L + 2 / Real.log x) / |h| * ∫ σ : ℝ in -U..(-1), x ^ (σ / 2)
        ≤ A₂ * (L + 2 / Real.log x) / |h| * (2 / Real.log x) := by gcongr
      _ ≤ A₂ * ((1 + 2 / Real.log x) * L) / |h| * (2 / Real.log x) := by gcongr
      _ = K₂ * L / (|h| * Real.log x) := by rw [hK₂def]; field_simp
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
    rw [intervalIntegral.integral_const_mul, integral_rpow_const hx0 hx.ne']
    gcongr
    have : 0 ≤ x ^ (-1 : ℝ) := by positivity
    linarith
  have hxc : 1 ≤ x ^ c := Real.one_le_rpow hx.le (by linarith)
  have hL0 : 0 ≤ L := by linarith
  calc _ ≤ K₂ * L / (|h| * Real.log x) + A₁ * L / (δ * |h|) * (x ^ c / Real.log x) :=
        add_le_add hfar hnear
    _ ≤ K₂ * x ^ c * L / (δ * |h| * Real.log x) +
        A₁ * x ^ c * L / (δ * |h| * Real.log x) := by
        gcongr ?_ + ?_
        · rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : K₂ * L * (δ * |h| * Real.log x) ≤ K₂ * L * (|h| * Real.log x) := by
            gcongr; nlinarith
          have h2 : K₂ * L * (|h| * Real.log x) ≤ K₂ * x ^ c * L * (|h| * Real.log x) := by
            have : 0 ≤ K₂ * L * (|h| * Real.log x) := by positivity
            nlinarith
          linarith
        · apply le_of_eq; field_simp
    _ = (A₁ + K₂) * x ^ c * L / (δ * |h| * Real.log x) := by ring

/-- **Davenport, Ch. 17, pp. 107-109**, for `x > 1` (the constant depends on `x`): for `1 < c ≤ 2`,
`T ≥ 2` at distance `≥ δ` from the ordinates `±γ` of all zeros,
`|J(x, T) - (x - ∑_{|γ|<T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2}))| ≤ B x^c log(T+2)/(δ T log x)`. -/
lemma norm_explicitJ_sub_main_le_small {x : ℝ} (hx : 1 < x) :
    ∃ B : ℝ, 0 < B ∧ ∀ c T δ : ℝ, 1 < c → c ≤ 2 → 2 ≤ T → 0 < δ → δ ≤ 1 →
      (∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - T| ∧ δ ≤ |ρ.val.im + T|) →
      ‖explicitJ x c T - explicitMain x T‖ ≤ B * x ^ c * Real.log (T + 2) / (δ * T * Real.log x) := by
  obtain ⟨B, hB, hH⟩ := norm_integral_explicitIntegrand_horiz_small hx
  obtain ⟨A, hA, hL⟩ := norm_integral_explicitIntegrand_left
  refine ⟨B, hB, fun c T δ hc1 hc2 hT hδ hδ1 hgood ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hT0 : 0 < T := by linarith
  have hπ := Real.pi_pos
  have hTz : ∀ ρ : ZeroIndex riemannXi, |ρ.val.im| ≠ T := by
    intro ρ e
    rcases abs_eq hT0.le |>.mp e with e' | e'
    · have := (hgood ρ).1; rw [e', sub_self, abs_zero] at this; linarith
    · have := (hgood ρ).2; rw [e', neg_add_cancel, abs_zero] at this; linarith
  obtain ⟨Hb, hHb⟩ : ∃ Hb : ℝ, Hb = B * x ^ c * Real.log (T + 2) / (δ * T * Real.log x) :=
    ⟨_, rfl⟩
  set R : ℕ → ℂ := fun K ↦ x - deriv riemannZeta 0 / riemannZeta 0 -
    ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val -
    ∑ k ∈ Finset.range K, perronKernel x (-(2 * ((k : ℂ) + 1))) with hR
  obtain ⟨lb, hlb⟩ : ∃ lb : ℕ → ℝ, lb = fun K : ℕ ↦ 2 * T * (A * Real.log (2 * (K : ℝ) + 1 + T + 2) *
      (x ^ (-(2 * (K : ℝ) + 1)) / (2 * (K : ℝ) + 1))) := ⟨_, rfl⟩
  have hJ : (∫ y : ℝ in -T..T, explicitIntegrand x (c + y * I)) = 2 * π * explicitJ x c T := by
    have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [explicitJ, ← mul_assoc, mul_one_div_cancel h2π, one_mul]
  have hTa : 2 ≤ |T| := by rw [abs_of_pos hT0]; exact hT
  have hTb : 2 ≤ |-T| := by rw [abs_neg]; exact hTa
  have hgb : ∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - -T| := fun ρ ↦ by
    rw [sub_neg_eq_add]; exact (hgood ρ).2
  have hn : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg hπ.le, mul_one]
  have hK : ∀ K : ℕ, ‖explicitJ x c T - R K‖ ≤ (2 * Hb + lb K) / (2 * π) := by
    intro K
    have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
    have hrect := Davenport.rectIntegral_explicitIntegrand hx0 hc1 hT0 hTz K
    unfold rectIntegral at hrect
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hrect
    rw [hJ] at hrect
    have hbot := hH c (-T) δ (2 * K + 1) hc1 hc2 (by linarith) hTb hδ hδ1 hgb
    have htop := hH c T δ (2 * K + 1) hc1 hc2 (by linarith) hTa hδ hδ1 (fun ρ ↦ (hgood ρ).1)
    rw [abs_neg, abs_of_pos hT0, ← hHb] at hbot
    rw [abs_of_pos hT0, ← hHb] at htop
    have hlft := hL x hx0 K T hT0.le
    have hlb' : 2 * T * (A * Real.log (2 * K + 1 + T + 2) *
        (x ^ (-(2 * K + 1) : ℝ) / (2 * K + 1))) = lb K := by rw [hlb]
    rw [hlb'] at hlft
    generalize (∫ σ : ℝ in -(2 * K + 1)..c, explicitIntegrand x (σ + (-T : ℝ) * I)) = bot
      at hrect hbot
    generalize (∫ σ : ℝ in -(2 * K + 1)..c, explicitIntegrand x (σ + T * I)) = top at hrect htop
    generalize (∫ y : ℝ in -T..T, explicitIntegrand x (((-(2 * K + 1) : ℝ) : ℂ) + y * I)) = lft
      at hrect hlft
    have hrect' : bot - top + I * (2 * π * explicitJ x c T) - I * lft = 2 * π * I * R K := hrect
    have hid : (2 * π * I) * (explicitJ x c T - R K) = top - bot + I * lft := by
      linear_combination hrect'
    have h2 : ‖top - bot + I * lft‖ ≤ 2 * Hb + lb K := by
      calc ‖top - bot + I * lft‖ ≤ ‖top‖ + ‖bot‖ + ‖I * lft‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ Hb + Hb + lb K := by
            rw [norm_mul, Complex.norm_I, one_mul]
            exact add_le_add (add_le_add htop hbot) hlft
        _ = 2 * Hb + lb K := by ring
    have h3 : 2 * π * ‖explicitJ x c T - R K‖ ≤ 2 * Hb + lb K := by
      rw [← hn, ← norm_mul, hid]; exact h2
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hRlim : Tendsto R atTop (𝓝 (explicitMain x T)) := by
    have := (tendsto_sum_trivial hx).const_sub (x - deriv riemannZeta 0 / riemannZeta 0 -
      ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val)
    convert this using 1
    simp only [explicitMain]
    ring
  have hlim1 : Tendsto (fun K ↦ ‖explicitJ x c T - R K‖) atTop
      (𝓝 ‖explicitJ x c T - explicitMain x T‖) :=
    (tendsto_const_nhds.sub hRlim).norm
  have hlim2 : Tendsto (fun K ↦ (2 * Hb + lb K) / (2 * π)) atTop (𝓝 ((2 * Hb + 0) / (2 * π))) := by
    rw [hlb]
    exact (tendsto_const_nhds.add (tendsto_left_bound hx A T hA.le hT0.le)).div_const _
  have := le_of_tendsto_of_tendsto' hlim1 hlim2 hK
  refine this.trans ?_
  have hHb0 : 0 ≤ Hb := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2)
    have : 0 ≤ x ^ c := by positivity
    rw [hHb]; positivity
  rw [← hHb, add_zero, div_le_iff₀ (by positivity)]
  have := Real.pi_gt_three
  nlinarith

set_option maxHeartbeats 1000000 in
/-- For `1 < x < 2` and `T ≥ 3`, `|ψ₀(x) - (x - ∑_{|γ|<T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2}))|
≤ C log²(xT)/T`, with `C` depending on `x`. -/
lemma norm_psi0R_sub_explicitMain_le_small {x : ℝ} (hx : 1 < x) (hx2 : x < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
      ‖(psi0R x : ℂ) - explicitMain x T‖ ≤ C * Real.log (x * T) ^ 2 / T := by
  obtain ⟨C₁, hC₁, h₁⟩ := norm_psi0R_sub_explicitJ_le_small hx hx2
  obtain ⟨B, hB, hJ⟩ := norm_explicitJ_sub_main_le_small hx
  obtain ⟨A₉, hA₉, h₉⟩ := Davenport.exists_good_height
  obtain ⟨A₇, hA₇, h₇⟩ := norm_sum_zeros_strip_le
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  refine ⟨C₁ + 9 * B * x * (A₉ + 1) / Real.log x + 3 * A₇ * x, by positivity, fun T hT3 ↦ ?_⟩
  have hT : 2 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  set c := perronAbscissa x with hcdef
  have hc1 : 1 < c := one_lt_perronAbscissa hx.le
  have hc2 : c ≤ 2 := perronAbscissa_le_two hx.le
  have hxc : x ^ c ≤ 3 * x := rpow_perronAbscissa_le hx.le
  set Λ := Real.log (x * T) with hΛdef
  have hΛ1 : 1 < Λ := by
    rw [hΛdef, Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hTΛ : Real.log T ≤ Λ := Real.log_le_log hT0 (by nlinarith)
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  obtain ⟨T', hT', hgood⟩ := h₉ T hT
  have hT'0 : 0 < T' := by linarith [hT'.1]
  have hT'2 : 2 ≤ T' := by linarith [hT'.1]
  set δ := min (1 / (A₉ * Real.log T)) 1 with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hinvδ : 1 / δ ≤ A₉ * Real.log T + 1 := by
    rcases le_total (1 / (A₉ * Real.log T)) 1 with h | h
    · rw [hδdef, min_eq_left h, one_div_one_div]; linarith
    · rw [hδdef, min_eq_right h]; have : 0 ≤ A₉ * Real.log T := by positivity
      linarith
  have hgood' : ∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - T'| ∧ δ ≤ |ρ.val.im + T'| :=
    fun ρ ↦ ⟨(min_le_left _ _).trans (hgood ρ).1, (min_le_left _ _).trans (hgood ρ).2⟩
  have e1 := h₁ T' hT'0
  have e2 := hJ c T' δ hc1 hc2 hT'2 hδ0 hδ1 hgood'
  have e3 := h₇ x hx.le T T' hT hT'.1 hT'.2
  have hsplit : (psi0R x : ℂ) - explicitMain x T =
      ((psi0R x : ℂ) - explicitJ x c T') + (explicitJ x c T' - explicitMain x T') -
        (∑ ρ ∈ zerosBelow T', perronKernel x ρ.val - ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val) := by
    simp only [explicitMain]; ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith
  have b1 : ‖(psi0R x : ℂ) - explicitJ x c T'‖ ≤ C₁ * Λ ^ 2 / T := by
    refine e1.trans ?_
    calc C₁ / T' ≤ C₁ / T := div_le_div_of_nonneg_left hC₁.le hT0 hT'.1
      _ ≤ C₁ * Λ ^ 2 / T := div_le_div_of_nonneg_right (by nlinarith) hT0.le
  have b2 : ‖explicitJ x c T' - explicitMain x T'‖ ≤
      9 * B * x * (A₉ + 1) / Real.log x * Λ ^ 2 / T := by
    refine e2.trans ?_
    have hlog3 := log_add_three_le hT
    have hq : Real.log (T' + 2) ≤ 3 * Λ := by
      have : Real.log (T' + 2) ≤ Real.log (T + 3) :=
        Real.log_le_log (by linarith) (by linarith [hT'.2])
      linarith
    have hq0 : 0 ≤ Real.log (T' + 2) := Real.log_nonneg (by linarith)
    have hA : 1 ≤ δ * ((A₉ + 1) * Λ) := by
      have h1 : 1 ≤ δ * (A₉ * Real.log T + 1) := by
        have := (div_le_iff₀ hδ0).mp hinvδ; linarith
      have h2 : A₉ * Real.log T + 1 ≤ (A₉ + 1) * Λ := by nlinarith
      nlinarith
    have e : 9 * B * x * (A₉ + 1) / Real.log x * Λ ^ 2 / T =
        9 * B * x * (A₉ + 1) * Λ ^ 2 / (T * Real.log x) := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hx3 : 0 ≤ B * (3 * x) * (3 * Λ) := by positivity
    calc B * x ^ c * Real.log (T' + 2) * (T * Real.log x)
        ≤ B * (3 * x) * (3 * Λ) * (T * Real.log x) := by gcongr
      _ ≤ B * (3 * x) * (3 * Λ) * ((δ * ((A₉ + 1) * Λ)) * T' * Real.log x) := by
          apply mul_le_mul_of_nonneg_left _ hx3
          have h1 : T ≤ T' := hT'.1
          have h2 : T' ≤ T' * (δ * ((A₉ + 1) * Λ)) := le_mul_of_one_le_right hT'0.le hA
          have : T ≤ (δ * ((A₉ + 1) * Λ)) * T' := by linarith
          exact mul_le_mul_of_nonneg_right this hlx.le
      _ = 9 * B * x * (A₉ + 1) * Λ ^ 2 * (δ * T' * Real.log x) := by ring
  have b3 : ‖∑ ρ ∈ zerosBelow T', perronKernel x ρ.val - ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val‖ ≤
      3 * A₇ * x * Λ ^ 2 / T := by
    refine e3.trans ?_
    apply div_le_div_of_nonneg_right _ hT0.le
    have hlog3 := log_add_three_le hT
    have hΛ2' : Λ ≤ Λ ^ 2 := by nlinarith
    have h1 : Real.log (T + 3) ≤ 3 * Λ ^ 2 := by linarith
    have h2 : 0 ≤ A₇ * x := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    linarith
  have := add_le_add (add_le_add b1 b2) b3
  refine this.trans (le_of_eq ?_)
  ring

/-- `log²(xT)/T → 0` as `T → ∞`, for fixed `x > 0`. -/
lemma tendsto_log_sq_div_small {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ ↦ Real.log (x * T) ^ 2 / T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ ↦ Real.log T ^ 2 / (1 * T + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h2 : Tendsto (fun T : ℝ ↦ Real.log T ^ 1 / (1 * T + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h3 : Tendsto (fun T : ℝ ↦ 1 / T) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h4 := (h1.add (h2.const_mul (2 * Real.log x))).add (h3.const_mul (Real.log x ^ 2))
  simp only [mul_zero, add_zero, one_mul] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [Real.log_mul hx.ne' hT.ne']
  field_simp
  ring

/-- **Davenport, Ch. 17, p. 104, (row 17-2)**: von Mangoldt's explicit formula for real `1 < x < 2`,
where `ψ₀(x) = 0`:
`lim_{T → ∞} (x - ∑_{|γ|<T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})) = ψ₀(x)`. -/
@[kb "davenport1980" "Ch 17, p. 104"]
theorem Davenport.tendsto_explicitMain_real_of_one_lt {x : ℝ} (hx : 1 < x) (hx2 : x < 2) :
    Tendsto (fun T : ℝ ↦ explicitMain x T) atTop (𝓝 (psi0R x : ℂ)) := by
  obtain ⟨C, hC, h⟩ := norm_psi0R_sub_explicitMain_le_small hx hx2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun T : ℝ ↦ C * (Real.log (x * T) ^ 2 / T)) atTop (𝓝 0) := by
    simpa using (tendsto_log_sq_div_small (by linarith : 0 < x)).const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
  rw [norm_norm, norm_sub_rev, ← mul_div_assoc]
  exact h T hT

/-- **Davenport, Ch. 17, p. 104 (row 17-2)** for every real `x > 1`:
`lim_{T → ∞} (x - ∑_{|γ|<T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})) = ψ₀(x)`. -/
theorem Davenport.tendsto_explicitMain_real_of_one_lt' {x : ℝ} (hx : 1 < x) :
    Tendsto (fun T : ℝ ↦ explicitMain x T) atTop (𝓝 (psi0R x : ℂ)) := by
  rcases lt_or_ge x 2 with h2 | h2
  · exact Davenport.tendsto_explicitMain_real_of_one_lt hx h2
  · exact Davenport.tendsto_explicitMain_real h2

/-- **Davenport, Ch. 17, p. 104, (1) (row 17-2)**, in the book's form: for real `x > 1`,
`∑_{|γ|<T} x^ρ/ρ → x - ψ₀(x) - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})` as `T → ∞`; that is,
`ψ₀(x) = x - ∑_ρ x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})`. Here `ζ'(0)/ζ(0) = log 2π`. -/
@[kb "davenport1980" "Ch 17, p. 104"]
theorem Davenport.explicit_formula_vonMangoldt {x : ℝ} (hx : 1 < x) :
    Tendsto (fun T : ℝ ↦ ∑ ρ ∈ zerosBelow T, (x : ℂ) ^ ρ.val / ρ.val) atTop
      (𝓝 ((x : ℂ) - psi0R x - Real.log (2 * π) -
        ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) := by
  have h := (Davenport.tendsto_explicitMain_real_of_one_lt' hx).const_sub
    ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 - ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))
  have hz : deriv riemannZeta 0 / riemannZeta 0 = (Real.log (2 * π) : ℂ) := by
    rw [deriv_riemannZeta_zero, riemannZeta_zero, Complex.ofReal_log (by positivity)]
    push_cast
    field_simp
  rw [hz] at h
  convert h using 1
  · funext T
    simp only [explicitMain, perronKernel, hz]
    ring
  · ring_nf

end NTKB
