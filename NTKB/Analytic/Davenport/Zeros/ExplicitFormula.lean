/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The explicit formula for `ψ₀(x)`

**Davenport, Ch. 17, pp. 107-110.** Moving the line of integration of `J(x, T)` to `σ = -U` and
letting `U → ∞` through odd integers:
`J(x, T) = x - ∑_{|γ| < T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2}) + O(x^c log T/(δ T log x))`
when `T` is at distance `≥ δ` from all ordinates. Combined with (11) and the choice of `T` (17-9)
this gives (17-13) at integers.
-/

open Filter Topology Complex Set MeasureTheory
open scoped Real Interval

namespace NTKB

/-- The residue sum at the trivial zeros, `∑_{k < K} x^{-2(k+1)} / (-2(k+1))`, tends to
`½ log(1 - x^{-2})`. -/
lemma tendsto_sum_trivial {x : ℝ} (hx : 1 < x) :
    Tendsto (fun K : ℕ ↦ ∑ k ∈ Finset.range K, perronKernel x (-(2 * ((k : ℂ) + 1)))) atTop
      (𝓝 (((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) := by
  have hx0 : 0 < x := by linarith
  set y : ℝ := x ^ (-2 : ℝ) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by norm_num)
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := y) (by rw [abs_of_pos hy0]; exact hy1)
  have hs' := (hs.mul_left (-(1 / 2))).map Complex.ofRealCLM Complex.continuous_ofReal
  have ht := hs'.tendsto_sum_nat
  have e : ∀ k : ℕ, perronKernel x (-(2 * ((k : ℂ) + 1))) =
      (Complex.ofRealCLM ∘ fun n : ℕ ↦ -(1 / 2) * (y ^ (n + 1) / (n + 1))) k := by
    intro k
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, perronKernel]
    have e1 : -(2 * ((k : ℂ) + 1)) = -(((2 * (k + 1) : ℕ) : ℂ)) := by push_cast; ring
    rw [e1, Complex.cpow_neg, Complex.cpow_natCast, hy, ← Real.rpow_natCast,
      ← Real.rpow_mul hx0.le]
    have e2 : (-2 : ℝ) * ((k + 1 : ℕ) : ℝ) = -((2 * (k + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [e2, Real.rpow_neg hx0.le, Real.rpow_natCast]
    push_cast
    have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hxk : (x : ℂ) ^ (2 * (k + 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hx0.ne')
    field_simp
  simp_rw [e]
  convert ht using 2
  simp only [Complex.ofRealCLM_apply]
  push_cast
  ring

/-- The left side tends to `0` as `U = 2K + 1 → ∞`. -/
lemma tendsto_left_bound {x : ℝ} (hx : 1 < x) (A T : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T) :
    Tendsto (fun K : ℕ ↦ 2 * T * (A * Real.log (2 * K + 1 + T + 2) *
      (x ^ (-(2 * K + 1) : ℝ) / (2 * K + 1)))) atTop (𝓝 0) := by
  have hx0 : 0 < x := by linarith
  set r : ℝ := x⁻¹
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hx
  have hlim : Tendsto (fun K : ℕ ↦ 2 * T * A * (3 + T) * r ^ K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul (2 * T * A * (3 + T))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun K ↦ ?_) (fun K ↦ ?_)
  · have hK : (0 : ℝ) ≤ K := K.cast_nonneg
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * K + 1 + T + 2)
    dsimp only
    positivity
  · have hK : (0 : ℝ) ≤ K := K.cast_nonneg
    dsimp only
    have hxr : x ^ (-(2 * K + 1) : ℝ) = r ^ (2 * K + 1) := by
      rw [Real.rpow_neg hx0.le, show (2 * (K : ℝ) + 1) = ((2 * K + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, inv_pow]
    rw [hxr]
    have h1 : r ^ (2 * K + 1) ≤ r ^ K := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    have h2 : Real.log (2 * K + 1 + T + 2) ≤ (3 + T) * (2 * K + 1) := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * K + 1 + T + 2)
      nlinarith
    have hlog0 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * K + 1 + T + 2)
    have h3 : Real.log (2 * K + 1 + T + 2) * (r ^ (2 * K + 1) / (2 * K + 1)) ≤ (3 + T) * r ^ K := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul h2 h1 (by positivity) (by positivity)
      nlinarith
    calc 2 * T * (A * Real.log (2 * K + 1 + T + 2) * (r ^ (2 * K + 1) / (2 * K + 1)))
        = 2 * T * A * (Real.log (2 * K + 1 + T + 2) * (r ^ (2 * K + 1) / (2 * K + 1))) := by ring
      _ ≤ 2 * T * A * ((3 + T) * r ^ K) := by gcongr
      _ = 2 * T * A * (3 + T) * r ^ K := by ring

/-- The main terms of the explicit formula: `x - ∑_{|γ| < T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})`. -/
noncomputable def explicitMain (x T : ℝ) : ℂ :=
  x - ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val - deriv riemannZeta 0 / riemannZeta 0 -
    ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)

/-- **Davenport, Ch. 17, pp. 107-109**: for `x ≥ 2`, `1 < c ≤ 2`, `T ≥ 2` at distance `≥ δ` from
the ordinates `±γ` of all zeros,
`|J(x, T) - (x - ∑_{|γ|<T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2}))| ≤ B x^c log(T+2)/(δ T log x)`. -/
@[kb "davenport1980" "Ch 17, p. 109"]
theorem Davenport.norm_explicitJ_sub_main_le :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 2 ≤ x → ∀ c T δ : ℝ, 1 < c → c ≤ 2 → 2 ≤ T → 0 < δ → δ ≤ 1 →
      (∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - T| ∧ δ ≤ |ρ.val.im + T|) →
      ‖explicitJ x c T - explicitMain x T‖ ≤ B * x ^ c * Real.log (T + 2) / (δ * T * Real.log x) := by
  obtain ⟨B, hB, hH⟩ := norm_integral_explicitIntegrand_horiz
  obtain ⟨A, hA, hL⟩ := norm_integral_explicitIntegrand_left
  refine ⟨B, hB, fun x hx c T δ hc1 hc2 hT hδ hδ1 hgood ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
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
  -- the bound for each `K`
  have hK : ∀ K : ℕ, ‖explicitJ x c T - R K‖ ≤ (2 * Hb + lb K) / (2 * π) := by
    intro K
    have hK0 : (0 : ℝ) ≤ K := K.cast_nonneg
    have hrect := Davenport.rectIntegral_explicitIntegrand hx0 hc1 hT0 hTz K
    unfold rectIntegral at hrect
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hrect
    rw [hJ] at hrect
    have hbot := hH x hx c (-T) δ (2 * K + 1) hc1 hc2 (by linarith) hTb hδ hδ1 hgb
    have htop := hH x hx c T δ (2 * K + 1) hc1 hc2 (by linarith) hTa hδ hδ1 (fun ρ ↦ (hgood ρ).1)
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
  -- `K → ∞`
  have hRlim : Tendsto R atTop (𝓝 (explicitMain x T)) := by
    have := (tendsto_sum_trivial hx1).const_sub (x - deriv riemannZeta 0 / riemannZeta 0 -
      ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val)
    convert this using 1
    simp only [explicitMain]
    ring
  have hlim1 : Tendsto (fun K ↦ ‖explicitJ x c T - R K‖) atTop
      (𝓝 ‖explicitJ x c T - explicitMain x T‖) :=
    (tendsto_const_nhds.sub hRlim).norm
  have hlim2 : Tendsto (fun K ↦ (2 * Hb + lb K) / (2 * π)) atTop (𝓝 ((2 * Hb + 0) / (2 * π))) := by
    rw [hlb]
    exact (tendsto_const_nhds.add (tendsto_left_bound hx1 A T hA.le hT0.le)).div_const _
  have := le_of_tendsto_of_tendsto' hlim1 hlim2 hK
  refine this.trans ?_
  have hHb0 : 0 ≤ Hb := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2)
    have : 0 ≤ x ^ c := by positivity
    rw [hHb]; positivity
  rw [← hHb, add_zero, div_le_iff₀ (by positivity)]
  have := Real.pi_gt_three
  nlinarith

end NTKB
