/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitPsi
import NTKB.Analytic.Davenport.Zeros.PerronReal
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The explicit formula for `ψ₀(x)` at real `x`

**Davenport, Ch. 17, p. 110, (13) (rows 17-13, 17-8), and p. 104 (row 17-2).** For real `x ≥ 2` and
`T ≥ 2`,
`ψ₀(x) = x - ∑_{|γ| < T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2}) + R(x, T)` with
`|R(x, T)| ≪ x log²(xT)/T + log x · min(1, x/(T ⟨x⟩))`, `⟨x⟩` the distance from `x` to the nearest prime
power other than `x`. Letting `T → ∞` gives von Mangoldt's explicit formula for every real `x ≥ 2`.
This removes the restriction to integers of `Davenport.explicit_formula_psi0`, which is
kept unchanged.
-/

open Filter Topology Complex Set
open scoped Real

namespace NTKB

/-- **Davenport, Ch. 17, p. 110, (11), (12) (row 17-8)** for real `x`: for `x ≥ 2`, `T ≥ 2` and
`c = 1 + 1/log(3x)`, `|ψ₀(x) - J(x, T)| ≤ A (x log² x/T + log x · min(1, x/(T ⟨x⟩)))`. -/
@[kb "davenport1980" "Ch 17, p. 110"]
theorem Davenport.norm_psi0R_sub_explicitJ_le :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖(psi0R x : ℂ) - explicitJ x (perronAbscissa x) T‖ ≤
        A * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * distPrimePow x))) := by
  obtain ⟨A, hA, hmaj⟩ := Davenport.exists_perron_majorant_real
  refine ⟨A, hA, fun x hx T hT ↦ ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hc1 : 1 < perronAbscissa x := one_lt_perronAbscissa (by linarith)
  have hJ := Davenport.hasSum_explicitJ (x := x) T hx0 hc1
  have hψ := hasSum_psi0R x
  have hd := hJ.sub hψ
  obtain ⟨G, S, hG, hS, hGb⟩ := hmaj x hx T hT (distPrimePow x) (distPrimePow_pos x)
    fun n hn hnx ↦ distPrimePow_le hn hnx
  have hbound := tsum_of_norm_bounded (f := fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) *
      perronIntegral (x / n) (perronAbscissa x) T -
        (ArithmeticFunction.vonMangoldt n : ℂ) * (perronStepR x n : ℂ)) hG
    fun n ↦ by
      have := hGb n
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg
        ArithmeticFunction.vonMangoldt_nonneg]
      exact this
  rw [hd.tsum_eq, norm_sub_rev] at hbound
  exact hbound.trans hS

/-- `1 < log(xT)` for `x, T ≥ 2`. -/
lemma one_lt_log_mul {x T : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) : 1 < Real.log (x * T) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have := Real.exp_one_lt_d9
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 17, p. 110, (13) (rows 17-13, 17-8)** for real `x`: there is an absolute
constant `A` such that for all real `x ≥ 2` and all `T ≥ 2`,
`|ψ₀(x) - (x - ∑_{|γ| < T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2}))| ≤
A (x log²(xT)/T + log x · min(1, x/(T ⟨x⟩)))`, where `⟨x⟩ = distPrimePow x` is the distance from
`x` to the nearest prime power other than `x`. -/
@[kb "davenport1980" "Ch 17, p. 110"]
theorem Davenport.explicit_formula_psi0_real :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖(psi0R x : ℂ) - explicitMain x T‖ ≤
        A * (x * Real.log (x * T) ^ 2 / T + Real.log x * min 1 (x / (T * distPrimePow x))) := by
  obtain ⟨A₈, hA₈, h₈⟩ := Davenport.norm_psi0R_sub_explicitJ_le
  obtain ⟨B, hB, hJ⟩ := Davenport.norm_explicitJ_sub_main_le
  obtain ⟨A₉, hA₉, h₉⟩ := Davenport.exists_good_height
  obtain ⟨A₇, hA₇, h₇⟩ := norm_sum_zeros_strip_le
  refine ⟨A₈ + 18 * B * (A₉ + 1) + 3 * A₇, by positivity, fun x hx T hT ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set c := perronAbscissa x with hcdef
  have hc1 : 1 < c := one_lt_perronAbscissa (by linarith)
  have hc2 : c ≤ 2 := perronAbscissa_le_two (by linarith)
  have hxc : x ^ c ≤ 3 * x := rpow_perronAbscissa_le (by linarith)
  set d := distPrimePow x with hddef
  have hd0 : 0 < d := distPrimePow_pos x
  set L := Real.log x with hLdef
  have hL : Real.log 2 ≤ L := Real.log_le_log two_pos hx
  have hl2 := log_two_gt_two_thirds
  have hL0 : 0 < L := by linarith
  set Λ := Real.log (x * T) with hΛdef
  have hΛ1 : 1 < Λ := one_lt_log_mul hx hT
  have hLΛ : L ≤ Λ := Real.log_le_log hx0 (by nlinarith)
  have hTΛ : Real.log T ≤ Λ := Real.log_le_log hT0 (by nlinarith)
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  -- the good height
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
  -- the three errors
  have e1 := h₈ x hx T' hT'2
  have e2 := hJ x hx c T' δ hc1 hc2 hT'2 hδ0 hδ1 hgood'
  have e3 := h₇ x (by linarith) T T' hT hT'.1 hT'.2
  have hsplit : (psi0R x : ℂ) - explicitMain x T =
      ((psi0R x : ℂ) - explicitJ x c T') + (explicitJ x c T' - explicitMain x T') -
        (∑ ρ ∈ zerosBelow T', perronKernel x ρ.val - ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val) := by
    simp only [explicitMain]; ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  set M := min 1 (x / (T * d)) with hMdef
  have hM0 : 0 ≤ M := le_min zero_le_one (by positivity)
  have b1 : ‖(psi0R x : ℂ) - explicitJ x c T'‖ ≤ A₈ * (x * Λ ^ 2 / T + L * M) := by
    refine e1.trans ?_
    have h1 : x * L ^ 2 / T' ≤ x * Λ ^ 2 / T := by
      calc x * L ^ 2 / T' ≤ x * L ^ 2 / T := div_le_div_of_nonneg_left (by positivity) hT0 hT'.1
        _ ≤ x * Λ ^ 2 / T := by gcongr
    have h2 : min 1 (x / (T' * d)) ≤ M := by
      refine min_le_min le_rfl ?_
      exact div_le_div_of_nonneg_left hx0.le (by positivity) (by gcongr; exact hT'.1)
    have h3 : L * min 1 (x / (T' * d)) ≤ L * M := mul_le_mul_of_nonneg_left h2 hL0.le
    gcongr
  have b2 : ‖explicitJ x c T' - explicitMain x T'‖ ≤ 18 * B * (A₉ + 1) * x * Λ ^ 2 / T := by
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
    have hLinv : 1 ≤ 2 * L := by linarith
    rw [div_le_div_iff₀ (by positivity) hT0]
    -- `B x^c log(T'+2) T ≤ 18 B (A₉+1) x Λ² · δ T' L`
    have hx3 : 0 ≤ B * (3 * x) * (3 * Λ) := by positivity
    calc B * x ^ c * Real.log (T' + 2) * T
        ≤ B * (3 * x) * (3 * Λ) * T := by gcongr
      _ ≤ B * (3 * x) * (3 * Λ) * (T' * (δ * ((A₉ + 1) * Λ)) * (2 * L)) := by
          apply mul_le_mul_of_nonneg_left _ hx3
          have h1 : T ≤ T' := hT'.1
          have h2 : T' ≤ T' * (δ * ((A₉ + 1) * Λ)) := le_mul_of_one_le_right hT'0.le hA
          have h3 : T' * (δ * ((A₉ + 1) * Λ)) ≤ T' * (δ * ((A₉ + 1) * Λ)) * (2 * L) :=
            le_mul_of_one_le_right (by positivity) hLinv
          linarith
      _ = 18 * B * (A₉ + 1) * x * Λ ^ 2 * (δ * T' * L) := by ring
  have b3 : ‖∑ ρ ∈ zerosBelow T', perronKernel x ρ.val - ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val‖ ≤
      3 * A₇ * x * Λ ^ 2 / T := by
    refine e3.trans ?_
    apply div_le_div_of_nonneg_right _ hT0.le
    have hlog3 := log_add_three_le hT
    have hΛ2 : Λ ≤ Λ ^ 2 := by nlinarith
    have h1 : Real.log (T + 3) ≤ 3 * Λ ^ 2 := by linarith
    have h2 : 0 ≤ A₇ * x := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    linarith
  have hfin : A₈ * (x * Λ ^ 2 / T + L * M) + 18 * B * (A₉ + 1) * x * Λ ^ 2 / T +
      3 * A₇ * x * Λ ^ 2 / T ≤ (A₈ + 18 * B * (A₉ + 1) + 3 * A₇) * (x * Λ ^ 2 / T + L * M) := by
    have hxΛ : 0 ≤ x * Λ ^ 2 / T := by positivity
    have hLM : 0 ≤ L * M := mul_nonneg hL0.le hM0
    have e : 18 * B * (A₉ + 1) * x * Λ ^ 2 / T = 18 * B * (A₉ + 1) * (x * Λ ^ 2 / T) := by ring
    have e' : 3 * A₇ * x * Λ ^ 2 / T = 3 * A₇ * (x * Λ ^ 2 / T) := by ring
    rw [e, e']
    have hpos : 0 ≤ (18 * B * (A₉ + 1) + 3 * A₇) * (L * M) := by positivity
    have key : (A₈ + 18 * B * (A₉ + 1) + 3 * A₇) * (x * Λ ^ 2 / T + L * M) -
        (A₈ * (x * Λ ^ 2 / T + L * M) + 18 * B * (A₉ + 1) * (x * Λ ^ 2 / T) +
          3 * A₇ * (x * Λ ^ 2 / T)) = (18 * B * (A₉ + 1) + 3 * A₇) * (L * M) := by ring
    linarith
  exact ((add_le_add (add_le_add b1 b2) b3).trans hfin)

/-- The error term of `Davenport.explicit_formula_psi0_real` tends to `0` as `T → ∞`, for fixed
`x ≥ 2`. -/
lemma tendsto_explicit_error_real {x : ℝ} (hx : 2 ≤ x) (A : ℝ) :
    Tendsto (fun T : ℝ ↦ A * (x * Real.log (x * T) ^ 2 / T +
      Real.log x * min 1 (x / (T * distPrimePow x)))) atTop (𝓝 0) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hd := distPrimePow_pos x
  have h1 : Tendsto (fun T : ℝ ↦ Real.log T ^ 2 / (1 * T + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h2 : Tendsto (fun T : ℝ ↦ Real.log T ^ 1 / (1 * T + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h3 : Tendsto (fun T : ℝ ↦ 1 / T) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h4 := ((h1.add (h2.const_mul (2 * Real.log x))).add (h3.const_mul (Real.log x ^ 2))).const_mul x
  simp only [mul_zero, add_zero, one_mul] at h4
  have h5 : Tendsto (fun T : ℝ ↦ x * Real.log (x * T) ^ 2 / T) atTop (𝓝 0) := by
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Real.log_mul hx0.ne' hT.ne']
    field_simp
    ring
  have h6 : Tendsto (fun T : ℝ ↦ min 1 (x / (T * distPrimePow x))) atTop (𝓝 0) := by
    have h7 : Tendsto (fun T : ℝ ↦ x / (T * distPrimePow x)) atTop (𝓝 0) := by
      have := (h3.const_mul (x / distPrimePow x))
      rw [mul_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      field_simp
    have h8 : Tendsto (fun T : ℝ ↦ min 1 (x / (T * distPrimePow x))) atTop (𝓝 (min 1 0)) :=
      tendsto_const_nhds.min h7
    simpa using h8
  have := (h5.add (h6.const_mul (Real.log x))).const_mul A
  simpa using this

/-- **Davenport, Ch. 17, p. 104, (row 17-2)**: von Mangoldt's explicit formula for real `x ≥ 2`,
`ψ₀(x) = x - ∑_ρ x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})`, the sum over the nontrivial zeros taken
symmetrically: `lim_{T → ∞} (x - ∑_{|γ|<T} x^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - x^{-2})) = ψ₀(x)`. -/
@[kb "davenport1980" "Ch 17, p. 104"]
theorem Davenport.tendsto_explicitMain_real {x : ℝ} (hx : 2 ≤ x) :
    Tendsto (fun T : ℝ ↦ explicitMain x T) atTop (𝓝 (psi0R x : ℂ)) := by
  obtain ⟨A, hA, h⟩ := Davenport.explicit_formula_psi0_real
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ (tendsto_explicit_error_real hx A)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  rw [norm_norm, norm_sub_rev]
  exact h x hx T hT

/-- Davenport, Ch. 17, p. 104, (1) (row 17-2) for real `x ≥ 2`; the book's form for every real
`x > 1` is `Davenport.explicit_formula_vonMangoldt` (ExplicitSmall.lean). -/
theorem Davenport.explicit_formula_vonMangoldt_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    Tendsto (fun T : ℝ ↦ ∑ ρ ∈ zerosBelow T, (x : ℂ) ^ ρ.val / ρ.val) atTop
      (𝓝 ((x : ℂ) - psi0R x - Real.log (2 * π) -
        ((1 / 2 * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))) := by
  have h := (Davenport.tendsto_explicitMain_real hx).const_sub
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
