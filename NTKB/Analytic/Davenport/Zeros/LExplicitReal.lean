/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LExplicitExact
import NTKB.Analytic.Davenport.Zeros.ExplicitReal

/-!
# The explicit formula for `ψ₀(x, χ)` at real `x`

**Davenport, Ch. 19, pp. 115-117 (rows 19-2, 19-3, 19-6).** For `χ` primitive mod `q > 1`, real
`x ≥ 2` and `T ≥ 2`, with `ℓ = log q + log x + log T`,
`ψ₀(x, χ) = r₀ - ∑_{|γ|<T} x^ρ/ρ + ∑_{m ≥ 1} x^{a-2m}/(2m - a) + R`,
`|R| ≪ x ℓ²/T + log x · min(1, x/(T ⟨x⟩))`; letting `T → ∞` gives the explicit formulas (2), (3)
of Chapter 19 for every real `x ≥ 2`. The integer forms (`Davenport.explicit_formula_psi0L_exact`,
`Davenport.explicit_formula_psi0L_odd`, `Davenport.explicit_formula_psi0L_even`) are kept unchanged.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

variable {q : ℕ} [NeZero q]

/-- **Davenport, Ch. 19, p. 115 (row 19-1)** for real `x`:
`ψ₀(x, χ) = ∑_{n < x} χ(n) Λ(n) + χ(x) Λ(x)/2` (the last term only when `x` is an integer). -/
noncomputable def psi0LR (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), χ n * Λ n * perronStepR x n

lemma hasSum_psi0LR (χ : DirichletCharacter ℂ q) (x : ℝ) :
    HasSum (fun n : ℕ ↦ χ n * (Λ n : ℂ) * perronStepR x n) (psi0LR χ x) := by
  refine hasSum_sum_of_ne_finset_zero fun n hn ↦ ?_
  rw [Finset.mem_range, not_lt] at hn
  have h1 : x < n := by
    have := Nat.lt_floor_add_one x
    have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  simp [perronStepR, not_lt.mpr h1.le, h1.ne']

omit [NeZero q] in
lemma psi0LR_natCast (χ : DirichletCharacter ℂ q) (N : ℕ) : psi0LR χ N = psi0L χ N := by
  rw [psi0LR, Nat.floor_natCast, Finset.sum_range_succ, psi0L]
  congr 1
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have h : (n : ℝ) < N := by exact_mod_cast Finset.mem_range.mp hn
    simp [perronStepR, h]
  · simp [perronStepR]; ring

/-- **Davenport, Ch. 19, p. 117** (the analogue of (11), (12) of Ch. 17) for real `x`: for every
Dirichlet character `χ`, `x ≥ 2`, `T ≥ 2` and `c = 1 + 1/log(3x)`,
`|ψ₀(x, χ) - J(x, T, χ)| ≤ A (x log² x/T + log x · min(1, x/(T ⟨x⟩)))`, `A` absolute. -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.norm_psi0LR_sub_explicitJL_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), ∀ x : ℝ, 2 ≤ x →
      ∀ T : ℝ, 2 ≤ T →
      ‖psi0LR χ x - explicitJL χ x (perronAbscissa x) T‖ ≤
        A * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * distPrimePow x))) := by
  obtain ⟨A, hA, hmaj⟩ := Davenport.exists_perron_majorant_real
  refine ⟨A, hA, fun {q} _ χ x hx T hT ↦ ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hc1 : 1 < perronAbscissa x := one_lt_perronAbscissa (by linarith)
  have hJ := Davenport.hasSum_explicitJL χ (x := x) T hx0 hc1
  have hψ := hasSum_psi0LR χ x
  have hd := hJ.sub hψ
  obtain ⟨G, S, hG, hS, hGb⟩ := hmaj x hx T hT (distPrimePow x) (distPrimePow_pos x)
    fun n hn hnx ↦ distPrimePow_le hn hnx
  have hbound := tsum_of_norm_bounded (f := fun n : ℕ ↦ χ n * (Λ n : ℂ) *
      perronIntegral (x / n) (perronAbscissa x) T - χ n * (Λ n : ℂ) * (perronStepR x n : ℂ)) hG
    fun n ↦ by
      have h1 := hGb n
      rw [← mul_sub, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg
        ArithmeticFunction.vonMangoldt_nonneg]
      have h2 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
      have h3 : 0 ≤ Λ n * ‖perronIntegral (x / n) (perronAbscissa x) T - perronStepR x n‖ :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (norm_nonneg _)
      calc ‖χ n‖ * Λ n * ‖perronIntegral (x / n) (perronAbscissa x) T - perronStepR x n‖
          = ‖χ n‖ * (Λ n * ‖perronIntegral (x / n) (perronAbscissa x) T - perronStepR x n‖) := by
            ring
        _ ≤ 1 * (Λ n * ‖perronIntegral (x / n) (perronAbscissa x) T - perronStepR x n‖) :=
            mul_le_mul_of_nonneg_right h2 h3
        _ ≤ G n := by rw [one_mul]; exact h1
  rw [hd.tsum_eq, norm_sub_rev] at hbound
  exact hbound.trans hS

set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 19, p. 117, (6) (row 19-6)** for real `x`, with the trivial zeros: there is
an absolute `A` such that for primitive `χ` mod `q > 1`, real `x ≥ 2` and `T ≥ 2`, with
`ℓ = log q + log x + log T`,
`|ψ₀(x, χ) - (r₀ - ∑_{|γ|<T} x^ρ/ρ + ∑_{m ≥ 1} x^{a-2m}/(2m - a))| ≤
A (x ℓ²/T + log x · min(1, x/(T ⟨x⟩)))`. -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.explicit_formula_psi0L_real :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖psi0LR χ x - (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val +
          trivialSumL χ x)‖ ≤
        A * (x * (Real.log q + Real.log x + Real.log T) ^ 2 / T +
          Real.log x * min 1 (x / (T * distPrimePow x))) := by
  obtain ⟨A₈, hA₈, h₈⟩ := Davenport.norm_psi0LR_sub_explicitJL_le
  obtain ⟨B, hB, hJ⟩ := Davenport.norm_explicitJL_sub_main_exact_le
  obtain ⟨A₉, hA₉, h₉⟩ := Davenport.exists_good_height_L
  obtain ⟨A₇, hA₇, h₇⟩ := norm_sum_L_zeros_strip_le
  refine ⟨A₈ + 12 * B * (3 * A₉ + 4) + 3 * A₇, by positivity, ?_⟩
  intro q _ χ hχ hq x hx T hT
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set c := perronAbscissa x with hcdef
  have hc1 : 1 < c := one_lt_perronAbscissa (by linarith)
  have hc2 : c ≤ 2 := perronAbscissa_le_two (by linarith)
  have hxc : x ^ c ≤ 3 * x := rpow_perronAbscissa_le (by linarith)
  set L := Real.log x with hLdef
  have hl2 := log_two_gt_two_thirds
  have hL : Real.log 2 ≤ L := Real.log_le_log two_pos hx
  have hL0 : 0 < L := by linarith
  have hLinv : 1 ≤ 2 * L := by linarith
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hlT2 : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  -- the good height
  obtain ⟨T', hT', hgood⟩ := h₉ hχ hq T hT
  have hT'0 : 0 < T' := by linarith [hT'.1]
  have hT'2 : 2 ≤ T' := by linarith [hT'.1]
  set δ := min (1 / (A₉ * (Real.log q + Real.log T))) 1 with hδdef
  have hqT : 0 < Real.log q + Real.log T := by linarith
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hinvδ : 1 / δ ≤ A₉ * (Real.log q + Real.log T) + 1 := by
    rcases le_total (1 / (A₉ * (Real.log q + Real.log T))) 1 with h | h
    · rw [hδdef, min_eq_left h, one_div_one_div]; linarith
    · rw [hδdef, min_eq_right h]; have : 0 ≤ A₉ * (Real.log q + Real.log T) := by positivity
      linarith
  have hgood' : ∀ ρ : ZeroIndex (dirichletXi χ), δ ≤ |ρ.val.im - T'| ∧ δ ≤ |ρ.val.im + T'| :=
    fun ρ ↦ ⟨(min_le_left _ _).trans (hgood ρ).1, (min_le_left _ _).trans (hgood ρ).2⟩
  -- the three errors
  have e1 := h₈ χ x hx T' hT'2
  have e2 := hJ hχ hq x hx c T' δ hc1 hc2 hT'2 hδ0 hδ1 hgood'
  have e3 := h₇ hχ hq x (by linarith) T T' hT hT'.1 hT'.2
  have hsplit : psi0LR χ x - (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val +
        trivialSumL χ x) =
      (psi0LR χ x - explicitJL χ x c T') + (explicitJL χ x c T' -
        (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hq T', perronKernel x ρ.val +
          trivialSumL χ x)) -
      (∑ ρ ∈ zerosBelowL hχ hq T', perronKernel x ρ.val -
        ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val) := by ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  set ℓ := Real.log q + Real.log x + Real.log T with hℓ
  have hLℓ : L ≤ ℓ := by rw [hℓ, ← hLdef]; linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hlog3 := log_add_three_le hT
  have hT2 : Real.log (T' + 2) ≤ Real.log (T + 3) :=
    Real.log_le_log (by linarith) (by linarith [hT'.2])
  have hq3 : Real.log q + Real.log (T + 3) ≤ 3 * ℓ := by rw [hℓ, ← hLdef]; linarith
  have hq3' : Real.log q + Real.log (T' + 2) ≤ 3 * ℓ := by linarith
  set M := min 1 (x / (T * distPrimePow x)) with hMdef
  have hd0 := distPrimePow_pos x
  have hM0 : 0 ≤ M := le_min zero_le_one (by positivity)
  -- first error
  have b1 : ‖psi0LR χ x - explicitJL χ x c T'‖ ≤ A₈ * (x * ℓ ^ 2 / T + L * M) := by
    refine e1.trans ?_
    have h1 : x * L ^ 2 / T' ≤ x * ℓ ^ 2 / T := by
      calc x * L ^ 2 / T' ≤ x * L ^ 2 / T := div_le_div_of_nonneg_left (by positivity) hT0 hT'.1
        _ ≤ x * ℓ ^ 2 / T := by gcongr
    have h2 : min 1 (x / (T' * distPrimePow x)) ≤ M := by
      refine min_le_min le_rfl ?_
      exact div_le_div_of_nonneg_left hx0.le (by positivity) (by gcongr; exact hT'.1)
    have h3 : L * min 1 (x / (T' * distPrimePow x)) ≤ L * M := mul_le_mul_of_nonneg_left h2 hL0.le
    gcongr
  -- second error
  have b2 : ‖explicitJL χ x c T' - (residueZeroL χ x -
        ∑ ρ ∈ zerosBelowL hχ hq T', perronKernel x ρ.val + trivialSumL χ x)‖ ≤
      12 * B * (3 * A₉ + 4) * (x * ℓ ^ 2 / T) := by
    refine e2.trans ?_
    have hX : x ^ c / (δ * T' * L) ≤ 6 * (A₉ + 1) * x * ℓ / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]
      have h1 : 1 ≤ δ * (A₉ * (Real.log q + Real.log T) + 1) := by
        have := (div_le_iff₀ hδ0).mp hinvδ; linarith
      have h2 : A₉ * (Real.log q + Real.log T) + 1 ≤ (A₉ + 1) * ℓ := by
        have : Real.log q + Real.log T ≤ ℓ := by rw [hℓ, ← hLdef]; linarith
        nlinarith
      have h3 : 1 ≤ δ * ((A₉ + 1) * ℓ) := h1.trans (by gcongr)
      have h4 : T ≤ T' * (2 * L) := by nlinarith [hT'.1]
      have h5 : x ^ c * T ≤ 3 * x * (T' * (2 * L)) := mul_le_mul hxc h4 hT0.le (by positivity)
      have h6 : 3 * x * (T' * (2 * L)) ≤ 3 * x * (T' * (2 * L)) * (δ * ((A₉ + 1) * ℓ)) := by
        have : 0 ≤ 3 * x * (T' * (2 * L)) := by positivity
        nlinarith
      calc x ^ c * T ≤ 3 * x * (T' * (2 * L)) * (δ * ((A₉ + 1) * ℓ)) := h5.trans h6
        _ = 6 * (A₉ + 1) * x * ℓ * (δ * T' * L) := by ring
    have hY : x ^ (-1 / 4 : ℝ) / (T' * L) ≤ 2 * x * ℓ / T := by
      have h1 : x ^ (-1 / 4 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      rw [div_le_div_iff₀ (by positivity) hT0]
      have h2 : T ≤ T' * (2 * L) := by nlinarith [hT'.1]
      have h3 : 1 ≤ x * ℓ := by nlinarith
      calc x ^ (-1 / 4 : ℝ) * T ≤ 1 * (T' * (2 * L)) := mul_le_mul h1 h2 hT0.le zero_le_one
        _ ≤ 2 * x * ℓ * (T' * L) := by
          have : 0 ≤ T' * L := by positivity
          nlinarith
    have hLg : Real.log q + Real.log (T' + 2) + 3 ≤ 6 * ℓ := by linarith
    have hB0 : 0 ≤ B * (Real.log q + Real.log (T' + 2) + 3) := by
      have := Real.log_nonneg (by linarith [hT'.1] : (1 : ℝ) ≤ T' + 2); positivity
    calc B * (Real.log q + Real.log (T' + 2) + 3) *
          (x ^ c / (δ * T' * L) + x ^ (-1 / 4 : ℝ) / (T' * L))
        ≤ B * (6 * ℓ) * (6 * (A₉ + 1) * x * ℓ / T + 2 * x * ℓ / T) := by
          gcongr
      _ = 12 * B * (3 * A₉ + 4) * (x * ℓ ^ 2 / T) := by ring
  -- third error
  have b3 : ‖∑ ρ ∈ zerosBelowL hχ hq T', perronKernel x ρ.val -
      ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val‖ ≤ 3 * A₇ * (x * ℓ ^ 2 / T) := by
    refine e3.trans ?_
    calc A₇ * (Real.log q + Real.log (T + 3)) * x / T ≤ A₇ * (3 * ℓ ^ 2) * x / T := by
          gcongr; linarith
      _ = 3 * A₇ * (x * ℓ ^ 2 / T) := by ring
  have hP : 0 ≤ x * ℓ ^ 2 / T := by positivity
  have hLM : 0 ≤ L * M := mul_nonneg hL0.le hM0
  calc _ ≤ A₈ * (x * ℓ ^ 2 / T + L * M) + 12 * B * (3 * A₉ + 4) * (x * ℓ ^ 2 / T) +
        3 * A₇ * (x * ℓ ^ 2 / T) := add_le_add (add_le_add b1 b2) b3
    _ ≤ (A₈ + 12 * B * (3 * A₉ + 4) + 3 * A₇) * (x * ℓ ^ 2 / T + L * M) := by
        have hpos : 0 ≤ (12 * B * (3 * A₉ + 4) + 3 * A₇) * (L * M) := by positivity
        have key : (A₈ + 12 * B * (3 * A₉ + 4) + 3 * A₇) * (x * ℓ ^ 2 / T + L * M) -
            (A₈ * (x * ℓ ^ 2 / T + L * M) + 12 * B * (3 * A₉ + 4) * (x * ℓ ^ 2 / T) +
              3 * A₇ * (x * ℓ ^ 2 / T)) = (12 * B * (3 * A₉ + 4) + 3 * A₇) * (L * M) := by ring
        linarith

/-- **Davenport, Ch. 19, pp. 115-116 (rows 19-2, 19-3), uniform form** for real `x ≥ 2`:
`∑_{|γ|<T} x^ρ/ρ → r₀ + ∑_{m ≥ 1} x^{a-2m}/(2m - a) - ψ₀(x, χ)` as `T → ∞`. -/
@[kb "davenport1980" "Ch 19, p. 115"]
theorem Davenport.tendsto_sum_L_zeros_real {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    Tendsto (fun T : ℝ ↦ ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val) atTop
      (𝓝 (residueZeroL χ x + trivialSumL χ x - psi0LR χ x)) := by
  obtain ⟨A, hA, h⟩ := Davenport.explicit_formula_psi0L_real
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hx0 : 0 < x := by linarith
  have hd := distPrimePow_pos x
  have hb1 := (tendsto_mul_add_log_sq_div x (Real.log q + Real.log x))
  have h3 : Tendsto (fun T : ℝ ↦ 1 / T) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
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
  have hb := (hb1.add (h6.const_mul (Real.log x))).const_mul A
  simp only [mul_zero, add_zero] at hb
  refine squeeze_zero' (Eventually.of_forall fun T ↦ norm_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop 2] with T hT
  have := h hχ hq x hx T hT
  have e : ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val -
      (residueZeroL χ x + trivialSumL χ x - psi0LR χ x) =
      psi0LR χ x - (residueZeroL χ x - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val +
        trivialSumL χ x) := by ring
  rw [e]
  refine this.trans (le_of_eq ?_)
  ring

/-- **Davenport, Ch. 19, p. 115, (2) (row 19-2)** for real `x`: for `χ` primitive and odd mod
`q > 1` and real `x ≥ 2`, `ψ₀(x, χ) = -∑_ρ x^ρ/ρ - L'/L(0, χ) + ∑_{m ≥ 1} x^{1-2m}/(2m - 1)`, the
sum over the nontrivial zeros `ρ` being `lim_{T → ∞} ∑_{|γ|<T}`. -/
@[kb "davenport1980" "Ch 19, p. 115"]
theorem Davenport.explicit_formula_psi0L_odd_real {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (ha : dirichletParity χ = 1) {x : ℝ} (hx : 2 ≤ x) :
    Tendsto (fun T : ℝ ↦ ∑ ρ ∈ zerosBelowL hχ hq T, (x : ℂ) ^ ρ.val / ρ.val) atTop
      (𝓝 (-(deriv (LFunction χ) 0 / LFunction χ 0) +
        ∑' m : ℕ, (x : ℂ) ^ (-(2 * (m : ℂ) + 1)) / (2 * (m : ℂ) + 1) - psi0LR χ x)) := by
  have h := Davenport.tendsto_sum_L_zeros_real hχ hq hx
  rw [trivialSumL_odd ha] at h
  have hr : residueZeroL χ x = -(deriv (LFunction χ) 0 / LFunction χ 0) := by
    simp [residueZeroL, ha]
  rw [hr] at h
  simpa [perronKernel] using h

/-- **Davenport, Ch. 19, p. 116, (3) (row 19-3)** for real `x`: for `χ` primitive and even mod
`q > 1` and real `x ≥ 2`, `ψ₀(x, χ) = -∑_ρ x^ρ/ρ - log x - b(χ) + ∑_{m ≥ 1} x^{-2m}/(2m)`, where
`L'/L(s, χ) = 1/s + b(χ) + O(|s|)` near `0` (`bEven`). -/
@[kb "davenport1980" "Ch 19, p. 116"]
theorem Davenport.explicit_formula_psi0L_even_real {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (ha : dirichletParity χ = 0) {x : ℝ} (hx : 2 ≤ x) :
    Tendsto (fun T : ℝ ↦ ∑ ρ ∈ zerosBelowL hχ hq T, (x : ℂ) ^ ρ.val / ρ.val) atTop
      (𝓝 (-((Real.log x : ℂ) + bEven χ) +
        ∑' m : ℕ, (x : ℂ) ^ (-(2 * ((m : ℂ) + 1))) / (2 * ((m : ℂ) + 1)) - psi0LR χ x)) := by
  have h := Davenport.tendsto_sum_L_zeros_real hχ hq hx
  rw [trivialSumL_even ha hx] at h
  have hr : residueZeroL χ x = -((Real.log x : ℂ) + bEven χ) := by
    simp [residueZeroL, ha]
  rw [hr] at h
  simpa [perronKernel] using h

end NTKB
