/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitFormula

/-!
# The explicit formula for `ψ₀(N)` with error term

**Davenport, Ch. 17, p. 110, (13) (rows 17-13, 17-15).** For integers `N ≥ 3` and `T ≥ 2`,
`ψ₀(N) = N - ∑_{|γ| < T} N^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - N^{-2}) + O(N log²(NT)/T)`.
-/

open Filter Topology Complex Set
open scoped Real

namespace NTKB

/-- `|x^ρ/ρ| ≤ x/T` for a nontrivial zero with `|γ| ≥ T > 0` and `x ≥ 1`. -/
lemma norm_perronKernel_zero_le {x T : ℝ} (hx : 1 ≤ x) (hT : 0 < T) (ρ : ZeroIndex riemannXi)
    (hρ : T ≤ |ρ.val.im|) : ‖perronKernel x ρ.val‖ ≤ x / T := by
  rw [norm_perronKernel (by linarith)]
  have hβ := (riemannXi_zero_mem ρ).2.2
  have h1 : x ^ ρ.val.re ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx hβ.le
  have h2 : T ≤ ‖ρ.val‖ := hρ.trans (Complex.abs_im_le_norm _)
  exact div_le_div₀ (by linarith) h1 hT h2

/-- The zeros with `T ≤ |γ| < T + 1` contribute `≪ x log T / T`. -/
lemma norm_sum_zeros_strip_le :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x → ∀ T T' : ℝ, 2 ≤ T → T ≤ T' → T' ≤ T + 1 →
      ‖∑ ρ ∈ zerosBelow T', perronKernel x ρ.val - ∑ ρ ∈ zerosBelow T, perronKernel x ρ.val‖ ≤
        A * x * Real.log (T + 3) / T := by
  classical
  obtain ⟨A, hA, h⟩ := Davenport.card_zeta_zeros_near_le
  refine ⟨2 * A, by positivity, fun x hx T T' hT hTT' hT'T ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hsub : zerosBelow T ⊆ zerosBelow T' := fun ρ hρ ↦
    mem_zerosBelow.mpr ((mem_zerosBelow.mp hρ).trans_le hTT')
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  set a := T + 1 / 2 with ha
  obtain ⟨hf1, hc1⟩ := h a
  obtain ⟨hf2, hc2⟩ := h (-a)
  have hdiff : zerosBelow T' \ zerosBelow T ⊆ hf1.toFinset ∪ hf2.toFinset := by
    intro ρ hρ
    rw [Finset.mem_sdiff, mem_zerosBelow, mem_zerosBelow, not_lt] at hρ
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    rcases le_or_gt 0 ρ.val.im with h0 | h0
    · left
      rw [abs_of_nonneg h0] at hρ
      show |ρ.val.im - a| < 1
      rw [abs_lt]; constructor <;> linarith [hρ.1, hρ.2, ha]
    · right
      rw [abs_of_neg h0] at hρ
      show |ρ.val.im - -a| < 1
      rw [abs_lt]; constructor <;> linarith [hρ.1, hρ.2, ha]
  have hcard : ((zerosBelow T' \ zerosBelow T).card : ℝ) ≤ 2 * A * Real.log (T + 3) := by
    have h1 : ((zerosBelow T' \ zerosBelow T).card : ℝ) ≤ hf1.toFinset.card + hf2.toFinset.card := by
      exact_mod_cast (Finset.card_le_card hdiff).trans (Finset.card_union_le _ _)
    rw [← Set.ncard_eq_toFinset_card _ hf1, ← Set.ncard_eq_toFinset_card _ hf2] at h1
    have hl : Real.log (|a| + 2) ≤ Real.log (T + 3) :=
      Real.log_le_log (by positivity) (by rw [abs_of_pos (by linarith)]; linarith)
    have hl' : Real.log (|-a| + 2) ≤ Real.log (T + 3) := by rwa [abs_neg]
    nlinarith
  calc ‖∑ ρ ∈ zerosBelow T' \ zerosBelow T, perronKernel x ρ.val‖
      ≤ ∑ ρ ∈ zerosBelow T' \ zerosBelow T, x / T := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
        rw [Finset.mem_sdiff, mem_zerosBelow, mem_zerosBelow, not_lt] at hρ
        exact norm_perronKernel_zero_le hx hT0 ρ hρ.2
    _ = (zerosBelow T' \ zerosBelow T).card * (x / T) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * A * Real.log (T + 3) * (x / T) := by gcongr
    _ = 2 * A * x * Real.log (T + 3) / T := by ring

/-- `log(T + 3) ≤ 3 log T` for `T ≥ 2`. -/
lemma log_add_three_le {T : ℝ} (hT : 2 ≤ T) : Real.log (T + 3) ≤ 3 * Real.log T := by
  rw [show (3 : ℝ) * Real.log T = ((3 : ℕ) : ℝ) * Real.log T by norm_num, ← Real.log_pow]
  have h4 : 4 ≤ T * T := by nlinarith
  have h5 : 4 * T ≤ T * T * T := by nlinarith
  exact Real.log_le_log (by linarith) (by push_cast; nlinarith)

/-- **Davenport, Ch. 17, p. 110, (13) (rows 17-13, 17-15)**: there is an absolute constant `A`
such that for all integers `N ≥ 3` and all `T ≥ 2`,
`|ψ₀(N) - (N - ∑_{|γ| < T} N^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - N^{-2}))| ≤ A N log²(NT)/T`. -/
@[kb "davenport1980" "Ch 17, p. 110"]
theorem Davenport.explicit_formula_psi0 :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 3 ≤ N → ∀ T : ℝ, 2 ≤ T →
      ‖(psi0 N : ℂ) - explicitMain N T‖ ≤ A * N * Real.log (N * T) ^ 2 / T := by
  obtain ⟨A₈, hA₈, h₈⟩ := Davenport.norm_psi0_sub_explicitJ_le
  obtain ⟨B, hB, hJ⟩ := Davenport.norm_explicitJ_sub_main_le
  obtain ⟨A₉, hA₉, h₉⟩ := Davenport.exists_good_height
  obtain ⟨A₇, hA₇, h₇⟩ := norm_sum_zeros_strip_le
  have he := Real.exp_one_lt_d9
  refine ⟨A₈ + 3 * (B * 3 * (A₉ + 1)) + 3 * A₇, by positivity, fun N hN T hT ↦ ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  set L := Real.log N with hLdef
  have hL : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt hN0]; linarith
  set c := 1 + 1 / L with hcdef
  have hc1 : 1 < c := by rw [hcdef]; have : 0 < 1 / L := by positivity
                         linarith
  have hc2 : c ≤ 2 := by
    rw [hcdef]; have : 1 / L ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hNc : (N : ℝ) ^ c = N * Real.exp 1 := by
    rw [hcdef, Real.rpow_add hN0, Real.rpow_one, Real.rpow_def_of_pos hN0, ← hLdef,
      mul_one_div_cancel (by linarith)]
  -- the good height
  obtain ⟨T', hT', hgood⟩ := h₉ T hT
  have hT'0 : 0 < T' := by linarith [hT'.1]
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
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
  have e1 := h₈ N hN T' hT'0
  have e2 := hJ N (by linarith) c T' δ hc1 hc2 (by linarith [hT'.1]) hδ0 hδ1 hgood'
  have e3 := h₇ N (by linarith) T T' hT hT'.1 hT'.2
  have hsplit : (psi0 N : ℂ) - explicitMain N T =
      ((psi0 N : ℂ) - explicitJ N c T') + (explicitJ N c T' - explicitMain N T') -
        (∑ ρ ∈ zerosBelow T', perronKernel N ρ.val - ∑ ρ ∈ zerosBelow T, perronKernel N ρ.val) := by
    simp only [explicitMain]; ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  -- estimates in terms of `Λ := log(NT)`
  set Λ := Real.log (N * T) with hΛdef
  have hLΛ : L ≤ Λ := Real.log_le_log hN0 (by nlinarith)
  have hTΛ : Real.log T ≤ Λ := Real.log_le_log hT0 (by nlinarith)
  have hΛ1 : 1 < Λ := by linarith
  have hlog3 := log_add_three_le hT
  have hT2 : Real.log (T' + 2) ≤ Real.log (T + 3) :=
    Real.log_le_log (by linarith) (by linarith [hT'.2])
  have b1 : ‖(psi0 N : ℂ) - explicitJ N c T'‖ ≤ A₈ * N * Λ ^ 2 / T := by
    refine e1.trans ?_
    have : A₈ * N * L ^ 2 ≤ A₈ * N * Λ ^ 2 := by gcongr
    calc A₈ * N * L ^ 2 / T' ≤ A₈ * N * L ^ 2 / T :=
          div_le_div_of_nonneg_left (by positivity) hT0 hT'.1
      _ ≤ A₈ * N * Λ ^ 2 / T := by gcongr
  have b2 : ‖explicitJ N c T' - explicitMain N T'‖ ≤ 3 * (B * 3 * (A₉ + 1)) * N * Λ ^ 2 / T := by
    refine e2.trans ?_
    rw [hNc]
    have hl2 : 0 ≤ Real.log (T' + 2) := Real.log_nonneg (by linarith)
    have h1 : B * (N * Real.exp 1) * Real.log (T' + 2) / (δ * T' * L) ≤
        B * (N * 3) * (3 * Λ) * (A₉ * Λ + 1) / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]
      have hA : 1 ≤ δ * (A₉ * Real.log T + 1) := by
        have := (div_le_iff₀ hδ0).mp hinvδ; linarith
      have hA' : A₉ * Real.log T + 1 ≤ A₉ * Λ + 1 := by gcongr
      have hq : Real.log (T' + 2) ≤ 3 * Λ := by linarith
      have hx : 0 ≤ B * (N * Real.exp 1) * Real.log (T' + 2) := by positivity
      -- LHS * T ≤ B N e log(T'+2) T ≤ B N e log(T'+2) δ (A₉ log T + 1) T' L
      calc B * (N * Real.exp 1) * Real.log (T' + 2) * T
          ≤ B * (N * Real.exp 1) * Real.log (T' + 2) * (δ * (A₉ * Real.log T + 1) * T' * L) := by
            apply mul_le_mul_of_nonneg_left _ hx
            have : T ≤ T' * L := by nlinarith [hT'.1]
            nlinarith
        _ = (B * (N * Real.exp 1) * Real.log (T' + 2) * (A₉ * Real.log T + 1)) * (δ * T' * L) := by
            ring
        _ ≤ (B * (N * 3) * (3 * Λ) * (A₉ * Λ + 1)) * (δ * T' * L) := by
            gcongr
            · linarith
      -- note `gcongr` needs nonnegativity of `A₉ log T + 1`
    refine h1.trans ?_
    apply div_le_div_of_nonneg_right _ hT0.le
    have : A₉ * Λ + 1 ≤ (A₉ + 1) * Λ := by nlinarith
    have hN' : (0 : ℝ) ≤ B * N := by positivity
    calc B * (N * 3) * (3 * Λ) * (A₉ * Λ + 1) = 9 * (B * N) * Λ * (A₉ * Λ + 1) := by ring
      _ ≤ 9 * (B * N) * Λ * ((A₉ + 1) * Λ) := by gcongr
      _ = 3 * (B * 3 * (A₉ + 1)) * N * Λ ^ 2 := by ring
  have b3 : ‖∑ ρ ∈ zerosBelow T', perronKernel N ρ.val - ∑ ρ ∈ zerosBelow T, perronKernel N ρ.val‖ ≤
      3 * A₇ * N * Λ ^ 2 / T := by
    refine e3.trans ?_
    apply div_le_div_of_nonneg_right _ hT0.le
    have hΛ2 : Λ ≤ Λ ^ 2 := by nlinarith
    have h1 : Real.log (T + 3) ≤ 3 * Λ ^ 2 := by linarith
    have h2 : 0 ≤ A₇ * N := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    linarith
  calc _ ≤ A₈ * N * Λ ^ 2 / T + 3 * (B * 3 * (A₉ + 1)) * N * Λ ^ 2 / T + 3 * A₇ * N * Λ ^ 2 / T :=
        add_le_add (add_le_add b1 b2) b3
    _ = (A₈ + 3 * (B * 3 * (A₉ + 1)) + 3 * A₇) * N * Λ ^ 2 / T := by ring

/-- **Davenport, Ch. 17, p. 104, (row 17-2)** at integers `N ≥ 3`: von Mangoldt's explicit formula
`ψ₀(N) = N - ∑_ρ N^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - N^{-2})`, the sum over the zeros taken
symmetrically: `lim_{T → ∞} (N - ∑_{|γ|<T} N^ρ/ρ - ζ'(0)/ζ(0) - ½ log(1 - N^{-2})) = ψ₀(N)`. -/
@[kb "davenport1980" "Ch 17, p. 104"]
theorem Davenport.tendsto_explicitMain (N : ℕ) (hN : 3 ≤ N) :
    Tendsto (fun T : ℝ ↦ explicitMain N T) atTop (𝓝 (psi0 N : ℂ)) := by
  obtain ⟨A, hA, h⟩ := Davenport.explicit_formula_psi0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- the bound `A N log²(NT)/T → 0`
  have hlim : Tendsto (fun T : ℝ ↦ A * N * Real.log (N * T) ^ 2 / T) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ ↦ Real.log T ^ 2 / (1 * T + 0)) atTop (𝓝 0) :=
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    have h2 : Tendsto (fun T : ℝ ↦ Real.log T ^ 1 / (1 * T + 0)) atTop (𝓝 0) :=
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h3 : Tendsto (fun T : ℝ ↦ 1 / T) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
    have h4 := ((h1.add (h2.const_mul (2 * Real.log N))).add (h3.const_mul (Real.log N ^ 2))).const_mul
      (A * N)
    simp only [mul_zero, add_zero, one_mul] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Real.log_mul hN0.ne' hT.ne']
    field_simp
    ring
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  rw [norm_norm, norm_sub_rev]
  exact h N hN T hT

end NTKB
