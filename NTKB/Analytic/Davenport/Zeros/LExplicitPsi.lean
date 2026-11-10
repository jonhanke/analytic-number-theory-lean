/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LExplicitFormula
import NTKB.Analytic.Davenport.Zeros.ExplicitPsi

/-!
# The explicit formula for `ψ₀(N, χ)` with error term

**Davenport, Ch. 19, p. 117, (D)-(F) (rows 19-6, 19-7)**, in the following form: for primitive
`χ` mod `q > 1`, integers `N ≥ 3` and `T ≥ 2`, with `ℓ = log q + log N + log T`,
`ψ₀(N, χ) = r₀ - ∑_{|γ|<T} N^ρ/ρ + O(N ℓ²/T + T ℓ N^{-1/2})`,
where `r₀ = -L'/L(0, χ)` for odd `χ` and `r₀ = -log N - b(χ)` for even `χ`. Davenport moves the
contour to `-∞` and keeps the trivial zeros (a sum `O(1/N)`); we stop at `σ = -1/2`, which costs
the term `T ℓ N^{-1/2}` (harmless for `T ≤ N^{1/2}`, and of the size of the error term `N^{1/2} log N`
of (12) for `T ≤ N`).
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

variable {q : ℕ} [NeZero q]

/-- `|x^ρ/ρ| ≤ x/T` for a nontrivial zero of `L(s, χ)` with `|γ| ≥ T > 0` and `x ≥ 1`. -/
lemma norm_perronKernel_L_zero_le {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    {x T : ℝ} (hx : 1 ≤ x) (hT : 0 < T) (ρ : ZeroIndex (dirichletXi χ))
    (hρ : T ≤ |ρ.val.im|) : ‖perronKernel x ρ.val‖ ≤ x / T := by
  rw [norm_perronKernel (by linarith)]
  have hβ := (dirichletXi_zero_mem hχ hq ρ).2.2
  have h1 : x ^ ρ.val.re ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx hβ.le
  have h2 : T ≤ ‖ρ.val‖ := hρ.trans (Complex.abs_im_le_norm _)
  exact div_le_div₀ (by linarith) h1 hT h2

/-- The zeros with `T ≤ |γ| < T + 1` contribute `≪ x log(q(T + 3)) / T`. -/
lemma norm_sum_L_zeros_strip_le :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ x : ℝ, 1 ≤ x → ∀ T T' : ℝ, 2 ≤ T → T ≤ T' → T' ≤ T + 1 →
      ‖∑ ρ ∈ zerosBelowL hχ hq T', perronKernel x ρ.val -
          ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel x ρ.val‖ ≤
        A * (Real.log q + Real.log (T + 3)) * x / T := by
  classical
  obtain ⟨A, hA, h⟩ := Davenport.card_L_zeros_near_le
  refine ⟨2 * A, by positivity, ?_⟩
  intro q _ χ hχ hq x hx T T' hT hTT' hT'T
  have hT0 : 0 < T := by linarith
  have hsub : zerosBelowL hχ hq T ⊆ zerosBelowL hχ hq T' := fun ρ hρ ↦
    mem_zerosBelowL.mpr ((mem_zerosBelowL.mp hρ).trans_le hTT')
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  set a := T + 1 / 2 with ha
  obtain ⟨hf1, hc1⟩ := h hχ hq a
  obtain ⟨hf2, hc2⟩ := h hχ hq (-a)
  have hdiff : zerosBelowL hχ hq T' \ zerosBelowL hχ hq T ⊆ hf1.toFinset ∪ hf2.toFinset := by
    intro ρ hρ
    rw [Finset.mem_sdiff, mem_zerosBelowL, mem_zerosBelowL, not_lt] at hρ
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
  have hlq := Real.log_natCast_nonneg q
  have hcard : ((zerosBelowL hχ hq T' \ zerosBelowL hχ hq T).card : ℝ) ≤
      2 * A * (Real.log q + Real.log (T + 3)) := by
    have h1 : ((zerosBelowL hχ hq T' \ zerosBelowL hχ hq T).card : ℝ) ≤
        hf1.toFinset.card + hf2.toFinset.card := by
      exact_mod_cast (Finset.card_le_card hdiff).trans (Finset.card_union_le _ _)
    rw [← Set.ncard_eq_toFinset_card _ hf1, ← Set.ncard_eq_toFinset_card _ hf2] at h1
    have hl : Real.log (|a| + 2) ≤ Real.log (T + 3) :=
      Real.log_le_log (by positivity) (by rw [abs_of_pos (by linarith)]; linarith)
    have hl' : Real.log (|-a| + 2) ≤ Real.log (T + 3) := by rwa [abs_neg]
    nlinarith
  calc ‖∑ ρ ∈ zerosBelowL hχ hq T' \ zerosBelowL hχ hq T, perronKernel x ρ.val‖
      ≤ ∑ ρ ∈ zerosBelowL hχ hq T' \ zerosBelowL hχ hq T, x / T := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
        rw [Finset.mem_sdiff, mem_zerosBelowL, mem_zerosBelowL, not_lt] at hρ
        exact norm_perronKernel_L_zero_le hχ hq hx hT0 ρ hρ.2
    _ = (zerosBelowL hχ hq T' \ zerosBelowL hχ hq T).card * (x / T) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * A * (Real.log q + Real.log (T + 3)) * (x / T) := by gcongr
    _ = 2 * A * (Real.log q + Real.log (T + 3)) * x / T := by ring

set_option maxHeartbeats 1000000 in
/-- **Davenport, Ch. 19, p. 117, (D)-(F) (rows 19-6, 19-7)**, integer form (see the module
docstring): there is an absolute `A` such that for primitive `χ` mod `q > 1`, integers `N ≥ 3`
and `T ≥ 2`, with `ℓ = log q + log N + log T`,
`|ψ₀(N, χ) - (r₀ - ∑_{|γ|<T} N^ρ/ρ)| ≤ A (N ℓ²/T + T ℓ N^{-1/2})`. -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.explicit_formula_psi0L :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ N : ℕ, 3 ≤ N → ∀ T : ℝ, 2 ≤ T →
      ‖psi0L χ N - (residueZeroL χ N - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val)‖ ≤
        A * (N * (Real.log q + Real.log N + Real.log T) ^ 2 / T +
          T * (Real.log q + Real.log N + Real.log T) * (N : ℝ) ^ (-1 / 2 : ℝ)) := by
  obtain ⟨B, hB, hJ⟩ := Davenport.norm_explicitJL_sub_main_le
  obtain ⟨A₉, hA₉, h₉⟩ := Davenport.exists_good_height_L
  obtain ⟨A₇, hA₇, h₇⟩ := norm_sum_L_zeros_strip_le
  have he := Real.exp_one_lt_d9
  refine ⟨100 + 30 * B * (A₉ + 1) + 6 * A₇, by positivity, ?_⟩
  intro q _ χ hχ hq N hN T hT
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
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  -- the good height
  obtain ⟨T', hT', hgood⟩ := h₉ hχ hq T hT
  have hT'0 : 0 < T' := by linarith [hT'.1]
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
  have e1 := Davenport.norm_psi0L_sub_explicitJL_le χ hN hT'0
  have e2 := hJ hχ hq N (by linarith) c T' δ hc1 hc2 (by linarith [hT'.1]) hδ0 hδ1 hgood'
  have e3 := h₇ hχ hq N (by linarith) T T' hT hT'.1 hT'.2
  have hsplit : psi0L χ N - (residueZeroL χ N - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val) =
      (psi0L χ N - explicitJL χ N c T') + (explicitJL χ N c T' -
        (residueZeroL χ N - ∑ ρ ∈ zerosBelowL hχ hq T', perronKernel N ρ.val)) -
      (∑ ρ ∈ zerosBelowL hχ hq T', perronKernel N ρ.val -
        ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val) := by ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  set ℓ := Real.log q + Real.log N + Real.log T with hℓ
  have hLℓ : L ≤ ℓ := by rw [hℓ, ← hLdef]; linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hlog3 := log_add_three_le hT
  have hT2 : Real.log (T' + 2) ≤ Real.log (T + 3) :=
    Real.log_le_log (by linarith) (by linarith [hT'.2])
  have hq3 : Real.log q + Real.log (T + 3) ≤ 3 * ℓ := by rw [hℓ, ← hLdef]; linarith
  have hq3' : Real.log q + Real.log (T' + 2) ≤ 3 * ℓ := by linarith
  set E := (N : ℝ) ^ (-1 / 2 : ℝ) with hE
  have hE0 : 0 ≤ E := by positivity
  -- first error
  have b1 : ‖psi0L χ N - explicitJL χ N c T'‖ ≤ 100 * (N * ℓ ^ 2 / T) := by
    refine e1.trans ?_
    have h1 : 100 * N * L ^ 2 / T' ≤ 100 * N * L ^ 2 / T :=
      div_le_div_of_nonneg_left (by positivity) hT0 hT'.1
    have h2 : 100 * N * L ^ 2 / T ≤ 100 * (N * ℓ ^ 2 / T) := by
      rw [mul_div_assoc', show (100 : ℝ) * N * L ^ 2 = 100 * (N * L ^ 2) by ring]
      gcongr
    linarith
  -- second error
  have b2 : ‖explicitJL χ N c T' - (residueZeroL χ N -
        ∑ ρ ∈ zerosBelowL hχ hq T', perronKernel N ρ.val)‖ ≤
      9 * B * (A₉ + 1) * (N * ℓ ^ 2 / T) + 6 * B * (T * ℓ * E) := by
    refine e2.trans ?_
    rw [hNc]
    have hX : (N : ℝ) * Real.exp 1 / (δ * T' * L) ≤ 3 * (A₉ + 1) * N * ℓ / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]
      have h1 : 1 ≤ δ * (A₉ * (Real.log q + Real.log T) + 1) := by
        have := (div_le_iff₀ hδ0).mp hinvδ; linarith
      have h2 : A₉ * (Real.log q + Real.log T) + 1 ≤ (A₉ + 1) * ℓ := by
        have : Real.log q + Real.log T ≤ ℓ := by rw [hℓ, ← hLdef]; linarith
        nlinarith
      have h3 : 1 ≤ δ * ((A₉ + 1) * ℓ) := h1.trans (by gcongr)
      have h4 : T ≤ T' * L := by nlinarith [hT'.1]
      have h5 : (N : ℝ) * Real.exp 1 * T ≤ N * 3 * (T' * L) := by
        have := mul_le_mul (by linarith : Real.exp 1 ≤ 3) h4 hT0.le (by norm_num)
        nlinarith
      have h6 : (N : ℝ) * 3 * (T' * L) ≤ N * 3 * (T' * L) * (δ * ((A₉ + 1) * ℓ)) := by
        have : 0 ≤ (N : ℝ) * 3 * (T' * L) := by positivity
        nlinarith
      nlinarith
    have hY : T' * E ≤ 2 * (T * E) := by
      have : T' ≤ 2 * T := by linarith [hT'.2]
      nlinarith
    have hB0 : 0 ≤ B * (Real.log q + Real.log (T' + 2)) := by
      have := Real.log_nonneg (by linarith [hT'.1] : (1 : ℝ) ≤ T' + 2); positivity
    calc B * (Real.log q + Real.log (T' + 2)) * ((N : ℝ) * Real.exp 1 / (δ * T' * L) + T' * E)
        ≤ B * (3 * ℓ) * (3 * (A₉ + 1) * N * ℓ / T + 2 * (T * E)) := by
          gcongr
      _ = 9 * B * (A₉ + 1) * (N * ℓ ^ 2 / T) + 6 * B * (T * ℓ * E) := by ring
  -- third error
  have b3 : ‖∑ ρ ∈ zerosBelowL hχ hq T', perronKernel N ρ.val -
      ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val‖ ≤ 3 * A₇ * (N * ℓ ^ 2 / T) := by
    refine e3.trans ?_
    calc A₇ * (Real.log q + Real.log (T + 3)) * N / T ≤ A₇ * (3 * ℓ ^ 2) * N / T := by
          gcongr; linarith
      _ = 3 * A₇ * (N * ℓ ^ 2 / T) := by ring
  have hP : 0 ≤ (N : ℝ) * ℓ ^ 2 / T := by positivity
  have hQ : 0 ≤ T * ℓ * E := by positivity
  have hA9 : 0 ≤ A₉ := hA₉.le
  have hB' : 6 * B ≤ 30 * B * (A₉ + 1) := by nlinarith
  calc _ ≤ 100 * (N * ℓ ^ 2 / T) + (9 * B * (A₉ + 1) * (N * ℓ ^ 2 / T) + 6 * B * (T * ℓ * E)) +
        3 * A₇ * (N * ℓ ^ 2 / T) := add_le_add (add_le_add b1 b2) b3
    _ ≤ (100 + 30 * B * (A₉ + 1) + 6 * A₇) * (N * ℓ ^ 2 / T + T * ℓ * E) := by
        nlinarith

end NTKB
