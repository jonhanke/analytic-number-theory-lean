/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LExceptionalFormula

/-!
# `ψ₀(N, χ) = -∑_{exceptional ρ} N^ρ/ρ + R`

**Davenport, Ch. 19, (11)-(12) and Ch. 20, (E)-(F), p. 122 (rows 19-12, 19-14).** See
`LExceptionalFormula` for the conventions.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ComplexConjugate

namespace NTKB

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- **Davenport, Ch. 19, (11)-(12) and Ch. 20, (E)-(F), p. 122 (rows 19-12, 19-14)**, for
primitive `χ` and integers `N ≥ 3`, `T ≥ 2`, with `ℓ = log q + log N + log T`, `c = 1/16200`:
`|ψ₀(N, χ) + ∑_{exceptional ρ, |γ| < T} N^ρ/ρ| ≤ A (N ℓ²/T + T ℓ N^{-1/2} + ℓ² + ℓ N^{1/2} log N
  + N ℓ² exp(-c log N/log(qT)))`. -/
@[kb "davenport1980" "Ch 20, p. 122"]
theorem Davenport.psi0L_exceptional :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ N : ℕ, 3 ≤ N → ∀ T : ℝ, 2 ≤ T →
      ‖psi0L χ N + ∑ ρ ∈ (zerosBelowL hχ hq T).filter (fun ρ ↦ IsExcPoint q ρ.val),
          perronKernel N ρ.val‖ ≤
        A * (N * (Real.log q + Real.log N + Real.log T) ^ 2 / T +
          T * (Real.log q + Real.log N + Real.log T) * (N : ℝ) ^ (-1 / 2 : ℝ) +
          (Real.log q + Real.log N + Real.log T) ^ 2 +
          (Real.log q + Real.log N + Real.log T) * (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N +
          N * (Real.log q + Real.log N + Real.log T) ^ 2 *
            Real.exp (-(1 / 16200 * Real.log N / logQT q T))) := by
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.explicit_formula_psi0L'
  obtain ⟨A₆, hA₆, h₆⟩ := card_zerosBelowL_one_le
  obtain ⟨C₇, hC₇, h₇⟩ := Davenport.sum_L_zeros_inv_norm_le
  refine ⟨A₁ + 70000 * A₆ + C₇ + 1, by positivity, ?_⟩
  intro q _ χ hχ hq N hN T hT
  have hχ1 := ne_one_of_isPrimitive hχ hq
  have hq2 := two_le_of_ne_one hχ1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlN : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hN0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlq : 0 < Real.log q := Real.log_pos (by linarith)
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  set ℓ := Real.log q + Real.log N + Real.log T with hℓ
  have hℓ1 : 1 ≤ ℓ := by linarith
  set Z1 := zerosBelowL hχ hq 1
  set ZT := zerosBelowL hχ hq T
  set E := Real.exp (-(1 / 16200 * Real.log N / logQT q T))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set P : ZeroIndex (dirichletXi χ) → Prop := fun ρ ↦ IsExcPoint q ρ.val with hP
  set M : ZeroIndex (dirichletXi χ) → Prop := fun ρ ↦ IsExcPoint q (1 - conj ρ.val) with hM
  set k : ZeroIndex (dirichletXi χ) → ℂ := fun ρ ↦ perronKernel N ρ.val with hk
  set iv : ZeroIndex (dirichletXi χ) → ℂ := fun ρ ↦ 1 / ρ.val with hiv
  have e₁ := h₁ hχ hq N hN T hT
  have hc1 := h₆ hχ hq
  set c1 : ℝ := (Z1.card : ℝ)
  -- structural facts
  have hPim : ∀ ρ, P ρ → ρ.val.im = 0 := fun ρ h ↦
    (Davenport.exceptional_zero_real hχ1 (dirichletXi_zero_mem hχ hq ρ).1 h).2
  have hMim : ∀ ρ, M ρ → ρ.val.im = 0 := fun ρ h ↦ (mirror_exc_real hχ hq ρ h).1
  -- the decomposition
  have hsT : ∑ ρ ∈ ZT, k ρ = ∑ ρ ∈ ZT.filter P, k ρ +
      (∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), k ρ +
        ∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), k ρ) := by
    have h1 := Finset.sum_filter_add_sum_filter_not ZT P k
    have h2 := Finset.sum_filter_add_sum_filter_not (ZT.filter (fun ρ ↦ ¬ P ρ)) M k
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    rw [h2]; exact h1.symm
  have hs1 : ∑ ρ ∈ Z1, iv ρ = ∑ ρ ∈ Z1.filter P, iv ρ +
      (∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), iv ρ +
        ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), iv ρ) := by
    have h1 := Finset.sum_filter_add_sum_filter_not Z1 P iv
    have h2 := Finset.sum_filter_add_sum_filter_not (Z1.filter (fun ρ ↦ ¬ P ρ)) M iv
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    rw [h2]; exact h1.symm
  have hTM : ZT.filter (fun ρ ↦ ¬ P ρ ∧ M ρ) = Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ) := by
    ext ρ
    simp only [Finset.mem_filter, ZT, Z1, mem_zerosBelowL]
    constructor
    · rintro ⟨-, h⟩; exact ⟨by rw [hMim ρ h.2]; simp, h⟩
    · rintro ⟨h1, h⟩; exact ⟨h1.trans_le (by linarith), h⟩
  have hid : psi0L χ N + ∑ ρ ∈ ZT.filter P, k ρ =
      (psi0L χ N - (∑ ρ ∈ Z1, iv ρ - ∑ ρ ∈ ZT, k ρ)) + ∑ ρ ∈ Z1.filter P, iv ρ +
        ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), (iv ρ - k ρ) +
        ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), iv ρ -
        ∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), k ρ := by
    rw [hsT, hs1, hTM, Finset.sum_sub_distrib]
    ring
  rw [hid]
  -- the bounds
  have B1 : ‖∑ ρ ∈ Z1.filter P, iv ρ‖ ≤ 2 * c1 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ρ ∈ Z1.filter P, ‖iv ρ‖ ≤ ∑ ρ ∈ Z1.filter P, (2 : ℝ) :=
          Finset.sum_le_sum fun ρ hρ ↦ norm_inv_le_of_exc hχ1 (Finset.mem_filter.mp hρ).2
      _ ≤ 2 * c1 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          gcongr; exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
  have B2 : ‖∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), (iv ρ - k ρ)‖ ≤
      c1 * ((N : ℝ) ^ (1 / 2 : ℝ) * Real.log N) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), ‖iv ρ - k ρ‖
        ≤ ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N :=
          Finset.sum_le_sum fun ρ hρ ↦
            norm_inv_sub_kernel_le_of_mirror hχ hq ρ (Finset.mem_filter.mp hρ).2.2 hN1
      _ ≤ c1 * ((N : ℝ) ^ (1 / 2 : ℝ) * Real.log N) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N := by positivity
          gcongr; exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
  have B3 : ‖∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), iv ρ‖ ≤ c1 * (16200 * Real.log q) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), ‖iv ρ‖
        ≤ ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), 16200 * Real.log q := by
          refine Finset.sum_le_sum fun ρ hρ ↦ ?_
          rw [Finset.mem_filter] at hρ
          exact norm_inv_le_of_not_mirror hχ1 (mem_zerosBelowL.mp hρ.1)
            (dirichletXi_zero_mem hχ hq ρ).2.1 hρ.2.2
      _ ≤ c1 * (16200 * Real.log q) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr; exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
  -- the remaining zeros up to `T`
  set u : ZeroIndex (dirichletXi χ) → ℝ := fun ρ ↦
    if |ρ.val.im| < 1 then 16200 * Real.log q else 0
  set w : ZeroIndex (dirichletXi χ) → ℝ := fun ρ ↦ if 1 ≤ |ρ.val.im| then 1 / ‖ρ.val‖ else 0
  have hu0 : ∀ ρ, 0 ≤ u ρ := fun ρ ↦ by simp only [u]; split_ifs <;> positivity
  have hw0 : ∀ ρ, 0 ≤ w ρ := fun ρ ↦ by simp only [w]; split_ifs <;> positivity
  have hsumu : ∑ ρ ∈ ZT, u ρ = c1 * (16200 * Real.log q) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have : ZT.filter (fun ρ ↦ |ρ.val.im| < 1) = Z1 := by
      ext ρ; simp only [Finset.mem_filter, ZT, Z1, mem_zerosBelowL]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨h.trans_le (by linarith), h⟩
    rw [this]
  have hsumw := h₇ hχ hq T hT
  have B4 : ‖∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), k ρ‖ ≤
      N * E * (c1 * (16200 * Real.log q) + C₇ * (Real.log q + Real.log T) * Real.log T) := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), ‖k ρ‖ ≤ N * E * (u ρ + w ρ) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hβ := dirichletXi_zero_mem hχ hq ρ
      have hρ0 : 0 < ‖ρ.val‖ := by linarith [Complex.re_le_norm ρ.val, hβ.2.1]
      simp only [k]
      rw [norm_perronKernel hN0]
      have hc := norm_cpow_le_of_not_exc hχ1 hN1 (by linarith) (mem_zerosBelowL.mp hρ.1) hρ.2.1
      have hinv : 1 / ‖ρ.val‖ ≤ u ρ + w ρ := by
        simp only [u, w]
        by_cases h1 : |ρ.val.im| < 1
        · have := norm_inv_le_of_not_mirror hχ1 h1 hβ.2.1 hρ.2.2
          rw [norm_div, norm_one] at this
          rw [if_pos h1, if_neg (not_le.mpr h1)]; linarith
        · rw [if_neg h1, if_pos (not_lt.mp h1)]; linarith
      calc (N : ℝ) ^ ρ.val.re / ‖ρ.val‖ = (N : ℝ) ^ ρ.val.re * (1 / ‖ρ.val‖) := by ring
        _ ≤ (N * E) * (u ρ + w ρ) := by
            apply mul_le_mul hc hinv (by positivity) (by positivity)
    calc ∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), ‖k ρ‖
        ≤ ∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), N * E * (u ρ + w ρ) := Finset.sum_le_sum hpt
      _ ≤ ∑ ρ ∈ ZT, N * E * (u ρ + w ρ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro ρ _ _; have := hu0 ρ; have := hw0 ρ; positivity
      _ = N * E * (∑ ρ ∈ ZT, u ρ + ∑ ρ ∈ ZT, w ρ) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ N * E * (c1 * (16200 * Real.log q) + C₇ * (Real.log q + Real.log T) * Real.log T) := by
          rw [hsumu]; gcongr
  -- assemble
  have hc1' : c1 ≤ 2 * A₆ * ℓ := by
    have : Real.log q + 1 ≤ 2 * ℓ := by rw [hℓ]; linarith
    calc c1 ≤ A₆ * (Real.log q + 1) := hc1
      _ ≤ A₆ * (2 * ℓ) := by gcongr
      _ = 2 * A₆ * ℓ := by ring
  have hc10 : 0 ≤ c1 := by positivity
  have hlqℓ : Real.log q ≤ ℓ := by rw [hℓ]; linarith
  have hqTℓ : (Real.log q + Real.log T) * Real.log T ≤ ℓ ^ 2 := by
    have h1 : Real.log q + Real.log T ≤ ℓ := by rw [hℓ]; linarith
    have h2 : Real.log T ≤ ℓ := by rw [hℓ]; linarith
    nlinarith
  set X1 := (N : ℝ) * ℓ ^ 2 / T
  set X2 := T * ℓ * (N : ℝ) ^ (-1 / 2 : ℝ)
  set X3 := ℓ ^ 2
  set X4 := ℓ * (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N
  set X5 := (N : ℝ) * ℓ ^ 2 * E
  have hX1 : 0 ≤ X1 := by positivity
  have hX2 : 0 ≤ X2 := by positivity
  have hX3 : 0 ≤ X3 := by positivity
  have hX4 : 0 ≤ X4 := by positivity
  have hX5 : 0 ≤ X5 := by positivity
  have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith
  have b1 : ‖psi0L χ N - (∑ ρ ∈ Z1, iv ρ - ∑ ρ ∈ ZT, k ρ)‖ ≤ A₁ * (X1 + X2 + X3) := by
    refine e₁.trans ?_
    gcongr
  have b2 : 2 * c1 ≤ 4 * A₆ * X3 := by nlinarith
  have b3 : c1 * ((N : ℝ) ^ (1 / 2 : ℝ) * Real.log N) ≤ 2 * A₆ * X4 := by
    have h0 : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N := by positivity
    calc c1 * ((N : ℝ) ^ (1 / 2 : ℝ) * Real.log N) ≤ 2 * A₆ * ℓ * ((N : ℝ) ^ (1 / 2 : ℝ) *
          Real.log N) := by gcongr
      _ = 2 * A₆ * X4 := by simp only [X4]; ring
  have b4 : c1 * (16200 * Real.log q) ≤ 32400 * A₆ * X3 := by
    calc c1 * (16200 * Real.log q) ≤ 2 * A₆ * ℓ * (16200 * ℓ) := by gcongr
      _ = 32400 * A₆ * X3 := by simp only [X3]; ring
  have b5 : N * E * (c1 * (16200 * Real.log q) + C₇ * (Real.log q + Real.log T) * Real.log T) ≤
      (32400 * A₆ + C₇) * X5 := by
    have h1 : c1 * (16200 * Real.log q) + C₇ * (Real.log q + Real.log T) * Real.log T ≤
        (32400 * A₆ + C₇) * ℓ ^ 2 := by
      have : C₇ * ((Real.log q + Real.log T) * Real.log T) ≤ C₇ * ℓ ^ 2 := by gcongr
      nlinarith
    calc (N : ℝ) * E * (c1 * (16200 * Real.log q) + C₇ * (Real.log q + Real.log T) * Real.log T)
        ≤ N * E * ((32400 * A₆ + C₇) * ℓ ^ 2) := by gcongr
      _ = (32400 * A₆ + C₇) * X5 := by simp only [X5]; ring
  have htri : ‖psi0L χ N - (∑ ρ ∈ Z1, iv ρ - ∑ ρ ∈ ZT, k ρ) + ∑ ρ ∈ Z1.filter P, iv ρ +
        ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), (iv ρ - k ρ) +
        ∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), iv ρ -
        ∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), k ρ‖
      ≤ ‖psi0L χ N - (∑ ρ ∈ Z1, iv ρ - ∑ ρ ∈ ZT, k ρ)‖ + ‖∑ ρ ∈ Z1.filter P, iv ρ‖ +
        ‖∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ M ρ), (iv ρ - k ρ)‖ +
        ‖∑ ρ ∈ Z1.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), iv ρ‖ +
        ‖∑ ρ ∈ ZT.filter (fun ρ ↦ ¬ P ρ ∧ ¬ M ρ), k ρ‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  refine htri.trans ?_
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add b1 (B1.trans b2)) (B2.trans b3))
    (B3.trans b4)) (B4.trans b5)
  refine hsum.trans ?_
  have e : (A₁ + 70000 * A₆ + C₇ + 1) * (X1 + X2 + X3 + X4 + X5) =
      A₁ * (X1 + X2 + X3) + (70000 * A₆ + C₇ + 1) * (X1 + X2 + X3) +
        (A₁ + 70000 * A₆ + C₇ + 1) * X4 + (A₁ + 70000 * A₆ + C₇ + 1) * X5 := by ring
  rw [e]
  have f1 : 0 ≤ (70000 * A₆ + C₇ + 1) * (X1 + X2) := by positivity
  have f2 : 4 * A₆ * X3 + 32400 * A₆ * X3 ≤ (70000 * A₆ + C₇ + 1) * X3 := by nlinarith
  have f3 : 2 * A₆ * X4 ≤ (A₁ + 70000 * A₆ + C₇ + 1) * X4 := by nlinarith
  have f4 : (32400 * A₆ + C₇) * X5 ≤ (A₁ + 70000 * A₆ + C₇ + 1) * X5 := by nlinarith
  nlinarith

end NTKB
