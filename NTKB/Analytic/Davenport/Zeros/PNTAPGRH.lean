/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.PNTAP
import NTKB.Analytic.Davenport.Zeros.PNTConditional

/-!
# Primes in progressions under the generalized Riemann hypothesis

**Davenport, Ch. 20, pp. 124-125 (rows 20-11 to 20-14).** Under the generalized Riemann hypothesis
(all zeros of all `L(s, χ)` in the critical strip lie on `σ = 1/2`):
`ψ(x, χ) ≪ x^{1/2} log²(qx)` for nonprincipal `χ` mod `q ≤ x`, and
`ψ(x; q, a) = x/φ(q) + O(x^{1/2} log² x)` for `q ≤ x`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ArithmeticFunction.vonMangoldt

namespace NTKB

/-- **Davenport, Ch. 20, p. 124 (row 20-11)**: the generalized Riemann hypothesis: every zero of
every `L(s, χ)` (including `ζ(s) = L(s, χ₀)` for `q = 1`) in the critical strip `0 < σ < 1` has
real part `1/2`. -/
def GeneralizedRiemannHypothesis : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), LFunction χ s = 0 → 0 < s.re →
    s.re < 1 → s.re = 1 / 2

/-- The generalized Riemann hypothesis contains the Riemann hypothesis. -/
lemma GeneralizedRiemannHypothesis.riemannHypothesis (h : GeneralizedRiemannHypothesis) :
    RiemannHypothesis := by
  intro s hs htriv hs1
  rcases riemannZeta_eq_zero_cases hs hs1 with ⟨m, hm⟩ | ⟨ρ, hρ⟩
  · exact absurd ⟨m, by rw [hm]; push_cast; ring⟩ htriv
  · have hρ' := riemannXi_zero_mem ρ
    rw [hρ] at hρ'
    have := h 1 (1 : DirichletCharacter ℂ 1) s (by rw [LFunction_modOne_eq]; exact hs)
      hρ'.2.1 hρ'.2.2
    exact this

set_option maxHeartbeats 2000000 in
/-- **Davenport, Ch. 20, p. 125 (row 20-13)**, primitive characters: under the generalized Riemann
hypothesis, `|ψ₀(N, χ)| ≤ A N^{1/2} log²(qN)` for primitive `χ` mod `q > 1` and integers `N ≥ 4`. -/
@[kb "davenport1980" "Ch 20, p. 125"]
theorem Davenport.norm_psi0L_le_of_GRH (hGRH : GeneralizedRiemannHypothesis) :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ N : ℕ, 4 ≤ N →
      ‖psi0L χ N‖ ≤ A * (N : ℝ) ^ (1 / 2 : ℝ) * Real.log (q * N) ^ 2 := by
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.explicit_formula_psi0L'
  obtain ⟨A₆, hA₆, h₆⟩ := card_zerosBelowL_one_le
  obtain ⟨C₇, hC₇, h₇⟩ := Davenport.sum_L_zeros_inv_norm_le
  refine ⟨10 * A₁ + 10 * A₆ + C₇ + 1, by positivity, ?_⟩
  intro q _ χ hχ hq N hN
  have hχ1 := ne_one_of_isPrimitive hχ hq
  have hq2 := two_le_of_ne_one hχ1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  set T := (N : ℝ) ^ (1 / 2 : ℝ) with hTdef
  have hT2 : 2 ≤ T := by
    have : T = √(N : ℝ) := by rw [hTdef, Real.sqrt_eq_rpow]
    rw [this, Real.le_sqrt (by norm_num) (by positivity)]; linarith
  have hT0 : 0 < T := by linarith
  have hTT : T * T = N := by
    rw [hTdef, ← Real.rpow_add hN0]; norm_num
  have hlogT : Real.log T = Real.log N / 2 := by
    rw [hTdef, Real.log_rpow hN0]; ring
  have hlq : 0 < Real.log q := Real.log_pos (by linarith)
  have hlN : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hN0]; have := Real.exp_one_lt_d9; linarith
  set Λ' := Real.log (q * N) with hΛ'
  have hΛ'eq : Λ' = Real.log q + Real.log N := by
    rw [hΛ', Real.log_mul (by positivity) (by positivity)]
  have hΛ'1 : 1 ≤ Λ' := by linarith
  have e₁ := h₁ hχ hq N (by omega) T hT2
  set ℓ := Real.log q + Real.log N + Real.log T with hℓ
  have hℓΛ : ℓ ≤ 2 * Λ' := by rw [hℓ, hlogT, hΛ'eq]; linarith
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ, hlogT]; linarith
  -- zeros on the critical line
  have hre : ∀ ρ : ZeroIndex (dirichletXi χ), ρ.val.re = 1 / 2 := fun ρ ↦
    hGRH q χ ρ.val (dirichletXi_zero_mem hχ hq ρ).1 (dirichletXi_zero_mem hχ hq ρ).2.1
      (dirichletXi_zero_mem hχ hq ρ).2.2
  -- `∑_{|γ|<1} 1/ρ`
  have hc1 := h₆ hχ hq
  have hS1 : ‖∑ ρ ∈ zerosBelowL hχ hq 1, 1 / ρ.val‖ ≤ 2 * A₆ * (Real.log q + 1) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ρ ∈ zerosBelowL hχ hq 1, ‖1 / ρ.val‖ ≤ ∑ ρ ∈ zerosBelowL hχ hq 1, (2 : ℝ) := by
          refine Finset.sum_le_sum fun ρ _ ↦ ?_
          have : 1 / 2 ≤ ‖ρ.val‖ := (hre ρ).symm.le.trans (Complex.re_le_norm _)
          rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
      _ = 2 * (zerosBelowL hχ hq 1).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * (A₆ * (Real.log q + 1)) := by gcongr
      _ = 2 * A₆ * (Real.log q + 1) := by ring
  -- `∑_{|γ|<T} N^ρ/ρ`
  set u : ZeroIndex (dirichletXi χ) → ℝ := fun ρ ↦ if |ρ.val.im| < 1 then 2 else 0
  set w : ZeroIndex (dirichletXi χ) → ℝ := fun ρ ↦ if 1 ≤ |ρ.val.im| then 1 / ‖ρ.val‖ else 0
  have hsumu : ∑ ρ ∈ zerosBelowL hχ hq T, u ρ ≤ 2 * A₆ * (Real.log q + 1) := by
    simp only [u]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have : (zerosBelowL hχ hq T).filter (fun ρ ↦ |ρ.val.im| < 1) = zerosBelowL hχ hq 1 := by
      ext ρ; simp only [Finset.mem_filter, mem_zerosBelowL]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.trans_le (by linarith), h⟩⟩
    rw [this]; nlinarith
  have hsumw := h₇ hχ hq T hT2
  have hST : ‖∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val‖ ≤
      (N : ℝ) ^ (1 / 2 : ℝ) * (2 * A₆ * (Real.log q + 1) +
        C₇ * (Real.log q + Real.log T) * Real.log T) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ρ ∈ zerosBelowL hχ hq T, ‖perronKernel N ρ.val‖
        ≤ ∑ ρ ∈ zerosBelowL hχ hq T, (N : ℝ) ^ (1 / 2 : ℝ) * (u ρ + w ρ) := by
          refine Finset.sum_le_sum fun ρ _ ↦ ?_
          rw [norm_perronKernel hN0, hre ρ, div_eq_mul_one_div]
          have hn : 1 / 2 ≤ ‖ρ.val‖ := (hre ρ).symm.le.trans (Complex.re_le_norm _)
          gcongr
          simp only [u, w]
          by_cases h1 : |ρ.val.im| < 1
          · rw [if_pos h1, if_neg (not_le.mpr h1), add_zero, div_le_iff₀ (by linarith)]; linarith
          · rw [if_neg h1, if_pos (not_lt.mp h1), zero_add]
      _ = (N : ℝ) ^ (1 / 2 : ℝ) * (∑ ρ ∈ zerosBelowL hχ hq T, u ρ +
            ∑ ρ ∈ zerosBelowL hχ hq T, w ρ) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ _ := by gcongr
  -- assemble
  have hsplit : psi0L χ N = (psi0L χ N - (∑ ρ ∈ zerosBelowL hχ hq 1, 1 / ρ.val -
      ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val)) +
      ∑ ρ ∈ zerosBelowL hχ hq 1, 1 / ρ.val - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val := by
    ring
  rw [hsplit]
  have hsq : (N : ℝ) ^ (1 / 2 : ℝ) = T := rfl
  have hNT : (N : ℝ) / T = T := by rw [← hTT]; field_simp
  have hTN : T * (N : ℝ) ^ (-1 / 2 : ℝ) = 1 := by
    rw [hTdef, ← Real.rpow_add hN0]; norm_num
  have hR : A₁ * ((N : ℝ) * ℓ ^ 2 / T + T * ℓ * (N : ℝ) ^ (-1 / 2 : ℝ) + ℓ) ≤
      A₁ * (4 * T * Λ' ^ 2 + 4 * Λ') := by
    have e1 : (N : ℝ) * ℓ ^ 2 / T = T * ℓ ^ 2 := by rw [mul_div_right_comm, hNT]
    have e2 : T * ℓ * (N : ℝ) ^ (-1 / 2 : ℝ) = ℓ := by
      rw [mul_comm T ℓ, mul_assoc, hTN, mul_one]
    rw [e1, e2]
    have h1 : ℓ ^ 2 ≤ 4 * Λ' ^ 2 := by nlinarith
    have h2 : ℓ ≤ 2 * Λ' := hℓΛ
    have h3 : T * ℓ ^ 2 ≤ 4 * T * Λ' ^ 2 := by nlinarith
    have h4 : T * ℓ ^ 2 + ℓ + ℓ ≤ 4 * T * Λ' ^ 2 + 4 * Λ' := by linarith
    exact mul_le_mul_of_nonneg_left h4 hA₁.le
  have hlog1 : Real.log q + 1 ≤ 2 * Λ' := by rw [hΛ'eq]; linarith
  have hlogT2 : (Real.log q + Real.log T) * Real.log T ≤ Λ' ^ 2 := by
    rw [hlogT, hΛ'eq]
    have : Real.log N / 2 ≤ Real.log q + Real.log N := by linarith
    nlinarith
  calc ‖psi0L χ N - (∑ ρ ∈ zerosBelowL hχ hq 1, 1 / ρ.val -
        ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val) +
        ∑ ρ ∈ zerosBelowL hχ hq 1, 1 / ρ.val - ∑ ρ ∈ zerosBelowL hχ hq T, perronKernel N ρ.val‖
      ≤ A₁ * ((N : ℝ) * ℓ ^ 2 / T + T * ℓ * (N : ℝ) ^ (-1 / 2 : ℝ) + ℓ) +
          2 * A₆ * (Real.log q + 1) +
          T * (2 * A₆ * (Real.log q + 1) + C₇ * (Real.log q + Real.log T) * Real.log T) := by
        rw [← hsq]
        exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add e₁ hS1)) hST)
    _ ≤ A₁ * (4 * T * Λ' ^ 2 + 4 * Λ') + 2 * A₆ * (2 * Λ') +
          T * (2 * A₆ * (2 * Λ') + C₇ * Λ' ^ 2) := by
        have h1 : 2 * A₆ * (Real.log q + 1) ≤ 2 * A₆ * (2 * Λ') := by gcongr
        have h2 : C₇ * (Real.log q + Real.log T) * Real.log T ≤ C₇ * Λ' ^ 2 := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hlogT2 hC₇.le
        have h3 : T * (2 * A₆ * (Real.log q + 1) + C₇ * (Real.log q + Real.log T) * Real.log T) ≤
            T * (2 * A₆ * (2 * Λ') + C₇ * Λ' ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hT0.le
        linarith
    _ ≤ (10 * A₁ + 10 * A₆ + C₇ + 1) * T * Λ' ^ 2 := by
        have h1 : Λ' ≤ Λ' ^ 2 := by nlinarith
        have h2 : Λ' ^ 2 ≤ T * Λ' ^ 2 := by nlinarith
        have h3 : 0 ≤ Λ' := by linarith
        have h4 : Λ' ≤ T * Λ' ^ 2 := by linarith
        have h5 : T * Λ' ≤ T * Λ' ^ 2 := mul_le_mul_of_nonneg_left h1 hT0.le
        have h6 : 0 ≤ T * Λ' ^ 2 := by positivity
        have e : (10 * A₁ + 10 * A₆ + C₇ + 1) * T * Λ' ^ 2 =
            10 * A₁ * (T * Λ' ^ 2) + 10 * A₆ * (T * Λ' ^ 2) + C₇ * (T * Λ' ^ 2) + T * Λ' ^ 2 := by
          ring
        rw [e]
        have f1 : A₁ * Λ' ≤ A₁ * (T * Λ' ^ 2) := mul_le_mul_of_nonneg_left h4 hA₁.le
        have f2 : A₆ * Λ' ≤ A₆ * (T * Λ' ^ 2) := mul_le_mul_of_nonneg_left h4 hA₆.le
        have f3 : A₆ * (T * Λ') ≤ A₆ * (T * Λ' ^ 2) := mul_le_mul_of_nonneg_left h5 hA₆.le
        nlinarith

open scoped Classical in
set_option maxHeartbeats 4000000 in
/-- **Davenport, Ch. 20, p. 125, (14) (rows 20-12, 20-14)**: under the generalized Riemann
hypothesis, `|ψ(N; q, a) - N/φ(q)| ≤ A N^{1/2} log² N` for `a` prime to `q`, `q ≤ N`, `N ≥ 4`. -/
@[kb "davenport1980" "Ch 20, p. 125"]
theorem Davenport.psiAP_sub_le_of_GRH (hGRH : GeneralizedRiemannHypothesis) :
    ∃ A : ℝ, 0 < A ∧ ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a → ∀ N : ℕ, 4 ≤ N → q ≤ N →
      ‖(psiAP a N : ℂ) - N / q.totient‖ ≤ A * (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N ^ 2 := by
  obtain ⟨C₁, hC₁, h₁⟩ := Davenport.psi_sub_self_le_of_riemannHypothesis hGRH.riemannHypothesis
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.norm_psi0L_le_of_GRH hGRH
  have hl2 := log_two_gt_two_thirds
  refine ⟨C₁ + 4 * A₂ + 6, by positivity, ?_⟩
  intro q _ a ha N hN hqN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  set L := Real.log N with hL
  have hL1 : 1 < L := by
    rw [hL, Real.lt_log_iff_exp_lt hN0]; have := Real.exp_one_lt_d9; linarith
  have hqN' : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlq : Real.log q ≤ L := Real.log_le_log hq0 hqN'
  have hlq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  set S := (N : ℝ) ^ (1 / 2 : ℝ) with hS
  have hS1 : 1 ≤ S := Real.one_le_rpow hN1 (by norm_num)
  set W := S * L ^ 2 with hW
  have hLW : L ≤ W := by
    have : L ≤ L ^ 2 := by nlinarith
    calc L ≤ L ^ 2 := this
      _ = 1 * L ^ 2 := by ring
      _ ≤ S * L ^ 2 := by gcongr
  have hLq : L / Real.log 2 * Real.log q ≤ 1.5 * W := by
    have h1 : L / Real.log 2 ≤ 1.5 * L := by rw [div_le_iff₀ (by linarith)]; nlinarith
    calc L / Real.log 2 * Real.log q ≤ 1.5 * L * L := by gcongr
      _ = 1.5 * L ^ 2 := by ring
      _ ≤ 1.5 * W := by
          have : L ^ 2 ≤ W := by
            calc L ^ 2 = 1 * L ^ 2 := by ring
              _ ≤ S * L ^ 2 := by gcongr
          linarith
  set B := (C₁ + 4 * A₂ + 6) * W with hB
  -- the principal character
  have hprin : ‖psiL (1 : DirichletCharacter ℂ q) N - N‖ ≤ B := by
    have h1 := Davenport.norm_psiL_one_sub_psi_le (q := q) hN1
    have h2 := h₁ N hN2
    have h4 : ‖(Chebyshev.psi N : ℂ) - N‖ ≤ C₁ * W := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      refine h2.trans (le_of_eq ?_)
      simp only [W, S, L]; ring
    have hsplit : psiL (1 : DirichletCharacter ℂ q) N - N =
        (psiL (1 : DirichletCharacter ℂ q) N - Chebyshev.psi N) + ((Chebyshev.psi N : ℂ) - N) := by
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [← hL] at h1
    have hW0 : 0 ≤ W := by positivity
    simp only [B]; nlinarith
  -- the nonprincipal characters
  have hnon : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖psiL χ N‖ ≤ B := by
    intro χ hχ
    have hcond : χ.conductor ≠ 1 := fun h ↦ hχ (eq_one_iff_conductor_eq_one.mpr h)
    haveI : NeZero χ.conductor := ⟨conductor_ne_zero χ⟩
    have hprim := primitiveCharacter_isPrimitive χ
    have hcq : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    have h1 := Davenport.norm_psiL_sub_primitive_le χ hN1
    have h2 := h₂ hprim hcond N hN
    have h3 := psiL_natCast_eq χ.primitiveCharacter N
    have hsplit : psiL χ N = (psiL χ N - psiL χ.primitiveCharacter N) +
        χ.primitiveCharacter N * Λ N / 2 + psi0L χ.primitiveCharacter N := by
      rw [h3]; ring
    rw [hsplit]
    have hΛ : ‖χ.primitiveCharacter N * Λ N / 2‖ ≤ L := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_two]
      have := DirichletCharacter.norm_le_one χ.primitiveCharacter N
      have h5 : Λ N ≤ L := ArithmeticFunction.vonMangoldt_le_log
      have h6 := ArithmeticFunction.vonMangoldt_nonneg (n := N)
      have : ‖χ.primitiveCharacter N‖ * Λ N ≤ L := by
        nlinarith [norm_nonneg (χ.primitiveCharacter N)]
      linarith
    have hlog : Real.log (χ.conductor * N) ≤ 2 * L := by
      have hc0 : (χ.conductor : ℝ) ≠ 0 := by exact_mod_cast conductor_ne_zero χ
      rw [Real.log_mul hc0 hN0.ne', ← hL]
      have : Real.log χ.conductor ≤ Real.log q :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (conductor_ne_zero χ)) hcq
      linarith
    have hlog0 : 0 ≤ Real.log (χ.conductor * N) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero (conductor_ne_zero χ)
      nlinarith)
    have h7 : A₂ * S * Real.log (χ.conductor * N) ^ 2 ≤ 4 * A₂ * W := by
      have : Real.log (χ.conductor * N) ^ 2 ≤ (2 * L) ^ 2 := by gcongr
      calc A₂ * S * Real.log (χ.conductor * N) ^ 2 ≤ A₂ * S * (2 * L) ^ 2 := by gcongr
        _ = 4 * A₂ * W := by simp only [W]; ring
    calc ‖(psiL χ N - psiL χ.primitiveCharacter N) + χ.primitiveCharacter N * Λ N / 2 +
          psi0L χ.primitiveCharacter N‖
        ≤ ‖psiL χ N - psiL χ.primitiveCharacter N‖ + ‖χ.primitiveCharacter N * Λ N / 2‖ +
          ‖psi0L χ.primitiveCharacter N‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ L / Real.log 2 * Real.log q + L + 4 * A₂ * W := by
          rw [← hL] at h1
          have := h2.trans h7
          linarith
      _ ≤ B := by
          have hW0 : 0 ≤ W := by positivity
          simp only [B]; nlinarith
  -- orthogonality
  set D : DirichletCharacter ℂ q → ℂ := fun χ ↦ psiL χ N - (if χ = 1 then (N : ℂ) else 0) with hD
  have hD : ∀ χ, ‖D χ‖ ≤ B := by
    intro χ
    by_cases h : χ = 1
    · simp only [D, h, if_true]; exact hprin
    · simp only [D, h, if_false, sub_zero]; exact hnon χ h
  have hsum1 : ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (if χ = 1 then (N : ℂ) else 0) = N := by
    rw [Finset.sum_eq_single 1 (fun χ _ hχ ↦ by simp [hχ]) (by simp)]
    have hinv : IsUnit a⁻¹ := by
      rw [← ha.unit_spec, ZMod.inv_coe_unit]; exact Units.isUnit _
    simp [MulChar.one_apply hinv]
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hid : (psiAP a N : ℂ) - N / q.totient =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * D χ := by
    rw [Davenport.psiAP_eq ha]
    simp only [D, mul_sub, Finset.sum_sub_distrib, hsum1]
    have : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ
    field_simp
  rw [hid]
  have hbound : ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * D χ‖ ≤ q.totient * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ χ : DirichletCharacter ℂ q, ‖χ a⁻¹ * D χ‖ ≤ ∑ χ : DirichletCharacter ℂ q, B := by
          refine Finset.sum_le_sum fun χ _ ↦ ?_
          rw [norm_mul]
          have := DirichletCharacter.norm_le_one χ a⁻¹
          calc ‖χ a⁻¹‖ * ‖D χ‖ ≤ 1 * B := mul_le_mul this (hD χ) (norm_nonneg _) zero_le_one
            _ = B := one_mul B
      _ = q.totient * B := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hφpos : (0 : ℝ) < q.totient := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hφ)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (q.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * D χ‖
      ≤ (q.totient : ℝ)⁻¹ * (q.totient * B) := by gcongr
    _ = B := by field_simp
    _ = (C₁ + 4 * A₂ + 6) * (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N ^ 2 := by
        simp only [B, W, S, L]; ring

end NTKB
