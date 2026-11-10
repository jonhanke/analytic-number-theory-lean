/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LExceptionalMain
import NTKB.Analytic.Davenport.Zeros.PNT

/-!
# `ψ(x, χ) = -x^{β₁}/β₁ + O(x exp(-c √log x))`

**Davenport, Ch. 20, p. 123, (8) (row 20-4)**, for primitive `χ` mod `q > 1` and integers
`N ≥ 3`: if `log q ≤ C √log N` then `ψ₀(N, χ) = -∑_{exceptional ρ} N^ρ/ρ + O(N exp(-c √log N))`,
with `c > 0` depending only on `C`. (Take `T = exp(√log N)` in 19-14.)
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real ComplexConjugate

namespace NTKB

open scoped Classical in
/-- The exceptional zeros are real, so the exceptional part of the sum over `|γ| < T` does not
depend on `T ≥ 1`. -/
lemma filter_exc_zerosBelowL_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    (zerosBelowL hχ hq T).filter (fun ρ ↦ IsExcPoint q ρ.val) =
      (zerosBelowL hχ hq 1).filter (fun ρ ↦ IsExcPoint q ρ.val) := by
  have hχ1 := ne_one_of_isPrimitive hχ hq
  ext ρ
  simp only [Finset.mem_filter, mem_zerosBelowL]
  constructor
  · rintro ⟨-, h⟩
    have := (Davenport.exceptional_zero_real hχ1 (dirichletXi_zero_mem hχ hq ρ).1 h).2
    exact ⟨by rw [this]; simp, h⟩
  · rintro ⟨h1, h⟩; exact ⟨h1.trans_le hT, h⟩

open scoped Classical in
set_option maxHeartbeats 4000000 in
/-- **Davenport, Ch. 20, p. 123, (8) (row 20-4)**, primitive characters: for every `C > 0` there
are `c, A > 0` such that for primitive `χ` mod `q > 1` and integers `N ≥ 3` with
`log q ≤ C √log N`,
`|ψ₀(N, χ) + ∑_{exceptional ρ} N^ρ/ρ| ≤ A N exp(-c √log N)`. -/
@[kb "davenport1980" "Ch 20, p. 123"]
theorem Davenport.psi0L_sub_exceptional_le (C : ℝ) (hC : 0 < C) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
      (hχ : χ.IsPrimitive) (hq : q ≠ 1), ∀ N : ℕ, 3 ≤ N →
      Real.log q ≤ C * √(Real.log N) →
      ‖psi0L χ N + ∑ ρ ∈ (zerosBelowL hχ hq 1).filter (fun ρ ↦ IsExcPoint q ρ.val),
          perronKernel N ρ.val‖ ≤ A * N * Real.exp (-(c * √(Real.log N))) := by
  obtain ⟨A₀, hA₀, h₀⟩ := Davenport.psi0L_exceptional
  set c' := min 1 (1 / 16200 / (C + 1)) with hc'
  have hc'0 : 0 < c' := lt_min one_pos (by positivity)
  have hc'1 : c' ≤ 1 := min_le_left _ _
  have hc'2 : c' ≤ 1 / 16200 / (C + 1) := min_le_right _ _
  set K := 24 * (2 / c') ^ 4 with hKdef
  have hK : 0 < K := by positivity
  have hp4 : ∀ v : ℝ, 0 ≤ v → v ^ 4 ≤ K * Real.exp (c' * v / 2) := fun v hv ↦ by
    rw [hKdef]; exact pow_four_le_exp hc'0 hv
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    have h2 : 1 ≤ 2 / c' := by rw [le_div_iff₀ hc'0]; linarith
    have := one_le_pow₀ (n := 4) h2
    nlinarith
  clear_value c' K
  refine ⟨c' / 2, A₀ * (C + 3) ^ 2 * 8 * K + 1, by positivity, by positivity, ?_⟩
  intro q _ χ hχ hq N hN hqN
  have hχ1 := ne_one_of_isPrimitive hχ hq
  have hq2 := two_le_of_ne_one hχ1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set L := Real.log N with hL
  have hL1 : 1 < L := by
    rw [hL, Real.lt_log_iff_exp_lt hN0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set u := √L with hu
  have hu2 : u ^ 2 = L := Real.sq_sqrt (by linarith)
  have hu1 : 1 < u := by rw [hu, Real.lt_sqrt zero_le_one]; linarith
  have hu0 : 0 < u := by linarith
  set T := Real.exp u with hT
  have hT2 : 2 ≤ T := by
    have := Real.add_one_le_exp u; rw [← hT] at this; linarith
  have hlogT : Real.log T = u := Real.log_exp u
  have hNe : (N : ℝ) = Real.exp L := (Real.exp_log hN0).symm
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  clear_value T u L
  have e := h₀ hχ hq N hN T hT2
  rw [filter_exc_zerosBelowL_eq hχ hq (by linarith)] at e
  refine e.trans ?_
  -- the sizes
  set ℓ := Real.log q + Real.log N + Real.log T with hℓ
  have hℓu : ℓ ≤ (C + 2) * u ^ 2 := by
    rw [hℓ, ← hL, hlogT, ← hu2]
    have : u ≤ u ^ 2 := by nlinarith
    nlinarith
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; linarith
  set E := Real.exp (-(c' / 2 * u)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- `N E ≥ 1`, `u^4 e^{-c' u} ≤ K E`
  have hNE : 1 ≤ (N : ℝ) * E := by
    rw [hNe, hE, ← Real.exp_add]; apply Real.one_le_exp
    have : c' / 2 * u ≤ u := by nlinarith
    nlinarith
  have hc'h : c' ≤ 1 / 2 := by
    have : 1 / 16200 / (C + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hu4 : u ^ 4 * Real.exp (-(c' * u)) ≤ K * E := by
    have h0 := hp4 u hu0.le
    have e1 : Real.exp (-(c' * u)) = E * E := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (c' * u / 2) * E = 1 := by
      rw [hE, ← Real.exp_add]; simp only [Real.exp_eq_one_iff]; ring
    rw [e1]
    have hEE : 0 ≤ E * E := by positivity
    calc u ^ 4 * (E * E) ≤ K * Real.exp (c' * u / 2) * (E * E) :=
          mul_le_mul_of_nonneg_right h0 hEE
      _ = K * E * (Real.exp (c' * u / 2) * E) := by ring
      _ = K * E := by rw [e2, mul_one]
  -- each of the five terms is `≤ (C + 3)² K N E`
  have hW : (C + 2) ^ 2 * u ^ 4 ≤ (C + 3) ^ 2 * u ^ 4 := by gcongr; linarith
  have hℓ2 : ℓ ^ 2 ≤ (C + 2) ^ 2 * u ^ 4 := by
    calc ℓ ^ 2 ≤ ((C + 2) * u ^ 2) ^ 2 := by gcongr
      _ = (C + 2) ^ 2 * u ^ 4 := by ring
  -- term 1: `N ℓ²/T ≤ (C+2)² N u⁴ e^{-u} ≤ (C+2)² K N E`
  have t1 : (N : ℝ) * ℓ ^ 2 / T ≤ (C + 3) ^ 2 * K * (N * E) := by
    have h1 : 1 / T = Real.exp (-u) := by rw [hT, Real.exp_neg, one_div]
    have h2 : Real.exp (-u) ≤ Real.exp (-(c' * u)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    calc (N : ℝ) * ℓ ^ 2 / T = N * ℓ ^ 2 * (1 / T) := by ring
      _ ≤ N * ((C + 3) ^ 2 * u ^ 4) * Real.exp (-(c' * u)) := by
          rw [h1]; gcongr; linarith
      _ = (C + 3) ^ 2 * N * (u ^ 4 * Real.exp (-(c' * u))) := by ring
      _ ≤ (C + 3) ^ 2 * N * (K * E) := by gcongr
      _ = (C + 3) ^ 2 * K * (N * E) := by ring
  -- term 3: `ℓ² ≤ (C+2)² u⁴ ≤ (C+2)² K e^{c'u/2} ≤ ... N E`
  have t3 : ℓ ^ 2 ≤ (C + 3) ^ 2 * K * (N * E) := by
    have h1 : u ^ 4 ≤ K * Real.exp (c' * u / 2) := hp4 u hu0.le
    have h2 : Real.exp (c' * u / 2) ≤ N * E := by
      rw [hNe, hE, ← Real.exp_add]; apply Real.exp_le_exp.mpr
      rw [← hu2]; nlinarith
    calc ℓ ^ 2 ≤ (C + 3) ^ 2 * u ^ 4 := hℓ2.trans hW
      _ ≤ (C + 3) ^ 2 * (K * Real.exp (c' * u / 2)) := by gcongr
      _ ≤ (C + 3) ^ 2 * (K * (N * E)) := by gcongr
      _ = (C + 3) ^ 2 * K * (N * E) := by ring
  -- term 2: `T N^{-1/2} = e^{u - u²/2} ≤ 2`, so `T ℓ N^{-1/2} ≤ 2 ℓ²`
  have t2 : T * ℓ * (N : ℝ) ^ (-1 / 2 : ℝ) ≤ 4 * ((C + 3) ^ 2 * K * (N * E)) := by
    have hNr : (N : ℝ) ^ (-1 / 2 : ℝ) = Real.exp (-(L / 2)) := by
      rw [Real.rpow_def_of_pos hN0, ← hL]; congr 1; ring
    have h1 : T * (N : ℝ) ^ (-1 / 2 : ℝ) ≤ 2 := by
      rw [hNr, hT, ← Real.exp_add]
      have h3 : u + -(L / 2) ≤ 1 / 2 := by rw [← hu2]; nlinarith [sq_nonneg (u - 1)]
      have h4 : Real.exp (1 / 2) ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h5 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
      exact (Real.exp_le_exp.mpr h3).trans h4
    have h2 : ℓ ≤ ℓ ^ 2 + 1 := by nlinarith
    have hTN : 0 ≤ T * (N : ℝ) ^ (-1 / 2 : ℝ) := by positivity
    have h6 : 1 ≤ (C + 3) ^ 2 * K * (N * E) := by
      have h9 : 1 ≤ (C + 3) ^ 2 := by nlinarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ (C + 3) ^ 2 * K * (N * E) := by gcongr
    calc T * ℓ * (N : ℝ) ^ (-1 / 2 : ℝ) = ℓ * (T * (N : ℝ) ^ (-1 / 2 : ℝ)) := by ring
      _ ≤ ℓ * 2 := mul_le_mul_of_nonneg_left h1 hℓ0
      _ ≤ 2 * (ℓ ^ 2 + 1) := by linarith
      _ ≤ 2 * ((C + 3) ^ 2 * K * (N * E) + (C + 3) ^ 2 * K * (N * E)) := by
          have := add_le_add t3 h6; linarith
      _ = 4 * ((C + 3) ^ 2 * K * (N * E)) := by ring
  -- term 4: `ℓ N^{1/2} log N ≤ (C+2) u⁴ e^{u²/2}`
  have t4 : ℓ * (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N ≤ (C + 3) ^ 2 * K * (N * E) := by
    have hNr : (N : ℝ) ^ (1 / 2 : ℝ) = Real.exp (L / 2) := by
      rw [Real.rpow_def_of_pos hN0, ← hL]; congr 1; ring
    have h1 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) * Real.exp (-(c' * u)) := by
      rw [hNr, hNe, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h3 : c' * u ≤ u / 2 := by nlinarith
      rw [← hu2]; nlinarith
    have h2 : ℓ * Real.log N ≤ (C + 3) ^ 2 * u ^ 4 := by
      rw [← hL, ← hu2]
      have : ℓ ≤ (C + 2) * u ^ 2 := hℓu
      have hu20 : 0 ≤ u ^ 2 := by positivity
      calc ℓ * u ^ 2 ≤ (C + 2) * u ^ 2 * u ^ 2 := by gcongr
        _ ≤ (C + 3) ^ 2 * u ^ 4 := by nlinarith
    calc ℓ * (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N = (ℓ * Real.log N) * (N : ℝ) ^ (1 / 2 : ℝ) := by
          ring
      _ ≤ ((C + 3) ^ 2 * u ^ 4) * ((N : ℝ) * Real.exp (-(c' * u))) := by
          have : 0 ≤ ℓ * Real.log N := mul_nonneg hℓ0 (by rw [← hL]; linarith)
          gcongr
      _ = (C + 3) ^ 2 * N * (u ^ 4 * Real.exp (-(c' * u))) := by ring
      _ ≤ (C + 3) ^ 2 * N * (K * E) := by gcongr
      _ = (C + 3) ^ 2 * K * (N * E) := by ring
  -- term 5: `N ℓ² exp(-c log N / log(qT)) ≤ (C+2)² N u⁴ e^{-c' u}`
  have t5 : (N : ℝ) * ℓ ^ 2 * Real.exp (-(1 / 16200 * Real.log N / logQT q T)) ≤
      (C + 3) ^ 2 * K * (N * E) := by
    have hqT : logQT q T = Real.log q + u := by
      rw [logQT_eq (by linarith), max_eq_right (by rw [abs_of_pos (by linarith)]; linarith),
        abs_of_pos (by linarith), hlogT]
    have hqT0 : 0 < logQT q T := by rw [hqT]; linarith
    have hqTu : logQT q T ≤ (C + 1) * u := by
      rw [hqT]
      have : Real.log q ≤ C * u := hqN
      linarith
    have h1 : Real.exp (-(1 / 16200 * Real.log N / logQT q T)) ≤ Real.exp (-(c' * u)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, le_div_iff₀ hqT0, ← hL, ← hu2]
      have h2 : c' * (C + 1) ≤ 1 / 16200 := by
        have := mul_le_mul_of_nonneg_right hc'2 (by linarith : (0 : ℝ) ≤ C + 1)
        rwa [div_mul_cancel₀ _ (by linarith)] at this
      calc c' * u * logQT q T ≤ c' * u * ((C + 1) * u) := by gcongr
        _ = c' * (C + 1) * u ^ 2 := by ring
        _ ≤ 1 / 16200 * u ^ 2 := by gcongr
    calc (N : ℝ) * ℓ ^ 2 * Real.exp (-(1 / 16200 * Real.log N / logQT q T))
        ≤ N * ((C + 3) ^ 2 * u ^ 4) * Real.exp (-(c' * u)) := by
          gcongr; exact hℓ2.trans hW
      _ = (C + 3) ^ 2 * N * (u ^ 4 * Real.exp (-(c' * u))) := by ring
      _ ≤ (C + 3) ^ 2 * N * (K * E) := by gcongr
      _ = (C + 3) ^ 2 * K * (N * E) := by ring
  set X := (C + 3) ^ 2 * K * (N * E) with hX
  have hX0 : 0 ≤ X := by positivity
  calc A₀ * ((N : ℝ) * ℓ ^ 2 / T + T * ℓ * (N : ℝ) ^ (-1 / 2 : ℝ) + ℓ ^ 2 +
        ℓ * (N : ℝ) ^ (1 / 2 : ℝ) * Real.log N +
        N * ℓ ^ 2 * Real.exp (-(1 / 16200 * Real.log N / logQT q T)))
      ≤ A₀ * (8 * X) := by
        apply mul_le_mul_of_nonneg_left _ hA₀.le
        linarith
    _ ≤ (A₀ * (C + 3) ^ 2 * 8 * K + 1) * N * E := by
        have : 0 ≤ (N : ℝ) * E := by positivity
        rw [hX]; nlinarith

end NTKB
