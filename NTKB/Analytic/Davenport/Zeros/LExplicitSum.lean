/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitPrime

/-!
# `ψ₀(N, χ) - J(N, T, χ)` for integral `N`

**Davenport, Ch. 19, pp. 115-117.** The analogue of 17-7 and of (11) of Ch. 17 for
`ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`: with `J(x, T, χ) = (1/2πi) ∫_{c-iT}^{c+iT} -L'/L(s, χ) x^s/s ds`,
`J(x, T, χ) = ∑ χ(n) Λ(n) I(x/n, T)` and `|ψ₀(N, χ) - J(N, T, χ)| ≪ N log² N / T` for integers
`N ≥ 3` and `c = 1 + 1/log N` (the same majorant as for `ψ`, since `|χ(n)| ≤ 1`).
-/

open Filter Topology Complex Set DirichletCharacter LSeries MeasureTheory
open scoped Real LSeries.notation ArithmeticFunction.vonMangoldt Interval

namespace NTKB

variable {q : ℕ} [NeZero q]

/-- `F(s, χ) = -L'/L(s, χ) · x^s/s`. -/
noncomputable def explicitIntegrandL (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  -(deriv (LFunction χ) s / LFunction χ s) * perronKernel x s

/-- `J(x, T, χ) = (1/2π) ∫_{-T}^{T} F(c + it, χ) dt`. -/
noncomputable def explicitJL (χ : DirichletCharacter ℂ q) (x c T : ℝ) : ℂ :=
  (1 / (2 * π)) * ∫ t : ℝ in -T..T, explicitIntegrandL χ x (c + t * I)

/-- **Davenport, Ch. 19, p. 115 (row 19-1)**: `ψ₀(N, χ) = ∑_{n < N} χ(n) Λ(n) + χ(N) Λ(N)/2`. -/
noncomputable def psi0L (χ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, χ n * Λ n) + χ N * Λ N / 2

/-- `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`. -/
noncomputable def psiL (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, χ n * Λ n

omit [NeZero q] in
lemma psiL_natCast_eq (χ : DirichletCharacter ℂ q) (N : ℕ) :
    psiL χ N = psi0L χ N + χ N * Λ N / 2 := by
  rw [psiL, Nat.floor_natCast, psi0L]
  have : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext n; simp [Finset.mem_Icc, Finset.mem_range, Nat.lt_succ_iff]
  rw [this, Finset.sum_range_succ]
  ring

/-- **Davenport, Ch. 19, p. 116**: `J(x, T, χ) = ∑_n χ(n) Λ(n) I(x/n, T)` for `x > 0`, `c > 1`. -/
@[kb "davenport1980" "Ch 19, p. 116"]
theorem Davenport.hasSum_explicitJL (χ : DirichletCharacter ℂ q) {x c : ℝ} (T : ℝ) (hx : 0 < x)
    (hc : 1 < c) :
    HasSum (fun n : ℕ ↦ χ n * (Λ n : ℂ) * perronIntegral (x / n) c T) (explicitJL χ x c T) := by
  have hc0 : 0 < c := by linarith
  have hc1 : 1 < ((c : ℝ) : ℂ).re := by simpa using hc
  have hsumΛ := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hc1
  set b : ℕ → ℝ := fun n ↦ ‖term (↗χ * ↗Λ) (c : ℂ) n‖ * x ^ c / c
  have hb : Summable b := (hsumΛ.norm.mul_right (x ^ c)).div_const c
  have hF : ∀ t : ℝ, HasSum (fun n : ℕ ↦ χ n * (Λ n : ℂ) * perronKernel (x / n) (c + t * I))
      (explicitIntegrandL χ x (c + t * I)) := by
    intro t
    have h1 : 1 < ((c : ℂ) + t * I).re := by simpa using hc
    have hs := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h1).LSeriesHasSum
    have he := neg_logDeriv_LFunction_eq_LSeries χ h1
    have := hs.mul_right (perronKernel x (c + t * I))
    rw [← he] at this
    have e : explicitIntegrandL χ x (c + t * I) = -deriv (LFunction χ) (c + t * I) /
        LFunction χ (c + t * I) * perronKernel x (c + t * I) := by
      simp [explicitIntegrandL, neg_div]
    rw [e]
    convert this using 1
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [term_of_ne_zero hn]
      simp only [Pi.mul_apply]
      rw [mul_assoc, ← perronKernel_div_nat hx.le hn]
      ring
  have hbound : ∀ n : ℕ, ∀ t : ℝ,
      ‖χ n * (Λ n : ℂ) * perronKernel (x / n) (c + t * I)‖ ≤ b n := by
    intro n t
    rcases eq_or_ne n 0 with rfl | hn
    · simp [b]
    rw [mul_assoc, ← perronKernel_div_nat hx.le hn, ← mul_assoc, norm_mul]
    simp only [b]
    rw [mul_div_assoc]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _)
    · rw [term_of_ne_zero hn]
      simp only [Pi.mul_apply, norm_div, norm_mul]
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_div_assoc]
    · rw [norm_perronKernel hx]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero]
      apply div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hc0
      have := Complex.re_le_norm ((c : ℂ) + t * I)
      simpa using this
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun t : ℝ ↦ χ n * (Λ n : ℂ) * perronKernel (x / n) (c + t * I))
      (volume.restrict (Ι (-T) T)) := by
    intro n
    refine (Continuous.aestronglyMeasurable ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero, zero_mul]
      exact continuous_const
    refine continuous_const.mul ?_
    have hy : 0 < x / n := div_pos hx (by exact_mod_cast Nat.pos_of_ne_zero hn)
    have hg : Continuous fun t : ℝ ↦ (c : ℂ) + t * I :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hne : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0 := fun t h ↦ by
      have := congrArg Complex.re h; simp at this; linarith
    have hy' : ((x / n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have h1 : Continuous fun t : ℝ ↦ ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) :=
      hg.const_cpow (Or.inl hy')
    have h2 : Continuous fun t : ℝ ↦ ((c : ℂ) + t * I)⁻¹ := hg.inv₀ hne
    exact (h1.mul h2).congr fun t ↦ by simp only [perronKernel, div_eq_mul_inv, Pi.mul_apply]
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -T)
    (b := T) (fun n _ ↦ b n) hmeas (fun n ↦ Eventually.of_forall fun t _ ↦ hbound n t)
    (Eventually.of_forall fun t _ ↦ hb) intervalIntegrable_const
    (Eventually.of_forall fun t _ ↦ hF t)
  unfold explicitJL
  have := h.mul_left (1 / (2 * π) : ℂ)
  refine this.congr_fun fun n ↦ ?_
  rw [intervalIntegral.integral_const_mul]
  show χ n * (Λ n : ℂ) * ((1 / (2 * π)) * ∫ t : ℝ in -T..T, perronKernel (x / n) (c + t * I)) = _
  ring

lemma hasSum_psi0L (χ : DirichletCharacter ℂ q) (N : ℕ) :
    HasSum (fun n : ℕ ↦ χ n * (Λ n : ℂ) * perronStep N n) (psi0L χ N) := by
  have : ∀ n ∉ Finset.range (N + 1), χ n * (Λ n : ℂ) * perronStep N n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have h1 : ¬ n < N := by omega
    rcases eq_or_ne n N with rfl | hnN
    · omega
    · simp [perronStep, h1, hnN]
  have h : HasSum (fun n : ℕ ↦ χ n * (Λ n : ℂ) * perronStep N n)
      (∑ n ∈ Finset.range (N + 1), χ n * (Λ n : ℂ) * perronStep N n) :=
    hasSum_sum_of_ne_finset_zero this
  convert h using 1
  rw [Finset.sum_range_succ, psi0L]
  congr 1
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    simp [perronStep, Finset.mem_range.mp hn]
  · simp [perronStep]; ring

/-- **Davenport, Ch. 19, p. 117 (the analogue of (11) of Ch. 17)**: for integers `N ≥ 3`,
`c = 1 + 1/log N`, `T > 0` and every Dirichlet character `χ`,
`|ψ₀(N, χ) - J(N, T, χ)| ≤ 100 N log² N / T` (the constant does not depend on `q`). -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.norm_psi0L_sub_explicitJL_le (χ : DirichletCharacter ℂ q) {N : ℕ} (hN : 3 ≤ N)
    {T : ℝ} (hT : 0 < T) :
    ‖psi0L χ N - explicitJL χ N (1 + 1 / Real.log N) T‖ ≤ 100 * N * Real.log N ^ 2 / T := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hc1 : 1 < 1 + 1 / Real.log N := by have : 0 < 1 / Real.log N := by positivity
                                          linarith
  have hJ := Davenport.hasSum_explicitJL χ (x := N) T hN0 hc1
  have hψ := hasSum_psi0L χ N
  have hd := hJ.sub hψ
  obtain ⟨G, S, hG, hS, hGb⟩ := exists_perron_majorant hN hT
  have hbound := tsum_of_norm_bounded (f := fun n : ℕ ↦ χ n * (Λ n : ℂ) *
      perronIntegral (N / n) (1 + 1 / Real.log N) T - χ n * (Λ n : ℂ) * (perronStep N n : ℂ)) hG
    fun n ↦ by
      have h1 := hGb n
      rw [← mul_sub, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg
        ArithmeticFunction.vonMangoldt_nonneg]
      have h2 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
      have h3 : 0 ≤ Λ n * ‖perronIntegral (N / n) (1 + 1 / Real.log N) T - perronStep N n‖ :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (norm_nonneg _)
      calc ‖χ n‖ * Λ n * ‖perronIntegral (N / n) (1 + 1 / Real.log N) T - perronStep N n‖
          = ‖χ n‖ * (Λ n * ‖perronIntegral (N / n) (1 + 1 / Real.log N) T - perronStep N n‖) := by
            ring
        _ ≤ 1 * (Λ n * ‖perronIntegral (N / n) (1 + 1 / Real.log N) T - perronStep N n‖) :=
            mul_le_mul_of_nonneg_right h2 h3
        _ ≤ G n := by rw [one_mul]; exact h1
  rw [hd.tsum_eq, norm_sub_rev] at hbound
  exact hbound.trans hS

end NTKB
