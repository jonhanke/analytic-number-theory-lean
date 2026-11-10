/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LZeroFreeReal

/-!
# Local distribution of the zeros of `ζ(s)`

**Davenport, Ch. 15, pp. 98-99.**

* (row 15-6, Lemma) `∑_ρ 1/(1 + (T - γ)²) = O(log T)`; we prove `≤ A log(|T| + 2)` for every real
  `T`, from the real part of (8) of Ch. 12 at `s = 2 + iT`;
* (row 15-7) the number of zeros with `|γ - T| < 1` is `O(log T)`;
* (row 15-8) `∑_{|γ - T| ≥ 1} (T - γ)^{-2} = O(log T)`;
* (row 15-9) for `-1 ≤ σ ≤ 2`, `|t| ≥ 2`, `ζ(s) ≠ 0`:
  `ζ'/ζ(s) = ∑_{|t - γ| < 1} 1/(s - ρ) + O(log |t|)`.
-/

open Filter Topology Complex Set DirichletCharacter LSeries
open scoped Real LSeries.notation ArithmeticFunction.vonMangoldt

namespace NTKB

/-- `|L'/L(σ + it, χ)| ≤ -ζ'/ζ(σ)` for `σ > 1`. -/
lemma norm_logDeriv_LFunction_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ -(deriv riemannZeta s.re / riemannZeta s.re).re := by
  have h1 : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  have e := neg_logDeriv_LFunction_eq_LSeries χ hs
  have e0 := neg_logDeriv_LFunction_eq_LSeries (1 : DirichletCharacter ℂ 1) h1
  rw [LFunction_modOne_eq] at e0
  have s0 := Complex.reCLM.hasSum (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
    (1 : DirichletCharacter ℂ 1) h1).LSeriesHasSum
  have hsre : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
  have hb : ∀ n, ‖term (↗χ * ↗Λ) s n‖ ≤
      Complex.reCLM (term (↗(1 : DirichletCharacter ℂ 1) * ↗Λ) ((s.re : ℝ) : ℂ) n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have t0 := term_twist_vonMangoldt_eq (1 : DirichletCharacter ℂ 1) s.re 0 hn
    simp only [Complex.ofReal_zero, zero_mul, add_zero, neg_zero, Complex.exp_zero,
      mul_one] at t0
    have t1 := term_twist_vonMangoldt_eq χ s.re s.im hn
    rw [← hsre] at t1
    rw [Complex.reCLM_apply, t0, t1, MulChar.one_apply (isUnit_of_subsingleton _)]
    set c : ℝ := Λ n * (n : ℝ) ^ (-s.re)
    have hc : 0 ≤ c := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg n.cast_nonneg _)
    have he : ‖Complex.exp (-(s.im * Real.log n) * I)‖ = 1 := by
      rw [show -((s.im : ℂ) * (Real.log n : ℝ)) * I = ((-(s.im * Real.log n)) : ℝ) * I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg hc]
    simp only [one_mul, Complex.ofReal_re]
    exact mul_le_of_le_one_left hc (χ.norm_le_one _)
  have := tsum_of_norm_bounded s0 hb
  rw [← LSeries, ← e] at this
  rw [← e0, neg_div, norm_neg, Complex.reCLM_apply, neg_div, Complex.neg_re] at this
  exact this

/-- The constant `-ζ'/ζ(2) = ∑ Λ(n) n^{-2}`. -/
noncomputable def zetaLogDerivTwo : ℝ := -(deriv riemannZeta (2 : ℝ) / riemannZeta (2 : ℝ)).re

lemma norm_logDeriv_riemannZeta_two_add (t : ℝ) :
    ‖deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I)‖ ≤ zetaLogDerivTwo := by
  have h := norm_logDeriv_LFunction_le (1 : DirichletCharacter ℂ 1) (s := 2 + t * I)
    (by simp)
  rw [LFunction_modOne_eq] at h
  simpa [zetaLogDerivTwo] using h

lemma zetaLogDerivTwo_nonneg : 0 ≤ zetaLogDerivTwo :=
  (norm_nonneg _).trans (norm_logDeriv_riemannZeta_two_add 0)

/-- `1/(1 + (T - γ)²) ≤ 4 Re 1/(2 + iT - ρ)` for `0 < β < 1`. -/
lemma inv_one_add_sq_le_four_re {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (T : ℝ) :
    1 / (1 + (T - ρ.im) ^ 2) ≤ 4 * (1 / (2 + T * I - ρ)).re := by
  have hz : (2 + T * I - ρ) ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h; simp at this; linarith
  rw [one_div (2 + T * I - ρ), Complex.inv_re, Complex.normSq_apply]
  simp only [sub_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, sub_im, add_im, im_ofNat, mul_im, zero_add]
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [sq_nonneg (T - ρ.im)]

/-- **Davenport, Ch. 15, p. 98, Lemma (row 15-6)**: there is `A` such that for every real `T`,
`∑_ρ 1/(1 + (T - γ)²) ≤ A log(|T| + 2)`, the sum over the nontrivial zeros of `ζ` with
multiplicity (summable). -/
@[kb "davenport1980" "Ch 15, p. 98"]
theorem Davenport.sum_zeta_zeros_inv_one_add_sq_le :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ,
      Summable (fun ρ : ZeroIndex riemannXi ↦ 1 / (1 + (T - ρ.val.im) ^ 2)) ∧
      ∑' ρ : ZeroIndex riemannXi, 1 / (1 + (T - ρ.val.im) ^ 2) ≤ A * Real.log (|T| + 2) := by
  have hl2 := log_two_gt_two_thirds
  have hC := zetaLogDerivTwo_nonneg
  refine ⟨4 * (5 + (1 + zetaLogDerivTwo) / Real.log 2), by positivity, fun T ↦ ?_⟩
  set s : ℂ := 2 + T * I with hs
  have hsre : s.re = 2 := by simp [s]
  have hsim : s.im = T := by simp [s]
  have hne : ∀ ρ : ZeroIndex riemannXi, ρ.val ≠ s := fun ρ h ↦ by
    have := congrArg Complex.re h; rw [hsre] at this; linarith [(riemannXi_zero_mem ρ).2.2]
  have hS := summable_re_inv_sub_riemannXi_zeros hne
  have hle : ∀ ρ : ZeroIndex riemannXi, 1 / (1 + (T - ρ.val.im) ^ 2) ≤
      4 * (1 / (s - ρ.val)).re := fun ρ ↦
    inv_one_add_sq_le_four_re (riemannXi_zero_mem ρ).2.1 (riemannXi_zero_mem ρ).2.2 T
  have hS' : Summable (fun ρ : ZeroIndex riemannXi ↦ 1 / (1 + (T - ρ.val.im) ^ 2)) :=
    Summable.of_nonneg_of_le (fun ρ ↦ by positivity) hle (hS.mul_left 4)
  refine ⟨hS', ?_⟩
  -- the identity at `s = 2 + iT`
  have hs1 : s ≠ 1 := fun h ↦ by have := congrArg Complex.re h; rw [hsre] at this; simp at this
  have hz := riemannZeta_ne_zero_of_one_lt_re (s := s) (by rw [hsre]; norm_num)
  have hid := Davenport.neg_re_logDeriv_riemannZeta_eq hs1 hz
  have hψ := re_digamma_half_le (s := s) (by rw [hsre]; norm_num) (by rw [hsre])
  have hz2 : -(deriv riemannZeta s / riemannZeta s).re ≥ -zetaLogDerivTwo := by
    have := norm_logDeriv_riemannZeta_two_add T
    have := Complex.re_le_norm (deriv riemannZeta s / riemannZeta s)
    linarith
  have hr1 : (1 / (s - 1)).re ≤ 1 := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, norm_one]
    refine div_le_one_of_le₀ ?_ (norm_nonneg _)
    have := Complex.re_le_norm (s - 1)
    simp [hsre] at this ⊢
    linarith
  have hπ : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  rw [hsim] at hψ
  have hlT : Real.log 2 ≤ Real.log (|T| + 2) := Real.log_le_log two_pos (by linarith [abs_nonneg T])
  have hsum : ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val)).re ≤
      (5 + (1 + zetaLogDerivTwo) / Real.log 2) * Real.log (|T| + 2) := by
    have h1 : ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val)).re ≤
        1 + zetaLogDerivTwo + 5 * Real.log (|T| + 2) := by linarith
    have h2 : 1 + zetaLogDerivTwo ≤ (1 + zetaLogDerivTwo) / Real.log 2 * Real.log (|T| + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      exact mul_le_mul_of_nonneg_left hlT (by linarith)
    linarith
  calc ∑' ρ : ZeroIndex riemannXi, 1 / (1 + (T - ρ.val.im) ^ 2)
      ≤ ∑' ρ : ZeroIndex riemannXi, 4 * (1 / (s - ρ.val)).re := hS'.tsum_le_tsum hle (hS.mul_left 4)
    _ = 4 * ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val)).re := tsum_mul_left
    _ ≤ 4 * (5 + (1 + zetaLogDerivTwo) / Real.log 2) * Real.log (|T| + 2) := by
        rw [mul_assoc]; gcongr

lemma norm_zeta_zero_le (ρ : ZeroIndex riemannXi) : ‖ρ.val‖ ≤ 1 + |ρ.val.im| := by
  have h := riemannXi_zero_mem ρ
  have := Complex.norm_le_abs_re_add_abs_im ρ.val
  rw [abs_of_pos h.2.1] at this
  linarith [h.2.2]

/-- **Davenport, Ch. 15, p. 99, corollary (a) (row 15-7)**: the number of zeros (with
multiplicity) with `|γ - T| < 1` is finite and at most `A log(|T| + 2)`. -/
@[kb "davenport1980" "Ch 15, p. 99"]
theorem Davenport.card_zeta_zeros_near_le :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, {ρ : ZeroIndex riemannXi | |ρ.val.im - T| < 1}.Finite ∧
      ({ρ : ZeroIndex riemannXi | |ρ.val.im - T| < 1}.ncard : ℝ) ≤ A * Real.log (|T| + 2) := by
  obtain ⟨A, hA, h⟩ := Davenport.sum_zeta_zeros_inv_one_add_sq_le
  refine ⟨2 * A, by positivity, fun T ↦ ?_⟩
  obtain ⟨hS, hle⟩ := h T
  have hfin : {ρ : ZeroIndex riemannXi | |ρ.val.im - T| < 1}.Finite := by
    have hF := finite_zeroIndex_closedBall differentiable_riemannXi (|T| + 2)
    refine (Set.finite_coe_iff.mp ?_).subset (s := {ρ : ZeroIndex riemannXi | ‖ρ.val‖ ≤ |T| + 2})
      fun ρ hρ ↦ ?_
    · exact hF
    · simp only [Set.mem_ofPred_eq] at hρ ⊢
      have := norm_zeta_zero_le ρ
      have : |ρ.val.im| ≤ |T| + 1 := by
        have := abs_sub_abs_le_abs_sub ρ.val.im T
        linarith
      linarith
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hsum := hS.sum_le_tsum hfin.toFinset (fun ρ _ ↦ by positivity)
  have hcard : (hfin.toFinset.card : ℝ) * (1 / 2) ≤
      ∑ ρ ∈ hfin.toFinset, 1 / (1 + (T - ρ.val.im) ^ 2) := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun ρ hρ ↦ ?_
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
    have : (T - ρ.val.im) ^ 2 < 1 := by
      rw [← sq_abs, abs_sub_comm]; nlinarith [abs_nonneg (ρ.val.im - T)]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  linarith

/-- **Davenport, Ch. 15, p. 99, corollary (b) (row 15-8)**:
`∑_{|γ - T| ≥ 1} (T - γ)^{-2} ≤ A log(|T| + 2)`. -/
@[kb "davenport1980" "Ch 15, p. 99"]
theorem Davenport.sum_zeta_zeros_far_le :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ,
      Summable (fun ρ : ZeroIndex riemannXi ↦
        if 1 ≤ |T - ρ.val.im| then 1 / (T - ρ.val.im) ^ 2 else 0) ∧
      ∑' ρ : ZeroIndex riemannXi, (if 1 ≤ |T - ρ.val.im| then 1 / (T - ρ.val.im) ^ 2 else 0) ≤
        A * Real.log (|T| + 2) := by
  obtain ⟨A, hA, h⟩ := Davenport.sum_zeta_zeros_inv_one_add_sq_le
  refine ⟨2 * A, by positivity, fun T ↦ ?_⟩
  obtain ⟨hS, hle⟩ := h T
  have hb : ∀ ρ : ZeroIndex riemannXi,
      (if 1 ≤ |T - ρ.val.im| then 1 / (T - ρ.val.im) ^ 2 else 0) ≤
        2 * (1 / (1 + (T - ρ.val.im) ^ 2)) := by
    intro ρ
    split_ifs with h1
    · have : 1 ≤ (T - ρ.val.im) ^ 2 := by rw [← sq_abs]; nlinarith
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    · positivity
  have hS' : Summable (fun ρ : ZeroIndex riemannXi ↦
      if 1 ≤ |T - ρ.val.im| then 1 / (T - ρ.val.im) ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun ρ ↦ by split_ifs <;> positivity) hb (hS.mul_left 2)
  refine ⟨hS', ?_⟩
  calc _ ≤ ∑' ρ : ZeroIndex riemannXi, 2 * (1 / (1 + (T - ρ.val.im) ^ 2)) :=
        hS'.tsum_le_tsum hb (hS.mul_left 2)
    _ = 2 * ∑' ρ : ZeroIndex riemannXi, 1 / (1 + (T - ρ.val.im) ^ 2) := tsum_mul_left
    _ ≤ 2 * A * Real.log (|T| + 2) := by rw [mul_assoc]; gcongr

/-- `‖ψ(z/2 + 1)‖ ≤ 5 + 4 log(|t| + 2)` for `-1 ≤ σ ≤ 2`, `|t| ≥ 2`. -/
lemma norm_digamma_half_add_one_le {z : ℂ} (h1 : -1 ≤ z.re) (h2 : z.re ≤ 2) (ht : 2 ≤ |z.im|) :
    ‖Complex.digamma (z / 2 + 1)‖ ≤ 5 + 4 * Real.log (|z.im| + 2) := by
  set w := z / 2 + 1
  have hwre : w.re = z.re / 2 + 1 := by simp [w]
  have hwim : w.im = z.im / 2 := by simp [w]
  have hw1 : 1 / 2 ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w
    rw [hwim, abs_div, abs_two] at this
    linarith
  have hwn : ‖w‖ ≤ |z.im| + 2 := by
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [hwre, hwim, abs_div, abs_two] at this
    have : |z.re / 2 + 1| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    linarith [abs_nonneg z.im]
  have hlogw : Real.log (‖w‖ + 1) ≤ 2 * Real.log (|z.im| + 2) := by
    rw [show (2 : ℝ) * Real.log (|z.im| + 2) = ((2 : ℕ) : ℝ) * Real.log (|z.im| + 2) by norm_num,
      ← Real.log_pow]
    exact Real.log_le_log (by linarith [norm_nonneg w]) (by nlinarith [abs_nonneg z.im])
  have := norm_digamma_le_of_half (w := w) (by rw [hwre]; linarith) hw1
  linarith

/-- The partial fraction formula (8) of Ch. 12 with the digamma function. -/
lemma logDeriv_riemannZeta_digamma {A B : ℂ}
    (h : ∀ s, riemannXi s = Complex.exp (A + B * s) *
      ∏' ρ : ZeroIndex riemannXi, (1 - s / ρ.val) * Complex.exp (s / ρ.val))
    {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      B - 1 / (s - 1) + Complex.log π / 2 - Complex.digamma (s / 2 + 1) / 2 +
        ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val) + 1 / ρ.val) := by
  rw [Davenport.logDeriv_riemannZeta h hs1 hz, Complex.digamma_def, logDeriv_apply]
  ring

/-- **Davenport, Ch. 15, p. 99, (D) (row 15-9)**: there is `A` such that for `-1 ≤ σ ≤ 2`,
`|t| ≥ 2` and `ζ(s) ≠ 0`, `|ζ'/ζ(s) - ∑_{|t - γ| < 1} 1/(s - ρ)| ≤ A log(|t| + 2)`; the sum is
over the zeros (with multiplicity) with `|t - γ| < 1`, written as a sum with finite support. -/
@[kb "davenport1980" "Ch 15, p. 99"]
theorem Davenport.logDeriv_riemannZeta_local :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s -
        ∑' ρ : ZeroIndex riemannXi, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ ≤
        A * Real.log (|s.im| + 2) := by
  classical
  obtain ⟨A₀, hA₀, h₀⟩ := Davenport.sum_zeta_zeros_inv_one_add_sq_le
  obtain ⟨Aa, Ba, hH⟩ := Davenport.riemannXi_hadamard
  have hC := zetaLogDerivTwo_nonneg
  refine ⟨zetaLogDerivTwo + 11 + 6 * A₀, by positivity, fun s hσ1 hσ2 ht hz ↦ ?_⟩
  set t := s.im with ht_def
  set s₀ : ℂ := 2 + t * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [s₀]
  have hs₀im : s₀.im = t := by simp [s₀]
  have hs1 : s ≠ 1 := fun h ↦ by
    have := congrArg Complex.im h; rw [← ht_def] at this; simp at this; rw [this] at ht
    norm_num at ht
  have hs₀1 : s₀ ≠ 1 := fun h ↦ by
    have := congrArg Complex.re h; rw [hs₀re] at this; norm_num at this
  have hz₀ := riemannZeta_ne_zero_of_one_lt_re (s := s₀) (by rw [hs₀re]; norm_num)
  obtain ⟨ha, ha0⟩ := summable_riemannXi_zeros
  have hne : ∀ ρ : ZeroIndex riemannXi, ρ.val ≠ s := riemannXi_zero_ne hz
  have hne₀ : ∀ ρ : ZeroIndex riemannXi, ρ.val ≠ s₀ := riemannXi_zero_ne hz₀
  have hS := summable_inv_sub_add_inv ha ha0 hne
  have hS₀ := summable_inv_sub_add_inv ha ha0 hne₀
  have hF := logDeriv_riemannZeta_digamma hH hs1 hz
  have hF₀ := logDeriv_riemannZeta_digamma hH hs₀1 hz₀
  -- the near and the remaining parts
  set n₁ : ZeroIndex riemannXi → ℂ := fun ρ ↦ if |t - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0
  set g : ZeroIndex riemannXi → ℂ := fun ρ ↦ 1 / (s - ρ.val) - 1 / (s₀ - ρ.val)
  have hg : Summable g := (hS.sub hS₀).congr fun ρ ↦ by simp only [g]; ring
  have hfin : {ρ : ZeroIndex riemannXi | |ρ.val.im - t| < 1}.Finite := by
    obtain ⟨A₁, -, h₁⟩ := Davenport.card_zeta_zeros_near_le
    exact (h₁ t).1
  have hn₁ : Summable n₁ := by
    refine summable_of_ne_finset_zero (s := hfin.toFinset) fun ρ hρ ↦ ?_
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, abs_sub_comm] at hρ
    simp [n₁, hρ]
  set r : ZeroIndex riemannXi → ℂ := fun ρ ↦ g ρ - n₁ ρ
  have hr : Summable r := hg.sub hn₁
  -- bound on `r`
  obtain ⟨hS1, hle1⟩ := h₀ t
  have hrb : ∀ ρ : ZeroIndex riemannXi, ‖r ρ‖ ≤ 6 * (1 / (1 + (t - ρ.val.im) ^ 2)) := by
    intro ρ
    have hβ := riemannXi_zero_mem ρ
    have hd₀ : 1 ≤ ‖s₀ - ρ.val‖ := by
      have := Complex.re_le_norm (s₀ - ρ.val)
      simp only [sub_re, hs₀re] at this
      linarith [hβ.2.2]
    simp only [r, g, n₁]
    split_ifs with hnear
    · have : (t - ρ.val.im) ^ 2 < 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (t - ρ.val.im)]
      rw [sub_sub_cancel_left, norm_neg, norm_div, norm_one]
      calc 1 / ‖s₀ - ρ.val‖ ≤ 1 := by rw [div_le_one (by linarith)]; exact hd₀
        _ ≤ 6 * (1 / (1 + (t - ρ.val.im) ^ 2)) := by
            rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
    · push Not at hnear
      have hsq : 1 ≤ (t - ρ.val.im) ^ 2 := by rw [← sq_abs]; nlinarith
      have hsρ : |t - ρ.val.im| ≤ ‖s - ρ.val‖ := by
        have := Complex.abs_im_le_norm (s - ρ.val); simpa [← ht_def] using this
      have hs₀ρ : |t - ρ.val.im| ≤ ‖s₀ - ρ.val‖ := by
        have := Complex.abs_im_le_norm (s₀ - ρ.val); simpa [hs₀im] using this
      have hne1 : s - ρ.val ≠ 0 := sub_ne_zero.mpr (hne ρ).symm
      have hne2 : s₀ - ρ.val ≠ 0 := sub_ne_zero.mpr (hne₀ ρ).symm
      have heq : 1 / (s - ρ.val) - 1 / (s₀ - ρ.val) - 0 =
          (s₀ - s) / ((s - ρ.val) * (s₀ - ρ.val)) := by field_simp; ring
      have hss : ‖s₀ - s‖ ≤ 3 := by
        have : s₀ - s = ((2 - s.re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [s₀, ← ht_def]
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
      rw [heq, norm_div, norm_mul]
      have hp : 0 < |t - ρ.val.im| := by linarith
      calc ‖s₀ - s‖ / (‖s - ρ.val‖ * ‖s₀ - ρ.val‖) ≤ 3 / (|t - ρ.val.im| * |t - ρ.val.im|) :=
            div_le_div₀ (by norm_num) hss (by positivity) (mul_le_mul hsρ hs₀ρ hp.le
              (norm_nonneg _))
        _ = 3 / (t - ρ.val.im) ^ 2 := by rw [abs_mul_abs_self, sq]
        _ ≤ 6 * (1 / (1 + (t - ρ.val.im) ^ 2)) := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hrsum : ‖∑' ρ, r ρ‖ ≤ 6 * A₀ * Real.log (|t| + 2) := by
    refine (tsum_of_norm_bounded (hS1.mul_left 6).hasSum hrb).trans ?_
    rw [tsum_mul_left, mul_assoc]; gcongr
  -- assemble
  have hsplit : ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val) + 1 / ρ.val) -
      ∑' ρ : ZeroIndex riemannXi, (1 / (s₀ - ρ.val) + 1 / ρ.val) =
      ∑' ρ, n₁ ρ + ∑' ρ, r ρ := by
    rw [← hS.tsum_sub hS₀, ← hn₁.tsum_add hr]
    exact tsum_congr fun ρ ↦ by simp only [r, g]; ring
  have hn₁eq : ∑' ρ : ZeroIndex riemannXi, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0) =
      ∑' ρ, n₁ ρ := rfl
  rw [hn₁eq]
  have hkey : deriv riemannZeta s / riemannZeta s - ∑' ρ, n₁ ρ =
      deriv riemannZeta s₀ / riemannZeta s₀ - 1 / (s - 1) + 1 / (s₀ - 1) -
        Complex.digamma (s / 2 + 1) / 2 + Complex.digamma (s₀ / 2 + 1) / 2 + ∑' ρ, r ρ := by
    rw [hF, hF₀]
    linear_combination hsplit
  rw [hkey]
  -- the individual bounds
  have b0 := norm_logDeriv_riemannZeta_two_add t
  have b1 : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))]
    have := Complex.abs_im_le_norm (s - 1)
    simp only [sub_im, one_im, sub_zero, ← ht_def] at this
    linarith
  have b2 : ‖1 / (s₀ - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (norm_pos_iff.mpr (sub_ne_zero.mpr hs₀1))]
    have := Complex.re_le_norm (s₀ - 1)
    simp only [sub_re, hs₀re, one_re] at this
    linarith
  have b3 := norm_digamma_half_add_one_le hσ1 hσ2 ht
  have b4 := norm_digamma_half_add_one_le (z := s₀) (by rw [hs₀re]; norm_num)
    (by rw [hs₀re]) (by rw [hs₀im]; exact ht)
  rw [hs₀im] at b4
  have hL : 1 ≤ Real.log (|t| + 2) := by
    have h4 : Real.log 4 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
    have : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := log_two_gt_two_thirds; push_cast; linarith
    linarith
  have tri : ‖deriv riemannZeta s₀ / riemannZeta s₀ - 1 / (s - 1) + 1 / (s₀ - 1) -
      Complex.digamma (s / 2 + 1) / 2 + Complex.digamma (s₀ / 2 + 1) / 2 + ∑' ρ, r ρ‖ ≤
      ‖deriv riemannZeta s₀ / riemannZeta s₀‖ + ‖1 / (s - 1)‖ + ‖1 / (s₀ - 1)‖ +
        ‖Complex.digamma (s / 2 + 1)‖ / 2 + ‖Complex.digamma (s₀ / 2 + 1)‖ / 2 +
        ‖∑' ρ, r ρ‖ := by
    have e1 : ‖Complex.digamma (s / 2 + 1) / 2‖ = ‖Complex.digamma (s / 2 + 1)‖ / 2 := by
      rw [norm_div]; simp
    have e2 : ‖Complex.digamma (s₀ / 2 + 1) / 2‖ = ‖Complex.digamma (s₀ / 2 + 1)‖ / 2 := by
      rw [norm_div]; simp
    rw [← e1, ← e2]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_sub_le _ _
  have hC0 : zetaLogDerivTwo ≤ zetaLogDerivTwo * Real.log (|t| + 2) := by nlinarith
  nlinarith

end NTKB
