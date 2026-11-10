/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ZetaPartialFraction
import NTKB.Analytic.Davenport.Zeros.ThreeFourOne

/-!
# A zero-free region for `ζ(s)` (de la Vallée Poussin)

**Davenport, Ch. 13, pp. 85-86.** Combining the 3-4-1 inequality (C) with the bounds
`-ζ'/ζ(σ) < 1/(σ - 1) + A`, `-Re ζ'/ζ(σ + 2iγ) < A log γ` and
`-Re ζ'/ζ(σ + iγ) < A log γ - 1/(σ - β)` at `σ = 1 + δ/log γ` gives:
there is `c > 0` such that `ζ(s) ≠ 0` for `σ > 1 - c/log t`, `t ≥ 2`; and also for
`σ ≥ 1 - c/log(|t| + 2)` and every `t`.

Our constants: `A = 5` in (D), `δ = 1/150`, `c = 1/1050`.
-/

open Filter Topology Complex Set
open scoped Real

namespace NTKB

lemma summable_tsum_nonneg_re {s : ℂ} (h1 : 1 < s.re) :
    0 ≤ ∑' ρ : ZeroIndex riemannXi, (1 / (s - ρ.val)).re :=
  tsum_nonneg fun ρ ↦ (re_one_div_sub_pos (by linarith [(riemannXi_zero_mem ρ).2.2])).le

/-- **Davenport, Ch. 13, p. 85 (row 13-8)**: `-ζ'/ζ(σ) < 1/(σ - 1) + A` for `1 < σ ≤ 2`
(with `A = 5 log 2`). -/
@[kb "davenport1980" "Ch 13, p. 85"]
theorem Davenport.neg_logDeriv_riemannZeta_real_le {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    -(deriv riemannZeta σ / riemannZeta σ).re ≤ 1 / (σ - 1) + 5 * Real.log 2 := by
  have h := Davenport.neg_re_logDeriv_riemannZeta_le (s := σ) (by simpa using h1)
    (by simpa using h2)
  have hn := summable_tsum_nonneg_re (s := σ) (by simpa using h1)
  have hre : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_one,
      ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [Complex.ofReal_im, abs_zero, zero_add, hre] at h
  linarith

lemma re_one_div_sub_one_le {s : ℂ} (ht : s.im ≠ 0) : (1 / (s - 1)).re ≤ 1 / |s.im| := by
  have hne : s - 1 ≠ 0 := fun h ↦ ht (by simpa using congrArg Complex.im h)
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_div, norm_one]
  refine one_div_le_one_div_of_le (abs_pos.mpr ht) ?_
  have := Complex.abs_im_le_norm (s - 1)
  simpa using this

/-- **Davenport, Ch. 13, p. 86 (row 13-10)**, first estimate: for `1 < σ ≤ 2`,
`-Re ζ'/ζ(s) ≤ Re 1/(s - 1) + 5 log(|t| + 2)`. -/
@[kb "davenport1980" "Ch 13, p. 86"]
theorem Davenport.neg_re_logDeriv_riemannZeta_le_log {s : ℂ} (h1 : 1 < s.re) (h2 : s.re ≤ 2) :
    -(deriv riemannZeta s / riemannZeta s).re ≤ (1 / (s - 1)).re + 5 * Real.log (|s.im| + 2) := by
  have h := Davenport.neg_re_logDeriv_riemannZeta_le h1 h2
  have hn := summable_tsum_nonneg_re h1
  linarith

/-- **Davenport, Ch. 13, p. 86 (row 13-10)**, second estimate: if `ρ = β + iγ` is a nontrivial
zero and `1 < σ ≤ 2`, then
`-Re ζ'/ζ(σ + iγ) ≤ Re 1/(σ + iγ - 1) + 5 log(|γ| + 2) - 1/(σ - β)`. -/
@[kb "davenport1980" "Ch 13, p. 86"]
theorem Davenport.neg_re_logDeriv_riemannZeta_le_zero (ρ : ZeroIndex riemannXi) {σ : ℝ}
    (h1 : 1 < σ) (h2 : σ ≤ 2) :
    -(deriv riemannZeta (σ + ρ.val.im * I) / riemannZeta (σ + ρ.val.im * I)).re ≤
      (1 / ((σ : ℂ) + ρ.val.im * I - 1)).re + 5 * Real.log (|ρ.val.im| + 2) -
        1 / (σ - ρ.val.re) := by
  set s : ℂ := σ + ρ.val.im * I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = ρ.val.im := by simp [s]
  have h := Davenport.neg_re_logDeriv_riemannZeta_le (s := s) (by rw [hsre]; exact h1)
    (by rw [hsre]; exact h2)
  have hβ := (riemannXi_zero_mem ρ).2.2
  have hsum : Summable fun ρ' : ZeroIndex riemannXi ↦ (1 / (s - ρ'.val)).re :=
    summable_re_inv_sub_riemannXi_zeros fun ρ' h ↦ by
      have := congrArg Complex.re h
      rw [hsre] at this
      linarith [(riemannXi_zero_mem ρ').2.2]
  have hle : (1 / (s - ρ.val)).re ≤ ∑' ρ' : ZeroIndex riemannXi, (1 / (s - ρ'.val)).re :=
    hsum.le_tsum ρ fun ρ' _ ↦
      (re_one_div_sub_pos (by rw [hsre]; linarith [(riemannXi_zero_mem ρ').2.2])).le
  have heq : (1 / (s - ρ.val)).re = 1 / (σ - ρ.val.re) := by
    have : s - ρ.val = ((σ - ρ.val.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s]
    rw [this, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hsim] at h
  linarith

/-- **de la Vallée Poussin's zero-free region** (Davenport, Ch. 13, p. 86, row 13-11):
there is `c > 0` such that every zero `β + iγ` of `ζ` with `|γ| ≥ 2` has `β ≤ 1 - c/log|γ|`
(we may take `c = 1/1050`). -/
@[kb "davenport1980" "Ch 13, p. 86"]
theorem Davenport.riemannZeta_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, riemannZeta s = 0 → 2 ≤ |s.im| →
      s.re ≤ 1 - c / Real.log |s.im| := by
  refine ⟨1 / 1050, by norm_num, fun s hs ht ↦ ?_⟩
  have hl2 := log_two_gt_two_thirds
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log |s.im| := ⟨_, rfl⟩
  rw [← hLdef]
  have hL2 : Real.log 2 ≤ L := hLdef ▸ Real.log_le_log two_pos ht
  have hL : 0 < L := by linarith
  -- trivial zeros and zeros left of the critical line are far from `σ = 1`
  rcases le_or_gt s.re 0 with h0 | h0
  · have : 1 / 1050 / L ≤ 1 := by
      rw [div_le_one hL]; linarith
    linarith
  obtain ⟨ρ, rfl⟩ := exists_zeroIndex_riemannXi hs h0
  have hβ := riemannXi_zero_mem ρ
  -- the choice `σ = 1 + δ/L`, `δ = 1/150`
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 + 1 / 150 / L := ⟨_, rfl⟩
  have hσ1 : 1 < σ := by
    rw [hσ]; have : 0 < 1 / 150 / L := by positivity
    linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσ]
    have : 1 / 150 / L ≤ 1 := by rw [div_le_one hL]; linarith
    linarith
  have hγ0 : ρ.val.im ≠ 0 := fun h ↦ by simp [h] at ht; linarith
  -- the three estimates
  have e1 := Davenport.neg_logDeriv_riemannZeta_real_le hσ1 hσ2
  have e2 := Davenport.neg_re_logDeriv_riemannZeta_le_zero ρ hσ1 hσ2
  have e3 := Davenport.neg_re_logDeriv_riemannZeta_le_log (s := σ + (2 * ρ.val.im : ℝ) * I)
    (by simpa using hσ1) (by simpa using hσ2)
  have key := Davenport.three_four_one_riemannZeta hσ1 ρ.val.im
  -- bounds on the auxiliary terms
  have hlogT2 : Real.log (|ρ.val.im| + 2) ≤ 2 * L := by
    rw [hLdef, show (2 : ℝ) * Real.log |ρ.val.im| = ((2 : ℕ) : ℝ) * Real.log |ρ.val.im| by
      norm_num, ← Real.log_pow]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hlog2T : Real.log (|2 * ρ.val.im| + 2) ≤ 3 * L := by
    rw [hLdef, show (3 : ℝ) * Real.log |ρ.val.im| = ((3 : ℕ) : ℝ) * Real.log |ρ.val.im| by
      norm_num, ← Real.log_pow, abs_mul, abs_two]
    have hTT : 2 * 2 ≤ |ρ.val.im| * |ρ.val.im| := mul_le_mul ht ht (by norm_num) (by linarith)
    exact Real.log_le_log (by linarith) (by nlinarith)
  have r2 : (1 / ((σ : ℂ) + ρ.val.im * I - 1)).re ≤ L := by
    have := re_one_div_sub_one_le (s := (σ : ℂ) + ρ.val.im * I) (by simpa using hγ0)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add,
      add_zero] at this
    have h12 : 1 / |ρ.val.im| ≤ 1 / 2 := one_div_le_one_div_of_le two_pos ht
    linarith
  have r3 : (1 / ((σ : ℂ) + (2 * ρ.val.im : ℝ) * I - 1)).re ≤ L := by
    have h2γ : (2 * ρ.val.im : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hγ0
    have := re_one_div_sub_one_le (s := (σ : ℂ) + (2 * ρ.val.im : ℝ) * I) (by simpa using h2γ)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add,
      add_zero] at this
    have h12 : 1 / |2 * ρ.val.im| ≤ 1 / 2 :=
      one_div_le_one_div_of_le two_pos (by rw [abs_mul, abs_two]; linarith)
    linarith
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add,
    add_zero] at e3
  have hσm1 : 1 / (σ - 1) = 150 * L := by rw [hσ]; field_simp; ring
  have hu : 0 < σ - ρ.val.re := by linarith [hβ.2.2]
  have hneg : ∀ z : ℂ, (-deriv riemannZeta z / riemannZeta z).re =
      -(deriv riemannZeta z / riemannZeta z).re := fun z ↦ by rw [neg_div, Complex.neg_re]
  rw [hneg, hneg, hneg] at key
  have hcomb : 4 * (1 / (σ - ρ.val.re)) ≤ 525 * L := by nlinarith
  have hLu : 4 / 525 ≤ L * (σ - ρ.val.re) := by
    rw [mul_one_div, div_le_iff₀ hu] at hcomb
    nlinarith
  have hLσ : L * σ = L + 1 / 150 := by rw [hσ]; field_simp
  rw [show 1 / 1050 / L = 1 / (1050 * L) by ring, le_sub_iff_add_le, ← le_sub_iff_add_le',
    div_le_iff₀ (by positivity)]
  nlinarith

/-- The zeros of `ξ` in `|s| ≤ 3` have real parts bounded by some `m < 1`. -/
lemma exists_re_le_of_norm_le_three :
    ∃ m : ℝ, 0 ≤ m ∧ m < 1 ∧ ∀ ρ : ZeroIndex riemannXi, ‖ρ.val‖ ≤ 3 → ρ.val.re ≤ m := by
  have hF := finite_zeroIndex_closedBall differentiable_riemannXi 3
  rcases isEmpty_or_nonempty {i : ZeroIndex riemannXi // ‖i.val‖ ≤ 3} with he | hne
  · exact ⟨0, le_rfl, one_pos, fun ρ hρ ↦ (he.false ⟨ρ, hρ⟩).elim⟩
  · obtain ⟨j, hj⟩ := Finite.exists_max fun i : {i : ZeroIndex riemannXi // ‖i.val‖ ≤ 3} ↦
      i.1.val.re
    refine ⟨max 0 j.1.val.re, le_max_left _ _,
      max_lt one_pos (riemannXi_zero_mem j.1).2.2, fun ρ hρ ↦ ?_⟩
    exact (hj ⟨ρ, hρ⟩).trans (le_max_right _ _)

/-- **Davenport, Ch. 13, p. 86 (row 13-12)**: there is `c > 0` such that `ζ(s)` has no zero in
`σ ≥ 1 - c/log(|t| + 2)`. -/
@[kb "davenport1980" "Ch 13, p. 86"]
theorem Davenport.riemannZeta_zero_free_region_all :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, riemannZeta s = 0 → s.re < 1 - c / Real.log (|s.im| + 2) := by
  obtain ⟨c₁, hc₁, h₁⟩ := Davenport.riemannZeta_zero_free_region
  obtain ⟨m, hm0, hm1, hm⟩ := exists_re_le_of_norm_le_three
  have hl2 := log_two_gt_two_thirds
  set c := min (c₁ / 2) ((1 - m) * Real.log 2 / 2) with hc
  have hm' : 0 < 1 - m := by linarith
  have hl0 : 0 < Real.log 2 := by linarith
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc0, fun s hs ↦ ?_⟩
  have hT : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log two_pos (by linarith [abs_nonneg s.im])
  have hLpos : 0 < Real.log (|s.im| + 2) := by linarith
  -- `c / log(|t| + 2) ≤ (1 - m)/2`
  have hsmall : c / Real.log (|s.im| + 2) ≤ (1 - m) / 2 := by
    rw [div_le_iff₀ hLpos]
    have : c ≤ (1 - m) * Real.log 2 / 2 := min_le_right _ _
    nlinarith
  rcases le_or_gt s.re 0 with h0 | h0
  · linarith
  obtain ⟨ρ, rfl⟩ := exists_zeroIndex_riemannXi hs h0
  have hβ := riemannXi_zero_mem ρ
  rcases le_or_gt 2 |ρ.val.im| with ht | ht
  · have h := h₁ ρ.val hs ht
    have hL : 0 < Real.log |ρ.val.im| := by
      have := Real.log_le_log two_pos ht; linarith
    have hLL : Real.log |ρ.val.im| < Real.log (|ρ.val.im| + 2) :=
      Real.log_lt_log (by linarith) (by linarith)
    have : c / Real.log (|ρ.val.im| + 2) < c₁ / Real.log |ρ.val.im| := by
      calc c / Real.log (|ρ.val.im| + 2) ≤ c / Real.log |ρ.val.im| :=
            div_le_div_of_nonneg_left hc0.le hL hLL.le
        _ < c₁ / Real.log |ρ.val.im| := by
            apply div_lt_div_of_pos_right _ hL
            have : c ≤ c₁ / 2 := min_le_left _ _
            linarith
    linarith
  · have hn : ‖ρ.val‖ ≤ 3 := by
      have := Complex.norm_le_abs_re_add_abs_im ρ.val
      rw [abs_of_pos hβ.2.1] at this
      linarith [hβ.2.2]
    have := hm ρ hn
    linarith

end NTKB
