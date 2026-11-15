/- Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license. -/
import NTKB.Analytic.Apostol.PNT.ZetaInverseBounds

/-!
# A zero-free region for `ζ(s)` (Apostol, Chapter 13, Theorem 13.10)

**Theorem 13.10.** There are `A, C > 0` such that `|ζ(σ + it)| ≥ C/log⁷ t` whenever `t ≥ e` and
`σ > 1 - A/log⁹ t`; in particular `ζ(s) ≠ 0` there (`apostol_thm_13_10`,
`riemannZeta_ne_zero_of_zeroFreeRegion`).

The proof is Apostol's: for `σ ≥ 1` this is Theorem 13.7 (`apostol_thm_13_7`); for `σ < 1`,
`|ζ(σ + it) - ζ(1 + it)| ≤ (1 - σ) max |ζ'| ≤ (A/log⁹ t) M log² t` by Theorem 13.4
(`apostol_thm_13_4`), which is at most half of `1/(M log⁷ t)` once `A` is small.
-/

open Complex

namespace NTKB.Apostol

/-- **Apostol, Theorem 13.10**: there are `A, C > 0` with `|ζ(σ + it)| ≥ C/log⁷ t` for `t ≥ e`
and `σ > 1 - A/log⁹ t`. -/
@[kb "apostol1976" "Thm 13.10, p. 291"]
theorem apostol_thm_13_10 :
    ∃ A > 0, ∃ C > 0, ∀ s : ℂ, Real.exp 1 ≤ s.im → 1 - A / Real.log s.im ^ 9 < s.re →
      C / Real.log s.im ^ 7 ≤ ‖riemannZeta s‖ := by
  obtain ⟨M₇, hM₇, h7⟩ := apostol_thm_13_7
  obtain ⟨M₄, hM₄, h4⟩ := apostol_thm_13_4 (A := 1) one_pos
  set A : ℝ := min (1 / 2) (1 / (2 * M₇ * M₄)) with hA
  have hA0 : 0 < A := lt_min (by norm_num) (by positivity)
  have hA1 : A ≤ 1 / 2 := min_le_left _ _
  have hA2 : A ≤ 1 / (2 * M₇ * M₄) := min_le_right _ _
  refine ⟨A, hA0, 1 / (2 * M₇), by positivity, fun s ht hσ ↦ ?_⟩
  set t := s.im with htdef
  set L := Real.log t with hL
  have hL1 : 1 ≤ L := by
    rw [hL, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) ht
  have hL0 : 0 < L := by linarith
  have hL7 : 0 < L ^ 7 := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  -- lower bound for σ ≥ 1
  have key : ∀ z : ℂ, 1 ≤ z.re → z.im = t → 1 / (M₇ * L ^ 7) ≤ ‖riemannZeta z‖ := by
    intro z hz hzt
    have hz0 : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hz
    have := (h7 z hz (by rw [hzt]; exact ht)).1
    rw [hzt, norm_inv] at this
    have hn : 0 < ‖riemannZeta z‖ := norm_pos_iff.2 hz0
    rw [div_le_iff₀ (by positivity)]
    rw [inv_le_iff_one_le_mul₀ hn] at this
    · nlinarith
  by_cases hσ1 : 1 ≤ s.re
  · have := key s hσ1 rfl
    calc 1 / (2 * M₇) / L ^ 7 = 1 / (2 * M₇ * L ^ 7) := by field_simp
      _ ≤ 1 / (M₇ * L ^ 7) := by
          apply one_div_le_one_div_of_le (by positivity); nlinarith [mul_pos hM₇ hL7]
      _ ≤ _ := this
  · push Not at hσ1
    have hAL : A / L ^ 9 ≤ 1 / L := by
      calc A / L ^ 9 ≤ A / L := by
            apply div_le_div_of_nonneg_left hA0.le hL0
            calc L = L ^ 1 := (pow_one L).symm
              _ ≤ L ^ 9 := pow_le_pow_right₀ hL1 (by norm_num)
        _ ≤ 1 / L := by
            apply div_le_div_of_nonneg_right _ hL0.le; linarith
    have hAL' : A / L ^ 9 ≤ 1 / 2 := by
      have : A / L ^ 9 ≤ A := div_le_self hA0.le (one_le_pow₀ hL1)
      linarith
    have hσhalf : 1 / 2 < s.re := by linarith
    set S : Set ℂ := {z | s.re ≤ z.re ∧ z.re ≤ 1 ∧ z.im = t} with hS
    have hSc : Convex ℝ S := by
      intro x hx y hy a b ha hb hab
      obtain ⟨hx1, hx2, hx3⟩ := hx
      obtain ⟨hy1, hy2, hy3⟩ := hy
      simp only [hS, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.smul_re,
        Complex.smul_im, smul_eq_mul]
      refine ⟨by nlinarith, by nlinarith, ?_⟩
      rw [hx3, hy3, ← add_mul, hab, one_mul]
    have hdiff : ∀ z ∈ S, DifferentiableAt ℂ riemannZeta z := by
      intro z hz
      apply differentiableAt_riemannZeta
      intro h
      have := hz.2.2
      rw [h] at this
      simp at this
      linarith
    have hder : ∀ z ∈ S, ‖deriv riemannZeta z‖ ≤ M₄ * L ^ 2 := by
      intro z hz
      obtain ⟨hz1, hz2, hz3⟩ := hz
      have := (h4 z (by linarith) (by rw [hz3]; linarith [hAL, hσ]) (by rw [hz3]; exact ht)).2
      rw [hz3] at this
      exact this
    set s1 : ℂ := ⟨1, t⟩ with hs1
    have hs1S : s1 ∈ S := ⟨hσ1.le, le_refl _, rfl⟩
    have hsS : s ∈ S := ⟨le_refl _, hσ1.le, rfl⟩
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hder hSc hsS hs1S
    have hnorm : ‖s1 - s‖ = 1 - s.re := by
      have : s1 - s = ((1 - s.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hs1, htdef]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [hnorm] at hmv
    have hk := key s1 le_rfl rfl
    have h1s : 1 - s.re < A / L ^ 9 := by linarith
    have h2 : (1 - s.re) * (M₄ * L ^ 2) ≤ A * M₄ / L ^ 7 := by
      calc (1 - s.re) * (M₄ * L ^ 2) ≤ A / L ^ 9 * (M₄ * L ^ 2) :=
            mul_le_mul_of_nonneg_right h1s.le (by positivity)
        _ = A * M₄ / L ^ 7 := by field_simp
    have h3 : A * M₄ ≤ 1 / (2 * M₇) := by
      calc A * M₄ ≤ 1 / (2 * M₇ * M₄) * M₄ := mul_le_mul_of_nonneg_right hA2 hM₄.le
        _ = 1 / (2 * M₇) := by field_simp
    have h4' : A * M₄ / L ^ 7 ≤ 1 / (2 * M₇) / L ^ 7 :=
      div_le_div_of_nonneg_right h3 hL7.le
    have h5 : 1 / (M₇ * L ^ 7) = 2 * (1 / (2 * M₇) / L ^ 7) := by field_simp
    have h6 := norm_sub_norm_le (riemannZeta s1) (riemannZeta s)
    rw [norm_sub_rev] at h6
    have : ‖riemannZeta s1‖ - ‖riemannZeta s1 - riemannZeta s‖ ≤ ‖riemannZeta s‖ := by
      linarith [norm_sub_norm_le (riemannZeta s1) (riemannZeta s1 - riemannZeta s),
        norm_sub_rev (riemannZeta s1) (riemannZeta s)]
    nlinarith [norm_sub_rev (riemannZeta s1) (riemannZeta s)]

/-- **Apostol, Theorem 13.10**: `ζ(σ + it) ≠ 0` for `t ≥ e` and `σ > 1 - A/log⁹ t`. -/
@[kb "apostol1976" "Thm 13.10, p. 291"]
theorem riemannZeta_ne_zero_of_zeroFreeRegion :
    ∃ A > 0, ∀ s : ℂ, Real.exp 1 ≤ s.im → 1 - A / Real.log s.im ^ 9 < s.re →
      riemannZeta s ≠ 0 := by
  obtain ⟨A, hA, C, hC, h⟩ := apostol_thm_13_10
  refine ⟨A, hA, fun s ht hσ ↦ ?_⟩
  have hL : 0 < Real.log s.im := by
    have := Real.log_le_log (Real.exp_pos 1) ht
    rw [Real.log_exp] at this; linarith
  have := h s ht hσ
  have hp : 0 < C / Real.log s.im ^ 7 := by positivity
  intro h0
  rw [h0, norm_zero] at this
  linarith

end NTKB.Apostol
