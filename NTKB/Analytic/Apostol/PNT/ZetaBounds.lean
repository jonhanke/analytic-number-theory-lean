/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.Liouville
import NTKB.Analytic.Apostol.Zeta.HurwitzBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Upper bounds for `|ζ(s)|` and `|ζ'(s)|` near the line `σ = 1` (Apostol, Theorem 13.4)

**Theorem 13.4.** For every `A > 0` there is `M` such that `|ζ(s)| ≤ M log t` and
`|ζ'(s)| ≤ M log² t` for all `s` with `σ ≥ 1/2`, `σ > 1 - A/log t` and `t ≥ e`.

Proof: the bound for `ζ` is Apostol's, from Theorem 12.21 with `a = 1` and `N = [t] - 1`
(`|n^{-s}| ≤ e^A/n` for `n ≤ t`). For `ζ'` Apostol differentiates the representation; here we use
Cauchy's estimate on a disc of radius `1/(4 log t)` instead, together with the bound for `ζ` in a
slightly larger region.
-/

open Complex Filter Topology Finset HurwitzZeta Metric

namespace NTKB.Apostol

/-- `y^{1-σ} ≤ e^A` for `1 ≤ y ≤ t` and `σ ≥ 1 - A/log t`. -/
lemma rpow_one_sub_le_exp {y t A σ : ℝ} (hy1 : 1 ≤ y) (hyt : y ≤ t) (ht : 1 < t) (hA : 0 ≤ A)
    (hσ : 1 - A / Real.log t ≤ σ) : y ^ (1 - σ) ≤ Real.exp A := by
  have hlt : 0 < Real.log t := Real.log_pos ht
  rw [Real.rpow_def_of_pos (by linarith)]
  apply Real.exp_le_exp.mpr
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hlyt : Real.log y ≤ Real.log t := Real.log_le_log (by linarith) hyt
  rcases le_or_gt σ 1 with h | h
  · have h1 : 1 - σ ≤ A / Real.log t := by linarith
    calc Real.log y * (1 - σ) ≤ Real.log t * (A / Real.log t) :=
          mul_le_mul hlyt h1 (by linarith) hlt.le
      _ = A := by field_simp
  · nlinarith

lemma riemannZeta_eq_hurwitz_one : (fun s ↦ hurwitzZeta ((1 : ℝ) : UnitAddCircle) s) = riemannZeta := by
  have h : ((1 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period 1
  rw [h, hurwitzZeta_zero]

/-- The bound `|ζ(s)| ≤ M (log t + 1)` in the strip `1/4 ≤ σ ≤ 3`, `t ≥ 2`, `σ ≥ 1 - A/log t`
(Apostol's proof of Theorem 13.4). -/
lemma zeta_bound_strip {A : ℝ} (hA : 0 < A) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 → 2 ≤ s.im →
      1 - A / Real.log s.im ≤ s.re → ‖riemannZeta s‖ ≤ M * (Real.log s.im + 1) := by
  refine ⟨38 * Real.exp A, by positivity, fun s hσ1 hσ3 ht hσA ↦ ?_⟩
  set t := s.im
  set σ := s.re
  have ht1 : 1 < t := by linarith
  have hlt : 0 < Real.log t := Real.log_pos ht1
  have heA : 1 ≤ Real.exp A := Real.one_le_exp hA.le
  have hs1 : s ≠ 1 := fun h ↦ by
    have : t = 0 := by simp [t, h]
    linarith
  set N : ℕ := ⌊t⌋₊ - 1 with hN
  have hfl : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
  have hN1 : N + 1 = ⌊t⌋₊ := by omega
  have hN1t : ((N + 1 : ℕ) : ℝ) ≤ t := by rw [hN1]; exact Nat.floor_le (by linarith)
  have hNpos : 1 ≤ N := by omega
  have hNt3 : t / 3 ≤ N := by
    have h1 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have h2 : (N : ℝ) = ⌊t⌋₊ - 1 := by rw [hN, Nat.cast_sub (by omega)]; simp
    have h3 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    rcases le_or_gt t 3 with h | h
    · linarith
    · linarith
  -- the representation of Theorem 12.21 with `a = 1`
  have hrep := hurwitzZeta_eq_J one_pos le_rfl N (s := s) (by linarith) hs1
  rw [show hurwitzZeta ((1 : ℝ) : UnitAddCircle) s = riemannZeta s from
    congrFun riemannZeta_eq_hurwitz_one s] at hrep
  rw [hrep]
  -- the three bounds
  have T1 : ‖∑ n ∈ range (N + 1), (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      Real.exp A * (Real.log t + 1) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ range (N + 1), ‖(((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ range (N + 1), Real.exp A * ((n : ℝ) + 1)⁻¹ := by
          refine sum_le_sum fun n hn ↦ ?_
          have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [n.cast_nonneg (α := ℝ)]
          have hnt : (n : ℝ) + 1 ≤ t := by
            have : n + 1 ≤ N + 1 := by simp at hn; omega
            exact (by exact_mod_cast this : ((n + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ)) |>.trans hN1t
              |> fun h ↦ by simpa using h
          rw [norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]
          calc ((n : ℝ) + 1) ^ (-σ) = ((n : ℝ) + 1) ^ (1 - σ) * ((n : ℝ) + 1)⁻¹ := by
                rw [← Real.rpow_neg_one, ← Real.rpow_add (by positivity)]; ring_nf
            _ ≤ Real.exp A * ((n : ℝ) + 1)⁻¹ := by
                gcongr; exact rpow_one_sub_le_exp hn1 hnt ht1 hA.le hσA
      _ = Real.exp A * (harmonic (N + 1) : ℝ) := by
          rw [← mul_sum, harmonic]; push_cast; rfl
      _ ≤ Real.exp A * (Real.log t + 1) := by
          gcongr
          refine (harmonic_le_one_add_log _).trans ?_
          have := Real.log_le_log (by positivity) hN1t
          linarith
  have T2 : ‖((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ Real.exp A := by
    have hden : 1 ≤ ‖s - 1‖ := by
      calc (1 : ℝ) ≤ |(s - 1).im| := by
            simp only [sub_im, one_im, sub_zero]; rw [abs_of_pos (by linarith)]; linarith
        _ ≤ ‖s - 1‖ := abs_im_le_norm _
    rw [norm_div]
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    rw [norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [sub_re, one_re]
    calc ((N : ℝ) + 1) ^ (1 - σ) ≤ Real.exp A :=
          rpow_one_sub_le_exp (by linarith [N.cast_nonneg (α := ℝ)]) (by simpa using hN1t) ht1
            hA.le hσA
      _ ≤ Real.exp A * ‖s - 1‖ := le_mul_of_one_le_right (by positivity) hden
  have T3 : ‖hurwitzJSum 1 N s‖ ≤ 36 * Real.exp A := by
    set p : ℝ := min σ 1
    have hp0 : 0 < p := lt_min (by linarith) one_pos
    have hp1 : p ≤ 1 := min_le_right _ _
    have hp4 : 1 / 4 ≤ p := le_min hσ1 (by norm_num)
    have hpσ : p ≤ σ := min_le_left _ _
    have hsumN : HasSum (fun n : ℕ ↦ ‖s‖ * (((N + 1 : ℕ) + n : ℝ)) ^ (-p - 1))
        (‖s‖ * ∑' n : ℕ, (((N + 1 : ℕ) + n : ℝ)) ^ (-p - 1)) := by
      refine HasSum.mul_left _ (Summable.hasSum ?_)
      have := (summable_nat_add_iff (N + 1)).mpr
        (Real.summable_nat_rpow.mpr (show -p - 1 < -1 by linarith))
      refine this.congr fun n ↦ ?_
      push_cast; ring_nf
    have hb : ‖hurwitzJSum 1 N s‖ ≤ ‖s‖ * ∑' n : ℕ, (((N + 1 : ℕ) + n : ℝ)) ^ (-p - 1) := by
      refine tsum_of_norm_bounded hsumN fun n ↦ ?_
      refine (norm_hurwitzJ_le (by positivity) hs1 (by linarith)).trans ?_
      gcongr
      push_cast
      rw [show (N : ℝ) + n + 1 = (N : ℝ) + 1 + n by ring]
      have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
      have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have htail := tsum_rpow_neg_sub_one_le hp0 hp1 (N := N + 1) (by omega)
    push_cast at htail
    rw [show (N : ℝ) + 1 - 1 = N by ring] at htail
    have hnorm : ‖s‖ ≤ 3 * t := by
      calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
        _ ≤ 3 + t := by
            rw [abs_of_pos (by linarith : (0 : ℝ) < s.re), abs_of_pos (by linarith : (0 : ℝ) < t)]
            linarith
        _ ≤ 3 * t := by linarith
    have hNp : (N : ℝ) ^ (-p) ≤ 3 * Real.exp A / t := by
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hNt : (N : ℝ) ≤ t := by have := hN1t; push_cast at this; linarith
      have hAl : 0 < A / Real.log t := div_pos hA hlt
      have h1 : (N : ℝ) ^ (1 - p) ≤ Real.exp A := rpow_one_sub_le_exp
        (by exact_mod_cast hNpos) hNt ht1 hA.le (le_min hσA (by linarith))
      have h2 : (N : ℝ) ^ (-p) = (N : ℝ) ^ (1 - p) / N := by
        rw [Real.rpow_sub hN0, Real.rpow_one, Real.rpow_neg hN0.le]; field_simp
      rw [h2, div_le_div_iff₀ hN0 (by linarith)]
      nlinarith
    calc ‖hurwitzJSum 1 N s‖ ≤ ‖s‖ * ∑' n : ℕ, (((N + 1 : ℕ) + n : ℝ)) ^ (-p - 1) := hb
      _ ≤ (3 * t) * ((N : ℝ) ^ (-p) / p) := by
          gcongr
          push_cast
          exact htail
      _ ≤ (3 * t) * ((3 * Real.exp A / t) / (1 / 4)) := by gcongr
      _ = 36 * Real.exp A := by field_simp; ring
  have hlog1 : 0 ≤ Real.log t + 1 := by linarith
  calc ‖∑ n ∈ range (N + 1), ((n + 1 : ℝ) : ℂ) ^ (-s) + ((N + 1 : ℝ) : ℂ) ^ (1 - s) / (s - 1) -
        hurwitzJSum 1 N s‖
      ≤ Real.exp A * (Real.log t + 1) + Real.exp A + 36 * Real.exp A := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add T1 T2)) T3)
    _ ≤ 38 * Real.exp A * (Real.log t + 1) := by nlinarith

/-- `|ζ(s)| ≤ 1 + ζ(2)` for `σ ≥ 2` (Theorem 12.23 (a) with `a = 1`, `δ = 1`). -/
lemma zeta_bound_right {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ 1 + (riemannZeta ((1 + 1 : ℝ) : ℂ)).re := by
  have h := apostol_thm_12_23_a one_pos le_rfl (δ := 1) one_pos (s := s) (by linarith)
  rw [show hurwitzZeta ((1 : ℝ) : UnitAddCircle) s = riemannZeta s from
    congrFun riemannZeta_eq_hurwitz_one s] at h
  have h1 : (((1 : ℝ) : ℂ)) ^ (-s) = 1 := by simp
  rw [h1] at h
  have h2 : ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1‖ + 1 := by
    have := norm_add_le (riemannZeta s - 1) 1
    simpa using this
  linarith

/-- `|ζ(s)| ≤ M (log t + 1)` for `σ ≥ 1/4`, `t ≥ 2`, `σ ≥ 1 - A/log t`. -/
lemma zeta_bound_region {A : ℝ} (hA : 0 < A) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → 2 ≤ s.im →
      1 - A / Real.log s.im ≤ s.re → ‖riemannZeta s‖ ≤ M * (Real.log s.im + 1) := by
  obtain ⟨M, hM, hMb⟩ := zeta_bound_strip hA
  set C : ℝ := 1 + (riemannZeta ((1 + 1 : ℝ) : ℂ)).re
  have hC : 1 ≤ C := by
    have := zeta_bound_right (s := 2) (by norm_num)
    have := norm_nonneg (riemannZeta 2)
    have h0 : 0 ≤ (riemannZeta ((1 + 1 : ℝ) : ℂ)).re := by
      have h := apostol_thm_12_23_a one_pos le_rfl (δ := 1) one_pos (s := 2) (by norm_num)
      exact (norm_nonneg _).trans h
    simp only [C]; linarith
  refine ⟨M + C, by positivity, fun s h1 ht hA' ↦ ?_⟩
  have hl : 0 ≤ Real.log s.im := Real.log_nonneg (by linarith)
  rcases le_or_gt s.re 3 with h | h
  · exact (hMb s h1 h ht hA').trans (by nlinarith)
  · exact (zeta_bound_right (by linarith)).trans (by nlinarith)

/-- **Apostol, Theorem 13.4**: for every `A > 0` there is `M` with `|ζ(s)| ≤ M log t` and
`|ζ'(s)| ≤ M log² t` whenever `σ ≥ 1/2`, `σ > 1 - A/log t`, `t ≥ e`. -/
@[kb "apostol1976" "Thm 13.4, p. 285"]
theorem apostol_thm_13_4 {A : ℝ} (hA : 0 < A) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → 1 - A / Real.log s.im < s.re →
      Real.exp 1 ≤ s.im →
      ‖riemannZeta s‖ ≤ M * Real.log s.im ∧ ‖deriv riemannZeta s‖ ≤ M * Real.log s.im ^ 2 := by
  obtain ⟨M₁, hM₁, hM₁b⟩ := zeta_bound_region (A := 2 * A + 1) (by positivity)
  refine ⟨12 * M₁, by positivity, fun s hσ hσA ht ↦ ?_⟩
  set t := s.im with ht_def
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ht2 : 2 ≤ t := he.trans ht
  have hlt1 : 1 ≤ Real.log t := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) ht
  have hlt : 0 < Real.log t := by linarith
  have hAA : A / Real.log t ≤ (2 * A + 1) / Real.log t :=
    div_le_div_of_nonneg_right (by linarith) hlt.le
  constructor
  · have := hM₁b s (by linarith) ht2 (by linarith)
    calc ‖riemannZeta s‖ ≤ M₁ * (Real.log t + 1) := this
      _ ≤ 12 * M₁ * Real.log t := by nlinarith
  · -- Cauchy's estimate on the disc of radius `r = 1/(4 log t)`
    set r := 1 / (4 * Real.log t)
    have hr : 0 < r := by positivity
    have hr4 : r ≤ 1 / 4 := by
      simp only [r]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hclosed : ∀ z ∈ closedBall s r, 1 / 4 ≤ z.re ∧ 2 ≤ z.im ∧ z.im ≤ t + 1 / 4 ∧
        s.re - r ≤ z.re := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      have h1 := abs_re_le_norm (z - s)
      have h2 := abs_im_le_norm (z - s)
      simp only [sub_re, sub_im] at h1 h2
      rw [abs_le] at h1 h2
      refine ⟨by linarith [h1.1], ?_, by linarith [h2.2], by linarith [h1.1]⟩
      have : (2 : ℝ) + 1 / 4 ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9; linarith
      linarith [h2.1]
    have hdiff : DifferentiableOn ℂ riemannZeta (closedBall s r) := fun z hz ↦ by
      refine (differentiableAt_riemannZeta fun h ↦ ?_).differentiableWithinAt
      have := (hclosed z hz).2.1
      rw [h] at this; simp at this; linarith
    have hbound : ∀ z ∈ sphere s r, ‖riemannZeta z‖ ≤ 3 * M₁ * Real.log t := by
      intro z hz
      obtain ⟨hz1, hz2, hz3, hz4⟩ := hclosed z (sphere_subset_closedBall hz)
      have hlz : Real.log z.im ≤ 2 * Real.log t := by
        rw [← Real.log_rpow (by linarith), Real.rpow_two]
        exact Real.log_le_log (by linarith) (by nlinarith)
      have hlz0 : 0 < Real.log z.im := Real.log_pos (by linarith)
      have hregion : 1 - (2 * A + 1) / Real.log z.im ≤ z.re := by
        have h1 : (2 * A + 1) / (2 * Real.log t) ≤ (2 * A + 1) / Real.log z.im :=
          div_le_div_of_nonneg_left (by positivity) hlz0 hlz
        have h2 : (2 * A + 1) / (2 * Real.log t) = A / Real.log t + 2 * r := by
          simp only [r]; field_simp; ring
        linarith
      calc ‖riemannZeta z‖ ≤ M₁ * (Real.log z.im + 1) := hM₁b z hz1 hz2 hregion
        _ ≤ M₁ * (2 * Real.log t + Real.log t) := by gcongr
        _ = 3 * M₁ * Real.log t := by ring
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (hdiff.diffContOnCl_ball subset_rfl) hbound
    calc ‖deriv riemannZeta s‖ ≤ 3 * M₁ * Real.log t / r := hc
      _ = 12 * M₁ * Real.log t ^ 2 := by simp only [r]; field_simp; ring

end NTKB.Apostol
