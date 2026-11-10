/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LContourMain
import NTKB.Analytic.Davenport.Zeros.GoodHeight

/-!
# Heights avoiding the ordinates of the zeros of `L(s, χ)`

**Davenport, Ch. 19, p. 117** (the analogues of 17-9 and 17-10): there are `≪ log q(T + 2)` zeros
with `|γ - T| < 1`, so `T` may be moved by `O(1)` to have `|γ ± T| ≫ 1/log(qT)` for all zeros,
and then `|L'/L(σ ± iT, χ)| ≪ log² (qT)` for `-1 ≤ σ ≤ 2`.
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

/-- **Davenport, Ch. 19, p. 117** (analogue of 17-9). -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.exists_good_height_L :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ T₀ : ℝ, 2 ≤ T₀ → ∃ T ∈ Icc T₀ (T₀ + 1), ∀ ρ : ZeroIndex (dirichletXi χ),
        1 / (A * (Real.log N + Real.log T₀)) ≤ |ρ.val.im - T| ∧
          1 / (A * (Real.log N + Real.log T₀)) ≤ |ρ.val.im + T| := by
  classical
  obtain ⟨A₁, hA₁, h₁'⟩ := Davenport.card_L_zeros_near_le
  have hl2 := log_two_gt_two_thirds
  refine ⟨12 * A₁ + 6, by positivity, ?_⟩
  intro N _ χ hχ hN T₀ hT₀
  have h₁ := h₁' hχ hN
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set a := T₀ + 1 / 2 with ha
  obtain ⟨hf1, hc1⟩ := h₁ a
  obtain ⟨hf2, hc2⟩ := h₁ (-a)
  set S₁ := hf1.toFinset.image fun ρ : ZeroIndex (dirichletXi χ) ↦ ρ.val.im
  set S₂ := hf2.toFinset.image fun ρ : ZeroIndex (dirichletXi χ) ↦ -ρ.val.im
  set S := S₁ ∪ S₂
  obtain ⟨T, hT, hfar⟩ := exists_far_point S T₀
  refine ⟨T, hT, fun ρ ↦ ?_⟩
  -- bounds on `#S`
  have hlog : Real.log (|a| + 2) ≤ 3 * Real.log T₀ := by
    rw [abs_of_pos (by positivity), show (3 : ℝ) * Real.log T₀ = ((3 : ℕ) : ℝ) * Real.log T₀ by
      norm_num, ← Real.log_pow]
    have h4 : (4 : ℝ) ≤ T₀ * T₀ := by nlinarith
    exact Real.log_le_log (by positivity) (by rw [ha]; nlinarith)
  have hlog' : Real.log (|-a| + 2) ≤ 3 * Real.log T₀ := by rwa [abs_neg]
  have hlT : Real.log 2 ≤ Real.log T₀ := Real.log_le_log two_pos hT₀
  have hcardS : (S.card : ℝ) ≤ 6 * A₁ * (Real.log N + Real.log T₀) := by
    have h1 : (S₁.card : ℝ) ≤ A₁ * (Real.log N + Real.log (|a| + 2)) := by
      refine le_trans ?_ hc1
      rw [Set.ncard_eq_toFinset_card _ hf1]
      exact_mod_cast Finset.card_image_le
    have h2 : (S₂.card : ℝ) ≤ A₁ * (Real.log N + Real.log (|-a| + 2)) := by
      refine le_trans ?_ hc2
      rw [Set.ncard_eq_toFinset_card _ hf2]
      exact_mod_cast Finset.card_image_le
    have h3 : (S.card : ℝ) ≤ S₁.card + S₂.card := by exact_mod_cast Finset.card_union_le _ _
    nlinarith
  have hδ : 1 / ((12 * A₁ + 6) * (Real.log N + Real.log T₀)) ≤ 1 / (2 * (S.card + 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hδ2 : 1 / ((12 * A₁ + 6) * (Real.log N + Real.log T₀)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le two_pos
    nlinarith
  constructor
  · by_cases hρ : |ρ.val.im - a| < 1
    · have : ρ.val.im ∈ S := Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨ρ, by simpa using hρ, rfl⟩)
      have := hfar _ this
      rw [abs_sub_comm] at this
      linarith
    · push Not at hρ
      have : 1 / 2 ≤ |ρ.val.im - T| := by
        have := abs_sub_abs_le_abs_sub (ρ.val.im - a) (T - a)
        have hTa : |T - a| ≤ 1 / 2 := by
          rw [abs_le]; constructor <;> linarith [hT.1, hT.2, ha]
        rw [show ρ.val.im - a - (T - a) = ρ.val.im - T by ring] at this
        linarith
      linarith
  · by_cases hρ : |ρ.val.im - -a| < 1
    · have : -ρ.val.im ∈ S := Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨ρ, by simpa using hρ, rfl⟩)
      have := hfar _ this
      rw [show T - -ρ.val.im = ρ.val.im + T by ring] at this
      linarith
    · push Not at hρ
      have : 1 / 2 ≤ |ρ.val.im + T| := by
        have := abs_sub_abs_le_abs_sub (ρ.val.im - -a) (a - T)
        have hTa : |a - T| ≤ 1 / 2 := by
          rw [abs_le]; constructor <;> linarith [hT.1, hT.2, ha]
        rw [show ρ.val.im - -a - (a - T) = ρ.val.im + T by ring] at this
        linarith
      linarith

/-- **Davenport, Ch. 19, p. 117** (analogue of 17-10). -/
@[kb "davenport1980" "Ch 19, p. 117"]
theorem Davenport.norm_logDeriv_LFunction_good_line :
    ∃ A : ℝ, 0 < A ∧ ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}, χ.IsPrimitive → N ≠ 1 →
      ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ ρ : ZeroIndex (dirichletXi χ), δ ≤ |ρ.val.im - s.im|) →
      LFunction χ s ≠ 0 ∧ ‖deriv (LFunction χ) s / LFunction χ s‖ ≤
        A * (Real.log N + Real.log (|s.im| + 2)) / δ := by
  classical
  obtain ⟨A₁, hA₁, h₁'⟩ := Davenport.logDeriv_LFunction_local
  obtain ⟨A₂, hA₂, h₂'⟩ := Davenport.card_L_zeros_near_le
  refine ⟨A₁ + A₂, by positivity, ?_⟩
  intro N _ χ hχ hN s hσ1 hσ2 ht δ hδ hδ1 hgood
  have h₁ := h₁' hχ hN
  have h₂ := h₂' hχ hN
  have hlN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hL : 0 ≤ Real.log N + Real.log (|s.im| + 2) := by
    have := Real.log_nonneg (by linarith [abs_nonneg s.im] : (1 : ℝ) ≤ |s.im| + 2); linarith
  -- `L(s, χ) ≠ 0` on the line
  have hz : LFunction χ s ≠ 0 := by
    intro hz
    rcases le_or_gt s.re 0 with hre | hre
    · refine LFunction_ne_zero_of_re_nonpos hχ hN (fun n hn ↦ ?_) hre hz
      have := congrArg Complex.im hn
      simp [dirichletParity_im] at this
      rw [this] at ht; norm_num at ht
    · obtain ⟨ρ, hρ⟩ := exists_zeroIndex_dirichletXi hχ hN hz hre
      have := hgood ρ; rw [hρ, sub_self, abs_zero] at this; linarith
  refine ⟨hz, ?_⟩
  have hloc := h₁ s hσ1 hσ2 ht hz
  obtain ⟨hfin, hcard⟩ := h₂ s.im
  -- the finite sum over the zeros near `t`
  have hsum : ∑' ρ : ZeroIndex (dirichletXi χ),
      (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0) =
      ∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0) := by
    refine tsum_eq_sum fun ρ hρ ↦ ?_
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, abs_sub_comm] at hρ
    simp [hρ]
  have hnear : ‖∑ ρ ∈ hfin.toFinset, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ ≤
      hfin.toFinset.card * (1 / δ) := by
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun ρ _ ↦ ?_
    split_ifs
    · rw [norm_div, norm_one]
      refine one_div_le_one_div_of_le hδ ?_
      have := Complex.abs_im_le_norm (s - ρ.val)
      simp only [Complex.sub_im] at this
      rw [abs_sub_comm] at this
      exact (hgood ρ).trans this
    · simp; positivity
  rw [← Set.ncard_eq_toFinset_card _ hfin] at hnear
  calc ‖deriv (LFunction χ) s / LFunction χ s‖
      ≤ ‖deriv (LFunction χ) s / LFunction χ s - ∑' ρ : ZeroIndex (dirichletXi χ),
          (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ +
        ‖∑' ρ : ZeroIndex (dirichletXi χ), (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ := by
        have := norm_add_le (deriv (LFunction χ) s / LFunction χ s - ∑' ρ : ZeroIndex (dirichletXi χ),
          (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0))
          (∑' ρ : ZeroIndex (dirichletXi χ), (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0))
        rwa [sub_add_cancel] at this
    _ ≤ A₁ * (Real.log N + Real.log (|s.im| + 2)) + A₂ * (Real.log N + Real.log (|s.im| + 2)) * (1 / δ) := by
        have hn' : ‖∑' ρ : ZeroIndex (dirichletXi χ),
            (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ ≤
            ({ρ : ZeroIndex (dirichletXi χ) | |ρ.val.im - s.im| < 1}.ncard : ℝ) * (1 / δ) := by
          rw [hsum]; exact hnear
        have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ 1 / δ)
        linarith
    _ ≤ (A₁ + A₂) * (Real.log N + Real.log (|s.im| + 2)) / δ := by
        have h1 : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
        have := mul_nonneg (mul_nonneg hA₁.le hL) (sub_nonneg.mpr h1)
        have e : (A₁ + A₂) * (Real.log N + Real.log (|s.im| + 2)) / δ = A₁ * (Real.log N + Real.log (|s.im| + 2)) * (1 / δ) +
            A₂ * (Real.log N + Real.log (|s.im| + 2)) * (1 / δ) := by ring
        rw [e]
        nlinarith


end NTKB
