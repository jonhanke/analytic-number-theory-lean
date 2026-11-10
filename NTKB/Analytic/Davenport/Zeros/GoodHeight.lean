/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitContour

/-!
# Heights avoiding the ordinates of zeros

**Davenport, Ch. 17, p. 108 (row 17-9).** Since there are `O(log T)` zeros with `|γ - T| < 1`,
among them there is a gap of length `≫ 1/log T`; varying `T` by a bounded amount we may assume
`|γ - T| ≫ 1/log T` for every zero.

* `exists_far_point`: pigeonhole, for a finite set `S` of reals and an interval of length `1`
  there is a point at distance `≥ 1/(2(#S + 1))` from `S`.
-/

open Filter Topology Complex Set
open scoped Real

namespace NTKB

/-- **Pigeonhole**: some `T ∈ [a, a + 1]` is at distance `≥ 1/(2(#S + 1))` from every `s ∈ S`. -/
lemma exists_far_point (S : Finset ℝ) (a : ℝ) :
    ∃ T ∈ Icc a (a + 1), ∀ s ∈ S, 1 / (2 * (S.card + 1)) ≤ |T - s| := by
  classical
  set N := S.card
  set δ : ℝ := 1 / (2 * (N + 1)) with hδ
  have hN : (0 : ℝ) < N + 1 := by positivity
  set t : ℕ → ℝ := fun j ↦ a + j / (N + 1) with ht
  have hblock : ∀ s ∈ S, ((Finset.range (N + 2)).filter fun j ↦ |t j - s| < δ).card ≤ 1 := by
    intro s _
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter] at hi hj
    by_contra hij
    have h1 : 1 / (N + 1) ≤ |t i - t j| := by
      simp only [t]
      rw [show a + (i : ℝ) / (N + 1) - (a + j / (N + 1)) = ((i : ℝ) - j) / (N + 1) by ring,
        abs_div, abs_of_pos hN]
      apply div_le_div_of_nonneg_right _ hN.le
      have : (i : ℤ) ≠ j := by exact_mod_cast hij
      have h2 := Int.one_le_abs (sub_ne_zero.mpr this)
      exact_mod_cast h2
    have h2 : |t i - t j| < 2 * δ := by
      calc |t i - t j| = |(t i - s) - (t j - s)| := by ring_nf
        _ ≤ |t i - s| + |t j - s| := abs_sub _ _
        _ < δ + δ := add_lt_add hi.2 hj.2
        _ = 2 * δ := by ring
    have : 2 * δ = 1 / (N + 1) := by rw [hδ]; field_simp
    linarith
  have hcard : ((Finset.range (N + 2)).filter fun j ↦ ∃ s ∈ S, |t j - s| < δ).card ≤ N := by
    have hsub : ((Finset.range (N + 2)).filter fun j ↦ ∃ s ∈ S, |t j - s| < δ) ⊆
        S.biUnion fun s ↦ (Finset.range (N + 2)).filter fun j ↦ |t j - s| < δ := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      obtain ⟨hjr, s, hs, hjs⟩ := hj
      exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_filter.mpr ⟨hjr, hjs⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ s ∈ S, ((Finset.range (N + 2)).filter fun j ↦ |t j - s| < δ).card
        ≤ ∑ _s ∈ S, 1 := Finset.sum_le_sum hblock
      _ = N := by simp [N]
  -- an unblocked index
  obtain ⟨j, hj, hjfree⟩ : ∃ j ∈ Finset.range (N + 2), ¬ ∃ s ∈ S, |t j - s| < δ := by
    by_contra h
    push Not at h
    have : (Finset.range (N + 2)).filter (fun j ↦ ∃ s ∈ S, |t j - s| < δ) = Finset.range (N + 2) :=
      Finset.filter_true_of_mem fun j hj ↦ h j hj
    rw [this, Finset.card_range] at hcard
    omega
  push Not at hjfree
  refine ⟨t j, ⟨?_, ?_⟩, hjfree⟩
  · simp only [t]; have : (0 : ℝ) ≤ j / (N + 1) := by positivity
    linarith
  · simp only [t]
    have hj' : (j : ℝ) ≤ N + 1 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have : (j : ℝ) / (N + 1) ≤ 1 := by rw [div_le_one hN]; exact hj'
    linarith

/-- **Davenport, Ch. 17, p. 108 (row 17-9)**: there is `A > 0` such that for every `T₀ ≥ 2` some
`T ∈ [T₀, T₀ + 1]` satisfies `|γ - T| ≥ 1/(A log T₀)` and `|γ + T| ≥ 1/(A log T₀)` for every
nontrivial zero `β + iγ`. -/
@[kb "davenport1980" "Ch 17, p. 108"]
theorem Davenport.exists_good_height :
    ∃ A : ℝ, 0 < A ∧ ∀ T₀ : ℝ, 2 ≤ T₀ → ∃ T ∈ Icc T₀ (T₀ + 1), ∀ ρ : ZeroIndex riemannXi,
      1 / (A * Real.log T₀) ≤ |ρ.val.im - T| ∧ 1 / (A * Real.log T₀) ≤ |ρ.val.im + T| := by
  classical
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.card_zeta_zeros_near_le
  have hl2 := log_two_gt_two_thirds
  refine ⟨12 * A₁ + 6, by positivity, fun T₀ hT₀ ↦ ?_⟩
  set a := T₀ + 1 / 2 with ha
  obtain ⟨hf1, hc1⟩ := h₁ a
  obtain ⟨hf2, hc2⟩ := h₁ (-a)
  set S₁ := hf1.toFinset.image fun ρ : ZeroIndex riemannXi ↦ ρ.val.im
  set S₂ := hf2.toFinset.image fun ρ : ZeroIndex riemannXi ↦ -ρ.val.im
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
  have hcardS : (S.card : ℝ) ≤ 6 * A₁ * Real.log T₀ := by
    have h1 : (S₁.card : ℝ) ≤ A₁ * Real.log (|a| + 2) := by
      refine le_trans ?_ hc1
      rw [Set.ncard_eq_toFinset_card _ hf1]
      exact_mod_cast Finset.card_image_le
    have h2 : (S₂.card : ℝ) ≤ A₁ * Real.log (|-a| + 2) := by
      refine le_trans ?_ hc2
      rw [Set.ncard_eq_toFinset_card _ hf2]
      exact_mod_cast Finset.card_image_le
    have h3 : (S.card : ℝ) ≤ S₁.card + S₂.card := by exact_mod_cast Finset.card_union_le _ _
    nlinarith
  have hδ : 1 / ((12 * A₁ + 6) * Real.log T₀) ≤ 1 / (2 * (S.card + 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hδ2 : 1 / ((12 * A₁ + 6) * Real.log T₀) ≤ 1 / 2 := by
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

/-- **Davenport, Ch. 17, p. 108 (row 17-10)**: there is `A` such that for `-1 ≤ σ ≤ 2`, `|t| ≥ 2`,
and `0 < δ ≤ 1` with `|γ - t| ≥ δ` for every zero, `|ζ'/ζ(σ + it)| ≤ A log(|t| + 2)/δ`
(with `δ ≫ 1/log T` from row 17-9 this is Davenport's `O(log² T)`). -/
@[kb "davenport1980" "Ch 17, p. 108"]
theorem Davenport.norm_logDeriv_riemannZeta_good_line :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ ρ : ZeroIndex riemannXi, δ ≤ |ρ.val.im - s.im|) →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ A * Real.log (|s.im| + 2) / δ := by
  classical
  obtain ⟨A₁, hA₁, h₁⟩ := Davenport.logDeriv_riemannZeta_local
  obtain ⟨A₂, hA₂, h₂⟩ := Davenport.card_zeta_zeros_near_le
  refine ⟨A₁ + A₂, by positivity, fun s hσ1 hσ2 ht δ hδ hδ1 hgood ↦ ?_⟩
  have hL : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  -- `ζ(s) ≠ 0` on the line
  have hs1 : s ≠ 1 := fun h ↦ by rw [h] at ht; norm_num at ht
  have hz : riemannZeta s ≠ 0 := by
    intro hz
    rcases riemannZeta_eq_zero_cases hz hs1 with ⟨m, rfl⟩ | ⟨ρ, hρ⟩
    · norm_num at ht
    · have := hgood ρ; rw [hρ, sub_self, abs_zero] at this; linarith
  have hloc := h₁ s hσ1 hσ2 ht hz
  obtain ⟨hfin, hcard⟩ := h₂ s.im
  -- the finite sum over the zeros near `t`
  have hsum : ∑' ρ : ZeroIndex riemannXi,
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
  calc ‖deriv riemannZeta s / riemannZeta s‖
      ≤ ‖deriv riemannZeta s / riemannZeta s - ∑' ρ : ZeroIndex riemannXi,
          (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ +
        ‖∑' ρ : ZeroIndex riemannXi, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ := by
        have := norm_add_le (deriv riemannZeta s / riemannZeta s - ∑' ρ : ZeroIndex riemannXi,
          (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0))
          (∑' ρ : ZeroIndex riemannXi, (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0))
        rwa [sub_add_cancel] at this
    _ ≤ A₁ * Real.log (|s.im| + 2) + A₂ * Real.log (|s.im| + 2) * (1 / δ) := by
        have hn' : ‖∑' ρ : ZeroIndex riemannXi,
            (if |s.im - ρ.val.im| < 1 then 1 / (s - ρ.val) else 0)‖ ≤
            ({ρ : ZeroIndex riemannXi | |ρ.val.im - s.im| < 1}.ncard : ℝ) * (1 / δ) := by
          rw [hsum]; exact hnear
        have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ 1 / δ)
        linarith
    _ ≤ (A₁ + A₂) * Real.log (|s.im| + 2) / δ := by
        have h1 : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
        have := mul_nonneg (mul_nonneg hA₁.le hL) (sub_nonneg.mpr h1)
        have e : (A₁ + A₂) * Real.log (|s.im| + 2) / δ = A₁ * Real.log (|s.im| + 2) * (1 / δ) +
            A₂ * Real.log (|s.im| + 2) * (1 / δ) := by ring
        rw [e]
        nlinarith

end NTKB
