/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.ExplicitPsi

/-!
# `∑_{|γ| < T} 1/|ρ| ≪ log² T`

**Davenport, Ch. 18, p. 111.** From the count of the zeros in unit strips (15-7):
the zeros with `k ≤ |γ| < k + 1` are `≪ log(k + 2)` in number.
-/

open Filter Topology Complex Set
open scoped Real

namespace NTKB

/-- `1/|ρ| ≤ K₀/(1 + |γ|)` for every nontrivial zero. -/
lemma exists_inv_norm_zero_le :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ ρ : ZeroIndex riemannXi, 1 / ‖ρ.val‖ ≤ K₀ / (1 + |ρ.val.im|) := by
  set S₀ := ∑ ρ ∈ zerosBelow 1, 1 / ‖ρ.val‖
  have hS₀ : 0 ≤ S₀ := Finset.sum_nonneg fun _ _ ↦ by positivity
  refine ⟨2 * S₀ + 2, by positivity, fun ρ ↦ ?_⟩
  have hγ := abs_nonneg ρ.val.im
  rw [le_div_iff₀ (by positivity)]
  by_cases h : |ρ.val.im| < 1
  · have h1 : 1 / ‖ρ.val‖ ≤ S₀ :=
      Finset.single_le_sum (f := fun ρ : ZeroIndex riemannXi ↦ 1 / ‖ρ.val‖)
        (fun _ _ ↦ by positivity) (mem_zerosBelow.mpr h)
    have h0 : 0 ≤ 1 / ‖ρ.val‖ := by positivity
    nlinarith
  · push Not at h
    have hn : |ρ.val.im| ≤ ‖ρ.val‖ := Complex.abs_im_le_norm _
    have hpos : 0 < ‖ρ.val‖ := by linarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
    nlinarith

/-- **Davenport, Ch. 18, p. 111**: `∑_{|γ| < T} 1/|ρ| ≤ C log² T` for `T ≥ 2`. -/
@[kb "davenport1980" "Ch 18, p. 111"]
theorem Davenport.sum_zeros_inv_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∑ ρ ∈ zerosBelow T, 1 / ‖ρ.val‖ ≤ C * Real.log T ^ 2 := by
  classical
  obtain ⟨K₀, hK₀, hK⟩ := exists_inv_norm_zero_le
  obtain ⟨A, hA, h⟩ := Davenport.card_zeta_zeros_near_le
  refine ⟨27 * A * K₀, by positivity, fun T hT ↦ ?_⟩
  have hT0 : 0 < T := by linarith
  have hlT : 2 / 3 < Real.log T :=
    log_two_gt_two_thirds.trans_le (Real.log_le_log two_pos hT)
  set M := ⌊T⌋₊ + 1
  -- the fibres `⌊|γ|⌋ = k`
  have hmaps : ∀ ρ ∈ zerosBelow T, (fun ρ : ZeroIndex riemannXi ↦ ⌊|ρ.val.im|⌋₊) ρ ∈
      Finset.range M := by
    intro ρ hρ
    rw [Finset.mem_range]
    have := Nat.floor_le_floor (R := ℝ) (mem_zerosBelow.mp hρ).le
    show ⌊|ρ.val.im|⌋₊ < ⌊T⌋₊ + 1
    omega
  have hfib : ∀ k ∈ Finset.range M,
      ∑ ρ ∈ zerosBelow T with ⌊|ρ.val.im|⌋₊ = k, 1 / ‖ρ.val‖ ≤
        2 * A * Real.log (T + 3) * (K₀ / (k + 1)) := by
    intro k hk
    have hkT : (k : ℝ) ≤ T := by
      have : k < ⌊T⌋₊ + 1 := Finset.mem_range.mp hk
      have h1 : k ≤ ⌊T⌋₊ := by omega
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hT0.le)
    set a : ℝ := k + 1 / 2 with ha
    obtain ⟨hf1, hc1⟩ := h a
    obtain ⟨hf2, hc2⟩ := h (-a)
    have hsub : (zerosBelow T).filter (fun ρ ↦ ⌊|ρ.val.im|⌋₊ = k) ⊆ hf1.toFinset ∪ hf2.toFinset := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have h1 : (k : ℝ) ≤ |ρ.val.im| := by
        rw [← hρ.2]; exact Nat.floor_le (abs_nonneg _)
      have h2 : |ρ.val.im| < k + 1 := by
        rw [← hρ.2]; exact Nat.lt_floor_add_one _
      rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      rcases le_or_gt 0 ρ.val.im with h0 | h0
      · left
        rw [abs_of_nonneg h0] at h1 h2
        show |ρ.val.im - a| < 1
        rw [abs_lt]; constructor <;> linarith
      · right
        rw [abs_of_neg h0] at h1 h2
        show |ρ.val.im - -a| < 1
        rw [abs_lt]; constructor <;> linarith
    have hcard : (((zerosBelow T).filter (fun ρ ↦ ⌊|ρ.val.im|⌋₊ = k)).card : ℝ) ≤
        2 * A * Real.log (T + 3) := by
      have h1 : (((zerosBelow T).filter (fun ρ ↦ ⌊|ρ.val.im|⌋₊ = k)).card : ℝ) ≤
          hf1.toFinset.card + hf2.toFinset.card := by
        exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [← Set.ncard_eq_toFinset_card _ hf1, ← Set.ncard_eq_toFinset_card _ hf2] at h1
      have hl : Real.log (|a| + 2) ≤ Real.log (T + 3) :=
        Real.log_le_log (by positivity) (by rw [abs_of_pos (by positivity)]; linarith)
      have hl' : Real.log (|-a| + 2) ≤ Real.log (T + 3) := by rwa [abs_neg]
      nlinarith
    calc ∑ ρ ∈ zerosBelow T with ⌊|ρ.val.im|⌋₊ = k, 1 / ‖ρ.val‖
        ≤ ∑ ρ ∈ zerosBelow T with ⌊|ρ.val.im|⌋₊ = k, K₀ / (k + 1) := by
          refine Finset.sum_le_sum fun ρ hρ ↦ (hK ρ).trans ?_
          rw [Finset.mem_filter] at hρ
          have h1 : (k : ℝ) ≤ |ρ.val.im| := by
            rw [← hρ.2]; exact Nat.floor_le (abs_nonneg _)
          exact div_le_div_of_nonneg_left hK₀.le (by positivity) (by linarith)
      _ = (((zerosBelow T).filter (fun ρ ↦ ⌊|ρ.val.im|⌋₊ = k)).card : ℝ) * (K₀ / (k + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * A * Real.log (T + 3) * (K₀ / (k + 1)) := by gcongr
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  have hH : ∑ k ∈ Finset.range M, K₀ / ((k : ℝ) + 1) ≤ K₀ * (1 + Real.log M) := by
    have := harmonic_le_one_add_log M
    rw [harmonic_eq_sum] at this
    simp_rw [div_eq_mul_one_div K₀, ← Finset.mul_sum]
    gcongr
  have hM : Real.log M ≤ 3 * Real.log T := by
    have : (M : ℝ) ≤ T + 1 := by
      simp only [M]; push_cast; linarith [Nat.floor_le hT0.le]
    calc Real.log M ≤ Real.log (T + 3) := Real.log_le_log (by positivity) (by linarith)
      _ ≤ 3 * Real.log T := log_add_three_le hT
  have hl3 := log_add_three_le hT
  have hlog3 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  calc 2 * A * Real.log (T + 3) * ∑ k ∈ Finset.range M, K₀ / ((k : ℝ) + 1)
      ≤ 2 * A * Real.log (T + 3) * (K₀ * (1 + Real.log M)) := by gcongr
    _ ≤ 2 * A * (3 * Real.log T) * (K₀ * (1 + 3 * Real.log T)) := by gcongr
    _ ≤ 2 * A * (3 * Real.log T) * (K₀ * (4.5 * Real.log T)) := by gcongr; linarith
    _ = 27 * A * K₀ * Real.log T ^ 2 := by ring

end NTKB
