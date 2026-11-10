/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Davenport.Zeros.LConstant
import NTKB.Analytic.Davenport.Zeros.ZeroSum

/-!
# `∑_{1 ≤ |γ| < T} 1/|ρ| ≪ log(qT) log T` for `L(s, χ)`

**Davenport, Ch. 20, p. 122**: "The sum `∑|ρ|^{-1}` extended over the zeros with `|γ| ≥ 1` can be
estimated as in §18" (unit strips, 16-6).
-/

open Filter Topology Complex Set DirichletCharacter
open scoped Real

namespace NTKB

/-- **Davenport, Ch. 20, p. 122**. -/
@[kb "davenport1980" "Ch 20, p. 122"]
theorem Davenport.sum_L_zeros_inv_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
      (hq : q ≠ 1), ∀ T : ℝ, 2 ≤ T →
      ∑ ρ ∈ zerosBelowL hχ hq T, (if 1 ≤ |ρ.val.im| then 1 / ‖ρ.val‖ else 0) ≤
        C * (Real.log q + Real.log T) * Real.log T := by
  classical
  obtain ⟨A, hA, h'⟩ := Davenport.card_L_zeros_near_le
  set K₀ : ℝ := 2
  have hK₀ : (0 : ℝ) < K₀ := two_pos
  refine ⟨27 * A * K₀, by positivity, ?_⟩
  intro q _ χ hχ hq T hT
  have h := h' hχ hq
  have hlq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hK : ∀ ρ : ZeroIndex (dirichletXi χ),
      (if 1 ≤ |ρ.val.im| then 1 / ‖ρ.val‖ else 0) ≤ K₀ / (1 + |ρ.val.im|) := by
    intro ρ
    split_ifs with h1
    · have hn : |ρ.val.im| ≤ ‖ρ.val‖ := Complex.abs_im_le_norm _
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      simp only [K₀]; linarith
    · positivity
  have hT0 : 0 < T := by linarith
  have hlT : 2 / 3 < Real.log T :=
    log_two_gt_two_thirds.trans_le (Real.log_le_log two_pos hT)
  set M := ⌊T⌋₊ + 1
  -- the fibres `⌊|γ|⌋ = k`
  have hmaps : ∀ ρ ∈ zerosBelowL hχ hq T, (fun ρ : ZeroIndex (dirichletXi χ) ↦ ⌊|ρ.val.im|⌋₊) ρ ∈
      Finset.range M := by
    intro ρ hρ
    rw [Finset.mem_range]
    have := Nat.floor_le_floor (R := ℝ) (mem_zerosBelowL.mp hρ).le
    show ⌊|ρ.val.im|⌋₊ < ⌊T⌋₊ + 1
    omega
  have hfib : ∀ k ∈ Finset.range M,
      ∑ ρ ∈ zerosBelowL hχ hq T with ⌊|ρ.val.im|⌋₊ = k, (if 1 ≤ |ρ.val.im| then 1 / ‖ρ.val‖ else 0) ≤
        2 * A * (Real.log q + Real.log (T + 3)) * (K₀ / (k + 1)) := by
    intro k hk
    have hkT : (k : ℝ) ≤ T := by
      have : k < ⌊T⌋₊ + 1 := Finset.mem_range.mp hk
      have h1 : k ≤ ⌊T⌋₊ := by omega
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hT0.le)
    set a : ℝ := k + 1 / 2 with ha
    obtain ⟨hf1, hc1⟩ := h a
    obtain ⟨hf2, hc2⟩ := h (-a)
    have hsub : (zerosBelowL hχ hq T).filter (fun ρ ↦ ⌊|ρ.val.im|⌋₊ = k) ⊆ hf1.toFinset ∪ hf2.toFinset := by
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
    have hcard : (((zerosBelowL hχ hq T).filter (fun ρ ↦ ⌊|ρ.val.im|⌋₊ = k)).card : ℝ) ≤
        2 * A * (Real.log q + Real.log (T + 3)) := by
      have h1 : (((zerosBelowL hχ hq T).filter (fun ρ ↦ ⌊|ρ.val.im|⌋₊ = k)).card : ℝ) ≤
          hf1.toFinset.card + hf2.toFinset.card := by
        exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [← Set.ncard_eq_toFinset_card _ hf1, ← Set.ncard_eq_toFinset_card _ hf2] at h1
      have hl : Real.log (|a| + 2) ≤ Real.log (T + 3) :=
        Real.log_le_log (by positivity) (by rw [abs_of_pos (by positivity)]; linarith)
      have hl' : Real.log (|-a| + 2) ≤ Real.log (T + 3) := by rwa [abs_neg]
      nlinarith
    calc ∑ ρ ∈ zerosBelowL hχ hq T with ⌊|ρ.val.im|⌋₊ = k, (if 1 ≤ |ρ.val.im| then 1 / ‖ρ.val‖ else 0)
        ≤ ∑ ρ ∈ zerosBelowL hχ hq T with ⌊|ρ.val.im|⌋₊ = k, K₀ / (k + 1) := by
          refine Finset.sum_le_sum fun ρ hρ ↦ (hK ρ).trans ?_
          rw [Finset.mem_filter] at hρ
          have h1 : (k : ℝ) ≤ |ρ.val.im| := by
            rw [← hρ.2]; exact Nat.floor_le (abs_nonneg _)
          exact div_le_div_of_nonneg_left hK₀.le (by positivity) (by linarith)
      _ = (((zerosBelowL hχ hq T).filter (fun ρ ↦ ⌊|ρ.val.im|⌋₊ = k)).card : ℝ) * (K₀ / (k + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * A * (Real.log q + Real.log (T + 3)) * (K₀ / (k + 1)) := by gcongr
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
  calc 2 * A * (Real.log q + Real.log (T + 3)) * ∑ k ∈ Finset.range M, K₀ / ((k : ℝ) + 1)
      ≤ 2 * A * (Real.log q + Real.log (T + 3)) * (K₀ * (1 + Real.log M)) := by gcongr
    _ ≤ 2 * A * (3 * (Real.log q + Real.log T)) * (K₀ * (1 + 3 * Real.log T)) := by
        gcongr; linarith
    _ ≤ 2 * A * (3 * (Real.log q + Real.log T)) * (K₀ * (4.5 * Real.log T)) := by gcongr; linarith
    _ = 27 * A * K₀ * (Real.log q + Real.log T) * Real.log T := by ring


end NTKB
