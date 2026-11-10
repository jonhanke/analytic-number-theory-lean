/-
Copyright (c) 2026 The NTKB authors. Released under Apache 2.0 license.
-/
import NTKB.Analytic.Apostol.Averages.DivisorSums
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Sums of powers (Apostol, Theorem 3.2 (c), (d) for general exponents)

* `∑_{a < n ≤ b} n^{-s} ≤ (a^{1-s} - b^{1-s})/(s-1)` and, for `0 < s < 1`,
  `∑_{n ≤ N} n^{-s} ≤ 1 + N^{1-s}/(1-s)` (comparison with `∫ t^{-s} dt`);
* Theorem 3.2 (c): `∑_{n > x} n^{-s} = O(x^{1-s})` for `s > 1`;
* Theorem 3.2 (d): `∑_{n ≤ x} n^α = x^{α+1}/(α+1) + O(x^α)` for `α > 0`.
-/

open Finset Real intervalIntegral MeasureTheory

namespace NTKB.Apostol

/-- `∫_a^b t^{-s} dt` for `0 < a ≤ b`, `s ≠ 1`. -/
theorem integral_rpow_neg {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : s ≠ 1) :
    ∫ t in a..b, t ^ (-s) = (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  have hne : -s ≠ -1 := by intro h; apply hs; linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]; intro h; exact absurd h.1 (not_le.2 ha)
  rw [integral_rpow (Or.inr ⟨hne, h0⟩)]
  congr 1 <;> ring_nf

theorem antitoneOn_rpow_neg {s : ℝ} (hs : 0 ≤ s) :
    AntitoneOn (fun t : ℝ ↦ t ^ (-s)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)

theorem sum_Ioc_eq_sum_Ico_succ (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Ioc a b, g n = ∑ x ∈ Ico a b, g (x + 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [sum_Ioc_succ_top hab, ih, sum_Ico_succ_top hab]

theorem sum_range_add_eq_sum_Ioc (g : ℕ → ℝ) (N M : ℕ) :
    ∑ i ∈ range M, g (i + (N + 1)) = ∑ n ∈ Ioc N (N + M), g n := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, show N + (M + 1) = N + M + 1 by ring, sum_Ioc_succ_top (by omega),
      show M + (N + 1) = N + M + 1 by ring]

/-- `∑_{a < n ≤ b} n^{-s} ≤ ∫_a^b t^{-s} dt` for integers `1 ≤ a ≤ b`, `s ≥ 0`. -/
theorem sum_Ioc_rpow_neg_le_integral {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) {s : ℝ} (hs : 0 ≤ s) :
    ∑ n ∈ Ioc a b, (n : ℝ) ^ (-s) ≤ ∫ t in (a : ℝ)..b, t ^ (-s) := by
  have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-s)) (Set.Icc (a : ℝ) b) := by
    refine (antitoneOn_rpow_neg hs).mono fun t ht ↦ ?_
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    exact lt_of_lt_of_le one_pos (this.trans ht.1)
  have h := AntitoneOn.sum_le_integral_Ico hab hanti
  rw [sum_Ioc_eq_sum_Ico_succ (fun n ↦ (n : ℝ) ^ (-s)) hab]
  convert h using 2

/-- **Apostol, Theorem 3.2 (c)** (tail of `ζ(s)`, `s > 1`): for `N ≥ 1`,
`|∑_{n ≥ 1} n^{-s} - ∑_{n ≤ N} n^{-s}| ≤ N^{1-s}/(s-1)`. -/
@[kb "apostol1976" "Thm 3.2(c), p. 55"]
theorem abs_tsum_rpow_neg_sub_le {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    |∑' n : ℕ, (n : ℝ) ^ (-s) - ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)| ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
  have hsum : Summable fun n : ℕ ↦ (n : ℝ) ^ (-s) := by
    rw [Real.summable_nat_rpow]; linarith
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-s) := fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
  have h0 : (0 : ℝ) ^ (-s) = 0 := Real.zero_rpow (by linarith)
  have hrange : ∑ i ∈ range (N + 1), (i : ℝ) ^ (-s) = ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) := by
    rw [range_eq_Ico, ← Icc_one_eq_Ioc_zero, sum_eq_sum_Ico_succ_bot (by omega)]
    simp [h0]; rfl
  rw [← hsplit, hrange, add_sub_cancel_left, abs_of_nonneg (tsum_nonneg fun n ↦ hnn _)]
  refine tsum_le_of_sum_range_le (fun n ↦ hnn _) fun M ↦ ?_
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc ∑ i ∈ range M, ((i + (N + 1) : ℕ) : ℝ) ^ (-s) = ∑ n ∈ Ioc N (N + M), (n : ℝ) ^ (-s) :=
        sum_range_add_eq_sum_Ioc (fun n ↦ (n : ℝ) ^ (-s)) N M
    _ ≤ ∫ t in (N : ℝ)..((N + M : ℕ) : ℝ), t ^ (-s) :=
        sum_Ioc_rpow_neg_le_integral hN (by omega) (by linarith)
    _ = (((N + M : ℕ) : ℝ) ^ (1 - s) - (N : ℝ) ^ (1 - s)) / (1 - s) :=
        integral_rpow_neg (by linarith) (by exact_mod_cast (by omega : N ≤ N + M)) hs.ne'
    _ ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
        have hM : 0 ≤ ((N + M : ℕ) : ℝ) ^ (1 - s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h1s : (1 : ℝ) - s ≠ 0 := by linarith
        rw [show (((N + M : ℕ) : ℝ) ^ (1 - s) - (N : ℝ) ^ (1 - s)) / (1 - s) =
          ((N : ℝ) ^ (1 - s) - ((N + M : ℕ) : ℝ) ^ (1 - s)) / (s - 1) by
            field_simp; ring]
        exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- For `0 < s`, `s ≠ 1`: `∑_{1 < n ≤ N} n^{-s} ≤ (N^{1-s} - 1)/(1-s)`. -/
theorem sum_Ioc_one_rpow_neg_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 1 N, (n : ℝ) ^ (-s) ≤ ((N : ℝ) ^ (1 - s) - 1) / (1 - s) := by
  have h := sum_Ioc_rpow_neg_le_integral le_rfl hN hs0
  rw [integral_rpow_neg (by norm_num) (by exact_mod_cast hN) hs] at h
  simpa using h

/-- **Apostol, Theorem 3.2 (d)** for `α > 0`, integer form:
`N^{α+1}/(α+1) ≤ ∑_{n ≤ N} n^α ≤ N^{α+1}/(α+1) + N^α`. -/
theorem sum_Ioc_rpow_bounds {α : ℝ} (hα : 0 < α) (N : ℕ) :
    (N : ℝ) ^ (α + 1) / (α + 1) ≤ ∑ n ∈ Ioc 0 N, (n : ℝ) ^ α ∧
      ∑ n ∈ Ioc 0 N, (n : ℝ) ^ α ≤ (N : ℝ) ^ (α + 1) / (α + 1) + (N : ℝ) ^ α := by
  have hmono : MonotoneOn (fun t : ℝ ↦ t ^ α) (Set.Icc ((0 : ℕ) : ℝ) N) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow hx.1 hxy hα.le
  have hint : ∫ t in ((0 : ℕ) : ℝ)..(N : ℝ), t ^ α = (N : ℝ) ^ (α + 1) / (α + 1) := by
    rw [integral_rpow (Or.inl (by linarith))]
    simp [Real.zero_rpow (by linarith : α + 1 ≠ 0)]
  have h1 := MonotoneOn.integral_le_sum_Ico (Nat.zero_le N) hmono
  have h2 := MonotoneOn.sum_le_integral_Ico (Nat.zero_le N) hmono
  rw [hint] at h1 h2
  have e1 : ∑ i ∈ Ico 0 N, (((i + 1 : ℕ) : ℝ)) ^ α = ∑ n ∈ Ioc 0 N, (n : ℝ) ^ α :=
    (sum_Ioc_eq_sum_Ico_succ (fun n ↦ (n : ℝ) ^ α) (Nat.zero_le N)).symm
  have e2 : ∑ i ∈ Ico 0 N, ((i : ℕ) : ℝ) ^ α = ∑ n ∈ Ioc 0 N, (n : ℝ) ^ α - (N : ℝ) ^ α := by
    rw [← e1, Nat.Ico_zero_eq_range, eq_sub_iff_add_eq]
    have := sum_range_succ (fun i : ℕ ↦ (i : ℝ) ^ α) N
    have h' := sum_range_succ' (fun i : ℕ ↦ (i : ℝ) ^ α) N
    simp only [Nat.cast_zero, Real.zero_rpow hα.ne', add_zero] at h'
    push_cast at this h' ⊢
    linarith
  constructor
  · calc (N : ℝ) ^ (α + 1) / (α + 1) ≤ ∑ i ∈ Ico 0 N, (((i + 1 : ℕ) : ℝ)) ^ α := by
          convert h1 using 2
      _ = _ := e1
  · have := h2
    rw [e2] at this
    linarith

/-- `y^{α+1} - N^{α+1} ≤ (α+1) y^α` for `0 ≤ N ≤ y < N + 1`, `α ≥ 0`. -/
theorem rpow_succ_sub_le {α : ℝ} (hα : 0 ≤ α) {y : ℝ} (hy : 0 ≤ y) :
    y ^ (α + 1) - (⌊y⌋₊ : ℝ) ^ (α + 1) ≤ (α + 1) * y ^ α := by
  set N := (⌊y⌋₊ : ℝ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNy : N ≤ y := Nat.floor_le hy
  have hyN : y - N ≤ 1 := by have := Nat.lt_floor_add_one y; simp only [N]; linarith
  have hint : ∫ t in N..y, t ^ α = (y ^ (α + 1) - N ^ (α + 1)) / (α + 1) :=
    integral_rpow (Or.inl (by linarith))
  have hle : ∫ t in N..y, t ^ α ≤ ∫ t in N..y, y ^ α := by
    refine intervalIntegral.integral_mono_on hNy ?_ intervalIntegrable_const fun t ht ↦ ?_
    · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    · exact Real.rpow_le_rpow (hN0.trans ht.1) ht.2 hα
  rw [hint, intervalIntegral.integral_const, smul_eq_mul] at hle
  have hpos : 0 < α + 1 := by linarith
  have hya : 0 ≤ y ^ α := Real.rpow_nonneg hy _
  rw [div_le_iff₀ hpos] at hle
  have h2 : (y - N) * y ^ α * (α + 1) ≤ 1 * y ^ α * (α + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hyN hya) hpos.le
  linarith

/-- **Apostol, Theorem 3.2 (d)** for `α > 0`: `∑_{n ≤ x} n^α = x^{α+1}/(α+1) + O(x^α)`;
explicitly the error is at most `x^α` for `x ≥ 0`. -/
@[kb "apostol1976" "Thm 3.2(d), p. 55"]
theorem abs_sum_rpow_sub_le {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 0 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (n : ℝ) ^ α - x ^ (α + 1) / (α + 1)| ≤ x ^ α := by
  have hb := sum_Ioc_rpow_bounds hα ⌊x⌋₊
  have hs := rpow_succ_sub_le hα.le hx
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hpow1 : (⌊x⌋₊ : ℝ) ^ (α + 1) ≤ x ^ (α + 1) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (by linarith)
  have hpow2 : (⌊x⌋₊ : ℝ) ^ α ≤ x ^ α := Real.rpow_le_rpow (Nat.cast_nonneg _) hNx hα.le
  have hpos : 0 < α + 1 := by linarith
  rw [abs_le]
  constructor
  · have : x ^ (α + 1) / (α + 1) - x ^ α ≤ (⌊x⌋₊ : ℝ) ^ (α + 1) / (α + 1) := by
      rw [sub_le_iff_le_add, div_add' _ _ _ hpos.ne', div_le_div_iff_of_pos_right hpos]
      linarith
    linarith [hb.1]
  · have : (⌊x⌋₊ : ℝ) ^ (α + 1) / (α + 1) ≤ x ^ (α + 1) / (α + 1) :=
      div_le_div_of_nonneg_right hpow1 hpos.le
    linarith [hb.2]

end NTKB.Apostol
